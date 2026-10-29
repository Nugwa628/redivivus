#!/usr/bin/env python3
"""fix_voidarith.py - give `void *` arithmetic back its byte cast.

    fix_voidarith.py [--apply] [PATTERN ...]

The generator writes a byte offset into a `void *` member as plain pointer
arithmetic, `(uint32_t*)(sgptDataTable->pSkillsCode + nOffset)`: g++ takes it
(GNU arithmetic on `void *` counts bytes), VC8 does not (C2036 'void *' :
unknown size), so the function is quarantined, its body blanked. The blanked
body costs its callers too: VC8 sees the callee in the same TU never return
and ends their call to it with int3 (ITEM_IsSocketable, 0062beb0, after
ITEMS_IsA). The tree before the regeneration had the cast,
`(uint8_t*)sgptDataTable->pSkillsCode + nOffset`, which is what g++ compiles
the plain form to, so the edit is neutral.

For every quarantine row with C2036 'void *' this puts `(uint8_t*)` before
each access on that line to a member the headers declare only as `void *`,
when a `+` or `-` follows it. The edit is kept only if the function then
compiles and nothing that matched stops matching (fixlib's batch loop).
"""
import argparse
import collections
import glob
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit            # noqa: E402
import fixlib           # noqa: E402
from oracle_config import BUILD, ORACLE, REPO  # noqa: E402

MEMBER_DECL = re.compile(r'^[ \t]*(?:/\*[^*]*\*/[ \t]*)?([A-Za-z_][\w:]*(?:[ \t]*\*)*)[ \t]*\b([A-Za-z_]\w*)[ \t]*;', re.M)


def void_members():
    """Member names every header declares as `void *` and as nothing else."""
    kinds = collections.defaultdict(set)
    for h in glob.glob(os.path.join(REPO, '**', '*.h'), recursive=True):
        if os.sep + 'asm_matching' + os.sep in h:
            continue
        for m in MEMBER_DECL.finditer(fixlib.read(h)):
            kinds[m.group(2)].add(re.sub(r'\s+', '', m.group(1)))
    return {n for n, k in kinds.items() if k == {'void*'}}


def site(members):
    names = '|'.join(sorted(members, key=len, reverse=True))
    # The access chain `a->b.c` ending in a void* member, an operator after it,
    # and no cast already before it.
    return re.compile(r'(?<![\w>.)])((?:[A-Za-z_]\w*(?:->|\.))+(?:' + names + r'))(?=\s*[-+](?![-+=>]))')


def candidates(pats, members):
    """tu -> [(function, line)]."""
    out = collections.defaultdict(list)
    seen = set()
    for line in open(os.path.join(BUILD, 'quarantine.tsv')):
        p = line.rstrip('\n').split('\t')
        if len(p) < 5 or p[0] == 'file' or not p[4].startswith("C2036 'void *'"):
            continue
        tu = p[0][:-4]
        if pats and not any(x in tu for x in pats):
            continue
        if (tu, int(p[1])) not in seen:
            seen.add((tu, int(p[1])))
            out[tu].append((p[3], int(p[1])))
    return out


def cast(cpp, ln, rx):
    def fn(texts):
        lines = texts[cpp].split('\n')
        new = rx.sub(r'(uint8_t*)\1', lines[ln - 1])
        if new == lines[ln - 1]:
            return None
        lines[ln - 1] = new
        return {cpp: '\n'.join(lines)}
    return fn


def compiles(tu, func):
    def fn():
        q = audit.load_quarantine(os.path.join(BUILD, 'quarantine.tsv'))
        return (tu, func.rsplit('::', 1)[-1]) not in q
    return fn


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('-j', '--jobs', type=int, default=4)
    ap.add_argument('patterns', nargs='*')
    args = ap.parse_args()
    rx = site(void_members())
    cands = candidates(args.patterns, void_members())
    rows = audit.load_funcmap(os.path.join(ORACLE, 'evidence', 'funcmap.tsv'))
    start_of = {(r[3], r[2].rsplit('::', 1)[-1]): r[0] for r in rows}
    n = sum(len(v) for v in cands.values())
    print('%d lines in %d TUs' % (n, len(cands)))
    if not args.apply:
        for tu in sorted(cands):
            cpp = os.path.join(REPO, tu + '.cpp')
            lines = fixlib.read(cpp).split('\n')
            for func, ln in cands[tu]:
                print('%s:%d %s %s' % (tu, ln, func, 'site' if rx.search(lines[ln - 1]) else 'NO SITE'))
        return 0
    _ref, model = audit.load_context()
    syms = audit.sym_map(rows)
    quarantined = audit.load_quarantine(os.path.join(BUILD, 'quarantine.tsv'))
    groups = {}
    for tu in sorted(cands):
        cpp = os.path.join(REPO, tu + '.cpp')
        # One edit per function: its body compiles only when all its lines do.
        by_func = collections.defaultdict(list)
        for func, ln in cands[tu]:
            by_func[func].append(ln)
        edits = []
        for func, lns in sorted(by_func.items()):
            fns = [cast(cpp, ln, rx) for ln in lns]

            def fn(texts, fns=fns):
                for f in fns:
                    new = f(texts)
                    if new is None:
                        return None
                    texts.update(new)
                return texts
            s = start_of.get((tu, func.rsplit('::', 1)[-1]))
            owners = [s] if s is not None else []
            edits.append(fixlib.Edit('%s:%s' % (tu, func), owners, owners, fn, neutral=True,
                                     check=compiles(tu, func)))
        groups[tu] = (edits, [cpp])
    kept, gained = fixlib.apply_batch(groups, (rows, model, syms, quarantined), jobs=args.jobs,
                                      log=lambda m: print(m, flush=True))
    print('kept %d of %d edits, MATCH %+d' % (kept, sum(len(g[0]) for g in groups.values()), gained))
    fixlib.record('fix_voidarith', n, kept, gained)
    return 0


if __name__ == '__main__':
    sys.exit(main())

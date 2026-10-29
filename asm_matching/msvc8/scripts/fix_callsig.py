#!/usr/bin/env python3
"""fix_callsig.py - a prototype back as it was when its callers matched, with every call's arguments.

    fix_callsig.py [--apply] [--only NAME,...] REV OLD_AUDIT [PATTERN ...]

A regeneration can change a function's prototype under functions that
matched: a parameter dropped (`FreeDialogStrc()` for the original's
`__fastcall FreeDialogStrc(D2DialogStrc *pDialog)`, whose callers load
ECX), two parameters swapped, a convention or a return type changed.
fix_restore.py cannot give such a caller its old body back: the body's calls
no longer fit the prototype. For every original function that was MATCH in
OLD_AUDIT (the old tree's evidence/audit.tsv) and is not MATCH here, this
looks at the functions its body in REV (the old tree's commit) calls, and at
the function itself: each whose definition's head differs between REV and
the tree is one edit, which puts back
  - the definition, head and body, as REV has it,
  - every declaration, as REV has it in the same file (else the old head,
    `static` as the declaration has it); for a function static in REV, no
    declaration outside its file (its header's removed, as fix_static.py
    does; the edit is not made where another file declares it),
  - the arguments of every call, taken from the same function in REV, the
    k-th call for the k-th call (left alone where that function has another
    number of calls in REV: the build then fails and drops the edit) - or,
    for a caller that matched in REV, its whole body there: a body written
    for the new prototype can need more than other arguments
    (`UNITS_GetRoom(pUnit); GetObjectControlSeed(pGame)` for the original's
    `GetObjectControlSeed(pGame, UNITS_GetRoom(pUnit))`).
fix_restore.py can then bring the callers' bodies back.

The evidence is the oracle's: all edits are made at once and the tree
rebuilt; every TU holding a function an edit touches, or an original caller
of its function, is judged, a renamed symbol standing for the original
function of its name. An edit is dropped when a TU it touches fails to
build, a function it affects stops matching, or its function comes out less
similar and none of the functions it affects comes to match; the rest is
tried again, a few rounds at most.
"""
import argparse
import collections
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import audit            # noqa: E402
import check            # noqa: E402
import fixlib           # noqa: E402
import ours as ourslib  # noqa: E402
from fix_fastcall import build_all, callers_of  # noqa: E402
from fix_ifelse import match_close  # noqa: E402
from fix_restore import load_status  # noqa: E402
from fix_static import blank_comments, forward_declare  # noqa: E402
from oracle_config import BUILD, ORACLE, REPO  # noqa: E402

ROUNDS = 4
DEF = re.compile(r'^(?P<head>[A-Za-z_][^;{}()\n]*?\b(?P<name>\w+)[ \t]*\((?P<params>[^;{}]*)\)[ \t]*)\{', re.M)
KEYWORDS = {'if', 'while', 'for', 'switch', 'return', 'sizeof', 'catch'}


def decl_rx(leaf):
    """A declaration of `leaf`: a type, then the name, at the start of a line."""
    return re.compile(r'^(?P<head>[ \t]*(?!return\b|else\b|case\b|delete\b|throw\b|goto\b)[A-Za-z_][^;{}()\n=]*?[\s*&]' +
                      re.escape(leaf) + r'[ \t]*\((?P<params>[^;{}]*)\)[ \t]*);', re.M)


def norm(head):
    return re.sub(r'\s+', ' ', re.sub(r'\bstruct\s+', '', head)).replace('( ', '(').replace(' )', ')').strip()


def defs(text):
    """leaf -> [(head start, body start, body end)] of the definitions in `text`."""
    out = collections.defaultdict(list)
    clean = blank_comments(text)
    for m in DEF.finditer(clean):
        if m.group('name') in KEYWORDS:
            continue
        i = m.end() - 1
        j = match_close(clean, i, '{', '}')
        if j is not None:
            out[m.group('name')].append((m.start(), i, j + 1))
    return out


def calls(text, leaf, lo=0, hi=None):
    """(open paren, close paren) of each call of `leaf` in text[lo:hi]."""
    hi = len(text) if hi is None else hi
    out = []
    for m in re.finditer(r'(?<![\w.>])(?:\w+::)*' + re.escape(leaf) + r'\s*\(', text[lo:hi]):
        i = lo + m.end() - 1
        j = match_close(text, i, '(', ')')
        if j is not None:
            out.append((i, j))
    return out


class Tree:
    """The sources of a tree, relative paths: the working tree, or REV."""

    def __init__(self, rev=None):
        if rev:
            names = subprocess.run(['git', '-C', REPO, 'ls-tree', '-r', '--name-only', rev],
                                   capture_output=True, text=True).stdout.split()
        else:
            names = subprocess.run(['git', '-C', REPO, 'ls-files'], capture_output=True, text=True).stdout.split()
        self.paths = [n for n in names if n.endswith(('.cpp', '.h'))]
        self.texts = {}
        if rev:
            blob = subprocess.run(['git', '-C', REPO, 'cat-file', '--batch'],
                                  input=''.join('%s:%s\n' % (rev, p) for p in self.paths).encode(),
                                  capture_output=True).stdout
            k = 0
            for p in self.paths:
                nl = blob.index(b'\n', k)
                size = int(blob[k:nl].split()[2])
                self.texts[p] = blob[nl + 1:nl + 1 + size].decode('utf-8', 'surrogateescape')
                k = nl + 1 + size + 1
        else:
            for p in self.paths:
                if os.path.exists(os.path.join(REPO, p)):
                    self.texts[p] = fixlib.read(os.path.join(REPO, p))
            self.paths = [p for p in self.paths if p in self.texts]
        self.defs = collections.defaultdict(list)
        for p in self.paths:
            if p.endswith('.cpp'):
                for leaf, spans in defs(self.texts[p]).items():
                    for sp in spans:
                        self.defs[leaf].append((p, sp))

    def one(self, leaf, prefer=None):
        c = self.defs.get(leaf, [])
        if prefer:
            here = [x for x in c if x[0] == prefer]
            if len(here) == 1:
                return here[0]
        return c[0] if len(c) == 1 else None

    def head(self, leaf, prefer=None):
        d = self.one(leaf, prefer)
        if d is None:
            return None
        p, (h, i, _j) = d
        return self.texts[p][h:i]


def static_decls(texts, cpp, leaf):
    """`texts` (relative paths) changed so that `leaf`, defined static in
    `cpp`, is declared nowhere else: its declaration in its own header
    removed (as fix_static.py promotes), its declarations in `cpp` static,
    one ahead of its first use there when that comes before the definition.
    None if another file names it: g++ refuses an extern declaration of a
    static function (VC8 does not), and a call from another file needs the
    function filed with its callers first (fix_refile.py)."""
    hdr = cpp[:-4] + '.h'
    for p, t in texts.items():
        if p not in (cpp, hdr) and leaf in t and re.search(r'\b%s\b' % re.escape(leaf), blank_comments(t)):
            return None
    out = {}
    if hdr in texts:
        h = texts[hdr]
        ms = list(decl_rx(leaf).finditer(h))
        if len(ms) > 1:
            return None
        if ms:
            a, b = ms[0].start(), ms[0].end()
            b += h[b:b + 1] == '\n'
            out[hdr] = h[:a] + h[b:]

    def make_static(m):
        hd = m.group('head')
        if re.match(r'\s*static\b', hd):
            return m.group(0)
        k = len(hd) - len(hd.lstrip())
        return hd[:k] + 'static ' + hd[k:] + ';'
    t = decl_rx(leaf).sub(make_static, texts[cpp])
    d = defs(t).get(leaf, [])
    if len(d) != 1:
        return None
    pre = blank_comments(t[:d[0][0]])
    use = re.search(r'\b%s\b' % re.escape(leaf), pre)
    if use and not decl_rx(leaf).search(pre):
        t = forward_declare(t, d[0][0], use.start(), t[d[0][0]:d[0][1]].rstrip() + ';')
    out[cpp] = t
    return out


def make_edit(leaf, old, new, oldpath, matched=frozenset()):
    """The edit for `leaf`: {relative path: text} -> {relative path: text}, or None.
    A caller named in `matched` (it matched in REV) gets its body from REV."""
    op, (oh, oi, oj) = old.one(leaf, oldpath)
    odef = old.texts[op][oh:oj]
    ohead = old.texts[op][oh:oi].rstrip()
    np_ = new.one(leaf)[0]

    def fn(texts):
        def cur(p):
            return out.get(p, texts.get(p, new.texts[p]))
        out = {}
        # The definition.
        t = cur(np_)
        d = defs(t).get(leaf, [])
        if len(d) != 1:
            return None
        h, _i, j = d[0]
        out[np_] = t[:h] + odef + t[j:]
        # The declarations.
        for p in new.paths:
            t = cur(p)
            if leaf not in t:
                continue
            olds = [m.group('head') for m in decl_rx(leaf).finditer(old.texts.get(p, ''))]

            def sub(m):
                if len(olds) == 1:
                    return olds[0] + ';'
                hd = m.group('head')
                indent = hd[:len(hd) - len(hd.lstrip())]
                stat = re.match(r'\s*static\b', hd) is not None
                return indent + ('static ' if stat else '') + re.sub(r'^\s*static\s+', '', ohead) + ';'
            t2 = decl_rx(leaf).sub(sub, t)
            if t2 != t:
                out[p] = t2
        # The calls.
        for p in new.paths:
            if not p.endswith('.cpp'):
                continue
            t = cur(p)
            if not re.search(r'\b%s\s*\(' % re.escape(leaf), t):
                continue
            pieces = []
            for caller, spans in defs(t).items():
                for (_ch, ci, cj) in spans:
                    sites = calls(t, leaf, ci, cj)
                    if not sites:
                        continue
                    o = old.one(caller, p)
                    if o is None:
                        continue
                    otext = old.texts[o[0]]
                    if caller in matched and caller != leaf and len(spans) == 1:
                        # It matched in REV: its body there, which fits the old prototype.
                        pieces.append((ci, cj, otext[o[1][1]:o[1][2]]))
                        continue
                    osites = calls(otext, leaf, o[1][1], o[1][2])
                    if len(osites) != len(sites):
                        continue
                    for (a, b), (oa, ob) in zip(sites, osites):
                        pieces.append((a, b, otext[oa:ob]))
            if pieces:
                s, last = [], 0
                for a, b, args in sorted(pieces):
                    if a < last:
                        continue
                    s += [t[last:a], args]
                    last = b
                s.append(t[last:])
                t2 = ''.join(s)
                if t2 != t:
                    out[p] = t2
        if re.match(r'\s*static\b', ohead):
            full = {p: cur(p) for p in new.paths}
            st = static_decls(full, np_, leaf)
            if st is None:
                return None
            out.update(st)
        return out
    return fn


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--only', default='', help='comma-separated function names to consider')
    ap.add_argument('rev')
    ap.add_argument('old_audit')
    ap.add_argument('patterns', nargs='*')
    args = ap.parse_args()
    rows = audit.load_funcmap(os.path.join(ORACLE, 'evidence', 'funcmap.tsv'))
    now = load_status(os.path.join(ORACLE, 'evidence', 'audit.tsv'))
    old_st = load_status(args.old_audit)
    old, new = Tree(args.rev), Tree()
    only = set(filter(None, args.only.split(',')))
    # Callers that matched in REV and do not here: their bodies come from REV.
    matched = frozenset({oname.rsplit('::', 1)[-1] for st, oname, _otu in old_st.values() if st == 'MATCH'} -
                        {name.rsplit('::', 1)[-1] for st, name, _tu in now.values() if st == 'MATCH'})
    targets = collections.defaultdict(set)          # leaf -> starts of the functions that matched
    oldpath = {}
    for s, (st, oname, otu) in old_st.items():
        if st != 'MATCH' or now.get(s, ('MATCH',))[0] == 'MATCH':
            continue
        if args.patterns and not any(p in otu for p in args.patterns):
            continue
        oleaf = oname.rsplit('::', 1)[-1]
        o = old.one(oleaf, otu + '.cpp')
        if o is None:
            continue
        body = old.texts[o[0]][o[1][1]:o[1][2]]
        for leaf in set(re.findall(r'\b(\w+)\s*\(', body)) | {oleaf}:
            if only and leaf not in only:
                continue
            prefer = otu + '.cpp' if leaf == oleaf else None
            oh = old.head(leaf, prefer)
            nh = new.head(leaf)
            if oh is None or nh is None or norm(oh) == norm(nh):
                continue
            targets[leaf].add(s)
            if prefer:
                oldpath[leaf] = prefer
    print('%d prototypes differ under %d functions that matched' % (
        len(targets), len(set().union(*targets.values())) if targets else 0), flush=True)
    for leaf in sorted(targets):
        print('  %-40s %d: %s  ->  %s' % (leaf, len(targets[leaf]), norm(new.head(leaf))[:100],
                                         norm(old.head(leaf, oldpath.get(leaf)))[:100]))
    if not args.apply:
        return 0
    _ref, model = audit.load_context()
    syms = audit.sym_map(rows)
    quarantined = audit.load_quarantine(os.path.join(BUILD, 'quarantine.tsv'))
    tu_of = {r[0]: r[3] for r in rows}
    name_of = {r[0]: r[2] for r in rows}
    start_of = collections.defaultdict(set)
    for s, name in name_of.items():
        start_of[name.rsplit('::', 1)[-1]].add(s)
    callee = {leaf: start_of.get(leaf, set()) for leaf in targets}
    callers = callers_of(model, set().union(*callee.values()) if callee else set(), set(tu_of))
    edits, paths = [], set()
    for leaf in sorted(targets):
        fn = make_edit(leaf, old, new, oldpath.get(leaf), matched)
        touched = fn(dict(new.texts)) or {}
        if not touched:
            continue
        owners = callee[leaf] | targets[leaf]
        aff = set(owners)
        for c in callee[leaf]:
            aff |= callers[c]
        e = fixlib.Edit(leaf, owners, aff,
                        (lambda f: lambda texts: (lambda r: None if r is None else
                                                  {os.path.join(REPO, k): v for k, v in r.items()})(
                            f({os.path.relpath(k, REPO): v for k, v in texts.items()})))(fn),
                        excused_by_match=True)
        e.tus = ({p[:-4] for p in touched if p.endswith('.cpp')} | {tu_of[x] for x in aff if x in tu_of})
        edits.append(e)
        paths |= {os.path.join(REPO, p) for p in touched}
    pats = sorted(set().union(*(e.tus for e in edits)) if edits else set())
    print('%d edits over %d files, judged in %d TUs' % (len(edits), len(paths), len(pats)), flush=True)

    def remap():
        # A changed prototype renames the symbol: the function of the same name stands for the original.
        for tu in pats:
            if not os.path.exists(os.path.join(BUILD, 'obj', tu + '.obj')):
                continue
            byname = collections.defaultdict(list)
            for f in ourslib.load_object(os.path.join(BUILD, 'obj'), tu + '.obj'):
                byname[f.name].append(f.symbol)
            for s, t in tu_of.items():
                if t == tu and len(byname.get(name_of[s], [])) == 1:
                    syms[byname[name_of[s]][0]] = s

    failed_before = build_all()                 # the baseline must be current
    base = check.judge(rows, pats, model, syms, quarantined)
    pristine = {p: fixlib.read(p) for p in paths}
    active = list(edits)
    state = None
    for rnd in range(ROUNDS):
        active = fixlib.materialise(pristine, active)
        if not active:
            break
        failed = build_all() - failed_before
        remap()
        state = check.judge(rows, pats, model, syms, quarantined)
        lost = (fixlib.matches(base) - fixlib.matches(state)) | fixlib.vanished(base, state)
        won = fixlib.matches(state) - fixlib.matches(base)
        tus_of = {e.label: set(e.tus) for e in active}
        unclaimed = fixlib.claim_failed(active, tus_of, failed)
        bad = [e for e in active if tus_of[e.label] & failed or e.affects & lost
               or (fixlib.worse(base, state, e.owners) and not e.affects & won)]
        print('round %d: %d edits, %d TUs failed (%d unclaimed), %d lost, %d won, %d to drop' % (
            rnd + 1, len(active), len(failed), len(unclaimed), len(lost), len(won), len(bad)), flush=True)
        for e in bad:
            print('  drop %s' % e.label, flush=True)
        if (lost and not any(e.affects & lost for e in bad)) or unclaimed:
            active = []
        if not bad and not failed and active:
            break
        active = [e for e in active if e not in bad]
        state = None
    if state is None:
        fixlib.materialise(pristine, [])
        build_all()
        print('kept 0 of %d edits' % len(edits))
        fixlib.record('fix_callsig', len(edits), 0, 0, 'prototypes from %s' % args.rev)
        return 0
    gained = len(fixlib.matches(state) - fixlib.matches(base))
    check.update_rows(state)
    for e in active:
        print('  kept %s' % e.label)
    print('kept %d of %d edits, MATCH %+d' % (len(active), len(edits), gained))
    fixlib.record('fix_callsig', len(edits), len(active), gained, 'prototypes from %s' % args.rev)
    return 0


if __name__ == '__main__':
    sys.exit(main())

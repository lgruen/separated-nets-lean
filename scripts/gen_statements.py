#!/usr/bin/env python3
"""Stage 13c: generate the unified statement library `QUNets/Statements/*.lean`, the roots
`ChallengeAll.lean`, `SolutionAll.lean` and the single configuration `comparatorAll.json` from the
thirteen stage-9 entries (`Challenge*.lean`, `comparator*.json`).

* Every compared theorem is copied **verbatim** (its docstring and its full text, proof `sorry`)
  from its current Challenge file, inside the same namespace and with the same `open`s as there.
* Definitions are not copied: each statement file imports the proof-side `*Defs` modules that
  define the definitions of the Challenge files its theorems come from, so Challenge and Solution
  see the same constants from the same `.olean`.
* Section of a theorem: the paper section (`core.tex`) of its first label in the per-theorem map of
  `STATEMENTS_INDEX.md`; within a file, theorems are ordered by the position of that label in the
  paper, ties by the order of the former entries and the Challenge files, grouped into one block
  per (namespace, `open`s) context.

Usage: python3 scripts/gen_statements.py   (from the Lean project (repository root); idempotent)
A one-shot migration tool: it reads the stage-9 Challenge files, which stage 13f retires.
"""
import collections
import glob
import json
import os
import re
import sys

L = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAPER = os.path.join(L, '..', 'paper', 'core.tex')
ENTRIES = ['main', 'Eis', 'F', 'Half', 'KNPP', 'Dim34', 'HLHL8', 'SkelS1E', 'S2T3S4', 'ObsWhyLat',
           'PPInvU', 'SplitS1E1', 'S5R2TC']
ERDER = {e: i for i, e in enumerate(ENTRIES)}


def chal(e):
    return os.path.join(L, 'Challenge' + ('' if e == 'main' else e) + '.lean')


def conf(e):
    return os.path.join(L, 'comparator' + ('' if e == 'main' else e) + '.json')


# ---------------------------------------------------------------- paper sections
# (first line, last line, file) of core.tex, by the section structure of revision 13.5
FILES = {
    'Prelim': ('sec:prelim', 'Graph forms, layers and lattices (incl. `sec:whylat`)'),
    'Frames': ('sec:frames', 'Frames: `t = 0` for free'),
    'Small3': ('sec:small', 'Small-entry layers, dimension three (`sec:construction`, `sec:sep`, '
                            '`sec:ceil`, `sec:two`)'),
    'Small4': ('sec:dim4ex', 'Small-entry layers, dimension four'),
    'SmallS': ('sec:dims', 'Small-entry layers, every dimension (incl. the deficit bounds)'),
    'Skeleton': ('sec:skel', 'Lattice skeletons (`sec:fine` up to two skeleton coordinates)'),
    'Skeleton3': ('sec:allm', 'Lattice skeletons in dimension three, three or more skeleton '
                              'coordinates, every resolution in dimension three'),
    'Large': ('sec:large', 'Large-entry layers: the reflected cube, shared rows, two cosets '
                           '(`sec:twocoset`)'),
    'Eisenstein': ('sec:eis', 'Large-entry layers: Eisenstein nets'),
    'Split': ('sec:large', 'Large-entry layers: half-integer layers, the split frame, separation '
                           'with carries, every resolution, searched designs'),
    'Appendix': ('app:designs', 'Appendices (`app:designs`, `app:perprime`, `app:proofs`, '
                                '`app:tables`)'),
}
ORDER = list(FILES)


def section_ranges(lines):
    """map the paper's section/subsection labels to statement files by line ranges"""
    def find(pat):
        for i, ln in enumerate(lines, 1):
            if pat in ln:
                return i
        raise SystemExit('paper anchor not found: ' + pat)
    a = {
        'Prelim': find(r'\label{sec:prelim}'),
        'Frames': find(r'\label{sec:frames}'),
        'Small3': find(r'\label{sec:small}'),
        'Small4': find(r'\label{sec:dim4ex}'),
        'SmallS': find(r'\label{sec:dims}'),
        'Skeleton': find(r'\label{sec:skel}'),
        'Skeleton3': find(r'\label{sec:allm}'),
        'Large': find(r'\label{sec:large}'),
        'Eisenstein': find(r'\label{sec:eis}'),
        'Large2': find(r'\subsection{Shared rows}'),
        'Split': find(r'\subsection{Half-integer layers}'),
        'Appendix': find(r'\label{sec:formal}'),
    }
    seq = sorted(a.items(), key=lambda kv: kv[1])
    rng = [(1, seq[0][1] - 1, 'INTRO')]
    for i, (k, v) in enumerate(seq):
        end = seq[i + 1][1] - 1 if i + 1 < len(seq) else 10 ** 9
        rng.append((v, end, 'Large' if k == 'Large2' else k))
    return rng


# results stated in the introduction: the section of their proof
INTRO = {'thm:main': 'Small3', 'prop:A': 'Small3', 'cor:allm': 'Skeleton3', 'thm:U': 'SmallS',
         'thm:S1': 'Skeleton', 'thm:HL': 'Split'}
# compared theorems whose per-theorem map row cites no label
OVERRIDE = {'Z3NetHL.half5_threshold': 'Split', 'Z3NetHL.half5_main': 'Split',
            'Z3NetF.frameGraphK_spec': 'Skeleton', 'Z3NetF.skel_graphGen': 'Skeleton'}

LBL = re.compile(r'\b((?:thm|prop|lem|cor|def|rem|tab|eis|app|sec)[:][A-Za-z0-9]+)')


def paper_labels():
    lines = open(PAPER).read().split('\n')
    rng = section_ranges(lines)
    where = {}
    for no, ln in enumerate(lines, 1):
        for lab in re.findall(r'\\label\{([^}]*)\}', ln):
            sec = [r for a, b, r in rng if a <= no <= b][0]
            if sec == 'INTRO':
                sec = INTRO.get(lab, 'INTRO')
            where[lab] = (sec, no)
    return where


def theorem_labels(cfg):
    txt = open(os.path.join(L, 'STATEMENTS_INDEX.md')).read().split('\n')
    lab = collections.defaultdict(list)
    ns = None
    for ln in txt:
        m = re.match(r'^### .*namespace `([^`]+)`', ln)
        if m:
            ns = m.group(1)
            continue
        if ln.startswith('## '):
            ns = None
        if ln.startswith('|') and not ln.startswith('|---'):
            cells = [c.strip() for c in ln.strip().strip('|').split('|')]
            if len(cells) < 2:
                continue
            if len(cells) >= 3 and cells[1].startswith('`') and '.' in cells[1]:
                names = re.findall(r'`([^`]+)`', cells[1])
                paper = ' '.join(cells[2:])
            else:
                names = re.findall(r'`([^`]+)`', cells[0])
                paper = ' '.join(cells[1:])
            for n in names:
                full = n if (ns is None or n.startswith(ns + '.')) else ns + '.' + n
                if full in cfg:
                    for x in LBL.findall(paper):
                        if x not in lab[full]:
                            lab[full].append(x)
    return lab


# ---------------------------------------------------------------- Lean parsing
def top_items(lines):
    """top-level items (start, end) outside block comments; comment blocks at column 0 are items"""
    items = []
    depth = 0
    for i, ln in enumerate(lines):
        if depth == 0 and ln and not ln[0].isspace():
            items.append(i)
        j = 0
        while j < len(ln):
            if ln.startswith('/-', j):
                depth += 1
                j += 2
                continue
            if ln.startswith('-/', j) and depth > 0:
                depth -= 1
                j += 2
                continue
            if ln.startswith('--', j) and depth == 0:
                break
            j += 1
    out = []
    for k, s in enumerate(items):
        e = items[k + 1] if k + 1 < len(items) else len(lines)
        while e > s + 1 and not lines[e - 1].strip():
            e -= 1
        out.append((s, e))
    return out


DECL = re.compile(r'^(?:(?:private|protected|noncomputable)\s+)*(def|abbrev|structure|theorem)\s+'
                  r'([^\s:({\[]+)')


def parse_challenge(e):
    lines = open(chal(e)).read().split('\n')
    ns = []
    opens = []
    thms = []
    defs = []
    prev = None
    for (s, t) in top_items(lines):
        ln = lines[s]
        m = re.match(r'^namespace\s+(\S+)\s*$', ln)
        if m:
            ns.append(m.group(1))
            opens.append([])
            prev = None
            continue
        m = re.match(r'^end\s+(\S+)\s*$', ln)
        if m:
            assert ns and ns[-1] == m.group(1), (e, s, ln)
            ns.pop()
            opens.pop()
            prev = None
            continue
        if ln.startswith('open '):
            assert t == s + 1, (e, s)
            opens[-1].append(ln)
            prev = None
            continue
        m = DECL.match(ln)
        if m:
            full = '.'.join(ns + [m.group(2)])
            if m.group(1) == 'theorem':
                doc = None
                if prev is not None and lines[prev[0]].startswith('/--') and prev[1] == s:
                    doc = '\n'.join(lines[prev[0]:prev[1]])
                body = '\n'.join(lines[s:t])
                thms.append(dict(name=full, entry=e, ns='.'.join(ns),
                                 opens=tuple(o for lv in opens for o in lv),
                                 doc=doc, body=body, pos=s))
            else:
                defs.append(full)
            prev = None
            continue
        prev = (s, t)
    assert not ns, e
    return thms, defs


def def_index():
    """fully qualified definition name -> proof-side module (Z3Net/**, EisensteinNet/**)"""
    idx = {}
    # V14 stage S16′: `EisensteinNet/` became `QUNetsM3/` (live) and the retired Eisenstein development (research history) (retired)
    for f in sorted(glob.glob(L + '/Z3Net/**/*.lean', recursive=True) +
                    glob.glob(L + '/QUNetsM3/**/*.lean', recursive=True) +
                    glob.glob(L + '/the retired material (research history)**/*.lean', recursive=True)):
        mod = os.path.relpath(f, L)[:-5].replace('/', '.')
        ns = []
        for ln in open(f):
            m = re.match(r'^namespace\s+(\S+)', ln)
            if m:
                ns.append(m.group(1))
                continue
            m = re.match(r'^end\s+(\S+)', ln)
            if m and ns and ns[-1] == m.group(1):
                ns.pop()
                continue
            m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                         r'(def|abbrev|structure|inductive)\s+([^\s:({\[]+)', ln)
            if m:
                idx.setdefault('.'.join(ns + [m.group(2)]), []).append(mod)
    return idx


HEADER = '''/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`). Results are cited by their `\\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
'''


def main():
    cfg = {}
    for e in ENTRIES:
        for t in json.load(open(conf(e)))['theorem_names']:
            assert t not in cfg, t
            cfg[t] = e
    where = paper_labels()
    lab = theorem_labels(cfg)
    idx = def_index()
    thms = {}
    entry_mods = {}
    for e in ENTRIES:
        ts, ds = parse_challenge(e)
        for t in ts:
            assert t['name'] not in thms, t['name']
            thms[t['name']] = t
        mods = set()
        for d in ds:
            ms = idx.get(d)
            if not ms or len(ms) != 1:
                raise SystemExit(f'definition {d} of Challenge {e}: proof-side modules {ms}')
            if not re.search(r'Defs\d*$', ms[0]):
                raise SystemExit(f'definition {d} of Challenge {e} lives in {ms[0]}, not a *Defs module')
            mods.add(ms[0])
        entry_mods[e] = mods
    assert set(thms) == set(cfg), (set(thms) ^ set(cfg))
    # sections
    for n, t in thms.items():
        if n in OVERRIDE:
            t['file'] = OVERRIDE[n]
            first = [x for x in lab.get(n, []) if x in where]
            t['key'] = where[first[0]][1] if first else 10 ** 8
            continue
        first = [x for x in lab.get(n, []) if x in where and where[x][0] != 'INTRO']
        if not first:
            raise SystemExit(f'no paper section for {n}: labels {lab.get(n)}')
        t['file'], t['key'] = where[first[0]][0], where[first[0]][1]
        t['label'] = first[0]
    out_dir = os.path.join(L, 'QUNets', 'Statements')
    os.makedirs(out_dir, exist_ok=True)
    allnames = []
    report = []
    for f in ORDER:
        ts = sorted((t for t in thms.values() if t['file'] == f),
                    key=lambda t: (t['key'], ERDER[t['entry']], t['pos']))
        # one block per (namespace, opens) context; blocks in the order of their first theorem
        first = {}
        for i, t in enumerate(ts):
            first.setdefault((t['ns'], t['opens']), i)
        ts = sorted(ts, key=lambda t: first[(t['ns'], t['opens'])])
        if not ts:
            continue
        mods = sorted(set().union(*(entry_mods[t['entry']] for t in ts)))
        entries = sorted({t['entry'] for t in ts}, key=ERDER.get)
        secl, title = FILES[f]
        body = [HEADER.rstrip('\n')]
        body += ['public import ' + m for m in mods]
        body += ['', '@[expose] public section', '']
        body += ['/-!',
                 f'# Statements: {title}',
                 '',
                 f'Paper section `{secl}` (the section of the first label of each theorem in the per-theorem',
                 'map of `STATEMENTS_INDEX.md`). The compared theorems below are verbatim copies (statement,',
                 'docstring, namespace, `open`s) of those of the stage-9 Challenge files of the entries',
                 ', '.join(f'`{e}`' for e in entries) + ', with proof `sorry`; within each namespace block',
                 'they are ordered by the position of that label in the paper. The definitions are not',
                 'copied: they are imported',
                 'from the proof-side `*Defs` modules above, so the Challenge root `ChallengeAll` and the',
                 'Solution root `SolutionAll` share the same constants. Generated by `scripts/gen_statements.py`.',
                 '-/', '']
        cur = None
        for t in ts:
            ctx = (t['ns'], t['opens'])
            if ctx != cur:
                if cur is not None:
                    body += [f'end {cur[0]}', '']
                body += [f'namespace {t["ns"]}', '']
                if t['opens']:
                    body += list(t['opens']) + ['']
                cur = ctx
            if t['doc']:
                body.append(t['doc'])
            body += [t['body'], '']
            allnames.append(t['name'])
        body += [f'end {cur[0]}', '']
        txt = '\n'.join(body)
        open(os.path.join(out_dir, f + '.lean'), 'w').write(txt)
        report.append((f, len(ts), txt.count('\n'), len(txt.encode()), mods))
    assert len(allnames) == len(cfg) == len(set(allnames))
    # Challenge root
    ch = [HEADER.rstrip('\n')]
    ch += [f'public import QUNets.Statements.{f}' for f, *_ in report]
    ch += ['', '@[expose] public section', '', '/-!',
           '# Challenge (all compared theorems)',
           '',
           f'The {len(cfg)} compared theorems of the project, in the statement library',
           '`QUNets/Statements/*.lean` (one file per paper section; definitions imported from the',
           'proof-side `*Defs` modules). Comparator configuration: `comparatorAll.json`.',
           'Generated by `scripts/gen_statements.py`.',
           '-/', '']
    open(os.path.join(L, 'ChallengeAll.lean'), 'w').write('\n'.join(ch))
    # Solution root: the union of the imports of the thirteen Solution roots
    simps = []
    for e in ENTRIES:
        for ln in open(os.path.join(L, 'Solution' + ('' if e == 'main' else e) + '.lean')):
            m = re.match(r'^public import (\S+)', ln)
            if m and m.group(1) not in simps:
                simps.append(m.group(1))
    so = [HEADER.rstrip('\n')]
    so += [f'public import {m}' for m in simps]
    so += ['', '@[expose] public section', '', '/-!',
           '# Solution (all compared theorems)',
           '',
           'The proof modules restating the compared theorems of `ChallengeAll.lean` by name (the',
           'union of the imports of the thirteen stage-9 Solution roots). Generated by',
           '`scripts/gen_statements.py`.',
           '-/', '']
    so += [f'#print axioms {n}' for n in allnames] + ['']
    open(os.path.join(L, 'SolutionAll.lean'), 'w').write('\n'.join(so))
    json.dump({'challenge_module': 'ChallengeAll', 'solution_module': 'SolutionAll',
               'theorem_names': allnames, 'definition_names': [],
               'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
               'enable_nanoda': True}, open(os.path.join(L, 'comparatorAll.json'), 'w'), indent=2)
    open(os.path.join(L, 'comparatorAll.json'), 'a').write('\n')
    tot = 0
    for f, n, nl, nb, mods in report:
        tot += nl
        print(f'{f:11s} {n:4d} theorems {nl:6d} lines {nb / 1024:6.1f} KiB  imports {len(mods)}')
    print('total', len(allnames), 'theorems', tot, 'lines')


if __name__ == '__main__':
    sys.exit(main())

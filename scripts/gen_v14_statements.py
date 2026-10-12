#!/usr/bin/env python3
"""V14 stage S0 (the research notes): retire, hold and re-section the statement library for paper
revision 14.3 (`paper/core.tex`, "Low-discrepancy quasi-uniform digital nets in every
dimension").

Input (read from git at the fixed commit BASE, so the script is idempotent after the 13-entry files
are deleted): the stage-13c library `QUNets/Statements/*.lean`, the per-theorem map of
`STATEMENTS_INDEX.md`, the thirteen stage-9 Challenge files and configurations (only to find the
`*Defs` modules each theorem's definitions come from) and `SolutionAll.lean`; and the current
`core.tex` (labels and section positions of rev 14.3).

Output: `QUNets/Statements/{Prelim,Frames,ThmA,Skeleton,Dim3,Base23,DGS,Deficit,WhyLat,Large,Split,
Appendix}.lean` (until stage S9′ also `Hold.lean`), the roots `Challenge.lean`, `Solution.lean` and the
one configuration `comparator.json`.

* Every kept or held theorem is copied **verbatim** (docstring, text, namespace, `open`s; proof
  `sorry`) from the BASE library. Definitions are imported from the proof-side `*Defs` modules.
* RETIRE (below, with reasons): dropped from the library, the configuration and the Solution's
  `#print axioms` (their proofs stay in the proof trees; git history keeps the statements).
* HOLD (below): the m = 3 material under redesign (Eisenstein nets, `prop:shared`, `thm:E1`/𝓔_p,
  `thm:two`/𝒬_{k,q}); kept, compiled and compared, in the holding file `Hold.lean`, in their
  BASE order — from stage S0 to stage S8. Stage S9′ retired the whole holding section (RETIRE,
  reasons `_RE1`, `_REIS`, `_RQ`, `_RSH`); HOLD is empty and `Hold.lean` is no longer generated.
* Section of a kept theorem: the rev-14.3 paper section of its first live result label in the
  per-theorem map (labels of sections/appendices only if it has no live result label); theorems
  whose labels were all removed but whose content the paper still claims are placed by SUBST.

Usage (from the repository root): uv run --no-project python scripts/gen_v14_statements.py
"""
import collections
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_statements as G  # noqa: E402  (parsing helpers of stage 13c)
import v14_delta as D  # noqa: E402  (statements changed or added after stage S1)
import v16_rename as R  # noqa: E402  (the legacy rename of stage S16′)

L = G.L
PAPER = os.environ.get('QUNETS_CORE_TEX', os.path.join(L, 'paper', 'core.tex'))  # override: a copy of the committed core.tex
BASE = 'd158b02286322eb237eb1df90f08dafb9f65b293'  # S0 starting point (13c library, 13 entries)
REL = ''
TITLE = 'Low-discrepancy quasi-uniform digital nets in every dimension'
REV = 'revision 15.2'

OLD_FILES = ['Prelim', 'Frames', 'Small3', 'Small4', 'SmallS', 'Skeleton', 'Skeleton3', 'Large',
             'Eisenstein', 'Split', 'Appendix']

# ------------------------------------------------------------------ retirement (S0) with reasons
_R4D = ('`thm:4D` (net 𝒫⁴ of design A) removed in rev 14.1, replaced by `prop:4D2`; parked in '
        '`paper/parked/partII_appendices_rev14.0.tex`')
_RN4 = ('instance of `{lab}` for the removed four-dimensional net of `thm:4D` (`def:N4`); the general '
        'form stays compared (`{gen}`)')
_RAS = ('`prop:4DK2` (design A♯ over ℤ[1/10]) removed in rev 14.1, replaced by `prop:4D2`; the prose '
        'no longer claims it (W10, rev 14.2)')
_RS5 = ('`prop:s5r2`, `tab:s5r2` removed in rev 14.0 (parked C3, `paper/parked/C3_skeletons_ell3.tex`); '
        'rev 14.3 mentions the seven s = 5 designs only as "computed; not printed"')
_RD4 = ('`cor:dim4` removed in rev 14.0 (parked C3); rev 14.3 keeps only `prop:korobov4` (p = 13) and '
        'calls the other dimension-four per-prime nets computed')
_RB8 = ('s = 8 split-frame design: its appendix was removed in rev 14.1 and the dimension-eight sentence '
        'of `sec:halfms` in rev 14.3 (`thm:HL` carries the E₈ limit)')
_RH68 = ('rows s = 6, 8 of the removed `tab:half`; rev 14.3 prints only the s = 5 layer (`prop:half5`); '
         'retired in S1 (orchestrator decision on V14_PLAN §9.4 item 1)')
RETIRE = {
    'Z3NetD4.D4_boxMinor': _R4D, 'Z3NetD4.D4_net': _R4D, 'Z3NetD4.D4_covering': _R4D,
    'Z3NetD4.D4_sep': _R4D, 'Z3NetD4.D4_sep_real': _R4D,
    'Z3NetD4.c4_expansion': _R4D + ' (the expansion of c₄)',
    'Z3NetD4.D4_relax_value': ('`prop:C4` (relaxation value of design A) removed in rev 14.1; its '
                               '`lem:Ss` link is an instance on the removed design A'),
    'Z3NetD4.D4_defN': _RN4.format(lab='def:Ns', gen='tsk_unit, tsk_net, U_defN'),
    'Z3NetD4.D4_propN': _RN4.format(lab='prop:Ns', gen='Ns_row0, U_propN'),
    'Z3NetD4.D4_propG': _RN4.format(lab='prop:Gs', gen='Gs_beta, Gs_gauge, Gs_row0, U_propG'),
    **{f'Z3NetF.{n}': _RAS for n in ['As_residual', 'As_unit', 'As_net', 'As_sep', 'As_covering',
                                     'As_upper', 'As_two_sided']},
    **{f'Z3NetF.{n}': _RS5 for n in ['s5r2_table', 's5r2_reach', 's5r2_net', 's5r2_sep',
                                     's5r2_sep_real', 's5r2_sepJ', 's5r2_sepJ_real', 's5r2_M',
                                     's5r2_J', 's5r2_lat', 's5r2_tab', 's5r2_main']},
    **{f'Z3NetF.{n}': _RD4 for n in ['dim4', 'dim4_one', 'dim4_full']},
    **{f'Z3NetHL.{n}': _RB8 for n in ['B8_design', 'B8_dom', 'B8_net', 'B8_main', 'B8_limit',
                                      'B8_sep_real']},
    # S1 housekeeping (orchestrator decision on V14_PLAN §9.4 item 1): Half statements about s = 6, 8 only
    **{f'Z3NetHL.{n}': _RH68 for n in ['half6_tab_sep', 'half8_tab_sep', 'half68_lam', 'half_tab_t0']},
}

# ------------------------------------------------------------------ V14 stage S9′: the former holding section retired
# (author decisions; the research notes). Their proofs stay in the proof trees (`EisensteinNet/`, `Z3Net/NetQ*.lean`,
# `Z3Net/CellRowsS11.lean`, `Z3Net/Q9ValueS12.lean`, `Z3Net/ObsShared.lean`); the E1 lemmas (`EisensteinNet/E1Net.lean`,
# `E1Sep.lean`) are used by the proof of `prop:twocoset` (`EisensteinNet/TC*.lean`) as non-compared library lemmas.
_RE1 = ('`thm:E1` / 𝓔_p, `prop:E1free`, `prop:E1shift` and the former `rem:E1exact`: removed in rev 15.0 (replaced '
        'by the column nets, `thm:col`, `prop:colfree`, `prop:colshift`; parked in '
        '`paper/parked/rev14.3_removed_for_15.0.tex`); retired in S9′')
_REIS = ('Eisenstein nets (`sec:eis`): removed in rev 14.0, no spin-out (author decision); retired in S9′')
_RQ = ('`thm:two` / 𝒬_{k,q} with `prop:Qnet`, `prop:rows`, `cor:rows`, `rem:q11` (`sec:two`, parked C2): not in '
       'rev 15.0 (author decision: parked); nothing live uses `frame_rows`; retired in S9′')
_RSH = ('`prop:shared` (spun out with C1): not in rev 15.0; `lem:shared` of `sec:m3` is a different statement (the '
        'box count, digital or not), formalized in S9′ (`Z3NetC.shared_count`, `shared_fun`); retired in S9′')
RETIRE.update({
    **{f'EisensteinNet.{n}': _RE1 for n in ['E1_freeJitter', 'E1_params', 'E1_net', 'E1_sep', 'E1_sep_real', 'cE1_tendsto', 'E1_mono', 'E1_gt874', 'E1_mindist_p5', 'E1_mindist_p7']},
    **{f'EisensteinNet.{n}': _REIS for n in ['cubeRoot_exists_iff_field', 'cEis_bounds', 'mindist_exact_real', 'isNet033_iff_field', 'order3_field', 'order3', 'net_iff', 'net_iff_field', 'net_closedForm_field', 't0_count_field', 'net_closedForm', 'digit_identities', 'gauge_digits', 'gauge_move', 'gauge_sep', 'gauge_graph', 'distance_lower_sharp', 'sharp_equality', 'distance_witness', 'mindist_exact', 'cEis_tendsto', 'exact_six', 'split', 'split_diag', 'split_counts', 'split_proj', 'split_field', 'split_diag_field', 'split_sites', 'split_torus', 'larger_bound', 'liminf_ge_one', 'larger_iff', 'larger_primes', 'mindist_p7', 'mindist_p7_smallRoot', 'mindist_p13', 'distance_lower', 'lower_gen', 'lower_cex', 'cover_mesh', 'cover_bound_tendsto']},
    **{f'Z3Net.{n}': _RQ for n in ['Q_net', 'Q_sep', 'Q_sep_real', 'Q_boxMinor_pow_two', 'Q_net_odd', 'Q_sep_odd', 'Q_sep_real_odd', 'Q_sep_ge11', 'Q_sep_real_ge11', 'cQ_expansion', 'frame_rows', 'Q_boxMinor_value', 'Q_not_net_even', 'Q2_net', 'Q_rows', 'Q9_witness', 'Q9_witness_value']},
    **{f'Z3NetF.{n}': _RSH for n in ['shared_row', 'shared_only']},
})

# ------------------------------------------------------------------ V14 stage S11′: the former Half entry (the layer M₅)
_RM5 = ('the layer M₅ of the removed `prop:half`/`tab:half` (rows s = 5, 6, 8): rev 15.0 replaced it by the layer '
        '`F₀*` of `prop:half5` (𝒬*, formalized in S11′); M₅ appears only in `rem:M5` with computed values; nothing '
        'live uses these statements; retired in S11′')
RETIRE.update({f'Z3NetHL.{n}': _RM5 for n in ['half_tab_LB2', 'half5_tab_sep', 'half5_lam', 'half5_net',
                                              'half5_threshold', 'half5_main']})

# ------------------------------------------------------------------ HOLD (m = 3 redesign)
_HE = 'Eisenstein nets (`sec:eis`, spun out in rev 14.0; may return as an appendix)'
_HE1 = '`thm:E1` / 𝓔_p (m = 3 material under redesign)'
_HQ = '`thm:two` / 𝒬_{k,q} (`sec:two`, parked C2; m = 3 material under redesign)'
_HS = '`prop:shared` (spun out with C1; m = 3 material under redesign)'
HOLD_GROUPS = []  # V14 stage S9′: the holding section is retired (above); the reasons `_HE` … `_HS` are kept as a record


# ------------------------------------------------------------------ kept, all labels removed
# name prefix -> (substitute live label that still claims the content, reason)
SUBST = [
    ('Z3NetU.U_', 'rem:Us', '`thm:U` was replaced by `thm:A`; `rem:Us` still claims the U_s theorem '
                            '(net, separation, sharpness, a_s bounds, Chebyshev/PNT growth)'),
    ('Z3NetHL.half', 'prop:half5', '`prop:half`/`tab:half` removed in rev 14.1; rev 14.3 prints '
                                   '`prop:half5` (Lean entry Half)'),
    ('Z3NetF.t3s4_', 'prop:korobov4', '`prop:t3s4`/`tab:t3s4` removed; rev 14.3 prints '
                                      '`prop:korobov4`, the design t3d13 of these statements'),
    ('Z3NetF.frameGraphK_spec', 'prop:skelcomp', 'skeleton infrastructure (no label in the map)'),
    ('Z3NetF.skel_graphGen', 'prop:skelcomp', 'skeleton infrastructure (no label in the map)'),
]

# ------------------------------------------------------------------ new files (rev 14.3 sections)
FILES = collections.OrderedDict([
    ('Prelim', ('sec:prelim', 'Graph forms and the one-digit relaxation')),
    ('Frames', ('sec:frames', 'Frames: `t = 0` for free (incl. the Cauchy identities)')),
    ('ThmA', ('sec:dims', 'Cubic cells, `m ≡ 0 (mod s)`: lattice designs (Theorem A, `prop:D`, '
                          'the design `U_s` of `rem:Us`)')),
    ('Skeleton', ('sec:skel', 'Lattice skeletons, `m = sk + r` (incl. `prop:korobov4`)')),
    ('Dim3', ('sec:dim3', 'Dimension three, every resolution')),
    ('Base23', ('sec:base23', 'Bases two and three: the deep-shift lift')),
    ('DGS', ('sec:dgs', 'The question of Dick, Goda and Suzuki')),
    ('Deficit', ('sec:deficit', 'The first-order deficit, why it grows with the dimension, drift and jitter '
                                '(`sec:deficit`, `sec:deficitgrowth`, `sec:drift`)')),
    ('WhyLat', ('sec:whylat', 'One point per cube: cube tilings and the value 1')),
    ('Large', ('sec:large', 'Beyond the cubic value: Euclidean skeletons and the layer of two cosets '
                            '(`sec:S1E`, `sec:twocoset`)')),
    ('Split', ('sec:large', 'Beyond the cubic value: the frame orbit and half-integer layers, the '
                            'split frame, separation with carries, one resolution (`sec:halfms`)')),
    ('Appendix', ('app:designs', 'Appendices (`app:designs`, `app:proofs`, `app:perprime`, '
                                 '`app:tables`)')),
])
EMPTY_NOTE = {
    'Base23': ('Stage S14′: `def:lift` (definitions in `Z3Net/B23Defs.lean`), `lem:lift`, `lem:liftsep`, the '
               'every-shift lemma `lem:shiftcert` and `thm:base23` with part (3) '
               '(the nets in `Z3Net/B23Fam.lean`).'),
    'DGS': 'V14 stage S9′ added the `m = 3` constant of `cor:allmshift` (`Z3NetC.allmshift_m3`, the column net '
           '`𝒞_p` under every digital shift, with the minimal `def:dshift` of `Z3Net/DShiftDefs.lean`). V14 stage S10′ '
           'added `lem:shift`, `prop:shift` (every separation core listed there; namespaces `Z3NetF`, `Z3NetA`, `Z3Net`, '
           '`Z3NetS1`, `Z3NetKN`, `Z3NetHL`), the `m ≥ 4` part of `cor:allmshift`, the column-net sentence of '
           '`rem:shiftshared`, `cor:dgs`, `rem:dgsfinite` and `prop:linf` (namespace `Z3NetDGS`, the definitions of '
           'Dick, Goda and Suzuki in `Z3Net/DGSDefs.lean`; the statement-review notes (research repository)).',
    'ThmA': 'V14 stage S3 added Theorem A (1) and the lower bound of (2) for every `k ≥ 1`, with `a*_s` '
            'kept abstract, `lem:sat`, `def:Ustar`, reachability and dominance (namespace `Z3NetA`, '
            'definitions `Z3Net/ThmADefs.lean`); stage S4 added `lem:adelic`, `lem:babai` and the '
            'reduction of the bound on `a*_s` to the local bounds `h_{d,j} ≤ H` (definitions '
            '`Z3Net/ThmALatDefs.lean`), and, ahead of S5, the `s = 3` display after `def:Ustar` and '
            '`a*_3 = 2`; the local bounds, the bound on `a*_s` itself and the sharpness in (2) are † '
            '(V14_PLAN stage S5). The file also holds '
            '`prop:D` and the design `U_s` of `rem:Us` (formerly `thm:U`).',
    'Deficit': '`def:K`, `prop:Dprime`, `prop:k1` (1), (2) and the deficits `K₁` of the printed layers of '
               '`prop:k1designs` were added in V14 stage S2 (with the definitions of `Z3Net/DeficitDefs.lean`), '
               'the identification of the `s = 4` frame layer with the level-0 layer of `U*_4` in stage S4; '
               '`lem:O`, `prop:E`, `lem:C`, `thm:Lstar` (with `PGL₂(ℚ)`-images of the places) in stage S7 '
               '(definitions `Z3Net/LstarDefs.lean`); '
               '`prop:4D2`, `prop:k1`(3) in stage S8; `lem:Kone` and `sec:drift` (`lem:drift`, `cor:colceil`, '
               '`thm:O`) in stage S9′ (definitions `Z3Net/ColDefs.lean`); the rest of `prop:k1designs` (`t = 0` '
               'completions, scans) is † (V14_PLAN stage S10).',
}

HEADER = f'''/-
Paper: L. Gruenschloss, "{TITLE}"
({REV}; LaTeX source `paper/core.tex`).
Results are cited by their `\\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
'''


def git_show(path):
    return subprocess.run(['git', 'show', f'{BASE}:{REL}{path}'], cwd=L, check=True,
                          capture_output=True, text=True).stdout


def parse_text(text, tag):
    """theorems/definitions of a Lean file, as `gen_statements.parse_challenge` (from text)"""
    lines = text.split('\n')
    ns, opens, thms, defs, prev = [], [], [], [], None
    for (s, t) in G.top_items(lines):
        ln = lines[s]
        m = re.match(r'^namespace\s+(\S+)\s*$', ln)
        if m:
            ns.append(m.group(1)); opens.append([]); prev = None
            continue
        m = re.match(r'^end\s+(\S+)\s*$', ln)
        if m:
            assert ns and ns[-1] == m.group(1), (tag, s, ln)
            ns.pop(); opens.pop(); prev = None
            continue
        if ln.startswith('open '):
            opens[-1].append(ln); prev = None
            continue
        m = G.DECL.match(ln)
        if m:
            full = '.'.join(ns + [m.group(2)])
            if m.group(1) == 'theorem':
                doc = None
                if prev is not None and lines[prev[0]].startswith('/--') and prev[1] == s:
                    doc = '\n'.join(lines[prev[0]:prev[1]])
                thms.append(dict(name=full, src=tag, ns='.'.join(ns),
                                 opens=tuple(o for lv in opens for o in lv),
                                 doc=doc, body='\n'.join(lines[s:t]), pos=s))
            else:
                defs.append(full)
            prev = None
            continue
        prev = (s, t)
    assert not ns, tag
    return thms, defs


def base_labels(names):
    """per-theorem map of STATEMENTS_INDEX.md at BASE (as `gen_statements.theorem_labels`)"""
    lab = collections.defaultdict(list)
    ns = None
    for ln in git_show('STATEMENTS_INDEX.md').split('\n'):
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
                nn = re.findall(r'`([^`]+)`', cells[1]); paper = ' '.join(cells[2:])
            else:
                nn = re.findall(r'`([^`]+)`', cells[0]); paper = ' '.join(cells[1:])
            for n in nn:
                full = n if (ns is None or n.startswith(ns + '.')) else ns + '.' + n
                if full in names:
                    for x in G.LBL.findall(paper):
                        if x not in lab[full]:
                            lab[full].append(x)
    return lab


def paper_positions():
    """label -> (new file, line) for rev 14.3"""
    lines = open(PAPER).read().split('\n')

    def find(pat, alt=None):
        for i, ln in enumerate(lines, 1):
            if pat in ln:
                return i
        if alt is not None:  # the heading was renamed in rev 15.7
            return find(alt)
        raise SystemExit('paper anchor not found: ' + pat)
    anchors = [
        ('INTRO', 1),
        ('Prelim', find(r'\label{sec:prelim}')),
        ('Frames', find(r'\label{sec:frames}')),
        ('ThmA', find(r'\label{sec:dims}')),
        ('Skeleton', find(r'\label{sec:skel}')),
        ('Dim3', find(r'\label{sec:dim3}')),
        ('Base23', find(r'\label{sec:base23}')),
        ('DGS', find(r'\label{sec:dgs}')),
        ('Deficit', find(r'\label{sec:deficit}')),
        ('WhyLat', find(r'\label{sec:whylat}')),
        ('Large', find(r'\label{sec:large}')),
        ('Split', find(r'\subsection{The frame orbit cannot carry a half-integer layer}', r'\label{sec:Pnohalf}')),
        ('Appendix', find(r'\label{sec:formal}')),
    ]
    anchors.sort(key=lambda a: a[1])
    where = {}
    for no, ln in enumerate(lines, 1):
        for lab in re.findall(r'\\label\{([^}]*)\}', ln):
            f = [a for a, b in anchors if b <= no][-1]
            if f == 'INTRO':
                f = {'thm:A': 'ThmA'}.get(lab, 'INTRO')
            where[lab] = (f, no)
    return where


# definitions of the stage-9 entries deleted from the proof-side `*Defs` modules since (they were reached only
# through the statements that changed; `scripts/v14_delta.py`)
REMOVED_DEFS = {'Z3NetKN.bndE1'}  # V14 stage S9′: the former `thm:E1` bound in `bndDim3`


def entry_mods():
    """theorem -> the `*Defs` modules of its stage-9 Challenge (as `gen_statements.main`)"""
    idx = G.def_index()
    th2mods = {}
    for e in G.ENTRIES:
        suf = '' if e == 'main' else e
        _, ds = parse_text(git_show(f'Challenge{suf}.lean'), e)
        mods = set()
        for d in ds:
            if d in REMOVED_DEFS:
                continue
            ms = idx.get(d) or idx.get(R.new_name(d))  # S16′: live definitions were renamed
            if not ms or len(ms) != 1 or not re.search(r'Defs\d*$', ms[0]):
                raise SystemExit(f'definition {d} of Challenge {e}: proof-side modules {ms}')
            if ms[0].startswith('Retired.'):
                continue  # S16′: retired definitions (no kept theorem uses them; the build checks it)
            mods.add(ms[0])
        for n in json.loads(git_show(f'comparator{suf}.json'))['theorem_names']:
            th2mods[n] = mods
            th2mods[R.new_name(n)] = mods
    return th2mods


def classify():
    thms = collections.OrderedDict()
    for f in OLD_FILES:
        ts, ds = parse_text(git_show(f'QUNets/Statements/{f}.lean'), f)
        assert not ds, (f, ds)
        for t in ts:
            assert t['name'] not in thms, t['name']
            thms[t['name']] = t
    base_cfg = json.loads(git_show('comparatorAll.json'))['theorem_names']
    assert set(base_cfg) == set(thms) and len(base_cfg) == len(thms) == 458
    assert set(RETIRE) <= set(thms), set(RETIRE) - set(thms)
    where = paper_positions()
    lab = base_labels(set(thms))
    for n, t in thms.items():
        t['labels'] = lab.get(n, [])
        hold = [r for r, p in HOLD_GROUPS if p(n, t['src'])]
        assert len(hold) <= 1, n
        if n in RETIRE:
            assert not hold, n
            t['status'], t['reason'] = 'retire', RETIRE[n]
            continue
        if hold:
            t['status'], t['reason'], t['file'], t['key'] = 'hold', hold[0], 'Hold', 0
            continue
        t['status'] = 'keep'
        live = [x for x in t['labels'] if x in where and where[x][0] != 'INTRO']
        res = [x for x in live if not x.startswith(('sec:', 'app:'))]
        pick = (res or live or [None])[0]
        sub = [(lb, r) for p, lb, r in SUBST if n.startswith(p)]
        primary_removed = bool(t['labels']) and t['labels'][0] not in where
        if pick is None and not sub:
            raise SystemExit(f'kept theorem {n} without a live label: {t["labels"]}')
        if sub and (pick is None or primary_removed):
            # placed with the result that still claims it (e.g. `t3s4_reach`: `prop:t3s4` removed,
            # its secondary `lem:box` is only the tool; it backs `prop:korobov4`)
            pick, t['reason'] = sub[0]
        t['label'] = pick
        t['file'], t['key'] = where[pick]
    # V14 stage S16′: the legacy rename (`scripts/v16_rename.py`): kept theorems of the namespace `EisensteinNet`
    # are renamed (prefix map) and their texts rewritten; retired ones keep their old names
    out = collections.OrderedDict()
    for n, t in thms.items():
        if t['status'] != 'retire':
            nn = R.new_name(n)
            t['name'], t['ns'] = nn, R.apply_text(t['ns'])
            t['opens'] = tuple(R.apply_text(o) for o in t['opens'])
            t['doc'], t['body'] = R.apply_text(t['doc']), R.apply_text(t['body'])
            n = nn
        out[n] = t
    return out


def apply_delta(thms, th2mods):
    """the statements changed or added after stage S1 (`scripts/v14_delta.py`)"""
    for n, c in D.CHANGED.items():
        t = thms[n]
        assert t['status'] == 'keep', n
        t['doc'], t['body'] = c['doc'], c['body']
    where = paper_positions()
    for i, x in enumerate(D.NEW):
        assert x['name'] not in thms, x['name']
        f, key = where[x['label']]
        assert f == x['file'], (x['name'], f)
        thms[x['name']] = dict(name=x['name'], src='NEW', ns=x['ns'], opens=x['opens'], doc=x['doc'],
                               body=x['body'], pos=i, labels=[x['label']], status='keep',
                               label=x['label'], file=f, key=key)
        th2mods[x['name']] = set()


def srcidx(t):
    return OLD_FILES.index(t['src']) if t['src'] in OLD_FILES else len(OLD_FILES)


def main():
    thms = classify()
    th2mods = entry_mods()
    apply_delta(thms, th2mods)
    out_dir = os.path.join(L, 'QUNets', 'Statements')
    files_ord = list(FILES)
    allnames, report = [], []
    for f in files_ord:
        ts = [t for t in thms.values() if t['status'] != 'retire' and t.get('file') == f]
        ts.sort(key=lambda t: (t['key'], srcidx(t), t['pos']))
        first = {}
        for i, t in enumerate(ts):
            first.setdefault((t['ns'], t['opens']), i)
        ts = sorted(ts, key=lambda t: first[(t['ns'], t['opens'])])
        mods = sorted((set().union(*(th2mods[t['name']] for t in ts)) if ts else set())
                      | set(D.EXTRA_MODS.get(f, [])))
        secl, title = FILES[f]
        body = [HEADER.rstrip('\n')] + ['public import ' + m for m in mods]
        body += ['', '@[expose] public section', '', '/-!', f'# Statements: {title}', '']
        body += [f'Paper section `{secl}` of {REV} (the section of the first live result label of',
                 'each theorem in the per-theorem map of `STATEMENTS_INDEX.md`; theorems whose labels',
                 'were all removed are placed with the result that still claims them, see',
                 'the research notes).']
        if f in EMPTY_NOTE:
            body += ['', EMPTY_NOTE[f]]
        body += ['',
                 'The compared theorems are verbatim copies (statement, docstring, namespace, `open`s) of',
                 'the stage-13c library, with proof `sorry`, except those changed or added after stage S1',
                 '(`scripts/v14_delta.py`); within each namespace block they are ordered',
                 'by the position of their label in the paper. Definitions are imported from the',
                 'proof-side `*Defs` modules above, so the roots `Challenge` and `Solution` share the',
                 'same constants. Generated by `scripts/gen_v14_statements.py`.',
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
        if cur is not None:
            body += [f'end {cur[0]}', '']
        txt = '\n'.join(body)
        open(os.path.join(out_dir, f + '.lean'), 'w').write(txt)
        report.append((f, len(ts), txt.count('\n'), len(txt.encode()), len(mods)))
    kept = [n for n, t in thms.items() if t['status'] != 'retire']
    assert sorted(allnames) == sorted(kept) and len(set(allnames)) == len(allnames)
    for f in OLD_FILES:
        if f not in FILES and os.path.exists(os.path.join(out_dir, f + '.lean')):
            os.remove(os.path.join(out_dir, f + '.lean'))
    # Challenge root
    ch = [HEADER.rstrip('\n')] + [f'public import QUNets.Statements.{f}' for f in files_ord]
    ch += ['', '@[expose] public section', '', '/-!', '# Challenge (all compared theorems)', '',
           f'The {len(allnames)} compared theorems of the project ({REV}), in the statement library',
           '`QUNets/Statements/*.lean` (one file per paper section; definitions imported from the',
           'proof-side `*Defs` modules). Comparator',
           'configuration: `comparator.json`. Generated by `scripts/gen_v14_statements.py`.', '-/', '']
    open(os.path.join(L, 'Challenge.lean'), 'w').write('\n'.join(ch))
    # Solution root: the BASE `SolutionAll` imports, minus modules that restate only retired theorems
    simps = re.findall(r'^public import (\S+)', git_show('SolutionAll.lean'), re.M)
    keep_mods, drop_mods = [], []
    for m in simps:
        if m.startswith('EisensteinNet') and m not in R.MODULES:
            drop_mods.append(m)  # S16′: archived (the retired Eisenstein development (research history)), restates only retired theorems
            continue
        m = R.MODULES.get(m, m)
        path = os.path.join(L, m.replace('.', '/') + '.lean')
        decl = set()
        if os.path.exists(path):
            ts, _ = parse_text(open(path).read(), m)
            decl = {t['name'] for t in ts} & set(thms)
        if (decl and decl <= set(RETIRE)) or m in D.DROP_SOLUTION:
            drop_mods.append(m)
        else:
            keep_mods.append(m)
    keep_mods += [m for m in D.EXTRA_SOLUTION if m not in keep_mods]
    so = [HEADER.rstrip('\n')] + [f'public import {m}' for m in keep_mods]
    so += ['', '@[expose] public section', '', '/-!', '# Solution (all compared theorems)', '',
           'The proof modules restating the compared theorems of `Challenge.lean` by name, and one',
           '`#print axioms` per compared theorem. Generated by `scripts/gen_v14_statements.py`',
           '(the stage-13c `SolutionAll` imports without the modules that restate only retired',
           'theorems: ' + ', '.join(f'`{m}`' for m in drop_mods) + '; plus the proof modules of the',
           'theorems added after stage S1: ' + ', '.join(f'`{m}`' for m in D.EXTRA_SOLUTION) + ').',
           '-/', '']
    so += [f'#print axioms {n}' for n in allnames] + ['']
    open(os.path.join(L, 'Solution.lean'), 'w').write('\n'.join(so))
    json.dump({'challenge_module': 'Challenge', 'solution_module': 'Solution',
               'theorem_names': allnames, 'definition_names': [],
               'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
               'enable_nanoda': True}, open(os.path.join(L, 'comparator.json'), 'w'), indent=2)
    open(os.path.join(L, 'comparator.json'), 'a').write('\n')
    st = collections.Counter(t['status'] for t in thms.values())
    for f, n, nl, nb, nm in report:
        print(f'{f:9s} {n:4d} theorems {nl:5d} lines {nb / 1024:6.1f} KiB  imports {nm}')
    print(f'retired {st["retire"]}, kept {st["keep"]}, held {st["hold"]}; compared {len(allnames)}')
    print('Solution: dropped imports', drop_mods)


if __name__ == '__main__':
    sys.exit(main())

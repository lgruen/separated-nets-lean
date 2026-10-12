#!/usr/bin/env python3
"""V14 stage S1 (the research notes; the research notes item 13e, section C): generate the
leanblueprint sources `blueprint/src/*` from the paper `paper/core.tex`.

Regenerable: re-run after any change of `core.tex`, `STATEMENTS_INDEX.md`, `comparator.json` or
`QUNets/Statements/Hold.lean` (retired in V14 stage S9′; the held-statement handling below is then inactive); every
file under `blueprint/src/` is overwritten.

What it does
* Walks `core.tex` in order. The paper's sections become chapters (`\\part`s are kept), its
  subsections become sections (only those that contain a result); every result environment
  (`theoremA`, `theorem`, `proposition`, `lemma`, `corollary`, `definition`, `remark`, `propA`) is
  copied **in the paper's words** with its `\\label`, followed by its proof (a proof printed
  elsewhere, "Proof of Theorem~\\ref{X}", is moved next to X). Running prose, figures and tables are
  dropped, except the formalized tables (`TABLE_NODES`), which become remark nodes carrying the
  table and its caption. The paper's `thebibliography` is copied at the end, so `\\cite` works.
* `\\lean{...}`: the per-theorem map of `STATEMENTS_INDEX.md` (Lean names -> labels, inverted),
  restricted to the compared theorems of `comparator.json`. Theorems whose labels were all removed
  from the paper are attached to the result that still claims them (`gen_v14_statements.SUBST`:
  `thm:U` -> `rem:Us`, `prop:half` -> `prop:half5`, `prop:t3s4` -> `prop:korobov4`, the skeleton
  infrastructure -> `prop:skelcomp`). Theorems mapped only to a section or an appendix get one
  remark node per section (`SECTION_NODES`; the text is the index's description). Definitions
  formalized as Lean definitions only (index section "Labels formalized as definitions only")
  are added for live labels.
* `\\leanok` (statement and proof) on every non-dagger result with at least one compared, non-held
  Lean name (all compared theorems are proved). Results marked dagger in the paper get
  `\\leanok` only once their formalization is complete (`DAGGER_DONE`, V14 stage S2: `lem:Ss`,
  `def:K`, `prop:Dprime`; stage S3: `lem:sat`, `def:Ustar`; stage S4: `lem:adelic`, `lem:babai`; stage S5: `thm:A`; stage S7: `lem:O`, `prop:E`, `lem:C`,
  `thm:Lstar`; stage S8: `prop:4D2`, `prop:k1`; stage S9′: `def:col`, `thm:colmin`, `thm:col`, `lem:shared`,
  `prop:colfree`, `prop:colshift`, `lem:Kone`, `lem:drift`, `cor:colceil`, `thm:O`, `cor:allm`; stage S10′ (see `DAGGER_DONE`);
  stage S11′: `lem:R2`, `prop:half5`, `thm:D`; with a note that the paper
  still marks them); where Lean names exist for a part (`prop:k1designs`) they are listed
  with a note (`DAGGER_PARTIAL_NOTE`).
  `PARTIAL` results (classical theorems as explicit hypotheses) get `\\leanok` and a note.
* Held statements (`QUNets/Statements/Hold.lean`: the dimension-three, m = 3 material under
  redesign). A live result whose Lean names are all held gets **no** `\\lean`/`\\leanok`, gets
  `\\notready` (orange border in the graph) and a visible "Held" note. Held theorems whose labels
  are not in the paper are listed (as text, not as `\\lean`) in a final section. TODO(m = 3
  redesign): when the paper's dimension-three section is rewritten, remap these from the new
  `STATEMENTS_INDEX.md` and re-run this script; no mapping is invented here.
* `\\uses{...}`: the `\\ref`s inside a statement (statement edges) and inside its proof (proof
  edges), restricted to result nodes. A first draft of the dependency graph (references are not
  always logical dependencies).
* `\\ref`s to labels that are not in the blueprint (figures, tables, equations of dropped prose,
  sections without results) are printed as the label in typewriter type.

Checks (exit 1 on failure): every compared theorem is referenced by some `\\lean{}` or listed as
held; every `\\lean` name is a compared theorem or a listed definition; every result of `tab:lean`
is a node with `\\leanok` (held results are reported, not failed). Name resolution against the
`Solution` environment: `scripts/check_blueprint_decls.py`. Build: `scripts/build_blueprint.sh`.

Usage (from the repository root): uv run --no-project python scripts/gen_blueprint.py
"""
import collections
import json
import os
import re
import sys

L = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(L, 'scripts'))
import gen_v14_statements as V  # noqa: E402  (SUBST, parse_text)

PAPER = os.environ.get('QUNETS_CORE_TEX', os.path.join(L, 'paper', 'core.tex'))  # override: a copy of the committed core.tex
OUT = os.path.join(L, 'blueprint', 'src')
TITLE = 'Low-discrepancy quasi-uniform digital nets in every dimension'

RESULT_ENVS = ['theoremA', 'theorem', 'proposition', 'lemma', 'corollary', 'definition', 'remark',
               'propA']
# formalized tables: become remark nodes (label kept)
TABLE_NODES = {'tab:S1E': 'Table of Proposition~\\ref{prop:S1E}'}
# classical theorems as explicit hypotheses (`sec:formal`, `app:formal` items (1), (2))
PARTIAL = {
    'rem:Us': 'The growth statement $\\log a_s=(1+o(1))s^2$ uses the prime number theorem as an '
              'explicit hypothesis (\\texttt{PNTpsi}); everything else is unconditional.',
    'prop:cube': "Uses Haj\\'os's theorem, Keller's conjecture for $s\\le7$ and the optimal packing "
                 'bounds in dimensions two and three as explicit hypotheses.',
}
DAGGER_PARTIAL_NOTE = {}
# results marked dagger in rev 14.3 whose formalization is complete: label -> (V14 stage, note);
# `\\leanok` with a note
DAGGER_DONE = {
    'lem:Ss': ('S2', 'every $k\\ge1$'),
    'def:K': ('S2', ''),
    'prop:Dprime': ('S2', ''),
    'lem:sat': ('S3', ''),
    'def:Ustar': ('S3', 'existence and uniqueness; the polynomial running time is not formalized'),
    'lem:adelic': ('S4', ''),
    'lem:babai': ('S4', ''),
    'thm:A': ('S5', '(1), (2) with the first-order sharpness (an explicit pair at distance '
                    '$<(1-a^*_s/q+(s-1)(a^*_s+1)^2/q^2)N^{-1/s}$ for $q>(s-1)a^*_s$), $a^*_3=2$, and the '
                    'bound on $a^*_s$ with $|\\log(\\text{bound})-s\\log s|\\le3s$; the values '
                    '$a^*_4,\\dots,a^*_{10}$ of Table~\\ref{tab:astar} and the polynomial running time are '
                    'not formalized'),
    'lem:O': ('S7', ''),
    'prop:E': ('S7', 'with the elementary bound $K(F)\\ge2^{s-3}/(s-2)$ and the instance $U^*_s$; the form '
                     '$e^{(1+o(1))s}$ by the prime number theorem is not formalized'),
    'lem:C': ('S7', 'also the sharper bound $1+2K\\tau^*(n)\\tau^*(nK)$ that the proof gives'),
    'thm:Lstar': ('S7', 'the $\\tau^*$ form, with $PGL_2(\\mathbb Q)$-images of the places; the consequence '
                        '$K(F)\\ge s^{1-O(1/\\log\\log s)}$ by Wigert\'s divisor bound is not formalized'),
    'prop:4D2': ('S8', 'the finite parts $K(F)=2$, $S(F)=7$ and the values at $q=17,19,21$ by kernel '
                       '\\texttt{decide}; (3) for every $k\\ge2$; the bounds ``$\\ge.5$ from $q=11$, $\\ge.8$ '
                       'from $q=15$\'\' after it (Table~\\ref{tab:Kdesigns}) are not formalized'),
    'prop:k1': ('S8', '(3) for any $K_1$ with $F_0[a][a]=-K_1$, also in the form '
                      '$\\delta N^{1/s}<1-K_1/q+C/q^2$, $C=\\sum_{u\\ne a}(|F_0[u][a]|+1)^2$'),
    'def:col': ('S9′', ''),
    'thm:colmin': ('S9′', 'in the form $3d^2=2q^4+(3g)^2$, attained by two points in neighbouring columns'),
    'thm:col': ('S9′', 'with the closest pairs; the expansions in (2) with explicit $O(q^{-3})$ constants $2$ '
                       'resp.\\ $1$; the box minors are among $1$, $\\pm a_c$, $a_x+a_y$; as integers, the depth-3 box minors (S16′)'),
    'lem:shared': ('S9′', ''),
    'prop:colfree': ('S9′', 'without the hypothesis $3\\nmid q$, which the proof does not use'),
    'prop:colshift': ('S9′', '(1) toroidal; the upper bound of (3) for the Euclidean distance too'),
    'lem:Kone': ('S9′', ''),
    'lem:drift': ('S9′, S16′', '(2) with the range hypothesis of revision 15.1, the excesses $\\varepsilon_i$, $\\varepsilon_i-q$ (S16′); excesses in units of thirds'),
    'cor:colceil': ('S9′', ''),
    'thm:O': ('S9′', '(1) for every $q\\ge2$, (2) for every even $q\\ge2$'),
    'cor:allm': ('S9′', 'the case $m=3$ through the column net $\\mathcal C_p$'),
    'def:dshift': ('S10′', 'for any point set at integer scale $q^m$; equal to [DGS2, Def.~2.2] for digital nets'),
    'lem:shift': ('S10′', 'any depths $K$; the net property for any point set, digital or not'),
    'prop:shift': ('S10′', 'every listed separation core, the coset in Theorem~\\ref{thm:S1}(2) and the first-order sharpness in Theorem~\\ref{thm:A}(2)'),
    'cor:allmshift': ('S10′', '$m=3$ in S9′; $m\\ge4$ with the constants and covering bounds of '
                              'Corollary~\\ref{cor:allm}'),
    'cor:dgs': ('S10′', 'with the definitions of [DGS2] (Defs.~2.1, 2.2, 3.1--3.3, 3.8); instances (1)--(5) '
                        'for every digital shift; (4) for the explicit nets $\\mathcal S^1_{k,p,\\rho}$, with the parenthetical $p>(\\lceil\\sqrt s\\rceil+1)^s$ (S16′)'),
    'rem:dgsfinite': ('S10′, S15′', 'the finite part, the frame nets for every $q$ and $m$; the families on all of '
                              '$\\mathbb N$ under every digital shift in every prime base (S15′): $p\\in\\{2,3\\}$ by '
                              'Theorem~\\ref{thm:base23}(3), $5\\le p\\le31$ by Theorem~\\ref{thm:main} ($m\\equiv0$) and '
                              'the per-prime designs with Remark~\\ref{rem:ppshift} ($m\\ge10$), $p\\ge37$ as in S10′, the '
                              'frame nets below; the frame nets are used for every $m\\le9$ when $5\\le p\\le31$'),
    'rem:ppshift': ('S15′', 'for every prime $p$ (Proposition~\\ref{prop:ppsep} is stated for odd $p$), the general '
                            'form with any certificate and the designs of Table~\\ref{tab:perprime}'),
    'prop:k1designs': ('S2, S4, S15′', '(1) the deficits $K_1$, the $s=4$ layer as level $0$ of $U^*_4$, the $s=5$ layer as '
                       'the layer $F_0$ of the design of Table~\\ref{tab:Kdesigns} (a Cauchy layer with '
                       '$\\lambda\'=(\\frac12,1,1,1,1)$), the $s=6$ Cauchy layer; (2) the $t=0$ completions for every '
                       'admissible $q$ (also for the second $s=6$ layer, $\\gcd(q,210)=1$), by integer completions whose box '
                       'minors have only the excluded primes (for the second $s=6$ layer also $11,13,17,19$, covered by '
                       'per-prime completions), the integer lift and the Chinese remainder theorem, instead of the '
                       'Schwartz--Zippel lemma; the thresholds $\\delta N^{1/s}\\ge0.8$ (finite scans) are not '
                       'formalized'),
    'prop:linf': ('S10′', 'the sentence on dominant designs after it is not formalized'),
    'lem:R2': ('S11′', 'for every odd $q$ (the paper: odd primes)'),
    'prop:half5': ('S11′', '(1) by the $126$ integer box determinants (with the layer row doubled they all divide '
                           '$360$); (2) by the exact scans for the primes $37\\le p<200$ and the monotone bound at '
                           '$p=200$, with the bounds $\\sqrt5/2-12\\sqrt5/p\\le\\delta N^{1/5}\\le\\sqrt5/2+4\\sqrt5/p$ '
                           '($p>32$) of the proof; (3) by the scans for $53\\le p<200$ and the monotone bound; kernel '
                           '\\texttt{decide}; the values $\\mathrm{LB}_2(31)$, $\\mathrm{LB}(47)$ and the exact minimum '
                           'distances after it are not formalized'),
    'thm:D': ('S11′', 'the skew case by hand; the normalized non-skew case by a kernel \\texttt{decide} enumeration of '
                      'the same layers (forward-checked (MIN), a list of $18$ binding witness steps; the count '
                      '$1{,}004{,}544$ itself is not computed in Lean); the normalization proved; '
                      '$\\mathrm{dr}(F_0^*)=\\frac{17}2$'),
    'rem:shiftshared': ('S10′', 'the sentence on $\\mathcal C_p$ (the sentences on $\\mathcal T_p$ and $\\mathcal W_p$ '
                                'moved to Remark~\\ref{rem:wshift})'),
    'rem:wshift': ('S12′, S16′', 'the bound of Proposition~\\ref{prop:twocoset}(2) for every shift with equal digits on the '
                                'shared positions (S16′); for $\\mathcal W_p$ the bound under shifts with $t\\equiv2t\'$ or '
                                '$t\\equiv2t\'+1$ (S12′) and the exact pairs for the digit $2\\zeta+1$ (S16′); the computed '
                                'values are not formalized'),
    'rem:shiftparity': ('S16′', r"(i) for even $L\ge1$ and any lift, with the contrapositive; (ii) in real form, the Euclidean distance (at least the toroidal one); (iii) the floor from some level on, for chains of lifts frozen from every resolution; the resolutions where $v^\circ_L$ vanishes (computed) are not formalized"),
    'cor:skelreach': ('S16′', '(N1)--(N3) in the coefficient form of the proof; the necessity for each single $k$'),
    'prop:wnet': ('S12′', '(1)--(3) as printed, (2) for any third digits; (4) by kernel \\texttt{decide} checks of the '
                          'exact minimum distances at the primes $17\\le p\\le89$ (each with an attaining pair; the check '
                          'lets the three third digits wrap independently, which is exact at these primes); the '
                          'computed comparisons after it are not formalized'),
    'lem:wwrap': ('S12′', 'for every $u$, also $u=0$'),
    'prop:wfamily': ('S12′', '(1) for every $u$, without the net property; (2) by a kernel \\texttt{decide} enumeration '
                             'of the options with Bernstein certificates on $(0,\\frac3{100}]$; (3) the six-contact '
                             'proof, exact in $\\sqrt{31}$'),
    'rem:wstar': ('S12′', '$t=0$, $\\rho$, $\\varepsilon_p\\le\\frac3{100}$, the bound with $K$, the limit, the '
                          'thresholds $67$, $97$, $9791$, $17737$ and ``provably ahead\'\'; the computed comparisons at '
                          'moderate $p$ and the sentence $\\mathcal W^*_p=\\mathcal W_p$ for $p<193$ are not formalized'),
    'rem:projlines': ('S13′', 'the middle-digit relation for the frame, $\\mathcal P^F_{k,q}$ (with the sign rule, and the '
                              'coefficient is unique) and $\\mathcal P_{k,q}$ (a sign $\\pm1$, every odd $k$), with a '
                              'general lemma (any net with invertible $(r{+}1,r)$, $(r,r{+}1)$ boxes has the relation '
                              'with some unit); the remedy: box minors and $t=0$, the coefficient becomes '
                              '$\\rho_bg\\rho_a^{-1}$, and the bounds of Lemma~\\ref{lem:Ss}, '
                              'Proposition~\\ref{prop:D}, Theorem~\\ref{thm:A}(2) and Theorem~\\ref{thm:sep} for any '
                              'row $r\\ge k+1$ and any $\\rho$; the lines in the projections and the size of the effect '
                              'are not formalized'),
    'def:lift': ('S14′', r"admissibility as $s^{cc'}\notin P_{cc'}+Z_e$ ($=\ker\lambda^{cc'}_e$); a chain of lifts with depth "
                         r"parameters $D_\ell$ (any $D_\ell$)"),
    'lem:lift': ('S14′', r"(A) through the box criterion; (B) by a greedy choice of the pivot digits of the proof"),
    'lem:liftsep': ('S14′', r"integer and real forms; for any depths $D_{L+3j'}\ge\lfloor L/2\rfloor+j'$"),
    'lem:shiftcert': ('S14′', r"(a) with the fix: distinct points, $\Delta=0$ allowed; $v^\circ_L=\min_{\tau'}v^*_L(P_L\oplus\tau')$; "
                              r"(b) for any digital point set, as two inequalities; the description of $\mu_n$ "
                              r"and the staircase criterion after it are not formalized (the kernel checks use a sound "
                              r"lower bound for $\mu_n$)"),
    'thm:base23': ('S14′', r"(2) and (3) for every $m\ge1$, with the replacement witnesses $b=2$, $m=6,7$ "
                           r"(\texttt{BASE23\_EVERYSHIFT.md}~\S5): $t=0$, the integers $v^\circ_L$, the exact "
                           r"every-shift distances at the levels below $L$ and of the witnesses by kernel "
                           r"\texttt{decide}; (1), and the larger constants of (2) for $b=3$, $m\equiv0,1$, are not "
                           r"formalized (beyond $L$ (1) is stated with its certificate $v^*_L$ as a hypothesis)"),
    'rem:accounting': ('S13′, S16′', 'both halves with explicit $O(p^{-2})$ terms ($(\\Lambda)$ only for the bound by '
                               '$\\mathrm{dj}$, $\\det F_0\\ne0$ only for the bound by $\\mathrm{dr}$; deeper rows '
                               'arbitrary), the $\\liminf$/$\\limsup$ form along the primes, the expansion when '
                               '$\\mathrm{dj}=\\mathrm{dr}$, $\\mathcal Q^*_p$, and the printed layer without '
                               '$(\\Lambda)$; toroidal distance; the two-sided expansion of $\\mathrm{LB}_2(p)$ and of $\\mathrm{LB}$ of Proposition~\\ref{prop:Hk}(1) in the proof (S16′); the plausibility estimate after it is not formalized'),
}


# ------------------------------------------------------------------ small LaTeX parsing helpers
def strip_comments(s):
    out = []
    for ln in s.split('\n'):
        i = 0
        while True:
            j = ln.find('%', i)
            if j < 0:
                break
            k, bs = j - 1, 0
            while k >= 0 and ln[k] == '\\':
                bs += 1
                k -= 1
            if bs % 2 == 0:
                ln = ln[:j].rstrip() if ln[:j].strip() else ''
                break
            i = j + 1
        out.append(ln)
    return '\n'.join(out)


def group(s, i, op='{', cl='}'):
    """s[i] == op: return (content, index after the closing delimiter); braces nest, and inside
    an optional argument `[...]` brace groups are skipped."""
    assert s[i] == op, (s[i:i + 40], op)
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c == '\\':
            j += 2
            continue
        if op == '[' and c == '{':
            _, j = group(s, j)
            continue
        if c == op:
            depth += 1
        elif c == cl:
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    raise SystemExit('unbalanced group at ' + s[i:i + 80])


def skip_ws(s, i):
    while i < len(s) and s[i] in ' \t\n':
        i += 1
    return i


def find_end(s, i, env):
    """index of the matching `\\end{env}` (nesting of the same env counted) after position i"""
    pat = re.compile(r'\\(begin|end)\{' + re.escape(env) + r'\}')
    depth = 1
    for m in pat.finditer(s, i):
        depth += 1 if m.group(1) == 'begin' else -1
        if depth == 0:
            return m.start(), m.end()
    raise SystemExit('no \\end{%s}' % env)


REF = re.compile(r'\\(?:ref|eqref)\{([^}]*)\}')


def refs(s):
    out = []
    for x in REF.findall(s):
        if x not in out:
            out.append(x)
    return out


# ------------------------------------------------------------------ paper
def parse_paper():
    src = strip_comments(open(PAPER).read())
    pre = src[:src.index('\\begin{document}')]
    body = src[src.index('\\begin{document}'):src.index('\\end{document}')]
    bib_s = body.index('\\begin{thebibliography}')
    bib_e = body.index('\\end{thebibliography}') + len('\\end{thebibliography}')
    bib = body[bib_s:bib_e]
    body = body[:bib_s]
    items = []   # ('head', level, title, labels) | ('res', env, opt, labels, text) | ('proof', opt, text)
    tok = re.compile(r'\\(part|section|subsection)(\*?)(?=[{\s])|\\appendix\b|'
                     r'\\begin\{(' + '|'.join(RESULT_ENVS) + r'|proof|table|figure|abstract)\}')
    i = 0
    prev_end = 0
    while True:
        m = tok.search(body, i)
        if not m:
            break
        if m.group(0) == '\\appendix':
            items.append(('appendix', m.start()))
            i = m.end()
            continue
        if m.group(1):
            lvl = m.group(1) + m.group(2)
            j = skip_ws(body, m.end())
            title, j = group(body, j)
            labels = []
            while True:
                k = skip_ws(body, j)
                mm = re.match(r'\\label\{([^}]*)\}', body[k:])
                if not mm:
                    break
                labels.append(mm.group(1))
                j = k + mm.end()
            items.append(('head', lvl, title, labels, m.start()))
            i = j
            continue
        env = m.group(3)
        j = m.end()
        opt = None
        if j < len(body) and body[j] == '[':
            opt, j = group(body, j, '[', ']')
        e0, e1 = find_end(body, j, env)
        text = body[j:e0]
        if env in ('table', 'figure', 'abstract'):
            labs = re.findall(r'\\label\{([^}]*)\}', text)
            items.append(('float', env, text, labs, m.start(), e1))
        elif env == 'proof':
            gap = body[prev_end:m.start()]
            items.append(('proof', opt, text, m.start(), gap.strip() == ''))
        else:
            labels = []
            k = 0
            while True:
                k2 = skip_ws(text, k)
                mm = re.match(r'\\label\{([^}]*)\}', text[k2:])
                if not mm:
                    break
                labels.append(mm.group(1))
                k = k2 + mm.end()
            items.append(('res', env, opt, labels, text[k:], m.start()))
        i = e1
        prev_end = e1
    return pre, items, bib


# ------------------------------------------------------------------ Lean side
def index_map(names):
    """per-theorem map of the current STATEMENTS_INDEX.md: compared name -> [labels]"""
    lab = collections.defaultdict(list)
    ns = None
    deflab = collections.defaultdict(list)   # label -> Lean definitions (definitions-only table)
    in_defs = False
    for ln in open(os.path.join(L, 'STATEMENTS_INDEX.md')).read().split('\n'):
        m = re.match(r'^### .*namespace `([^`]+)`', ln)
        if m:
            ns = m.group(1)
            continue
        if ln.startswith('## '):
            ns = None
            in_defs = ln.startswith('## Labels formalized as definitions only')
            continue
        if not (ln.startswith('|') and not ln.startswith('|---')):
            continue
        cells = [c.strip() for c in ln.strip().strip('|').split('|')]
        if in_defs:
            if len(cells) >= 3 and cells[0].startswith('`'):
                lb = cells[0].strip('`')
                # fully qualified Lean names only (the cell also cites labels and theorem groups)
                deflab[lb] += [x for x in re.findall(r'`([^`]+)`', cells[2])
                               if re.fullmatch(r"[A-Za-z_][\w']*(\.[A-Za-z_][\w']*)+", x)]
            continue
        if len(cells) < 2:
            continue
        if len(cells) >= 3 and cells[1].startswith('`') and '.' in cells[1]:
            nn = re.findall(r'`([^`]+)`', cells[1])
            paper = ' '.join(cells[2:])
        else:
            nn = re.findall(r'`([^`]+)`', cells[0])
            paper = ' '.join(cells[1:])
        for n in nn:
            # a fully qualified name under a heading of another namespace (e.g. the S6b table, headed
            # "namespaces `Z3NetF`, `Z3NetA`") is taken as is
            full = n if (ns is None or n.startswith(ns + '.') or n in names) else ns + '.' + n
            if full in names:
                # a parenthetical "(note …)" is a remark, not a mapping (e.g. `net_iff`: "note
                # `thm:t0`; not core.tex `thm:t0`")
                for x in V.G.LBL.findall(re.sub(r'\(note [^)]*\)', '', paper)):
                    if x not in lab[full]:
                        lab[full].append(x)
    return lab, deflab


def lean_side(live_results, live_all):
    names = json.load(open(os.path.join(L, 'comparator.json')))['theorem_names']
    hold_path = os.path.join(L, 'QUNets', 'Statements', 'Hold.lean')  # retired in V14 stage S9′
    held = ([t['name'] for t in V.parse_text(open(hold_path).read(), 'Hold')[0]]
            if os.path.exists(hold_path) else [])
    assert set(held) <= set(names)
    lab, deflab = index_map(set(names))
    node_names = collections.defaultdict(list)     # label -> compared, non-held names
    held_names = collections.defaultdict(list)     # live label -> held names
    held_offpaper = []                             # (name, labels) of held names without live label
    section_names = collections.defaultdict(list)  # sec/app label -> names
    unplaced = []
    for n in names:
        ls = lab.get(n, [])
        res = [x for x in ls if x in live_results]
        primary_removed = bool(ls) and ls[0] not in live_all
        sub = [lb for p, lb, _ in V.SUBST if n.startswith(p)]
        if n in held:
            hl = [x for x in ls if x in live_results]
            if hl:
                for x in hl:
                    held_names[x].append(n)
            else:
                held_offpaper.append((n, ls))
            continue
        targets = list(res)
        if sub and (not res or primary_removed):
            targets = [sub[0]] + [x for x in res if x != sub[0]]
        if not targets:
            secs = [x for x in ls if x in live_all and x.startswith(('sec:', 'app:'))]
            if secs:
                section_names[secs[0]].append(n)
                continue
            unplaced.append((n, ls))
            continue
        for x in targets:
            node_names[x].append(n)
    return names, held, node_names, held_names, held_offpaper, section_names, unplaced, deflab


# ------------------------------------------------------------------ emit
def fix_math(s):
    s = re.sub(r'\\begin\{psmallmatrix\}', r'\\left(\\begin{smallmatrix}', s)
    s = re.sub(r'\\end\{psmallmatrix\}', r'\\end{smallmatrix}\\right)', s)
    for c in ['needspace', 'enlargethispage']:
        s = re.sub(r'\\' + c + r'\{[^}]*\}', '', s)
    s = re.sub(r'\\(sloppy|fussy|allowbreak|medskip|smallskip)\b', '', s)
    return s


def fix_refs(s, known):
    def rep(m):
        cmd, x = m.group(1), m.group(2)
        if x in known:
            return m.group(0)
        return ('(\\texttt{%s})' if cmd == 'eqref' else '\\texttt{%s}') % x
    return re.sub(r'\\(ref|eqref)\{([^}]*)\}', rep, s)


def lean_list(ns):
    return '\\lean{' + ', '.join(ns) + '}'


def main():
    pre, items, bib = parse_paper()
    live_all = set(re.findall(r'\\label\{([^}]*)\}', strip_comments(open(PAPER).read())))
    results = [it for it in items if it[0] == 'res']
    live_results = {lb for it in results for lb in it[3]}
    (names, held, node_names, held_names, held_offpaper, section_names, unplaced,
     deflab) = lean_side(live_results | set(TABLE_NODES), live_all)
    problems = []
    if unplaced:
        problems.append('compared theorems without a live label or substitute: %s' % unplaced)
    for x in list(node_names):
        if x not in live_results and x not in TABLE_NODES:
            problems.append('substitute label %s is not a result of the paper' % x)

    # attach proofs
    proofs = collections.defaultdict(list)
    last_res = None
    last_head = None
    for it in items:
        if it[0] == 'res':
            last_res = it
        elif it[0] == 'head':
            last_head = it
            last_res = None
        elif it[0] == 'float':
            continue
        elif it[0] == 'proof':
            opt, text, pos, adjacent = it[1], it[2], it[3], it[4]
            target = None
            if opt and re.search(r'Proof of', opt) and refs(opt):
                target = refs(opt)[0]
            elif adjacent and last_res is not None and last_res[3]:
                target = last_res[3][0]
            elif last_head is not None and 'Proof of' in last_head[2] and refs(last_head[2]):
                target = refs(last_head[2])[0]
            elif last_res is not None and last_res[3]:
                target = last_res[3][0]
            if target is None or target not in live_results:
                problems.append('unattached proof at offset %d: %r' % (pos, (opt or text)[:80]))
                continue
            proofs[target].append((opt, text))

    # which subsections contain results (only those are emitted)
    # (sub)sections that contain a node are emitted, the others dropped (parts are always kept)
    head_has = set()
    cur = sec = None
    for it in items:
        if it[0] == 'head' and it[1].startswith('subsection'):
            cur = it
        elif it[0] == 'head' and it[1].startswith('section'):
            cur, sec = None, it
            if set(it[3]) & set(section_names):
                head_has.add(id(it))
        elif it[0] == 'head':
            cur = sec = None
        elif it[0] == 'res' or (it[0] == 'float' and set(it[3]) & set(TABLE_NODES)):
            for h in (cur, sec):
                if h is not None:
                    head_has.add(id(h))
    known = set(live_results) | set(TABLE_NODES)
    for it in items:
        if it[0] == 'head' and (it[1] == 'part' or id(it) in head_has):
            known |= set(it[3])
    for it in results:   # labels inside statements (equations, items)
        known |= set(re.findall(r'\\label\{([^}]*)\}', it[4]))
    for lb, pl in proofs.items():
        for _, t in pl:
            known |= set(re.findall(r'\\label\{([^}]*)\}', t))

    out = []
    stats = collections.Counter()
    leanok_labels = set()
    held_nodes = []
    dagger_nodes = []
    dagger_done_nodes = []

    # ---- dependency edges: candidates from the \ref's, made acyclic (plastexdepgraph needs a DAG)
    primary, pos, kind = {}, {}, {}
    order = 0
    for it in items:
        if it[0] == 'res' and it[3]:
            for x in it[3]:
                primary[x] = it[3][0]
            pos[it[3][0]] = order
            kind[it[3][0]] = it[1]
        elif it[0] == 'float':
            for x in it[3]:
                if x in TABLE_NODES:
                    primary[x] = x
                    pos[x] = order
                    kind[x] = 'remark'
        order += 1
    cand = []   # (user, used, 'stmt'|'proof')
    for it in results:
        if not it[3]:
            continue
        me = it[3][0]
        for x in refs(it[4]):
            if x in primary and primary[x] != me:
                cand.append((me, primary[x], 'stmt'))
        for _, pt in proofs.get(me, []):
            for x in refs(pt):
                if x in primary and primary[x] != me:
                    cand.append((me, primary[x], 'proof'))
    cand = list(dict.fromkeys(cand))
    # priority: uses of a definition, then backward references, then forward ones; statement
    # edges before proof edges; an edge that would close a cycle is dropped
    def prio(e):
        user, used, k = e
        return (0 if kind[used] == 'definition' else 1, 0 if pos[used] < pos[user] else 1,
                0 if k == 'stmt' else 1, pos[user], pos[used])
    succ = collections.defaultdict(set)   # used -> users

    def reaches(a, b):
        seen, todo = set(), [a]
        while todo:
            x = todo.pop()
            if x == b:
                return True
            if x in seen:
                continue
            seen.add(x)
            todo.extend(succ[x])
        return False
    accepted = collections.defaultdict(list)   # (user, kind) -> [used]
    dropped = []
    for e in sorted(cand, key=prio):
        user, used, k = e
        if reaches(user, used):
            dropped.append(e)
            continue
        succ[used].add(user)
        accepted[(user, k)].append(used)
    stats['edges'] = len(cand) - len(dropped)
    stats['edges_dropped'] = len(dropped)

    def uses(me, k):
        u = sorted(set(accepted.get((me, k), [])), key=lambda x: pos[x])
        return ('\\uses{' + ', '.join(u) + '}\n') if u else ''

    def emit_section_node(sec):
        ns = section_names[sec]
        stats['extra'] += 1
        stats['leanok'] += 1
        desc = SECTION_DESC.get(sec, '')
        out.append('\\begin{remark}[Formalized statements of this section without a result '
                   'label]\\label{bp:%s}\n%s\\leanok\n%s\n\\end{remark}\n' % (sec, lean_list(ns), desc))

    SECTION_DESC = {
        'sec:prelim': 'An invertible box matrix makes a digital point set a graph form '
                      '(Section~\\ref{sec:prelim}, subsection "Graph forms").',
        'sec:frames': 'The frame layer $\\lambda_c\\mu_dw_{cd}$ is a Cauchy layer in homogeneous '
                      'coordinates (Section~\\ref{sec:frames}, subsection "Cauchy identities").',
        'app:perprime': 'The 17 resp.\\ 20 per-prime designs of Appendix~\\ref{app:perprime} '
                        'satisfy (S2), (N2), (K) resp.\\ (S1), (N1), (J).',
    }
    pending_secnode = None
    for it in items:
        if it[0] == 'appendix':
            if pending_secnode:
                emit_section_node(pending_secnode)
                pending_secnode = None
            out.append('\\appendix\n')
            continue
        if it[0] == 'head':
            lvl, title, labels = it[1], it[2], it[3]
            if lvl.startswith('section') and id(it) not in head_has:
                if pending_secnode:
                    emit_section_node(pending_secnode)
                    pending_secnode = None
                stats['chapters_dropped'] += 1
                continue
            if lvl.startswith('section') or lvl.startswith('part'):
                if pending_secnode:
                    emit_section_node(pending_secnode)
                    pending_secnode = None
                cmd = {'part': 'part', 'section': 'chapter', 'section*': 'chapter*'}[lvl]
                out.append('\n\\%s{%s}%s\n' % (cmd, fix_refs(title, known),
                                               ''.join('\\label{%s}' % x for x in labels)))
                for x in labels:
                    if x in section_names:
                        pending_secnode = x
                if lvl == 'section':
                    stats['chapters'] += 1
            elif id(it) in head_has:
                cmd = 'section' + ('*' if lvl.endswith('*') else '')
                out.append('\n\\%s{%s}%s\n' % (cmd, fix_refs(title, known),
                                               ''.join('\\label{%s}' % x for x in labels)))
                stats['sections'] += 1
            continue
        if it[0] == 'float':
            labs = [x for x in it[3] if x in TABLE_NODES]
            if not labs:
                continue
            lb = labs[0]
            text = it[2]
            cap = ''
            mc = re.search(r'\\caption\{', text)
            if mc:
                cap, _ = group(text, mc.end() - 1)
            tab = ''
            mt = re.search(r'\\begin\{tabular\}', text)
            if mt:
                t0 = mt.start()
                _, t1 = find_end(text, mt.end(), 'tabular')
                tab = text[t0:t1]
            ns = node_names.get(lb, [])
            stats['extra'] += 1
            body = '\\begin{remark}[%s]\\label{%s}\n' % (TABLE_NODES[lb], lb)
            if ns:
                body += lean_list(ns) + '\\leanok\n'
                leanok_labels.add(lb)
                stats['leanok'] += 1
            body += fix_refs(fix_math(cap), known) + '\n\n' + fix_refs(fix_math(tab), known) + '\n'
            body += '\\end{remark}\n'
            out.append(body)
            continue
        if it[0] != 'res':
            continue
        env, opt, labels, text = it[1], it[2], it[3], it[4]
        stats[env] += 1
        lb = labels[0] if labels else None
        dagger = bool(opt and '\\dagger' in opt)
        ns = []
        for x in labels:
            for n in node_names.get(x, []):
                if n not in ns:
                    ns.append(n)
        defs = [d for x in labels for d in deflab.get(x, [])]
        hn = [n for x in labels for n in held_names.get(x, [])]
        head = '\\begin{%s}%s%s\n' % (env, '[%s]' % fix_refs(opt, known) if opt else '',
                                      ''.join('\\label{%s}' % x for x in labels))
        meta = ''
        note = ''
        ok = False
        if hn and not ns:
            meta += '\\notready\n'
            note = ('\n\n\\textbf{Lean: held.} The compared statements of this result (%s) are in '
                    'the holding section \\texttt{QUNets/Statements/Hold.lean}, while the '
                    'dimension-three material is redesigned; they will be mapped again when this '
                    'section of the paper is rewritten.' % ', '.join('\\texttt{%s}' % n.replace('_', '\\_') for n in hn))
            held_nodes.append(lb)
        elif hn:
            note = ('\n\n\textbf{Lean: also held.} %s (in \\texttt{QUNets/Statements/Hold.lean}).'
                    % ', '.join('\\texttt{%s}' % n.replace('_', '\\_') for n in hn))
        if dagger and lb in DAGGER_DONE:
            allns = ns + [d for d in defs if d not in ns]
            meta += lean_list(allns) + '\\leanok\n'
            ok = True
            stg, dn = DAGGER_DONE[lb]
            note += ('\n\n\\textbf{Lean: formalized} (V14 stage %s%s); still marked $\\dagger$ in '
                     'revision 14.3.' % (stg, '; ' + dn if dn else ''))
            dagger_done_nodes.append(lb)
        elif dagger:
            dagger_nodes.append(lb)
            if ns:
                meta += lean_list(ns) + '\n'
                note += '\n\n\\textbf{Lean: partial.} ' + DAGGER_PARTIAL_NOTE.get(
                    lb, 'Formalization in progress (marked $\\dagger$ in the paper).')
        elif ns or defs:
            allns = ns + [d for d in defs if d not in ns]
            meta += lean_list(allns) + '\\leanok\n'
            ok = True
            if lb in PARTIAL:
                note += '\n\n\\textbf{Lean: assuming classical theorems.} ' + PARTIAL[lb]
        if ok:
            leanok_labels.update(labels)
            stats['leanok'] += 1
        meta += uses(lb, 'stmt') if lb else ''
        out.append(head + meta + fix_refs(fix_math(text.strip()), known) + note + '\n\\end{%s}\n' % env)
        for popt, ptext in proofs.get(lb, []):
            pm = ('\\leanok\n' if ok else '') + uses(lb, 'proof')
            out.append('\\begin{proof}%s\n%s%s\n\\end{proof}\n' % (
                '[%s]' % fix_refs(popt, known) if popt else '', pm,
                fix_refs(fix_math(ptext.strip()), known)))
            stats['proof'] += 1
    if pending_secnode:
        emit_section_node(pending_secnode)

    # held statements without a label in the paper
    grp = collections.OrderedDict()
    for n, ls in held_offpaper:
        key = ', '.join(ls) if ls else '(no label)'
        grp.setdefault(key, []).append(n)
    if held:
        out.append('\n\\chapter*{Held statements}\n')
        out.append('% TODO(m = 3 redesign): remap from STATEMENTS_INDEX.md and re-run '
                   'scripts/gen_blueprint.py when the dimension-three section is rewritten.\n')
        out.append('The holding section \\texttt{QUNets/Statements/Hold.lean} keeps %d compared '
                   'statements compiled and compared while the dimension-three, $m=3$ material is '
                   'redesigned (V14\\_PLAN.md, stage S0). %d of them belong to results of the current '
                   'paper (shown above with the note ``Lean: held\'\'). The other %d belong to labels '
                   'that are not in the current text of the paper; they are listed here by their former '
                   'labels and are not mapped to blueprint nodes.\n\n\\begin{itemize}\n'
                   % (len(held), len(held) - len(held_offpaper), len(held_offpaper)))
        for key, ns in grp.items():
            out.append('\\item %s: %s\n' % (key.replace('_', '\\_'),
                                             ', '.join('\\texttt{%s}' % n.replace('_', '\\_') for n in ns)))
        out.append('\\end{itemize}\n')
    out.append('\n' + bib + '\n')

    content = ('% Generated by scripts/gen_blueprint.py from `paper/core.tex`; do not edit.\n'
               + '\n'.join(out))
    os.makedirs(os.path.join(OUT, 'macros'), exist_ok=True)
    open(os.path.join(OUT, 'content.tex'), 'w').write(content)
    write_static(pre)

    # ---------------------------------------------------------------- checks
    in_lean = set(re.findall(r'\\lean\{([^}]*)\}', content))
    lean_names = [n.strip() for grp_ in in_lean for n in grp_.split(',')]
    deflist = {d for v in deflab.values() for d in v}
    bad = [n for n in lean_names if n not in names and n not in deflist]
    if bad:
        problems.append('\\lean names that are neither compared nor listed definitions: %s' % bad)
    ref_cmp = set(lean_names) & set(names)
    listed_held = set(held)
    missing = [n for n in names if n not in ref_cmp and n not in listed_held]
    if missing:
        problems.append('compared theorems not referenced by any \\lean: %s' % missing)
    held_in_lean = [n for n in lean_names if n in listed_held]
    if held_in_lean:
        problems.append('held theorems inside \\lean: %s' % held_in_lean)
    # tab:lean
    src = strip_comments(open(PAPER).read())
    mt = src.index('\\label{tab:lean}')
    t0 = src.rfind('\\begin{table}', 0, mt)
    tl = [x for x in refs(src[t0:mt]) if x in live_results]
    tab_held = [x for x in tl if x in held_nodes]
    tab_partial = [x for x in tl if x in dagger_nodes]
    tab_missing = [x for x in tl if x not in leanok_labels and x not in held_nodes
                   and x not in dagger_nodes]
    if tab_missing:
        problems.append('results of tab:lean without \\leanok: %s' % tab_missing)
    non_dagger_unmapped = [it[3][0] for it in results if it[3] and not (it[2] and '\\dagger' in it[2])
                           and it[3][0] not in leanok_labels and it[3][0] not in held_nodes
                           and it[1] not in ('remark',)]
    print('blueprint/src/content.tex: %d chapters (%d paper sections without results dropped), '
          '%d sections; nodes: %s' % (stats['chapters'], stats['chapters_dropped'], stats['sections'],
        ', '.join('%s %d' % (e, stats[e]) for e in RESULT_ENVS if stats[e])))
    nnodes = sum(stats[e] for e in RESULT_ENVS)
    print('result nodes %d (+%d table/section nodes), proofs %d, \\leanok %d, dagger %d (+%d dagger '
          'formalized, with \\leanok: %s), held %d'
          % (nnodes, stats['extra'], stats['proof'], stats['leanok'],
             len(dagger_nodes), len(dagger_done_nodes), ', '.join(dagger_done_nodes), len(held_nodes)))
    print('\\lean names: %d distinct (%d compared theorems of %d; %d held listed as text; '
          '%d definitions)' % (len(set(lean_names)), len(ref_cmp), len(names), len(held),
                               len(set(lean_names) - set(names))))
    print('\\uses edges: %d (dropped %d that would close a cycle: %s)' % (
        stats['edges'], stats['edges_dropped'],
        ', '.join('%s %s-uses %s' % (u, k, v) for u, v, k in dropped)))
    print('held nodes:', held_nodes)
    print('tab:lean results held (no \\leanok):', tab_held, '; dagger, partial Lean:', tab_partial)
    print('non-dagger theorem/proposition/lemma/corollary/definition nodes without \\leanok:',
          non_dagger_unmapped)
    for p in problems:
        print('PROBLEM:', p)
    print('OK' if not problems else 'PROBLEMS FOUND')
    return 1 if problems else 0


def write_static(pre):
    """web.tex, print.tex, macros, plastex.cfg, blueprint.sty, latexmkrc, extra_styles.css"""
    w = lambda p, s: open(os.path.join(OUT, p), 'w').write(s)  # noqa: E731
    # paper macros (preamble), as \newcommand
    mac = ['% Generated by scripts/gen_blueprint.py from the preamble of core.tex; do not edit.',
           '\\newtheorem{theorem}{Theorem}',
           '\\newtheorem{proposition}[theorem]{Proposition}',
           '\\newtheorem{lemma}[theorem]{Lemma}',
           '\\newtheorem{corollary}[theorem]{Corollary}',
           # numbered (with the number "A") so that plasTeX attaches their \\label to the node
           '\\newtheorem{theoremA}{Theorem}',
           '\\renewcommand{\\thetheoremA}{A}',
           '\\newtheorem{propA}{Proposition}',
           '\\renewcommand{\\thepropA}{A}',
           '\\theoremstyle{definition}',
           '\\newtheorem{definition}[theorem]{Definition}',
           '\\newtheorem{remark}[theorem]{Remark}',
           '\\theoremstyle{plain}', '']
    for m in re.finditer(r'\\(?:newcommand|providecommand)\{\\(Z|F|e|coef|Res|Q|R|N)\}(\[\d\])?', pre):
        j = m.end()
        val, _ = group(pre, j)
        mac.append('\\newcommand{\\%s}%s{%s}' % (m.group(1), m.group(2) or '', val))
    for m in re.finditer(r'\\DeclareMathOperator\{\\([A-Za-z]+)\}\{([^}]*)\}', pre):
        mac.append('\\newcommand{\\%s}{\\operatorname{%s}}' % (m.group(1), m.group(2)))
    w('macros/common.tex', '\n'.join(mac) + '\n')
    w('macros/web.tex', '% Macros for the web version only (none).\n')
    w('macros/print.tex', '% Macros for the print version only: no-op blueprint commands '
      '(leanblueprint 0.0.20 template).\n'
      '\\newcommand{\\lean}[1]{}\n\\newcommand{\\discussion}[1]{}\n\\newcommand{\\leanok}{}\n'
      '\\newcommand{\\mathlibok}{}\n\\newcommand{\\notready}{}\n\\ExplSyntaxOn\n'
      '\\NewDocumentCommand{\\uses}{m}\n {\\clist_map_inline:nn{#1}{\\vphantom{\\ref{##1}}}%\n'
      '  \\ignorespaces}\n\\NewDocumentCommand{\\proves}{m}\n'
      ' {\\clist_map_inline:nn{#1}{\\vphantom{\\ref{##1}}}%\n  \\ignorespaces}\n\\ExplSyntaxOff\n')
    thms = 'definition+lemma+proposition+theorem+corollary+remark+theoremA+propA'
    w('web.tex', '\\documentclass{report}\n'
      '\\usepackage{amssymb, amsthm, amsmath}\n\\usepackage{hyperref}\n'
      '\\usepackage[dep_graph, thms=%s]{blueprint}\n'
      '\\input{macros/common}\n\\input{macros/web}\n'
      '\\title{%s: blueprint}\n\\author{Leonhard Gruenschloss}\n'
      '\\begin{document}\n\\maketitle\n\\input{content}\n\\end{document}\n' % (thms, TITLE))
    w('print.tex', '\\documentclass[a4paper]{report}\n\\usepackage{geometry}\n\\usepackage{expl3}\n'
      '\\usepackage{amssymb, amsthm, mathtools}\n'
      '\\usepackage[unicode,colorlinks=true,linkcolor=blue,urlcolor=magenta,citecolor=blue]{hyperref}\n'
      '\\input{macros/common}\n\\input{macros/print}\n'
      '\\title{%s: blueprint}\n\\author{Leonhard Gruenschloss}\n'
      '\\begin{document}\n\\maketitle\n\\input{content}\n\\end{document}\n' % TITLE)
    w('plastex.cfg', '[general]\nrenderer=HTML5\ncopy-theme-extras=yes\n'
      'plugins=plastexdepgraph leanblueprint\n\n[document]\ntoc-depth=3\ntoc-non-files=True\n\n'
      '[files]\ndirectory=../web/\nsplit-level=0\n\n[html5]\nlocaltoc-level=0\n'
      'extra-css=extra_styles.css\nmathjax-dollars=False\n')
    # print version: no-op versions of the blueprint commands (as leanblueprint's template)
    w('blueprint.sty', '\\DeclareOption*{}\n\\ProcessOptions\n\n\\newcommand{\\graphcolor}[3]{}\n')
    w('latexmkrc', "$pdf_mode = 1;\n$pdflatex = 'xelatex -synctex=1';\n@default_files = ('print.tex');\n")
    w('extra_styles.css', '/* Extra styles for the web blueprint (none). */\n')


if __name__ == '__main__':
    sys.exit(main())

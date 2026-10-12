#!/usr/bin/env python3
"""deficit_tables.py -- Tables tab:Kdesigns and tab:practical, Proposition prop:4D2 (Part II, Section sec:deficit).

Every design / layer is read from Appendix app:designs of core.tex (the s = 7, 8 designs of tab:Kdesigns, which the
paper does not print, from designs_K.json next to this script), and every printed cell is read from core.tex.
Recomputed in exact integer arithmetic (numpy int64):
  * the relaxation LB of Lemma lem:Ss (all (2L+1)^s - 1 configurations, L = number of levels; the truncations to
    fewer levels have no smaller LB, so L = s - 1 covers every k >= 1), the deficit K(F) and S(F) of Definition def:K,
    the largest |M^(j)| and Q_D of Proposition prop:Dprime;
  * the thresholds "LB >= 1 - K/q for q >=" and "LB >= .5/.8/.9 for q >=": the least admissible q_0 such that the
    exact LB holds at every admissible q in [q_0, max(Q_D, K/(1-c))], and Proposition prop:Dprime (LB >= 1 - K/q for
    q >= Q_D) beyond; admissible = every prime factor >= s - 1 (tab:Kdesigns) resp. the base sets of tab:practical;
  * tab:practical: K_1 of each level-0 layer (attained by a one-axis step), its thresholds q_0 for c = .5, .8, .9 at
    k = 1 (Proposition prop:k1(1): L = 1), the sizes N = q_0^s (rounded as printed), the s = 3 row from c(q) of
    Theorem thm:main (N = q^6), the frame layers' off-diagonal parts (U*_4 resp. the s = 5 design), and the remarks
    of the caption and of the introduction (13^5, 19^6, 15^8, 29^10, 59^12, q = 23);
  * prop:4D2: 2400 configurations, K(F) = 2, S(F) = 7, Q_D = 23, LB = (q-2)/q at q = 17, 19, 21, column inf of F_0 =
    (-2,1,1,1), |F_0| <= 2, and the inequality 6/alpha <= 102/15 (alpha = 1-2/q >= 15/17) with 102/15 < 8 (rev 15.1: k >= 2).
The s = 7, 8 rows of tab:Kdesigns: S(F), largest |M^(j)| and Q_D are recomputed; K(F) (13^7, 15^8 configurations)
and the thresholds are not (the paper states them as computed values; K is taken from designs_K.json and asserted
equal to the printed value).

    uv run --with numpy --with python-flint python scripts/deficit_tables.py      (~15 s, ~0.5 GB)
"""
import json
import math
import os
import re
import sys
import time
from fractions import Fraction as Fr

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
CORE = os.path.join(os.path.dirname(HERE), 'core.tex')
TEX = open(CORE).read()
LINES = TEX.split('\n')
BAD = []
T0 = time.time()


def ok(label, cond, detail=''):
    print(f'  {"ok      " if cond else "MISMATCH"} {label}' + (f'   [{detail}]' if detail else ''))
    if not cond:
        BAD.append(label)


# ------------------------------------------------------------------------------------------------ core.tex
def table_rows(label):
    i = next(i for i, l in enumerate(LINES) if '\\label{%s}' % label in l)
    j = max(j for j in range(i) if '\\begin{table}' in LINES[j])
    out = []
    for l in LINES[j:i]:
        if '&' in l and '\\begin{tabular}' not in l:
            t = l.strip()
            if t.endswith('\\\\'):
                t = t[:-2]
            out.append([c.strip() for c in t.split('&')])
    return out


def row(rows, head):
    r = [r for r in rows if r[0].startswith(head)]
    assert len(r) == 1, (head, r)
    return r[0][1:]


def psmall(text):
    out = []
    for body in re.findall(r'\\begin\{psmallmatrix\}(.*?)\\end\{psmallmatrix\}', text):
        out.append([[int(x) for x in r.split('&')] for r in body.split('\\\\')])
    return out


def app_section(start, end):
    a = TEX.index(start)
    return TEX[a:TEX.index(end, a)]


def parse_N(cell):
    """'$1.6\\cdot10^4$' / '$10^6$' -> (value, unit of the last printed digit or None if printed exactly)."""
    c = cell.replace('$', '').replace('{', '').replace('}', '').strip()
    m = re.fullmatch(r'10\^(\d+)', c)
    if m:
        return 10 ** int(m.group(1)), None
    m = re.fullmatch(r'([0-9.]+)\\cdot10\^(\d+)', c)
    assert m, cell
    mant, e = m.group(1), int(m.group(2))
    d = len(mant.split('.')[1]) if '.' in mant else 0
    return Fr(mant) * 10 ** e, Fr(10 ** e, 10 ** d)


def N_ok(N, cell):
    v, u = parse_N(cell)
    return N == v if u is None else v <= N < v + u      # rev 15.2: truncated (was: nearest)


# ------------------------------------------------------------------------------------------------ relaxation
class Design:
    """all configurations (e, j) of a design F = (F_0, ..., F_{L-1}) (Lemma lem:Ss, Definition def:K)."""

    def __init__(self, F):
        self.F, self.L, self.s = F, len(F), len(F[0])
        s, L = self.s, self.L
        acc = np.zeros((s, s), dtype=np.int64)
        Ms = []
        for j in range(L):
            acc = acc + np.array(F[j], dtype=np.int64)
            Ms.append(acc.copy())
        self.Ms = Ms
        SIG = np.zeros((1, s), dtype=np.int64)
        EV = np.zeros((1, 0), dtype=np.int64)
        for d in range(s):
            opts = [(0, np.zeros(s, dtype=np.int64))] + [(e, e * Ms[j][:, d]) for e in (1, -1) for j in range(L)]
            C = np.array([o[1] for o in opts])
            Ev = np.array([o[0] for o in opts], dtype=np.int64)
            n_old, n_opt = SIG.shape[0], C.shape[0]
            SIG = (SIG[:, None, :] + C[None, :, :]).reshape(-1, s)
            EV = np.concatenate([np.repeat(EV, n_opt, axis=0), np.tile(Ev, n_old)[:, None]], axis=1)
        keep = np.any(EV != 0, axis=1)
        self.SIG, self.EV = SIG[keep], EV[keep]
        mov = (self.EV != 0).sum(1)
        self.jit = np.ones_like(self.EV)
        self.jit[(mov == 1)[:, None] & (self.EV != 0)] = 0          # jit_i = 0 iff e = +-e_i
        self.nconf = self.SIG.shape[0]

    def K_S(self):
        mv = self.EV != 0
        back = mv & (self.EV * self.SIG <= 0)
        nb = back.sum(1)
        assert (nb > 0).all(), 'a configuration without backward coordinate: K = infinity'
        one = nb == 1
        b = np.argmax(back[one], axis=1)
        r = np.arange(b.size)
        cost = np.abs(self.SIG[one][r, b]) + self.jit[one][r, b]
        K = int(cost.max()) if cost.size else 0
        S = int(np.abs(self.SIG).max())
        S_formula = max(sum(max(abs(int(self.Ms[j][i][d])) for j in range(self.L)) for d in range(self.s))
                        for i in range(self.s))
        assert S == S_formula
        return K, S

    def S2(self, q):
        """min over configurations of sum_i b_i^2 (exact integer); LB = min(1, sqrt(S2)/q)."""
        EV, jit = self.EV, self.jit
        dl = np.mod(self.SIG, q)
        o1 = np.abs(EV * q + dl)
        o2 = np.where(dl != 0, np.abs(EV * q + dl - q), o1)
        b = np.maximum(0, np.minimum(o1, o2) - jit)
        return int((b * b).sum(1).min())

    def max_M(self):
        return max(abs(int(self.Ms[j][c][d])) for j in range(self.L) for c in range(self.s) for d in range(self.s)
                   if c != d)


def partial_sums(F):
    out, acc = [], [[0] * len(F[0]) for _ in F[0]]
    for Fj in F:
        acc = [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(acc, Fj)]
        out.append(acc)
    return out


def QD(K, S):
    """max(S+1, ceil((sqrt2 (S+1) - K)/(sqrt2 - 1))) = max(S+1, 2(S+1) - K + ceil(sqrt2 (S+1-K))), exact."""
    x = S + 1 - K
    c = math.isqrt(2 * x * x)
    if c * c < 2 * x * x:
        c += 1
    return max(S + 1, 2 * (S + 1) - K + c)


def lb_ge(S2, q, c):        # min(1, sqrt(S2)/q) >= c, c a Fraction < 1
    return Fr(S2, q * q) >= c * c


def thresholds(D, K, Q_D, adm, cs, qlo=3):
    """least admissible q_0 for LB >= 1-K/q (exact below Q_D) and for LB >= c, c in cs (exact up to
    max(Q_D, K/(1-c)), Proposition prop:Dprime beyond)."""
    top = max([Q_D] + [math.ceil(K / (1 - c)) for c in cs])
    qs = [q for q in range(qlo, top + 1) if adm(q)]
    S2 = {q: D.S2(q) for q in qs}
    out = {}
    good = [S2[q] >= (q - K) ** 2 or S2[q] >= q * q for q in qs if q < Q_D]
    bad = [q for q, g in zip([q for q in qs if q < Q_D], good) if not g]
    out['1-K/q'] = next(q for q in qs if q > max(bad, default=0))
    for c in cs:
        bad = [q for q in qs if not lb_ge(S2[q], q, c)]
        out[c] = next(q for q in qs if q > max(bad, default=0))
        assert all(lb_ge((q - K) ** 2, q, c) for q in range(top + 1, top + 50))      # the tail beyond top
    return out, S2


def lpf_ge(m):
    return lambda q: all(q % r for r in range(2, m))


CS = (Fr(1, 2), Fr(4, 5), Fr(9, 10))


def main():
    import ustar_det          # U*_4 (frame layer of tab:practical); needs python-flint
    kd_txt = app_section('\\subsection{The designs of Table', '\\subsection{The layers of Table')
    pr_txt = app_section('\\subsection{The layers of Table', '\\subsection{The five-dimensional')
    Mk = psmall(kd_txt)
    assert len(Mk) == 3 + 4 + 5, len(Mk)
    DES = {4: Mk[0:3], 5: Mk[3:7], 6: Mk[7:12]}
    JK = json.load(open(os.path.join(HERE, 'designs_K.json')))
    for s in (4, 5, 6):
        ok(f'tab:Kdesigns s={s}: design printed in app:designs == designs_K.json', DES[s] == JK[str(s)]['F'])
    DES[7], DES[8] = JK['7']['F'], JK['8']['F']
    J4 = json.load(open(os.path.join(HERE, 'dim4_deficit2_design.json')))
    ok('prop:4D2 design == dim4_deficit2_design.json (used by figs_arc.py)', DES[4] == J4['F'])

    # ---------------------------------------------------------------- tab:Kdesigns
    print('Table tab:Kdesigns')
    rk = table_rows('tab:Kdesigns')
    SK = [int(x) for x in row(rk, '$s$')]
    pK = dict(zip(SK, row(rk, 'certified deficit')))   # rev 15.7 pass 3 row labels
    pSM = dict(zip(SK, row(rk, '$\\sigma_{\\max}(F)$')))
    pQ = dict(zip(SK, row(rk, '$q_{\\mathrm{tail}}$')))
    p1K = dict(zip(SK, row(rk, '$\\mathrm{LB}\\ge1-K/q$')))
    pc = dict(zip(SK, row(rk, '$\\mathrm{LB}\\ge.5/.8/.9$')))
    KD = {}
    for s in SK:
        t = time.time()
        S_, M_ = (int(x) for x in pSM[s].split(';'))
        Ms = partial_sums(DES[s])
        mx = max(abs(Ms[j][c][d]) for j in range(len(Ms)) for c in range(s) for d in range(s) if c != d)
        if s <= 6:
            D = Design(DES[s])
            K, S = D.K_S()
            ok(f's={s} K(F) = {K} (all {D.nconf} configurations)', str(K) == pK[s], f'printed {pK[s]}')
        else:                 # (2s-1)^s configurations: too many for this script
            D, K = None, JK[str(s)]['K']
            S = max(sum(max(abs(Ms[j][i][d]) for j in range(len(Ms))) for d in range(s)) for i in range(s))
            ok(f's={s} K(F) = {K} from designs_K.json (not recomputed)', str(K) == pK[s], f'printed {pK[s]}')
        ok(f's={s} S(F) = {S}', S == S_, f'printed {S_}')
        ok(f's={s} largest |M^(j)| = {mx}', mx == M_, f'printed {M_}')
        q_d = QD(int(pK[s]), S_)
        ok(f's={s} Q_D = {q_d} (from the printed K, S)', str(q_d) == pQ[s], f'printed {pQ[s]}')
        KD[s] = (D, K, S)
        if s <= 6:
            th, _ = thresholds(D, K, q_d, lpf_ge(s - 1), CS)
            ok(f's={s} LB >= 1-K/q for admissible q >= {th["1-K/q"]}', str(th['1-K/q']) == p1K[s], f'printed {p1K[s]}')
            got = '/'.join(str(th[c]) for c in CS)
            ok(f's={s} LB >= .5/.8/.9 for admissible q >= {got}', got == pc[s], f'printed {pc[s]}')
        print(f'      ({time.time() - t:.1f} s)')
    th8 = {s: pc[s].split('/')[1] for s in SK}

    # ---------------------------------------------------------------- prop:4D2
    print('Proposition prop:4D2')
    D4, K4, S4 = KD[4]
    ok('2400 configurations, K(F) = 2, S(F) = 7', D4.nconf == 2400 and K4 == 2 and S4 == 7)
    ok('q_tail = 23', QD(2, 7) == 23 and '$q_{\\mathrm{tail}}=23$' in TEX)
    ok('LB = (q-2)/q exactly at q = 17, 19, 21 (L = 3)', all(D4.S2(q) == (q - 2) ** 2 for q in (17, 19, 21)))
    F0 = DES[4][0]
    ok('column inf of F_0 = (-2,1,1,1), |F_0| <= 2', [r[0] for r in F0] == [-2, 1, 1, 1]
       and max(abs(x) for r in F0 for x in r) <= 2)
    alpha = Fr(15, 17)                       # rev 15.1 (k >= 2, no q^{1-k} term by (H2)): alpha = 1 - 2/q >= 1 - 2/17
    ok('6/alpha <= 102/15 for alpha >= 15/17, and 102/15 < 8 (prop:4D2(3), k >= 2)', 6 / alpha == Fr(102, 15)
       and Fr(102, 15) < 8 and '\\frac{102}{15}/q^2<1-2/q+8/q^2' in TEX and 'every $k\\ge2$, toroidal or Euclidean' in TEX)

    # ---------------------------------------------------------------- tab:practical
    print('Table tab:practical (k = 1, L = 1)')
    LAY = psmall(pr_txt)
    assert len(LAY) == 6, len(LAY)
    U4 = ustar_det.construct(4)[0][0]
    off = lambda A: [[A[c][d] for d in range(len(A)) if d != c] for c in range(len(A))]
    ok('frame layer s=4: off-diagonal part = that of U*_4', off(LAY[0]) == off(U4))
    ok('frame layer s=5: off-diagonal part = that of the s=5 design of tab:Kdesigns', off(LAY[1]) == off(DES[5][0]))
    E6 = (2, 3, 5, 7, 11, 13, 17, 23, 31)
    rp = table_rows('tab:practical')
    rp = [r for r in rp if r[0].strip().isdigit()]
    assert [r[0] for r in rp] == ['3', '4', '5', '5', '6', '6', '6'], [r[0] for r in rp]
    # (layer, admissible q, printed base set) in the order of the table rows 2..7
    spec = [(LAY[0], lambda q: q % 2 == 1, 'odd'),
            (LAY[3], lambda q: math.gcd(q, 30) == 1, '$(q,30)=1$'),
            (LAY[1], lambda q: math.gcd(q, 6) == 1, '$(q,6)=1$'),
            (LAY[4], lambda q: all(q % r for r in E6), 'no prime factor in $\\mathcal E_6$'),
            (LAY[5], lambda q: math.gcd(q, 210) == 1, '$(q,210)=1$'),
            (LAY[2], lambda q: math.gcd(q, 6) == 1, '$(q,6)=1$')]
    ok('prop:k1designs: E_6 = {2,3,5,7,11,13,17,23,31}', '$\\mathcal E_6=\\{2,3,5,7,11,13,17,23,31\\}$' in TEX)
    # s = 3: Theorem thm:main, c(q) = min((1-1/q)^2, (1-2/q)^2+(1-4/q)^2, 3(1-3/q)^2)^(1/2), every q >= 4
    c3 = lambda q: min((1 - Fr(1, q)) ** 2, (1 - Fr(2, q)) ** 2 + (1 - Fr(4, q)) ** 2, 3 * (1 - Fr(3, q)) ** 2)
    r3 = rp[0]
    for c, cell in zip(CS, r3[4:7]):
        q0 = 1 + max(q for q in range(4, 2000) if c3(q) < c * c)
        q0p, Np = (x.strip() for x in cell.split(';'))
        ok(f's=3 c(q) >= {float(c)} for every q >= {q0}; N = q0^6 = {q0 ** 6}', q0p == f'${q0}$' and N_ok(q0 ** 6, Np),
           f'printed {cell}')
    q0s = {5: [], 6: []}
    for (F0, adm, bases), r in zip(spec, rp[1:]):
        s = int(r[0])
        D = Design([F0])
        K1, S1 = D.K_S()
        ok(f's={s} {r[1][:28]:28s} K_1 = {K1}', str(K1) == r[2], f'printed {r[2]}')
        ok(f's={s} K_1 attained by a one-axis step (max_a -F_0[a][a] = K_1)', max(-F0[a][a] for a in range(s)) == K1)
        ok(f's={s} base set printed "{bases}"', r[3] == bases, f'printed {r[3]}')
        th, S2 = thresholds(D, K1, QD(K1, S1), adm, CS)
        for c, cell in zip(CS, r[4:7]):
            q0 = th[c]
            q0p, Np = (x.strip() for x in cell.split(';'))
            ok(f's={s}   c >= {float(c)} for admissible q >= {q0}; N = q0^{s} = {q0 ** s}',
               q0p == f'${q0}$' and N_ok(q0 ** s, Np), f'printed {cell}')
            if c == CS[1] and s in q0s:
                q0s[s].append(q0)
        if s == 6 and r[2] in ('5', '6'):
            ok(f's=6 K_1={K1}: q=23 admissible, LB_1(23) < .8 (caption)', adm(23) and not lb_ge(S2[23], 23, CS[1]))
        if s == 6 and r[2] == '3':
            ok('s=6 K_1=3: q=23 not admissible (caption)', not adm(23))
    ok(f'intro: delta N^(1/5) >= 0.8 from N = 13^5 = {13 ** 5} ~ 3.7e5', min(q0s[5]) == 13
       and '$N=13^5\\approx3.7\\cdot10^5$' in TEX and N_ok(13 ** 5, '$3.7\\cdot10^5$'))
    ok(f'intro: delta N^(1/6) >= 0.8 from N = 19^6 = {19 ** 6} ~ 4.7e7', min(q0s[6]) == 19
       and '$N=19^6\\approx4.7\\cdot10^7$' in TEX and N_ok(19 ** 6, '$4.7\\cdot10^7$'))
    for s, q, Np in ((4, 15, '$2.5\\cdot10^9$'), (5, 29, '$4.2\\cdot10^{14}$'), (6, 59, '$1.7\\cdot10^{21}$')):
        # rev 15.2: sizes truncated, written with \approx
        txt = f'$N={q}^{2 * s}\\approx{Np[1:]}' if s == 4 else f'${q}^{{{2 * s}}}\\approx{Np[1:]}'
        ok(f'caption: k=2, s={s}: c >= .8 from N = {q}^{2 * s} ~ {Np}', th8[s] == str(q) and N_ok(q ** (2 * s), Np)
           and txt in TEX, f'.8 threshold of tab:Kdesigns: {th8[s]}')
    print(f'deficit_tables: {"all values agree with core.tex" if not BAD else f"{len(BAD)} MISMATCH(ES): {BAD}"}'
          f' ({time.time() - T0:.1f} s)')
    sys.exit(1 if BAD else 0)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""half5_qstar.py -- exact checks for the s = 5 one-resolution net Q*_p (layer F0*, lean D1, sparse D2, D3) and
the comparison layer M5 of Proposition prop:half5.

Q*_p: the point with index n in F_p^5 has, in coordinate c, the digits n_c, (F0* n)_c, (D1 n)_c, (D2 n)_c,
(D3 n)_c, with 1/2 == (p+1)/2 mod p.  We store H = 2 F0 (odd integers).

Checks (all exact: Python integers and fractions.Fraction; floats only for printing):
  (a) the 126 box minors of Q* (graph form, depths (1,...,1); lem:box, lem:nie) are nonzero rationals with
      prime factors in {2,3,5}; a direct mod-p count of singular boxes is 0 at p = 7,11,13,31,37,257; control:
      the same code on prop:half5's printed M5, D1..D3 gives exactly prop:half5(1)'s exceptional set;
  (b) det(2F0*) = -880; F0* skew off the diagonal; alpha = (3,3,3,3,1)/2, sum 13/2; the |entry| = 3/2 graph is
      a path P4 on rows {0,1,2,3}; row 4 is the light row;
  (c) the hypotheses of Lemma R2 / prop:Hk(1): max|(2F0* E)_c| = 22, max|(D1 E)_c| = 24 over E in {-2..2}^5;
  (d) dr(F0*) = 17/2 = dj(F0*, D1); the binding steps attaining 17/2 (up to sign);
  (e) condition (Lambda): the leading length^2 is >= 2 on every non-binding E in {-2..2}^5 (F0* and M5), and
      lambda^2 = 5/4 is attained exactly on the 122 binding steps;
  (f) the scans LB_R2 (Q*, primes 29 <= p < 200) and LB_Hk (prop:Hk(1), k = 1; F0* primes 23 <= p < 400, M5)
      with their exact monotone tails, and the coarse variant LB' of prop:half5's proof for M5;
  (g) the drift accounting of M5 (and of F0* on the full steps).
What is covered: (a) is a proof of t = 0 for every prime p >= 7 via lem:nie (finitely many exact minors);
(f)'s scans are finite, and the statements for all larger p rest on the monotone tails (proved in the notes /
in prop:Hk's remark), evaluated here exactly at one p.  Nothing else is extrapolated.

    uv run python scripts/half5_qstar.py         (~2 s)
Exit status 0 iff every check passes; last line 'half5_qstar: ALL OK'.
"""
import sys
import time
from fractions import Fraction as Fr
from itertools import product
from math import isqrt

S = 5
# ---- Q* ----
HQ = [[-3, -3, -3, -1, -1],
      [3, -3, -1, -3, 1],
      [3, 1, -3, 1, -1],
      [1, 3, -1, -3, -1],
      [1, -1, 1, 1, -1]]
D1Q = [[-2, 0, -1, -1, 1],
       [0, -1, -1, -1, -1],
       [2, -1, -3, 1, 0],
       [-1, 2, -1, -2, 0],
       [-1, -1, 3, 2, -5]]
D2Q = [[0, -1, -1, 0, 0],
       [-1, 0, 0, 0, -1],
       [-1, -1, 0, 0, 0],
       [-1, -1, 0, 0, 0],
       [-1, -1, 0, 0, 0]]
D3Q = [[0, -1, 0, 0, 0],
       [-1, 0, 0, 0, 0],
       [-1, 0, 0, 0, 0],
       [-1, 0, 0, 0, 0],
       [-1, 0, 0, 0, 0]]
# ---- prop:half5 (core.tex) ----
HM = [[-5, 3, 1, -3, 1],
      [-3, -3, 3, -1, -1],
      [1, -1, -5, -3, 3],
      [-1, -1, 3, -7, 1],
      [3, -1, 1, -1, -3]]
D1M = [[-1, 1, -1, -4, -2], [-1, 4, 0, -1, -3], [-4, 1, 1, 1, 2], [-3, -1, 0, -3, 2], [-1, 3, -1, -2, 4]]
D2M = [[4, 3, 0, 1, -3], [-3, 3, 2, 0, 2], [-3, -4, 0, -1, -2], [-2, -2, 1, -1, 1], [-4, -3, -1, 0, 3]]
D3M = [[4, -4, -4, 3, -1], [4, -1, 3, -1, -4], [3, -3, -1, -2, 3], [-1, 1, -4, -1, -3], [-2, -3, 3, 4, 1]]

ALLE = [E for E in product(range(-2, 3), repeat=S) if any(E)]                       # 3124 steps
BIND = [E for E in product((-1, 0, 1), repeat=S) if sum(E) % 2]                     # 122 binding steps
FULL = [E for E in BIND if all(E)]                                                   # 32 full steps

FAILS = []


def check(ok, msg):
    print(('  OK    ' if ok else '  FAIL  ') + msg, flush=True)
    if not ok:
        FAILS.append(msg)
    return ok


def sgn(x):
    return (x > 0) - (x < 0)


def matvec(A, E):
    return [sum(A[c][d] * E[d] for d in range(S)) for c in range(S)]


def primes_in(a, b):
    return [q for q in range(max(a, 2), b) if all(q % r for r in range(2, isqrt(q) + 1))]


def trunc(sq, scale2, digits=6):
    """floor(10^digits * min(2, sqrt(sq)/sqrt(scale2))) as a decimal string (scale2 a perfect square)."""
    r = isqrt(scale2)
    assert r * r == scale2
    f = min(2 * 10 ** digits, isqrt(sq * 10 ** (2 * digits)) // r)
    return f'{f // 10 ** digits}.{f % 10 ** digits:0{digits}d}'


def trunc_fr(x, digits=6):
    """truncation of a nonnegative Fraction"""
    f = (x.numerator * 10 ** digits) // x.denominator
    return f'{f // 10 ** digits}.{f % 10 ** digits:0{digits}d}'


# ---------------- exact linear algebra ----------------
def det(A):
    A = [[Fr(x) for x in r] for r in A]
    n, d = len(A), Fr(1)
    for k in range(n):
        piv = next((i for i in range(k, n) if A[i][k] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != k:
            A[k], A[piv] = A[piv], A[k]
            d = -d
        d *= A[k][k]
        for i in range(k + 1, n):
            f = A[i][k] / A[k][k]
            if f:
                for j in range(k, n):
                    A[i][j] -= f * A[k][j]
    return d


def detmod(M, p):
    A = [[x % p for x in r] for r in M]
    n, d = len(A), 1
    for k in range(n):
        piv = next((i for i in range(k, n) if A[i][k]), None)
        if piv is None:
            return 0
        if piv != k:
            A[k], A[piv] = A[piv], A[k]
            d = -d
        d = d * A[k][k] % p
        inv = pow(A[k][k], p - 2, p)
        for i in range(k + 1, n):
            f = A[i][k] * inv % p
            if f:
                for j in range(k, n):
                    A[i][j] = (A[i][j] - f * A[k][j]) % p
    return d % p


def prime_factors(n):
    n, fs, q = abs(n), set(), 2
    while q * q <= n:
        while n % q == 0:
            fs.add(q)
            n //= q
        q += 1
    if n > 1:
        fs.add(n)
    return fs


def compositions(m, s):
    if s == 1:
        yield (m,)
        return
    for a in range(m + 1):
        for rest in compositions(m - a, s - 1):
            yield (a,) + rest


def gen_rows(H, Ds):
    """rational generator matrix of coordinate c: rows e_c, F0_c, D1_c, D2_c, D3_c"""
    return [[[Fr(int(d == c)) for d in range(S)], [Fr(H[c][d], 2) for d in range(S)]]
            + [[Fr(D[c][d]) for d in range(S)] for D in Ds] for c in range(S)]


def gens_mod(H, Ds, p):
    half = (p + 1) // 2
    return [[[int(d == c) for d in range(S)], [H[c][d] * half % p for d in range(S)]]
            + [[D[c][d] % p for d in range(S)] for D in Ds] for c in range(S)]


def box_minors(H, Ds):
    """the 126 box minors at depths (1,...,1) (lem:box): the first d_c rows of each coordinate, sum d_c = 5"""
    C = gen_rows(H, Ds)
    return [(d, det([row for c in range(S) for row in C[c][:d[c]]])) for d in compositions(S, S)]


def singular_boxes_mod(H, Ds, p):
    G = gens_mod(H, Ds, p)
    return [d for d in compositions(S, S) if detmod([row for c in range(S) for row in G[c][:d[c]]], p) == 0]


# ---------------- drift / jitter accounting ----------------
def drift2(H, E):
    """2 dr(E) = sum_c 2 dr_c, dr_c = |beta_c| (E_c = 0), -E_c beta_c (E_c != 0), beta = F0 E = HE/2"""
    h = matvec(H, E)
    return sum(abs(h[c]) if E[c] == 0 else -E[c] * h[c] for c in range(S))


def bsign(H, E):
    h = matvec(H, E)
    return [E[c] if E[c] else -sgn(h[c]) for c in range(S)]


def n_harmful(H, D1, E):
    s, v = bsign(H, E), matvec(D1, E)
    return sum(1 for c in range(S) if v[c] != 0 and sgn(v[c]) == s[c])


def dr(H):
    return Fr(max(drift2(H, E) for E in BIND), 2)


def dj(H, D1):
    return max(Fr(drift2(H, E), 2) + n_harmful(H, D1, E) for E in BIND)


def canon_sign(E):
    f = next(x for x in E if x)
    return tuple(E) if f > 0 else tuple(-x for x in E)


# ---------------- leading length (prop:half5's proof) ----------------
def lead_len2(H, E):
    odd = sum(E) % 2 != 0
    h = matvec(H, E)
    tot = Fr(0)
    for c in range(S):
        if odd:
            l = min(abs(E[c] + Fr(1, 2)), abs(E[c] - Fr(1, 2)))
        else:
            l = abs(Fr(E[c])) if h[c] == 0 else min(abs(Fr(E[c])), abs(Fr(E[c] - sgn(h[c]))))
        tot += l * l
    return tot


# ---------------- the relaxations (exact integers) ----------------
class Steps:
    """per-step data independent of p: E, parity, h = 2 F0 E, v = D1 E"""
    def __init__(self, H, D1=None):
        self.rows = [(E, sum(E) % 2 != 0, matvec(H, E), matvec(D1, E) if D1 else None) for E in ALLE]
        self.maxh = max(abs(x) for _, _, h, _ in self.rows for x in h)
        self.maxv = max(abs(x) for _, _, _, v in self.rows for x in v) if D1 else None


def ropts(h, odd, p):
    """integers in (-p,p) congruent to beta_c = h/2 (with 1/2 == (p+1)/2), valid if |h| < p"""
    if odd:
        return ((h + p) // 2, (h - p) // 2)
    b = h // 2
    return (0,) if b == 0 else (b, b - p * sgn(b))


def dopts(v, p):
    return (0,) if v == 0 else (v, v - p * sgn(v))


def ropts_free(h, p):
    """hypothesis-free: the integers in (-p,p) congruent to h * (p+1)/2 mod p"""
    t = h * ((p + 1) // 2) % p
    return (0,) if t == 0 else (t, t - p)


def lb_r2_sq(st, p, free=False):
    """Lemma R2: min_E sum_c b_c^2 (scale p^4), b_c = min_{t,u} max(0, |p^2 E_c + p t + u| - 1); argmin E.
    free=True reduces both residues mod p (no hypothesis on p; equals R2 when the hypotheses hold)."""
    pp = p * p
    best, arg = None, None
    for E, odd, h, v in st.rows:
        tot = 0
        for c in range(S):
            T = ropts_free(h[c], p) if free else ropts(h[c], odd, p)
            U = (lambda t: (0,) if t == 0 else (t, t - p))(v[c] % p) if free else dopts(v[c], p)
            base = pp * E[c]
            b = min(abs(base + p * t + u) for t in T for u in U) - 1
            if b > 0:
                tot += b * b
                if best is not None and tot >= best:
                    break
        if best is None or tot < best:
            best, arg = tot, E
    return best, arg


def lb_hk_sq(st, p, coarse=False):
    """prop:Hk(1) at k = 1: min_E sum_c b_c^2 (scale p^2), b_c = min_t max(0, |p E_c + t| - 1).
    coarse=True: prop:half5's LB' (sigma_E odd: b'_c = max(0, min_+- p|E_c +- 1/2| - |beta_c| - 1), computed
    as max(0, min_+- (|2pE_c +- p| - |h|) / 2 - 1), which is exact since |2pE_c +- p| and |h| are odd)."""
    best, arg = None, None
    for E, odd, h, _ in st.rows:
        tot = 0
        for c in range(S):
            if coarse and odd:
                b = min(abs(2 * p * E[c] + p), abs(2 * p * E[c] - p)) - abs(h[c])
                b = b // 2 - 1
            else:
                b = min(abs(p * E[c] + t) for t in ropts(h[c], odd, p)) - 1
            if b > 0:
                tot += b * b
                if best is not None and tot >= best:
                    break
        if best is None or tot < best:
            best, arg = tot, E
    return best, arg


def tail_r2_sq(st, p):
    """L*(p)^2 for Lemma R2 (exact): per option p^2 a + p b + v (a, b, v independent of p) contributes
    max(0, |a| - |b|/p - (|v|+1)/p^2), nondecreasing in p; min over options, sum of squares, min over E, cap 4."""
    p = Fr(p)
    best = None
    for E, odd, h, vv in st.rows:
        tot = Fr(0)
        for c in range(S):
            if odd:
                rset = [(Fr(1, 2), Fr(h[c], 2)), (Fr(-1, 2), Fr(h[c], 2))]
            else:
                b0 = h[c] // 2
                rset = [(Fr(0), Fr(b0))] if b0 == 0 else [(Fr(0), Fr(b0)), (Fr(-sgn(b0)), Fr(b0))]
            v = vv[c]
            dset = [(0, 0)] if v == 0 else [(0, v), (-sgn(v), v)]
            m = min(max(Fr(0), abs(E[c] + ka) - abs(kb + kd) / p - (abs(cv) + 1) / (p * p))
                    for ka, kb in rset for kd, cv in dset)
            tot += m * m
        best = tot if best is None else min(best, tot)
    return min(Fr(4), best)


def tail_hk_sq(st, p):
    """L*(p)^2 for prop:Hk(1): per option |alpha p + beta_c| - 1 >= |alpha| p - |beta_c| - 1 (prop:Hk remark)."""
    p = Fr(p)
    best = None
    for E, odd, h, _ in st.rows:
        tot = Fr(0)
        for c in range(S):
            if odd:
                al = (E[c] + Fr(1, 2), E[c] - Fr(1, 2))
            else:
                b0 = h[c] // 2
                al = (Fr(E[c]),) if b0 == 0 else (Fr(E[c]), Fr(E[c] - sgn(b0)))
            m = min(max(Fr(0), abs(a) - abs(Fr(h[c], 2)) / p - 1 / p) for a in al)
            tot += m * m
        best = tot if best is None else min(best, tot)
    return min(Fr(4), best)


STQ = None   # lazily built Steps objects
STM = None


def steps():
    global STQ, STM
    if STQ is None:
        STQ, STM = Steps(HQ, D1Q), Steps(HM, D1M)
    return STQ, STM


# =====================================================================================================
def part_a():
    print('(a) t = 0: the 126 box minors (lem:box, lem:nie)')
    for name, H, Ds, expect in (('Q*', HQ, (D1Q, D2Q, D3Q), {2, 3, 5}),
                                ('M5 (prop:half5, control)', HM, (D1M, D2M, D3M),
                                 {2, 3, 5, 7, 11, 13, 17, 29, 41, 47, 257})):
        mins = box_minors(H, Ds)
        zero = [d for d, v in mins if v == 0]
        ps = set()
        for _, v in mins:
            if v:
                ps |= prime_factors(v.numerator) | prime_factors(v.denominator)
        check(len(mins) == 126 and not zero and ps == expect,
              f'{name}: {len(mins)} minors, {len(zero)} zero, primes of numerators/denominators {sorted(ps)}')
    for p in (7, 11, 13, 31, 37, 257):
        n = len(singular_boxes_mod(HQ, (D1Q, D2Q, D3Q), p))
        check(n == 0, f'Q* mod p = {p}: {n} singular box minors')
    nm = {p: len(singular_boxes_mod(HM, (D1M, D2M, D3M), p)) for p in (7, 31, 257)}
    check(nm[7] > 0 and nm[257] > 0 and nm[31] == 0, f'M5 control mod p: singular boxes {nm} (7, 257 exceptional)')


def part_b():
    print('(b) the layer F0*')
    d = det(HQ)
    check(d == -880, f'det(2F0*) = {d}')
    check(all(HQ[c][d] == -HQ[d][c] for c in range(S) for d in range(S) if c != d), 'F0* is skew off the diagonal')
    check(all(x % 2 for r in HQ for x in r), 'every entry of 2F0* is odd (Half)')
    alpha = [Fr(-HQ[c][c], 2) for c in range(S)]
    check(alpha == [Fr(3, 2)] * 4 + [Fr(1, 2)] and sum(alpha) == Fr(13, 2),
          f'alpha = ({", ".join(map(str, alpha))}), sum = {sum(alpha)}')
    check(all(alpha[c] == Fr(max(abs(HQ[c][e]) for e in range(S) if e != c), 2) for c in range(S)),
          'minimal diagonal: alpha_c = max_{d != c} |F0*[c][d]| (B2 with equality)')
    edges = sorted((c, e) for c in range(S) for e in range(c + 1, S) if abs(HQ[c][e]) == 3)
    deg = [sum(1 for e in edges if c in e) for c in range(S)]
    # P4 on {0,1,2,3}: 3 edges, degrees (2,2,1,1) there (a graph with these degrees on 4 vertices is a path)
    check(len(edges) == 3 and sorted(deg[:4]) == [1, 1, 2, 2] and deg[4] == 0,
          f'|entry| = 3/2 graph: edges {edges}, degrees {deg} = path P4 on rows {{0,1,2,3}}')
    check(all(abs(HQ[4][e]) == 1 for e in range(S)), 'row 4 is the light row: all entries +-1/2')
    mins = [HQ[a][c] * HQ[b][d] - HQ[a][d] * HQ[b][c] for a in range(S) for b in range(S) if a != b
            for c in range(S) for d in range(c + 1, S) if len({a, b, c, d}) == 4]
    check(all(mins), f'(MIN): all off-diagonal entries and all {len(mins) // 2} disjoint 2x2 minors of F0* nonzero')


def part_c():
    print('(c) hypotheses of Lemma R2 and prop:Hk(1)')
    stq, stm = steps()
    check(stq.maxh == 22 and stq.maxv == 24,
          f'Q*: max|(2F0* E)_c| = {stq.maxh}, max|(D1 E)_c| = {stq.maxv} over E in {{-2..2}}^5 '
          f'(R2 for p >= 29, prop:Hk(1) for p >= 23)')
    check(stm.maxh == 26, f'M5: max|(2M5 E)_c| = {stm.maxh} (prop:Hk(1) for p > 26, i.e. p >= 29), '
                          f'max|(D1 E)_c| = {stm.maxv}')


def part_d():
    print('(d) drift and jitter')
    K = dr(HQ)
    check(K == Fr(17, 2), f'dr(F0*) = {K}')
    J = dj(HQ, D1Q)
    check(J == Fr(17, 2), f'dj(F0*, D1) = {J}')
    att = sorted({canon_sign(E) for E in BIND if Fr(drift2(HQ, E), 2) == K}, reverse=True)
    check(set(att) == {(0, 1, 1, 1, 0), (1, 0, -1, -1, 0), (1, 1, 0, 0, -1)},
          f'binding steps with dr = 17/2 (up to sign): {att}')
    att2 = {canon_sign(E): (Fr(drift2(HQ, E), 2), n_harmful(HQ, D1Q, E)) for E in BIND
            if Fr(drift2(HQ, E), 2) + n_harmful(HQ, D1Q, E) == J}
    tie = sorted(E for E in att2 if E not in att)
    check(all(att2.get(E) == (K, 0) for E in att) and len(tie) == 3
          and all(att2[E] == (Fr(13, 2), 2) for E in tie),
          f'dj = 17/2 is attained on the 3 drift-17/2 steps (0 harmful coordinates) and ties on the 3 drift-13/2 '
          f'steps {tie} (2 harmful each)')
    KM, JM = dr(HM), dj(HM, D1M)
    check(KM == Fr(35, 2) and JM == Fr(39, 2), f'M5: dr = {KM}, dj(M5, its D1) = {JM}')


def part_e():
    print('(e) condition (Lambda) and lambda')
    for name, H in (('F0*', HQ), ('M5', HM)):
        L = {E: lead_len2(H, E) for E in ALLE}
        bindset = set(BIND)
        nb = min(v for E, v in L.items() if E not in bindset)
        lam = min(L.values())
        at = [E for E, v in L.items() if v == lam]
        check(nb == 2, f'{name}: min leading length^2 over the {len(ALLE) - len(BIND)} non-binding steps = {nb}')
        check(lam == Fr(5, 4) and set(at) == bindset,
              f'{name}: lambda^2 = {lam}, attained at {len(at)} steps = exactly the 122 binding steps')


def part_f():
    print('(f) exact scans and monotone tails')
    stq, stm = steps()
    t0 = time.time()
    # --- Lemma R2 for Q*, primes 29 <= p < 200 ---
    r2 = {p: lb_r2_sq(stq, p) for p in primes_in(29, 200)}
    for p in (29, 31, 37):
        sq, E = r2[p]
        print(f'        LB_R2({p}) = {trunc(sq, p ** 4)}...  argmin E = +-{canon_sign(E)}')
    # truncations (the notes' .982971, .991900 are these values ROUNDED to 6 digits)
    want = {29: '0.9829706', 31: '0.9918996', 37: '1.0127911'}
    check(all(trunc(r2[p][0], p ** 4, 7) == w for p, w in want.items()),
          'LB_R2(29) = 0.982970..., LB_R2(31) = 0.991899..., LB_R2(37) = 1.012791... (truncated; rounded: '
          '.982971, .991900, 1.012791 as in the notes)')
    check(r2[29][0] < 29 ** 4 and r2[31][0] < 31 ** 4, 'LB_R2(29), LB_R2(31) < 1')
    above = [p for p in r2 if p >= 37]
    check(all(r2[p][0] > p ** 4 for p in above), f'LB_R2(p) > 1 at all {len(above)} primes 37 <= p < 200')
    pmin = min(above, key=lambda p: Fr(r2[p][0], p ** 4))
    check(pmin == 37, f'minimum of LB_R2 over primes 37 <= p < 200 is at p = {pmin}')
    check(all(canon_sign(r2[p][1]) == (1, 1, 0, 0, -1) for p in r2), 'argmin step +-(1,1,0,0,-1) at every p scanned')
    # hypothesis-free (residues reduced mod p) agrees with R2 where the hypotheses hold
    check(all(lb_r2_sq(stq, p, free=True)[0] == r2[p][0] for p in (29, 31, 37, 101, 199)),
          'residue-reduced (hypothesis-free) variant equals LB_R2 at p = 29, 31, 37, 101, 199')
    T = tail_r2_sq(stq, 200)
    check(T > 1 and trunc_fr(T) == '1.187720', f'R2 tail: L*(200)^2 = {trunc_fr(T)}... > 1 (exact Fraction)')
    # rev 15.7 pass 3 (Lean S11 review item 2): the monotone tails already exceed 1 from p = 50 (R2) and p = 63 (Hk)
    check(tail_r2_sq(stq, 50) > 1 and tail_r2_sq(stq, 49) < 1, 'R2 tail: L*(50)^2 > 1 > L*(49)^2 (printed: from p = 50)')
    print(f'        [R2 scan + tail: {time.time() - t0:.1f} s]')
    # --- prop:Hk(1) for F0*, primes 23 <= p < 400 ---
    t0 = time.time()
    hk = {p: lb_hk_sq(stq, p) for p in primes_in(23, 400)}
    for p in (47, 53):
        print(f'        LB_Hk({p}) = {trunc(hk[p][0], p ** 2)}...  argmin E = +-{canon_sign(hk[p][1])}')
    check(trunc(hk[47][0], 47 ** 2, 7) == '0.9906763' and trunc(hk[53][0], 53 ** 2, 7) == '1.0049716',
          'F0*: LB_Hk(47) = 0.990676..., LB_Hk(53) = 1.004971... (truncated; rounded: 1.004972 as in the audit)')
    check(all(hk[p][0] > p * p for p in hk if p >= 53) and hk[47][0] < 47 ** 2,
          f'F0*: LB_Hk(p) > 1 at every prime 53 <= p < 400 ({sum(1 for p in hk if p >= 53)} primes), < 1 at 47')
    T = tail_hk_sq(stq, 200)
    check(T > 1 and trunc_fr(T) == '1.168931', f'F0* Hk tail: L*(200)^2 = {trunc_fr(T)}... > 1 (exact Fraction)')
    check(tail_hk_sq(stq, 63) > 1 and tail_hk_sq(stq, 62) < 1, 'F0* Hk tail: L*(63)^2 > 1 > L*(62)^2 (printed: from p = 63)')
    print(f'        [Hk scan + tail: {time.time() - t0:.1f} s]')
    # --- M5: LB_Hk vs prop:half5's coarse LB' ---
    t0 = time.time()
    res = {}
    for p in (83, 89):
        a, b = lb_hk_sq(stm, p)[0], lb_hk_sq(stm, p, coarse=True)[0]
        res[p] = (trunc(a, p * p), trunc(b, p * p))
        print(f"        M5: LB_Hk({p}) = {res[p][0]}...   LB'({p}) = {res[p][1]}...")
    check(res[83][0][:6] == '0.9975' and res[89][0][:6] == '1.0056',
          'M5: LB_Hk(83) = .9975..., LB_Hk(89) = 1.0056... (prop:half5)')
    check(res[83][1][:6] == '0.9975' and res[89][1][:6] == '1.0056',
          "M5: the coarse LB'(83), LB'(89) also give .9975..., 1.0056... (prop:half5's proof uses LB')")
    ok = all(lb_hk_sq(stm, p, coarse=True)[0] > p * p for p in primes_in(89, 269))
    check(ok, "M5: LB'(p) > 1 at every prime 89 <= p < 269 (prop:half5's scan range)")
    eqM = all(lb_hk_sq(stm, p)[0] == lb_hk_sq(stm, p, coarse=True)[0] for p in primes_in(29, 400))
    check(eqM, "M5: LB'(p) = LB_Hk(p) exactly at every prime 29 <= p < 400 (so both definitions reproduce prop:half5)")
    cmpQ = [(lb_hk_sq(stq, p, coarse=True)[0], hk[p][0]) for p in hk]
    check(all(a <= b for a, b in cmpQ), f"F0*: LB' <= LB_Hk at every prime 23 <= p < 400 (strictly smaller at "
                                         f"{sum(a < b for a, b in cmpQ)} of {len(cmpQ)}); the paper's F0* values use LB_Hk")
    print(f'        [M5 scans: {time.time() - t0:.1f} s]')


def part_g():
    print('(g) drift accounting: M5 vs F0*')
    alpha = [Fr(-HM[c][c], 2) for c in range(S)]
    check(alpha == [Fr(5, 2), Fr(3, 2), Fr(5, 2), Fr(7, 2), Fr(3, 2)] and sum(alpha) == Fr(23, 2),
          f'alpha(M5) = ({", ".join(map(str, alpha))}), sum = {sum(alpha)}')
    m = [Fr(max(abs(HM[c][d]) for d in range(S) if d != c), 2) for c in range(S)]
    check(sum(m) == Fr(15, 2), f'sum_c max_(d != c) |M5[c][d]| = {sum(m)}')
    q = {(c, d): -(HM[c][d] + HM[d][c]) // 2 for c in range(S) for d in range(c + 1, S)}
    assert all((HM[c][d] + HM[d][c]) % 2 == 0 for c, d in q)
    f = {E: sum(q[c, d] * E[c] * E[d] for c, d in q) for E in FULL}
    check(max(f.values()) == 6, f'symmetric-part imbalance max_E f(E) over full steps = {max(f.values())}')
    check(all(Fr(drift2(HM, E), 2) == sum(alpha) + f[E] for E in FULL), 'dr(E) = sum alpha + f(E) on every full step')
    K = dr(HM)
    att = [E for E in BIND if Fr(drift2(HM, E), 2) == K]
    check(K == Fr(35, 2) and all(all(E) for E in att), f'dr(M5) = {K}, attained only on full steps ({len(att)} with sign)')
    Hmin = [[HM[c][d] if c != d else -int(2 * m[c]) for d in range(S)] for c in range(S)]
    Km = dr(Hmin)
    check(Km == Fr(27, 2), f'dr with the diagonal lowered to m_c = max_(d != c)|M5[c][d]|: {Km}')
    check(K == Fr(13, 2) + 1 + (sum(alpha) - sum(m)) + 6, '35/2 = 13/2 + 1 + 4 + 6 (accounting identity)')
    fq = {Fr(drift2(HQ, E), 2) for E in FULL}
    check(fq == {Fr(13, 2)}, f'F0*: every full step has dr = {", ".join(map(str, fq))} = sum alpha (skew)')


def main():
    t0 = time.time()
    for part in (part_a, part_b, part_c, part_d, part_e, part_f, part_g):
        t = time.time()
        part()
        print(f'        [{part.__name__}: {time.time() - t:.1f} s]')
    print(f'total {time.time() - t0:.1f} s')
    if FAILS:
        print(f'half5_qstar: {len(FAILS)} FAILURE(S):')
        for m in FAILS:
            print('   ', m)
        sys.exit(1)
    print('half5_qstar: ALL OK')
    sys.exit(0)


if __name__ == '__main__':
    main()

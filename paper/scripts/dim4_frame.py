"""dim4_frame -- DIM4 probe: exact (over Q) graph form of 4-place rational frames, written fresh
(independent of sg_lib) to cross-check SGEN_NOTES s=4 claims and to answer the coordinator's frame (a).

Frame: V in Q[t]_{<m}, m = 4k. Coordinate c reads V at place a_c: digit j = coeff of (t-a_c)^j
(a_c finite) or coeff of t^{m-1-j} (a_c = inf). Graph form: cells n_c = first k digits of c;
offset of c = sum_d Phi_cd n_d. Row 0 of Phi_cd (the first offset digit) restricted to levels
k-1, k-2, k-3 is the 'geometric layer' (levels k-1 = M~, k-2 = 'h', k-3 = new in s=4).

usage: uv run python dim4_frame.py            (all checks, prints report)
"""
from fractions import Fraction as Fr
from itertools import product, combinations, permutations
from math import comb
import sys

INF = 'inf'


def gen_mats(places, m):
    Cs = []
    for a in places:
        if a == INF:
            C = [[Fr(1 if i == m - 1 - j else 0) for i in range(m)] for j in range(m)]
        else:
            a = Fr(a)
            C = [[Fr(comb(i, j)) * a ** (i - j) if i >= j else Fr(0) for i in range(m)] for j in range(m)]
        Cs.append(C)
    return Cs


def inv_q(A):
    n = len(A)
    M = [list(A[i]) + [Fr(int(i == j)) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        iv = 1 / M[col][col]
        M[col] = [x * iv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return [row[n:] for row in M]


def det_q(A):
    n = len(A)
    M = [list(r) for r in A]
    d = Fr(1)
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            d = -d
        d *= M[col][col]
        for r in range(col + 1, n):
            if M[r][col] != 0:
                f = M[r][col] / M[col][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return d


def matmul(A, B):
    return [[sum(A[i][l] * B[l][j] for l in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def graph_form(Cs, k):
    s = len(Cs)
    m = s * k
    G = [Cs[c][j] for c in range(s) for j in range(k)]
    Gi = inv_q(G)
    return [matmul([Cs[c][j] for j in range(k, m)], Gi) for c in range(s)], det_q(G)


def blk(Phi, c, d, k):
    return [row[d * k:(d + 1) * k] for row in Phi[c]]


def primes_of(x):
    x = abs(int(x))
    out, f = set(), 2
    while x > 1 and f * f <= x:
        while x % f == 0:
            out.add(f)
            x //= f
        f += 1
    if x > 1:
        out.add(x)
    return out


def frac_primes(fr):
    fr = Fr(fr)
    return primes_of(fr.numerator) | primes_of(fr.denominator) if fr != 0 else set()


def pf4(S):
    return S[0][1] * S[2][3] - S[0][2] * S[1][3] + S[0][3] * S[1][2]


def rpf4(S):
    """reciprocal Pfaffian Pf(1/S_cd): vanishes for every Lambda C Lambda, C Cauchy (Pf[(a_c-a_d)] = 0)."""
    return 1 / (S[0][1] * S[2][3]) - 1 / (S[0][2] * S[1][3]) + 1 / (S[0][3] * S[1][2])


def skewify(M):
    """column scaling y with M_cd y_d skew (exists iff all 3-cycle ratios are -1)."""
    s = len(M)
    y = [Fr(1)] + [None] * (s - 1)
    for d in range(1, s):
        # M_0d y_d = - M_d0 y_0
        y[d] = -M[d][0] * y[0] / M[0][d]
    S = [[M[c][d] * y[d] if c != d else Fr(0) for d in range(s)] for c in range(s)]
    ok = all(S[c][d] == -S[d][c] for c in range(s) for d in range(s) if c != d)
    return S, y, ok


def cycle_ratios(M):
    out = {}
    for a, b, c in combinations(range(len(M)), 3):
        out[(a, b, c)] = (M[a][b] * M[b][c] * M[c][a]) / (M[b][a] * M[c][b] * M[a][c])
    return out


def diag_equiv(M, S):
    """find lam, mu (rationals) with S_cd = lam_c M_cd mu_d for all c != d; None if impossible."""
    s = len(M)
    lam = [Fr(1)] + [None] * (s - 1)
    mu = [None] * s
    for d in range(1, s):
        mu[d] = S[0][d] / M[0][d]
    for c in range(1, s):
        d = 1 if c != 1 else 2
        lam[c] = S[c][d] / (M[c][d] * mu[d])
    mu[0] = S[1][0] / (lam[1] * M[1][0])
    for c in range(s):
        for d in range(s):
            if c != d and lam[c] * M[c][d] * mu[d] != S[c][d]:
                return None
    return lam, mu


def z2_normalizable(lam, mu):
    """can a common t make all lam_c*t and mu_d/t into +-2^j ?  (odd parts all equal / inverse)"""
    def oddpart(x):
        x = Fr(x)
        n, d = abs(x.numerator), x.denominator
        while n % 2 == 0:
            n //= 2
        while d % 2 == 0:
            d //= 2
        return Fr(n, d)
    ol = {oddpart(x) for x in lam}
    om = {oddpart(x) for x in mu}
    if len(ol) != 1 or len(om) != 1:
        return False
    return list(ol)[0] * list(om)[0] == 1


def main():
    out = []
    P = lambda *a: out.append(' '.join(str(x) for x in a))
    # ---------- frame (a): orbit order of t -> (t-1)/(t+1): 0 -> -1 -> inf -> 1 -> 0
    places = [0, -1, INF, 1]
    P('== Frame (a): places in orbit order', places)
    for k in (2, 3, 4):
        m = 4 * k
        Phi, d0 = graph_form(gen_mats(places, m), k)
        Mt = [[blk(Phi, c, d, k)[0][k - 1] if c != d else Fr(0) for d in range(4)] for c in range(4)]
        P('k=%d  det(k,k,k,k box)=%s primes %s' % (k, d0, sorted(frac_primes(d0))))
        P('  M~ (level k-1, row 0):', [[str(x) for x in r] for r in Mt])
        cr = cycle_ratios(Mt)
        P('  3-cycle ratios:', {kk: str(v) for kk, v in cr.items()})
        S, y, ok = skewify(Mt)
        P('  skew-symmetrisable by column scaling:', ok, ' reciprocal Pf(skewified) =', rpf4(S))
        # Cauchy test: X_cd = M~_cd * D_cd should be rank-one (lam_c mu_d) off-diagonal,
        # D_cd = homogeneous det [u_c v_d - u_d v_c], place a=(a:1), inf=(1:0)
        hom = [(Fr(1), Fr(0)) if a == INF else (Fr(a), Fr(1)) for a in places]
        X = [[Mt[c][d] * (hom[c][0] * hom[d][1] - hom[d][0] * hom[c][1]) if c != d else None for d in range(4)] for c in range(4)]
        rk1 = all(X[c][d] * X[e][f] == X[c][f] * X[e][d] for c, d, e, f in product(range(4), repeat=4)
                  if len({c, d}) == 2 and len({e, f}) == 2 and c != f and e != d)
        P('  M~_cd = lam_c mu_d / (a_c - a_d)  [Cauchy, homogeneous]:', rk1)
        # corner W_d: rows c != d, levels k-1, k-2, k-3: rank 3 needed (box (k+1,k+1,k+1,k-3))
        if k >= 3:
            for d in range(4):
                W = [[blk(Phi, c, d, k)[0][k - 1 - l] for l in range(3)] for c in range(4) if c != d]
                dW = det_q(W)
                P('  corner W_%d det = %s (primes %s)' % (d, dW, sorted(frac_primes(dW))))
        # row 0 support: which levels are nonzero (before gauge)
        if k == 4:
            P('  row-0 of Phi_01 all levels:', [str(x) for x in blk(Phi, 0, 1, k)[0]])
    # ---------- negacyclic structure and the sqrt2 obstruction
    P('')
    P('== Negacyclic skew layers N = s1 (P + P^3) + s2 P^2  (P = negacyclic shift, P^4 = -I)')
    s1, s2 = Fr(1), None
    for s2v in (1, 2, -1, -2):
        Pm = [[Fr(0)] * 4 for _ in range(4)]
        for c in range(4):
            for j, sj in ((1, Fr(1)), (2, Fr(s2v)), (3, Fr(1))):
                d = (c + j) % 4
                Pm[c][d] = sj if c + j < 4 else -sj
        sk = all(Pm[c][d] == -Pm[d][c] for c in range(4) for d in range(4) if c != d)
        P('  s1=1 s2=%d skew=%s reciprocal Pf=%s  (= 2/s1^2 - 1/s2^2, zero iff s1 = +-sqrt2 s2)' % (s2v, sk, rpf4(Pm)))
    # ---------- enumerate small skew S reachable from frame (a) over Q / over Z[1/2]
    P('')
    P('== Small skew S (entries in {+-1,+-2}) diagonally equivalent to frame (a) M~ (k=2), any coordinate order')
    k = 2
    Phi, _ = graph_form(gen_mats(places, 4 * k), k)
    Mt = [[blk(Phi, c, d, k)[0][k - 1] if c != d else Fr(0) for d in range(4)] for c in range(4)]
    vals = (1, -1, 2, -2)
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    found_q, found_z2 = [], []
    for v in product(vals, repeat=6):
        S = [[Fr(0)] * 4 for _ in range(4)]
        for (a, b), x in zip(pairs, v):
            S[a][b], S[b][a] = Fr(x), Fr(-x)
        r = diag_equiv(Mt, S)
        if r is None:
            continue
        found_q.append(v)
        if z2_normalizable(*r):
            found_z2.append(v)
    P('  #skew S over Q: %d ; of which reachable with lam,mu in +-2^Z (valid all odd q): %d' % (len(found_q), len(found_z2)))
    n1 = [v for v in found_q if all(abs(x) == 1 for x in v)]
    P('  with all entries +-1: %d' % len(n1))
    from collections import Counter
    P('  #entries of size 2 among reachable:', dict(Counter(sum(abs(x) == 2 for x in v) for v in found_q)))
    if found_z2:
        P('  example Z[1/2]-reachable skew S (pairs 01,02,03,12,13,23):', found_z2[:4])
    print('\n'.join(out))


if __name__ == '__main__':
    main()

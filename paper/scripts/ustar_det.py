"""Deterministic Theorem A design U*_s (Definition def:Ustar of core.tex).  Copy of the repository's
as_push/ustar_det.py, changed only so that it writes its JSON when asked (--out FILE); used by as_table.py.

Places [inf,0..n], n = s-2, row gauge lambda' = 1, S = primes <= n.
Per column d (frame order inf,0..n) with rows c != d in frame order, weights rho_c and nodes y_c (prop:Ns):
  for j = 0..n:
    Lam_j = V_j ∩ Z^N  (N = s-1), computed as its row-HNF basis (canonical; any basis gives the same E_j);
    kappa_j = Lagrange leading coefficient on the first j+1 rows (exact on V_j);
    gamma_j = positive generator of kappa_j(Lam_j) (gcd of kappa_j on the HNF rows);
    v = any vector of Lam_j with kappa_j(v) = +gamma_j (here: sequential extended Euclid on the HNF rows);
    c = Gram solve of the orthogonal projection of v on span(E_0..E_{j-1}) in the basis E_i;
    E_j = v - sum_i floor(c_i + 1/2) E_i.
  E_j does NOT depend on the choice of v (two choices differ by an integer combination of E_0..E_{j-1} =
  basis of Lam_{j-1}, and floor(x+1/2) commutes with integer shifts), nor on the basis of Lam_j.
Design: M^{(j)}[c][d] = E_j[c]; alpha_c = sum_{d!=c} max_j |M^{(j)}[c][d]|; F_0[c][c] = -alpha_c, deeper diagonal 0.
Checks: prop:F (deg g = j exactly, S-unit leading coefficient, S-integral coefficients) by exact
interpolation over all N nodes; dominance; Theorem A bound ||E_j|| <= (3/2)^j H_s.
Run: uv run --with python-flint python scripts/ustar_det.py 10 [--out FILE.json]   (~1 s for s <= 10)
"""
import sys, os, json, time
from fractions import Fraction as Fr
from math import gcd, lcm, factorial, sqrt, floor
import flint

def primes_upto(n): return [p for p in range(2, n + 1) if all(p % r for r in range(2, p))]

def is_Sunit(x, S):
    x = Fr(x)
    if x == 0: return False
    for v in (abs(x.numerator), x.denominator):
        for p in S:
            while v % p == 0: v //= p
        if v != 1: return False
    return True

def column_data(n, d):
    if d == 'inf':
        return [Fr(1)] * (n + 1), [Fr(c) for c in range(n + 1)]
    rho, ys = [Fr(1)], [Fr(0)]          # row inf
    for c in range(n + 1):
        if c != d: rho.append(Fr(1, c - d)); ys.append(Fr(1, c - d))
    return rho, ys

def kappa(rho, ys, x, j):
    tot = Fr(0)
    for b in range(j + 1):
        tau = rho[b]
        for b2 in range(j + 1):
            if b2 != b: tau *= ys[b] - ys[b2]
        tot += Fr(x[b]) / tau
    return tot

def saturated_hnf(rows_V, N):
    """row-HNF basis of (Q-span of rows_V) ∩ Z^N."""
    k = len(rows_V)
    L = 1
    for r in rows_V:
        for a in r: L = lcm(L, a.denominator)
    A = flint.fmpz_mat([[int(a * L) for a in r] for r in rows_V])   # k x N, rank k
    if k == N:
        return [[int(i == c) for c in range(N)] for i in range(N)]
    ns, rk = A.nullspace()                       # N x N, first rk columns span ker A = V^perp (rational)
    P = [[int(ns[r, c]) for r in range(N)] for c in range(rk)]   # rows: integer basis of V^perp (Q-span)
    # Lam = {x in Z^N : P x = 0}; HNF of [P^T | I] isolates the integer kernel
    r = len(P)
    Mx = flint.fmpz_mat([[P[a][i] for a in range(r)] + [int(i == b) for b in range(N)] for i in range(N)])
    H = Mx.hnf()
    K = [[int(H[i, r + b]) for b in range(N)] for i in range(N) if all(H[i, a] == 0 for a in range(r))]
    assert len(K) == k
    Hk = flint.fmpz_mat(K).hnf()                 # canonical row-HNF of Lam
    return [[int(Hk[i, c]) for c in range(N)] for i in range(k)]

def ext_gcd_comb(vals):
    """x with sum x_i vals_i = g = gcd(vals) >= 0 (standard Euclid, sequential in index order)."""
    g, co = 0, []
    for i, v in enumerate(vals):
        a, b = g, v; x0, y0, x1, y1 = 1, 0, 0, 1
        while b != 0:
            q = a // b; a, b = b, a - q * b; x0, x1 = x1, x0 - q * x1; y0, y1 = y1, y0 - q * y1
        co = [c * x0 for c in co] + [y0]; g = a
    if g < 0: g, co = -g, [-c for c in co]
    return g, co

def solve_exact(G, b):
    n = len(G); M = [G[i][:] + [b[i]] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[p] = M[p], M[c]
        pv = M[c][c]; M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [a - f * bb for a, bb in zip(M[r], M[c])]
    return [M[i][n] for i in range(n)]

def construct(s):
    n = s - 2; N = s - 1
    cols = ['inf'] + list(range(n + 1))
    E = {}; ties = 0; ratio = 0.0
    Hs = 2 * sqrt(N) * factorial(n) * lcm(*range(1, n + 1))
    for di, d in enumerate(cols):
        rho, ys = column_data(n, d)
        V = [[rho[c] * ys[c] ** i for c in range(N)] for i in range(n + 1)]
        Es = []
        for j in range(n + 1):
            B = saturated_hnf(V[:j + 1], N)
            ks = [kappa(rho, ys, b, j) for b in B]
            D = 1
            for k in ks: D = lcm(D, k.denominator)
            g, co = ext_gcd_comb([int(k * D) for k in ks])
            v = [sum(co[t] * B[t][c] for t in range(len(B))) for c in range(N)]
            gam = Fr(g, D); assert gam > 0 and kappa(rho, ys, v, j) == gam
            if Es:
                G = [[sum(Fr(a) * b for a, b in zip(Ei, Ek)) for Ek in Es] for Ei in Es]
                rhs = [sum(Fr(a) * b for a, b in zip(Ei, v)) for Ei in Es]
                cv = solve_exact(G, rhs)
                ties += sum(1 for c in cv if (c - Fr(1, 2)).denominator == 1)
                rnd = [floor(c + Fr(1, 2)) for c in cv]
                v = [v[c] - sum(rnd[t] * Es[t][c] for t in range(len(Es))) for c in range(N)]
            assert kappa(rho, ys, v, j) == gam
            ratio = max(ratio, sqrt(sum(x * x for x in v)) / (1.5 ** j * Hs))
            Es.append(v); E[(di, j)] = v
    L = n + 1
    Mp = [[[0] * s for _ in range(s)] for _ in range(L)]
    for di in range(s):
        rows = [c for c in range(s) if c != di]
        for j in range(L):
            for t, c in enumerate(rows): Mp[j][c][di] = E[(di, j)][t]
    F = [[[Mp[j][c][d] - (Mp[j - 1][c][d] if j else 0) for d in range(s)] for c in range(s)] for j in range(L)]
    alpha = [sum(max(abs(Mp[j][c][d]) for j in range(L)) for d in range(s) if d != c) for c in range(s)]
    for c in range(s): F[0][c][c] = -alpha[c]
    return F, Mp, alpha, ties, ratio

def interp(xs, vals):
    """coefficients (low->high) of the unique poly of degree < len(xs) through (xs, vals)."""
    n = len(xs); A = [[x ** i for i in range(n)] + [v] for x, v in zip(xs, vals)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0); A[c], A[p] = A[p], A[c]
        pv = A[c][c]; A[c] = [a / pv for a in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]; A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [A[i][n] for i in range(n)]

def check(s, F, Mp, alpha):
    n = s - 2; S = primes_upto(n); L = n + 1
    for di, d in enumerate(['inf'] + list(range(n + 1))):
        rho, ys = column_data(n, d)
        rows = [c for c in range(s) if c != di]
        for j in range(L):
            vals = [Fr(Mp[j][c][di]) / rho[t] for t, c in enumerate(rows)]
            g = interp(ys, vals)
            assert all(x == 0 for x in g[j + 1:]), ('deg', s, d, j)
            assert is_Sunit(g[j], S), ('lead', s, d, j, g[j])
            for a in g:
                den = a.denominator
                for p in S:
                    while den % p == 0: den //= p
                assert den == 1, ('Sint', s, d, j, a)
    for c in range(s):   # dominance
        assert alpha[c] >= sum(max(abs(Mp[j][c][d]) for j in range(L)) for d in range(s) if d != c)
        assert all(F[j][c][c] == 0 for j in range(1, L))
    return True

if __name__ == '__main__':
    smax = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1] != '--out' else 10
    out = {}
    for s in range(3, smax + 1):
        t = time.time()
        F, Mp, alpha, ties, ratio = construct(s)
        ok = check(s, F, Mp, alpha)
        mx = max(abs(Mp[j][c][d]) for j in range(s - 1) for c in range(s) for d in range(s) if c != d)
        out[str(s)] = {'places': ['inf'] + [str(c) for c in range(s - 1)], 'lam': ['1'] * s, 'F': F,
                       'alpha': alpha, 'a': max(alpha), 'max_entry': mx}
        print(f"s={s} a={max(alpha)} max_entry={mx} ties={ties} max||E_j||/((3/2)^j H_s)={ratio:.3g} "
              f"propF+dominance={ok} {time.time()-t:.2f}s", flush=True)
    if '--out' in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index('--out') + 1], 'w'))

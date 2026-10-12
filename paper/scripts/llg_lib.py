"""llg_lib -- the research notes: the split (two-point) frame and half-integer layers at k >= 2.

Self-contained (imports nothing from sg_*, sgg_*, dim*_*), exact arithmetic (Fractions / ints).

SPLIT FRAME.  2s distinct points of P^1(Q): cell points v_0..v_{s-1}, offset points u_0..u_{s-1}.
V in Q[t]_{<m}, m = s k.  Coordinate c has digits
    digit j (j < k)      = coefficient of (t - v_c)^j in V            (the CELL of c)
    digit k + j (j < m-k) = coefficient of (t - u_c)^j in V            (the OFFSET of c)
(INF: digit j = v_{m-1-j}).  Every box minor is a confluent Vandermonde in the 2s points
(zeros of total order m at distinct points), i.e. +- a product of point differences.

Graph form: cells n_c in Q^k (index = cells), offset rows of c = Phi_c . n, Phi_cd: (m-k) x k,
column j <-> level j of n_d (level k-1 = last cell digit).  x-index n <-> level k-1-n.
"""
from fractions import Fraction as Fr
from math import comb, gcd
from itertools import combinations, product

INF = None


def reading_rows(a, m, nrows):
    if a is INF:
        return [[Fr(1 if i == m - 1 - j else 0) for i in range(m)] for j in range(nrows)]
    a = Fr(a)
    return [[Fr(comb(i, j)) * a ** (i - j) if i >= j else Fr(0) for i in range(m)] for j in range(nrows)]


def split_generators(u, v, k):
    s = len(u)
    m = s * k
    return [reading_rows(v[c], m, k) + reading_rows(u[c], m, m - k) for c in range(s)]


def solve_right(G, O):
    """O * G^{-1}, exact."""
    n = len(G)
    A = [[G[j][i] for j in range(n)] + [O[r][i] for r in range(len(O))] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        iv = 1 / A[col][col]
        A[col] = [x * iv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[col])]
    XT = [row[n:] for row in A]
    return [[XT[i][r] for i in range(n)] for r in range(len(O))]


def split_graph_form(u, v, k):
    s = len(u)
    m = s * k
    C = split_generators(u, v, k)
    G = [C[c][j] for c in range(s) for j in range(k)]
    Phi = {}
    for c in range(s):
        X = solve_right(G, C[c][k:])
        for d in range(s):
            Phi[c, d] = [row[d * k:(d + 1) * k] for row in X]
    return Phi


# ---------- series helpers (x-index) ----------
def smul(a, b, n):
    out = [Fr(0)] * n
    for i, x in enumerate(a[:n]):
        if x:
            for j, y in enumerate(b[:n - i]):
                out[i + j] += x * y
    return out


def sinv(a, n):
    out = [Fr(0)] * n
    out[0] = 1 / a[0]
    for i in range(1, n):
        acc = sum(a[j] * out[i - j] for j in range(1, min(i, len(a) - 1) + 1))
        out[i] = -acc / a[0]
    return out


def predicted_row0(u, v, c, d, k):
    """Normal-form prediction (finite points): P_c^k / (Pi_d(v_d+x) (u_c - v_d - x)) mod x^k,
    P_c = prod_{d'} (u_c - v_d'), Pi_d(t) = prod_{d' != d} (t - v_d')^k."""
    n = k
    Pd = [Fr(1)] + [Fr(0)] * (n - 1)
    for dd in range(len(v)):
        if dd == d:
            continue
        lin = [Fr(v[d]) - Fr(v[dd]), Fr(1)]
        for _ in range(k):
            Pd = smul(Pd, lin, n)
    P = Fr(1)
    for dd in range(len(v)):
        P *= Fr(u[c]) - Fr(v[dd])
    e = Fr(u[c]) - Fr(v[d])
    geo = [1 / e ** (i + 1) for i in range(n)]
    return [P ** k * t for t in smul(sinv(Pd, n), geo, n)]


def row_gf(row, k):
    return [row[k - 1 - n] for n in range(k)]


# ---------- exact linear solve ----------
def solve_exact(A, b):
    """least-structure exact solve of A x = b (A: r x n). Returns (x, consistent). Free vars = 0."""
    r, n = len(A), len(A[0])
    M = [list(map(Fr, A[i])) + [Fr(b[i])] for i in range(r)]
    piv_cols, row = [], 0
    for col in range(n):
        p = next((i for i in range(row, r) if M[i][col] != 0), None)
        if p is None:
            continue
        M[row], M[p] = M[p], M[row]
        iv = 1 / M[row][col]
        M[row] = [x * iv for x in M[row]]
        for i in range(r):
            if i != row and M[i][col] != 0:
                f = M[i][col]
                M[i] = [x - f * y for x, y in zip(M[i], M[row])]
        piv_cols.append(col)
        row += 1
        if row == r:
            break
    consistent = all(M[i][n] == 0 for i in range(row, r))
    x = [Fr(0)] * n
    for i, col in enumerate(piv_cols):
        x[col] = M[i][n]
    return x, consistent


# ---------- gauge: make row 0 equal a design ----------
def gauge_to_design(Phi, s, k, T):
    """T[n][c][d] (n < min(s-1,k)) rational design incl. diagonal (diagonal ignored here).
    Find lambda_c and lower-triangular (in levels) U_d with row0(lambda_c Phi_cd U_d) = T_cd on
    x-indices < min(s-1,k) and 0 on x-indices s-1..k-1.  Returns (lam, U, ok, msg)."""
    rho = {(c, d): Phi[c, d][0] for c in range(s) for d in range(s) if c != d}
    X = {(c, d): Fr(T[0][c][d]) / rho[c, d][k - 1] for (c, d) in rho}
    lam = [None] * s
    u00 = [None] * s
    lam[0] = Fr(1)
    for d in range(1, s):
        u00[d] = X[0, d]
    for c in range(1, s):
        dstar = next(d for d in range(1, s) if d != c)
        lam[c] = X[c, dstar] / u00[dstar]
    u00[0] = X[1, 0] / lam[1]
    for (c, d) in X:
        if lam[c] * u00[d] != X[c, d]:
            return None, None, False, "level-0 layer not rank-one (not reachable)"
    U = {}
    nd = min(s - 1, k)
    for d in range(s):
        rows = [c for c in range(s) if c != d]
        Ud = [[Fr(0)] * k for _ in range(k)]
        Ud[k - 1][k - 1] = u00[d]
        for n in range(1, k):
            lp = k - 1 - n                     # target level
            if n < nd:
                unk = list(range(lp, k))       # U[l][lp], l = lp..k-1
                A = [[lam[c] * rho[c, d][l] for l in unk] for c in rows]
                b = [Fr(T[n][c][d]) for c in rows]
                x, ok = solve_exact(A, b)
                if not ok:
                    return None, None, False, f"column {d} x-index {n}: design not reachable"
                for l, val in zip(unk, x):
                    Ud[l][lp] = val
                if Ud[lp][lp] == 0:
                    return None, None, False, f"column {d} x-index {n}: zero diagonal (leading coeff not unit)"
            else:
                Ud[lp][lp] = Fr(1)
                unk = list(range(k - 1, k - 1 - (s - 1), -1))   # top s-1 levels
                A = [[rho[c, d][l] for l in unk] for c in rows]
                b = [-rho[c, d][lp] for c in rows]
                x, ok = solve_exact(A, b)
                if not ok:
                    return None, None, False, f"column {d} x-index {n}: cannot zero"
                for l, val in zip(unk, x):
                    Ud[l][lp] = val
        U[d] = Ud
    return lam, U, True, "ok"


def matmul(A, B):
    return [[sum(A[i][t] * B[t][j] for t in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def build_net(Phi, s, k, T, lam, U):
    """Generator matrices (rational) of the gauged graph form with design T (diag from T)."""
    m = s * k
    nd = min(s - 1, k)
    Pp = {}
    for c in range(s):
        for d in range(s):
            if c == d:
                B = [[Fr(0)] * k for _ in range(m - k)]
                for n in range(nd):
                    B[0][k - 1 - n] = Fr(T[n][c][c])
            else:
                B = matmul(Phi[c, d], U[d])
                B[0] = [lam[c] * x for x in B[0]]
            Pp[c, d] = B
    C = []
    for c in range(s):
        rows = []
        for j in range(k):
            r = [Fr(0)] * m
            r[c * k + j] = Fr(1)
            rows.append(r)
        for i in range(m - k):
            r = []
            for d in range(s):
                r += Pp[c, d][i]
            rows.append(r)
        C.append(rows)
    return C, Pp


# ---------- boxes / t = 0 ----------
def compositions(m, s):
    for cuts in combinations(range(m + s - 1), s - 1):
        prev, parts = -1, []
        for c in cuts:
            parts.append(c - prev - 1)
            prev = c
        parts.append(m + s - 1 - prev - 1)
        yield parts


def det_mod(M, q):
    A = [[x % q for x in r] for r in M]
    n = len(A)
    det = 1
    for col in range(n):
        p = next((i for i in range(col, n) if A[i][col]), None)
        if p is None:
            return 0
        if p != col:
            A[col], A[p] = A[p], A[col]
            det = -det
        det = det * A[col][col] % q
        inv = pow(A[col][col], q - 2, q)
        for i in range(col + 1, n):
            if A[i][col]:
                f = A[i][col] * inv % q
                A[i] = [(x - f * y) % q for x, y in zip(A[i], A[col])]
    return det % q


def to_mod(C, q):
    out = []
    for M in C:
        out.append([[(x.numerator * pow(x.denominator, -1, q)) % q for x in r] for r in M])
    return out


def t0_check_mod(Cq, s, q):
    m = len(Cq[0])
    bad = 0
    nbox = 0
    for d in compositions(m, s):
        rows = []
        for c in range(s):
            rows += Cq[c][:d[c]]
        nbox += 1
        if det_mod(rows, q) == 0:
            bad += 1
    return bad, nbox


def bareiss(M):
    M = [list(r) for r in M]
    n = len(M)
    if n == 0:
        return 1
    sign, prev = 1, 1
    for i in range(n - 1):
        if M[i][i] == 0:
            sw = next((r for r in range(i + 1, n) if M[r][i] != 0), None)
            if sw is None:
                return 0
            M[i], M[sw] = M[sw], M[i]
            sign = -sign
        for r in range(i + 1, n):
            for c in range(i + 1, n):
                M[r][c] = (M[r][c] * M[i][i] - M[r][i] * M[i][c]) // prev
        prev = M[i][i]
    return sign * M[n - 1][n - 1]


def frac_det(M):
    from math import lcm
    den = 1
    for r in M:
        for x in r:
            den = lcm(den, Fr(x).denominator)
    Z = [[int(Fr(x) * den) for x in r] for r in M]
    return Fr(bareiss(Z), den ** len(M))


def primes_of(n):
    n = abs(int(n))
    out, p = set(), 2
    while p * p <= n:
        while n % p == 0:
            out.add(p)
            n //= p
        p += 1
    if n > 1:
        out.add(n)
    return out


def box_primes_exact(C, s):
    """exact rational box determinants -> set of primes dividing a numerator or denominator; zeros count."""
    m = len(C[0])
    P, zeros, nbox = set(), 0, 0
    for d in compositions(m, s):
        rows = []
        for c in range(s):
            rows += C[c][:d[c]]
        D = frac_det(rows)
        nbox += 1
        if D == 0:
            zeros += 1
        else:
            P |= primes_of(D.numerator) | primes_of(D.denominator)
    return P, zeros, nbox


# ---------- designs in normal-form coordinates (Prop F for the split frame) ----------
def design_from_params(u, v, lamp, g, diag):
    """M^{(j)}[c][d] = lamp_c * z * g[d][j](z),  z = 1/(u_c - v_d), g[d][j] = coefficient list of a
    polynomial in y=z of degree j (low -> high).  Returns partial sums Ms[j][c][d] (off-diag) and the
    design F[n] = Ms[n] - Ms[n-1] with diagonal F[0][c][c] = diag[c], deeper diagonal 0."""
    s = len(u)
    L = len(g[0])
    Ms = []
    for j in range(L):
        Mj = [[Fr(0)] * s for _ in range(s)]
        for c in range(s):
            for d in range(s):
                if c == d:
                    continue
                z = 1 / (Fr(u[c]) - Fr(v[d]))
                val = sum(Fr(co) * z ** i for i, co in enumerate(g[d][j]))
                Mj[c][d] = Fr(lamp[c]) * z * val
        Ms.append(Mj)
    F = []
    for n in range(L):
        Fn = [[(Ms[n][c][d] - (Ms[n - 1][c][d] if n else 0)) if c != d else Fr(0) for d in range(s)] for c in range(s)]
        F.append(Fn)
    for c in range(s):
        F[0][c][c] = Fr(diag[c])
    return Ms, F

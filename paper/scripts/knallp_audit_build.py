#!/usr/bin/env python3
"""KN_ALLP audit (2026-10-07): independent rebuild of the all-prime families B1/B2.

Own code (does not import x2_lib / kn2_lib):
  * Moebius frame (T^2, I, T), T[j][i] = C(m-1-i, j)(-1)^j  (tau V = (1-t)^(m-1) V(1/(1-t))),
  * graph form with depths K, the Sec.2 gauge recipe of the research notes (column ops / column
    scalings inside a block, off-diagonal block scalings, diagonal blocks set),
  * 'random completion': coarse + skeleton rows as in ChallengeKN.IsKNskel, every other row random,
  * literal transcription of ChallengeKN.{depth, off, win, winEntry, IsKNskel, skB1, skB2},
  * t=0 by rank of every box (d0+d1+d2=m).
Usage: knallp_audit_build.py MODE r p k rho [seed]   MODE in {recipe, random, randomnonnet}
Prints 'p m 3' + three m x m matrices on stdout,
diagnostics on stderr.
"""
import sys, random
from math import comb


def inv(a, p): return pow(a % p, p - 2, p)


def matmul(A, B, p):
    return [[sum(A[i][l] * B[l][j] for l in range(len(B))) % p for j in range(len(B[0]))] for i in range(len(A))]


def matinv(A, p):
    n = len(A); M = [list(r) + [int(i == j) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] % p)
        M[c], M[piv] = M[piv], M[c]
        iv = inv(M[c][c], p); M[c] = [v * iv % p for v in M[c]]
        for i in range(n):
            if i != c and M[i][c]:
                f = M[i][c]; M[i] = [(a - f * b) % p for a, b in zip(M[i], M[c])]
    return [r[n:] for r in M]


def rank(A, p):
    M = [list(r) for r in A]; rk = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c] % p), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]; iv = inv(M[rk][c], p)
        M[rk] = [v * iv % p for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] % p:
                f = M[i][c]; M[i] = [(a - f * b) % p for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk


def is_t0(C, p, m):
    bad = []
    for d0 in range(m + 1):
        for d1 in range(m + 1 - d0):
            d2 = m - d0 - d1
            rows = C[0][:d0] + C[1][:d1] + C[2][:d2]
            if rank(rows, p) < m: bad.append((d0, d1, d2))
    return bad


# ---- literal transcription of the ChallengeKN definitions ----
def depth(r, k, c): return k + 1 if c < r else k
def off(r, k, c): return 0 if c == 0 else (depth(r, k, 0) if c == 1 else depth(r, k, 0) + depth(r, k, 1))
def win(r, d): return 4 if (r == 1 and d == 0) else 3
def winEntry(row, L, K, l):
    i = K - 1 - l  # l < K always here, so no natural-number truncation
    return row[i] if (i < 4 and i < L) else 0


def skB2(rho):
    Z = [0, 0, 0, 0]
    return [[Z, Z, Z], [Z, Z, Z], [[rho, 0, 0, 0], [rho ** 2, 0, 0, 0], Z]]


def skB1(rho):
    Z = [0, 0, 0, 0]
    return [[Z, Z, Z], [[rho, 0, 0, 0], Z, [1, 0, 0, 0]], [[rho ** 2, 1, 0, 0], [1, 0, 0, 0], [-1, 0, 0, 0]]]


def is_knskel(r, p, k, sk, C):
    m = 3 * k + r
    for c in range(3):
        for j in range(depth(r, k, c)):
            for col in range(m):
                if C[c][j][col] % p != (1 if col == off(r, k, c) + j else 0): return False
    for c in range(3):
        if not r <= c: continue
        for d in range(3):
            for l in range(depth(r, k, d)):
                if C[c][depth(r, k, c)][off(r, k, d) + l] % p != winEntry(sk[c][d], win(r, d), depth(r, k, d), l) % p:
                    return False
    return True


# ---- frame and graph form ----
def frame(p, m):
    T = [[0] * m for _ in range(m)]
    for i in range(m):
        for j in range(m - i): T[j][i] = comb(m - 1 - i, j) * (-1) ** j % p
    T2 = matmul(T, T, p); I = [[int(i == j) for j in range(m)] for i in range(m)]
    return [T2, I, T]


def graph_form(C, K, p):
    Tc = [C[c][j] for c in range(3) for j in range(K[c])]
    Ti = matinv(Tc, p)
    return [matmul(C[c], Ti, p) for c in range(3)]


class GF:
    """graph-form net: G[c] = coarse unit rows then offset rows; column (d, level l) = off_d + l."""
    def __init__(s, G, K, p): s.G, s.K, s.p = G, K, p; s.o = [0, K[0], K[0] + K[1]]
    def col(s, d, l): return s.o[d] + l
    def ent(s, c, i, d, l): return s.G[c][s.K[c] + i][s.col(d, l)]   # offset row i of c, block d level l
    def col_add(s, d, j, i, lam):   # column (d,j) += lam * column (d,i), i > j  (deeper)
        assert i > j
        a, b = s.col(d, j), s.col(d, i)
        for c in range(3):
            for row in s.G[c][s.K[c]:]: row[a] = (row[a] + lam * row[b]) % s.p
    def col_scale(s, d, j, lam):
        a = s.col(d, j)
        for c in range(3):
            for row in s.G[c][s.K[c]:]: row[a] = row[a] * lam % s.p
    def blk_scale(s, c, d, lam):    # Phi_cd -> lam Phi_cd, c != d
        assert c != d
        for row in s.G[c][s.K[c]:]:
            for l in range(s.K[d]): row[s.col(d, l)] = row[s.col(d, l)] * lam % s.p
    def set_diag_zero(s):
        for c in range(3):
            for row in s.G[c][s.K[c]:]:
                for l in range(s.K[c]): row[s.col(c, l)] = 0


def recipe_B2(p, k, rho):
    m = 3 * k + 2; K = [k + 1, k + 1, k]
    g = GF(graph_form(frame(p, m), K, p), K, p)
    for d, tgt in ((0, rho), (1, rho * rho)):           # x-block target rho, y-block rho^2
        piv = g.ent(2, 0, d, k); assert piv % p, "pivot Z0|x_k or Z0|y_k zero"
        for l in range(k):
            g.col_add(d, l, k, (-g.ent(2, 0, d, l) * inv(piv, p)) % p)
        g.col_scale(d, k, tgt * inv(g.ent(2, 0, d, k), p) % p)
    g.set_diag_zero()
    return g.G, K


def recipe_B1(p, k, rho):
    m = 3 * k + 1; K = [k + 1, k, k]
    g = GF(graph_form(frame(p, m), K, p), K, p)
    Y, Z = 1, 2
    # x-block: 2x2 pivot on (x_k, x_{k-1})
    a, b = g.ent(Y, 0, 0, k), g.ent(Y, 0, 0, k - 1)
    c_, d_ = g.ent(Z, 0, 0, k), g.ent(Z, 0, 0, k - 1)
    det = (a * d_ - b * c_) % p; assert det, "2x2 pivot singular"
    for l in range(k - 1):
        # col_l += al*col_k + be*col_{k-1} with Y0,Z0 zero
        ty, tz = (-g.ent(Y, 0, 0, l)) % p, (-g.ent(Z, 0, 0, l)) % p
        al = (ty * d_ - b * tz) * inv(det, p) % p
        be = (a * tz - c_ * ty) * inv(det, p) % p
        g.col_add(0, l, k, al); g.col_add(0, l, k - 1, be)
        assert g.ent(Y, 0, 0, l) == 0 and g.ent(Z, 0, 0, l) == 0
    assert g.ent(Y, 0, 0, k) % p
    g.col_add(0, k - 1, k, (-g.ent(Y, 0, 0, k - 1) * inv(g.ent(Y, 0, 0, k), p)) % p)
    assert g.ent(Y, 0, 0, k - 1) == 0 and g.ent(Z, 0, 0, k - 1) % p and g.ent(Z, 0, 0, k) % p
    g.blk_scale(Z, 0, inv(g.ent(Z, 0, 0, k - 1), p))
    g.col_scale(0, k, rho * rho * inv(g.ent(Z, 0, 0, k), p) % p)
    g.blk_scale(Y, 0, rho * inv(g.ent(Y, 0, 0, k), p) % p)
    # y-block: kill Z0|y_l (l<k-1) with pivot Z0|y_{k-1}, then block-scale to 1
    piv = g.ent(Z, 0, 1, k - 1); assert piv % p
    for l in range(k - 1): g.col_add(1, l, k - 1, (-g.ent(Z, 0, 1, l) * inv(piv, p)) % p)
    g.blk_scale(Z, 1, inv(g.ent(Z, 0, 1, k - 1), p))
    # z-block: same for Y0|z
    piv = g.ent(Y, 0, 2, k - 1); assert piv % p
    for l in range(k - 1): g.col_add(2, l, k - 1, (-g.ent(Y, 0, 2, l) * inv(piv, p)) % p)
    g.blk_scale(Y, 2, inv(g.ent(Y, 0, 2, k - 1), p))
    g.set_diag_zero()
    g.G[Z][K[Z]][g.col(2, k - 1)] = p - 1      # Z0|z_{k-1} = -1
    return g.G, K


def random_member(r, p, k, sk, rng, need_net=True, tries=2000):
    m = 3 * k + r
    for t in range(tries):
        C = []
        for c in range(3):
            M = []
            for j in range(m):
                if j < depth(r, k, c):
                    M.append([int(col == off(r, k, c) + j) for col in range(m)])
                elif c >= r and j == depth(r, k, c):
                    row = [0] * m
                    for d in range(3):
                        for l in range(depth(r, k, d)):
                            row[off(r, k, d) + l] = winEntry(sk[c][d], win(r, d), depth(r, k, d), l) % p
                    M.append(row)
                else:
                    M.append([rng.randrange(p) for _ in range(m)])
            C.append(M)
        if not need_net or not is_t0(C, p, m): return C, t + 1
    raise RuntimeError("no t=0 completion found")


if __name__ == "__main__":
    mode, r, p, k, rho = sys.argv[1], *map(int, sys.argv[2:6])
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    m = 3 * k + r; sk = skB1(rho) if r == 1 else skB2(rho)
    if mode == "recipe":
        C, K = (recipe_B1 if r == 1 else recipe_B2)(p, k, rho); tries = 0
    else:
        C, tries = random_member(r, p, k, sk, random.Random(seed), need_net=(mode == "random"))
    bad = is_t0(C, p, m)
    print(f"# mode={mode} r={r} p={p} k={k} rho={rho} IsKNskel={is_knskel(r, p, k, sk, C)} "
          f"t0={'yes' if not bad else 'NO ' + str(bad[:3])} tries={tries}", file=sys.stderr)
    print(p, m, 3)
    for M in C:
        for row in M: print(*row)

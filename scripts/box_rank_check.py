"""Sanity checks of the hypotheses chosen in Challenge.lean (independent re-implementation from the
paper's formulas, cross-checked against the C++ reference at p = 11, 13):
  * P_boxMinor: every box minor of (L T^2, L, L T) is +-1 over Z (k <= 5);
  * Q_net: every box matrix of Q_{k,p} is invertible mod p for odd p (k <= 5), and fails at p = 2.
Usage: box_rank_check.py <path-to-genz3net_test>"""
import subprocess, sys
from math import comb
from sympy import Matrix, eye, zeros

def tau_T(k):
    m = 3 * k
    return (-1) ** (k + 1) * Matrix(m, m, lambda i, l: (-1) ** i * comb(m - 1 - l, i))

def pgen(k):
    m = 3 * k
    T = tau_T(k)
    K = Matrix(m, m, lambda i, j: comb(i - j + k - 1, k - 1) if i >= j else 0)
    E = eye(m)
    if k >= 2:
        for j in range(m):
            E[k - 2, j] = 1 if j <= k - 2 else 0
    E[k - 1, k - 1] = -1
    E[k, k - 1] = 1
    L = E * K
    return [L * T * T, L, L * T]

def box(C, d):
    return Matrix.vstack(*[C[c][:d[c], :] for c in range(3) if d[c] > 0])

def qgen(k):
    m = 3 * k
    T = tau_T(k)
    F = [T * T, eye(m), T]
    Binv = box(F, (k, k, k)).inv()
    G = F[0] * Binv
    B = G[k:, k:2 * k]
    C = G[k:, 2 * k:]
    R = eye(2 * k); R[1, 0] = k - 1
    U0 = Matrix(k, k, lambda i, j: (-1) ** (i - j) * comb(k + 1, i - j) if i >= j else 0)
    V = eye(k)
    def setV(i, j, v):
        if i >= 0 and j >= 0: V[i, j] = v
    setV(k - 1, k - 1, -1); setV(k - 3, k - 3, -2); setV(k - 4, k - 4, 4); setV(k - 3, k - 4, -2)
    for j in range(0, k - 4): setV(k - 4, j, -1)
    U = U0 * V
    A = zeros(2 * k, k); A[0, k - 1] = -1
    blocks = {0: A, 1: R * B * U, 2: -(R * C * U)}
    gens = []
    for c in range(3):
        top = zeros(k, m); top[:, c * k:(c + 1) * k] = eye(k)
        bot = Matrix.hstack(*[blocks[(d - c) % 3] for d in range(3)])
        gens.append(Matrix.vstack(top, bot))
    return gens

def boxes(m):
    return [(a, b, m - a - b) for a in range(m + 1) for b in range(m + 1 - a)]

def rank_mod(M, p):
    return Matrix(M.rows, M.cols, lambda i, j: M[i, j] % p).rank(iszerofunc=lambda x: x % p == 0) if False else _rank_mod(M, p)

def _rank_mod(M, p):
    A = [[int(x) % p for x in M.row(i)] for i in range(M.rows)]
    r = 0
    for c in range(M.cols):
        piv = next((i for i in range(r, len(A)) if A[i][c]), None)
        if piv is None: continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], -1, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                f = A[i][c]; A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        r += 1
    return r

exe = sys.argv[1]
# cross-check the Python Q against C++ mod 11, 13
for p, k in [(11, 2), (11, 3), (13, 4)]:
    out = subprocess.run([exe, "mats", str(p), str(3 * k), "two"], capture_output=True, text=True).stdout.split("\n")
    Q = qgen(k)
    for c in range(3):
        assert [int(x) % p for x in Q[c]] == list(map(int, out[1 + c].split())), (p, k, c)
print("python Q == C++ two (p=11,13)")
for k in range(1, 6):
    P = pgen(k)
    dets = {box(P, d).det() for d in boxes(3 * k)}
    print(f"P k={k}: box minors {sorted(dets)}")
for k in range(2, 6):
    Q = qgen(k)
    for p in [2, 3, 5, 7, 11]:
        bad = [d for d in boxes(3 * k) if _rank_mod(box(Q, d), p) < 3 * k]
        print(f"Q k={k} p={p}: singular boxes {len(bad)}" + (f" e.g. {bad[:3]}" if bad else ""))

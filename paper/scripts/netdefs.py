# netdefs.py -- the nets P_{k,q} (Definition def:net) and Q_{k,p} (Definition def:Q) of core.tex, rebuilt from the
# paper's formulas. Pure Python ints; matrices = lists of rows.
#   P_{k,q}:  (L T^2, L, L T), L = E K, T = s_k tau, tau column l = coefficients of (1-t)^(m-1-l)
#   Q_{k,p}:  circulant graph form (A*, R B U*, -R C U*)
# Conventions (Section sec:conv): index digit v_l (least significant first) = coefficient of t^l; output digit 0
# most significant; write_mats writes "q m 3" + three lines of m*m entries (row-major), the input of netmind.cpp.
from math import comb

def binom(a, b):
    return comb(a, b) if 0 <= b <= a else 0

def zeros(r, c): return [[0] * c for _ in range(r)]
def eye(n): return [[int(i == j) for j in range(n)] for i in range(n)]
def mul(A, B):
    n, l, c = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(l)) for j in range(c)] for i in range(n)]
def modm(A, q): return [[x % q for x in r] for r in A]

def poly_pow_1mt(e, m):
    """coefficients (t^0..t^{m-1}) of (1-t)^e, e >= 0"""
    return [(-1) ** i * binom(e, i) for i in range(m)]

def frame(k):
    m = 3 * k; sk = (-1) ** (k + 1)
    tau = zeros(m, m)
    for l in range(m):
        col = poly_pow_1mt(m - 1 - l, m)
        for i in range(m): tau[i][l] = col[i]
    T = [[sk * x for x in r] for r in tau]
    T2 = mul(T, T)
    assert mul(T2, T) == eye(m), "T^3 != I"
    return T, T2

def K_mat(k):
    m = 3 * k
    return [[binom(i - j + k - 1, k - 1) if i >= j else 0 for j in range(m)] for i in range(m)]

def E_mat(k):
    m = 3 * k; E = eye(m)
    if k - 2 >= 0: E[k - 2] = [1 if j <= k - 2 else 0 for j in range(m)]
    E[k - 1] = [(-1 if j == k - 1 else 0) for j in range(m)]
    E[k] = [(1 if j in (k - 1, k) else 0) for j in range(m)]
    return E

def P_mats(k, flip=False):
    """raw generator matrices over Z of P_{k,q}; flip=True: row k of E = -e_{k-1} + e_k (diag of M -> +1)"""
    T, T2 = frame(k); K = K_mat(k); E = E_mat(k)
    if flip: E[k][k - 1] = -1
    L = mul(E, K)
    return dict(T=T, T2=T2, K=K, E=E, L=L, C=[mul(L, T2), L, mul(L, T)])

def inv_mod(A, p):
    n = len(A); M = [[x % p for x in r] + [int(i == j) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] % p)
        M[c], M[piv] = M[piv], M[c]
        iv = pow(M[c][c], -1, p); M[c] = [x * iv % p for x in M[c]]
        for i in range(n):
            if i != c and M[i][c]:
                f = M[i][c]; M[i] = [(x - f * y) % p for x, y in zip(M[i], M[c])]
    return [r[n:] for r in M]

def graph_form(C, k, p):
    """C_c B_kkk^{-1} mod p (p prime or any q when B_kkk is unimodular -- we use prime p here)"""
    Bk = [C[c][i] for c in range(3) for i in range(k)]
    Bi = inv_mod(Bk, p)
    return [modm(mul(Cc, Bi), p) for Cc in C]

def blocks(G, k):
    """Phi[c][d] = rows k..3k-1 of G[c], column block d (2k x k)"""
    return [[[G[c][k + r][d * k:(d + 1) * k] for r in range(2 * k)] for d in range(3)] for c in range(3)]

def toeplitz(series, k):
    return [[series[i - j] if i >= j else 0 for j in range(k)] for i in range(k)]

def U0(k):
    return toeplitz([(-1) ** i * binom(k + 1, i) for i in range(k)], k)

def assemble(Phi_cc, Phi_c1, Phi_c2, k, p):
    """circulant graph form -> generator matrices C_x, C_y, C_z (index digits = cell digits)"""
    m = 3 * k; C = []
    for c in range(3):
        G = zeros(m, m)
        for i in range(k): G[i][c * k + i] = 1
        blk = {c: Phi_cc, (c + 1) % 3: Phi_c1, (c + 2) % 3: Phi_c2}
        for d in range(3):
            for r in range(2 * k):
                for j in range(k): G[k + r][d * k + j] = blk[d][r][j] % p
        C.append(G)
    return C

def frame_BC(k, p):
    T, T2 = frame(k)
    G = graph_form([T2, eye(3 * k), T], k, p)
    Ph = blocks(G, k)
    B, C = Ph[0][1], Ph[0][2]
    # circulance of the frame's graph form
    assert Ph[1][2] == B and Ph[2][0] == B and Ph[1][0] == C and Ph[2][1] == C, "frame graph form not circulant"
    return B, C

def Astar(k):
    A = zeros(2 * k, k); A[0][k - 1] = -1; return A

def setV(V, i, j, v, k):
    if i >= 0 and j >= 0: V[i][j] = v

def Q_net(k, p):
    B, C = frame_BC(k, p)
    R = eye(2 * k); R[1][0] = k - 1
    V = eye(k)
    setV(V, k - 1, k - 1, -1, k); setV(V, k - 3, k - 3, -2, k); setV(V, k - 4, k - 4, 4, k); setV(V, k - 3, k - 4, -2, k)
    for j in range(0, k - 4):   # j <= k-5
        setV(V, k - 4, j, -1, k)
    U = mul(U0(k), V)
    P1 = modm(mul(mul(R, B), U), p)
    P2 = modm([[-x for x in r] for r in mul(mul(R, C), U)], p)
    return assemble(Astar(k), P1, P2, k, p), (Astar(k), P1, P2)

def point(C, q, i):
    m = len(C[0]); v = []
    for _ in range(m): v.append(i % q); i //= q
    out = []
    for Cc in C:
        X = 0
        for j in range(m): X = X * q + sum(Cc[j][l] * v[l] for l in range(m)) % q
        out.append(X)
    return tuple(out)

def write_mats(C, q, path):
    m = len(C[0])
    with open(path, 'w') as f:
        f.write(f"{q} {m} 3\n")
        for Cc in C: f.write(' '.join(str(x % q) for r in Cc for x in r) + '\n')

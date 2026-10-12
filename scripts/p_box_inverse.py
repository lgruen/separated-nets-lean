"""Print the exact integer inverse of the (k,k,k) box matrix of P_{k,q}'s generators (L T^2, L, L T),
built independently from the paper's formulas, as a Lean literal (used by Checks.lean)."""
import sys
from math import comb
from sympy import Matrix, zeros, eye

def pgen(k):
    m = 3 * k
    s = (-1) ** (k + 1)
    T = s * Matrix(m, m, lambda i, l: (-1) ** i * comb(m - 1 - l, i))
    K = Matrix(m, m, lambda i, j: comb(i - j + k - 1, k - 1) if i >= j else 0)
    E = eye(m)
    if k >= 2:
        for j in range(m):
            E[k - 2, j] = 1 if j <= k - 2 else 0
    E[k - 1, k - 1] = -1
    E[k, k - 1] = 1
    L = E * K
    return [L * T * T, L, L * T]

for k in map(int, sys.argv[1:]):
    B = Matrix.vstack(*[g[:k, :] for g in pgen(k)])
    assert B.det() in (1, -1)
    Bi = B.inv()
    rows = "; ".join(", ".join(str(int(x)) for x in Bi.row(i)) for i in range(Bi.rows))
    print(f"def pBoxInv{k} : Matrix (Fin (3 * {k})) (Fin (3 * {k})) ℤ := !![{rows}]")

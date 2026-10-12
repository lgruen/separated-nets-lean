"""Print, as Lean `!![...]` literals, the exact integer inverse of the (k,k,k) box matrix of
the frame (T^2, I, T) (paper Sec. 3), built independently from the paper's formulas.
Used only by Checks.lean, which re-verifies `box * inverse = 1` in the Lean kernel."""
import sys
from math import comb
from sympy import Matrix

def frame_box(k):
    m = 3 * k
    s = (-1) ** (k + 1)
    tau = Matrix(m, m, lambda i, l: (-1) ** i * comb(m - 1 - l, i))
    T = s * tau
    gens = [T * T, Matrix.eye(m), T]
    return Matrix.vstack(*[g[:k, :] for g in gens])

for k in map(int, sys.argv[1:]):
    B = frame_box(k)
    assert B.det() in (1, -1)
    Bi = B.inv()
    rows = "; ".join(", ".join(str(int(x)) for x in Bi.row(i)) for i in range(Bi.rows))
    print(f"-- k = {k}, det = {B.det()}")
    print(f"def frameBoxInv{k} : Matrix (Fin (3 * {k})) (Fin (3 * {k})) ℤ := !![{rows}]")

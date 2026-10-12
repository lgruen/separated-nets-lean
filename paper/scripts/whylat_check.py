"""whylat_check.py -- independent exact check of one-point-per-cube lattices (Remark rem:cubecost); used by cubecost.py.

For L = H Z^s / e (H integer upper triangular, columns = basis):
  * period: P = smallest integer with P Z^s in L;  enumerate L mod P Z^s exactly (integer units 1/e);
  * one-per-cube: the floor map L/PZ^s -> Z^s/PZ^s is a bijection;
  * min distance by brute force over all points of L in a box of radius 2 around 0;
  * offset g(n) = x - n (x the point of cube n): is n -> g(n) mod 1 additive (affine offsets, as for the first-digit
    layer n + {Bn/p} of a digital net)?
"""
import itertools, math, sys
from math import gcd

def lattice_points_mod(H, e, s, P):
    # L' = H Z^s ; L = L'/e ; want L mod P Z^s  <->  L' mod (eP) Z^s
    M = e * P
    pts = set()
    # generate subgroup of (Z/M)^s spanned by columns of H
    cols = [tuple(H[i][j] % M for i in range(s)) for j in range(s)]
    frontier = [tuple([0]*s)]; pts.add(frontier[0])
    while frontier:
        nf = []
        for p in frontier:
            for c in cols:
                q = tuple((p[i] + c[i]) % M for i in range(s))
                if q not in pts:
                    pts.add(q); nf.append(q)
        frontier = nf
    return pts

def member(H, e, s, u):  # u integer vector (units 1/e)
    # solve upper-triangular H x = u
    x = [0]*s
    for i in reversed(range(s)):
        r = u[i] - sum(H[i][j]*x[j] for j in range(i+1, s))
        if r % H[i][i]: return False
        x[i] = r // H[i][i]
    return True

def period(H, e, s):
    P = 1
    while not all(member(H, e, s, [e*P if i == j else 0 for i in range(s)]) for j in range(s)):
        P += 1
    return P

def check(H, e):
    s = len(H)
    P = period(H, e, s)
    pts = lattice_points_mod(H, e, s, P)
    M = e * P
    assert len(pts) == P**s, (len(pts), P**s)
    cubes = {}
    for p in pts:
        n = tuple(x // e for x in p)
        cubes.setdefault(n, []).append(p)
    opc = len(cubes) == P**s and all(len(v) == 1 for v in cubes.values())
    # min distance (units 1/e): vectors u in L' with |u_i| <= 2e
    best = None
    for u in itertools.product(range(-2*e, 2*e+1), repeat=s):
        if any(u) and member(H, e, s, list(u)):
            n2 = sum(x*x for x in u)
            if best is None or n2 < best: best = n2
    lam = math.sqrt(best)/e
    # linearity of offsets mod 1: g(n) in units 1/e, mod e
    lin = None
    if opc:
        g = {n: tuple((v[0][i] - e*n[i]) % e for i in range(s)) for n, v in cubes.items()}
        basis = [tuple(1 if i == j else 0 for i in range(s)) for j in range(s)]
        A = [g[b] for b in basis]
        lin = all(g[n] == tuple(sum(n[j]*A[j][i] for j in range(s)) % e for i in range(s)) for n in g)
    # phase group and product-of-projections (Hajos full-grid test)
    Y = {tuple(x % e for x in p) for p in pts}
    prod = 1
    for i in range(s): prod *= len({y[i] for y in Y})
    return dict(e=e, period=P, one_per_cube=opc, lam=lam, lam2=f"{best}/{e*e}", offsets_linear_mod1=lin,
                phases=len(Y), product_of_projections=prod)

CASES = [   # the first maximizer printed by whylat_cube for e = 4, 6, 8, 9, 10 (s = 3)
    ([[8, 1, 4], [0, 4, 1], [0, 0, 2]], 4),
    ([[18, 3, 12], [0, 6, 1], [0, 0, 2]], 6),
    ([[128, 40, 66], [0, 1, 0], [0, 0, 4]], 8),
    ([[27, 14, 18], [0, 27, 3], [0, 0, 1]], 9),
    ([[50, 5, 11], [0, 20, 2], [0, 0, 1]], 10),   # best found for e <= 11: lambda^2 = 116/100 = 29/25
]
if __name__ == "__main__":
    for H, e in CASES:
        print(H, check(H, e))

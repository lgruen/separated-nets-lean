#!/usr/bin/env python3
"""Entry HL8: interpolate the column polynomials f_{d,n} (gco) of the s = 8 split-frame design
(witnesses/llg_s8_design.json) independently of the search code, check reachability (degree <= n),
the dominance data (Half, zero deeper diagonal, A_c <= a_c, B), and factor every number whose primes
enter admissibility (point differences, lambda', leading coefficients gco d n n, denominators),
per level.  Prints the Lean data block with --lean.
Usage: uv run --with sympy python scripts/hl8_data.py [--lean]"""
import json, os, sys
from fractions import Fraction as Fr
import sympy

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
D = json.load(open(os.path.join(ROOT, '..', 'witnesses', 'llg_s8_design.json')))
s = D['s']; u = D['u']; v = D['v']; F2 = D['F2']; lam = [Fr(x) for x in D['lamp']]
assert s == 8 and len(F2) == s - 1

def y(c, d): return Fr(1, u[c] - v[d])

def interp(xs, ys):
    """coefficients (constant first) of the interpolating polynomial, exact."""
    n = len(xs); coef = [Fr(0)] * n
    for i in range(n):
        basis = [Fr(1)]; den = Fr(1)
        for j in range(n):
            if j != i:
                basis = [Fr(0)] + basis
                for t in range(len(basis) - 1):
                    basis[t] -= xs[j] * basis[t + 1]
                den *= xs[i] - xs[j]
        for t in range(n):
            coef[t] += ys[i] * basis[t] / den
    return coef

gco = {}
for d in range(s):
    cs = [c for c in range(s) if c != d]
    for n in range(s - 1):
        vals = [Fr(F2[n][c][d], 2) / (lam[c] * y(c, d)) for c in cs]
        co = interp([y(c, d) for c in cs], vals)
        assert all(x == 0 for x in co[n + 1:]), ("not reachable", d, n)
        assert co[n] != 0
        gco[d, n] = co[:n + 1]

def HLdes(n, c, d):
    if c == d:
        return Fr(F2[0][c][c], 2) if n == 0 else Fr(0)
    return lam[c] * sum(gco[d, n][t] * y(c, d) ** (t + 1) for t in range(n + 1))

assert all(2 * HLdes(n, c, d) == F2[n][c][d] for n in range(s - 1) for c in range(s) for d in range(s))
assert all(F2[n][c][c] == 0 for n in range(1, s - 1) for c in range(s))
assert all(F2[0][c][d] % 2 == 1 for c in range(s) for d in range(s))
assert all(F2[n][c][d] % 2 == 0 for n in range(1, s - 1) for c in range(s) for d in range(s))
M2 = [[[sum(F2[i][c][d] for i in range(j + 1)) for d in range(s)] for c in range(s)] for j in range(s - 1)]
A2 = [sum(max(abs(M2[j][c][d]) for j in range(s - 1)) for d in range(s) if d != c) for c in range(s)]
assert all(A2[c] <= -F2[0][c][c] for c in range(s))
B = max(-F2[0][c][c] + A2[c] for c in range(s))
print("B =", B, "json B =", D['B']); assert str(B) == D['B']

def primes(x):
    x = Fr(x); return set(sympy.factorint(abs(x.numerator))) | set(sympy.factorint(x.denominator))
pts = [p for c in range(s) for p in (v[c], u[c])]
lev = {}
P = set()
for i in range(len(pts)):
    for j in range(i):
        P |= primes(pts[i] - pts[j])
lev['pts'] = P
lev['lam'] = set().union(*[primes(x) for x in lam])
for n in range(s - 1):
    lev[n] = set().union(*[primes(gco[d, n][n]) for d in range(s)])
dens = set().union(*[set(sympy.factorint(x.denominator)) for d in range(s) for n in range(s - 1) for x in gco[d, n]])
for kk, vv in lev.items():
    print("level", kk, sorted(vv))
print("all denominators of gco:", sorted(dens))
allp = set().union(*lev.values())
print(len(allp), "exceptional primes:", sorted(allp))
paper = [2, 3, 5, 7, 11, 13, 17, 19, 31, 37, 97, 281, 773, 1193, 2543, 3119, 5647, 61, 211, 257, 271, 1171,
         2903, 10331, 58831, 7623037, 736578889, 233, 293, 11833, 52541, 203381, 656303, 1171699, 1717117,
         7819033, 743720623, 979256059, 5526505499, 3061420595773]
print("paper list (40):", len(paper), "equal:", sorted(paper) == sorted(allp))
if '--lean' in sys.argv:
    def q(x):
        x = Fr(x); return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"
    print("def gcoTabB8 : List (List (List ℚ)) :=")
    rows = []
    for d in range(s):
        rows.append("[" + ", ".join("[" + ", ".join(q(x) for x in gco[d, n]) + "]" for n in range(s - 1)) + "]")
    print("  [" + ",\n   ".join(rows) + "]")
    print("def F2TabB8 : List (List (List ℤ)) :=")
    print("  [" + ",\n   ".join("[" + ", ".join("[" + ", ".join(str(x) for x in r) + "]" for r in Fn) + "]" for Fn in F2) + "]")
if '--mult' in sys.argv:
    mult = {}
    nums = [Fr(x) for x in lam] + [Fr(pts[i] - pts[j]) for i in range(len(pts)) for j in range(i)]
    nums += [gco[d, n][t] for d in range(s) for n in range(s - 1) for t in range(n + 1)]
    for x in nums:
        for part in (abs(x.numerator), x.denominator):
            for p, e in sympy.factorint(part).items():
                mult[p] = max(mult.get(p, 0), e)
    print("max multiplicities:", sorted(mult.items()))

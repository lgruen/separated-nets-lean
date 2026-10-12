#!/usr/bin/env python3
"""rem:gk2d: the even-m Gruenschloss-Keller permutation (0,m,2)-nets are not digitally shifted digital nets.

Builds the points (X, Y) of rem:gk2d for m = 2r (R = 2^r, N = R^2):
    X = (R*rev_r(k) + floor(k/4) + (R/4)(j+1)) mod N,  Y = k + R*j,  0 <= j, k < R,
reads each point as the 2m-bit vector of the binary digits of X and Y, and checks
(1) the net property (every elementary interval of every shape (d, m-d) holds one point);
(2) whether the digit vectors form an affine subspace of F_2^{2m}: for N = 2^m vectors this holds iff the
    F_2-span of {v xor v0} has dimension m.  A digitally shifted digital net is such an affine subspace.
Run: uv run python scripts/gk2d_affine.py   (< 1 s; exit status 1 if a net check fails or a net is affine)
"""
import sys


def rev(x, r):
    return int(format(x, "0%db" % r)[::-1], 2)


def points(m):
    r = m // 2
    R, N = 1 << r, 1 << m
    return [((R * rev(k, r) + k // 4 + (R // 4) * (j + 1)) % N, k + R * j) for j in range(R) for k in range(R)]


def is_net(P, m):
    for d in range(m + 1):
        seen = set()
        for X, Y in P:
            key = (X >> (m - d), Y >> d)
            if key in seen:
                return False
            seen.add(key)
    return True


def span_dim(vecs):
    basis = []  # reduced rows, keyed by leading bit
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


ok = True
for m in (4, 6, 8, 10):
    P = points(m)
    vec = [(X << m) | Y for X, Y in P]
    dim = span_dim([v ^ vec[0] for v in vec])
    net = is_net(P, m)
    affine = dim == m
    print("m=%d: net=%s, dim span(v xor v0)=%d (affine iff %d), affine=%s" % (m, net, dim, m, affine))
    ok &= net and not affine
print("OK" if ok else "FAIL")
sys.exit(0 if ok else 1)

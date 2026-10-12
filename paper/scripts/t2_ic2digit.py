#!/usr/bin/env python3
"""t2_ic2digit.py -- exact two-digit separation relaxation (the proof scheme of
Theorem thm:two) for the m = 3k nets of Theorem thm:two, in
EXACT integer arithmetic.  Used by truncate_bounds.py; runs in < 1 s.

Relaxation.  Rows G[j][c][d][i] (j = 0, 1 offset digit; block (c, d);
i = 0 is level k-1, ..., W-1 = level k-W).  A neighbour step e in {-1,0,1}^3 \\ 0 with carry depths j_d (d moving)
changes digit j of coordinate c by the constant D_{c,j} = sum_d e_d sum_{i<=j_d} G[j][c][d][i] (mod p); the real
change is D mod p or D mod p - p (only 0 if D = 0 mod p).  In units of p^-2 cells, coordinate c moves by
V_c = e_c p^2 + d_1 p + d_2 (+ jitter phi, |phi| < 1, phi = 0 iff only c's own index moves), so
a_c = |V_c| (no jitter) or max(0, |V_c| - 1), and LB^2 = min_{e, j} sum_c a_c^2 / p^4.  W = 4 levels: 26
directions x carries = 728 configurations (the count in the proof of Theorem thm:two).

Self-test: for Q_{k,p} (rows of Corollary cor:rows) the relaxation must equal the closed form of Theorem thm:two,
S = p^2(p-1)^2 + (p-1)^2 + (p-2)^2, at every prime 11 <= p <= 400 (the claim of app:verify).
"""
import itertools
import os
import sys


# tau-symmetric blocks: Phi_cc = A, Phi_{c,c+1} = B, Phi_{c,c+2} = C (indices mod 3)
def cyc(A, B, C):
    """A, B, C: [row0 (4 levels), row1 (4 levels)] -> G[j][c][d][i]."""
    blk = {0: A, 1: B, 2: C}
    return [[[list(blk[(d - c) % 3][j]) for d in range(3)] for c in range(3)] for j in range(2)]


def configs(W=4):
    for e in itertools.product((-1, 0, 1), repeat=3):
        if e == (0, 0, 0):
            continue
        mv = [d for d in range(3) if e[d]]
        for js in itertools.product(range(W), repeat=len(mv)):
            j = [0, 0, 0]
            for d, v in zip(mv, js):
                j[d] = v
            yield e, tuple(j)


def cert_S(p, G):
    """exact integer S = min over configurations of sum_c a_c^2 (units p^-4); LB = sqrt(S)/p^2.
    returns (S, argmin (e, j), number of configurations)."""
    W = len(G[0][0][0])
    best, arg, ncfg = None, None, 0
    for e, j in configs(W):
        ncfg += 1
        tot = 0
        for c in range(3):
            Ds = [sum(e[d] * sum(G[r][c][d][i] for i in range(j[d] + 1)) for d in range(3) if e[d]) for r in range(2)]
            opts = []
            for D in Ds:
                r = D % p
                opts.append([0] if r == 0 else [r, r - p])
            jit = any(e[d] for d in range(3) if d != c)
            mn = None
            for d1 in opts[0]:
                for d2 in opts[1]:
                    V = e[c] * p * p + d1 * p + d2
                    a = max(0, abs(V) - 1) if jit else abs(V)
                    if mn is None or a < mn:
                        mn = a
            tot += mn * mn
        if best is None or tot < best:
            best, arg = tot, (e, j)
    return best, arg, ncfg


# Corollary cor:rows (Q_k over Z): row 0 / row 1 of A_*, Phi_{c,c+1}, Phi_{c,c+2}
QROWS = cyc([[-1, 0, 0, 0], [0, 0, 0, 0]], [[-1, -1, 0, 0], [0, -1, -2, -2]], [[-1, 0, 0, 0], [1, -1, 2, -2]])


def cstar_S(p):
    return p * p * (p - 1) ** 2 + (p - 1) ** 2 + (p - 2) ** 2


if __name__ == '__main__':
    from math import isqrt
    bad = [p for p in range(11, 401) if all(p % r for r in range(2, isqrt(p) + 1)) and cert_S(p, QROWS)[0] != cstar_S(p)]
    print('Q_{k,p} closed form 11<=p<=400 mismatches:', bad)
    sys.exit(1 if bad else 0)

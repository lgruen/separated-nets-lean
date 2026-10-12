#!/usr/bin/env python3
"""wfamily.py -- rev 15.3: Proposition prop:wfamily (optimum of the rank-one layers w u^T, w = (2,2,1), at m = 3) and
Remark rem:wstar (the nets W*_p that reach it), Section sec:wnet.

Exact arithmetic throughout: rationals (Fraction), integers, and numbers a + b sqrt(31) (class R31, exact signs),
except the threshold roots (mpmath at 60 digits, with a guard against near-ties).  Checked here:
  [1] the constants: eps* = (13 - 2 sqrt31)/90 is the smaller root of 45 e^2 - 13 e + 1/4 = q_a - q_b; q_a(eps*) =
      q_b(eps*) = mu*^2 = (72 - 8 sqrt31)/25; K = |q_a'(eps*)|/2 = (9 sqrt31 - 36)/5 > q_b'(eps*)/2 = (36 - 4 sqrt31)/5;
      q_a decreases and q_b increases on [0, 1/18]; 1/48 is the unit fraction closest to eps*; q_a(1/48) = 281/256 <
      q_b(1/48) = 211/192; mu*^2 - 281/256 < 7e-4.
  [2] every numerical fact of the proof of (3) (the six contacts) and of (2) (the rows (c)-(g) at 3/100, 1.05^2).
  [3] F(tau*) = mu*^2 from ALL options of all steps in {-2..2}^3 (exact in Q(sqrt31)); the tying options are rows
      (a), (b) and their images; the next value.
  [4] (1): F_p(u) = F(u/p) -- the rule of the model against a brute force over the points without third digits (no
      use of lem:wwrap): every u at p = 5, 7, 11 and random u at 13, 17; and max_u F_p(u) < mu*^2 over ALL u != 0 at
      every prime 5 <= p <= 61 (the strict inequality of (3) for nets, exhaustively at small p).
  [5] (2) at the nets: F_p(u) = min(q_a(eps), q_b(eps)) for u = ((p-rho)/2, (p-rho)/2, rho), every odd rho with
      rho/(2p) <= 3/100, primes 53..400 (all such rho), and for W*_p at every prime 401..3000.
  [6] rem:wstar: W*_p is a (0,3,3)-net (10 box determinants, every prime 5..3000; the minors -rho, 2rho, h-r, -4rho,
      -3rho in (0,p) up to sign); |eps_p - eps*| < 1/(2p); eps_p <= 3/100 for p >= 17; F_p > mu*^2 - K/p exactly at every
      prime 17..3000; W*_p = W_p for p < 193; the primes <= 1009 where they
      differ; W*_p != W_p for every p > 8548; at the differing primes <= 1009, eps(W*) < eps* < eps(W).
  [7] thresholds of the bound sqrt(mu*^2 - K/p) - sqrt3/p: > 1 from 67, > sqrt66/8 from 97, > sqrt281/16 from 9791, >
      sqrt281/16 + 5/(2p) (prop:wnet(3)) from 17737 (each: false at the previous prime, true here, monotone).
  [8] exact minimum distances of W_p and W*_p where they differ (p <= 1009): cellmin.cpp at 193, 241, 337, the rest from
      wstar_exact.json (audit data, cross-checked against both CSVs of ../../wnet_gap*/ when present); W_p ahead at all 8.
  [9] rem:wshift: the digit 2 zeta + 1 has the same wrap pairs as lem:wwrap (enumeration, p = 5..31).
 [10] every value printed in core.tex for these items.

    g++ -O3 -std=c++17 -o scripts/bin/cellmin scripts/cellmin.cpp
    uv run --with numpy --with mpmath python scripts/wfamily.py          (~30 s)
"""
import itertools
import json
import math
import os
import random
import re
import subprocess
import sys
import time
from fractions import Fraction as Fr
from math import isqrt

import mpmath
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)
GEO = os.path.dirname(PAPER)
CORE = os.path.join(PAPER, 'core.tex')
CELLMIN = os.path.join(HERE, 'bin', 'cellmin')
sys.path.insert(0, HERE)
import wnet  # noqa: E402  (is_net, W, cellmin, primes)

mpmath.mp.dps = 60
FAIL, NCHK = [], [0]
WV = (2, 2, 1)
STEPS = [E for E in itertools.product(range(-2, 3), repeat=3) if any(E)]


T0 = time.time()


def tick(s):
    print(f'{s}   [{time.time() - T0:.1f} s]')


def check(ok, what):
    NCHK[0] += 1
    if not ok:
        FAIL.append(what)
        print('  FAIL:', what)


class R31:
    """a + b sqrt(31), a, b rational; exact sign and comparisons"""
    __slots__ = ('a', 'b')

    def __init__(self, a, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def _c(self, o):
        return o if isinstance(o, R31) else R31(o)

    def __add__(self, o):
        o = self._c(o)
        return R31(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __neg__(self):
        return R31(-self.a, -self.b)

    def __sub__(self, o):
        return self + (-self._c(o))

    def __rsub__(self, o):
        return self._c(o) - self

    def __mul__(self, o):
        o = self._c(o)
        return R31(self.a * o.a + 31 * self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = self._c(o)
        n = o.a * o.a - 31 * o.b * o.b
        return self * R31(o.a / n, -o.b / n)

    def sign(self):
        a, b = self.a, self.b
        if b == 0:
            return (a > 0) - (a < 0)
        if a >= 0 and b >= 0:
            return 1
        if a <= 0 and b <= 0:
            return -1
        d = a * a - 31 * b * b
        return ((d > 0) - (d < 0)) * (1 if a > 0 else -1)

    def __lt__(self, o):
        return (self - o).sign() < 0

    def __le__(self, o):
        return (self - o).sign() <= 0

    def __gt__(self, o):
        return (self - o).sign() > 0

    def __ge__(self, o):
        return (self - o).sign() >= 0

    def __eq__(self, o):
        return (self - o).sign() == 0

    def __hash__(self):
        return hash((self.a, self.b))

    def mp(self):
        return mpmath.mpf(self.a.numerator) / self.a.denominator + mpmath.mpf(self.b.numerator) / self.b.denominator * mpmath.sqrt(31)

    def floor(self):
        k = int(mpmath.floor(self.mp()))
        for j in (k - 1, k, k + 1):
            if R31(j) <= self < R31(j + 1):
                return j
        raise AssertionError('floor')

    def __repr__(self):
        return f'{self.a}+{self.b}r31'


S31 = R31(0, 1)
EPS = (13 - 2 * S31) / 90
MU2 = (72 - 8 * S31) / 25
KA = (9 * S31 - 36) / 5
KB = (36 - 4 * S31) / 5


def qa(e):
    return Fr(5, 4) - 9 * e + 81 * e * e


def qb(e):
    return 1 + 4 * e + 36 * e * e


def isprime(n):
    return n > 1 and all(n % k for k in range(2, isqrt(n) + 1))


def primes(a, b):
    return [p for p in range(a, b + 1) if isprime(p)]


def Wr(p, r):
    """W_p of prop:wnet with a given r (r = floor(p/48): W_p; r = floor(p eps*): W*_p)"""
    h, rho = (p - 1) // 2, 2 * r + 1
    return [[-rho, -rho, 2 * rho], [-rho, -rho, 2 * rho], [h - r, h - r, rho]], [[0, 1, 2], [1, 0, 1], [0, 1, 0]]


def rstar(p):
    return (p * EPS).floor()


def Fp_rule(p, u):
    """p^2 F(u/p): the options of the definition of F (equivalently of lem:wwrap), integers"""
    h, best = (p - 1) // 2, None
    for E in STEPS:
        sig = sum(a * b for a, b in zip(u, E)) % p
        for dz in ([0] if sig == 0 else [sig, sig - p]):
            for k in {(dz > 0) - (dz < 0)} | ({0} if abs(dz) <= h else set()):
                v = (p * E[0] + 2 * dz - p * k, p * E[1] + 2 * dz - p * k, p * E[2] + dz)
                n2 = v[0] ** 2 + v[1] ** 2 + v[2] ** 2
                best = n2 if best is None or n2 < best else best
    return best


def Fp_rule_all(p):
    """p^2 F(u/p) for ALL u in F_p^3 (numpy, vectorized over u); index u = (ux, uy, uz)"""
    h = (p - 1) // 2
    ux, uy, uz = np.meshgrid(np.arange(p), np.arange(p), np.arange(p), indexing='ij')
    best = np.full(ux.shape, 1 << 62, dtype=np.int64)
    for E in STEPS:
        sig = (ux * E[0] + uy * E[1] + uz * E[2]) % p
        for dz in (sig, sig - p):
            valid = dz != -p                                 # sigma = 0: only dz = 0
            for k, ok in ((np.sign(dz), valid), (np.zeros_like(dz), valid & (np.abs(dz) <= h))):
                vx = p * E[0] + 2 * dz - p * k
                vy = p * E[1] + 2 * dz - p * k
                vz = p * E[2] + dz
                n2 = vx * vx + vy * vy + vz * vz
                best = np.where(ok & (n2 < best), n2, best)
    return best


def Fp_brute_all(p, us):
    """p^2 F_p(u) from the points p^2 n + p g(n) (no third digits), by scanning every cell n and step E in {-2..2}^3:
    independent of lem:wwrap"""
    n = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)
    out = {}
    for u in us:
        z = (n @ np.array(u)) % p
        g = np.stack([2 * z % p, 2 * z % p, z], 1)
        best = None
        for E in STEPS:
            m = (n + np.array(E)) % p
            z2 = (m @ np.array(u)) % p
            g2 = np.stack([2 * z2 % p, 2 * z2 % p, z2], 1)
            v = p * np.array(E) + g2 - g
            b = int((v * v).sum(1).min())
            best = b if best is None or b < best else best
        out[u] = best
    return out


def lt_mu2(N, p):
    """N/p^2 < mu*^2 exactly (N integer)"""
    return R31(Fr(N, p * p)) < MU2


def trunc(x, nd):
    """the truncation of the mpmath value x to nd decimals, as a string"""
    v = int(mpmath.floor(x * 10 ** nd))
    return f'{v // 10 ** nd}.{v % 10 ** nd:0{nd}d}'



def main():
    TEX = open(CORE, encoding='utf-8').read()
    i0 = TEX.index('\\label{sec:wnet}')
    SEC = TEX[i0:TEX.index('\\subsection', i0 + 20)]
    i1 = TEX.index('\\label{rem:wshift}')   # rev 15.7 pass 3: the T_p/W_p half of rem:shiftshared moved here
    REMS = TEX[i1:TEX.index('\\end{remark}', i1)]

    tick('[1] constants')
    check(45 * EPS * EPS - 13 * EPS + Fr(1, 4) == R31(0), 'eps* is a root of 45e^2 - 13e + 1/4')
    other = (13 + 2 * S31) / 90
    check(EPS < other, 'eps* is the smaller root')
    check(qa(EPS) == MU2 and qb(EPS) == MU2, 'q_a(eps*) = q_b(eps*) = (72 - 8 sqrt31)/25')
    check(all(qa(e) - qb(e) == 45 * e * e - 13 * e + Fr(1, 4) for e in (Fr(1, 7), Fr(3, 100), Fr(0))), 'q_a - q_b')
    dqa, dqb = -9 + 162 * EPS, 4 + 72 * EPS
    check(-dqa / 2 == KA and dqb / 2 == KB and KB < KA and KA + KB == S31, 'K = |q_a\'|/2 = (9 sqrt31 - 36)/5 > K_b')
    check(Fr(9, 162) == Fr(1, 18) and EPS < Fr(1, 18) and EPS < Fr(3, 100),
          'vertex of q_a at 1/18: q_a decreases, q_b increases on [0, 1/18] (q_b vertex at -1/18)')
    check(abs((Fr(1, 48) - EPS).mp()) < abs((Fr(1, 49) - EPS).mp()) and abs((Fr(1, 48) - EPS).mp()) < abs((Fr(1, 47) - EPS).mp())
          and R31(Fr(1, 49)) < EPS < R31(Fr(1, 48)), '1/48 is the unit fraction closest to eps* (1/49 < eps* < 1/48)')
    check(qa(Fr(1, 48)) == Fr(281, 256) and qb(Fr(1, 48)) == Fr(211, 192) and Fr(281, 256) < Fr(211, 192),
          'q_a(1/48) = 281/256 < q_b(1/48) = 211/192')
    check(MU2 - Fr(281, 256) < R31(Fr(7, 10000)) and MU2 - Fr(281, 256) > R31(Fr(6, 10000)), 'mu*^2 - 281/256 < 7e-4')
    mu = mpmath.sqrt(MU2.mp())
    print(f'    eps* = {mpmath.nstr(EPS.mp(), 12)}, mu* = {mpmath.nstr(mu, 14)}, K = {mpmath.nstr(KA.mp(), 12)}')

    tick('[2] numerical facts of the proofs of (2) and (3)')
    O1 = lambda f: 9 * f * f - 8 * f + 2
    Ox = lambda g: 9 * g * g - 4 * g + 1
    check(O1(Fr(2, 15)) == Fr(246, 225) and O1(Fr(3, 4)) == Fr(17, 16), 'e_z: 9f^2-8f+2 = 246/225 at 2/15, 17/16 at 3/4')
    check(all(R31(x) < MU2 for x in (Fr(246, 225), Fr(17, 16), Fr(9, 25), 1)), '246/225, 17/16, 9/25, 1 < mu*^2')
    check(8 * Fr(1, 16) + Fr(9, 16) == Fr(17, 16), 'f = 3/4: 8(1-f)^2 + f^2 = 17/16 (and 1 at f = 1)')
    check(Ox(Fr(0)) == 1 and Ox(Fr(7, 15)) == Fr(246, 225), 'e_x: 9g^2-4g+1 = 1 at 0, 246/225 at 7/15')
    check(Fr(1, 2) - Fr(7, 15) == Fr(1, 30), 'alpha in (-1/30, 1/30)')
    check(qb(Fr(1, 15)) == 1 + 2 * Fr(2, 15) + 9 * Fr(2, 15) ** 2, 'q_b(f/2) = 1 + 2f + 9f^2')
    check(2 * EPS - Fr(1, 15) > R31(-1) and 2 * EPS - Fr(1, 15) > R31(Fr(-1, 15)) and Fr(2, 15) + Fr(2, 30) == Fr(1, 5),
          'lock: sigma~ in (-1/15, 1/5)')
    check(9 * Fr(1, 5) ** 2 == Fr(9, 25), 'lock: 9 sigma~^2 < 9/25')
    check(2 * EPS - Fr(1, 30) > R31(0) and Fr(1, 30) + Fr(2, 15) == Fr(1, 6) and Fr(1, 6) / 3 == Fr(1, 18),
          'diagonal: s in (2eps* - 1/30, 1/6) subset (0, 1/6), s/3 < 1/18')
    check(all(qa(s / 3) == Fr(5, 4) - 3 * s + 9 * s * s for s in (Fr(1, 7), Fr(1, 10))), 'q_a(s/3) = 5/4 - 3s + 9s^2')
    s_ = Fr(1, 9)
    V = (1 - 2 * s_, -2 * s_, -Fr(1, 2) - s_)
    d_ = Fr(1, 2) - s_
    check(V == (2 * d_, 2 * d_ - 1, d_ - 1), 'V of (1,0,-1) with delta = 1/2 - s, kappa = 1')
    # (2): rows at 3/100, all decreasing on (0, 3/100]; 1.05^2; 8 eps < 1/2
    e3 = Fr(3, 100)
    rc, rd, rf = (lambda e: Fr(5, 4) - 5 * e + 9 * e * e), (lambda e: Fr(5, 4) - 3 * e + 9 * e * e), (lambda e: 2 - 16 * e + 36 * e * e)
    check(rc(e3) == Fr(11081, 10000) and rd(e3) == Fr(11681, 10000) and rf(e3) == Fr(15524, 10000),
          'rows (c), (d), (f) at 3/100: 1.1081, 1.1681, 1.5524')
    check(-5 + 18 * e3 < 0 and -3 + 18 * e3 < 0 and -16 + 72 * e3 < 0, 'rows (c), (d), (f) decrease on (0, 3/100]')
    check(Fr(105, 100) ** 2 == Fr(11025, 10000) and R31(Fr(11025, 10000)) > MU2 and R31(Fr(11081, 10000)) > MU2,
          '1.05^2 = 1.1025 > mu*^2; 1.1081 > mu*^2')
    check(8 * e3 < Fr(1, 2), '|Q eps| <= 8 eps < 1/2 for eps <= 3/100')
    check(all(qb(e) <= qa(e) for e in [Fr(k, 10000) for k in range(1, 207)]) and
          all(qa(e) <= qb(e) for e in [Fr(k, 10000) for k in range(208, 301)]), 'min(q_a, q_b): q_b below eps*, q_a above')

    tick('[3] F(tau*) = mu*^2 from all options')
    tau = (Fr(1, 2) - EPS, Fr(1, 2) - EPS, 2 * EPS)
    vals = []
    for E in STEPS:
        x = sum((t * e for t, e in zip(tau, E)), R31(0))
        s = x - x.floor()
        ds = [s] if s == R31(0) else [s, s - 1]
        for d in ds:
            sg = d.sign()
            for k in {sg} | ({0} if (d - Fr(1, 2)).sign() < 0 and (d + Fr(1, 2)).sign() > 0 else set()):
                v = [E[c] + d * WV[c] - (k if c < 2 else 0) for c in range(3)]
                vals.append((v[0] * v[0] + v[1] * v[1] + v[2] * v[2], E, k))
    mn = min(vals, key=lambda t: t[0].mp())[0]
    ties = [t for t in vals if t[0] == MU2]
    nxt = min(t[0].mp() for t in vals if not t[0] == MU2)
    check(mn == MU2 and all(t[0] >= MU2 for t in vals), 'F(tau*) = mu*^2 exactly (all options of all 124 steps)')
    check(sorted(t[1] for t in ties) == sorted([(1, 0, -1), (-1, 0, 1), (0, 1, -1), (0, -1, 1), (0, 0, 1), (0, 0, -1),
                                               (1, 1, 2), (-1, -1, -2)]),
          f'the tying options: rows (a), (b) and their images ({len(ties)})')
    print(f'    {len(vals)} options; {len(ties)} attain mu*^2; next value {mpmath.nstr(nxt, 8)}')

    tick('[4] F_p(u) = F(u/p) (brute force over the points) and max_u F_p(u) < mu*^2')
    random.seed(1)
    nb = 0
    for p, us in ((5, None), (7, None), (11, None), (13, 300), (17, 150)):
        allu = [u for u in itertools.product(range(p), repeat=3) if any(u)]
        sel = allu if us is None else random.sample(allu, us)
        br = Fp_brute_all(p, sel)
        nb += sum(br[u] != Fp_rule(p, u) for u in sel)
    check(nb == 0, 'F_p(u) from the points without third digits == the rule of F at u/p (p = 5, 7, 11 all u; 13, 17 sampled)')
    worst = None
    for p in primes(5, 61):
        A = Fp_rule_all(p)
        A[0, 0, 0] = -1                                     # u = 0 is not a net
        if p in (11, 13):
            for u in random.sample([u for u in itertools.product(range(p), repeat=3) if any(u)], 40):
                check(int(A[u]) == Fp_rule(p, u), f'numpy rule == scalar rule at p = {p}, u = {u}')
        N = int(A.max())
        ok = lt_mu2(N, p)
        check(ok, f'max_u F_p(u) < mu*^2 at p = {p}')
        gap = float(p * (MU2.mp() - mpmath.mpf(N) / p ** 2))
        worst = (gap, p) if worst is None or gap < worst[0] else worst
    print(f'    every prime 5..61: max_u F_p(u) < mu*^2; least p(mu*^2 - max) = {worst[0]:.4f} at p = {worst[1]}')

    tick('[5] (2) at the nets: F_p = min(q_a(eps), q_b(eps)) for u = ((p-rho)/2, (p-rho)/2, rho), rho/(2p) <= 3/100')
    nbad = ncase = 0
    for p in primes(53, 400):
        for rho in range(1, p, 2):
            if Fr(rho, 2 * p) > e3:
                break
            u = ((p - rho) // 2, (p - rho) // 2, rho)
            e = Fr(rho, 2 * p)
            ncase += 1
            nbad += Fr(Fp_rule(p, u), p * p) != min(qa(e), qb(e))
    for p in primes(401, 3000):
        rho = 2 * rstar(p) + 1
        u = ((p - rho) // 2, (p - rho) // 2, rho)
        e = Fr(rho, 2 * p)
        ncase += 1
        nbad += Fr(Fp_rule(p, u), p * p) != min(qa(e), qb(e))
    check(nbad == 0, f'(2): F_p(u) = min(q_a, q_b) in {ncase} cases (all odd rho at primes 53..400; W*_p at 401..3000)')

    tick('[6] rem:wstar: W*_p')
    bad = []
    for p in primes(5, 3000):
        r = rstar(p)
        B, R = Wr(p, r)
        h, rho = (p - 1) // 2, 2 * r + 1
        if not (wnet.is_net(B, R, p) and 1 <= rho < p and 1 <= h - r < p and all(x % p for x in (rho, 2 * rho, 3 * rho, 4 * rho, h - r))):
            bad.append(p)
        if not (R31(Fr(2 * r, 2 * p)) < EPS < R31(Fr(2 * r + 2, 2 * p))) or not abs((Fr(rho, 2 * p) - EPS).mp()) < mpmath.mpf(1) / (2 * p):
            bad.append(('eps', p))
        if abs(rho - 2 * p * EPS.mp()) >= 1:                 # rho = odd integer nearest to 2 p eps*
            bad.append(('nearest', p))
    check(not bad, f'W*_p: (0,3,3)-net, minors units, |eps_p - eps*| < 1/(2p), rho nearest odd, primes 5..3000 ({bad[:5]})')
    check(Fr(3, 106) == Fr(2 * rstar(53) + 1, 106) and Fr(3, 106) <= e3 and EPS + Fr(1, 118) < R31(e3)
          and all(rstar(p) == 0 and Fr(1, 2 * p) <= e3 for p in primes(17, 47)) and not Fr(1, 26) <= e3
          and all(Fr(2 * rstar(p) + 1, 2 * p) <= e3 for p in primes(17, 3000)),
          'eps_p <= 3/100 for p >= 17 (1/(2p) for p <= 47, eps_53 = 3/106; not at p = 13)')
    nbad, least = 0, None
    for p in primes(17, 3000):
        rho = 2 * rstar(p) + 1
        u = ((p - rho) // 2, (p - rho) // 2, rho)
        F = R31(Fr(Fp_rule(p, u), p * p))
        lb = MU2 - KA / p
        nbad += not (F > lb)
        m_ = float(p * (F - lb).mp())
        least = (m_, p) if least is None or m_ < least[0] else least
    check(nbad == 0, 'F_p(W*_p) > mu*^2 - K/p exactly at every prime 17..3000')
    print(f'    least p(F_p - mu*^2 + K/p) = {least[0]:.4f} at p = {least[1]}')

    def LB(p):
        return mpmath.sqrt(MU2.mp() - KA.mp() / p) - mpmath.sqrt(3) / p
    check(all(rstar(p) == 0 == p // 48 for p in primes(5, 47)), 'p <= 47: W*_p = W_p (r = 0)')
    diff = [p for p in primes(5, 1009) if rstar(p) != p // 48]
    check(diff == [193, 241, 337, 433, 577, 673, 769, 1009], f'primes <= 1009 where W*_p != W_p: {diff}')
    check(R31(Fr(8549)) * (Fr(1, 48) - EPS) > R31(1) and R31(Fr(8548)) * (Fr(1, 48) - EPS) < R31(1),
          'p (1/48 - eps*) > 1 iff p > 8548: then floor(p/48) > floor(p eps*)')
    check(all(Fr(2 * rstar(p) + 1, 2 * p) < EPS < R31(Fr(2 * (p // 48) + 1, 2 * p)) for p in diff),
          'at the differing primes <= 1009: eps(W*) < eps* < eps(W)')
    check(all(qb(Fr(2 * rstar(p) + 1, 2 * p)) < qa(Fr(2 * rstar(p) + 1, 2 * p)) and
              qa(Fr(2 * (p // 48) + 1, 2 * p)) < qb(Fr(2 * (p // 48) + 1, 2 * p)) for p in diff),
          'there W* binds at (b), W at (a), without the third digits')

    tick('[7] thresholds')
    R66, R281 = mpmath.sqrt(66) / 8, mpmath.sqrt(281) / 16
    PR = primes(53, 20000)

    def first(f):
        """the least prime p >= 53 from which f holds at every prime up to 2e4 (f(p) - f is monotone in p)"""
        ok = [f(p) for p in PR]
        i = max(j for j in range(len(PR)) if not ok[j]) + 1
        return PR[i], all(ok[i:]), PR[i - 1]
    for name, f, want in (('1', lambda p: LB(p) > 1, 67), ('sqrt66/8', lambda p: LB(p) > R66, 97),
                          ('sqrt281/16', lambda p: LB(p) > R281, 9791),
                          ('sqrt281/16 + 5/(2p)', lambda p: LB(p) > R281 + mpmath.mpf(5) / (2 * p), 17737)):
        p0, tail, prev = first(f)
        check(p0 == want and tail, f'bound > {name} from p = {p0} (not at {prev}); expected {want}')
        print(f'    > {name}: from {p0} (previous prime {prev})')
    check(all(LB(p) < LB(q) for p, q in zip(PR[:-1], PR[1:])), 'LB increasing (and sqrt281/16 + 5/(2p) decreasing)')

    tick('[8] exact minimum distances of W_p and W*_p where they differ')
    js = json.load(open(os.path.join(HERE, 'wstar_exact.json')))
    dW = {int(k): v['d2'] for k, v in js['W'].items()}
    dS = {int(k): v['d2'] for k, v in js['Wstar'].items()}
    check(sorted(dW) == sorted(dS) == diff, 'wstar_exact.json covers exactly the differing primes <= 1009')
    for p in (193, 241, 337):
        check(wnet.cellmin(*Wr(p, p // 48), p) == dW[p] and wnet.cellmin(*Wr(p, rstar(p)), p) == dS[p],
              f'cellmin == wstar_exact.json at p = {p}')
    for k, v in js['Wstar'].items():
        p = int(k)
        check(v['rho'] == 2 * rstar(p) + 1 and v['u'] == [(p - v['rho']) // 2] * 2 + [v['rho']], f'W*_{p} data: rho, u')
    for path, cn in ((os.path.join(GEO, 'wnet_gap_audit', 'amind.csv'), 'audit'), (os.path.join(GEO, 'wnet_gap', 'out', 'mind.csv'), 'note')):
        if os.path.exists(path):
            rows = [l.split(',') for l in open(path).read().split('\n')[1:] if l]
            got = {(r[0], int(r[1])): int(r[6]) for r in rows if r[0] in ('W', 'Ws')}
            check(all(got.get(('W', p)) == dW[p] and got.get(('Ws', p)) == dS[p] for p in diff), f'json == {cn} CSV')
        else:
            print(f'    ({path} not present; cross-check skipped)')
    check(all(dW[p] > dS[p] for p in diff), 'W_p ahead of W*_p at every differing prime <= 1009')
    c = lambda d, p: mpmath.sqrt(d) / p ** 2
    tr = {p: (trunc(c(dW[p], p), 4), trunc(c(dS[p], p), 4)) for p in (193, 1009)}
    print('    ', {p: (float(c(dW[p], p)), float(c(dS[p], p))) for p in diff})

    tick('[9] rem:wshift: the digit 2 zeta + 1 has the wrap pairs of lem:wwrap')
    nb = 0
    for p in primes(5, 31):
        h = (p - 1) // 2
        for d in range(1, p):
            got = {((2 * (z + d) + 1) >= p) * 1 - ((2 * z + 1) >= p) * 1 for z in range(0, p - d)}
            lem = {1} | ({0} if d <= h else set())
            nb += got != lem
    check(nb == 0, 'pairs (delta, kappa) of 2 zeta + 1 = those of lem:wwrap, p = 5..31')

    tick('[10] values printed in core.tex')
    snips = [
        ('$\\mu^*=\\sqrt{(72-8\\sqrt{31})/25}=' + trunc(mu, 4) + '\\ldots$', SEC),
        ('$\\varepsilon^*=(13-2\\sqrt{31})/90=' + trunc(EPS.mp(), 5) + '\\ldots$', SEC),
        ('\\frac{9\\sqrt{31}-36}5=' + trunc(KA.mp(), 4) + '\\ldots', SEC),
        ('$\\frac{246}{225}=' + trunc(mpmath.mpf(246) / 225, 4) + '\\ldots$', SEC),
        ('$\\mu^{*2}=' + trunc(MU2.mp(), 4) + '\\ldots$', SEC),
        ('to $1.1081$, $1.1681$ and $1.5524$', SEC), ('$1.05^2=1.1025$', SEC),
        ('from $p=67$ on and $\\sqrt{66}/8$ from $p=97$ on', SEC), ('from $p=9791$ on', SEC), ('from $p=17737$ on', SEC),
        ('$\\mathcal W^*_p=\\mathcal W_p$ for $p<193$', SEC), ('for $p>8548$', SEC),
        ('$193$, $241$, $337$, $433$, $577$, $673$, $769$ and $1009$', SEC),
        (f'${tr[193][0]}\\ldots$ against ${tr[193][1]}\\ldots$ at $p=193$', SEC),
        (f'${tr[1009][0]}\\ldots$ against ${tr[1009][1]}\\ldots$ at $p=1009$', SEC),
        ('$\\mu^{*2}-\\frac{281}{256}<7\\cdot10^{-4}$', SEC),
        ('$\\varepsilon_{53}=\\frac3{106}$', SEC), ('for every prime $p\\ge17$. With', SEC),
        ('$\\varepsilon_p=\\frac1{2p}$ for $p\\le47$', SEC), ('$\\varepsilon^*+\\frac1{118}<\\frac3{100}$', SEC),
        ('$r=\\lfloor p\\varepsilon^*\\rfloor$ in place of $\\lfloor p/48\\rfloor$', SEC),
        ('\\label{prop:wfamily}', SEC), ('\\label{rem:wstar}', SEC),
        ('$t\\equiv2t\'$ or $t\\equiv2t\'+1$', REMS),
    ]
    for s, where in snips:
        check(s in where, f'printed: {s}')
    check('heuristic reading' in SEC and 'computed' in SEC, 'rem:wstar labels the comparison computed and the reading heuristic')

    print(f'wfamily: {NCHK[0]} checks, {len(FAIL)} failures ({time.time() - T0:.1f} s)')
    sys.exit(1 if FAIL else 0)


if __name__ == '__main__':
    main()

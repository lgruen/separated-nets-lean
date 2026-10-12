#!/usr/bin/env python3
r"""gk09_decay.py -- normalized separation of the Gruenschloss--Keller base-2 (0,m,3)-net.

Reproduces the sentence in core.tex (Introduction, "Natural candidates"):
  "The base-2 (0,m,3)-net of [GK09, Sec. 2] ... its normalized separation delta*N^{1/3}
   falls, not monotonically, from 0.75 (m=3) to 0.19 (m=13)."

Construction ([GK09] = Gruenschloss & Keller, "(t,m,s)-Nets and Maximized Minimum Distance,
Part II", MCQMC 2008, Sec. 2 "A new (0,m,3)-net in base 2"):
  C'_1 = (1 if j <= r else 0)_{j,r}         Larcher--Pillichshammer (0,1)-sequence matrix
  C'_2 = C_2 C'_1 = (binom(r+1, j+1) mod 2)  Sobol'/Faure second matrix C_2=(binom(r,j) mod 2)
                                               reordered by D = C_1^{-1} C'_1 = C'_1
  point n (0 <= n < 2^m):  ( n/2^m , C'_1 d(n) , C'_2 d(n) ),  d(n) = binary digits of n
  (radical-inverse packing: output digit j -> 2^{-(j+1)}).  The (x1,x2)-projection
  (n/2^m, C'_1 d(n)) is the Larcher--Pillichshammer point set.

Two independent generators are used and must agree point-for-point:
  (a) the matrix definition above (binomials mod 2), and
  (b) a transcription of the paper's own C99 bit-twiddling routine x_n() (32-bit columns,
      truncated to the top m bits, which is exact because C'_1, C'_2 are upper triangular).
The (0,m,3)-net property is verified exactly (every elementary box of volume 2^{-m} holds one
point).  The minimum toroidal distance is computed EXACTLY on the integer grid 2^m*x (all
coordinates are integers in [0,2^m)), by chunked all-pairs in numpy (N=8192 -> 33.5M pairs).

Output: m, N, d2 = 4^m * delta^2 (integer), delta^2 N^{2/3} = d2 * 2^{-4m/3} (exact rational
when 3 | m), delta N^{1/3}.

Asserted against core.tex (Introduction and Appendix app:verify): delta N^{1/3} = .750, .649, .486, .433, .472, .466,
.424, .447, .376, .265, .187 for m = 3..13 (exact values truncated, decided in exact integer arithmetic; read from
core.tex at run time);
"falls, not monotonically, from 0.75 (m=3) to 0.19 (m=13)".

Run:  uv run --with numpy python scripts/gk09_decay.py      (~1 s)
"""
import sys
import time
from fractions import Fraction
from math import comb

import numpy as np


# ---------------------------------------------------------------- (a) matrix definition
def gk09_points_matrix(m):
    C1 = [[1 if j <= r else 0 for r in range(m)] for j in range(m)]
    C2 = [[comb(r + 1, j + 1) % 2 for r in range(m)] for j in range(m)]
    # sanity: C'_2 == Pascal * C'_1 (mod 2), the paper's derivation
    P = [[comb(r, j) % 2 for r in range(m)] for j in range(m)]
    PC1 = [[sum(P[j][k] * C1[k][r] for k in range(m)) % 2 for r in range(m)] for j in range(m)]
    assert PC1 == C2, "Christmas-stocking identity C_2 C'_1 = C'_2 failed"
    N = 1 << m
    n = np.arange(N, dtype=np.int64)
    digits = np.stack([(n >> r) & 1 for r in range(m)], axis=1)          # N x m, d_r(n)
    pts = np.empty((N, 3), dtype=np.int64)
    pts[:, 0] = n
    for col, C in ((1, C1), (2, C2)):
        out = (digits @ np.array(C, dtype=np.int64).T) & 1                # N x m, out digit j
        w = np.array([1 << (m - 1 - j) for j in range(m)], dtype=np.int64)
        pts[:, col] = out @ w
    return pts


# ---------------------------------------------------- (b) the paper's C99 routine x_n()
def gk09_point_c99(n, m):
    M32 = 0xFFFFFFFF
    x0 = n
    r1 = r2 = 0
    v1, v2 = 1 << 31, 3 << 30
    while n:
        if n & 1:
            r1 ^= v1
            r2 ^= (v2 << 1) & M32
        v1 = (v1 | (v1 >> 1)) & M32
        v2 = (v2 ^ (v2 >> 1)) & M32
        n >>= 1
    # x[1] = r1/2^32, x[2] = r2/2^32; on the 2^m grid keep the top m bits (lower bits are 0)
    assert r1 & ((1 << (32 - m)) - 1) == 0 and r2 & ((1 << (32 - m)) - 1) == 0
    return (x0, r1 >> (32 - m), r2 >> (32 - m))


# ------------------------------------------------------------------- (0,m,3)-net check
def is_0m3_net(pts, m):
    N = 1 << m
    for a in range(m + 1):
        for b in range(m + 1 - a):
            c = m - a - b
            key = ((pts[:, 0] >> (m - a)) << (b + c)) | ((pts[:, 1] >> (m - b)) << c) \
                | (pts[:, 2] >> (m - c))
            if np.bincount(key, minlength=N).max() != 1:
                return False
    return True


# ----------------------------------------------------- exact toroidal min squared distance
def min_tor_d2(pts, m, chunk=512):
    N = 1 << m
    P = pts.astype(np.int64)
    best = None
    for i0 in range(0, N, chunk):
        A = P[i0:i0 + chunk]
        diff = np.abs(A[:, None, :] - P[None, :, :])
        diff = np.minimum(diff, N - diff)
        d2 = (diff * diff).sum(axis=2)
        idx = np.arange(i0, min(i0 + chunk, N))
        d2[idx - i0, idx] = np.iinfo(np.int64).max                         # drop self-pairs
        v = int(d2.min())
        best = v if best is None else min(best, v)
    return best


def brute_d2(pts, m):
    N = 1 << m
    best = None
    for i in range(N):
        for k in range(i + 1, N):
            s = 0
            for t in range(3):
                d = abs(int(pts[i, t]) - int(pts[k, t]))
                d = min(d, N - d)
                s += d * d
            best = s if best is None else min(best, s)
    return best


def main(mmax=13):
    t0 = time.time()
    print(f"{'m':>2} {'N':>5} {'d2=4^m*delta^2':>15} {'delta^2 N^(2/3)':>22} "
          f"{'delta N^(1/3)':>14}  net  c99==matrix")
    rows = []
    for m in range(3, mmax + 1):
        pts = gk09_points_matrix(m)
        c99 = np.array([gk09_point_c99(n, m) for n in range(1 << m)], dtype=np.int64)
        same = bool((c99 == pts).all())
        net = is_0m3_net(pts, m)
        d2 = min_tor_d2(pts, m)
        if m <= 7:
            assert d2 == brute_d2(pts, m), "chunked min-dist disagrees with brute force"
        # delta^2 N^{2/3} = d2 / 4^m * 2^{2m/3} = d2 * 2^{-4m/3}
        if m % 3 == 0:
            exact = str(Fraction(d2, 2 ** (4 * m // 3)))
        else:
            exact = f"{d2}*2^(-{4 * m}/3)"
        val = d2 ** 0.5 * 2.0 ** (-2.0 * m / 3.0)
        rows.append((m, d2, val))
        print(f"{m:>2} {1 << m:>5} {d2:>15} {exact:>22} {val:>14.4f}  {str(net):>4} {str(same):>5}")
        assert net and same
    print(f"\nelapsed {time.time() - t0:.1f} s")
    return rows




def trunc(d2, m, dig):
    """floor(delta N^{1/3} 10^dig), exactly: x = sqrt(d2) 2^{-2m/3}, so x^6 = d2^3 2^{-4m} (rev 15.2: the paper prints
    exact values truncated, not rounded)"""
    D = 10 ** dig
    n = int(d2 ** 0.5 * 2.0 ** (-2.0 * m / 3.0) * D)
    x6 = Fraction(d2 ** 3, 2 ** (4 * m))
    while Fraction(n, D) ** 6 > x6:
        n -= 1
    while Fraction(n + 1, D) ** 6 <= x6:
        n += 1
    return n


def printed_list():
    """the eleven values of app:verify and the two of the Introduction, read from core.tex"""
    import os
    import re
    tex = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'core.tex')).read()
    i = tex.index('\\cite[Sec.~2]{GK09}, built from its generator matrices')
    seg = tex[i:tex.index('for $m=3,\\dots,13$', i)]
    vals = re.findall(r'[=$](\.\d{3})\$', seg)
    m = re.search(r'falls, not monotonically, from \$(0\.\d\d)\$ \(\$m=3\$\) to \$(0\.\d\d)\$ \(\$m=13\$\)', tex)
    assert m, 'introduction sentence not found'
    return vals, (m.group(1), m.group(2))


if __name__ == "__main__":
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 13
    rows = main(mmax)
    if mmax == 13:
        got = ['.%03d' % trunc(d2, m, 3) for m, d2, _ in rows]
        vals = [v for _, _, v in rows]
        PAPER, (i3, i13) = printed_list()
        assert len(PAPER) == 11, PAPER
        bad = [(m, g, w) for (m, _, _), g, w in zip(rows, got, PAPER) if g != w]
        t3, t13 = '0.%02d' % trunc(rows[0][1], 3, 2), '0.%02d' % trunc(rows[-1][1], 13, 2)
        if (t3, t13) != (i3, i13):
            bad.append(('3/13 (intro)', (t3, t13), (i3, i13)))
        assert any(b > a for a, b in zip(vals, vals[1:])) and vals[-1] < vals[0], 'falls, not monotonically'
        for m, g, w in bad:
            print(f'MISMATCH m={m}: the truncated exact value is {g}, the paper prints {w}')
        if bad:
            sys.exit(1)
        print('gk09_decay: values agree with the paper:', ', '.join(got))

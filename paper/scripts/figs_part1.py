#!/usr/bin/env python3
"""figs_part1.py -- three Part I figures of core.tex, in the visual language of figs_arc.py.

  thmA_design   Theorem A (thm:A): the lattice design U*_4 (a*_4 = 5) at s = 4, q = 29 = 5a*_4 + 4, k = 1
                (N = 29^4).  (a) one elementary-box slab (cells n_3, n_4 fixed) projected to (x_1, x_2): lattice image
                n + r/q, points, jitter, slips of the geometric digit, shortest vectors (I + F_0/q)e_c;  (b) zoom on
                one slip, with the 1/q jitter boxes and the skipped lattice site.
  base23_lift   Bases two and three (thm:base23, def:lift): the b = 3, m = 9 net of the R1 chain for m = 0 mod 3,
                i.e. one deep-shift lift of the m = 6 seed, digitally shifted (variant (i) of thm:base23).
                (a) an elementary slab in z projected to (x, y): nine coarse cells, each a frozen copy of the seed;
                (b) one coarse cell: frozen images, seed copy, points, jitter;  (c) the digits of one point.
  projlines     The middle-digit relation of rem:projlines on the (x_1, x_2) projection of the frame net with the
                design U*_5, s = 5, q = 17, k = 1: (a) a window with the predicted line family; (b) the phases h.x mod 1
                of all N points (Lemma R band) and |S(h)|.

Every net is BUILT here (frame + gauge from the definition, as in as_growth_audit/build.py, or read from the two NET
files part1_b3r0_m{6,9}.net next to this script = the R1 witness chain b3_mod0 replayed by base23_audit/ba_dump), and
every number printed in a caption is ASSERTED: t = 0 by the rank of every composition, the exact relaxation bound of
lem:Ss at k = 1 (Theorem K1), the exact toroidal minimum distance (integer arithmetic, all pairs of neighbouring
cells, which is exhaustive because every pair of points in non-neighbouring cells is at least one cell apart), the
lift structure (tops, frozen block digits), the middle relation and its line family (Lemma R, checked on all N
points).  Self-contained: needs numpy + matplotlib only.

    uv run --with numpy --with matplotlib --with mpmath python scripts/figs_part1.py [--out DIR]   (~2 s)
Output: DIR/{thmA_design,base23_lift,projlines}.{pdf,png} and DIR/part1_captions.tex.
"""
import os
import sys
import math
import time
import itertools
from fractions import Fraction as Fr
from math import comb

import numpy as np
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, Polygon
from matplotlib.lines import Line2D
from matplotlib.collections import LineCollection
import logging
logging.getLogger('fontTools').setLevel(logging.ERROR)

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(HERE), 'figs')
if '--out' in sys.argv:
    OUT = os.path.abspath(sys.argv[sys.argv.index('--out') + 1])
os.makedirs(OUT, exist_ok=True)


def ftr(x, d=3):
    """rev 15.2: exact and computed values are printed truncated (not rounded) to d decimals, as in Section sec:conv
    (round(., 9) first, so that a float just below an exactly representable decimal is not cut one digit low)."""
    v = math.floor(round(float(x) * 10 ** d, 9))
    return f'%.{d}f' % (v / 10 ** d)


def ffloor(x, d=3):
    """certified lower bounds and measured values are printed truncated (not rounded) to d decimals."""
    v = math.floor(float(x) * 10 ** d - 1e-12) / 10 ** d
    return f'%.{d}f' % v


# ------------------------------------------------------------------ visual language (as figs_arc.py)
plt.rcParams.update({
    'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
    'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False,
    'font.size': 7.5, 'axes.titlesize': 7.5, 'axes.labelsize': 7.5, 'legend.fontsize': 6.8,
    'xtick.labelsize': 6.3, 'ytick.labelsize': 6.3, 'axes.linewidth': 0.4,
    'xtick.major.width': 0.3, 'ytick.major.width': 0.3, 'xtick.major.size': 1.5, 'ytick.major.size': 1.5,
    'pdf.fonttype': 42, 'savefig.dpi': 300})
WIDTH = 6.3                     # \textwidth of core.tex
INK = '#111111'                 # points, text
GRID = '#c8c8c8'                # cell grid
FINE = '#e2e2e2'                # sub-grid
LATE = '#6f6f6f'                # lattice-image circles
JIT = '#4a4a4a'                 # jitter segments
ACC = '#2b6cb0'                 # the one accent colour
S_PT, S_LAT = 7.0, 22.0
DASH = (0, (2.4, 1.3))

CHECKS = []


def check(fig, cond, what):
    assert cond, f'[{fig}] FAILED: {what}'
    CHECKS.append((fig, what))


def legend_handles(keys):
    H = {
        'grid': Line2D([], [], color=GRID, lw=0.9, label='cell grid'),
        'lat': Line2D([], [], ls='none', marker='o', ms=4.4, mfc='none', mec=LATE, mew=0.6, label='lattice image'),
        'frz': Line2D([], [], ls='none', marker='o', ms=4.4, mfc='none', mec=LATE, mew=0.6, label='frozen image'),
        'pt': Line2D([], [], ls='none', marker='o', ms=2.7, mfc=INK, mec='none', label='actual point'),
        'jit': Line2D([], [], color=JIT, lw=0.7, label='jitter'),
        'vec': Line2D([], [], color=ACC, lw=1.3, label='shortest lattice vectors'),
        'slip': Line2D([], [], color=ACC, lw=0.9, ls=DASH, label='slip'),
        'skip': Line2D([], [], ls='none', marker='x', ms=4.0, mec=ACC, mew=0.9, label='skipped site'),
        'seed': Line2D([], [], ls='none', marker='+', ms=4.6, mec=ACC, mew=0.8, label='seed point (copy)'),
        'coarse': Line2D([], [], color=INK, lw=0.8, label='top box (top digits)'),
        'line': Line2D([], [], color=ACC, lw=0.8, label='predicted lines'),
    }
    return [H[k] for k in keys]


def grid(ax, x0, x1, y0, y1, step=1.0, color=GRID, lw=0.35, z=0, off=0.0):
    xs = np.arange(np.ceil((x0 - off) / step - 1e-9) * step + off, x1 + 1e-9, step)
    ys = np.arange(np.ceil((y0 - off) / step - 1e-9) * step + off, y1 + 1e-9, step)
    segs = [[(x, y0), (x, y1)] for x in xs] + [[(x0, y), (x1, y)] for y in ys]
    ax.add_collection(LineCollection(segs, colors=color, linewidths=lw, zorder=z))


def draw_points(ax, ideal, actual, s_lat=S_LAT, s_pt=S_PT, jit=True, lat=True, jlw=0.55):
    if jit:
        ax.add_collection(LineCollection(np.stack([ideal, actual], 1), colors=JIT, linewidths=jlw, zorder=4))
    if lat:
        ax.scatter(ideal[:, 0], ideal[:, 1], s=s_lat, facecolors='none', edgecolors=LATE, linewidths=0.55, zorder=3)
    ax.scatter(actual[:, 0], actual[:, 1], s=s_pt, c=INK, lw=0, zorder=5)


def arrow(ax, o, v, col=ACC, lw=1.1, ls='-', ms=7, z=6):
    ax.annotate('', xy=(o[0] + v[0], o[1] + v[1]), xytext=(o[0], o[1]),
                arrowprops=dict(arrowstyle='-|>', color=col, lw=lw, ls=ls, mutation_scale=ms, shrinkA=0, shrinkB=0),
                zorder=z)


def label(ax, x, y, s, col=ACC, fs=7.0, ha='center', va='center', z=7, bg=True):
    ax.text(x, y, s, color=col, fontsize=fs, ha=ha, va=va, zorder=z,
            bbox=dict(fc='white', ec='none', pad=0.4, alpha=0.9) if bg else None)


def panel_title(ax, s):
    ax.set_title(s, fontsize=7.5, pad=3)


def clean(ax, lim, ticks=False):
    ax.set_aspect('equal')
    ax.set_xlim(*lim[0]); ax.set_ylim(*lim[1])
    for sp in ax.spines.values():
        sp.set_color('#9a9a9a')
    if not ticks:
        ax.set_xticks([]); ax.set_yticks([])
    else:
        ax.tick_params(length=1.5, pad=1)


def save(fig, name):
    fig.savefig(os.path.join(OUT, name + '.pdf'), metadata={'CreationDate': None, 'ModDate': None})
    fig.savefig(os.path.join(OUT, name + '.png'), dpi=220)
    plt.close(fig)


# ------------------------------------------------------------------ linear algebra over F_p
def rank_mod(A, p):
    A = [[int(x) % p for x in r] for r in A]
    rk, ncol = 0, len(A[0]) if A else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(A)) if A[i][c]), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        iv = pow(A[rk][c], -1, p)
        A[rk] = [x * iv % p for x in A[rk]]
        for i in range(len(A)):
            if i != rk and A[i][c]:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk


def left_kernel_mod(rows, p):
    """basis of {kappa : sum_i kappa_i rows_i = 0} over F_p."""
    n, m = len(rows), len(rows[0])
    A = [[int(rows[i][j]) % p for i in range(n)] for j in range(m)]          # m x n, kernel of A
    piv, r = [], 0
    for c in range(n):
        pr = next((i for i in range(r, m) if A[i][c]), None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        iv = pow(A[r][c], -1, p)
        A[r] = [x * iv % p for x in A[r]]
        for i in range(m):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    free = [c for c in range(n) if c not in piv]
    out = []
    for f in free:
        v = [0] * n; v[f] = 1
        for i, c in enumerate(piv):
            v[c] = (-A[i][f]) % p
        out.append(v)
    return out


def t0_check(C, p):
    """t = 0 <=> for every composition (d_1..d_s) of m the top d_c rows of the C_c are independent over F_p
    (Niederreiter; row 0 = most significant digit).  Returns (ok, number of compositions)."""
    s, m = len(C), len(C[0])
    n = 0
    for cut in itertools.combinations(range(m + s - 1), s - 1):
        d, prev = [], -1
        for x in cut + (m + s - 1,):
            d.append(x - prev - 1); prev = x
        rows = [C[c][r] for c in range(s) for r in range(d[c])]
        n += 1
        if rank_mod(rows, p) < m:
            return False, n
    return True, n


# ------------------------------------------------------------------ frame + gauge builder (def:Ns), exact over Q
# Independent re-statement of as_growth_audit/build.py: frame readings (Taylor jets at finite places, reversed
# coefficients at infinity), (k..k) box inverse -> graph form, column gauge U_d solved exactly over Q with row
# scalars lambda_c = lambda'_c Q_c^{-k}; row 0 of the offset part = the design (F_0, ..., F_{L-1}).
def frame_matrix(a, m):
    if a is None:
        return [[Fr(int(i == m - 1 - j)) for i in range(m)] for j in range(m)]
    return [[Fr(comb(i, j)) * a ** (i - j) if i >= j else Fr(0) for i in range(m)] for j in range(m)]


def mat_inv_Q(A):
    n = len(A)
    M = [row[:] + [Fr(int(i == j)) for j in range(n)] for i, row in enumerate(A)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return [row[n:] for row in M]


def matmul_Q(A, B):
    return [[sum(A[i][t] * B[t][j] for t in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def solve_Q(A, b):
    r, n = len(A), len(A[0])
    M = [A[i][:] + [b[i]] for i in range(r)]
    pc, row = [], 0
    for col in range(n):
        p = next((i for i in range(row, r) if M[i][col] != 0), None)
        if p is None:
            continue
        M[row], M[p] = M[p], M[row]
        pv = M[row][col]; M[row] = [x / pv for x in M[row]]
        for i in range(r):
            if i != row and M[i][col] != 0:
                f = M[i][col]; M[i] = [a - f * bb for a, bb in zip(M[i], M[row])]
        pc.append(col); row += 1
    assert all(M[i][n] == 0 for i in range(row, r)), 'gauge system inconsistent'
    assert len(pc) == n
    x = [Fr(0)] * n
    for i, col in enumerate(pc):
        x[col] = M[i][n]
    return x


def frame_net(F, k, q):
    """generator matrices (mod q) of P^F_{k,q} (def:Ns) for places (inf, 0, 1, ..., s-2), lambda' = 1."""
    s = len(F[0]); m = s * k; L = len(F)
    places = [None] + [Fr(c) for c in range(s - 1)]
    C = [frame_matrix(a, m) for a in places]
    B = []
    for c in range(s):
        B += C[c][:k]
    G = [matmul_Q(Cc, mat_inv_Q(B)) for Cc in C]
    for c in range(s):
        for r in range(k):
            assert all(G[c][r][col] == (1 if col == c * k + r else 0) for col in range(m))
    PhiF = {(c, d): [row[d * k:(d + 1) * k] for row in G[c][k:]] for c in range(s) for d in range(s)}
    Q = []
    for c in range(s):
        if places[c] is None:
            Q.append(Fr(1))
        else:
            v = Fr(1)
            for b in range(s):
                if b != c and places[b] is not None:
                    v *= places[c] - places[b]
            Q.append(v)
    lamk = [1 / Q[c] ** k for c in range(s)]
    Phi = {}
    for d in range(s):
        rows = [c for c in range(s) if c != d]
        A = [[lamk[c] * PhiF[(c, d)][0][k - 1 - n] for n in range(k)] for c in rows]
        U = [[Fr(0)] * k for _ in range(k)]
        for n in range(k):
            tgt = [Fr(F[n][c][d]) if n < L else Fr(0) for c in rows]
            if n <= s - 2:
                x = solve_Q([[A[i][t] for t in range(n + 1)] for i in range(len(rows))], tgt)
                for t in range(n + 1):
                    U[t][n] = x[t]
            else:
                x = solve_Q([[A[i][t] for t in range(s - 1)] for i in range(len(rows))], [-A[i][n] for i in range(len(rows))])
                for t in range(s - 1):
                    U[t][n] = x[t]
                U[n][n] = Fr(1)
        Ul = [[U[k - 1 - i][k - 1 - j] for j in range(k)] for i in range(k)]
        for c in rows:
            blk = matmul_Q(PhiF[(c, d)], Ul)
            blk[0] = [lamk[c] * x for x in blk[0]]
            Phi[(c, d)] = blk
    for c in range(s):
        blk = [[Fr(0)] * k for _ in range(m - k)]
        for n in range(min(L, k)):
            blk[0][k - 1 - n] = Fr(F[n][c][c])
        Phi[(c, c)] = blk
    for c in range(s):
        for d in range(s):
            for j in range(k):
                n = k - 1 - j
                assert Phi[(c, d)][0][j] == (F[n][c][d] if n < L else 0)
    mats = []
    for c in range(s):
        Cm = [[0] * m for _ in range(m)]
        for r in range(k):
            Cm[r][c * k + r] = 1
        for r in range(m - k):
            for d in range(s):
                for j in range(k):
                    x = Phi[(c, d)][r][j]
                    assert x.denominator % q != 0
                    Cm[k + r][d * k + j] = (x.numerator * pow(x.denominator, -1, q)) % q
        mats.append(Cm)
    return mats


# The pinned design U*_s of Theorem A (as_push/ustar_det.py, the research notes Sec. 6.1, confirmed AS_PUSH_AUDIT Sec. 8):
# places (inf, 0, ..., s-2), lambda' = 1; F[n][c][d] = level n of the design, diagonal of F_0 = -alpha_c.
USTAR = {
    4: [[[-5, 2, 1, 2], [1, -3, -1, -1], [1, 2, -5, -2], [1, 1, 1, -3]],
        [[0, -3, -1, -1], [-2, 0, 2, 1], [-1, -1, 0, 3], [0, -1, 0, 0]],
        [[0, 2, 0, -1], [2, 0, -2, 0], [0, -1, 0, -2], [-1, 0, -1, 0]]],
    5: [[[-16, 6, 2, 2, 6], [1, -8, -2, -1, -2], [1, 6, -12, -2, -3], [1, 3, 2, -12, -6], [1, 2, 1, 2, -7]],
        [[0, -11, -3, -1, -1], [-3, 0, 5, 1, 1], [-2, -5, 0, 3, 2], [-1, -4, -1, 0, 7], [0, -3, -1, 1, 0]],
        [[0, 6, 0, -2, -4], [2, 0, -3, 0, 1], [0, 1, 0, -3, 1], [-1, 1, 1, 0, -3], [-1, 1, 0, -3, 0]],
        [[0, -1, 1, 1, -1], [-1, 0, 1, 0, 0], [1, -1, 0, 2, 0], [1, 0, -2, 0, 3], [0, 0, 0, 1, 0]]],
    7: [[[-170, 60, 12, 6, 6, 12, 60], [1, -52, -12, -3, -2, -3, -12], [1, 60, -117, -6, -3, -4, -15],     # F_0 only
         [1, 30, 12, -86, -6, -6, -20], [1, 20, 6, 6, -86, -12, -30], [1, 15, 4, 3, 6, -116, -60],
         [1, 12, 3, 2, 3, 12, -51]]],
}
ASTAR = {4: 5, 5: 16, 7: 170}


def check_ustar_against_repo():
    """optional provenance check against the repository copy (skipped when this folder is used stand-alone)."""
    import json
    p = os.path.join(HERE, '..', '..', 'as_push', 'ustar_det_designs.json')
    if not os.path.exists(p):
        return False
    D = json.load(open(p))
    for s in (4, 5, 7):
        L = len(USTAR[s])
        assert D[str(s)]['F'][:L] == USTAR[s] and D[str(s)]['a'] == ASTAR[s], s
    return True


def ustar_alpha(s):
    return [-USTAR[s][0][c][c] for c in range(s)]


# ------------------------------------------------------------------ the relaxation of lem:Ss at k = 1 (Theorem K1)
def lb_k1(F0, q):
    """min over e in {-1,0,1}^s \\ 0 of sum_i b_i^2 (integer), with sigma = F_0 e, delta_i = sigma_i mod q,
    jit_i = 0 for the own coordinate of a single-axis step and 1 otherwise, and
    b_i = max(0, min(|e_i q + delta_i|, |e_i q + delta_i - q|) - jit_i)   (delta_i = 0: b_i = max(0, |e_i| q - jit_i)).
    LB_1(q) = min(1, sqrt(min)/q).  Returns (min, argmin e)."""
    s = len(F0)
    best, arg = None, None
    for e in itertools.product((-1, 0, 1), repeat=s):
        if not any(e):
            continue
        W = [i for i in range(s) if e[i]]
        tot = 0
        for i in range(s):
            sg = sum(e[d] * F0[i][d] for d in range(s))
            dl = sg % q
            jit = 0 if (len(W) == 1 and W[0] == i) else 1
            if dl == 0:
                b = max(0, abs(e[i] * q) - jit)
            else:
                b = max(0, min(abs(e[i] * q + dl) - jit, abs(e[i] * q + dl - q) - jit))
            tot += b * b
        if best is None or tot < best:
            best, arg = tot, e
    return best, arg


# ------------------------------------------------------------------ k = 1 nets: points by cell
def k1_points(C, q, cells):
    """k = 1, graph form: row 0 of C_c is e_c, so the index is the cell vector n.  Returns the digit array
    D (n_pts, s, m) and the integer coordinates X (units q^{-m}, cell n_c = X // q^{m-1})."""
    Cn = np.array(C, dtype=np.int64)                         # (s, m, m)
    s, m = Cn.shape[0], Cn.shape[1]
    D = np.einsum('crj,nj->ncr', Cn, cells) % q
    w = q ** np.arange(m - 1, -1, -1, dtype=np.int64)
    X = (D * w).sum(-1)
    return D, X


def k1_min_dist(C, q):
    """exact toroidal minimum distance of a k = 1 net (N = q^s), in integer units q^{-2m} (squared).
    Every pair whose cells differ by >= 2 in some coordinate (toroidally) is >= 1 cell apart; so if the minimum over
    neighbouring cells is < 1 cell it is the global minimum (asserted).  Returns (d2, e*, #pairs at the minimum)."""
    s = len(C); m = s
    Q = q ** m
    g = np.stack(np.meshgrid(*(np.arange(q),) * s, indexing='ij'), -1).reshape(-1, s)
    _, X = k1_points(C, q, g)
    X = X.reshape((q,) * s + (s,))
    best, arg, cnt = None, None, 0
    for e in itertools.product((-1, 0, 1), repeat=s):
        if not any(e) or next(x for x in e if x) < 0:          # e and -e give the same pairs
            continue
        Y = np.roll(X, shift=tuple(-x for x in e), axis=tuple(range(s)))
        dd = np.abs(Y - X) % Q
        dd = np.minimum(dd, Q - dd)
        d2 = (dd * dd).sum(-1)
        v = int(d2.min())
        if best is None or v < best:
            best, arg, cnt = v, e, int((d2 == v).sum())
        elif v == best:
            cnt += int((d2 == v).sum())
    unit = q ** (m - 1)                                        # one cell, in units q^{-m}
    assert best < unit * unit, 'minimum not below one cell: neighbour scan would not be exhaustive'
    return best, arg, cnt


# ================================================================== fig:thmA
def fig_thmA():
    s, q, k = 4, 29, 1
    a = ASTAR[s]
    F = USTAR[s]
    F0 = np.array(F[0])
    alpha = ustar_alpha(s)
    check('thmA', max(alpha) == a and q == 5 * a + 4, f'U*_4: a*_4 = max alpha = {a}; q = 5a*_4+4 = {q} (threshold of thm:A)')
    t = time.time()
    C = frame_net(F, k, q)
    ok, nb = t0_check(C, q)
    check('thmA', ok, f'P^(U*_4)_(1,{q}) is a (0,{s},{s})-net over F_{q}: all {nb} compositions full rank')
    Cn = np.array(C)
    check('thmA', all(np.array_equal(Cn[c][1], F0[c] % q) for c in range(s)),
          'graph form: row 1 (geometric digit) of C_c = row c of F_0 mod q, i.e. r = F_0 n mod q (H1_1)')
    check('thmA', all(Cn[c][r][c] == 0 for c in range(s) for r in range(2, s)),
          'deeper rows vanish in their own column (H2)')
    # --- proved bound: the relaxation of lem:Ss at k = 1 (Theorem K1)
    mb, eb = lb_k1(F0.tolist(), q)
    LB = Fr(1) if mb >= q * q else None
    LBf = min(1.0, math.sqrt(mb) / q)
    r_ = math.isqrt(mb)
    check('thmA', r_ * r_ == mb and Fr(r_, q) == Fr(q - a, q),
          f'LB_1({q}) = sqrt({mb})/{q} = {r_}/{q} (exact relaxation; argmin e = {eb}); equals 1 - a*_4/q here')
    # --- measured: exact toroidal min distance
    d2, emin, npair = k1_min_dist(C, q)
    cm = math.sqrt(d2) / q ** (s - 1)
    check('thmA', cm >= LBf, f'measured c = sqrt({d2})/{q}^3 = {cm:.6f} >= LB = {LBf:.6f} (exact, {npair} minimal pairs, step e = {emin})')
    # --- lattice (I + F_0/q) Z^4: shortest vectors
    L = np.eye(s) + F0 / q
    V = np.array([v for v in itertools.product(range(-2, 3), repeat=s) if any(v)])
    ln = np.linalg.norm(V @ L.T, axis=1)
    lam1 = ln.min()
    sv = [tuple(V[i]) for i in np.where(ln < lam1 + 1e-12)[0]]
    check('thmA', all(sum(map(abs, v)) == 1 for v in sv), f'shortest vectors of (I+F_0/q)Z^4 (|v|_inf<=2) are +-{sorted(set(tuple(abs(x) for x in v) for v in sv))}, lambda_1 = {lam1:.5f}')
    lam = np.linalg.norm(L, axis=0)
    # --- the drawn slab: cells (n1, n2) in a window, (n3, n4) fixed
    W = 15
    x0, y0, n3, n4 = 4, 7, 11, 20
    cells = np.array([(x, y, n3, n4) for x in range(x0, x0 + W) for y in range(y0, y0 + W)], dtype=np.int64)
    D, X = k1_points(C, q, cells)
    unit = q ** (s - 1)
    Xc = X / unit                                              # cell units
    check('thmA', np.all(X // unit == cells), 'every drawn point lies in its cell (one point per cell of the slab)')
    r = D[:, :, 1]
    check('thmA', np.all(r == (cells @ F0.T) % q), 'geometric digit r = F_0 n mod q on the drawn cells')
    ideal = cells + r / q
    jit = Xc - ideal
    check('thmA', np.all((jit >= 0) & (jit < 1 / q)), 'jitter (digits 3, 4) lies in [0, 1/q)^4')
    # slips: neighbour steps whose projected (x1, x2) step deviates from L e
    idx = {tuple(c[:2]): i for i, c in enumerate(cells)}
    segs, pairs = [], set()
    for i, c in enumerate(cells):
        for ax_ in (0, 1):
            nb_ = (c[0] + (ax_ == 0), c[1] + (ax_ == 1))
            if nb_ not in idx:
                continue
            e = np.zeros(s); e[ax_] = 1
            dv = ideal[idx[nb_]] - ideal[i] - L @ e
            if np.abs(dv[:2]).max() > 0.5:
                pairs.add((i, idx[nb_]))
                segs.append([(c[0] + 1, c[1]), (c[0] + 1, c[1] + 1)] if ax_ == 0 else [(c[0], c[1] + 1), (c[0] + 1, c[1] + 1)])
    # every slip is a wrap of r_1 or r_2 (a jump of exactly one cell in x_1 or x_2)
    for i, j in pairs:
        dv = ideal[j] - ideal[i] - L @ (np.eye(s)[0] if cells[j][0] != cells[i][0] else np.eye(s)[1])
        assert np.allclose(np.abs(dv[:2]), np.round(np.abs(dv[:2]))) and np.abs(np.round(dv[:2])).sum() >= 1
    check('thmA', len(segs) > 0, f'{len(segs)} slip edges in the window (wraps of r_1 or r_2 by one cell)')
    # skipped sites of the projected lattice continuation (as in figs_arc.skipped_sites)
    L2 = L[:2, :2]
    sk = []
    for i, c in enumerate(cells):
        for ax_ in (0, 1):
            for sg in (1, -1):
                nb_ = (c[0] + sg * (ax_ == 0), c[1] + sg * (ax_ == 1))
                if nb_ not in idx:
                    continue
                e2 = np.zeros(2); e2[ax_] = sg
                pnt = ideal[i, :2] + L2 @ e2
                if np.abs(ideal[idx[nb_], :2] - pnt).max() <= 0.5:
                    continue
                if np.all(pnt >= [x0, y0]) and np.all(pnt < [x0 + W, y0 + W]) and \
                        np.min(np.linalg.norm(ideal[:, :2] - pnt, axis=1)) > 0.4 and \
                        not any(np.linalg.norm(pnt - x_) < 0.4 for x_ in sk):
                    sk.append(pnt)
    sk = np.array(sk).reshape(-1, 2)
    # anchor for the arrows: a cell whose +e1 and +e2 steps are exact lattice steps (in all four coordinates)
    best = None
    for i, c in enumerate(cells):
        okk = True
        for ax_ in (0, 1):
            nb_ = (c[0] + (ax_ == 0), c[1] + (ax_ == 1))
            if nb_ not in idx:
                okk = False; break
            e = np.zeros(s); e[ax_] = 1
            okk = okk and np.abs(ideal[idx[nb_]] - ideal[i] - L @ e).max() < 1e-9
        if okk:
            dd = (c[0] - (x0 + 4)) ** 2 + (c[1] - (y0 + 9)) ** 2
            if best is None or dd < best[0]:
                best = (dd, i)
    i0 = best[1]
    # zoom: a slip in x (wrap of r_1) away from the anchor
    zcands = [(i, j) for (i, j) in pairs if cells[j][0] != cells[i][0]]
    zi, zj = min(zcands, key=lambda p: abs(cells[p[0]][0] - (x0 + 9)) + abs(cells[p[0]][1] - (y0 + 3)))
    # the lattice continuation of zi in direction e_1 = the skipped site
    cont = ideal[zi] + L @ np.eye(s)[0]
    step_sl = np.linalg.norm(Xc[zj] - Xc[zi])
    step_ok = np.linalg.norm(L @ np.eye(s)[0])
    dz = ideal[zj] - cont
    check('thmA', np.allclose(dz, np.round(dz)) and np.allclose(dz[:2], [1, 0]) and abs(step_sl - np.linalg.norm(cont[:2] + [1, 0] - ideal[zi, :2])) < 2 / q,
          f'zoomed slip: r_1 wraps, the neighbour sits one cell beyond the continued lattice site; step {step_sl:.3f} vs lattice {step_ok:.3f}')

    # ------------------------------------------------ figure
    fig = plt.figure(figsize=(WIDTH, 3.35))
    axa = fig.add_axes([0.02, 0.10, 0.50, 0.81])
    axb = fig.add_axes([0.56, 0.42, 0.42, 0.47])
    lim = ((x0 - 0.05, x0 + W + 0.05), (y0 - 0.05, y0 + W + 0.05))
    grid(axa, x0, x0 + W, y0, y0 + W)
    axa.add_collection(LineCollection(segs, colors=ACC, linewidths=0.8, linestyles=[DASH], zorder=2))
    draw_points(axa, ideal[:, :2], Xc[:, :2])
    axa.scatter(sk[:, 0], sk[:, 1], marker='x', s=13, c=ACC, linewidths=0.9, zorder=6)
    o = ideal[i0, :2]
    for ax_ in (0, 1):
        arrow(axa, o, L[:2, ax_], lw=1.2)
    label(axa, o[0] + L[0, 0] + 0.1, o[1] + L[1, 0] - 0.45, r'$(I+\frac{F_0}{q})e_1$', fs=6.2, ha='left')
    label(axa, o[0] + L[0, 1] - 0.1, o[1] + L[1, 1] + 0.15, r'$(I+\frac{F_0}{q})e_2$', fs=6.2, ha='right')
    zc = cells[zi][:2]
    bx0, by0, bw, bh = zc[0] - 1.0, zc[1] - 0.0, 3.0, 2.0
    axa.add_patch(Rectangle((bx0, by0), bw, bh, fc='none', ec=INK, lw=0.6, ls=(0, (1, 1)), zorder=8))
    label(axa, bx0 + 0.05, by0 + bh + 0.05, '(b)', col=INK, fs=6.5, ha='left', va='bottom')
    clean(axa, lim)
    panel_title(axa, r'(a) $\mathcal{U}^*_4$, $q=%d$, $k=1$: slab $(n_3,n_4)=(%d,%d)$, $(x_1,x_2)$' % (q, n3, n4))
    # (b) zoom on the slip
    zl = ((bx0, bx0 + bw), (by0, by0 + bh))
    sel = np.where((cells[:, 0] >= bx0) & (cells[:, 0] < bx0 + bw) & (cells[:, 1] >= by0) & (cells[:, 1] < by0 + bh))[0]
    grid(axb, *zl[0], *zl[1], lw=0.5)
    for i in sel:
        axb.add_patch(Rectangle(ideal[i, :2], 1 / q, 1 / q, fc='#cfcfcf', ec=INK, lw=0.35, zorder=4.5))
    sg_ = [sgm for sgm in segs if all(bx0 - 1e-9 <= p_[0] <= bx0 + bw + 1e-9 and by0 - 1e-9 <= p_[1] <= by0 + bh + 1e-9
                                      for p_ in sgm)]
    axb.add_collection(LineCollection(sg_, colors=ACC, linewidths=1.0, linestyles=[DASH], zorder=2))
    draw_points(axb, ideal[sel, :2], Xc[sel, :2], s_lat=26, s_pt=3.5, jit=False)
    arrow(axb, ideal[zi, :2], L[:2, 0], lw=1.3, ms=8)
    axb.scatter([cont[0]], [cont[1]], marker='x', s=30, c=ACC, linewidths=1.1, zorder=6)
    yb = Xc[zi, 1] - 0.11
    arrow(axb, [Xc[zi, 0], yb], [Xc[zj, 0] - Xc[zi, 0], Xc[zj, 1] - Xc[zi, 1]], col=INK, lw=0.6, ms=5, z=7)
    label(axb, ideal[zi, 0] + 0.38, ideal[zi, 1] + 0.2, r'$|(I+\frac{F_0}{q})e_1|=%s$' % ftr(step_ok, 3), fs=6.3)
    label(axb, (Xc[zi, 0] + Xc[zj, 0]) / 2, yb - 0.04, r'step across the slip: $%s$' % ftr(step_sl, 3), col=INK, fs=6.3, va='top')
    label(axb, cont[0] + 0.1, cont[1] + 0.1, 'skipped site', fs=6.0, ha='left', va='bottom')
    clean(axb, zl)
    panel_title(axb, r'(b) a slip of $r_1$; grey squares: jitter boxes (side $1/q$)')
    txt = (r'proved (Lemma lem:Ss at $k=1$):' + '\n' +
           r'$\delta N^{1/4}\geq\mathrm{LB}=%d/%d=%s$' % (r_, q, ffloor(LBf, 4)) + '\n' +
           r'measured: $c=%s$,  $\lambda_1=%s$' % (ffloor(cm, 4), ffloor(lam1, 4)))
    fig.text(0.60, 0.33, txt.replace('Lemma lem:Ss', 'relaxation'), fontsize=6.6, ha='left', va='top', linespacing=1.45,
             bbox=dict(fc='white', ec='#b0b0b0', lw=0.4, pad=2.5))
    fig.legend(handles=legend_handles(['grid', 'lat', 'pt', 'jit', 'vec', 'slip', 'skip']), loc='lower center', ncol=7,
               frameon=False, bbox_to_anchor=(0.5, 0.0), handlelength=1.6, columnspacing=1.0, handletextpad=0.4, fontsize=6.4)
    save(fig, 'thmA_design')
    return dict(q=q, s=s, a=a, N=q ** s, nbox=nb, mb=mb, r=r_, LB=LBf, eb=eb, d2=d2, c=cm, emin=emin, npair=npair,
                lam1=lam1, W=W, x0=x0, y0=y0, n3=n3, n4=n4, nslip=len(segs), nskip=len(sk), step_sl=step_sl,
                step_ok=step_ok, t=time.time() - t)


# ================================================================== fig:base23
def read_net(path):
    t = open(path).read().split()
    assert t[0] == 'NET'
    b, M = int(t[1]), int(t[2])
    vals = list(map(int, t[3:]))
    gens = [vals[i * 3 * M:(i + 1) * 3 * M] for i in range(M)]
    shift = vals[M * 3 * M:M * 3 * M + 3 * M]
    assert len(shift) == 3 * M
    return b, M, np.array(gens, dtype=np.int64), np.array(shift, dtype=np.int64)


def net_digits(b, M, gens, shift):
    """all b^M points: digits (N, 3, M), MSB first (point = shift + sum_i n_i gen_i, digitwise mod b)."""
    N = b ** M
    n = np.arange(N, dtype=np.int64)
    idx = np.stack([(n // b ** i) % b for i in range(M)], 1)
    dg = (idx @ gens + shift) % b
    return dg.reshape(N, 3, M)


def to_int(dg, b):
    M = dg.shape[-1]
    w = b ** np.arange(M - 1, -1, -1, dtype=np.int64)
    return (dg * w).sum(-1)


def min_dist_3d(Xi, b, M, cell_depth):
    """exact toroidal min distance of a (0,M,3)-net with integer coordinates Xi (units b^-M): every elementary box with
    cell_depth digits per coordinate (3*cell_depth <= M) holds b^(M-3 cell_depth) points; pairs in non-neighbouring
    boxes are >= one box side apart, so the min over neighbouring boxes (incl. the same box) is exact when it is
    below one box side (asserted)."""
    Q = b ** M
    G = b ** cell_depth
    side = b ** (M - cell_depth)
    cell = Xi // side
    key = (cell[:, 0] * G + cell[:, 1]) * G + cell[:, 2]
    order = np.argsort(key, kind='stable')
    per = len(Xi) // G ** 3
    assert np.all(np.bincount(key, minlength=G ** 3) == per)
    P = Xi[order].reshape(G, G, G, per, 3)
    best, cnt = None, 0
    offs = [e for e in itertools.product((-1, 0, 1), repeat=3) if any(e) and next(x for x in e if x) > 0] + [(0, 0, 0)]
    for e in offs:
        Y = np.roll(P, shift=tuple(-x for x in e), axis=(0, 1, 2))
        dd = np.abs(Y[:, :, :, None, :, :] - P[:, :, :, :, None, :]) % Q
        dd = np.minimum(dd, Q - dd)
        d2 = (dd * dd).sum(-1)
        if e == (0, 0, 0):
            ii = np.arange(per)
            d2[..., ii, ii] = np.iinfo(np.int64).max
        v = int(d2.min())
        c_ = int((d2 == v).sum()) // (2 if e == (0, 0, 0) else 1)
        if best is None or v < best:
            best, cnt = v, c_
        elif v == best:
            cnt += c_
    assert best < side * side
    return best, cnt


def fig_base23():
    b = 3
    _, M0, g0, s0 = read_net(os.path.join(HERE, 'part1_b3r0_m6.net'))
    _, M, g, sh = read_net(os.path.join(HERE, 'part1_b3r0_m9.net'))
    check('base23', (M0, M) == (6, 9), 'seed m = 6, one lift to m = 9 (R1 chain b = 3, m = 0 mod 3)')
    Dpar = M0 // 2                                             # frozen block depth floor(M0/2) = D
    # generator matrices C_c (rows = output digits) and t = 0
    for nm, MM, gg in (('seed', M0, g0), ('lift', M, g)):
        Cm = [[[int(gg[i][c * MM + d]) for i in range(MM)] for d in range(MM)] for c in range(3)]
        ok, nb = t0_check(Cm, b)
        check('base23', ok, f'{nm} (m={MM}) is a digital (0,{MM},3)-net over F_3 (shifted): all {nb} compositions full rank')
    # structure of the lift (def:lift): first M0 generators = seed generators embedded at block digits 1..M0,
    # shift = seed shift embedded; the three new generators move the top digits by a unitriangular map
    emb = np.zeros((M0, 3 * M), dtype=np.int64)
    for c in range(3):
        emb[:, c * M + 1:c * M + 1 + M0] = g0[:, c * M0:(c + 1) * M0]
    check('base23', np.array_equal(g[:M0], emb), 'generators 1..6 of the lift = seed generators embedded in the block digits')
    se = np.zeros(3 * M, dtype=np.int64)
    for c in range(3):
        se[c * M + 1:c * M + 1 + M0] = s0[c * M0:(c + 1) * M0]
    check('base23', np.array_equal(sh, se), 'digital shift of the lift = seed shift embedded (depth-9 shift sigma_9)')
    T = np.array([[g[M0 + i][c * M] for c in range(3)] for i in range(3)])
    check('base23', T.tolist() == [[1, 1, 1], [0, 1, 1], [0, 0, 1]], 'tops (a, a+d1, a+d1+d2): unitriangular in (a, d1, d2)')
    Jx = np.array([[g[M0 + i][c * M + M - 2], g[M0 + i][c * M + M - 1]] for i in range(3) for c in range(3)]).reshape(3, 3, 2)
    check('base23', np.all(Jx[0] == 0) and all(rank_mod(Jx[1:, c, :].tolist(), b) == 2 for c in range(3)),
          'the two deepest digits of each coordinate are a bijection of (d1, d2) (jitter), independent of a')
    check('base23', np.all(g[:M0, [c * M + M - 2 for c in range(3)] + [c * M + M - 1 for c in range(3)]] == 0) and
          np.all(sh[[c * M + M - 2 for c in range(3)] + [c * M + M - 1 for c in range(3)]] == 0),
          'seed generators and shift do not touch the jitter digits')
    # points
    P0 = net_digits(b, M0, g0, s0)
    P = net_digits(b, M, g, sh)
    N = b ** M
    Xi = to_int(P, b)
    check('base23', len(set(map(tuple, Xi))) == N, f'{N} distinct points')
    # freezing: in every coarse cell (top digits) the top D block digits are exactly the seed's top-D triples
    seedfrz = sorted(map(tuple, P0[:, :, :Dpar].reshape(len(P0), -1)))
    tops = P[:, :, 0]
    tkey = (tops[:, 0] * 3 + tops[:, 1]) * 3 + tops[:, 2]
    ncells = 0
    for tk in np.unique(tkey):
        blk = P[tkey == tk][:, :, 1:1 + Dpar].reshape(-1, 3 * Dpar)
        assert sorted(map(tuple, blk)) == seedfrz, tk
        ncells += 1
    check('base23', ncells == 27, f'freezing: each of the 27 coarse cells holds a copy of the seed whose top {Dpar} '
                                  f'block digits are exactly the seed\'s (BASE23_AUDIT Lemma C)')
    # exact toroidal minimum distance
    d2, npair = min_dist_3d(Xi, b, M, 3)
    cm = math.sqrt(d2) / b ** (2 * M // 3)                    # c = sqrt(d2) b^{-M} N^{1/3}
    d20, _ = min_dist_3d(to_int(P0, b), b, M0, 2)
    cm0 = math.sqrt(d20) / b ** (2 * M0 // 3)
    FLOOR_RES0, FLOOR_B3 = 0.4699, 0.3538
    check('base23', abs(cm - 0.529139) < 1e-6 and abs(cm0 - 0.55624) < 1e-5,
          f'exact toroidal c: m=6 seed {cm0:.5f}, m=9 lift {cm:.6f} = sqrt({d2})/3^6 (matches BASE23_AUDIT/R1 tables)')
    check('base23', cm >= FLOOR_RES0 >= FLOOR_B3, f'c(m=9) = {cm:.4f} >= {FLOOR_RES0} (thm:base23(i), b=3, m=0 mod 3) >= {FLOOR_B3}')
    # ---- the drawn slab: z in an elementary interval of length 3^-3 (z digits 1..3 fixed)
    zfix = (1, 0, 2)
    sl = np.all(P[:, 2, :3] == zfix, axis=1)
    Ps = P[sl]
    check('base23', len(Ps) == 729, 'slab z in [z0, z0 + 3^-3): 729 points, one in each of the 27 x 27 boxes of side 3^-3')
    xy = to_int(Ps[:, :2, :], b) / b ** M                      # unit square
    frz = to_int(Ps[:, :2, :1 + Dpar], b) / b ** (1 + Dpar)    # frozen image: top digit + D frozen block digits
    eps = xy - frz
    check('base23', np.all((eps >= 0) & (eps < b ** -(1 + Dpar))), f'jitter (all digits below the frozen ones) in [0, 3^-{1 + Dpar})')
    # each coarse cell of the slab: the same frozen pattern (a copy of the seed's slab)
    ccell = Ps[:, :2, 0]
    pats = {}
    for cx in range(3):
        for cy in range(3):
            mk = (ccell[:, 0] == cx) & (ccell[:, 1] == cy)
            pats[(cx, cy)] = sorted(map(tuple, np.round((frz[mk] - [cx / 3, cy / 3]) * 81).astype(int)))
    check('base23', len({tuple(v) for v in pats.values()}) == 1 and len(pats[(0, 0)]) == 81,
          'the nine coarse cells of the slab carry the same 81-point frozen pattern (translates)')
    # the seed copy in a coarse cell: seed points with the slab's frozen z digits, scaled by 1/3
    zc_top = zfix[0]
    s_sel = np.all(P0[:, 2, :2] == zfix[1:], axis=1)
    seed_xy = to_int(P0[s_sel][:, :2, :], b) / b ** M0
    zoom = (1, 2)
    zsel = (ccell[:, 0] == zoom[0]) & (ccell[:, 1] == zoom[1])
    seed_in = (seed_xy + np.array(zoom)) / 3
    # every lifted point shares its frozen box with exactly one seed-copy point
    fb_l = sorted(map(tuple, np.floor(xy[zsel] * 81 + 1e-9).astype(int)))
    fb_s = sorted(map(tuple, np.floor(seed_in * 81 + 1e-9).astype(int)))
    check('base23', fb_l == fb_s, 'in the zoomed coarse cell each point lies in the frozen box (side 3^-4) of one seed-copy point')
    # tops of the zoomed cell -> (a, d1, d2)
    a_ = zoom[0]; d1 = (zoom[1] - a_) % 3; d2_ = (zc_top - a_ - d1) % 3
    # one point for the digit strip
    ip = np.where(zsel)[0][np.argmin(np.linalg.norm(xy[zsel] - (np.array(zoom) + [0.52, 0.5]) / 3, axis=1))]
    pd = Ps[ip]

    # ------------------------------------------------ figure
    fig = plt.figure(figsize=(WIDTH, 3.25))
    axa = fig.add_axes([0.012, 0.115, 0.355, 0.775])
    axb = fig.add_axes([0.385, 0.115, 0.355, 0.775])
    axc = fig.add_axes([0.775, 0.27, 0.215, 0.58])
    # (a)
    grid(axa, 0, 1, 0, 1, step=1 / 27, color=FINE, lw=0.25, z=0)
    grid(axa, 0, 1, 0, 1, step=1 / 3, color=INK, lw=0.7, z=1)
    axa.scatter(xy[:, 0], xy[:, 1], s=2.2, c=INK, lw=0, zorder=5)
    axa.add_patch(Rectangle((zoom[0] / 3, zoom[1] / 3), 1 / 3, 1 / 3, fc='none', ec=ACC, lw=1.0, ls=(0, (2, 1.2)), zorder=6))
    label(axa, zoom[0] / 3 + 0.012, zoom[1] / 3 + 1 / 3 - 0.012, '(b)', col=ACC, fs=6.5, ha='left', va='top')
    clean(axa, ((-0.003, 1.003), (-0.003, 1.003)))
    panel_title(axa, r'(a) $b=3$, $m=9$: slab $z\in[\frac{%d}{27},\frac{%d}{27})$, $(x,y)$' % (int(to_int(np.array(zfix), b)),
                                                                                               int(to_int(np.array(zfix), b)) + 1))
    # (b)
    zx0, zy0 = zoom[0] / 3, zoom[1] / 3
    grid(axb, zx0, zx0 + 1 / 3, zy0, zy0 + 1 / 3, step=1 / 27, color=GRID, lw=0.45, z=0)
    for p_ in frz[zsel]:
        axb.add_patch(Rectangle(p_, 1 / 81, 1 / 81, fc='#e4e4e4', ec='#b5b5b5', lw=0.3, zorder=1))
    draw_points(axb, frz[zsel], xy[zsel], s_lat=14, s_pt=6.5, jlw=0.6)
    axb.scatter(seed_in[:, 0], seed_in[:, 1], marker='+', s=9, c=ACC, linewidths=0.6, zorder=6)
    axb.scatter([xy[ip, 0]], [xy[ip, 1]], s=90, facecolors='none', edgecolors=ACC, linewidths=0.8, zorder=7)
    label(axb, xy[ip, 0] + 0.009, xy[ip, 1] + 0.009, '(c)', fs=6.2, ha='left', va='bottom')
    clean(axb, ((zx0 - 0.001, zx0 + 1 / 3 + 0.001), (zy0 - 0.001, zy0 + 1 / 3 + 0.001)))
    panel_title(axb, r'(b) one top box, $(\alpha,\beta_1,\beta_2)=(%d,%d,%d)$' % (a_, d1, d2_))
    # (c) digit strip of one point
    axc.set_xlim(-0.2, M + 0.2); axc.set_ylim(-0.6, 4.2); axc.axis('off')
    roles = ['top'] + ['frz'] * Dpar + ['deep'] * (M0 - Dpar) + ['jit'] * 2
    fc = {'top': INK, 'frz': '#8c8c8c', 'deep': '#d4d4d4', 'jit': 'white'}
    tc = {'top': 'white', 'frz': 'white', 'deep': INK, 'jit': ACC}
    for ci, nmc in enumerate('xyz'):
        yy = 2.6 - ci * 1.05
        axc.text(-0.35, yy + 0.4, nmc, ha='right', va='center', fontsize=7)
        for j in range(M):
            ec = ACC if roles[j] == 'jit' else '#7a7a7a'
            axc.add_patch(Rectangle((j, yy), 0.92, 0.8, fc=fc[roles[j]], ec=ec, lw=0.5))
            axc.text(j + 0.46, yy + 0.4, str(pd[ci, j]), ha='center', va='center', fontsize=6.3, color=tc[roles[j]])
    for x_, w_, t_ in ((0, 1, 'top'), (1, Dpar, 'frozen'), (1 + Dpar, M0 - Dpar, 'deep'), (1 + M0, 2, 'jitter')):
        axc.annotate('', xy=(x_ + 0.02, 3.55), xytext=(x_ + w_ - 0.1, 3.55),
                     arrowprops=dict(arrowstyle='-', color='#7a7a7a', lw=0.5))
        axc.text(x_ + (w_ - 0.08) / 2, 3.68, t_, ha='center', va='bottom', fontsize=5.6,
                 color=ACC if t_ == 'jitter' else INK)
    axc.text(1 + M0 / 2, -0.25, 'block (seed digits)', ha='center', va='top', fontsize=5.6)
    axc.annotate('', xy=(1.02, -0.05), xytext=(1 + M0 - 0.1, -0.05), arrowprops=dict(arrowstyle='-', color='#7a7a7a', lw=0.5))
    axc.set_title('(c) digits of the marked point', fontsize=7.2, pad=2)
    hl = legend_handles(['coarse', 'frz', 'pt', 'jit', 'seed'])
    fig.legend(handles=hl, loc='lower center', ncol=5, frameon=False, bbox_to_anchor=(0.5, 0.0),
               handlelength=1.6, columnspacing=1.2, handletextpad=0.4, fontsize=6.4)
    save(fig, 'base23_lift')
    return dict(M0=M0, M=M, D=Dpar, N=N, d2=d2, c=cm, c0=cm0, npair=npair, zfix=zfix, zoom=zoom, a=a_, d1=d1, d2_=d2_,
                floor0=FLOOR_RES0, floorb3=FLOOR_B3)


# ================================================================== fig:projlines
def middle_relation(Ca, Cb, q, rs):
    rows = [Ca[l] for l in range(rs + 1)] + [Cb[l] for l in range(rs + 1)]
    K = left_kernel_mod(rows, q)
    assert len(K) == 1
    kap = K[0]
    al, be = kap[:rs + 1], kap[rs + 1:]
    assert al[rs] and be[rs]
    g = (-al[rs] * pow(be[rs], -1, q)) % q            # y_rs(x_b) = g y_rs(x_a) + more significant digits
    return al, be, g


def balanced(x, q):
    x %= q
    return x - q if x > q // 2 else x


def fig_projlines():
    s, q, k = 5, 17, 1
    m = s * k
    rs = (m - 1) // 2
    F = USTAR[s]
    C = frame_net(F, k, q)
    ok, nb = t0_check(C, q)
    check('projlines', ok, f'P^(U*_5)_(1,{q}) is a (0,{m},{s})-net over F_{q}: all {nb} compositions full rank')
    # sign of the middle relation on every pair (rem:projlines): +1 if one place is inf, (-1)^{r*} otherwise
    gs = {}
    for a_, b_ in itertools.combinations(range(s), 2):
        gs[(a_, b_)] = middle_relation(C[a_], C[b_], q, rs)[2]
    check('projlines', all(v == 1 for v in gs.values()), f's=5, k=1 (r*={rs}): middle multiplier g = +1 on all 10 pairs')
    # odd r*: s = 7, k = 1 (m = 7, r* = 3), U*_7 frame net at q = 29 -- relation check only (no points)
    s7, q7 = 7, 29
    C7 = frame_net(USTAR[s7], 1, q7)
    ok7, _ = t0_check(C7, q7)
    g7 = {(a_, b_): middle_relation(C7[a_], C7[b_], q7, 3)[2] for a_, b_ in itertools.combinations(range(s7), 2)}
    check('projlines', ok7 and all(v == (1 if a_ == 0 else q7 - 1) for (a_, b_), v in g7.items()),
          's=7, k=1, q=29 (U*_7, r*=3 odd): g = +1 on the 6 pairs with inf, g = -1 = (-1)^{r*} on the 15 finite pairs')
    # the drawn pair: coordinates 1, 2 = places (inf, 0)
    al, be, g = middle_relation(C[0], C[1], q, rs)
    best = None
    for lam in range(1, q):
        Dl = [balanced(lam * x, q) for x in al]
        Dp = [balanced(lam * x, q) for x in be]
        E = sum(map(abs, Dl)) + sum(map(abs, Dp))
        h = (sum(Dl[l] * q ** l for l in range(rs + 1)), sum(Dp[l] * q ** l for l in range(rs + 1)))
        key = (E, h[0] ** 2 + h[1] ** 2)
        if best is None or key < best[0]:
            best = (key, lam, Dl, Dp, h, E)
    _, lam, Dl, Dp, h, E = best
    hn = math.hypot(*h)
    N = q ** m
    sig = hn / math.sqrt(N)
    # all N points, coordinates 1 and 2 as integers (units q^-m)
    n = np.arange(N, dtype=np.int64)
    idx = np.stack([(n // q ** (m - 1 - j)) % q for j in range(m)], 1)      # index digits, MSB first
    w = q ** np.arange(m - 1, -1, -1, dtype=np.int64)
    Cn = np.array(C, dtype=np.int64)
    X1 = (((idx @ Cn[0].T) % q) * w).sum(1)
    X2 = (((idx @ Cn[1].T) % q) * w).sum(1)
    check('projlines', np.array_equal(np.sort(X1), n) and np.array_equal(np.sort(X2), n), 'each coordinate alone is a permutation of the q^5 grid values')
    ph = (h[0] * X1 + h[1] * X2) % N                          # h.x mod 1, in units 1/N
    srt = np.sort(ph)
    gaps = np.diff(np.r_[srt, srt[0] + N])
    gmax = int(gaps.max())
    occ = 1 - gmax / N
    check('projlines', occ <= E / q + 1e-12, f'Lemma R: h.x mod 1 of all {N} points lies in an arc of length {occ:.4f} <= E = {E}/{q} = {E / q:.4f}')
    Sh = abs(np.exp(2j * np.pi * ph / N).mean())
    S2h = abs(np.exp(2j * np.pi * (2 * ph % N) / N).mean())
    phase0 = (srt[np.argmax(gaps) + 1] if np.argmax(gaps) + 1 < len(srt) else srt[0]) / N   # start of the occupied arc
    # window
    wdw = 12.0 / math.sqrt(N)
    wx0, wy0 = 0.37, 0.41
    x1 = X1 / N; x2 = X2 / N
    mk = (x1 >= wx0) & (x1 < wx0 + wdw) & (x2 >= wy0) & (x2 < wy0 + wdw)
    pts = np.stack([x1[mk], x2[mk]], 1)
    # predicted lines: h.x = phase0 + E/(2q) + j (band centres), j integer
    hv = np.array(h, dtype=float)
    pp = pts @ hv
    jj = np.floor(pp - phase0)
    off = pp - phase0 - jj
    check('projlines', np.all(off <= E / q + 1e-9), 'every drawn point lies in its predicted band (h.x - phi_0 mod 1 in [0, E])')
    nlines = int(np.unique(jj).size)
    # ------------------------------------------------ figure
    fig = plt.figure(figsize=(WIDTH, 3.0))
    axa = fig.add_axes([0.075, 0.20, 0.36, 0.70])
    axb = fig.add_axes([0.56, 0.20, 0.42, 0.70])
    # (a) in units of N^{-1/2} from the window corner: band boundaries h.x = phi_0 + j and phi_0 + j + E/q
    sq = math.sqrt(N)
    U = (pts - [wx0, wy0]) * sq
    hu = hv / sq                                               # h.x = hu.u + h.(x0, y0)
    c0 = hv @ [wx0, wy0]
    hun = np.linalg.norm(hu)
    d_ = np.array([-hu[1], hu[0]]) / hun
    cen = np.array([6.0, 6.0])
    def foot(val):                                            # the point of {hu.u = val - c0} closest to cen
        return cen + (val - c0 - cen @ hu) * hu / hun ** 2
    vals = c0 + np.array([[0, 0], [12, 0], [0, 12], [12, 12]]) @ hu
    jlo, jhi = int(np.floor(vals.min() - phase0)) - 1, int(np.ceil(vals.max() - phase0)) + 1
    for j in range(jlo, jhi + 1):
        f0, f1, f2 = foot(phase0 + j), foot(phase0 + j + E / q), foot(phase0 + j + 1)
        for f_ in (f0, f1):
            axa.plot(*np.stack([f_ - 30 * d_, f_ + 30 * d_], 1), color=ACC, lw=0.6, zorder=2)
        axa.add_patch(Polygon([f1 - 30 * d_, f1 + 30 * d_, f2 + 30 * d_, f2 - 30 * d_], closed=True, fc='#ebebeb',
                              ec='none', zorder=0))
    grid(axa, 0, 12, 0, 12, step=1.0, color=FINE, lw=0.25, z=1)
    axa.scatter(U[:, 0], U[:, 1], s=4.5, c=INK, lw=0, zorder=5)
        # normal vector h/|h|^2 (one period), anchored on a band boundary near the lower right
    jj0 = int(np.floor((c0 + np.array([9.5, 2.0]) @ hu) - phase0))
    o = foot(phase0 + jj0) + d_ * (np.array([9.5, 2.0]) - cen) @ d_
    arrow(axa, o, hu / hun ** 2, lw=0.9, ms=6)
    label(axa, o[0] + 0.5 * hu[0] / hun ** 2 + 0.25, o[1] + 0.5 * hu[1] / hun ** 2 + 0.25, r'$h/|h|^2$', fs=6.3, ha='left')
    clean(axa, ((0, 12), (0, 12)), ticks=True)
    axa.set_xticks([0, 4, 8, 12]); axa.set_yticks([0, 4, 8, 12])
    axa.set_xlabel(r'$(x_1-%.2f)\,\sqrt{N}$' % wx0, labelpad=1); axa.set_ylabel(r'$(x_2-%.2f)\,\sqrt{N}$' % wy0, labelpad=1)
    panel_title(axa, r'(a) $(x_1,x_2)$-window, side $12N^{-1/2}$')
    # (b) phase histogram over all N points
    nbins = 4 * q
    hist, edges = np.histogram(((ph / N) - phase0) % 1.0, bins=nbins, range=(0, 1))
    axb.bar(edges[:-1], hist / N * nbins, width=1 / nbins, align='edge', color='#8c8c8c', ec='white', lw=0.3)
    axb.axvspan(0, E / q, color=ACC, alpha=0.10, lw=0)
    axb.axvline(E / q, color=ACC, lw=0.8, ls=DASH)
    axb.axhline(1.0, color=INK, lw=0.5, ls=(0, (1, 1.5)))
    axb.text(E / q + 0.01, 0.92 * (hist / N * nbins).max(), r'$E=\frac{%d}{%d}$' % (E, q), color=ACC, fontsize=6.6, ha='left')
    axb.text(0.98, 1.08, 'uniform', fontsize=6.0, ha='right', va='bottom')
    axb.set_xlim(0, 1); axb.set_ylim(0, (hist / N * nbins).max() * 1.12)
    axb.set_xlabel(r'$h\cdot x-\phi_0\ \mathrm{mod}\ 1$', labelpad=1)
    axb.set_ylabel('density (all $N$ points)', labelpad=2)
    axb.tick_params(length=1.5, pad=1)
    for sp_ in axb.spines.values():
        sp_.set_color('#9a9a9a')
    panel_title(axb, r'(b) $h=(%d,%d)$: $|S(h)|=%s$, occupied arc $%s$' % (h[0], h[1], ffloor(Sh, 2), ffloor(occ + 5e-4, 3)))
    hl = [Line2D([], [], ls='none', marker='o', ms=2.7, mfc=INK, mec='none', label='points of the projection'),
          Line2D([], [], color=ACC, lw=0.8, label='predicted band boundaries'),
          Rectangle((0, 0), 1, 1, fc='#ebebeb', ec='none', label='predicted empty strips')]
    fig.legend(handles=hl, loc='lower center', ncol=3, frameon=False, bbox_to_anchor=(0.5, 0.0),
               handlelength=1.6, columnspacing=1.2, handletextpad=0.4, fontsize=6.4)
    save(fig, 'projlines')
    return dict(s=s, q=q, m=m, rs=rs, N=N, al=al, be=be, g=g, lam=lam, Dl=Dl, Dp=Dp, h=h, E=E, hn=hn, sig=sig, occ=occ,
                Sh=Sh, S2h=S2h, gap=1 / hn * math.sqrt(N), nlines=nlines, npts=len(pts), wdw=wdw, nb=nb)


# ================================================================== captions
def write_captions(R):
    A = R['thmA']
    caps = {}
    caps['thmADesignCaption'] = (
        r"Theorem~\ref{thm:A} at its threshold: the net $\mathcal P^{U^*_4}_{1,q}$ of the lattice design "
        r"$U^*_4$ ($a^*_4=%d$) at $q=5a^*_4+4=%d$, $k=1$, $N=q^4$; in cell units (side $N^{-1/4}$). "
        r"(a) The elementary slab of the cells $(n_3,n_4)=(%d,%d)$, a $%d\times%d$ window of cells $(n_1,n_2)$, "
        r"projected to $(x_1,x_2)$; one point per cell. Open circles: the lattice image $n+r/q$, $r=F_0n\bmod q$ "
        r"((H1) of Lemma~\ref{lem:Ss}); dots: the points; grey segments: the jitter of the two deeper digits, inside "
        r"$[0,1/q)^4$. Accent arrows: the projections of $(I+F_0/q)e_1$ and $(I+F_0/q)e_2$; dashed: slips, where "
        r"$r_1$ or $r_2$ wraps; crosses: lattice sites the net skips there. (b) Zoom on one slip of $r_1$ (dotted box in "
        r"(a)), with the jitter boxes of side $1/q$: across the slip the step is $%s$ instead of $|(I+F_0/q)e_1|$. "
        r"Proved: $\delta N^{1/4}\ge\mathrm{LB}=%d/%d=%s$, the relaxation of Lemma~\ref{lem:Ss} at $k=1$ (here equal "
        r"to the bound $1-a^*_4/q$ of Theorem~\ref{thm:A}). Measured (computed, exact): $c=%s$; the lattice minimum is "
        r"$\lambda_1(I+F_0/q)=%s$."
        % (A['a'], A['q'], A['n3'], A['n4'], A['W'], A['W'], ftr(A['step_sl'], 3), A['r'], A['q'],
           ffloor(A['LB'], 4), ffloor(A['c'], 4), ffloor(A['lam1'], 4)))
    B = R['base23']
    zlo = (B['zfix'][0] * 9 + B['zfix'][1] * 3 + B['zfix'][2])
    caps['baseTwoThreeCaption'] = (
        r"The deep-shift lift (Definition~\ref{def:lift}) in base $b=3$: the digitally shifted (Definition~\ref{def:dshift}) "
        r"$(0,%d,3)$-net of Theorem~\ref{thm:base23}(1) for $m\equiv0\pmod 3$, one lift of the $m=%d$ seed. A point has "
        r"one top digit per coordinate, $%d$ block digits (a copy of a seed point shifted below block depth "
        r"$\lfloor %d/2\rfloor=%d$) and two jitter digits; the top digits $(\alpha,\alpha+\beta_1,\alpha+\beta_1+\beta_2)$ "
        r"select one of $27$ top boxes (side $\frac13$). (a) The slab $z\in[\frac{%d}{27},\frac{%d}{27})$ projected to "
        r"$(x,y)$: %d points, one in each box of side $3^{-3}$; the nine top boxes (thick) carry the same frozen pattern. "
        r"(b) The top box $(\alpha,\beta_1,\beta_2)=(%d,%d,%d)$ (dashed in (a)): each point (dot) lies in the frozen box "
        r"of side $3^{-4}$ (shaded; open circle at its corner) of exactly one point of the seed copy (plus signs), i.e. the "
        r"box fixed by the top digits of that point, which later lifts never change; grey "
        r"segments: the jitter, i.e.\ the deep block digits and the two jitter digits. (c) The nine digits of the "
        r"marked point of (b). Computed, exact: the net is a $(0,9,3)$-net over $\mathbb F_3$, and its toroidal "
        r"$\delta N^{1/3}$ is $%s$, above the floor $%s$ of Theorem~\ref{thm:base23}(1) for $m\equiv0\pmod3$ ($%s$ for "
        r"all $m$; the seed has $%s$)."
        % (B['M'], B['M0'], B['M0'], B['M0'], B['D'], zlo, zlo + 1, 729, B['a'], B['d1'], B['d2_'],
           ffloor(B['c'], 4), '%.4f' % B['floor0'], '%.4f' % B['floorb3'], ffloor(B['c0'], 4)))
    P = R['projlines']
    caps['projLinesCaption'] = (
        r"Lines in a two-dimensional projection (Remark~\ref{rem:projlines}). For odd $m=sk$, $(s,k)\neq(3,1)$, the "
        r"middle digit $r^*=(m-1)/2$ of every pair of coordinates of $\mathcal P^F_{k,q}$ satisfies "
        r"$y_{r^*}(x_b)\equiv\pm y_{r^*}(x_a)$ modulo more significant digits; the sign is $+1$ when one place is "
        r"$\infty$, and $(-1)^{r^*}$ otherwise (checked by computation on all pairs of the net shown, and of "
        r"$U^*_7$ at $q=29$, $k=1$, where $r^*=3$). This is the reversal symmetry of the two-dimensional "
        r"Hammersley set (Proposition~\ref{prop:faure}), transported by M\"obius maps; $t=0$ does not see it. Shown: the "
        r"frame net with the design $U^*_5$, $q=%d$, $k=1$, $N=q^5$, coordinates $(x_1,x_2)$ at the places "
        r"$(\infty,0)$, $r^*=%d$. The relation, with balanced digits, gives the dual frequency $h=(%d,%d)$, "
        r"$|h|=%s\sqrt N$, and puts $h\cdot x\bmod 1$ for all $N$ points in an interval of length at most $E=%d/%d$: "
        r"the points lie in bands around parallel lines with normal $h$ and spacing $1/|h|=%s\,N^{-1/2}$. (a) A window "
        r"of side $12N^{-1/2}$ (light grid: $N^{-1/2}$); accent: the predicted band boundaries "
        r"$h\cdot x\in\phi_0+\{0,E\}+\mathbb Z$ ($\phi_0$: start of the occupied arc); shaded: the predicted empty "
        r"strips. (b) The distribution of $h\cdot x-\phi_0\bmod1$ over all $N$ points (computed): it occupies an arc "
        r"of length $%s$, and $|S(h)|=%s$. A per-$q$ scaling of the middle generator row can break the lines without "
        r"changing $t$ or the separation bounds (Remark~\ref{rem:projlines})."
        % (P['q'], P['rs'], P['h'][0], P['h'][1], ftr(P['sig'], 3), P['E'], P['q'], ftr(P['gap'], 2),
           ftr(P['occ'], 3), ffloor(P['Sh'], 2)))
    hdr = ('% part1_captions.tex -- GENERATED by scripts/figs_part1.py (do not edit by hand; rerun the script).\n'
           '% Caption macros for figs/{thmA_design,base23_lift,projlines}.pdf; every number is asserted by the script.\n')
    with open(os.path.join(OUT, 'part1_captions.tex'), 'w') as f:
        f.write(hdr)
        for k_, v_ in caps.items():
            f.write('\\newcommand{\\%s}{%%\n%s}\n' % (k_, v_))
    return caps


if __name__ == '__main__':
    t0 = time.time()
    if check_ustar_against_repo():
        CHECKS.append(('data', 'U*_4, U*_5 and F_0 of U*_7 equal as_push/ustar_det_designs.json'))
    R = {}
    for nm, fn in (('thmA', fig_thmA), ('base23', fig_base23), ('projlines', fig_projlines)):
        t = time.time()
        R[nm] = fn()
        print(f'{nm:10s} {time.time() - t:5.1f}s  {R[nm]}')
    write_captions(R)
    for fg, what in CHECKS:
        print(f'  [ok] {fg:9s} {what}')
    print(f'total {time.time() - t0:.1f}s; {len(CHECKS)} checks passed')

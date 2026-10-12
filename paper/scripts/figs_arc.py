#!/usr/bin/env python3
"""figs_arc.py -- the "arc" figure series of core.tex.

One mechanism, three regimes: every cell holds one point; the geometric digit (first offset digit) places the
point on a LATTICE IMAGE folded into the cells; the deeper digits only JITTER it.  Separation = lattice minimum
minus the jitter / fault cost.  Five figures, one visual language (see `legend_handles`):

    cell grid            light grey lines
    lattice image        open grey circles  (the point with its deeper digits set to 0, or, in the large-entry
                                             regime, the exact limit lattice anchored at one point)
    actual point         black dots
    jitter               dark grey segment from the lattice image to the actual point
    shortest lattice vec accent arrows (solid)
    fault / slip         accent dashed lines / arrows

  arc_anatomy   toy two-dimensional layer: cells, lattice image, jitter, slips, shortest vector, budget
  arc_small     regime I:   P_{2,11} (thm:main), one z-layer; 4D net over F_17 (k=2) of the deficit-two design over
                            Z[1/2], places (inf,0,1,2) (sec:dim4ex; dim4_deficit2_design.json), one xy-slice
  arc_skeleton  regime II:  B^2_{1,43,3} = S1 at s=3 (thm:S1 / rem:B2); B^1_{1,37,3} Korobov + faults (B1)
  arc_large     regime III: the column net C_13 (thm:col; rev 14.3: E_13) in 3D; C_13 along (1,1,1) (5^3 cells);
                            H5* (prop:HL5) at k=1, a (0,5,5)-net over F_10007 (prop:Hk, k=1), xy-slice: D_5^+ parity
  arc_split     split frame (def:split, lem:Hs, thm:HL, prop:HL5): places, Cauchy layer, H5* net at k=2
  arc_twocoset  prop:twocoset: the two-coset (0,3,3)-net T_1009 ((y,z)-layer, (x,y)-cut) and delta N^{1/3} against p
                (exact values from twocoset_exact.json, precomputed with cellmin.cpp; see twocoset.py)

Nets are built with the builders in this folder (netdefs.py = P_{k,q} of Definition def:net from its formula,
knallp_audit_build.py, dim4_build.py, llg_dump.py / llg_lib.py); only the
drawn points are generated (from their cells).  Key properties are ASSERTED (t=0 by the rank of every box, layer = design, lattice relations,
shortest vectors, and every property stated in the captions), so the figures cannot silently drift.  Also writes figs/arc_captions.tex (caption macros).

    uv run --with numpy --with matplotlib python scripts/figs_arc.py [--out DIR]     (deterministic; ~10 s)
Output (default DIR = figs/ next to scripts/): DIR/arc_{anatomy,gk2d,whylat,small,skeleton,large,twocoset,split}.pdf
(+ .png previews) and DIR/arc_captions.tex.  The committed PDFs were written with matplotlib 3.11.0 (arc_twocoset,
arc_whylat: 3.11.2); with that version the output is byte-identical, with others identical up to PDF encoding.
"""
import os
import sys
import json
import importlib.util
import itertools
import time
from fractions import Fraction as Fr


def ffloor(x, d=3):
    """Lower bounds are printed truncated (not rounded) to d decimals."""
    import math
    v = math.floor(float(x) * 10 ** d - 1e-12) / 10 ** d
    return f'%.{d}f' % v


def ftr(x, d=3):
    """rev 15.2: exact and computed values are printed truncated (not rounded) to d decimals, as in Section sec:conv
    (round(., 9) first, so that a float just below an exactly representable decimal is not cut one digit low)."""
    import math
    v = math.floor(round(float(x) * 10 ** d, 9))
    return f'%.{d}f' % (v / 10 ** d)
import numpy as np
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from matplotlib.lines import Line2D
from matplotlib.collections import LineCollection
import logging
logging.getLogger('fontTools').setLevel(logging.ERROR)

HERE = os.path.dirname(os.path.abspath(__file__))          # scripts/ (builders and data files)
OUT = os.path.join(os.path.dirname(HERE), 'figs')           # the paper's figs/
if '--out' in sys.argv:
    OUT = os.path.abspath(sys.argv[sys.argv.index('--out') + 1])
os.makedirs(OUT, exist_ok=True)
sys.path.insert(0, HERE)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


kb = load('knallp_audit_build', os.path.join(HERE, 'knallp_audit_build.py'))      # B1 / B2 recipes
llg_lib = load('llg_lib', os.path.join(HERE, 'llg_lib.py'))                       # split frame, t0 by det
llg_dump = load('llg_dump', os.path.join(HERE, 'llg_dump.py'))                    # gauged split-frame net
dim4 = load('dim4_build', os.path.join(HERE, 'dim4_build.py'))                    # 4D design nets
netdefs = load('netdefs', os.path.join(HERE, 'netdefs.py'))                       # P_{k,q} from def:net

# ------------------------------------------------------------------ common visual language
plt.rcParams.update({
    'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
    'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False,
    'font.size': 7.5, 'axes.titlesize': 7.5, 'axes.labelsize': 7.5, 'legend.fontsize': 6.8,
    'xtick.labelsize': 6.3, 'ytick.labelsize': 6.3, 'axes.linewidth': 0.4,
    'xtick.major.width': 0.3, 'ytick.major.width': 0.3, 'xtick.major.size': 1.5, 'ytick.major.size': 1.5,
    'pdf.fonttype': 42, 'savefig.dpi': 300})
WIDTH = 6.3                     # \textwidth of core.tex (amsart, 11pt, margin 1.1in)
INK = '#111111'                 # actual points, text
GRID = '#c8c8c8'                # cell grid
FINE = '#e2e2e2'                # sub-grid / shading
LATE = '#6f6f6f'                # lattice-image circles
JIT = '#4a4a4a'                 # jitter segments
ACC = '#2b6cb0'                 # the one accent colour (as in fig_main / fig_B_lattice)
S_PT, S_LAT = 7.0, 22.0         # scatter sizes (pt^2)
DASH = (0, (2.4, 1.3))


def legend_handles(keys):
    H = {
        'grid': Line2D([], [], color=GRID, lw=0.9, label='cell grid'),
        'lat': Line2D([], [], ls='none', marker='o', ms=4.4, mfc='none', mec=LATE, mew=0.6, label='lattice image'),
        'pt': Line2D([], [], ls='none', marker='o', ms=2.7, mfc=INK, mec='none', label='actual point'),
        'jit': Line2D([], [], color=JIT, lw=0.7, label='jitter'),
        'vec': Line2D([], [], color=ACC, lw=1.3, label='shortest lattice vectors'),
        'slip': Line2D([], [], color=ACC, lw=0.9, ls=DASH, label='slip / fault'),
        'drift': Line2D([], [], color=JIT, lw=0.7, label='drift + jitter'),
        'skip': Line2D([], [], ls='none', marker='x', ms=4.0, mec=ACC, mew=0.9, label='skipped site'),
    }
    return [H[k] for k in keys]


def common_legend(fig, keys, y=0.0):
    leg = fig.legend(handles=legend_handles(keys), loc='lower center', ncol=len(keys), frameon=False,
                     bbox_to_anchor=(0.5, y), handlelength=1.8, columnspacing=1.4, handletextpad=0.5)
    return leg


def grid(ax, x0, x1, y0, y1, step=1.0, color=GRID, lw=0.35, z=0):
    xs = np.arange(np.ceil(x0 / step) * step, x1 + 1e-9, step)
    ys = np.arange(np.ceil(y0 / step) * step, y1 + 1e-9, step)
    segs = [[(x, y0), (x, y1)] for x in xs] + [[(x0, y), (x1, y)] for y in ys]
    ax.add_collection(LineCollection(segs, colors=color, linewidths=lw, zorder=z))


def draw_points(ax, ideal, actual, s_lat=S_LAT, s_pt=S_PT, jit=True, lat=True):
    if jit:
        ax.add_collection(LineCollection(np.stack([ideal, actual], 1), colors=JIT, linewidths=0.55, zorder=4))
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


# ------------------------------------------------------------------ digital nets from their cells
def inv_mod(A, q):
    n = len(A)
    A = [[int(x) % q for x in r] + [int(i == j) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        piv = next(i for i in range(c, n) if A[i][c] % q)
        A[c], A[piv] = A[piv], A[c]
        iv = pow(A[c][c], -1, q)
        A[c] = [x * iv % q for x in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                f = A[i][c]
                A[i] = [(x - f * y) % q for x, y in zip(A[i], A[c])]
    return np.array([r[n:] for r in A], dtype=np.int64)


class DNet:
    """digital net over Z/q (q prime here) with generator matrices C[c] (m x m, digit j = row j, MSB first) and
    cell depths K.  The cell digits determine the point (asserted), so only the drawn points are generated."""

    def __init__(self, C, q, K):
        self.q, self.K, self.s = q, list(K), len(C)
        self.C = [np.array([[int(x) % q for x in r] for r in Cc], dtype=np.int64) for Cc in C]
        self.m = self.C[0].shape[0]
        assert sum(K) == self.m
        self.Ti = inv_mod(np.vstack([self.C[c][:K[c]] for c in range(self.s)]), q)

    def t0(self):
        bad, nbox = llg_lib.t0_check_mod([Cc.tolist() for Cc in self.C], self.s, self.q)
        return bad == 0, nbox

    def eval(self, cells):
        """cells (n, s) ints, cell c in [0, q^K_c).  Returns (X, D): X (n, s) float coordinates in cell units
        (cell + offset in [0,1)), D[c] (n, m) the digit vectors."""
        q, s = self.q, self.s
        cells = np.asarray(cells, dtype=np.int64)
        dig = np.concatenate([np.stack([(cells[:, c] // q ** (self.K[c] - 1 - j)) % q for j in range(self.K[c])], 1)
                              for c in range(s)], 1)
        v = (dig @ self.Ti.T) % q
        X = np.zeros(cells.shape, dtype=np.float64)
        D = []
        for c in range(s):
            Dc = (v @ self.C[c].T) % q
            cell = np.zeros(len(cells), dtype=np.int64)
            for j in range(self.K[c]):
                cell = cell * q + Dc[:, j]
            assert np.all(cell == cells[:, c]), 'point not in its cell'
            off = np.zeros(len(cells))
            for j in range(self.K[c], self.m):
                off += Dc[:, j] * float(q) ** (-(j - self.K[c] + 1))
            X[:, c] = cell + off
            D.append(Dc)
        return X, D

    def geo(self, D):
        """geometric digit r (first offset digit) of every coordinate, (n, s) ints."""
        return np.stack([D[c][:, self.K[c]] for c in range(self.s)], 1)


def window(x0, y0, W, H=None, rest=()):
    H = W if H is None else H
    gx, gy = np.meshgrid(np.arange(x0, x0 + W), np.arange(y0, y0 + H), indexing='ij')
    cols = [gx.ravel(), gy.ravel()] + [np.full(gx.size, r) for r in rest]
    return np.stack(cols, 1)


def slip_edges(cells, ideal, Lmat, dims=(0, 1), tol=0.5):
    """cell edges across which the step of the lattice image deviates from the lattice step L e by more than tol
    (in the drawn coordinates): a wrap of the geometric digit.  Returns segments and the set of slip pairs."""
    idx = {tuple(c[:2]): i for i, c in enumerate(cells)}
    segs, pairs = [], set()
    for i, c in enumerate(cells):
        for a in (0, 1):
            nb = (c[0] + (a == 0), c[1] + (a == 1))
            if nb not in idx:
                continue
            e = np.zeros(Lmat.shape[0]); e[a] = 1
            d = ideal[idx[nb]] - ideal[i] - Lmat @ e
            if np.abs(d[list(dims)]).max() > tol:
                pairs.add((i, idx[nb]))
                if a == 0:
                    segs.append([(c[0] + 1, c[1]), (c[0] + 1, c[1] + 1)])
                else:
                    segs.append([(c[0], c[1] + 1), (c[0] + 1, c[1] + 1)])
    return segs, pairs


def draw_slips(ax, segs, lw=0.9):
    ax.add_collection(LineCollection(segs, colors=ACC, linewidths=lw, linestyles=[DASH], zorder=2))


SKIP_TOL = 0.4                  # a site within this distance of a point counts as occupied (lambda_1 ~ 0.9)


def skipped_sites(cells, ideal2, L2):
    """Vernier skips of a planar lattice image (xy).  From every point, continue its local lattice one step
    L2 e (e = +-e_x, +-e_y) into the neighbouring cell; if the neighbour's lattice image is not there (a component
    of the geometric digit wrapped: a slip), the continued site is an ideal lattice site that the net skips,
    unless some point sits on it (within SKIP_TOL).  Sites outside the window are dropped; duplicates merged."""
    idx = {tuple(c[:2]): i for i, c in enumerate(cells)}
    lo = cells[:, :2].min(0).astype(float)
    hi = cells[:, :2].max(0) + 1.0
    sk = []
    for i, c in enumerate(cells):
        for a in (0, 1):
            for sg in (1, -1):
                nb = (c[0] + sg * (a == 0), c[1] + sg * (a == 1))
                if nb not in idx:
                    continue
                e = np.zeros(2); e[a] = sg
                pnt = ideal2[i] + L2 @ e
                if np.abs(ideal2[idx[nb]] - pnt).max() <= 0.5:
                    continue                                   # no wrap: the continuation is the neighbour
                if np.all(pnt >= lo) and np.all(pnt < hi) and \
                        np.min(np.linalg.norm(ideal2 - pnt, axis=1)) > SKIP_TOL and \
                        not any(np.linalg.norm(pnt - x) < SKIP_TOL for x in sk):
                    sk.append(pnt)
    return np.array(sk).reshape(-1, 2)


def seg_dist(P, segs):
    """distance of each point of P to the nearest segment."""
    S = np.array(segs, dtype=float)
    A, B = S[:, 0], S[:, 1]
    AB = B - A
    t = np.clip((((P[:, None, :] - A[None]) * AB[None]).sum(-1)) / (AB * AB).sum(-1)[None], 0, 1)
    Q = A[None] + t[..., None] * AB[None]
    return np.linalg.norm(P[:, None, :] - Q, axis=-1).min(1)


def draw_skips(ax, sk, s=16):
    ax.scatter(sk[:, 0], sk[:, 1], marker='x', s=s, c=ACC, linewidths=0.9, zorder=6)


def check_skips(fig, sk, segs, L2, W, what, density=True):
    """(#ideal sites - #net points) in the window = #skips ~ (1/det L2 - 1) W^2 up to the boundary; every skip
    lies next to a slip line."""
    exp = (1 / np.linalg.det(L2) - 1) * W * W
    check(fig, (not density) or abs(len(sk) - exp) <= W, f'{what}: {len(sk)} skipped sites vs density excess (1/det-1)W^2 = '
                                        f'{exp:.1f} ' + (f'(|diff| <= W = {W}, boundary)' if density else '(recorded, not asserted)'))
    dd = seg_dist(sk, segs)
    check(fig, dd.max() <= 1.0, f'{what}: every skipped site lies within {dd.max():.2f} <= 1 cell of a slip line')
    return exp


def pick_anchor(cells, ideal, Lmat, pairs, target, extra_ok=lambda i: True):
    """a cell whose +e_x and +e_y steps are exact lattice steps (no slip, no carry), closest to target."""
    idx = {tuple(c[:2]): i for i, c in enumerate(cells)}
    best = None
    for i, c in enumerate(cells):
        ok = extra_ok(i)
        for a in (0, 1):
            nb = (c[0] + (a == 0), c[1] + (a == 1))
            if not ok or nb not in idx or (i, idx[nb]) in pairs:
                ok = False
                break
            e = np.zeros(Lmat.shape[0]); e[a] = 1
            ok = np.abs(ideal[idx[nb]] - ideal[i] - Lmat @ e).max() < 1e-9
        if ok:
            dd = (c[0] - target[0]) ** 2 + (c[1] - target[1]) ** 2
            if best is None or dd < best[0]:
                best = (dd, i)
    assert best is not None, 'no exact-lattice anchor in the window'
    return best[1]


CHECKS = []                      # (figure, statement) pairs, printed at the end


def check(fig, cond, what):
    assert cond, f'[{fig}] FAILED: {what}'
    CHECKS.append((fig, what))


# ================================================================== arc_anatomy
def fig_anatomy():
    q = 9
    M = np.array([[-1, -1], [1, -1]])                     # 2D analogue of M = -I + [u x] of prop:cell
    L = np.eye(2) + M / q                                 # lattice image (I + M/q) Z^2: rotated + contracted Z^2
    W, x0, y0 = 11, 1, 0
    cells = window(x0, y0, W)
    ell = cells % q
    r = (ell @ M.T) % q                                   # geometric digit, a linear function of the last cell digits
    rng = np.random.default_rng(20261007)
    f = rng.random(cells.shape)                           # deeper digits: an arbitrary jitter in [0,1)^2 (units 1/q)
    ideal = cells + r / q
    actual = ideal + f / q
    segs, pairs = slip_edges(cells, ideal, L)
    lam = np.linalg.norm(L[:, 0])
    check('anatomy', abs(lam - np.sqrt(1 - 2 / q + 2 / q ** 2)) < 1e-12, 'lambda_1 = |(I+M/q)e_x| = (1-2/q+2/q^2)^(1/2)')
    i0 = pick_anchor(cells, ideal, L, pairs, (x0 + 5.5, y0 + 6.5))
    n0 = cells[i0]
    # shortest vectors of (I+M/q)Z^2 are the columns of L (|L v|^2 = ((1-1/q)^2+1/q^2)|v|^2 since L is conformal)
    check('anatomy', np.allclose(L.T @ L, lam ** 2 * np.eye(2)), '(I+M/q) is a rotation times a contraction')
    check('anatomy', len(segs) > 0, 'window contains slips of the geometric digit')
    d = np.sqrt(((actual[:, None] - actual[None]) ** 2).sum(-1)) + np.eye(len(actual)) * 9
    dmin = d.min()
    sk = skipped_sites(cells, ideal, L)
    exp = check_skips('anatomy', sk, segs, L, W, 'toy')

    fig = plt.figure(figsize=(WIDTH, 3.05))
    axa = fig.add_axes([0.035, 0.12, 0.43, 0.80])
    axb = fig.add_axes([0.505, 0.40, 0.31, 0.50])
    # (a)
    grid(axa, x0, x0 + W, y0, y0 + W)
    draw_slips(axa, segs)
    draw_points(axa, ideal, actual)
    draw_skips(axa, sk)
    o = ideal[i0]
    arrow(axa, o, L[:, 0]); arrow(axa, o, L[:, 1])
    label(axa, o[0] + L[0, 0] + 0.15, o[1] + L[1, 0] - 0.42, r'$(I+\frac{M}{q})e_x$', fs=6.5, ha='left')
    label(axa, o[0] + L[0, 1] - 0.12, o[1] + L[1, 1] + 0.12, r'$(I+\frac{M}{q})e_y$', fs=6.5, ha='right')
    i1 = [i for i, c in enumerate(cells) if c[0] == n0[0] + 1 and c[1] == n0[1]][0]
    cxy = (ideal[i0] + ideal[i1]) / 2
    bx0, bx1, by0, by1 = cxy[0] - 1.05, cxy[0] + 1.25, cxy[1] - 0.8, cxy[1] + 1.12
    axa.add_patch(Rectangle((bx0, by0), bx1 - bx0, by1 - by0, fc='none', ec=INK, lw=0.5, ls=(0, (1, 1)), zorder=8))
    label(axa, bx0 + 0.04, by1 + 0.04, '(b)', col=INK, fs=6.5, ha='left', va='bottom')
    # one slip label: pick a slip segment far from the anchor
    sg = max(segs, key=lambda s: -abs(s[0][0] - (x0 + 8.0)) - abs(s[0][1] - (y0 + 2.0)))
    label(axa, sg[0][0] + 0.15, sg[0][1] + 0.5, 'slip', fs=6.5, ha='left')
    clean(axa, ((x0 - 0.05, x0 + W + 0.05), (y0 - 0.05, y0 + W + 0.05)))
    panel_title(axa, r'(a) one point per cell; lattice image $n+r/q$, $r=Mu\ \mathrm{mod}\ q$')
    # (b) the separation budget for one step
    sub = 1.0 / q
    grid(axb, bx0, bx1, by0, by1)
    grid(axb, bx0, bx1, by0, by1, step=sub, color=FINE, lw=0.25, z=-1)
    for i in (i0, i1):                                   # the sub-cell of side 1/q that the jitter cannot leave
        axb.add_patch(Rectangle(ideal[i], sub, sub, fc='#ececec', ec=LATE, lw=0.4, zorder=1))
    draw_points(axb, ideal[[i0, i1]], actual[[i0, i1]], s_lat=60, s_pt=22)
    arrow(axb, ideal[i0], L[:, 0], lw=1.4, ms=9)
    arrow(axb, actual[i0], actual[i1] - actual[i0], col=INK, lw=0.6, ms=6, z=7)
    mid = ideal[i0] + L[:, 0] / 2
    label(axb, mid[0], mid[1] - 0.22, r'$\lambda_1=%s$' % ftr(lam, 3), fs=7)
    ma = (actual[i0] + actual[i1]) / 2
    label(axb, ma[0], ma[1] + 0.12, r'$\Delta$', col=INK, fs=7.5)
    label(axb, ideal[i1][0] + 0.02, ideal[i1][1] - 0.12, r'jitter box, side $1/q$', col=JIT, fs=6.0, ha='center',
          va='top', bg=False)
    pair = np.linalg.norm(actual[i1] - actual[i0])
    check('anatomy', pair >= lam - np.sqrt(2) / q, f'(b): |Delta| = {pair:.3f} >= lambda_1 - sqrt2/q')
    txt = (r'$\Delta=(I+\frac{M}{q})e_x+\frac{f^\prime-f}{q}$' + '\n' +
           r'$|\Delta|\geq\lambda_1-\frac{|f^\prime-f|}{q}$' + '\n' +
           r'$\quad\ >\lambda_1-\frac{\sqrt{2}}{q}=%s$' % ffloor(lam - np.sqrt(2) / q) + '\n' +
           'separation =\nlattice minimum\n$-$ jitter cost')
    fig.text(0.828, 0.88, txt, fontsize=6.6, ha='left', va='top', linespacing=1.45,
             bbox=dict(fc='white', ec='#b0b0b0', lw=0.4, pad=2.5))
    clean(axb, ((bx0, bx1), (by0, by1)))
    panel_title(axb, r'(b) one step: lattice vector + jitter')
    # (c) the vernier in one dimension: r = -l mod q along one axis, lattice spacing 1 - 1/q
    axc = fig.add_axes([0.52, 0.13, 0.46, 0.17])
    n1 = np.arange(1, q + 4)
    pts1 = n1 + ((-n1) % q) / q                                  # one point per cell
    sites = 1 + (1 - 1 / q) * np.arange(1, q + 4)                # the lattice of the point of cell 1, continued
    sites = sites[sites < q + 4]
    hit = np.array([np.min(np.abs(pts1 - x_)) < 1e-9 for x_ in sites])
    skip1 = sites[~hit & (sites < q + 1)]
    check('anatomy', len(skip1) == 1 and q <= skip1[0] < q + 1 and np.all(hit | (sites >= q + 1) | (np.abs(sites - skip1[0]) < 1e-12)),
          f'1D vernier: cells 1..q hold the sites 1+m(1-1/q), m=1..q, and cell q holds one more, skipped '
          f'(at {skip1[0]:.3f})')
    after = pts1[n1 > q] - (1 + (1 - 1 / q) * (n1[n1 > q] + 1))
    check('anatomy', np.allclose(after, 1 / q), '1D vernier: after the slip the points sit on the lattice shifted by 1/q')
    for t in range(1, q + 5):
        axc.plot([t, t], [-0.5, 0.5], color=GRID, lw=0.5, zorder=0)
    axc.plot([1, q + 4], [0, 0], color=GRID, lw=0.4, zorder=0)
    axc.plot([q + 1, q + 1], [-0.62, 0.62], color=ACC, lw=0.9, ls=DASH, zorder=2)
    axc.scatter(sites, np.zeros_like(sites), s=20, facecolors='none', edgecolors=LATE, linewidths=0.55, zorder=3)
    axc.scatter(pts1, np.zeros_like(pts1), s=7, c=INK, lw=0, zorder=5)
    axc.scatter(skip1, [0], marker='x', s=22, c=ACC, linewidths=1.0, zorder=6)
    axc.text(q + 1.06, 0.38, 'slip', fontsize=6.2, color=ACC, ha='left', va='center')
    axc.annotate('', xy=(q + 1 + ((-(q + 1)) % q) / q, -0.33), xytext=(q, -0.33),
                 arrowprops=dict(arrowstyle='-|>', color=INK, lw=0.6, mutation_scale=5, shrinkA=0, shrinkB=0))
    axc.text(q + 0.95, -0.62, r'step $2-\frac{1}{q}$', fontsize=5.8, ha='center', va='top')
    for t_ in (2, 5, 8):
        axc.text(t_ + 0.5, 0.42, r'$r=%d$' % ((-t_) % q), fontsize=5.6, color='#505050', ha='center', va='bottom')
    axc.set_xlim(0.95, q + 4.05); axc.set_ylim(-0.95, 0.75); axc.axis('off')
    axc.set_title(r'(c) one axis, $r=-u$ mod $q$: spacing $1-\frac{1}{q}$, one site in $q$ skipped',
                  fontsize=7.2, pad=2)
    common_legend(fig, ['grid', 'lat', 'pt', 'jit', 'vec', 'slip', 'skip'], y=0.0)
    save(fig, 'arc_anatomy')
    return dict(q=q, W=W, lam=lam, nslip=len(segs), dmin=dmin, nskip=len(sk), exp=exp,
                det=np.linalg.det(L))


# ================================================================== arc_small
MM3 = np.array([[-1, -1, 1], [1, -1, -1], [-1, 1, -1]])           # prop:cell
JJ3 = np.array([[0, 0, -1], [-1, 0, 0], [0, -1, 0]])


def pkq_mats(q, m):
    """generator matrices of P_{k,q} (Definition def:net, m = 3k) from netdefs.py, and all q^m points by index
    enumeration (index digits v, least significant first; coordinate c = digits C_c v mod q, most significant
    first) -- an evaluation independent of the cell-wise one of DNet."""
    k = m // 3
    C = [np.array(Cc, dtype=np.int64) % q for Cc in netdefs.P_mats(k)['C']]
    idx = np.arange(q ** m, dtype=np.int64)
    V = np.stack([(idx // q ** l) % q for l in range(m)], 1)            # (N, m), column l = digit v_l
    w = q ** np.arange(m - 1, -1, -1, dtype=np.int64)
    P = np.stack([((V @ Cc.T) % q) @ w for Cc in C], 1)
    return C, P


def regime1_panel(ax, net, cells, Mlay, title, s_pt=S_PT, s_lat=S_LAT, anchor_target=None, mname='M'):
    X, D = net.eval(cells)
    r = net.geo(D)
    ideal = np.floor(X) + r / net.q                          # deeper digits set to 0
    L = np.eye(net.s) + Mlay / net.q
    segs, pairs = slip_edges(cells, ideal, L)
    k = net.K[0]
    i0 = pick_anchor(cells, ideal, L, pairs, anchor_target,
                     extra_ok=lambda i: all(D[a][i, k - 1] != net.q - 1 for a in (0, 1)))
    x0, y0 = cells[:, 0].min(), cells[:, 1].min()
    W = cells[:, 0].max() - x0 + 1
    grid(ax, x0, x0 + W, y0, y0 + W)
    draw_slips(ax, segs, lw=0.8)
    draw_points(ax, ideal[:, :2], X[:, :2], s_lat=s_lat, s_pt=s_pt)
    L2 = L[:2, :2]                                   # the xy-projection of a layer is the planar image (I+M_xy/q)Z^2
    sk = skipped_sites(cells, ideal[:, :2], L2)
    draw_skips(ax, sk, s=13)
    o = ideal[i0, :2]
    for a in (0, 1):
        arrow(ax, o, L[:2, a], lw=1.2)
    label(ax, o[0] + L[0, 0] + 0.1, o[1] + L[1, 0] - 0.45, r'$(I+\frac{%s}{q})e_x$' % mname, fs=6.2, ha='left')
    label(ax, o[0] + L[0, 1] - 0.1, o[1] + L[1, 1] + 0.15, r'$(I+\frac{%s}{q})e_y$' % mname, fs=6.2, ha='right')
    clean(ax, ((x0 - 0.05, x0 + W + 0.05), (y0 - 0.05, y0 + W + 0.05)))
    panel_title(ax, title)
    return X, D, ideal, segs, i0, L, sk, L2


def fig_small():
    # ---- (a) P_{2,7}: q = 7, k = 2, m = 6, N = 7^6
    q, k = 11, 2
    m = 3 * k
    C, Pidx = pkq_mats(q, m)
    net = DNet(C, q, [k] * 3)
    ok, nbox = net.t0()
    check('small', ok, f'P_{{{k},{q}}} is a (0,{m},3)-net: all {nbox} box ranks full over F_{q}')
    G = q ** k
    allc = np.stack(np.meshgrid(*(np.arange(G),) * 3, indexing='ij'), -1).reshape(-1, 3)
    Xall, _ = net.eval(allc)
    Iall = np.rint(Xall * q ** (m - k)).astype(np.int64)
    check('small', set(map(tuple, Iall)) == set(map(tuple, Pidx)) and len(Pidx) == q ** m,
          f'cell-wise points of P_{{{k},{q}}} == points by index enumeration ({q ** m} points)')
    W = 14
    x0, y0, z0 = 53, 49, G // 2
    cells = window(x0, y0, W, rest=(z0,))
    X, D = net.eval(cells)
    ell = np.stack([D[c][:, k - 1] for c in range(3)], 1)
    hh = np.stack([D[c][:, k - 2] for c in range(3)], 1)
    r = net.geo(D)
    check('small', np.all(r == (ell @ MM3.T + hh @ JJ3.T) % q), 'geometric digit r = M l + J h mod q (prop:cell)')
    # ---- (b) 4D deficit-two design over Z[1/2], places (inf, 0, 1, 2) (sec:dim4ex), k = 2, q = 17
    D4d = json.load(open(os.path.join(HERE, 'dim4_deficit2_design.json')))
    F, places4 = D4d['F'], D4d['places']
    F0 = np.array(F[0])
    check('small', places4 == ['inf', '0', '1', '2'] and
          F0.tolist() == [[-2, -2, -1, -2], [1, -2, 1, 1], [1, -2, -2, 2], [1, -1, -1, -1]] and
          F[1] == [[0, 3, 1, 1], [0, 1, -2, -1], [-1, 1, 0, -3], [-2, 1, 0, 0]],
          'dim4_deficit2_design.json = the deficit-two design over Z[1/2] on the places (inf,0,1,2) (sec:dim4ex)')
    Mps = [np.array(F[0])]
    for Fn in F[1:]:
        Mps.append(Mps[-1] + np.array(Fn))
    check('small', max(np.abs(M_).max() for M_ in Mps) == 2 and np.abs(F0).max() == 2 and
          max(np.abs(np.array(Fn)).max() for Fn in F) == 3,
          'design: max|M^(j)| = 2 = max|F_0| (entries of size two, rem:pm1), max|F_n| = 3')
    q4, k4 = 17, 2
    Cs, up, ep = dim4.build(F, k4, places=places4)
    check('small', up <= {2} and ep <= {2}, f'4D gauge solved exactly over Q: units and denominators are powers of 2 '
                                            f'(unit primes {sorted(up)}, denominator primes {sorted(ep)})')
    mp4, nbq4 = dim4.minor_primes(Cs)
    check('small', mp4 is not None and mp4 <= {2}, f'4D net (k={k4}): all {nbq4} box minors over Q are +-2^j '
                                                   f'(primes {sorted(mp4)}), so t=0 for every odd q')
    net4 = DNet([[[(Fr(x).numerator * pow(Fr(x).denominator, -1, q4)) % q4 for x in row] for row in Cc] for Cc in Cs],
                q4, [k4] * 4)
    ok4, nbox4 = net4.t0()
    check('small', ok4, f'4D net (deficit-two design, k={k4}) is a (0,{4 * k4},4)-net over F_{q4}: all {nbox4} boxes '
                        f'full rank')
    for c in range(4):
        for d in range(4):
            assert net4.C[c][k4, d * k4 + k4 - 1] == F[0][c][d] % q4 and net4.C[c][k4, d * k4 + k4 - 2] == F[1][c][d] % q4
    check('small', True, 'row 0 of the 4D graph form = (F_0, F_1) of the deficit-two design on levels k-1, k-2')
    W4 = 14
    G4 = q4 ** k4
    x40, y40 = 41, 49
    cells4 = window(x40, y40, W4, rest=(G4 // 2, G4 // 3))
    check('small', any(t % q4 == 0 for t in range(x40 + 1, x40 + W4)) and
          any(t % q4 == 0 for t in range(y40 + 1, y40 + W4)), '4D window crosses a carry in x and in y')

    fig = plt.figure(figsize=(WIDTH, 3.45))
    axa = fig.add_axes([0.02, 0.10, 0.47, 0.82])
    axb = fig.add_axes([0.51, 0.10, 0.47, 0.82])
    X, D, ideal, segs, i0, L, sk, L2 = regime1_panel(
        axa, net, cells, MM3,
        r'(a) $\mathcal{P}_{2,11}$: $z$-slab $n_z=%d$, $(I+\frac{M}{q})\mathbb{Z}^3$' % z0,
        anchor_target=(x0 + 5, y0 + 8))
    check('small', abs(np.linalg.norm(L[:, 0]) - np.sqrt(1 - 2 / q + 3 / q ** 2)) < 1e-12,
          'lambda_1(Lambda_q) = (1-2/q+3/q^2)^(1/2) (rem:lattice3)')
    lam4 = {}
    for nm_, LL, ss in (('3D', L, 3), ('4D', np.eye(4) + F0 / q4, 4)):
        V = np.array([v for v in itertools.product(range(-2, 3), repeat=ss) if any(v)])
        ln = np.linalg.norm(V @ LL.T, axis=1)
        o_ = np.argsort(ln, kind='stable')[:2 * ss]
        assert all(np.abs(V[i]).sum() == 1 for i in o_), nm_
        lam4[nm_] = ln.min()
    check('small', True, 'the 2s shortest vectors of (I+M/q)Z^3 and (I+F_0/q)Z^4 (over |v|_inf <= 2) are the '
                         f'+-columns; lambda_1 = {lam4["3D"]:.4f} (3D), {lam4["4D"]:.4f} (4D)')
    X4, D4, ideal4, segs4, i04, L4, sk4, L24 = regime1_panel(
        axb, net4, cells4, F0,
        r'(b) deficit-two design, $s=4$, $q=17$: $xy$-slice, $(I+\frac{F_0}{q})\mathbb{Z}^4$',
        anchor_target=(x40 + 5, y40 + 8), mname='F_0')
    exp3 = check_skips('small', sk, segs, L2, W, 'P_{2,11} layer (xy)')
    exp4 = check_skips('small', sk4, segs4, L24, W4, '4D slice (xy)')
    check('small', q4 > q and len(segs4) > len(segs),
          f'4D slice: more slip edges than the P_{{2,{q}}} layer in the same {W}x{W} window ({len(segs4)} vs {len(segs)})')
    check('small', abs(np.linalg.det(L) - (1 - 1 / q) * ((1 - 1 / q) ** 2 + 3 / q ** 2)) < 1e-12,
          'det(I+M/q) = (1-1/q)((1-1/q)^2+3/q^2) (3D lattice too dense by ~3/q)')
    # carry lines (last cell digit wraps): thin dotted, to show where the second layer row enters
    for ax, cc, kk, qq in ((axa, cells, k, q), (axb, cells4, k4, q4)):
        xs0, ys0 = cc[:, 0].min(), cc[:, 1].min(); Wd = cc[:, 0].max() - xs0 + 1
        for t in range(xs0 + 1, xs0 + Wd):
            if t % qq == 0:
                ax.plot([t, t], [ys0, ys0 + Wd], color=INK, lw=0.45, ls=(0, (0.6, 1.4)), zorder=1)
        for t in range(ys0 + 1, ys0 + Wd):
            if t % qq == 0:
                ax.plot([xs0, xs0 + Wd], [t, t], color=INK, lw=0.45, ls=(0, (0.6, 1.4)), zorder=1)
    handles = legend_handles(['grid', 'lat', 'pt', 'jit', 'vec', 'slip', 'skip']) + [
        Line2D([], [], color=INK, lw=0.6, ls=(0, (0.6, 1.4)), label='last cell digit wraps')]
    fig.legend(handles=handles, loc='lower center', ncol=8, frameon=False, bbox_to_anchor=(0.5, 0.0),
               handlelength=1.6, columnspacing=0.9, handletextpad=0.4, fontsize=6.4)
    save(fig, 'arc_small')
    return dict(q=q, k=k, W=W, z0=z0, nslip=len(segs), q4=q4, k4=k4, W4=W4, nslip4=len(segs4), lam4=lam4,
                nsk=len(sk), exp3=exp3, nsk4=len(sk4), exp4=exp4, det2=np.linalg.det(L2), det24=np.linalg.det(L24),
                det3=np.linalg.det(L),
                c4=(x40, y40, G4 // 2, G4 // 3), lam=np.linalg.norm(L[:, 0]), nbox4=nbox4, nbox=nbox)


# ================================================================== arc_skeleton
class BNet:
    """B^2 (r=2) / B^1 (r=1) nets from knallp_audit_build's recipe; fine positions P_c (fine-cell units)."""

    def __init__(self, r, p, k, rho):
        self.r, self.p, self.k, self.rho, self.m = r, p, k, rho, 3 * k + r
        C, K = (kb.recipe_B2 if r == 2 else kb.recipe_B1)(p, k, rho)
        sk = kb.skB2(rho) if r == 2 else kb.skB1(rho)
        assert kb.is_knskel(r, p, k, sk, C), 'skeleton digits are not those of Definition B'
        self.K = K
        self.net = DNet(C, p, K)

    def fine(self, cells):
        X, D = self.net.eval(cells)
        Pf = np.stack([X[:, c] * self.p ** (self.k + 1 - self.K[c]) for c in range(3)], 1)   # fine units
        return Pf, D


def reduce2(u, v):
    u, v = np.array(u), np.array(v)
    while True:
        if u @ u > v @ v:
            u, v = v, u
        t = int(np.round((u @ v) / (u @ u)))
        if t == 0:
            return u, v
        v = v - t * u


def fig_skeleton():
    # ---- B^2_{1,43,3} = S1 at s = 3: K = (2,2,1), skeleton digit S_z = rho x_k + rho^2 y_k
    p, k, rho = 43, 1, 3
    B2 = BNet(2, p, k, rho)
    ok, nbox = B2.net.t0()
    check('skeleton', ok, f'B^2_{{1,{p},{rho}}} is a (0,{B2.m},3)-net over F_{p}: all {nbox} boxes full rank')
    W, xa, ya, zstar = 30, 700, 896, 1000
    layers = list(range(zstar, zstar + rho))
    cells = np.array([(x, y, z) for x in range(xa, xa + W) for y in range(ya, ya + W)
                      for z in sorted({zz // p for zz in layers})], dtype=np.int64)
    Pf, _ = B2.fine(cells)
    P = np.floor(Pf).astype(np.int64)
    check('skeleton', np.all((rho * P[:, 0] + rho * rho * P[:, 1] - P[:, 2]) % p == 0),
          'occupied fine cells of B^2 lie in Lambda_2 = {a_z = rho a_x + rho^2 a_y mod p}')
    keep1 = P[:, 2] == zstar
    keepS = np.isin(P[:, 2], layers)
    Ps = P[keepS]
    dsup = np.abs(Ps[:, None, :2] - Ps[None, :, :2]).max(-1) + np.eye(len(Ps), dtype=np.int64) * 10 ** 6
    check('skeleton', dsup.min() >= rho, f'inside a slab of rho={rho} layers, occupied cells differ by >= rho '
                                         f'in x or y (lem:skellat (L)) [min {dsup.min()}]')
    u2, v2 = reduce2((-rho, 1), (p, 0))
    for w in (u2, v2):
        assert (rho * w[0] + rho * rho * w[1]) % p == 0
    check('skeleton', tuple(u2) == (-rho, 1), f'shortest in-layer vector of Lambda_2 is (-rho,1) = ({u2[0]},{u2[1]})')
    # ---- B^1_{1,37,3}: K = (2,1,1), Korobov (1, rho, rho^2) mod p, unit faults between coarse blocks
    p1, k1, rho1 = 37, 1, 3
    B1 = BNet(1, p1, k1, rho1)
    ok1, nbox1 = B1.net.t0()
    check('skeleton', ok1, f'B^1_{{1,{p1},{rho1}}} is a (0,{B1.m},3)-net over F_{p1}: all {nbox1} boxes full rank')
    half, yblk = 12, 5
    xs0, zs0 = p1 - half, p1 - half
    W1 = 2 * half
    cells1 = np.array([(x, yblk, zc) for x in range(xs0, xs0 + W1) for zc in (0, 1)], dtype=np.int64)
    Pf1, _ = B1.fine(cells1)
    P1 = np.floor(Pf1).astype(np.int64)
    sel = (P1[:, 2] >= zs0) & (P1[:, 2] < zs0 + W1)
    Pf1, P1 = Pf1[sel], P1[sel]
    fl = P1 // p1
    check('skeleton', np.all((P1[:, 1] - rho1 * P1[:, 0] - fl[:, 2]) % p1 == 0) and
          np.all((P1[:, 2] - rho1 ** 2 * P1[:, 0] - fl[:, 0] - fl[:, 1] + fl[:, 2]) % p1 == 0),
          'B^1 relations P_y = rho P_x + |P_z/p|, P_z = rho^2 P_x + |P_x/p| + |P_y/p| - |P_z/p| (mod p)')
    oref = yblk % p1                                       # coset of block (x_0, z_0) = (0, 0)
    fault = (P1[:, 2] - rho1 ** 2 * P1[:, 0] - oref) % p1
    fault = np.where(fault > p1 // 2, fault - p1, fault)
    check('skeleton', set(fault.tolist()) <= {-1, 0, 1}, f'faults against the continued coset are unit '
                                                        f'({sorted(set(fault.tolist()))})')
    check('skeleton', np.all(fault == fl[:, 0] - fl[:, 2]), 'fault in coarse block (x_0, z_0) equals x_0 - z_0 '
                                                          '(the labels of panel (c))')
    u1, v1 = reduce2((1, rho1 ** 2), (0, p1))

    fig = plt.figure(figsize=(WIDTH, 2.5))
    axs = [fig.add_axes([0.058 + 0.333 * i, 0.185, 0.27, 0.74]) for i in range(3)]
    # (a) one fine layer
    ax = axs[0]
    grid(ax, xa, xa + W, ya, ya + W, lw=0.25)
    Q = P[keep1]
    for (a, b) in Q[:, :2]:
        ax.add_patch(Rectangle((a, b), 1, 1, fc=FINE, ec='none', zorder=1))
    draw_points(ax, Q[:, :2].astype(float), Pf[keep1][:, :2], s_lat=9, s_pt=3.2)
    occ = {tuple(t) for t in Q[:, :2]}
    c0 = min(occ, key=lambda t: (t[0] - xa - 0.42 * W) ** 2 + (t[1] - ya - 0.30 * W) ** 2)
    arrow(ax, c0, u2, ms=5)
    arrow(ax, c0, v2, ms=5)
    label(ax, c0[0] + u2[0] - 1.6, c0[1] + u2[1] + 1.3, r'$(%d,%d)$' % tuple(u2), fs=6.3)
    label(ax, c0[0] + v2[0] + 0.3, c0[1] + v2[1] + 1.5, r'$(%d,%d)$' % tuple(v2), fs=6.3)
    clean(ax, ((xa, xa + W), (ya, ya + W)), ticks=True)
    ax.set_xlabel(r'$P_x$ (fine cells)', labelpad=1); ax.set_ylabel(r'$P_y$', labelpad=0)
    panel_title(ax, r'(a) $\mathcal{B}^2_{1,43,3}$ ($=\mathcal{S}^1$, $s=3$): slab $P_z=%d$' % zstar)
    nlat = sum(1 for a_ in range(xa, xa + W) for b_ in range(ya, ya + W) if (rho * a_ + rho * rho * b_ - zstar) % p == 0)
    check('skeleton', nlat == int(keep1.sum()), f'B^2 layer: every cell of Lambda_2 in the window is occupied '
                                                f'({nlat} = {int(keep1.sum())}): no faults, no skipped sites')
    ax.text(0.97, 0.03, 'no faults, no skips:\nexact lattice $\\Lambda_{\\mathcal{B}^2}$', transform=ax.transAxes, fontsize=5.9, ha='right', va='bottom', zorder=9,
            color=ACC, bbox=dict(fc='white', ec=ACC, lw=0.4, pad=1.6, alpha=0.95))
    # (b) slab of rho layers with rho x rho exclusion squares
    ax = axs[1]
    grid(ax, xa, xa + W, ya, ya + W, lw=0.25)
    greys = ['#5c5c5c', '#9c9c9c', '#d0d0d0']
    PfS = Pf[keepS]
    for (a, b, c) in Ps:
        ax.add_patch(Rectangle((a + 0.5 - rho / 2, b + 0.5 - rho / 2), rho, rho, fc='none', ec='#8f8f8f', lw=0.35,
                               zorder=1))
        ax.add_patch(Rectangle((a, b), 1, 1, fc=greys[c - zstar], ec='none', zorder=2))
    draw_points(ax, Ps[:, :2].astype(float), PfS[:, :2], s_lat=9, s_pt=3.2)
    for i, z in enumerate(layers):
        ax.add_patch(Rectangle((0, 0), 0, 0, fc=greys[i], ec='#808080', lw=0.3, label=r'$P_z=%d$' % z))
    leg = ax.legend(loc='upper right', fontsize=5.6, handletextpad=0.3, borderpad=0.3, labelspacing=0.15,
                    handlelength=0.9, handleheight=0.9, framealpha=0.95, borderaxespad=0.25)
    leg.get_frame().set_linewidth(0.3)
    clean(ax, ((xa, xa + W), (ya, ya + W)), ticks=True)
    ax.set_xlabel(r'$P_x$ (fine cells)', labelpad=1)
    panel_title(ax, r'(b) $\rho=3$ slabs; squares of side $\rho$')
    # (c) B^1: xz-view of one y-block, coset continued from block (0,0), faults
    ax = axs[2]
    grid(ax, xs0, xs0 + W1, zs0, zs0 + W1, lw=0.25)
    ideal_coset = np.array([(a, b) for a in range(xs0, xs0 + W1) for b in range(zs0, zs0 + W1)
                            if (b - rho1 ** 2 * a - oref) % p1 == 0], dtype=float)
    for (a, b), fz in zip(P1[:, [0, 2]], fault):
        ax.add_patch(Rectangle((a, b), 1, 1, fc='#a8a8a8' if fz else FINE, ec='none', zorder=1))
    ax.scatter(ideal_coset[:, 0], ideal_coset[:, 1], s=9, facecolors='none', edgecolors=LATE, linewidths=0.55,
               zorder=3)
    ax.add_collection(LineCollection(np.stack([P1[:, [0, 2]].astype(float), Pf1[:, [0, 2]]], 1), colors=JIT,
                                     linewidths=0.55, zorder=4))
    ax.scatter(Pf1[:, 0], Pf1[:, 2], s=3.2, c=INK, lw=0, zorder=5)
    nf = 0
    for (a, b), fz in zip(P1[:, [0, 2]], fault):
        if fz:
            nf += 1
            arrow(ax, (a, b - fz), (0, fz), lw=0.8, ls=(0, (1.6, 0.9)), ms=4.5)
    ax.axvline(p1, color=INK, lw=0.7, zorder=2); ax.axhline(p1, color=INK, lw=0.7, zorder=2)
    for (bx, bz) in itertools.product((0, 1), (0, 1)):
        sh = bx - bz
        label(ax, p1 + (0.5 if bx else -0.5), p1 + (0.6 if bz else -0.6),
              r'shift $%s$' % ('%+d' % sh if sh else '0'), fs=5.8,
              ha='left' if bx else 'right', va='bottom' if bz else 'top')
    cc = min({(int(a), int(b)) for a, b in P1[:, [0, 2]] if a < p1 and b < p1},
             key=lambda t: (t[0] - (p1 - 0.6 * half)) ** 2 + (t[1] - (p1 - 0.95 * half)) ** 2)
    arrow(ax, cc, u1, ms=5); arrow(ax, cc, v1, ms=5)
    label(ax, cc[0] + u1[0] - 0.4, cc[1] + u1[1] + 1.0, r'$(%d,%d)$' % tuple(u1), fs=6.3)
    label(ax, cc[0] + v1[0] + 0.9, cc[1] + v1[1] + 0.9, r'$(%d,%d)$' % tuple(v1), fs=6.3)
    clean(ax, ((xs0, xs0 + W1), (zs0, zs0 + W1)), ticks=True)
    ax.set_xlabel(r'$P_x$ (fine cells)', labelpad=1); ax.set_ylabel(r'$P_z$', labelpad=0)
    panel_title(ax, r'(c) $\mathcal{B}^1_{1,37,3}$: Korobov $(1,\rho,\rho^2)$, $xz$-view')
    occ1 = set(map(tuple, P1[:, [0, 2]].tolist()))
    shifted = {(a_, b_) for a_ in range(xs0, xs0 + W1) for b_ in range(zs0, zs0 + W1)
               if (b_ - rho1 ** 2 * a_ - oref - (a_ // p1 - b_ // p1)) % p1 == 0}
    check('skeleton', occ1 == shifted, 'B^1 (xz, one y-block): in each coarse block the occupied cells are exactly '
                                       'the Korobov coset shifted by x_0 - z_0 (a coset shift, no skipped sites)')
    ax.text(0.97, 0.03, 'faults = coset shifts by $\\pm1$\nfine cell between blocks', transform=ax.transAxes, fontsize=5.9, ha='right', va='bottom', zorder=9,
            color=ACC, bbox=dict(fc='white', ec=ACC, lw=0.4, pad=1.6, alpha=0.95))
    common_legend(fig, ['grid', 'lat', 'pt', 'jit', 'vec', 'slip'], y=0.0)
    save(fig, 'arc_skeleton')
    return dict(p=p, rho=rho, W=W, xa=xa, ya=ya, zstar=zstar, n1=int(keep1.sum()), nS=int(keepS.sum()),
                u2=tuple(u2), v2=tuple(v2), p1=p1, rho1=rho1, yblk=yblk, W1=W1, nf=nf, u1=tuple(u1), v1=tuple(v1),
                n1c=len(P1), nbox=nbox, nbox1=nbox1)


# ================================================================== arc_large
U1 = np.array([1, -1, 0]) / np.sqrt(2)
U2 = np.array([1, 1, -2]) / np.sqrt(6)
ONE = np.ones(3)
HREF = np.eye(3) - 2.0 / 3.0 * np.outer(ONE, ONE)                 # the reflected cube H = I - (2/3) 1 1^T


def col_row(q):
    """row a = (q 1 + w)/3 of the column net C_q (def:col): w = (-2,1,1) for q = 2, (-1,-1,2) for q = 1 mod 3."""
    assert q % 2 and q % 3
    w = np.array([-2, 1, 1]) if q % 3 == 2 else np.array([-1, -1, 2])
    return (q + w) // 3


def col_c(q):
    """exact delta N^{1/3} of C_q (thm:col(2)): c^2 = 2/3 + (tau/q^2)^2/3."""
    q = np.asarray(q, float)
    tau = np.where(np.round(q) % 3 == 2, q * q - q - 3, q * q - 2 * q)
    return np.sqrt(2 / 3 + (tau / q ** 2) ** 2 / 3)


def hz3_ideal(X, cells, sig0, t0):
    """anchored H Z^3 position of each cell: n + (t0 + (sigma(n)-sigma0)/3) 1, shifted by an integer multiple of 1
    (1 = -H 1 lies in H Z^3) to be nearest to the actual point."""
    t = t0 + (cells.sum(1) - sig0) / 3.0
    base = cells + t[:, None] * ONE
    shift = np.rint(((X - base) @ ONE) / 3.0)
    return base + shift[:, None] * ONE


def fig_large():
    # ---- (a) the column net C_p, p = 13 (def:col, thm:col): rows e_c, a, l = (-1,1,0); a = (p 1 + w)/3, w = (-1,-1,2)
    p = 13
    arow = col_row(p)
    wvec = 3 * arow - p
    lrow = np.array([-1, 1, 0])
    e = np.eye(3, dtype=np.int64)
    CE = [[e[c].tolist(), arow.tolist(), lrow.tolist()] for c in range(3)]
    E1 = DNet(CE, p, [1, 1, 1])
    ok, nbox = E1.t0()
    check('large', ok, f'C_{p} is a (0,3,3)-net: all {nbox} boxes full rank (thm:col(1))')
    allc = np.stack(np.meshgrid(*(np.arange(p),) * 3, indexing='ij'), -1).reshape(-1, 3)
    XA_, D = E1.eval(allc)
    check('large', np.all(E1.geo(D) == ((allc @ arow) % p)[:, None]),
          f'C_{p}: every coordinate reads the same geometric digit a.n mod p (a={arow.tolist()}; def:col)')
    check('large', all(np.all(D[c][:, 2] == (allc @ lrow) % p) for c in range(3)),
          f'C_{p}: the third digit of every coordinate is n_y - n_x (shared; def:col)')
    offs = XA_ - allc
    check('large', np.allclose(offs, offs[:, :1]), f'C_{p}: every point lies on the body diagonal of its cell (column point set)')
    # anchor: cell with geometric digit h0 = 1, interior
    n0 = next(np.array(c) for c in itertools.product(range(3, 9), repeat=3)
              if (np.array(c) @ arow) % p == 1 and (c[1] - c[0]) % p == 0)
    sig0, t0 = int(n0.sum()), 1.0 / p
    blk = n0 + np.stack(np.meshgrid(*(np.arange(-1, 2),) * 3, indexing='ij'), -1).reshape(-1, 3)
    XE, _ = E1.eval(blk)
    IE = hz3_ideal(XE, blk, sig0, t0)
    devE = np.abs(XE - IE).max()
    check('large', devE < (np.abs(wvec).sum() / 3 + 1) / p + 1e-9,
          f'C_{p}: 3x3x3 block within (||w||_1/3+1)/p of the anchored H Z^3 (max dev {devE:.3f})')
    check('large', np.allclose(XE - IE, ((XE - IE) @ ONE / 3)[:, None] * ONE[None, :]),
          f'C_{p}: drift and jitter run along (1,1,1) only')
    c_i = int(np.where((blk == n0).all(1))[0][0])
    dd = np.linalg.norm(IE - IE[c_i], axis=1)
    nn = np.where((dd > 1e-9) & (dd < 1 + 1e-9))[0]
    nnvec = IE[nn] - IE[c_i]
    check('large', len(nn) == 6 and np.allclose(sorted(map(tuple, np.round(nnvec, 9))),
                                                 sorted(map(tuple, np.round(np.vstack([HREF, -HREF]), 9)))),
          'nearest neighbours of the anchor in the lattice image are exactly +-H e_i = +-(e_i - (2/3)1)')
    # one site of the anchored H Z^3 per cell of the block: no skipped sites (covolume 1, one site per diagonal)
    Z = np.array(list(itertools.product(range(-5, 6), repeat=3)))
    sites = IE[c_i] + Z @ HREF.T
    inb = np.all((sites >= blk.min(0)) & (sites < blk.max(0) + 1), axis=1)
    cnt = {}
    for c_ in map(tuple, np.floor(sites[inb]).astype(int)):
        cnt[c_] = cnt.get(c_, 0) + 1
    check('large', len(cnt) == len(blk) and set(cnt.values()) == {1},
          f'anchored H Z^3 has exactly one site in each of the {len(blk)} cells of the block: no skipped sites')
    # ---- (b) E_p itself, view along (1,1,1): three sheets around the anchor
    rad = 2
    blk2 = n0 + np.stack(np.meshgrid(*(np.arange(-rad, rad + 1),) * 3, indexing='ij'), -1).reshape(-1, 3)
    XS, _ = E1.eval(blk2)
    IS = hz3_ideal(XS, blk2, sig0, t0)
    devS = np.abs(XS - IS).max()
    check('large', devS < 0.5, f'C_{p}: 5^3 block near the anchored H Z^3 (max dev {devS:.3f}, no slip)')
    cS = int(np.where((blk2 == n0).all(1))[0][0])
    rel = IS - IS[cS]
    hgt = rel @ ONE / np.sqrt(3)
    tr = np.stack([rel @ U1, rel @ U2], 1)
    sel = (np.abs(hgt) < 0.8) & (np.linalg.norm(tr, axis=1) < 1.75)
    sheet = np.rint(hgt * np.sqrt(3)).astype(int)
    devS = np.abs(XS[sel] - IS[sel]).max()                       # over the drawn points
    check('large', devS < (np.abs(wvec).sum() * rad / 3 + 1) / p + 1e-9,
          f'C_{p} along (1,1,1): every drawn point ({int(sel.sum())}) within {devS:.3f} (per coordinate) of its site '
          f'of the anchored H Z^3 (<= (||w||_1 |E|/3+1)/p)')
    prd = np.stack([(XS[sel] - IS[sel]) @ U1, (XS[sel] - IS[sel]) @ U2], 1)
    check('large', np.abs(prd).max() < 1e-12, f'C_{p} along (1,1,1): every drawn point projects exactly onto its site')
    # ---- (c) the split-frame design H5* (prop:HL5) at k = 1 (m = s = 5), p = 10007: prop:Hk with k = 1
    path5 = os.path.join(HERE, 'llg_s5_design.json')
    W5d = json.load(open(path5))
    s5, F25 = W5d['s'], np.array(W5d['F2'])
    check('large', W5d['u'] == [-2, 0, 2, 4, 8] and W5d['v'] == [5, 7, -1, 3, 1] and np.all(F25[0] % 2 == 1),
          'llg_s5_design.json = H5* of prop:HL5; 2F_0 odd (F_0 in 1/2 + Z)')
    k5, q5 = 1, 10007
    _, C5 = llg_dump.build(path5, k5)
    H5 = DNet(llg_lib.to_mod(C5, q5), q5, [k5] * s5)
    ok5, nbox5 = H5.t0()
    check('large', ok5, f'H5* at k={k5} is a (0,{s5 * k5},{s5})-net over F_{q5}: all {nbox5} boxes full rank')
    half5 = (q5 + 1) // 2
    check('large', all(H5.C[c][1, d] == (int(F25[0][c][d]) * half5) % q5 for c in range(s5) for d in range(s5)),
          f'H5* at k={k5}: row 0 of the graph form = F_0 (level 0), entries in 1/2 + Z mod {q5}')
    rng = np.random.default_rng(6)
    W6 = 8
    for trial in range(20000):
        n06 = rng.integers(W6, q5 - W6, size=s5)
        X0, D0 = H5.eval(n06[None])
        c0 = H5.geo(D0)[0] / q5
        if not (0.07 <= c0[0] <= 0.13 and 0.07 <= c0[1] <= 0.13):
            continue
        cells6 = window(n06[0] - 3, n06[1] - 3, W6, rest=tuple(n06[2:]))
        X6, D6 = H5.eval(cells6)
        par = (cells6.sum(1) - n06.sum()) % 2
        I6 = cells6 + c0[None, :] + 0.5 * par[:, None]
        dev6 = X6 - I6
        if np.abs(dev6).max() < 0.2:
            break
    else:
        raise AssertionError('no slip-free half-integer window found')
    check('large', True, f'H5* slice (k={k5}, q={q5}): every drawn point within {np.abs(dev6).max():.3f} of the '
                         f'anchored D_5^+ position n + c0 + (1/2)[sigma(n)-sigma0 odd] 1')
    ia = int(np.where((cells6 == n06).all(1))[0][0])
    # one site of the anchored D_5^+ per cell of the slice: sites I6[ia] + m (sigma(m) even) or + m + 1/2 1 (odd)
    base = I6[ia]
    rngs = [range(-4, 6)] * 2 + [range(-1, 2)] * (s5 - 2)
    cnt6 = {}
    for mvec in itertools.product(*rngs):
        mv = np.array(mvec, float)
        site = base + mv + (0.5 if sum(mvec) % 2 else 0.0)
        c_ = tuple(np.floor(site).astype(int))
        if c_[2:] == tuple(n06[2:]) and cells6[:, 0].min() <= c_[0] <= cells6[:, 0].max() and \
                cells6[:, 1].min() <= c_[1] <= cells6[:, 1].max():
            cnt6[c_] = cnt6.get(c_, 0) + 1
    check('large', len(cnt6) == len(cells6) and set(cnt6.values()) == {1},
          f'anchored D_5^+ has exactly one site in each of the {len(cells6)} cells of the slice: no skipped sites')
    vecs = I6 - I6[ia]
    lens = np.linalg.norm(vecs, axis=1)
    check('large', abs(np.sort(lens)[1] - np.sqrt(s5) / 2) < 1e-12,
          'shortest lattice-image vector in the slice has length sqrt(5)/2 = min(sqrt(s)/2, sqrt 2) (D_5^+)')

    fig = plt.figure(figsize=(WIDTH, 3.0))
    # (a) 3D: points on the cell diagonals at heights {sigma/3}
    ax = fig.add_axes([-0.02, 0.15, 0.37, 0.74], projection='3d', proj_type='ortho')
    lo = n0 - 1
    for i in (0, 3):
        for j in (0, 3):
            for (P0, P1_) in (((0, i, j), (3, i, j)), ((i, 0, j), (i, 3, j)), ((i, j, 0), (i, j, 3))):
                ax.plot(*np.stack([lo + np.array(P0), lo + np.array(P1_)], 1), color=GRID, lw=0.5)
    for c in blk:                                   # every cell's body diagonal: the point sits on it
        ax.plot(*np.stack([c, c + 1], 1), color='#a8a8a8', lw=0.5, ls=(0, (1, 1.4)))
    ax.scatter(*IE.T, s=14, facecolors='none', edgecolors=LATE, linewidths=0.55, depthshade=False)
    for P0, P1_ in zip(IE, XE):
        ax.plot(*np.stack([P0, P1_], 1), color=JIT, lw=0.55)
    ax.scatter(*XE.T, s=5, c=INK, lw=0, depthshade=False)
    for v in nnvec:
        ax.plot(*np.stack([IE[c_i], IE[c_i] + v], 1), color=ACC, lw=1.2)
    ax.view_init(elev=24, azim=-58)
    ax.set_box_aspect((1, 1, 1), zoom=1.25)
    ax.set_axis_off()
    fig.text(0.165, 0.885, r'(a) $\mathcal{C}_{13}$: $3^3$ cells, diagonals', ha='center', fontsize=7.5)
    fig.text(0.165, 0.105, 'one lattice site per cell: no skipped sites', ha='center', fontsize=5.9, color=ACC,
             bbox=dict(fc='white', ec=ACC, lw=0.4, pad=1.6, alpha=0.95))
    # (b) along (1,1,1)
    ax = fig.add_axes([0.355, 0.165, 0.30, 0.70])
    o = XS[cS]
    fills = {-1: '#d6d6d6', 0: 'white', 1: '#7a7a7a'}
    for sh in (-1, 0, 1):
        mk = sel & (sheet == sh)
        pr = np.stack([(IS[mk] - IS[cS]) @ U1, (IS[mk] - IS[cS]) @ U2], 1)
        ax.scatter(pr[:, 0], pr[:, 1], s=34, facecolors=fills[sh], edgecolors=LATE, linewidths=0.6, zorder=3)
    prA = np.stack([(XS[sel] - IS[cS]) @ U1, (XS[sel] - IS[cS]) @ U2], 1)
    prI = np.stack([(IS[sel] - IS[cS]) @ U1, (IS[sel] - IS[cS]) @ U2], 1)
    ax.add_collection(LineCollection(np.stack([prI, prA], 1), colors=JIT, linewidths=0.55, zorder=4))
    ax.scatter(prA[:, 0], prA[:, 1], s=6, c=INK, lw=0, zorder=5)
    for i, v in enumerate(np.vstack([-HREF, HREF])):             # b_c = (2/3)1 - e_c = -H e_c: one sheet UP
        pv = np.array([v @ U1, v @ U2])
        arrow(ax, (0, 0), pv, lw=1.1, ms=6)
        if i < 3:
            nm = 'xyz'[i]
            label(ax, 1.36 * pv[0], 1.36 * pv[1], r'$b_{%s}$' % nm, fs=6.8)
    check('large', np.allclose(-HREF @ ONE / np.sqrt(3), 1 / np.sqrt(3)) and
          np.allclose(np.stack([(-HREF[i]) @ U1 for i in range(3)]), -np.stack([np.eye(3)[i] @ U1 for i in range(3)])),
          'b_c = (2/3)1 - e_c rises one sheet and projects opposite to e_c (the reflected cube)')
    # cell axes for comparison (projected), lower-left inset
    oc = np.array([-1.45, -1.42])
    for i, nm in enumerate('xyz'):
        pv = 0.42 * np.array([np.eye(3)[i] @ U1, np.eye(3)[i] @ U2])
        arrow(ax, oc, pv, col='#7a7a7a', lw=0.7, ms=4.5)
        ax.text(oc[0] + 1.35 * pv[0], oc[1] + 1.35 * pv[1], r'$e_{%s}$' % nm, fontsize=5.8, color='#5a5a5a',
                ha='center', va='center')
    lh = [Line2D([], [], ls='none', marker='o', ms=4.6, mfc=fills[s_], mec=LATE, mew=0.6, label=lb)
          for s_, lb in ((1, r'one plane up ($+1/\sqrt{3}$)'), (0, 'same plane'), (-1, 'one plane down'))]
    leg = ax.legend(handles=lh, loc='upper center', bbox_to_anchor=(0.5, 1.0), ncol=1, fontsize=5.5,
                    framealpha=0.95, borderpad=0.3, labelspacing=0.15, handletextpad=0.2, borderaxespad=0.2)
    leg.get_frame().set_linewidth(0.3)
    clean(ax, ((-1.8, 1.8), (-1.85, 2.45)))
    ax.text(0.97, 0.03, 'one site per cell', transform=ax.transAxes, fontsize=5.9, ha='right', va='bottom', zorder=9,
            color=ACC, bbox=dict(fc='white', ec=ACC, lw=0.4, pad=1.6, alpha=0.95))
    panel_title(ax, r'(b) $\mathcal{C}_{13}$, $5^3$ cells: along $(1,1,1)$')
    # (c) half-integer slice
    ax = fig.add_axes([0.675, 0.165, 0.32, 0.70])
    xw0, yw0 = cells6[:, 0].min(), cells6[:, 1].min()
    for (cx, cy), pr in zip(cells6[:, :2], par):
        if pr:
            ax.add_patch(Rectangle((cx, cy), 1, 1, fc='#ededed', ec='none', zorder=0))
    grid(ax, xw0, xw0 + W6, yw0, yw0 + W6)
    draw_points(ax, I6[:, :2], X6[:, :2], s_lat=24, s_pt=7)
    oa = I6[ia, :2]
    order = np.argsort(lens)
    short = [i for i in order if abs(lens[i] - np.sqrt(s5) / 2) < 1e-9]
    diag = [i for i in order if abs(lens[i] - np.sqrt(2)) < 1e-9]
    dg = [i for i in diag if abs(abs(vecs[i, 0] * vecs[short[0], 1] - vecs[i, 1] * vecs[short[0], 0])) > 1e-9][0]
    for i in short + [dg]:
        arrow(ax, oa, vecs[i, :2], lw=1.1, ms=6)
    for i in short:
        vs = vecs[i, :2]
        label(ax, oa[0] + 1.85 * vs[0], oa[1] + 1.85 * vs[1], r'$\frac{\sqrt{5}}{2}$', fs=7)
    vd = vecs[dg, :2]
    label(ax, oa[0] + 1.18 * vd[0], oa[1] + 1.18 * vd[1], r'$\sqrt{2}$', fs=7)
    clean(ax, ((xw0, xw0 + W6), (yw0, yw0 + W6)))
    panel_title(ax, r'(c) $\mathcal{H}^{5*}_{1,p}$, $m=s=5$, $p=10007$: $D_5^+$')
    ax.text(0.5, -0.015, 'one site per cell: no skips; drift + jitter $O(1/p)$', transform=ax.transAxes, fontsize=5.9, ha='center', va='top', zorder=9,
            color=ACC, bbox=dict(fc='white', ec=ACC, lw=0.4, pad=1.6, alpha=0.95))
    common_legend(fig, ['grid', 'lat', 'pt', 'jit', 'vec'], y=0.0)
    save(fig, 'arc_large')
    return dict(p=p, a=arow.tolist(), w=wvec.tolist(), n0=n0.tolist(), devE=devE, devS=devS, s5=s5, q5=q5, k5=k5, W6=W6,
                n06=n06.tolist(), c06=c0[:2].tolist(), dev6=np.abs(dev6).max(), nbox5=nbox5,
                nsel=int(sel.sum()))


# ================================================================== arc_split
def fig_split():
    path = os.path.join(HERE, 'llg_s5_design.json')
    Wd = json.load(open(path))
    s, u, v = Wd['s'], Wd['u'], Wd['v']
    F2 = np.array(Wd['F2'])                                        # 2 F_n
    check('split', u == [-2, 0, 2, 4, 8] and v == [5, 7, -1, 3, 1], 'llg_s5_design.json = split frame of prop:HL5')
    tau = np.array([[u[c] - v[d] for d in range(s)] for c in range(s)])
    check('split', np.all(tau % 2 == 1) and all(x % 2 == 0 for x in u) and all(x % 2 == 1 for x in v),
          'u even, v odd => every tau_cd = u_c - v_d is odd')
    check('split', np.all(F2[0] % 2 == 1) and np.all(F2[1:] % 2 == 0),
          '(Half): 2F_0 odd (F_0 in 1/2+Z), 2F_x even (F_x integral) for x >= 1')
    # the design is reachable on the split frame (prop:Gsplit): the gauge solve succeeds and row 0 = design
    k, q = 2, 10007
    s_, C = llg_dump.build(path, k)
    Cq = llg_lib.to_mod(C, q)
    net = DNet(Cq, q, [k] * s)
    ok, nbox = net.t0()
    check('split', ok, f'H5* (k={k}) is a (0,{s * k},{s})-net over F_{q}: all {nbox} boxes full rank')
    half = (q + 1) // 2
    for c in range(s):
        for d in range(s):
            assert net.C[c][k, d * k + k - 1] == (int(F2[0][c][d]) * half) % q
            assert net.C[c][k, d * k + k - 2] == (int(F2[1][c][d]) * half) % q
    check('split', True, 'row 0 of the gauged split-frame graph form = (F_0, F_1) of H5* (levels k-1, k-2)')
    # Cauchy form of the level-0 layer: off-diagonal F_0[c][d] * (u_c - v_d) / lambda'_c depends on d only?
    # (prop:Gsplit: M^(0) = lambda'_c mu_d / (u_c - v_d)); check the rank-one structure of F_0 * tau off the diagonal
    R = np.array([[Fr(int(F2[0][c][d]), 2) * int(tau[c][d]) for d in range(s)] for c in range(s)], dtype=object)
    rk1 = all(R[c][d] * R[c2][d2] == R[c][d2] * R[c2][d] for c in range(s) for c2 in range(s) for d in range(s)
              for d2 in range(s) if len({c, d}) == 2 and len({c2, d2}) == 2 and len({c, d2}) == 2 and len({c2, d}) == 2)
    check('split', rk1, 'level-0 layer is Cauchy: F_0[c][d] = lambda_c mu_d / (u_c - v_d) off the diagonal')
    # net slice across carries
    G = q ** k
    rng = np.random.default_rng(5)
    W = 10
    for trial in range(40000):
        jx, jy = rng.integers(2, q - 2, size=2)
        rest = rng.integers(0, G, size=s - 2)
        X0c, Y0c = jx * q - 4, jy * q - 5                        # the last cell digit of x (y) wraps inside
        n0 = np.array([X0c + 3, Y0c + 3] + rest.tolist())
        _, D0 = net.eval(n0[None])
        c0 = net.geo(D0)[0] / q
        if not (0.07 <= c0[0] <= 0.13 and 0.07 <= c0[1] <= 0.13):
            continue
        cells = window(X0c, Y0c, W, rest=tuple(rest))
        X, D = net.eval(cells)
        par = (cells.sum(1) - n0.sum()) % 2
        I = cells + c0[None, :] + 0.5 * par[:, None]
        dev = X - I
        if np.abs(dev).max() < 0.15:
            break
    else:
        raise AssertionError('no slip-free split window found')
    carry_x = [t for t in range(X0c + 1, X0c + W) if t % q == 0]
    carry_y = [t for t in range(Y0c + 1, Y0c + W) if t % q == 0]
    check('split', len(carry_x) == 1 and len(carry_y) == 1 and np.abs(dev).max() < 0.15,
          f'H5* slice (q={q}, k=2) crosses a carry in x and in y and stays within {np.abs(dev).max():.3f} of the '
          f'anchored D_5^+ parity pattern (prop:Hk: M^(j) in 1/2+Z at every carry length)')
    ia = int(np.where((cells == n0).all(1))[0][0])
    vecs = I - I[ia]
    lens = np.linalg.norm(vecs, axis=1)
    check('split', abs(np.sort(lens)[1] - np.sqrt(5) / 2) < 1e-12, 'shortest vector in the slice: sqrt(5)/2 (D_5^+)')

    fig = plt.figure(figsize=(WIDTH, 4.0))
    # (a) places on the line: frame vs split frame
    ax = fig.add_axes([0.0, 0.645, 1.0, 0.30])
    ax.set_xlim(-4.2, 16.8); ax.set_ylim(-1.0, 1.9); ax.axis('off')
    yF, yS = 1.4, -0.25
    for yy in (yF, yS):
        ax.plot([-3.4, 9.5], [yy, yy], color='#9a9a9a', lw=0.6, zorder=0)
        for t in range(-3, 10):
            ax.plot([t, t], [yy - 0.07, yy + 0.07], color='#9a9a9a', lw=0.4)
            if yy == yS:
                ax.text(t, yy + 0.13, r'$%d$' % t, fontsize=5.2, color='#8a8a8a', ha='center', va='bottom')
    ax.text(-4.1, yF, 'frame', fontsize=7, ha='left', va='center')
    ax.text(-4.1, yS, 'split', fontsize=7, ha='left', va='center')
    ax.plot([9.5, 9.85], [yF, yF], color='#9a9a9a', lw=0.6, ls=(0, (1, 1)))
    for c, a_ in enumerate([0, 1, 2, 3, None]):
        xx = 10.2 if a_ is None else a_
        ax.scatter([xx], [yF], marker='s', s=26, c='#5a5a5a', edgecolors=INK, linewidths=0.5, zorder=3)
        ax.scatter([xx], [yF], marker='s', s=80, facecolors='none', edgecolors=INK, linewidths=0.5, zorder=3)
        ax.text(xx, yF - 0.3, r'$a_{%d}%s$' % (c, r'=\infty' if a_ is None else ''), fontsize=6.3,
                ha='center', va='top')
    for c in range(s):
        ax.scatter([v[c]], [yS], marker='s', s=30, c='#5a5a5a', edgecolors=INK, linewidths=0.5, zorder=3)
        ax.scatter([u[c]], [yS], marker='s', s=30, facecolors='white', edgecolors=INK, linewidths=0.6, zorder=3)
        ax.text(v[c], yS - 0.27, r'$v_{%d}$' % c, fontsize=6.6, ha='center', va='top')
        ax.text(u[c], yS - 0.27, r'$u_{%d}$' % c, fontsize=6.6, ha='center', va='top')
    for (cH, dH) in ((2, 0), (4, 1)):                              # two Cauchy entries tau_cd = u_c - v_d
        lo_, hi_ = sorted((u[cH], v[dH]))
        xs_ = np.linspace(lo_, hi_, 40)
        hh = 0.16 + 0.05 * (hi_ - lo_)
        ax.plot(xs_, yS + 0.36 + hh * np.sin(np.pi * (xs_ - lo_) / (hi_ - lo_)), color=ACC, lw=0.9)
        ax.text((lo_ + hi_) / 2, yS + 0.42 + hh, r'$\vartheta_{%d%d}=%d$' % (cH, dH, tau[cH][dH]),
                fontsize=6.4, color=ACC, ha='center', va='bottom',
                bbox=dict(fc='white', ec='none', pad=0.2, alpha=0.9))
    ax.text(10.9, yF, r'cell and offset of $c$ at one place $a_c$;' + '\n' +
            r'layer $\lambda_c\mu_d/(a_c-a_d)$: Pl$\ddot{\rm u}$cker' + '\n' +
            r'relations $\Rightarrow$ never all in $\frac{1}{2}+\mathbb{Z}$ (Prop. P)',
            fontsize=6.3, ha='left', va='center', linespacing=1.3)
    ax.text(10.9, yS - 0.05, r'cell of $c$ at $v_c$ (odd, filled), offset at $u_c$' + '\n' +
            r'(even, open); layer $\lambda^\prime_c\mu_d/(u_c-v_d)$:' + '\n' +
            r'all $\vartheta_{cd}$ odd $\Rightarrow$ $\frac{1}{2}+\mathbb{Z}$ possible (Lem. Hs)',
            fontsize=6.3, ha='left', va='center', linespacing=1.3)
    fig.text(0.012, 0.975, r'(a) places: a frame, and the split frame of $H_5^*$ (Prop. HL5)', fontsize=7.5,
             va='top')
    # (b) the matrices tau and 2 F_0
    axl = fig.add_axes([0.045, 0.13, 0.20, 0.36])
    axr = fig.add_axes([0.285, 0.13, 0.20, 0.36])
    for axm, Mat, ttl in ((axl, tau, r'$\vartheta_{cd}=u_c-v_d$ (all odd)'), (axr, F2[0], r'$2F_0$ (all odd)')):
        for c in range(s):
            for d in range(s):
                if c == d:
                    axm.add_patch(Rectangle((d, s - 1 - c), 1, 1, fc='#eeeeee', ec='none'))
                axm.text(d + 0.5, s - 0.5 - c, r'$%d$' % Mat[c][d], fontsize=6.4, ha='center', va='center')
        for t in range(s + 1):
            axm.plot([t, t], [0, s], color=GRID, lw=0.4); axm.plot([0, s], [t, t], color=GRID, lw=0.4)
        axm.set_xlim(-0.05, s + 0.05); axm.set_ylim(-0.05, s + 0.05); axm.set_aspect('equal'); axm.axis('off')
        axm.set_title(ttl, fontsize=7, pad=2)
        for c in range(s):
            axm.text(-0.12, s - 0.5 - c, r'$%d$' % c, fontsize=5.6, ha='right', va='center', color='#606060')
            axm.text(c + 0.5, -0.1, r'$%d$' % c, fontsize=5.6, ha='center', va='top', color='#606060')
    fig.text(0.012, 0.565, r'(b) the geometric layer: $F_0[c][d]=\lambda^\prime_c\mu_d/\vartheta_{cd}\in\frac{1}{2}+\mathbb{Z}$'
                           r' $(c\neq d)$', fontsize=7.5, ha='left')
    fig.text(0.265, 0.088, r'row $c$, column $d$; the diagonal of $F_0$ (shaded) is free, not of Cauchy form',
             fontsize=6.0, ha='center', color='#505050')
    # (c) the net at k = 2
    ax = fig.add_axes([0.53, 0.085, 0.46, 0.505])
    for (cx, cy), pr in zip(cells[:, :2], par):
        if pr:
            ax.add_patch(Rectangle((cx, cy), 1, 1, fc='#ededed', ec='none', zorder=0))
    grid(ax, X0c, X0c + W, Y0c, Y0c + W)
    for t in carry_x:
        ax.plot([t, t], [Y0c, Y0c + W], color=INK, lw=0.6, ls=(0, (0.6, 1.4)), zorder=1)
    for t in carry_y:
        ax.plot([X0c, X0c + W], [t, t], color=INK, lw=0.6, ls=(0, (0.6, 1.4)), zorder=1)
    draw_points(ax, I[:, :2], X[:, :2], s_lat=22, s_pt=6.5)
    oa = I[ia, :2]
    order = np.argsort(lens)
    short = [i for i in order if abs(lens[i] - np.sqrt(5) / 2) < 1e-9]
    diag = [i for i in order if abs(lens[i] - np.sqrt(2)) < 1e-9]
    dg = [i for i in diag if abs(abs(vecs[i, 0] * vecs[short[0], 1] - vecs[i, 1] * vecs[short[0], 0])) > 1e-9][0]
    for i in short + [dg]:
        arrow(ax, oa, vecs[i, :2], lw=1.1, ms=6)
    for i in short:
        vs = vecs[i, :2]
        label(ax, oa[0] + 1.85 * vs[0], oa[1] + 1.85 * vs[1], r'$\frac{\sqrt{5}}{2}$', fs=7)
    vd = vecs[dg, :2]
    label(ax, oa[0] + 1.18 * vd[0], oa[1] + 1.18 * vd[1], r'$\sqrt{2}$', fs=7)
    label(ax, carry_x[0] + 0.08, Y0c + W - 0.35, 'carry', col=INK, fs=6.0, ha='left')
    label(ax, X0c + W - 0.08, carry_y[0] + 0.3, 'carry', col=INK, fs=6.0, ha='right')
    clean(ax, ((X0c, X0c + W), (Y0c, Y0c + W)))
    panel_title(ax, r'(c) $\mathcal{H}^{5*}_{2,p}$, $p=10007$: $xy$-slice; $D_5^+$ across carries')
    common_legend(fig, ['grid', 'lat', 'pt', 'jit', 'vec'], y=0.0)
    save(fig, 'arc_split')
    return dict(u=u, v=v, k=k, q=q, W=W, nbox=nbox, dev=np.abs(dev).max(), X0=int(X0c), Y0=int(Y0c),
                carry=(carry_x[0], carry_y[0]), c0=c0[:2].tolist(), rest=rest.tolist())


# ================================================================== arc_gk2d
def gk_points(r):
    """Gruenschloss-Keller even-m permutation (0,2r,2)-net (GK09 Sec. 3, gendiag0m2.h, Rud26 Challenge.lean):
    X = (R rev_r(k) + floor(k/4) + (R/4)(j+1)) mod N, Y = k + R j (integer grid, N = R^2)."""
    R = 1 << r
    N = R * R
    k, j = np.meshgrid(np.arange(R), np.arange(R), indexing='ij')
    k, j = k.ravel(), j.ravel()
    rv = np.zeros_like(k)
    for i in range(r):
        rv |= ((k >> i) & 1) << (r - 1 - i)
    X = (R * rv + k // 4 + (R // 4) * (j + 1)) % N
    Y = k + R * j
    return X, Y, k, j, rv, R, N


def fig_gk2d():
    r = 4
    X, Y, k, j, u, R, N = gk_points(r)
    m = 2 * r
    # t = 0: every elementary box of area 1/N holds exactly one point
    nbox = 0
    for dx in range(m + 1):
        dy = m - dx
        ids = (X >> (m - dx)) * (1 << dy) + (Y >> (m - dy))
        assert len(np.unique(ids)) == N, (dx, dy)
        nbox += 1
    check('gk2d', True, f'GK net r={r} (N={N}) is a (0,{m},2)-net: all {nbox} box shapes hold one point per box')
    # line form: (X,Y) = u e + (j + rev(u)/R) v + (R/4 + floor(k/4) - k/4, 0), e = (R,0), v = (R/4,R), k = rev(u)
    Fx = [Fr(R * int(uu)) + (int(jj) + Fr(int(kk), R)) * Fr(R, 4) for uu, jj, kk in zip(u, j, k)]
    dev = [Fr(int(x)) - fx - Fr(R, 4) for x, fx in zip(X, Fx)]
    dev = [((d + N // 2) % N) - N // 2 for d in dev]               # X modulo N
    check('gk2d', all(-1 < d <= 0 for d in dev) and np.all(Y == k + R * j),
          '(X,Y) = u e + (j + rev(u)/R) v + (R/4, 0) + (d, 0) with d in (-1, 0] grid units (line/phase form)')
    a, b = X >> (r - 2), Y >> r                                      # depths (r+2, r)
    check('gk2d', np.all((a - b - 1) % 4 == 0) and len(set(zip(a.tolist(), b.tolist()))) == N,
          'occupied (r+2, r) cells are exactly the coset a = b + 1 (mod 4) (N cells of N)')
    # exact separation in GK's row-shifted tiling <(N,0),(N/4,N)>
    P = np.stack([X, Y], 1).astype(np.int64)
    D = P[:, None, :] - P[None, :, :]
    best = None
    for aa in (-1, 0, 1):
        for bb in (-1, 0, 1):
            t = np.array([aa * N + bb * N // 4, bb * N])
            d2 = ((D + t) ** 2).sum(-1)
            if aa == 0 and bb == 0:
                np.fill_diagonal(d2, 10 ** 12)
            best = d2.min() if best is None else min(best, d2.min())
    bound = 4 / np.sqrt(17) * (1 - 1 / R)
    check('gk2d', best == 241 and np.sqrt(best) / R >= bound,
          f'exact tiling minimum delta^2 N = {best}/256 = 241/256 (Rud26) >= bound ((4/sqrt17)(1-1/R))^2')
    # cell units
    act = np.stack([X / R, Y / R], 1)
    img = np.stack([(u + (j + 1) / 4.0) % R, j.astype(float)], 1)   # lattice image: u e + j v + (1/4, 0)
    dlt = act - img
    dlt[:, 0] = (dlt[:, 0] + R / 2) % R - R / 2
    check('gk2d', np.allclose(dlt[:, 1], k / R) and np.all(np.abs(dlt[:, 0] - k / (4 * R)) < 1 / R),
          'actual - lattice image = (rev(u)/R) v + (< 1 grid unit), rev(u) = k: a van der Corput slide along the line')

    fig = plt.figure(figsize=(WIDTH, 3.25))
    axa = fig.add_axes([0.02, 0.11, 0.47, 0.76])
    axb = fig.add_axes([0.52, 0.11, 0.47, 0.76])
    for ax, (x0, x1, y0, y1), sp, sl in ((axa, (0, R, 0, R), 3.5, 11), (axb, (5, 11, 4, 10), 14, 40)):
        if ax is axb:
            grid(ax, x0, x1, y0, y1, step=0.25, color=FINE, lw=0.3, z=-1)
            for (aa, bb) in zip(a, b):
                xx, yy = aa / 4.0, float(bb)
                if x0 <= xx < x1 and y0 <= yy < y1:
                    ax.add_patch(Rectangle((xx, yy), 0.25, 1, fc='#e6e6e6', ec='none', zorder=0))
        grid(ax, x0, x1, y0, y1, lw=0.45 if ax is axb else 0.3)
        segs = []                                                   # the lines u e + R v (+ (1/4,0)), mod R in x
        for uu in range(R):
            for t in range(R):
                xa = (uu + 0.25 + t / 4.0) % R
                segs.append([(xa, t), (xa + 0.25, t + 1)])
        ax.add_collection(LineCollection(segs, colors='#9a9a9a', linewidths=0.4, linestyles=[(0, (3, 1.5))],
                                         zorder=1))
        sel = (img[:, 0] >= x0 - 1) & (img[:, 0] < x1) & (img[:, 1] >= y0 - 1) & (img[:, 1] < y1)
        draw_points(ax, img[sel], img[sel] + dlt[sel], s_lat=sl, s_pt=sp)
        clean(ax, ((x0, x1), (y0, y1)))
    # (a) annotations: shortest vector e, basis v, line spacing
    i0 = int(np.where((u == 3) & (j == 5))[0][0])
    o = img[i0]
    arrow(axa, o, (1, 0), lw=1.2)
    arrow(axa, o, (0.25, 1), lw=1.2)
    label(axa, o[0] + 0.5, o[1] - 0.45, r'$e$', fs=7)
    label(axa, o[0] - 0.3, o[1] + 0.75, r'$v$', fs=7)
    panel_title(axa, r'(a) $m=8$, $R=16$: $(r,r)$ cells, lines of $\Lambda=\langle e,v\rangle$')
    # (b) annotations: line spacing 4/sqrt17 and the coset
    i1 = int(np.where((u == 7) & (j == 6))[0][0])
    o = img[i1]
    nrm = np.array([4.0, -1.0]) / np.sqrt(17)                       # unit normal to v = (1/4, 1)
    gap = 4 / np.sqrt(17)
    axb.annotate('', xy=(o[0] + gap * nrm[0], o[1] + gap * nrm[1]), xytext=(o[0], o[1]),
                 arrowprops=dict(arrowstyle='<|-|>', color=ACC, lw=0.9, mutation_scale=6, shrinkA=0, shrinkB=0),
                 zorder=7)
    label(axb, o[0] + 0.5 * gap * nrm[0] + 0.12, o[1] + 0.5 * gap * nrm[1] - 0.32, r'$4/\sqrt{17}$', fs=7)
    arrow(axb, img[i1] + np.array([0, 1.0]) * 0 + np.array([-0.0, 0.0]), (1, 0), lw=1.2)
    label(axb, o[0] + 0.5, o[1] + 0.2, r'$e$', fs=7)
    axb.set_title(r'(b) zoom: occupied $(r{+}2,r)$ cells, $a\equiv b+1\ (\mathrm{mod}\ 4)$' + '\n' +
                  r'$\delta\sqrt{N}\geq\frac{4}{\sqrt{17}}(1-\frac{1}{Q})=%s$ (any slides); '
                  r'vdC slides: $\delta^2N=241/256$' % ffloor(bound), fontsize=7.0, pad=3, linespacing=1.5)
    handles = legend_handles(['grid', 'lat', 'pt', 'jit', 'vec']) + [
        Line2D([], [], color='#9a9a9a', lw=0.6, ls=(0, (3, 1.5)), label='lattice lines')]
    fig.legend(handles=handles, loc='lower center', ncol=6, frameon=False, bbox_to_anchor=(0.5, 0.0),
               handlelength=1.8, columnspacing=1.3, handletextpad=0.45)
    save(fig, 'arc_gk2d')
    return dict(r=r, R=R, N=N, best=int(best), bound=bound, nbox=nbox)


# ================================================================== arc_twocoset
def twocoset_mats(p):
    """T_p of prop:twocoset: rows e_c, B_c, R_c; B = [[0,h,h],[r,-1,1],[r,-1,1]], h=(p-1)/2, r=round(p/8)."""
    h, r = (p - 1) // 2, round(p / 8)
    B = [[0, h, h], [r, p - 1, 1], [r, p - 1, 1]]
    Rr = [[0, 1, 2], [3, 0, 1], [1, 5, 0]]
    return [[[int(j == c) for j in range(3)], [x % p for x in B[c]], Rr[c]] for c in range(3)]


def twocoset_LB(p):
    return np.sqrt(33 / 32 - 41 / (16 * p)) - np.sqrt(3) / p


def twocoset_dstar(p):
    r = np.round(np.asarray(p, dtype=float) / 8)
    p = np.asarray(p, dtype=float)
    return np.sqrt((p * p - 2 * p + 3) ** 2 + ((r - 1) * p + 4) ** 2 + ((r - 1) * p + 6) ** 2) / p ** 2


def fig_twocoset():
    p = 1009
    TN = DNet(twocoset_mats(p), p, [1, 1, 1])
    ok, nbox = TN.t0()
    check('twocoset', ok, f'T_{p} is a (0,3,3)-net: all {nbox} boxes full rank (prop:twocoset(1))')
    # anchor: x-offset ~ 3/4 (away from the wrap), y = z offset ~ 0.4 (between multiples of 1/8; points near the
    # cell centres in (a), one wrap of the y-offset inside the window of (b))
    rng = np.random.default_rng(3)
    for _ in range(200000):
        n0 = rng.integers(12, p - 12, size=3)
        _, D0 = TN.eval(n0[None])
        g0 = TN.geo(D0)[0] / p
        if 0.70 <= g0[0] <= 0.80 and 0.38 <= g0[1] <= 0.43:
            break
    else:
        raise AssertionError('no anchor found')
    a0, b0 = g0[0], g0[1]

    def site(cells):
        cells = np.asarray(cells)
        sx = (a0 + 0.5 * ((cells[:, 1] + cells[:, 2] - n0[1] - n0[2]) % 2)) % 1.0
        sy = (b0 + (cells[:, 0] - n0[0]) / 8.0) % 1.0
        return cells + np.stack([sx, sy, sy], 1)

    # 3D block: the anchored pattern Gamma, one site per cell, minimum sqrt(33/32), minimal vectors
    blk = n0 + np.stack(np.meshgrid(np.arange(-1, 10), np.arange(-3, 4), np.arange(-3, 4), indexing='ij'),
                        -1).reshape(-1, 3)
    XB, DB = TN.eval(blk)
    G = TN.geo(DB)
    check('twocoset', np.all(G[:, 1] == G[:, 2]), 'y and z read the same geometric digit (equal rows: shared wrap)')
    SB = site(blk)
    devB = np.abs(XB - SB).max()
    check('twocoset', devB < 0.05, f'every point of the 11x7x7 block within {devB:.4f} of the anchored two-coset '
                                   f'pattern n + ({{(n_y+n_z)/2}}, {{n_x/8}}, {{n_x/8}}) (drift + jitter)')
    check('twocoset', np.all(np.floor(SB + 1e-12).astype(int) == blk), 'the anchored pattern has its site in the cell')
    dif = SB[:, None, :] - SB[None, :, :]
    d2 = (dif ** 2).sum(-1)
    np.fill_diagonal(d2, 9.0)
    check('twocoset', abs(d2.min() - 33 / 32) < 1e-12, 'minimum of the anchored pattern in the block = 33/32 (squared)')
    mins = {tuple(np.round(v * 8).astype(int)) for v in dif[np.abs(d2 - 33 / 32) < 1e-12]}
    check('twocoset', (8, 1, 1) in mins and (4, -7, 1) in mins and (4, 1, -7) in mins,
          'minimal differences include (1,1/8,1/8) (same parity) and (1/2,-7/8,1/8), (1/2,1/8,-7/8) (opposite parity)')
    # not a lattice: (1/2,1,0) is a difference, its double (1,2,0) is not (period lattice <(1,1/8,1/8),(0,1,1),(0,1,-1)>)
    diffs = {tuple(np.round(v * 8).astype(int)) for v in dif.reshape(-1, 3)}
    check('twocoset', (4, 8, 0) in diffs and (8, 16, 0) not in diffs,
          'non-lattice: (1/2,1,0) is a difference of two sites, (1,2,0) is not')
    # (a) one layer n_x = x0 in the (y,z)-plane, and the next layer
    W = 7
    lay = [np.array([[n0[0] + dx, n0[1] + iy, n0[2] + iz] for iy in range(-3, W - 3) for iz in range(-3, W - 3)])
           for dx in (0, 1)]
    XA = [TN.eval(L)[0] for L in lay]
    SA = [site(L) for L in lay]
    raised = ((lay[0][:, 1] + lay[0][:, 2] - n0[1] - n0[2]) % 2 == 1) if a0 < 0.5 else \
        ((lay[0][:, 1] + lay[0][:, 2] - n0[1] - n0[2]) % 2 == 0)
    check('twocoset', np.allclose(SA[0][raised, 0] - lay[0][raised, 0], SA[0][~raised, 0][0] - lay[0][~raised, 0][0] + 0.5)
          if a0 < 0.5 else np.allclose(SA[0][raised, 0] - lay[0][raised, 0], a0),
          'raised cells (checkerboard by the parity of n_y+n_z) sit 1/2 higher in x')
    # (b) xy-cut n_z = z0
    WX, WY = 10, 6
    cut = np.array([[n0[0] - 1 + ix, n0[1] - 2 + iy, n0[2]] for ix in range(WX) for iy in range(WY)])
    XC, _ = TN.eval(cut)
    SC = site(cut)
    # (c) exact values
    Wt = json.load(open(os.path.join(HERE, 'twocoset_exact.json')))
    ex = sorted((int(k), np.sqrt(v['d2']) / int(k) ** 2) for k, v in Wt['twocoset'].items())
    for q_, c_ in ex:
        check('twocoset', twocoset_LB(q_) <= c_ <= twocoset_dstar(q_) + 1e-15,
              f'p={q_}: proved bound {twocoset_LB(q_):.4f} <= exact {c_:.6f} <= pair value')
    exC = [(q_, float(col_c(q_))) for q_, _ in ex]
    check('twocoset', all(c_ < 1 for _, c_ in exC) and exC[0][1] > ex[0][1] and all(cT > cC for (_, cT), (_, cC) in
                                                                                  zip(ex[1:], exC[1:])),
          'column nets C_p (thm:col, exact): < 1; ahead of T_p at p=101, behind it at the other computed primes')

    fig = plt.figure(figsize=(WIDTH, 2.75))
    # ---- (a)
    ax = fig.add_axes([0.005, 0.17, 0.30, 0.70])
    for (cy, cz), rz in zip(lay[0][:, 1:], raised):
        if rz:
            ax.add_patch(Rectangle((cy, cz), 1, 1, fc='#e6e6e6', ec='none', zorder=0))
    y0, z0 = lay[0][:, 1].min(), lay[0][:, 2].min()
    grid(ax, y0, y0 + W, z0, z0 + W)
    ax.scatter(XA[1][:, 1], XA[1][:, 2], s=6, c='#9a9a9a', lw=0, zorder=2)
    draw_points(ax, SA[0][:, 1:], XA[0][:, 1:], s_lat=24, s_pt=7)
    ia = int(np.where((lay[0] == n0).all(1))[0][0]) if raised[np.where((lay[0] == n0).all(1))[0][0]] else \
        int(np.where((lay[0] == n0 + np.array([0, 1, 0])).all(1))[0][0])
    oa = SA[0][ia]
    tgt1 = int(np.where((lay[1] == lay[0][ia] + np.array([1, 0, 0])).all(1))[0][0])
    tgt2 = int(np.where((lay[1] == lay[0][ia] + np.array([1, -1, 0])).all(1))[0][0])
    v1, v2 = SA[1][tgt1] - oa, SA[1][tgt2] - oa
    check('twocoset', np.allclose(v1, [1, 1 / 8, 1 / 8]) and np.allclose(v2, [0.5, -7 / 8, 1 / 8]),
          'panel (a): from a raised point, the next layer has (1,1/8,1/8) and (1/2,-7/8,1/8), both of squared length 33/32')
    arrow(ax, oa[1:], v1[1:], lw=1.0, ms=4)
    arrow(ax, oa[1:], v2[1:], lw=1.1, ms=5)
    label(ax, oa[1] + 0.62, oa[2] + 0.62, r'$(1,\frac{1}{8},\frac{1}{8})$', fs=5.6)
    label(ax, oa[1] - 0.45, oa[2] - 0.32, r'$(\frac{1}{2},-\frac{7}{8},\frac{1}{8})$', fs=5.6)
    clean(ax, ((y0, y0 + W), (z0, z0 + W)))
    panel_title(ax, r'(a) $\mathcal{T}_{1009}$, slab $n_x$: $(y,z)$-plane')
    ax.text(0.5, -0.02, r'shaded: raised by $\frac{1}{2}$ in $x$;  grey dots: slab $n_x+1$', transform=ax.transAxes,
            fontsize=5.6, ha='center', va='top')
    # ---- (b)
    ax = fig.add_axes([0.33, 0.17, 0.36, 0.70])
    x0c, y0c = cut[:, 0].min(), cut[:, 1].min()
    rz_c = ((cut[:, 1] + cut[:, 2] - n0[1] - n0[2]) % 2 == (1 if a0 < 0.5 else 0))
    for (cx, cy), rz in zip(cut[:, :2], rz_c):
        if rz:
            ax.add_patch(Rectangle((cx, cy), 1, 1, fc='#e6e6e6', ec='none', zorder=0))
    grid(ax, x0c, x0c + WX, y0c, y0c + WY)
    draw_points(ax, SC[:, :2], XC[:, :2], s_lat=22, s_pt=6.5)
    ctr = np.array([x0c + 3, y0c + 2, n0[2]])                      # a raised cell near the centre of the window
    ib = int(np.where((cut == ctr).all(1))[0][0])
    if not rz_c[ib]:
        ib = int(np.where((cut == ctr + np.array([0, 1, 0])).all(1))[0][0])
    ob = SC[ib]
    for dv, txt, sgn in (((1, 0, 0), r'$\frac{\sqrt{66}}{8}$', 1), ((1, -1, 0), r'$\frac{\sqrt{66}}{8}$', 1),
                         ((0, 1, 0), r'$\frac{\sqrt{5}}{2}$', -1)):
        k_ = int(np.where((cut == cut[ib] + np.array(dv)).all(1))[0][0])
        v = SC[k_] - ob
        arrow(ax, ob[:2], v[:2], lw=1.1, ms=5)
        nv = np.array([-v[1], v[0]]) / np.hypot(v[0], v[1])
        label(ax, ob[0] + 0.6 * v[0] + sgn * 0.42 * nv[0], ob[1] + 0.6 * v[1] + sgn * 0.42 * nv[1], txt, fs=6.0)
    check('twocoset', abs(np.linalg.norm(SC[int(np.where((cut == cut[ib] + np.array([0, 1, 0])).all(1))[0][0])] - ob)
                          - np.sqrt(5) / 2) < 1e-12, 'in-layer neighbours are sqrt(5)/2 apart (the pucker)')
    clean(ax, ((x0c, x0c + WX), (y0c, y0c + WY)))
    panel_title(ax, r'(b) the same net, $(x,y)$-plane: pucker and shear $\frac{1}{8}$')
    # ---- (c)
    ax = fig.add_axes([0.765, 0.20, 0.225, 0.64])
    pp = np.array([q_ for q_ in range(41, 200001) if all(q_ % d for d in range(2, int(q_ ** .5) + 1))])
    pp = pp[np.unique(np.round(np.log(pp) * 60), return_index=True)[1]]
    ax.axhline(np.sqrt(66) / 8, color=ACC, lw=0.6, ls=(0, (3, 1.5)))
    ax.axhline(1.0, color='#7a7a7a', lw=0.6, ls=(0, (3, 1.5)))
    ax.plot(pp, twocoset_dstar(pp), color='#9a9a9a', lw=0.6)
    ax.plot(pp, twocoset_LB(pp), color=ACC, lw=0.9)
    for res, ls_ in ((1, (0, (1, 1))), (2, '-')):
        qq = np.exp(np.linspace(np.log(40), np.log(2e5), 400))
        qq = 3 * np.floor(qq / 3) + res                          # a continuous branch through q = res mod 3
        ax.plot(qq, col_c(qq), color=INK, lw=0.6, ls=ls_)
    ax.scatter([a for a, _ in ex], [b for _, b in ex], s=9, c=ACC, lw=0, zorder=5)
    ax.set_xscale('log')
    ax.set_xlim(40, 2e5)
    ax.set_ylim(0.94, 1.022)
    ax.tick_params(length=1.5, pad=1)
    for sp_ in ax.spines.values():
        sp_.set_color('#9a9a9a')
    ax.set_xlabel('$p$', labelpad=0)
    ax.text(5e4, np.sqrt(66) / 8 + 0.0012, r'$\sqrt{66}/8$', color=ACC, fontsize=5.8, ha='center', va='bottom')
    hl = [Line2D([], [], ls='none', marker='o', ms=2.8, mfc=ACC, mec='none', label=r'$\mathcal{T}_p$ exact'),
          Line2D([], [], color=ACC, lw=0.9, label='proved bound'),
          Line2D([], [], color='#9a9a9a', lw=0.6, label='pair $d_*/p^2$'),
          Line2D([], [], color=INK, lw=0.6, label=r'$\mathcal{C}_p$, $p\equiv2$'),
          Line2D([], [], color=INK, lw=0.6, ls=(0, (1, 1)), label=r'$\mathcal{C}_p$, $p\equiv1$')]
    leg = ax.legend(handles=hl, loc='lower right', fontsize=5.2, framealpha=0.95, borderpad=0.3, labelspacing=0.2,
                    handletextpad=0.3, handlelength=1.4)
    leg.get_frame().set_linewidth(0.3)
    panel_title(ax, r'(c) $\delta N^{1/3}$, $m=3$')
    common_legend(fig, ['grid', 'lat', 'pt', 'jit', 'vec'], y=0.0)
    save(fig, 'arc_twocoset')
    return dict(p=p, n0=n0.tolist(), a0=a0, b0=b0, devB=devB, nbox=nbox, ex=ex, exC=exC)


# ================================================================== captions
# ------------------------------------------------------------------ sec:whylat: sweeps and wraps (rev 12.0)
def fig_whylat():
    """(a) affine vs tent sweep of a sub-cell (Corollary cor:linoff(b), Remark rem:open(11));
    (b) wrap patterns realized by a shared (equal-row) layer and by a bounded perturbation of it (Lemma lem:phase(i));
    (c) the folded contribution min(b, 1-b) of a coordinate with E_c = 0 (Remark rem:glue)."""
    W = 24
    aff = np.arange(W)
    tent = np.array([2 * i if 2 * i < W else 2 * (W - 1 - i) + 1 for i in range(W)])
    check('whylat', sorted(aff) == list(range(W)) and sorted(tent) == list(range(W)), f'both sweeps are bijections of Z/{W}')
    cyc = lambda f: np.abs(np.diff(np.r_[f, f[0]]))
    check('whylat', cyc(aff).max() == W - 1 and int((cyc(aff) > 2).sum()) == 1,
          f'affine sweep: exactly one cyclic jump, of size W-1 = {W - 1} (the slip)')
    check('whylat', cyc(tent).max() == 2, 'tent sweep: every cyclic step at most 2')
    # (b) real layers at p = 31, step E = e_1
    p = 31
    arow = col_row(p)                                               # row a of the column net C_31 (def:col)
    a = int(arow[0])
    Bs = np.tile(arow, (3, 1)).astype(np.int64)                     # equal rows 1 a^T: the layer of C_p
    Pp = np.array([[0, 1, 0], [0, 0, 2], [1, 0, 0]], dtype=np.int64)  # bounded perturbation
    Bf = (Bs + Pp) % p
    detf = int(round(np.linalg.det(Bf))) % p
    check('whylat', detf != 0, f'perturbed layer invertible mod {p} (det = {detf})')
    n = np.stack(np.meshgrid(*[np.arange(p)] * 3, indexing='ij'), -1).reshape(-1, 3)
    E = np.array([1, 0, 0])

    def realized(B):
        r = (n @ B.T) % p
        beta = (B @ E) % p
        kap = (r + beta >= p).astype(int)
        pats = {tuple(k) for k in kap}
        lens = {k: float(np.linalg.norm(E + beta / p - np.array(k))) for k in pats}
        return beta, pats, lens

    bs, ps, ls = realized(Bs)
    bf, pf, lf = realized(Bf)
    check('whylat', ps == {(0, 0, 0), (1, 1, 1)}, 'equal rows: only the wrap patterns 000 and 111 occur (shared wrap)')
    check('whylat', len(pf) == 8 and all(bf != 0), 'perturbed (invertible) layer: all 8 wrap patterns occur (lem:phase(i))')
    ms, mf = min(ls.values()), min(lf.values())
    check('whylat', ms > 1 and mf < 0.6, f'min folded length at E=e_1: shared {ms:.4f} > 1, free {mf:.4f} < 0.6')
    # (c)
    bb = np.linspace(0, 1, 401)
    fc = np.minimum(bb, 1 - bb)
    check('whylat', abs(fc.max() - 0.5) < 1e-12 and abs(bb[fc.argmax()] - 0.5) < 1e-12,
          'min(b,1-b) is maximal (1/2) only at b = 1/2')

    fig = plt.figure(figsize=(WIDTH, 1.85))
    ax1 = fig.add_axes([0.045, 0.20, 0.27, 0.66])
    ax2 = fig.add_axes([0.375, 0.20, 0.27, 0.66])
    ax3 = fig.add_axes([0.71, 0.20, 0.27, 0.66])
    # (a)
    ax1.step(np.arange(W + 1), np.r_[aff, aff[0]] / W, where='post', color=LATE, lw=0.9)
    ax1.plot(np.arange(W + 1), np.r_[tent, tent[0]] / W, color=ACC, lw=1.0, marker='o', ms=1.8)
    ax1.annotate('', xy=(W, 0.02), xytext=(W, (W - 1) / W - 0.02),
                 arrowprops=dict(arrowstyle='->', color=INK, lw=0.6))
    ax1.text(W - 0.6, 0.5, 'slip', ha='right', va='center', fontsize=6.5)
    ax1.text(1.0, 0.86, 'affine', color=LATE, fontsize=6.5)
    ax1.text(8.0, 0.86, 'tent', color=ACC, fontsize=6.5)
    ax1.set_xlim(0, W + 0.5); ax1.set_ylim(-0.03, 1.03)
    ax1.set_xlabel('cell along a line (cyclic, $W=%d$)' % W, labelpad=1)
    ax1.set_ylabel('sub-cell offset', labelpad=1)
    panel_title(ax1, '(a) two sweeps of $\\mathbb{Z}/W$')
    # (b)
    allk = [(i, j, k) for i in (0, 1) for j in (0, 1) for k in (0, 1)]
    for row, (pats, lens, nm) in enumerate(((ps, ls, 'equal rows'), (pf, lf, 'perturbed'))):
        y = 1 - row
        for x, kk in enumerate(allk):
            on = kk in pats
            ax2.add_patch(Rectangle((x, y), 0.9, 0.7, facecolor=(INK if on else 'white'), edgecolor=GRID, lw=0.5))
            if on and abs(lens[kk] - min(lens.values())) < 1e-12:
                ax2.add_patch(Rectangle((x - 0.05, y - 0.05), 1.0, 0.8, fill=False, edgecolor=ACC, lw=1.2))
        ax2.text(-0.15, y + 0.35, nm, ha='right', va='center', fontsize=6.5)
        ax2.text(8.1, y + 0.35, ftr(min(lens.values()), 3), ha='left', va='center', fontsize=6.5, color=ACC)
    for x, kk in enumerate(allk):
        ax2.text(x + 0.45, -0.25, ''.join(map(str, kk)), ha='center', va='center', fontsize=5.6)
    ax2.set_xlim(-2.6, 9.3); ax2.set_ylim(-0.5, 1.9); ax2.axis('off')
    panel_title(ax2, '(b) wrap patterns $\\omega$ at $E=\\mathbf{e}_1$, $p=%d$' % p)
    # (c)
    ax3.plot(bb, fc, color=INK, lw=0.9)
    for bv, nm in ((1 / 3, "$\\frac{1}{3}$ ($H\\mathbb{Z}^3$)"), (0.5, "$\\frac{1}{2}$ ($D_s^+$)")):
        ax3.plot([bv], [min(bv, 1 - bv)], 'o', color=ACC, ms=3)
        ax3.text(bv, min(bv, 1 - bv) + 0.05, nm, ha='center', fontsize=6.3, color=ACC)
    ax3.set_xlim(0, 1); ax3.set_ylim(0, 0.68)
    ax3.set_xlabel('glue $b_c$', labelpad=1)
    ax3.set_ylabel('$\\min(b_c,1-b_c)$', labelpad=1)
    panel_title(ax3, '(c) a coordinate with $E_c=0$, free wraps')
    save(fig, 'arc_whylat')
    return dict(W=W, p=p, a=a, arow=[int(x) for x in arow], P=Pp.tolist(), ms=ms, mf=mf, ns=len(ps), nf=len(pf))


def up2(x):
    return np.ceil(float(x) * 100 - 1e-9) / 100          # 'below up2(x)' is then true


def write_captions(R):
    A, S, K, L, P = R['anatomy'], R['small'], R['skeleton'], R['large'], R['split']
    caps = {}
    caps['arcAnatomyCaption'] = (
        r"The mechanism of the nets of this paper, on a toy two-dimensional example ($q=%d$; schematic, not a net from the "
        r"text). (a) A $%d\times%d$ window of cells (grey grid), one point per cell. The geometric digit "
        r"$r=Mu\bmod q$ is linear in the last cell digits $u$, with $M=-I+R_{90^\circ}$ (the $xy$-block of the "
        r"geometric layer of the three-dimensional nets, Proposition~\ref{prop:cell}); it puts the point of cell $n$ at the lattice image $n+r/q$ (open "
        r"circles). On each patch this is a piece of $(I+\frac Mq)\mathbb{Z}^2$, which is $\mathbb{Z}^2$ rotated by "
        r"$\arctan\frac1{q-1}$ and contracted, with shortest vectors $(I+\frac Mq)e_x,(I+\frac Mq)e_y$ (arrows). Where "
        r"a coordinate of $r$ wraps modulo $q$ the patch ends at a slip (dashed), which keeps one point per "
        r"cell. The deeper digits add a jitter $f/q$, $f\in[0,1)^2$ (grey segments to the actual points, dots). Since "
        r"$\det(I+\frac Mq)=(1-\frac1q)^2+\frac1{q^2}<1$, the lattice image is about $2/q$ too dense: about every $q$ "
        r"cells one lattice site is skipped ($\times$) and the point jumps by about one cell at a slip; here %d "
        r"skipped sites against the density surplus $(\det^{-1}-1)\,%d^2=%s$, up to boundary effects. (b) The "
        r"dotted box of (a): the jitter stays in a sub-cell of side $1/q$, so the separation is at least the lattice "
        r"minimum $\lambda_1=%s$ minus the jitter cost. (c) One axis, $r=-u\bmod q$ (the diagonal entry $-1$ of "
        r"$M$): the points of cells $1,\dots,q$ sit on the sites $1+i(1-\frac1q)$, $i\in\Z$; cell $q$ receives a second site, "
        r"which is skipped, and the next point steps $2-\frac1q$ across the slip. Theorem~\ref{thm:sep} makes this "
        r"exact ($1-1/q$ from the own-axis step); the other regimes (II and III, Section~\ref{sec:prelim}) change only the lattice and the cost."
        % (A['q'], A['W'], A['W'], A['nskip'], A['W'], ftr(A['exp'], 1), ftr(A['lam'], 3)))
    caps['arcSmallCaption'] = (
        r"Regime I, small-entry layers ($m=sk$). (a) $\mathcal P_{2,%d}$ ($q=%d$, $k=2$, $N=%d^6$; "
        r"Theorem~\ref{thm:main}): the %d points with $z$-cell $n_z=%d$ and $(x,y)$-cells in a $%d\times%d$ window, "
        r"projected to the $xy$-plane in cell units. Open circles: the lattice image $n+r/q$, with $r=Mu+Jv\bmod q$ "
        r"the geometric digit of Proposition~\ref{prop:cell}; dots: the points; grey segments: the jitter ($<1/q$ per "
        r"coordinate). Arrows: the $(x,y)$ parts of the shortest vectors $(I+\frac Mq)e_x$, $(I+\frac Mq)e_y$ of "
        r"$\Lambda_q=(I+\frac Mq)\mathbb{Z}^3$, $\lambda_1(\Lambda_q)=%s$ (Remark~\ref{rem:lattice3}). Dashed: slip "
        r"edges, where a geometric digit wraps; dotted: cell boundaries where the last cell digit wraps (the term "
        r"$Jv$ enters); $\times$: skipped sites. As in Figure~\ref{fig:arc}, $\Lambda_q$ is too dense, "
        r"$\det(I+\frac Mq)=%s\approx1-\frac3q$: %d skipped sites against the density surplus %s, up to boundary "
        r"effects. (b) Dimension four: a $(0,8,4)$-net over $\mathbb F_{%d}$ ($k=2$, $N=%d^8$) whose row~$0$ is the "
        r"deficit-two design over $\Z[1/2]$ (places $\infty,0,1,2$; Section~\ref{sec:dim4ex}), $xy$-slice with $n_z=%d$, "
        r"$n_w=%d$ fixed; arrows: two of the eight shortest vectors $\pm(I+\frac{F_0}q)e_c$ of "
        r"$(I+\frac{F_0}q)\mathbb{Z}^4$ ($\lambda_1=%s$). Despite the larger base, the entries of size two of $F_0$ "
        r"(Remark~\ref{rem:pm1}) make the patches smaller and the slips denser than in (a): %d against %d slip edges "
        r"in the same window, and "
        r"%d $\times$ against a planar density surplus of %s, up to boundary effects. The separation bound of "
        r"Section~\ref{sec:dim4ex} uses only row~$0$."
        % (S['q'], S['q'], S['q'], S['W'] ** 2, S['z0'], S['W'], S['W'], ftr(S['lam'], 3), ftr(S['det3'], 3), S['nsk'], ftr(S['exp3'], 1),
           S['q4'], S['q4'], S['c4'][2], S['c4'][3], ftr(S['lam4']['4D'], 3), S['nslip4'], S['nslip'], S['nsk4'], ftr(S['exp4'], 1)))
    caps['arcSkeletonCaption'] = (
        r"Regime II, lattice skeletons ($m=sk+r$), in fine-cell units. (a) $\mathcal B^2_{1,43,3}$ ($p=43$, "
        r"$\rho=3$, $m=5$; Remark~\ref{rem:B2}): the slab of fine cells $P_z=%d$ over a $%d\times%d$ window. "
        r"Shaded: the occupied fine cells, which are exactly the cells of the index-$p$ lattice "
        r"$\Lambda_{\mathcal B^2}=\{a:a_z\equiv\rho a_x+\rho^2a_y\pmod p\}$: no faults, no skipped sites. Open circles: their "
        r"corners (the lattice image); dots: the points, displaced by up to one fine cell of jitter; arrows: a reduced "
        r"basis $(%d,%d)$, $(%d,%d)$ of the lattice section. (b) The three slabs $P_z=%d,%d,%d$ (shades): the "
        r"squares of side $\rho$ about the occupied cells have disjoint interiors, so two points of these slabs differ by "
        r"at least $\rho$ fine cells in $x$ or $y$ (Lemma~\ref{lem:skellat}(L)), and $\delta N^{1/3}\ge(\rho-1)p^{-1/3}$ "
        r"after one fine cell of jitter. (c) $\mathcal B^1_{1,37,3}$ ($m=4$; Theorem~\ref{thm:allm}): $xz$-view of "
        r"the points with $y$-cell index $%d$ over the four coarse blocks around $(37,37)$ (black lines). Open "
        r"circles: the coset of the Korobov lattice $\Lambda_{\mathcal B^1}$ (generating vector $(1,\rho,\rho^2)$ modulo $p$), "
        r"continued from the lower-left block (projected basis $(%d,%d)$, $(%d,%d)$); dashed arrows: the faults. In "
        r"each coarse block the occupied cells are exactly a Korobov coset, shifted by $\pm1$ fine cell from block to "
        r"block (dark where shifted): the faults are coset shifts, like stacking faults, not skips. The separation is "
        r"the shortest vector minus faults and jitter (Lemma~\ref{lem:skelred})."
        % (K['zstar'], K['W'], K['W'], K['u2'][0], K['u2'][1], K['v2'][0], K['v2'][1], K['zstar'], K['zstar'] + 1,
           K['zstar'] + 2, K['yblk'], K['u1'][0], K['u1'][1], K['v1'][0], K['v1'][1]))
    caps['arcLargeCaption'] = (
        r"Regime III, large-entry layers ($m=s$). (a) The column net $\mathcal C_{13}$ (Theorem~\ref{thm:col}, "
        r"$a=(%d,%d,%d)$, $w=(%d,%d,%d)$): the $3^3$ cells around $n=(%d,%d,%d)$. All three coordinates read the same "
        r"two offset digits, so each point lies exactly on the body diagonal of its cell (dotted), at the fraction "
        r"$\varphi(n)/p^2$ of it, which changes by $\frac13+\frac{w\cdot E}{3p}$ from cell to cell, up to the jitter "
        r"$\Delta j/p^2$. Open circles: the reflected cube $H\mathbb{Z}^3$, $H=I-\frac23\mathbf 1\mathbf 1^{\!\top}$, "
        r"anchored at the central point; accent: its six minimal vectors $\pm He_c$; grey segments: drift and jitter, "
        r"both along $(1,1,1)$. (b) The same net, the $5^3$ cells around $n$, viewed along $(1,1,1)$: the lattice "
        r"points within one plane spacing $1/\sqrt3$ of the centre along $(1,1,1)$ (fill: the plane $x+y+z=\mathrm{const}$). The three neighbours one plane up, $-He_c$, "
        r"project opposite to the cell axes $e_c$ (grey), whereas in $\mathbb{Z}^3$ they are the $e_c$ themselves: "
        r"$H\mathbb{Z}^3$ is $\mathbb{Z}^3$ turned half a turn about $(1,1,1)$. Drift and jitter run along $(1,1,1)$ "
        r"and are invisible here: every drawn point projects exactly onto its site, and differs "
        r"from its site of the anchored lattice by less than $%.2f$ of a cell in each coordinate. (c) Dimension five: the net "
        r"$\mathcal H^{5*}_{1,p}$ of Proposition~\ref{prop:HL5} with $k=1$ ($m=s=5$), $p=%d$, a $(0,5,5)$-net over "
        r"$\mathbb F_p$: the $xy$-slice of an $%d\times%d$ window of cells, the other three cells fixed. Its layer "
        r"$F_0$ lies in $\frac12+\mathbb{Z}$, so by the parity of $\Sigma n$ the point sits at $n+c_0$ or, in the "
        r"shaded cells, at $n+c_0+\frac12\mathbf 1$, for one fixed $c_0\in[0,1)^5$ (here $c_0\approx%s$ in $x$ and "
        r"$y$), up to drift and jitter below $%.2f$ of a cell: locally the packing $D_5^+$, whose minimum $\sqrt5/2>1$ "
        r"(a step to a cell of the other parity) exceeds the cubic value~$1$; a diagonal step within one parity has "
        r"length $\sqrt2$ (Proposition~\ref{prop:Hk} with $k=1$). In all three panels the limit lattice has "
        r"covolume~$1$ and one site in each drawn cell: no site is skipped, and the net departs from the lattice only "
        r"by the $O(1/p)$ drift and jitter."
        % (*L['a'], *L['w'], L['n0'][0], L['n0'][1], L['n0'][2], up2(L['devS']), L['q5'], L['W6'], L['W6'],
           ftr(sum(L['c06']) / 2, 2), up2(L['dev6'])))
    caps['arcSplitCaption'] = (
        r"Split frames (Definition~\ref{def:split}). (a) Top: a frame reads the cell and the offset of coordinate $c$ "
        r"at one place $a_c$, so its geometric layer is a symmetric Cauchy matrix, and a Pl\"ucker relation among four "
        r"places rules out a half-integer layer (Proposition~\ref{prop:P}). Bottom: the split frame of $H_5^*$ "
        r"(Proposition~\ref{prop:HL5}), $u=(%s)$ even, $v=(%s)$ odd: coordinate $c$ reads its cell at $v_c$ (filled) "
        r"and its offset at $u_c$ (open); arcs: two entries $\vartheta_{cd}=u_c-v_d$. The box minors are confluent "
        r"Vandermonde determinants in the ten places (Lemma~\ref{lem:Tsplit}). (b) The geometric layer is the "
        r"non-symmetric Cauchy matrix $\lambda^\prime_c\mu_d/(u_c-v_d)$ (Proposition~\ref{prop:Gsplit}); every "
        r"$\vartheta_{cd}$ is odd, so the layer can be put in $\frac12+\mathbb{Z}$ (Lemma~\ref{lem:Hs}; for the explicit "
        r"$H_s$, $u_c=2c$, $v_d=2d+1$). Shown: $\vartheta$ and $2F_0$ of $H_5^*$. (c) The net $\mathcal H^{5*}_{2,p}$, "
        r"$p=10007$: the $xy$-slice of a $%d\times%d$ window of cells that crosses a carry in $x$ and in $y$ (dotted), "
        r"the other three cells fixed. Every partial sum $M^{(j)}$ of the design lies in $\frac12+\mathbb{Z}$, so the "
        r"corner/centre parity pattern of $D_5^+$ (minimum $\sqrt5/2>1$) continues across the carries "
        r"(Proposition~\ref{prop:Hk}); drift and jitter stay below $%.2f$ of a cell."
        % (','.join(map(str, P['u'])), ','.join(map(str, P['v'])), P['W'], P['W'], up2(P['dev'])))
    T = R['twocoset']
    caps['arcTwoCosetCaption'] = (
        r"A two-coset layer at $m=3$: the net $\mathcal T_{%d}$ of Proposition~\ref{prop:twocoset} ($h=%d$, $r=%d$), in "
        r"cell units. (a) The $(y,z)$-plane of the slab of cells $n_x=%d$, $7\times7$ cells around $(n_y,n_z)=(%d,%d)$. "
        r"The coordinates $y$ and $z$ read the same geometric digit $rn_x-n_y+n_z$, so the points of a slab lie, up to "
        r"drift and jitter, on a translate of $\mathbb{Z}^2$ (open circles: the pattern $\Gamma$ anchored at the central "
        r"point); the geometric digit $h(n_y+n_z)$ of $x$, with $h\equiv-\frac12$, raises the points of every other "
        r"cell (shaded) by $\frac12$ in $x$. Grey dots: the next slab $n_x+1$, shifted by $(\frac18,\frac18)$. Accent: "
        r"from a raised point, the two kinds of shortest vectors to the next slab, $(1,\frac18,\frac18)$ and "
        r"$(\frac12,-\frac78,\frac18)$, both of length $\sqrt{66}/8$. (b) The $(x,y)$-plane of the cells with $n_z=%d$: "
        r"along $y$ the points alternate between the two heights (the pucker; in-slab neighbours are $\sqrt5/2$ apart), "
        r"and from column to column the $y$-offset grows by $\frac18$ (the shear) and wraps after eight columns. Accent: "
        r"the same two shortest vectors (their $z$-components $\frac18$ are not visible) and an in-slab neighbour. In "
        r"(a) and (b) every point is within $%s$ of its site of $\Gamma$ in each coordinate, and $\Gamma$ has one site in "
        r"each cell; it is the union of two cosets of a lattice of covolume $2$ and is not a lattice. (c) "
        r"$\delta N^{1/3}$ against $p$: exact values for $\mathcal T_p$ at %d primes $%d\le p\le%d$ (dots; computed, "
        r"Appendix~\ref{app:verify}), the lower bound of Proposition~\ref{prop:twocoset}(2) (for $p\ge41$), the pair "
        r"value $d_*/p^2$ of (3), and for comparison the exact values of the column nets $\mathcal C_p$ "
        r"(Theorem~\ref{thm:col}; solid for $p\equiv2$, dotted for $p\equiv1\pmod3$), which stay below $1$ "
        r"(Corollary~\ref{cor:colceil}); dashed: $1$ and $\sqrt{66}/8$."
        % (T['p'], (T['p'] - 1) // 2, round(T['p'] / 8), T['n0'][0], T['n0'][1], T['n0'][2], T['n0'][2],
           up2(T['devB']), len(T['ex']), T['ex'][0][0], T['ex'][-1][0]))
    G = R['gk2d']
    caps['arcGKCaption'] = (
        r"The mechanism in its simplest instance: the permutation $(0,m,2)$-net of Gr\"unschlo{\ss} and Keller "
        r"\cite[Sec.~3]{GK09} for $m=2r=%d$, $Q=2^r=%d$, $N=Q^2=%d$, in cell units (Remark~\ref{rem:gk2d}). (a) The "
        r"$(r,r)$ cells (grey grid), one point each. Open circles: the lattice image $ue+jv+(\frac14,0)$, $e=(1,0)$, "
        r"$v=(\frac14,1)$, on the lines (dashed) of $\Lambda=\langle e,v\rangle$ in direction $v$; the tiling lattice of "
        r"the row-shifted torus is $Q\Lambda$, so the lines close up and there are no slips. Dots: the points "
        r"$(X,Y)=ue+(j+\varrho(u)/Q)v+(d,0)$, $|d|<1$ grid unit: line $u$ is slid along itself by its slide "
        r"$\varrho(u)/Q$ of one step, a van der Corput value (grey segments, the jitter). Accent: the basis $e$ (shortest, length $1$) "
        r"and $v$. (b) Zoom on $6\times6$ cells with the cells of depths $(r+2,r)$ (light grid); the occupied ones "
        r"(shaded) are exactly the coset $\{(a,b):a\equiv b+1\pmod 4\}$ of the index-$4$ lattice $\Lambda$. Since the "
        r"slides move the points arbitrarily along the lines, only the line spacing $4/\sqrt{17}$ (double arrow) "
        r"survives as a separation bound: $\delta\sqrt N\ge\frac4{\sqrt{17}}(1-\frac1Q)=%s$ for every choice of "
        r"slides; the van der Corput slides give exactly $\delta^2N=%d/256$ (in the tiling metric; \cite{Rud26})."
        % (2 * G['r'], G['R'], G['N'], ffloor(G['bound']), G['best']))
    WL = R['whylat']
    caps['arcWhyLatCaption'] = (
        r"What linearity forces (Section~\ref{sec:whylat}). (a) Two bijections of $\Z/W$, $W=%d$, as sub-cell offsets "
        r"along a cyclic line of cells: the affine bijection $i\mapsto i$ (grey), the kind that a linear offset gives, "
        r"jumps once, by $W-1$, and this jump sits at a slip plane (Corollary~\ref{cor:linoff}); every affine bijection of "
        r"$\Z/W$ has a step of size at least $W/2$, since its steps are congruent modulo $W$ and sum to zero. A tent-shaped bijection (accent), available only "
        r"to nets that are not digital, moves by at most $2$ between neighbouring cells (Remark~\ref{rem:open}(11)). "
        r"(b) The wrap vectors $\omega$ of Lemma~\ref{lem:phase}(i) that occur for the step $E=\e_1$ over all $p^3$ "
        r"cells, $p=%d$ (filled), for the equal-row layer $\mathbf 1a^{\!\top}$, $a=(%s)$, of the column net "
        r"$\mathcal C_{%d}$ (Definition~\ref{def:col}) and for the invertible layer obtained by adding $%s$; framed, the pattern of least length $|E+b-\omega|$, "
        r"printed on the right (computed: $%s$ and $%s$). The shared wrap allows only $000$ and $111$; the "
        r"perturbed layer realizes all eight, and with the glue $b\approx\frac13\mathbf 1$ (Lemma~\ref{lem:phase}) the fully folded length drops to $1/\sqrt3$. "
        r"(c) A coordinate that does not move contributes $\min(b_c,1-b_c)$ under free wraps, at most $\frac12$, "
        r"attained only at $b_c=\frac12$ (Remark~\ref{rem:glue})."
        % (WL['W'], WL['p'], ','.join(map(str, WL['arow'])), WL['p'],
           r"\left(\begin{smallmatrix}0&1&0\\0&0&2\\1&0&0\end{smallmatrix}\right)",
           ftr(WL['ms'], 3), ftr(WL['mf'], 3)))
    hdr = ('% arc_captions.tex -- GENERATED by figs_arc.py (do not edit by hand; rerun the script).\n'
           '% Caption macros for figs/arc_{anatomy,small,skeleton,large,split,twocoset,gk2d,whylat}.pdf; parameters are those drawn.\n')
    with open(os.path.join(OUT, 'arc_captions.tex'), 'w') as f:
        f.write(hdr)
        for k_, v_ in caps.items():
            f.write('\\newcommand{\\%s}{%%\n%s}\n' % (k_, v_))


if __name__ == '__main__':
    t0 = time.time()
    R = {}
    for nm, fn in (('gk2d', fig_gk2d), ('anatomy', fig_anatomy), ('small', fig_small), ('skeleton', fig_skeleton),
                   ('large', fig_large), ('twocoset', fig_twocoset), ('split', fig_split), ('whylat', fig_whylat)):
        t = time.time()
        R[nm] = fn()
        print(f'{nm:9s} {time.time() - t:5.1f}s  {R[nm]}')
    write_captions(R)
    for fg, what in CHECKS:
        print(f'  [ok] {fg:9s} {what}')
    print(f'total {time.time() - t0:.1f}s; {len(CHECKS)} checks passed')

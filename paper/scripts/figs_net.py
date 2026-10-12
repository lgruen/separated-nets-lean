#!/usr/bin/env python3
"""figs_net.py -- the point-cloud figures of P_{k,q} in core.tex (Appendix app:figs):
fig:full -> figs/fig_full.pdf, fig:slab -> figs/fig_slab.pdf, fig:axis -> figs/fig_axis.pdf.

The nets are built from Definition def:net by netdefs.py (P_mats: generator matrices (L T^2, L, L T) over Z,
reduced mod q).  Only the drawn points are generated: the (k,k,k) cells determine the point (one point per cell),
so the point in cell n = (n_x, n_y, n_z) has index digits v = B^{-1} (cell digits), B the box matrix of the depths
(k,k,k), and coordinates C_c v.
ASSERTED: for every full net drawn (fig:full) the cell-wise points equal the points by index enumeration, and the
net is a (0,m,3)-net (every elementary box of volume q^-m holds one point); the window sizes and point counts of the
captions of fig:slab and fig:axis.

    uv run --with numpy --with matplotlib python scripts/figs_net.py [--out DIR]     (default DIR = figs/; ~5 s)
The committed PDFs were written with matplotlib 3.11.0 (byte-identical output with that version).
"""
import os
import sys
import numpy as np
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))           # scripts/
sys.path.insert(0, HERE)
import netdefs                                               # noqa: E402

OUT = os.path.join(os.path.dirname(HERE), 'figs')            # the paper's figs/
if '--out' in sys.argv:
    OUT = os.path.abspath(sys.argv[sys.argv.index('--out') + 1])
os.makedirs(OUT, exist_ok=True)
plt.rcParams.update({'font.family': 'serif', 'font.size': 7, 'axes.linewidth': 0.4, 'pdf.fonttype': 42,
                     'xtick.major.width': 0.3, 'ytick.major.width': 0.3, 'xtick.major.size': 1.5,
                     'ytick.major.size': 1.5, 'xtick.labelsize': 5.5, 'ytick.labelsize': 5.5})
INK, GRID, ACC = '#1a1a1a', '#c9c9c9', '#2b6cb0'


def mats(q, m):
    """generator matrices of P_{m/3,q} mod q (rows = output digits, most significant first)"""
    return [np.array(Cc, dtype=np.int64) % q for Cc in netdefs.P_mats(m // 3)['C']]


def inv_mod(A, q):
    n = len(A); A = [[int(x) % q for x in r] + [int(i == j) for j in range(n)] for i, r in enumerate(A)]
    from math import gcd
    for c in range(n):
        piv = next(i for i in range(c, n) if gcd(A[i][c], q) == 1)
        A[c], A[piv] = A[piv], A[c]; iv = pow(A[c][c], -1, q); A[c] = [x * iv % q for x in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                f = A[i][c]; A[i] = [(x - f * y) % q for x, y in zip(A[i], A[c])]
    return np.array([r[n:] for r in A], dtype=np.int64)


class Net:
    def __init__(self, q, m):
        self.q, self.m, self.k = q, m, m // 3
        self.C = mats(q, m)
        self.Ti = inv_mod(np.vstack([self.C[c][:self.k] for c in range(3)]), q)

    def pts_cells(self, cells):
        """cells: (n,3) ints in [0, q^k). Returns integer coordinates (n,3) in [0, q^m)."""
        q, k, m = self.q, self.k, self.m
        cells = np.asarray(cells, dtype=np.int64)
        dig = np.zeros((len(cells), 3 * k), dtype=np.int64)
        for c in range(3):
            for j in range(k):                               # level j = digit j (most significant first)
                dig[:, c * k + j] = (cells[:, c] // q ** (k - 1 - j)) % q
        v = (dig @ self.Ti.T) % q
        X = np.zeros((len(cells), 3), dtype=np.int64)
        w = q ** np.arange(m - 1, -1, -1, dtype=np.int64)
        for c in range(3):
            X[:, c] = ((v @ self.C[c].T) % q) @ w
        assert np.all(X // q ** (2 * k) == cells), "point not in its cell"
        return X

    def all_pts(self):
        G = self.q ** self.k
        g = np.stack(np.meshgrid(*(np.arange(G),) * 3, indexing='ij'), -1).reshape(-1, 3)
        return self.pts_cells(g)

    def index_pts(self):
        """all q^m points by index enumeration: index digits v_l (least significant first), coordinate digits
        C_c v mod q (most significant first) -- independent of the cell-wise evaluation"""
        q, m = self.q, self.m
        idx = np.arange(q ** m, dtype=np.int64)
        V = np.stack([(idx // q ** l) % q for l in range(m)], 1)
        w = q ** np.arange(m - 1, -1, -1, dtype=np.int64)
        return np.stack([((V @ Cc.T) % q) @ w for Cc in self.C], 1)


def is_0m3_net(P, q, m):
    """every elementary box q^-d1 x q^-d2 x q^-d3, d1+d2+d3 = m, holds exactly one point"""
    for d1 in range(m + 1):
        for d2 in range(m + 1 - d1):
            d3 = m - d1 - d2
            key = ((P[:, 0] // q ** (m - d1)) * q ** d2 + P[:, 1] // q ** (m - d2)) * q ** d3 + P[:, 2] // q ** (m - d3)
            if len(np.unique(key)) != q ** m:
                return False
    return True


def check_full(net):
    P = net.all_pts()
    Q = net.index_pts()
    assert len(Q) == len(P) and set(map(tuple, P)) == set(map(tuple, Q)), (net.q, net.m)
    assert is_0m3_net(P, net.q, net.m), ('not a (0,m,3)-net', net.q, net.m)
    return P


U1 = np.array([1, -1, 0]) / np.sqrt(2); U2 = np.array([1, 1, -2]) / np.sqrt(6)   # orthonormal basis of (1,1,1)-perp


def style(ax, lim=None):
    ax.set_aspect('equal'); ax.tick_params(length=1.5, pad=1)
    for s in ax.spines.values(): s.set_color('#808080')
    if lim is not None: ax.set_xlim(*lim[0]); ax.set_ylim(*lim[1])


def dot(n):  # marker size by count, for print
    return 4.0 if n <= 150 else 1.6 if n <= 1500 else 0.5 if n <= 5000 else 0.12


MM = np.array([[-1, -1, 1], [1, -1, -1], [-1, 1, -1]])


def slab_panel(ax, net, W, title, dotsize):
    """one z-cell layer, W x W window of cells, xy view in cell units; accent segments = slip edges, i.e. cell
    edges across which the (x, y) part of the point step deviates from the tilted-lattice step (I + M/q)e by more
    than 1/2 (a wrap of the geometric digit, visible in this view)."""
    q, k = net.q, net.k; G = q ** k; W = min(W, G)
    x0 = (G - W) // 2; y0 = (G - W) // 3; z0 = G // 2
    gx, gy = np.meshgrid(np.arange(x0, x0 + W), np.arange(y0, y0 + W), indexing='ij')
    cells = np.stack([gx.ravel(), gy.ravel(), np.full(gx.size, z0)], -1)
    X = (net.pts_cells(cells) / q ** (2 * k)).reshape(W, W, 3)
    for t in range(W + 1):
        ax.plot([x0 + t] * 2, [y0, y0 + W], color=GRID, lw=0.2, zorder=0)
        ax.plot([x0, x0 + W], [y0 + t] * 2, color=GRID, lw=0.2, zorder=0)
    nslip = 0
    for a, e in (((0, np.array([1, 0, 0])), (1, np.array([0, 1, 0]))) if k >= 2 else ()):   # M needs k >= 2
        step = e + MM @ e / q
        for i in range(W - (a == 0)):
            for j in range(W - (a == 1)):
                d = X[i + (a == 0), j + (a == 1)] - X[i, j] - step
                if np.abs(d[:2]).max() > 0.5:
                    nslip += 1
                    if a == 0: ax.plot([x0 + i + 1] * 2, [y0 + j, y0 + j + 1], color=ACC, lw=0.6, zorder=1)
                    else: ax.plot([x0 + i, x0 + i + 1], [y0 + j + 1] * 2, color=ACC, lw=0.6, zorder=1)
    P = X.reshape(-1, 3)
    ax.scatter(P[:, 0], P[:, 1], s=dotsize, c=INK, lw=0, zorder=2)
    style(ax, ((x0, x0 + W), (y0, y0 + W))); ax.set_xticks([]); ax.set_yticks([])
    ax.set_title(title, fontsize=6.5, pad=2)
    return W, len(P), nslip


# ---------------------------------------------------------------- fig:full: full projections, small N
def fig_full():
    cases = [(4, 3), (5, 3), (7, 3), (11, 3), (4, 6), (5, 6)]
    fig, axes = plt.subplots(len(cases), 4, figsize=(5.0, 1.27 * len(cases)))
    info = []
    for r, (q, m) in enumerate(cases):
        P = check_full(Net(q, m)) / q ** m; n = len(P); s = dot(n)
        info.append((q, m, n))
        for c, (a, b, lab) in enumerate(((0, 1, 'xy'), (0, 2, 'xz'), (1, 2, 'yz'))):
            ax = axes[r, c]; ax.scatter(P[:, a], P[:, b], s=s, c=INK, lw=0, rasterized=n > 5000)
            style(ax, ((0, 1), (0, 1))); ax.set_xticks([0, 1]); ax.set_yticks([0, 1])
            ax.set_title(f'$q={q}$, $m={m}$, $N={n}$: {lab}', fontsize=6, pad=2)
        ax = axes[r, 3]; ax.scatter(P @ U1, P @ U2, s=s, c=INK, lw=0, rasterized=n > 5000)
        style(ax); ax.set_xticks([]); ax.set_yticks([])
        ax.set_title('along $(1,1,1)$', fontsize=6, pad=2)
    fig.tight_layout(pad=0.3, h_pad=0.5, w_pad=0.3)
    fig.savefig(os.path.join(OUT, 'fig_full.pdf'), metadata={'CreationDate': None}); plt.close(fig)
    assert [n for _, m, n in info if m == 6] == [4096, 15625], 'fig:full caption N'
    return info


# ---------------------------------------------------------------- fig:slab: one z-cell slab, window of cells, xy
def fig_slab():
    bases, ms = (4, 5, 7, 11), (3, 6, 9)
    fig, axes = plt.subplots(len(ms), len(bases), figsize=(6.3, 1.72 * len(ms)))
    info = []
    for r, m in enumerate(ms):
        for c, q in enumerate(bases):
            net = Net(q, m); W = min(q ** (m // 3), 18)
            info.append((q, m) + slab_panel(axes[r, c], net, W, f'$q={q}$, $m={m}$, $N={q}^{{{m}}}$',
                                             6 if W < 10 else 2.2))
    fig.tight_layout(pad=0.3, h_pad=0.6, w_pad=0.4)
    fig.savefig(os.path.join(OUT, 'fig_slab.pdf'), metadata={'CreationDate': None}); plt.close(fig)
    # caption: W = q for m = 3 (the whole layer), 16 for q = 4, m = 6, 18 otherwise; 16 to 324 points;
    # no slip edges drawn for k = 1
    for q, m, W, npts, nslip in info:
        assert W == (q if m == 3 else 16 if (q, m) == (4, 6) else 18) and npts == W * W, (q, m, W)
        assert m > 3 or nslip == 0
    assert min(i[3] for i in info) == 16 and max(i[3] for i in info) == 324, 'fig:slab caption point counts'
    return info


# ---------------------------------------------------------------- fig:axis: view along the rotation axis (1,1,1)
def fig_axis():
    bases, ms = (4, 5, 7, 11), (6, 9)
    fig, axes = plt.subplots(len(ms), len(bases), figsize=(6.3, 1.78 * len(ms)))
    info = []
    for r, m in enumerate(ms):
        for c, q in enumerate(bases):
            net = Net(q, m); k = m // 3; G = q ** k; R = min(G, 14); o = (G - R) // 2
            g = np.stack(np.meshgrid(*(np.arange(o, o + R),) * 3, indexing='ij'), -1).reshape(-1, 3)
            X = net.pts_cells(g) / q ** (2 * k); ctr = o + R / 2.0
            ax = axes[r, c]; lim = R / 2.6
            ax.scatter((X - ctr) @ U1, (X - ctr) @ U2, s=0.7, c=INK, lw=0)
            style(ax, ((-lim, lim), (-lim, lim))); ax.set_xticks([]); ax.set_yticks([])
            ax.set_title(f'$q={q}$, $m={m}$: ${R}^3$ cells', fontsize=6.5, pad=2)
            shown = int(np.sum(np.max(np.abs(np.stack([(X - ctr) @ U1, (X - ctr) @ U2], 1)), 1) < lim))
            info.append((q, m, R, len(X), shown))
    fig.tight_layout(pad=0.3, h_pad=0.6, w_pad=0.4)
    fig.savefig(os.path.join(OUT, 'fig_axis.pdf'), metadata={'CreationDate': None}); plt.close(fig)
    # caption: 2744 points of 14^3 cells, central square of half-side 5.4 (= 14/2.6), about 1700 points shown
    assert all(R == 14 and n == 2744 for _, _, R, n, _ in info) and round(14 / 2.6, 1) == 5.4, 'fig:axis caption'
    assert all(1600 <= sh <= 1800 for *_, sh in info), 'fig:axis caption: about 1700 points shown'
    return info


if __name__ == '__main__':
    print('fig_full (q, m, N); cell-wise == index points, (0,m,3)-net:', fig_full())
    print('fig_slab (q, m, W, npts, nslip):', fig_slab())
    print('fig_axis (q, m, R, npts, shown):', fig_axis())
    print('figs_net: all asserted values OK')

#!/usr/bin/env python3
"""figs_eis.py -- the Eisenstein figures of core.tex (Section sec:eis, Appendix app:figs):
eis:figproj, eis:figsep, eis:figdiag, eis:fig3d  ->  figs/eis_fig_{proj,sep,diag,3d}.pdf.

The net (base p, prime p = 1 mod 3, N = p^3 points) is
    P_A = { (phi(v), phi(A v), phi(A^2 v)) : v in F_p^3 },   phi(w) = w0 p^2 + w1 p + w2,
with the closed-form generator
    A(p) = [[w^2, w^2 - 1, (w^2 - 1)/3], [0, 1, 0], [0, 0, w]]  (mod p),
w a primitive cube root of unity mod p.  Equivalently, with x = phi(v) and F(x) = phi(A digits(x)),
the point of index x is (x, F(x), F(F(x))) (the point list `pts` of the Lean entry Eis).

ROOT CONVENTION (as in the paper and the Lean statements `mindist_p7` / `mindist_p13`): the SMALLER
primitive cube root for p >= 13, the LARGER one (w = 4) at p = 7, where it gives the larger separation
(d^2 = 1834 vs 1729).  The closed-form witness d^2_*(p, w) = p^4 - (4/3)p^3 - 2wp^2 - (2/3)p^2 + 2w^2 + 2w + 2
(Proposition eis:witness) is stated for the smaller root.

Figures:
  fig_diag    view along the body diagonal (1,1,1), p = 7, 13, 19 (eis:figdiag)
  fig_proj    the (x,y) projection (a (0,3,2)-net), p = 7, 13, 19 (eis:figproj)
  fig_3d      the p = 7 net (343 points) with its minimum-distance edges (black) and the other
              near-neighbour edges along b_i = (2/3)(1,1,1) - e_i (grey) (eis:fig3d)
  fig_sep     (a) c(p) = sqrt(d^2_min)/p^2 for the 21 primes p = 1 mod 3, 7 <= p <= 199: exact (cell scan over
              the (1,1,1)-elementary boxes), the witness value and the bound (1 - 1/p)/2; (b) p(1 - c) vs w/p
              against w/p + 2/3 (eis:figsep)
ASSERTED (caption values): d^2_min = 1729 (p=7, w=2), 1834 (p=7, w=4), 24531 (p=13, w=3); d^2_*(7,4) = 1561;
exact d^2_min = d^2_* (smaller root) at all 21 primes 7..199.

Self-contained (numpy + matplotlib); deterministic; ~17 s.
    uv run --with numpy --with matplotlib python scripts/figs_eis.py [--out DIR]   (default DIR = figs/)
The committed PDFs were written with matplotlib 3.11.0 (byte-identical output with that version).
"""
import os
import sys
import numpy as np
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
import logging
logging.getLogger('fontTools').setLevel(logging.ERROR)

HERE = os.path.dirname(os.path.abspath(__file__))          # scripts/
OUT = os.path.join(os.path.dirname(HERE), 'figs')           # the paper's figs/
if '--out' in sys.argv:
    OUT = os.path.abspath(sys.argv[sys.argv.index('--out') + 1])

# ------------------------------------------------------------------ the net
def is_prime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def cube_roots(p):
    """the two primitive cube roots of unity mod p, ascending"""
    return [u for u in range(2, p) if pow(u, 3, p) == 1]


def paper_root(p):
    """root convention of the paper / Lean mindist_p7, mindist_p13"""
    r = cube_roots(p)
    return r[1] if p == 7 else r[0]


def closed_form_A(p, w):
    w2 = w * w % p
    u = (w2 - 1) % p
    return np.array([[w2, u, u * pow(3, -1, p) % p], [0, 1, 0], [0, 0, w]], dtype=np.int64)


def net_points(p, w=None):
    """(p^3, 3) int64 array, row x = (x, F(x), F(F(x))), coordinates in [0, p^3)."""
    if w is None:
        w = paper_root(p)
    A = closed_form_A(p, w)
    A2 = A @ A % p
    x = np.arange(p ** 3, dtype=np.int64)
    V = np.stack([x // p ** 2, x // p % p, x % p], axis=1)          # digits, most significant first
    phi = np.array([p * p, p, 1], dtype=np.int64)
    return np.stack([x, (V @ A.T % p) @ phi, (V @ A2.T % p) @ phi], axis=1)


def min_d2(P, p):
    """EXACT squared toroidal minimum distance (integer scale p^3).
    t = 0 for the composition (1,1,1) puts exactly one point in each leading-digit cell
    (cells of side p^2).  A pair at toroidal distance < p^2 has every min-image coordinate
    difference < p^2, so its cells are (cyclically) adjacent; and d^2_min < p^4 (the witness),
    so scanning the 13 half-neighbourhood offsets of the cell grid is exact."""
    N = p ** 3
    G = np.empty((p, p, p, 3), dtype=np.int64)
    c = P // (p * p)
    assert len(np.unique(c @ np.array([p * p, p, 1]))) == p ** 3, 'not one point per (1,1,1)-cell'
    G[c[:, 0], c[:, 1], c[:, 2]] = P
    best = None
    offs = [(a, b, d) for a in (-1, 0, 1) for b in (-1, 0, 1) for d in (-1, 0, 1) if (a, b, d) > (0, 0, 0)]
    for o in offs:
        D = np.roll(G, shift=o, axis=(0, 1, 2)) - G
        D = (D + N // 2) % N - N // 2                                  # minimum image per coordinate
        m = int((D * D).sum(-1).min())
        best = m if best is None else min(best, m)
    assert best < p ** 4
    return best


def d2_witness(p, w):
    """p^4 - (4/3)p^3 - 2wp^2 - (2/3)p^2 + 2w^2 + 2w + 2  (Lean `d2witness`; an integer)"""
    t = 3 * p ** 4 - 4 * p ** 3 - 6 * w * p * p - 2 * p * p + 6 * w * w + 6 * w + 6
    assert t % 3 == 0
    return t // 3




def primes_1mod3(lo, hi):
    return [q for q in range(lo, hi + 1) if q % 3 == 1 and is_prime(q)]


# ------------------------------------------------------------------ style (matches figs_net.py)
plt.rcParams.update({
    'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
    'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False,
    'font.size': 7.5, 'axes.titlesize': 7.5, 'axes.labelsize': 7.5, 'legend.fontsize': 6.5,
    'xtick.labelsize': 6.5, 'ytick.labelsize': 6.5, 'axes.linewidth': 0.4,
    'xtick.major.width': 0.3, 'ytick.major.width': 0.3, 'xtick.major.size': 1.5, 'ytick.major.size': 1.5,
    'pdf.fonttype': 42, 'savefig.dpi': 300})
INK, MID, LIGHT = '#1a1a1a', '#808080', '#bdbdbd'
WIDTH = 5.0                                   # amsart \textwidth (30pc) in inches
DIAG_PS = (7, 13, 19)

# orthonormal basis of the plane perpendicular to (1,1,1); U2 is the projection of +z (up)
U1 = np.array([1.0, -1.0, 0.0]) / np.sqrt(2)
U2 = np.array([-1.0, -1.0, 2.0]) / np.sqrt(6)
PROJ = np.stack([U1, U2], axis=1)             # (3,2)
# the rotated cube axes b_i = (2/3)(1,1,1) - e_i: the cube axes e_i turned by 180 deg about (1,1,1)
BAX = 2.0 / 3.0 - np.eye(3)


def save(fig, name):
    path = os.path.join(OUT, f'eis_{name}.pdf')                   # as included by core.tex
    fig.savefig(path, bbox_inches='tight', pad_inches=0.02, metadata={'CreationDate': None})  # reproducible bytes
    plt.close(fig)
    print('wrote', path)


def square(ax, ticks=True):
    ax.set_aspect('equal')
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.tick_params(length=1.5, pad=1)
    for sp in ax.spines.values():
        sp.set_color(MID)
    if ticks:
        ax.set_xticks([0, 1])
        ax.set_yticks([0, 1])


# ------------------------------------------------------------------ Figure 1: along the body diagonal
def fig_diag():
    """Row 1: the net in the unit cube seen along (1,1,1) (orthographic, viewer at +inf (1,1,1));
    grey level = depth x+y+z, near points drawn last and darkest.  Row 2: the same projection on
    the torus: the plane modulo the projected lattice Lambda = proj(Z^3); points in the
    Voronoi (hexagonal) fundamental domain black, periodic images grey."""
    dot_cube = {7: 5.5, 13: 1.9, 19: 0.9}
    dot_tor = {7: 5.0, 13: 1.7, 19: 0.8}
    fig, axes = plt.subplots(2, len(DIAG_PS), figsize=(WIDTH, 3.42))
    E = np.eye(3) @ PROJ                                       # proj(e_i), |.| = sqrt(2/3)
    L = E[:2].T
    Linv = np.linalg.inv(L)
    sh = np.array([i * E[0] + j * E[1] for i in range(-3, 4) for j in range(-3, 4)])
    i0 = int(np.argmin((sh ** 2).sum(1)))
    rhex = np.sqrt(2) / 3                                      # circumradius of the Voronoi hexagon
    hexv = rhex * np.array([[np.cos(a), np.sin(a)] for a in np.radians(np.arange(0, 360, 60))])
    sil = np.array([(1, 0, 0), (1, 1, 0), (0, 1, 0), (0, 1, 1), (0, 0, 1), (1, 0, 1)]) @ PROJ
    info = []
    for j, p in enumerate(DIAG_PS):
        X = net_points(p) / p ** 3
        Q = X @ PROJ
        h = X.sum(1)
        # (a) cube, depth-shaded
        ax = axes[0, j]
        o = np.argsort(h, kind='stable')
        g = np.clip(0.80 - 0.80 * (h[o] - 1.0) / 1.9, 0.0, 0.80)
        ax.add_patch(plt.Polygon(sil, closed=True, fill=False, lw=0.35, ec=LIGHT, zorder=0))
        ax.scatter(Q[o, 0], Q[o, 1], s=dot_cube[p], c=np.repeat(g[:, None], 3, 1), lw=0, zorder=1)
        ax.set_aspect('equal')
        ax.set_xlim(-0.75, 0.75)
        ax.set_ylim(-0.84, 0.84)
        ax.axis('off')
        ax.set_title(f'$p={p}$,  $N={p ** 3}$', pad=1.5)
        # (b) torus
        ax = axes[1, j]
        R0 = ((Q @ Linv.T) % 1.0) @ L.T
        nsite = len(np.unique(np.round((Q @ Linv.T) % 1.0, 9) % 1.0, axis=0))
        allp = (R0[None] + sh[:, None]).reshape(-1, 2)
        near = ((allp[:, None, :] - sh[None]) ** 2).sum(-1)
        inside = near.argmin(1) == i0
        rad = 0.60
        win = (allp ** 2).sum(1) < (rad - 0.025) ** 2
        ax.scatter(*allp[win & ~inside].T, s=dot_tor[p], c=LIGHT, lw=0, zorder=1)
        ax.scatter(*allp[inside].T, s=dot_tor[p], c=INK, lw=0, zorder=2)
        ax.add_patch(plt.Polygon(hexv, closed=True, fill=False, lw=0.45, ec=MID, zorder=3))
        ax.set_aspect('equal')
        ax.set_xlim(-rad, rad)
        ax.set_ylim(-rad, rad)
        ax.axis('off')
        assert inside.sum() == p ** 3
        info.append((p, nsite))
    axes[0, 0].text(-0.06, 0.5, 'unit cube', transform=axes[0, 0].transAxes, rotation=90,
                    ha='right', va='center')
    axes[1, 0].text(-0.06, 0.5, 'torus', transform=axes[1, 0].transAxes, rotation=90,
                    ha='right', va='center')
    fig.subplots_adjust(left=0.04, right=0.995, top=0.95, bottom=0.0, wspace=0.04, hspace=0.04)
    save(fig, 'fig_diag')
    return info


# ------------------------------------------------------------------ Figure 2: coordinate projections
def fig_proj():
    """The (x,y) projection, which is a (0,3,2)-net, for p = 7, 13, 19.  The cyclic coordinate
    shift (x,y,z) -> (y,z,x) maps the net onto itself (v -> Av, A^3 = I), so the (y,z) projection
    IS the (x,y) projection and the (x,z) projection is its transpose -- asserted below."""
    ps = DIAG_PS
    dot = {7: 2.0, 13: 0.5, 19: 0.2}
    fig, axes = plt.subplots(1, len(ps), figsize=(WIDTH, 1.78))
    for c, p in enumerate(ps):
        P = net_points(p)
        xy = set(map(tuple, P[:, [0, 1]].tolist()))
        assert xy == set(map(tuple, P[:, [1, 2]].tolist())) == set(map(tuple, P[:, [2, 0]].tolist()))
        X = P / p ** 3
        ax = axes[c]
        ax.scatter(X[:, 0], X[:, 1], s=dot[p], c=INK, lw=0)
        square(ax)
        ax.set_title(f'$p={p}$,  $N={p ** 3}$', pad=2)
        ax.set_xlabel('$x$', labelpad=-4)
        if c == 0:
            ax.set_ylabel('$y$', labelpad=-3)
    fig.subplots_adjust(left=0.04, right=0.99, top=0.9, bottom=0.1, wspace=0.12)
    save(fig, 'fig_proj')


# ------------------------------------------------------------------ Figure 3: 3D view, p = 7
def fig_3d():
    from mpl_toolkits.mplot3d.art3d import Line3DCollection
    p = 7
    N = p ** 3
    P = net_points(p)
    D = P[None, :, :] - P[:, None, :]
    Dm = (D + N // 2) % N - N // 2
    wrap = np.any(Dm != D, axis=-1)                           # pair is nearest only across the torus
    d2 = (Dm ** 2).sum(-1)
    np.fill_diagonal(d2, np.iinfo(np.int64).max)
    dmin = int(d2.min())
    V = Dm / p ** 2                                           # difference in units of 1/p
    axis_cls = np.full(d2.shape, -1)
    for k in range(3):
        dev = np.minimum(np.linalg.norm(V - BAX[k], axis=-1), np.linalg.norm(V + BAX[k], axis=-1))
        axis_cls[dev < 0.3] = k
    iu = np.triu_indices(N, 1)
    is_min = d2[iu] == dmin
    is_ax = axis_cls[iu] >= 0
    assert np.all(is_ax[is_min]), 'a minimum-distance pair is not along a rotated cube axis'
    X = P / N

    def az_el(v):
        v = v / np.linalg.norm(v)
        return np.degrees(np.arctan2(v[1], v[0])), np.degrees(np.arcsin(v[2]))

    tilt = np.ones(3) / np.sqrt(3) + np.array([0.16, -0.06, -0.10])     # ~11 deg off the diagonal
    views = [('(a) along $(1,1,1)$', az_el(np.ones(3)), True),
             ('(b) tilted $11^\\circ$ off $(1,1,1)$', az_el(tilt), False)]
    cube_e = [((0, 0, 0), (1, 0, 0)), ((0, 0, 0), (0, 1, 0)), ((0, 0, 0), (0, 0, 1)),
              ((1, 1, 1), (0, 1, 1)), ((1, 1, 1), (1, 0, 1)), ((1, 1, 1), (1, 1, 0)),
              ((1, 0, 0), (1, 1, 0)), ((1, 0, 0), (1, 0, 1)), ((0, 1, 0), (1, 1, 0)),
              ((0, 1, 0), (0, 1, 1)), ((0, 0, 1), (1, 0, 1)), ((0, 0, 1), (0, 1, 1))]
    fig = plt.figure(figsize=(WIDTH, 2.62))
    for t, (title, (az, el), grey_edges) in enumerate(views):
        ax = fig.add_axes([0.5 * t, 0.0, 0.5, 0.92], projection='3d', proj_type='ortho')
        ax.add_collection3d(Line3DCollection(np.array(cube_e, float), colors='#d4d4d4', linewidths=0.35))
        if grey_edges:
            m = is_ax & ~is_min & ~wrap[iu]
            ax.add_collection3d(Line3DCollection(np.stack([X[iu[0][m]], X[iu[1][m]]], 1),
                                                 colors='#a0a0a0', linewidths=0.3))
        m = is_min & ~wrap[iu]
        ax.add_collection3d(Line3DCollection(np.stack([X[iu[0][m]], X[iu[1][m]]], 1),
                                             colors=INK, linewidths=0.85))
        ax.scatter(*X.T, s=2.0, c=INK, lw=0, depthshade=False)
        ax.view_init(elev=el, azim=az)
        ax.set_box_aspect((1, 1, 1), zoom=1.18)
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        ax.set_zlim(0, 1)
        ax.set_axis_off()
        fig.text(0.5 * t + 0.25, 0.965, title, ha='center', va='center')
    save(fig, 'fig_3d')
    return dict(dmin=dmin, n_min=int(is_min.sum()), n_min_drawn=int((is_min & ~wrap[iu]).sum()),
                n_axis_edges=int(is_ax.sum()),
                n_min_per_axis=[int((is_min & (axis_cls[iu] == k)).sum()) for k in range(3)])


# ------------------------------------------------------------------ Figure 4: separation constant
def sep_data(pmax=199):
    rows = []
    for p in primes_1mod3(7, pmax):
        w = cube_roots(p)[0]                                  # smaller root (witness formula)
        d2 = min_d2(net_points(p, w), p)
        rows.append((p, w, d2, d2_witness(p, w)))
    return rows


def fig_sep(rows):
    p = np.array([r[0] for r in rows], float)
    w = np.array([r[1] for r in rows], float)
    c = np.sqrt([r[2] for r in rows]) / p ** 2
    cw = np.sqrt([float(r[3]) for r in rows]) / p ** 2
    c7big = np.sqrt(min_d2(net_points(7, 4), 7)) / 49          # paper's root at p = 7 (Lean: 1834)
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(WIDTH, 2.0), gridspec_kw=dict(width_ratios=(1.25, 1)))
    pp = np.linspace(7, p.max() + 6, 400)
    a1.axhline(1.0, color=LIGHT, lw=0.5, zorder=0)
    a1.plot(pp, 0.5 * (1 - 1 / pp), color=MID, lw=0.7, ls=(0, (4, 2)), label=r'lower bound $\frac{1}{2}(1-\frac{1}{p})$')
    a1.plot(p, cw, 'o', ms=4.6, mfc='none', mec=INK, mew=0.5, label='witness (upper bound)')
    a1.plot(p, c, 'o', ms=1.7, color=INK, mew=0, label=r'exact $c(p)$, smaller $\omega$')
    a1.plot([7], [c7big], '^', ms=3.4, mfc='none', mec=INK, mew=0.5, label=r'exact $c(7)$, $\omega=4$')
    a1.set_xlim(0, p.max() + 6)
    a1.set_ylim(0.4, 1.04)
    a1.set_xlabel('$p$', labelpad=1)
    a1.set_ylabel(r'$c(p)=\sqrt{d^2_{\min}}\,/\,p^2$', labelpad=2)
    a1.legend(loc='center right', bbox_to_anchor=(1.0, 0.47), frameon=False, handlelength=1.8, borderaxespad=0.2, labelspacing=0.3)
    # (b) rate: p(1 - c) against omega/p, vs the witness rate omega/p + 2/3
    x = w / p
    y = p * (1 - c)
    xx = np.linspace(0, 0.5, 2)
    a2.plot(xx, xx + 2 / 3, color=MID, lw=0.7, ls=(0, (4, 2)), label=r'$\omega/p+\frac{2}{3}$')
    a2.scatter(x, y, s=np.clip(40 / np.sqrt(p), 2, 14), facecolors='none', edgecolors=INK, lw=0.5,
               label=r'$p\,(1-c(p))$')
    for pi, xi, yi in zip(p, x, y):
        if pi in (7, 13, 19, 31, 97, 181, 199):
            a2.annotate(f'{int(pi)}', (xi, yi), xytext=(2.5, -1.5), textcoords='offset points', fontsize=5.5)
    a2.set_xlim(0, 0.5)
    a2.set_ylim(0.6, 1.3)
    a2.set_xlabel(r'$\omega/p$  (smaller root)', labelpad=1)
    a2.set_ylabel(r'$p\,(1-c(p))$', labelpad=2)
    a2.legend(loc='upper left', frameon=False, handlelength=1.8, borderaxespad=0.2, labelspacing=0.3)
    for ax in (a1, a2):
        ax.tick_params(length=1.5, pad=1.5)
        for sp in ax.spines.values():
            sp.set_color(MID)
    a1.set_title('(a)', pad=2)
    a2.set_title('(b)', pad=2)
    fig.subplots_adjust(left=0.08, right=0.99, top=0.92, bottom=0.17, wspace=0.28)
    save(fig, 'fig_sep')


# ------------------------------------------------------------------ asserted caption values
def check():
    for p, w, val in [(7, 2, 1729), (7, 4, 1834), (13, 3, 24531)]:
        d2 = min_d2(net_points(p, w), p)
        print(f'  exact d2_min p={p} w={w}: {d2}   (paper / Lean: {val})')
        assert d2 == val, (p, w, d2, val)
    assert d2_witness(7, 4) == 1561 and d2_witness(7, 2) == 1729, 'd2_* at p = 7'
    print('  d2_*(7,4) = 1561, d2_*(7,2) = 1729')
    roots = {p: paper_root(p) for p in (7, 13, 19)}
    assert roots == {7: 4, 13: 3, 19: 7}, roots
    print('  paper roots:', roots)


if __name__ == '__main__':
    os.makedirs(OUT, exist_ok=True)
    check()
    print('fig_diag (p, distinct projected sites on the torus):', fig_diag())
    fig_proj()
    print('fig_3d:', fig_3d())
    rows = sep_data()
    bad = [r for r in rows if r[2] != r[3]]
    print('fig_sep: exact d2_min == witness for the smaller root at all %d primes 7..%d: %s'
          % (len(rows), rows[-1][0], not bad), bad or '')
    assert len(rows) == 21 and rows[0][0] == 7 and rows[-1][0] == 199 and not bad, 'eis:figsep caption'
    fig_sep(rows)
    print('figs_eis: all asserted values OK')

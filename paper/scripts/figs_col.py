#!/usr/bin/env python3
"""figs_col.py -- the figures of the column nets and of the drift-and-jitter accounting (rev 15.0).

  col_net    fig:col    the column net C_5 (def:col, thm:col): (a) in 3D, columns parallel to (1,1,1), points coloured
                        by their height phi; (b) viewed along (1,1,1): the triangular lattice of columns, each drawn as
                        a dial whose hand shows the height of its points modulo the spacing; the closest pair.
  col_drift  fig:drift  (a), (b) the holonomy: heights along the three cycles through one column of C_11 and C_13,
                        against the ideal step q^2/3 of the reflected cube; (c) p(1-c) for the column nets (exact,
                        thm:col), the frozen-drift nets J_p and E_p (exact values, computed; colnets_exact.json).
  col_half5  fig:half5  s = 5, one resolution: exact c of Q*_p and the certificates LB_2 (lem:R2) of Q*_p and
                        LB (prop:Hk(1)) of F_0^* and of M_5, from half5_exact.json.

Every number in the captions is computed here and asserted; the nets are rebuilt from Definition def:col and checked
against the closed form of Theorem thm:col by brute force.  Writes figs/col_{net,drift,half5}.pdf and
figs/col_captions.tex.

    uv run --with numpy --with matplotlib python scripts/figs_col.py [--out DIR]       (deterministic; ~2 s)
"""
import os
import sys
import json
import itertools
import time
import numpy as np
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.collections import LineCollection
from matplotlib.colors import LinearSegmentedColormap
import logging
logging.getLogger('fontTools').setLevel(logging.ERROR)

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(HERE), 'figs')
if '--out' in sys.argv:
    OUT = os.path.abspath(sys.argv[sys.argv.index('--out') + 1])
os.makedirs(OUT, exist_ok=True)

plt.rcParams.update({
    'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
    'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False,
    'font.size': 7.5, 'axes.titlesize': 7.5, 'axes.labelsize': 7.5, 'legend.fontsize': 6.8,
    'xtick.labelsize': 6.3, 'ytick.labelsize': 6.3, 'axes.linewidth': 0.4,
    'xtick.major.width': 0.3, 'ytick.major.width': 0.3, 'xtick.major.size': 1.5, 'ytick.major.size': 1.5,
    'pdf.fonttype': 42, 'savefig.dpi': 300, 'svg.hashsalt': 'core', 'pdf.compression': 6})
WIDTH = 6.3
INK, GRID, LATE, JIT, ACC = '#111111', '#c8c8c8', '#6f6f6f', '#4a4a4a', '#2b6cb0'
MID = '#8a8a8a'
CMAP = LinearSegmentedColormap.from_list('heights', ['#dfe6ee', ACC, '#0d2a4d'])
ONE = np.ones(3)
U1 = np.array([1, -1, 0]) / np.sqrt(2)
U2 = np.array([1, 1, -2]) / np.sqrt(6)

CHECKS = []


def check(fig, cond, what):
    if not cond:
        raise AssertionError(f'[{fig}] {what}')
    CHECKS.append((fig, what))


def save(fig, name):
    fig.savefig(os.path.join(OUT, name + '.pdf'), metadata={'CreationDate': None, 'ModDate': None})
    fig.savefig(os.path.join(OUT, name + '.png'), dpi=150)
    plt.close(fig)


def panel_title(ax, s):
    ax.set_title(s, fontsize=7.5, pad=3)


def ffloor(x, d):
    import math
    v = math.floor(float(x) * 10 ** d + 1e-9) / 10 ** d
    return f'%.{d}f' % v


# ---------------------------------------------------------------- the column nets (def:col, thm:col)
def col_w(q):
    assert q % 2 and q % 3 and q >= 5
    return np.array([-2, 1, 1]) if q % 3 == 2 else np.array([-1, -1, 2])


def col_net(q):
    """cells n (q^3 x 3) and the heights phi(n) = q h + j, h = a.n, j = n_y - n_x (mod q)."""
    a = (q + col_w(q)) // 3
    n = np.array(list(itertools.product(range(q), repeat=3)))
    h = (n @ a) % q
    j = (n[:, 1] - n[:, 0]) % q
    return a, n, q * h + j


def tau(q):
    return q * q - q - 3 if q % 3 == 2 else q * q - 2 * q


def d2_closed(q):
    return (2 * q ** 4 + tau(q) ** 2) // 3


def brute_d2(q):
    """exact toroidal minimum squared distance at integer scale q^3, all pairs (q <= 13)."""
    a, n, phi = col_net(q)
    X = q * q * n + phi[:, None]
    M = q ** 3
    best, arg = None, None
    for i in range(len(X)):
        d = np.abs(X[i + 1:] - X[i]) % M
        d = np.minimum(d, M - d)
        s = (d * d).sum(1)
        if len(s):
            k = int(s.argmin())
            if best is None or s[k] < best:
                best, arg = int(s[k]), (i, i + 1 + k)
    return best, arg


def column_segments(P0, q):
    """the closed line {P0 + t 1 mod q} on the torus [0,q)^3, as straight segments inside the cube."""
    segs = []
    t = 0.0
    P = P0.copy()
    while t < q - 1e-12:
        # distance along 1 to the next wrap of some coordinate
        dt = min(q - P.max(), q - t)
        segs.append([P.copy(), P + dt * ONE])
        t += dt
        P = (P + dt * ONE)
        P[P >= q - 1e-12] -= q
    return segs


# ================================================================== col_net
def fig_net():
    q = 5
    a, n, phi = col_net(q)
    d2, (i0, i1) = brute_d2(q)
    check('net', d2 == d2_closed(q) == 513, f'C_{q}: brute-force toroidal d^2 = {d2} = closed form of thm:col (513)')
    # t = 0 by box counting (all 10 shapes)
    X = q * q * n + phi[:, None]
    dig = np.stack([X // q ** 2, (X // q) % q, X % q], 2)          # (point, coordinate, digit)
    ok = True
    for d in itertools.product(range(4), repeat=3):
        if sum(d) != 3:
            continue
        keys = {tuple(int(v) for c in range(3) for v in dig[k, c, :d[c]]) for k in range(len(X))}
        ok &= len(keys) == q ** 3
    check('net', ok, f'C_{q} is a (0,3,3)-net (box counting, all 10 shapes)')
    # the closest pairs differ by +-D
    Dq = np.array([-(2 * q * q - q - 3), q * q + q + 3, -(2 * q * q - q - 3)]) // 3
    M = q ** 3
    cl = []
    for i in range(len(X)):
        d = (X - X[i]) % M
        d = np.where(d > M // 2, d - M, d)
        s = (d * d).sum(1)
        s[i] = 10 ** 18
        for k in np.where(s == d2)[0]:
            cl.append(tuple(d[k]))
    check('net', set(cl) == {tuple(Dq), tuple(-Dq)}, f'every closest pair of C_{q} differs by +-D = +-{tuple(Dq)}')
    P = n + (phi / q ** 2)[:, None]                                  # cell units
    # a closest pair whose straight segment stays in the cube
    pick = None
    for i in range(len(P)):
        Q = P[i] + Dq / q ** 2
        if np.all(Q >= 0) and np.all(Q < q):
            k = np.where(np.all(np.abs(P - Q) < 1e-9, axis=1))[0]
            if len(k):
                pick = (i, int(k[0]))
                if 1.0 < P[i].min() and P[i].max() < 4.0:
                    break
    check('net', pick is not None, 'a closest pair inside the drawn cube')

    fig = plt.figure(figsize=(WIDTH, 3.05))
    # ---- (a) 3D
    ax = fig.add_axes([-0.05, 0.03, 0.56, 0.88], projection='3d', proj_type='ortho')
    for P0, P1 in itertools.product(itertools.product((0, q), repeat=3), repeat=2):
        if sum(x != y for x, y in zip(P0, P1)) == 1 and P0 < P1:
            ax.plot(*np.stack([P0, P1], 1), color=GRID, lw=0.5)
    cols = {}
    for k in range(len(n)):
        key = tuple((n[k] - n[k][2]) % q)
        cols.setdefault(key, k)
    for key, k in cols.items():
        for s0, s1 in column_segments(P[k], q):
            ax.plot(*np.stack([s0, s1], 1), color='#b9b9b9', lw=0.45, zorder=1)
    sc = ax.scatter(*P.T, c=phi, cmap=CMAP, vmin=0, vmax=q * q - 1, s=11, lw=0.25, edgecolors='#333333',
                    depthshade=False)
    i, k = pick
    ax.plot(*np.stack([P[i], P[k]], 1), color=ACC, lw=2.0, zorder=10)
    mid = (P[i] + P[k]) / 2
    ax.text(*(mid + np.array([0.0, 0.0, 0.45])), r'$D$', color=ACC, fontsize=8)
    ax.view_init(elev=20, azim=-62)
    ax.set_box_aspect((1, 1, 1), zoom=1.18)
    ax.set_axis_off()
    fig.text(0.24, 0.93, r'(a) $\mathcal{C}_5$: $125$ points on $25$ columns parallel to $(1,1,1)$', ha='center',
             fontsize=7.5)
    cax = fig.add_axes([0.075, 0.08, 0.17, 0.022])
    cb = fig.colorbar(sc, cax=cax, orientation='horizontal', ticks=[0, 12, 24])
    cb.outline.set_linewidth(0.3)
    cb.ax.tick_params(labelsize=5.8, length=1.2, pad=1)
    cax.set_title(r'height $\varphi(n)$', fontsize=6.0, pad=2)
    # ---- (b) along (1,1,1): the triangular lattice of columns of C_11, one period; dials = height phase
    ax = fig.add_axes([0.50, 0.03, 0.49, 0.86])
    qb = 11
    ab, nb_, phib = col_net(qb)
    idb = {tuple(v): k for k, v in enumerate(nb_)}
    Db = np.array([-(2 * qb * qb - qb - 3), qb * qb + qb + 3, -(2 * qb * qb - qb - 3)]) // 3
    Xb = qb * qb * nb_ + phib[:, None]
    Mb = qb ** 3
    wb = col_w(qb)
    sites, dev, cells = [], [], []
    for x in range(qb):
        for y in range(qb):
            m = np.array([x, y, 0])
            k = idb[tuple(m)]
            sites.append(np.array([m @ U1, m @ U2]))
            psi = (m.sum() / 3 + phib[k] / qb ** 2) % 1.0                    # height along 1, in turns of sqrt3
            d_ = (wb @ m) / (3 * qb) + ((m[1] - m[0]) % qb) / qb ** 2        # drift + jitter, unwrapped
            check_dev = (psi - 2 * m.sum() / 3 - d_) % 1.0
            assert min(check_dev, 1 - check_dev) < 1e-9                       # psi = 2 sigma/3 + drift + jitter
            dev.append(d_)
            cells.append(m)
    sites, dev, cells = np.array(sites), np.array(dev), np.array(cells)
    check('net', True, f'C_{qb}: the height phase of every column is 2 sigma(n)/3 (reflected cube) + w.n/(3q) (drift) '
                       f'+ j(n)/q^2 (jitter), modulo 1')
    from matplotlib.patches import RegularPolygon
    from matplotlib.collections import PatchCollection
    hexr = np.sqrt(2.0) / 3.0                                              # circumradius of the Voronoi hexagon of P Z^3
    pc = PatchCollection([RegularPolygon(s_, 6, radius=hexr, orientation=0) for s_ in sites], cmap=CMAP,
                         edgecolors='white', linewidths=0.25, zorder=2)
    pc.set_array(dev)
    pc.set_clim(dev.min(), dev.max())
    ax.add_collection(pc)
    gx = (wb[0] - wb[2]) / (3 * qb)
    check('net', abs(dev.max() - dev.min() - (abs(wb[0] - wb[2]) + abs(wb[1] - wb[2])) * (qb - 1) / (3 * qb)) < 0.1,
          'the deviation is a linear ramp (drift) plus a ripple below 1/q (jitter)')
    # neighbour steps turn the dial by 2/3 + drift + jitter
    steps = []
    for k in range(len(nb_)):
        for i_ in range(3):
            m = nb_[k] + np.eye(3, dtype=int)[i_]
            k2 = idb[tuple(m % qb)]
            steps.append(((m.sum() - nb_[k].sum()) / 3 + (phib[k2] - phib[k]) / qb ** 2) % 1.0)
    steps = np.array(steps)
    check('net', np.all(np.abs(steps - 2 / 3) < 0.25),
          f'C_{qb}: every neighbour step turns the dial by 2/3 + O(1/q) (the reflected cube turns it back by 1/3)')
    # a closest pair of C_11 between neighbouring columns, near the centre of the drawn period
    best = None
    for k, m in enumerate(cells):
        mm = idb[tuple((m + np.array([0, 1, 0])) % qb)]
        d = (Xb[mm] - Xb[idb[tuple(m)]]) % Mb
        d = np.where(d > Mb // 2, d - Mb, d)
        if np.array_equal(d, Db) and m[1] < qb - 1:
            dist = np.linalg.norm(sites[k] - sites.mean(0))
            if best is None or dist < best[0]:
                best = (dist, k)
    check('net', best is not None, f'C_{qb}: a closest pair (difference D) between neighbouring drawn columns')
    db2 = int((Db * Db).sum())
    check('net', db2 == d2_closed(qb), f'C_{qb}: |D|^2 = {db2} = closed form of thm:col')
    kb = best[1]
    pD = np.array([Db @ U1, Db @ U2]) / qb ** 2
    check('net', np.allclose(pD, [np.array([0, 1, 0]) @ U1, np.array([0, 1, 0]) @ U2]),
          'along (1,1,1) the closest pair joins neighbouring columns: D projects to P e_y')
    seg = np.stack([sites[kb], sites[kb] + pD])
    ax.plot(*seg.T, color='white', lw=3.2, zorder=5, solid_capstyle='round')
    ax.plot(*seg.T, color=INK, lw=1.3, zorder=6, solid_capstyle='round')
    ax.annotate(r'$D$', xy=sites[kb] + 0.5 * pD, xytext=(sites[kb][0] - 1.6, sites[kb][1] + 1.3), fontsize=8,
                color=INK, ha='center', va='center', zorder=7,
                arrowprops=dict(arrowstyle='-', color=INK, lw=0.5, shrinkA=1, shrinkB=2))
    cax = fig.add_axes([0.83, 0.10, 0.13, 0.022])
    cb = fig.colorbar(pc, cax=cax, orientation='horizontal')
    cb.outline.set_linewidth(0.3)
    cb.ax.tick_params(labelsize=5.6, length=1.2, pad=1)
    cb.set_ticks([round(dev.min() + 0.05, 1), 0, round(dev.max() - 0.05, 1)])
    cax.set_title('deviation (turns)', fontsize=6.0, pad=2)
    corn = [np.array([x, y, 0]) for x, y in ((0, 0), (qb, 0), (qb, qb), (0, qb), (0, 0))]
    off = -0.5 * np.array([np.array([1, 1, 0]) @ U1, np.array([1, 1, 0]) @ U2])
    poly = np.array([[c @ U1, c @ U2] for c in corn]) + off
    o = np.array([sites[:, 0].min() + 0.6, sites[:, 1].max() - 1.0])
    for i_, nm in enumerate('xyz'):
        cx = np.eye(3)[i_]
        pv = 0.9 * np.array([cx @ U1, cx @ U2])
        ax.annotate('', xy=o + pv, xytext=o, arrowprops=dict(arrowstyle='-|>', color=MID, lw=0.6, mutation_scale=4.5,
                                                             shrinkA=0, shrinkB=0))
        ax.text(*(o + 1.3 * pv), r'$e_{%s}$' % nm, fontsize=5.8, color='#5a5a5a', ha='center', va='center')
    ax.set_aspect('equal')
    ax.set_xlim(sites[:, 0].min() - 0.5, sites[:, 0].max() + 0.5)
    ax.set_ylim(sites[:, 1].min() - 0.5, sites[:, 1].max() + 0.5)
    ax.axis('off')
    panel_title(ax, r'(b) $\mathcal{C}_{11}$ along $(1,1,1)$: deviation from $H\mathbb{Z}^3$')
    save(fig, 'col_net')
    return dict(q=q, d2=d2, D=Dq.tolist(), c=float(np.sqrt(d2) / q ** 2), npts=len(n), ncol=len(cols), qb=qb,
                Db=Db.tolist(), d2b=db2, cb=float(np.sqrt(db2) / qb ** 2),
                stepmin=float(steps.min()), stepmax=float(steps.max()))


# ================================================================== col_drift
def cycle_heights(q, i):
    """heights along the cycle of q steps in direction e_i from the column of the cell 0: cumulative sums of the
    representatives x of the step values in the window around q^2/3 (Theorem thm:O, case of sum q^2)."""
    a, n, phi = col_net(q)
    idx = {tuple(v): k for k, v in enumerate(n)}
    m = np.zeros(3, dtype=int)
    xs = []
    for t in range(q):
        m2 = (m + np.eye(3, dtype=int)[i]) % q
        dl = (phi[idx[tuple(m2)]] - phi[idx[tuple(m)]]) % q ** 2
        x = dl - q * q if dl > 5 * q * q / 6 else dl                     # representative in (-q^2/6, 5q^2/6]
        xs.append(int(x))
        m = m2
    return np.array(xs)


def fig_drift():
    C = json.load(open(os.path.join(HERE, 'colnets_exact.json')))
    res = {}
    fig = plt.figure(figsize=(WIDTH, 2.35))
    styles = [dict(color=MID, ls=(0, (1.2, 1.2))), dict(color=INK, ls='-'), dict(color=ACC, ls='-')]
    for pn, q in enumerate((11, 13)):
        ax = fig.add_axes([0.085 + 0.25 * pn, 0.19, 0.195, 0.66])
        w = col_w(q)
        a = (q + w) // 3
        r = np.array([q - 1, 1, 0])
        eps = q * w / 3 + r
        info = []
        for i in range(3):
            xs = cycle_heights(q, i)
            e = xs - q * q / 3
            check('drift', abs(e.sum() - q * q * w[i] / 3) < 1e-9,
                  f'C_{q}: excesses along the e_{"xyz"[i]}-cycle sum to q^2 w_i/3 (lem:drift(2))')
            check('drift', set(np.round(e, 9)) <= {round(eps[i], 9), round(eps[i] - q, 9)} and
                  int(np.sum(np.abs(e - (eps[i] - q)) < 1e-9)) == r[i],
                  f'C_{q}: e_{"xyz"[i]} steps have excess eps_i or eps_i - q, the latter exactly r_i = {r[i]} times')
            H = np.r_[0, np.cumsum(xs)] / q ** 2
            check('drift', abs(H[-1] - round(H[-1])) < 1e-12 and abs(H[-1] - (q / 3 + w[i] / 3)) < 1e-12,
                  f'C_{q}: the e_{"xyz"[i]}-cycle closes at the integer q/3 + w_i/3 = {H[-1]:.0f} (units of q^2)')
            Ex = H - np.arange(q + 1) / 3                                   # height minus the ideal t q^2/3
            ax.plot(np.arange(q + 1), Ex, lw=0.9, marker='o', ms=1.7, **styles[i], zorder=3)
            ax.plot(np.arange(q + 1), np.arange(q + 1) * w[i] / (3 * q), lw=0.45, color=styles[i]['color'],
                    ls=(0, (1, 1.6)), zorder=2)
            info.append((int(round(H[-1])), w[i]))
        ax.axhline(0, color=JIT, lw=0.5, ls=(0, (4, 2)), zorder=1)
        for v in sorted(set(w)):
            ax.annotate('', xy=(q + 0.45, v / 3), xytext=(q + 0.45, 0),
                        arrowprops=dict(arrowstyle='-|>', color=ACC, lw=0.8, mutation_scale=5, shrinkA=0, shrinkB=0))
            ax.text(q + 0.75, v / 3, r'$%s$' % {-2: '-\\frac{2}{3}', -1: '-\\frac{1}{3}', 1: '+\\frac{1}{3}',
                                                2: '+\\frac{2}{3}'}[int(v)], fontsize=6.0, color=ACC, va='center')
        ax.set_xlim(-0.3, q + 2.3)
        ax.set_ylim(-0.95, 0.95)
        ax.set_xticks([0, q])
        ax.set_xlabel(r'step $t$ along a cycle', labelpad=0)
        if pn == 0:
            ax.set_ylabel(r'(height $-\,t\,q^2/3)/q^2$', labelpad=1)
        for sp_ in ax.spines.values():
            sp_.set_color('#9a9a9a')
        panel_title(ax, r'(%s) $\mathcal{C}_{%d}$, $q\equiv%d$, $w=(%d,%d,%d)$' % ('ab'[pn], q, q % 3, *w))
        res[q] = dict(ends=[h for h, _ in info], w=w.tolist(), eps=[float(x) for x in eps], eta=float(eps.max()))
    hl = [Line2D([], [], lw=0.9, label=r'along $e_%s$' % 'xyz'[i], **styles[i]) for i in range(3)] + \
        [Line2D([], [], color=JIT, lw=0.5, ls=(0, (4, 2)), label=r'ideal'),
         Line2D([], [], color=INK, lw=0.45, ls=(0, (1, 1.6)), label=r'drift')]
    fig.legend(handles=hl, loc='lower center', ncol=5, frameon=False, bbox_to_anchor=(0.29, -0.01), fontsize=6.0,
               handlelength=1.8, columnspacing=0.9)
    # ---- (c) deficits
    ax = fig.add_axes([0.62, 0.19, 0.37, 0.66])
    pr = [p for p in range(5, 200) if all(p % d for d in range(2, int(p ** .5) + 1))]
    lims = {}
    for nm, key, mk, colr, lab in (('E', 'E', 'x', MID, r'$\mathcal{E}_p$'), ('J', 'J', '^', INK, r'$\mathcal{J}_p$')):
        for cls in (1, 2):
            ps = [p for p in pr if p % 3 == cls and str(p) in C[key]]
            v = [p * (1 - np.sqrt(C[key][str(p)]['d2']) / p ** 2) for p in ps]
            if mk == 'x':
                ax.scatter(ps, v, s=8, marker=mk, lw=0.5, c=colr, zorder=3)
            else:
                ax.scatter(ps, v, s=7, marker=mk, lw=0.5, facecolors=(colr if cls == 2 else 'none'), edgecolors=colr,
                           zorder=3)
            lims[(nm, cls)] = v[-1]
    for cls in (1, 2):
        ps = [p for p in pr if p % 3 == cls]
        v = [p * (1 - np.sqrt(d2_closed(p)) / p ** 2) for p in ps]
        ax.scatter(ps, v, s=7, marker='o', lw=0.5, facecolors=(ACC if cls == 2 else 'none'), edgecolors=ACC, zorder=4)
        lims[('C', cls)] = v[-1]
    for y, s in ((1 / 3, r'$\frac{1}{3}$'), (2 / 3, r'$\frac{2}{3}$'), (4 / 3, r'$\frac{4}{3}$'), (2, r'$2$')):
        ax.axhline(y, color=GRID, lw=0.5, zorder=1)

    check('drift', abs(lims[('C', 2)] - 1 / 3) < 0.02 and abs(lims[('C', 1)] - 2 / 3) < 0.02 and
          abs(lims[('J', 1)] - 2 / 3) < 0.02 and abs(lims[('J', 2)] - 4 / 3) < 0.02 and
          abs(lims[('E', 1)] - 4 / 3) < 0.02 and abs(lims[('E', 2)] - 2) < 0.03,
          'p(1-c) at the largest computed primes: C 1/3, 2/3; J 2/3, 4/3; E 4/3, 2 (within 0.03)')
    ax.set_xlim(0, 200)
    ax.set_ylim(0, 2.25)
    ax.set_yticks([0, 1 / 3, 2 / 3, 1, 4 / 3, 2])
    ax.set_yticklabels(['$0$', r'$\frac{1}{3}$', r'$\frac{2}{3}$', '$1$', r'$\frac{4}{3}$', '$2$'])
    ax.set_xlabel(r'prime $p$', labelpad=0)
    ax.set_ylabel(r'$p\,(1-\delta N^{1/3})$', labelpad=1)
    for sp_ in ax.spines.values():
        sp_.set_color('#9a9a9a')
    hl = [Line2D([], [], ls='none', marker='o', ms=3, mfc=ACC, mec=ACC, label=r'$\mathcal{C}_p$ (Thm.)'),
          Line2D([], [], ls='none', marker='^', ms=3, mfc=INK, mec=INK, label=r'$\mathcal{J}_p$'),
          Line2D([], [], ls='none', marker='x', ms=3, mec=MID, mew=0.6, label=r'$\mathcal{E}_p$')]
    leg = ax.legend(handles=hl, loc='center right', fontsize=5.6, framealpha=0.95, borderpad=0.3, labelspacing=0.2,
                    handletextpad=0.2, ncol=3, columnspacing=0.8, bbox_to_anchor=(0.97, 0.46))
    leg.get_frame().set_linewidth(0.3)
    ax.text(0.95, 0.37, r'filled: $p\equiv2$, open: $p\equiv1\ (\mathrm{mod}\ 3)$', transform=ax.transAxes,
            fontsize=5.5, ha='right', color=JIT)
    panel_title(ax, r'(c) first-order deficit, $m=3$')
    save(fig, 'col_drift')
    res['lims'] = {f'{a}{b}': float(v) for (a, b), v in lims.items()}
    res['pmax'] = max(int(p) for p in C['E'])
    return res


# ================================================================== col_half5
def fig_half5():
    H = json.load(open(os.path.join(HERE, 'half5_exact.json')))
    mind = {int(p): v for p, v in H['mind'].items()}
    cur = {k: {int(p): v for p, v in d.items()} for k, d in H['curves'].items()}
    ex = sorted((p, v['c']) for p, v in mind.items())
    shown = [(p, c) for p, c in ex if p >= 15]
    check('half5', [p for p, c in ex if c > 1][0] == 37 and all(c < 1 for p, c in ex if p <= 31),
          'exact c(Q*_p) < 1 for p <= 31 and > 1 from p = 37 (half5_exact.json)')
    r2 = sorted((p, v['val']) for p, v in cur['r2'].items() if v.get('hyp', True))
    hkF = sorted((p, v['val']) for p, v in cur['hkF'].items())
    hkM = sorted((p, v['val']) for p, v in cur['hkM'].items())
    first = lambda L: min(p for p, v in L if v > 1 and all(vv > 1 for pp, vv in L if pp >= p))
    f2, fF, fM = first(r2), first(hkF), first(hkM)
    check('half5', (f2, fF, fM) == (37, 53, 89), f'the certificates exceed 1 from p = {f2} (LB_2 of Q*), {fF} '
                                                 f'(prop:Hk(1), F_0^*), {fM} (prop:Hk(1), M_5) on')
    for p, v in r2:
        if p in mind:
            check('half5', v <= mind[p]['c'] + 1e-12, f'LB_2({p}) = {v:.6f} <= exact {mind[p]["c"]:.6f}')
    fig = plt.figure(figsize=(WIDTH, 2.45))
    ax = fig.add_axes([0.075, 0.17, 0.905, 0.76])
    s5 = np.sqrt(5) / 2
    pp = np.linspace(20, 215, 300)
    for K, ls_ in ((17 / 2, (0, (1, 1.2))), (17 / 2 + 5, (0, (1, 1.2))), (35 / 2 + 5, (0, (1, 1.2)))):
        ax.plot(pp, s5 * (1 - 2 * K / (5 * pp)), color=MID, lw=0.55, ls=ls_, zorder=1)
    ax.axhline(1, color=JIT, lw=0.5, ls=(0, (4, 2)))
    ax.axhline(s5, color=ACC, lw=0.5, ls=(0, (4, 2)))
    ax.text(210, s5 - 0.004, r'$\sqrt{5}/2$', color=ACC, fontsize=6.3, ha='right', va='top')
    ax.plot(*zip(*hkM), color=MID, lw=0.9, marker='.', ms=2.0)
    ax.plot(*zip(*hkF), color=INK, lw=0.9, marker='.', ms=2.0)
    ax.plot(*zip(*r2), color=ACC, lw=1.0, marker='.', ms=2.0)
    check('half5', all(c > 0.86 for _, c in shown), 'all exact values with p >= 17 lie inside the drawn range')
    ax.scatter([p for p, _ in shown], [c for _, c in shown], s=16, facecolors='white', edgecolors=ACC, lw=0.8, zorder=5)
    for p_, lab in ((37, '37'), (53, '53'), (89, '89')):
        ax.annotate(lab, xy=(p_, 1), xytext=(p_, 0.885), fontsize=6.3, ha='center', color=ACC,
                    arrowprops=dict(arrowstyle='-', color=ACC, lw=0.4, shrinkA=1, shrinkB=0))
    ax.set_xlim(14, 216)
    ax.set_ylim(0.86, 1.13)
    ax.set_xlabel(r'prime $p$', labelpad=0)
    ax.set_ylabel(r'$\delta N^{1/5}$, $N=p^5$', labelpad=1)
    for sp_ in ax.spines.values():
        sp_.set_color('#9a9a9a')
    hl = [Line2D([], [], ls='none', marker='o', ms=3.5, mfc='white', mec=ACC, mew=0.8, label=r'$\mathcal{Q}^*_p$, exact'),
          Line2D([], [], color=ACC, lw=1.0, label=r'$\mathrm{LB}_2$ of $\mathcal{Q}^*_p$ (Lemma R2)'),
          Line2D([], [], color=INK, lw=0.9, label=r'$\mathrm{LB}$ of $F_0^*$ (Prop. Hk(1))'),
          Line2D([], [], color=MID, lw=0.9, label=r'$\mathrm{LB}$ of $M_5$ (Prop. Hk(1))'),
          Line2D([], [], color=MID, lw=0.55, ls=(0, (1, 1.2)),
                 label=r'$\frac{\sqrt{5}}{2}(1-\frac{2K}{5p})$, $K=\frac{17}{2},\ \frac{17}{2}+5,\ \frac{35}{2}+5$')]
    leg = ax.legend(handles=hl, loc='lower right', bbox_to_anchor=(0.995, 0.02), fontsize=6.2, framealpha=0.95,
                    labelspacing=0.35, borderpad=0.4)
    leg.get_frame().set_linewidth(0.3)
    save(fig, 'col_half5')
    return dict(first=(f2, fF, fM), exmin=shown[0][0], exmax=shown[-1][0], c31=mind[31]['c'], c37=mind[37]['c'],
                pmax=max(p for p, _ in r2))


def write_captions(R):
    N, D, Hh = R['net'], R['drift'], R['half5']
    caps = {}
    caps['colNetCaption'] = (
        r"Column nets (Definition~\ref{def:col}), in cell units. (a) The $%d$ points of $\mathcal C_{%d}$ on the torus "
        r"$[0,%d)^3$. Each lies on the body diagonal of its cell, and the points of one column lie on a closed line "
        r"parallel to $(1,1,1)$ (grey; the $%d$ columns wrap around the torus). Shade: the height "
        r"$\varphi(n)=q\,r(n)+j(n)$. Accent: a closest pair; every closest pair differs by $\pm D$, $D=(%d,%d,%d)$ at "
        r"integer scale $q^3$, $|D|^2=%d$, $\delta N^{1/3}=%.4f\ldots$ (Theorem~\ref{thm:col}; checked against all "
        r"pairs). (b) $\mathcal C_{%d}$ viewed along $(1,1,1)$, one period: every column projects to one site of the "
        r"triangular lattice $P\mathbb{Z}^3$ (a hexagon each). The points of a column are $\sqrt3$ apart, and their "
        r"common height modulo $\sqrt3$ is, in turns, $\frac23\Sigma n$ for the reflected cube $H\mathbb{Z}^3$ plus "
        r"the deviation shown, $\frac{w\cdot n}{3q}+\frac{j(n)}{q^2}$ for the cell $n=(x,y,0)$ of the column, a linear ramp (the drift) with a small ripple "
        r"(the jitter of the third digit; checked for every column). Across one period the ramp gains $\frac13w_c$ of "
        r"a turn along $e_c$, which is not an integer, since $3\nmid q$: an ideal reflected cube cannot close up on "
        r"the torus, and the drift spreads the mismatch (Section~\ref{sec:drift}). Black: a closest pair of "
        r"$\mathcal C_{%d}$, $|D|^2=%d$, between neighbouring columns."
        % (N['npts'], N['q'], N['q'], N['ncol'], *N['D'], N['d2'], np.floor(N['c'] * 1e4) / 1e4, N['qb'], N['qb'],
           N['d2b']))
    a11, a13 = D[11], D[13]
    caps['colDriftCaption'] = (
        r"Drift and jitter. (a), (b) The holonomy: along the three cycles of $q$ steps through the column of the "
        r"cell $0$, the heights $\varphi$ (each step value taken near $\frac13q^2$) minus the ideal $\frac13q^2$ per "
        r"step of the reflected cube, in units of $q^2$. After $q$ steps the ideal heights would end at $\frac q3$, not "
        r"an integer, but the heights must return modulo $q^2$: the heights of the cycles of $\mathcal C_{11}$ end at "
        r"$%d$, $%d$, $%d$ (times $q^2$) and those of $\mathcal C_{13}$ at $%d$, $%d$, $%d$, so the excess sums to the forced leftover $\frac13w_c$ "
        r"(accent arrows). Thin dotted: the drift, $\frac13w_c$ spread evenly over the cycle; the jitter adds the "
        r"residue $\bar b_c$ of the third digit on the steps where it does not wrap and subtracts $q-\bar b_c$ where it does "
        r"(Lemma~\ref{lem:drift}). The first-order deficit is $\eta/q$, with $\eta$ the largest step excess, "
        r"$\frac q3+1$ resp.\ $\frac23q$. (c) The first-order deficit $p(1-\delta N^{1/3})$ at the primes "
        r"$5\le p\le%d$: the column nets $\mathcal{C}_p$ (exact, Theorem~\ref{thm:col}) tend to $\frac13$ "
        r"($p\equiv2$) and $\frac23$ ($p\equiv1\pmod3$). For comparison two nets that share the second digit "
        r"$\lfloor p/3\rfloor\Sigma n$ in all coordinates, so that their drift vector is fixed at $w=-\gamma\mathbf 1$, $\gamma\in\{1,2\}$ "
        r"(computed exact values): $\mathcal{J}_p$ with the third digit $\frac12(-n_c-n_{c+1}+n_{c+2})$ tends to "
        r"$\frac23$ and $\frac43$, and $\mathcal{E}_p$ with the third digit $n_{c+1}$ to $\frac43$ and $2$."
        % (*a11['ends'], *a13['ends'], D['pmax']))
    caps['colHalfCaption'] = (
        r"Dimension five, one resolution, $N=p^5$: the layer $F_0^*$ of Proposition~\ref{prop:half5} against the "
        r"dominant layer $M_5$ of Remark~\ref{rem:M5}. Open circles: the exact $\delta N^{1/5}$ of $\mathcal{Q}^*_p$ at "
        r"the primes $%d\le p\le%d$ (computed); it exceeds $1$ from $p=37$ on ($%s$ at $p=31$, $%s$ at $p=37$). "
        r"Lines: the proved lower bounds, computed exactly at every prime: Lemma~\ref{lem:R2} for $\mathcal{Q}^*_p$ (from $p=29$, where "
        r"its hypotheses hold), which exceeds $1$ from $p=%d$ on, and Proposition~\ref{prop:Hk}(1), which charges a "
        r"jitter of $1$ to every coordinate, for every graph form with the first offset rows $F_0^*$ (from $p=%d$ on) "
        r"and $M_5$ (from $p=%d$ on). Dotted: the first-order lines $\frac{\sqrt5}2(1-\frac{2K}{5p})$ with "
        r"$K=\mathrm{dr}=\frac{17}2$ (lean second row, Remark~\ref{rem:accounting}), $K=\frac{17}2+5$ and "
        r"$K=\frac{35}2+5$: the drift of the layer and the jitter decide the base."
        % (Hh['exmin'], Hh['exmax'], ffloor(Hh['c31'], 4), ffloor(Hh['c37'], 4), *Hh['first']))   # rev 15.2: truncated, not rounded
    with open(os.path.join(OUT, 'col_captions.tex'), 'w') as f:
        f.write('% col_captions.tex -- GENERATED by figs_col.py (do not edit by hand; rerun the script).\n'
                '% Caption macros for figs/col_{net,drift,half5}.pdf; every number is asserted by the script.\n')
        for k_, v_ in caps.items():
            f.write('\\newcommand{\\%s}{%%\n%s}\n' % (k_, v_))


if __name__ == '__main__':
    t0 = time.time()
    R = {}
    for nm, fn in (('net', fig_net), ('drift', fig_drift), ('half5', fig_half5)):
        t = time.time()
        R[nm] = fn()
        print(f'{nm:6s} {time.time() - t:5.1f}s  {R[nm]}')
    write_captions(R)
    for fg, what in CHECKS:
        print(f'  [ok] {fg:6s} {what}')
    print(f'total {time.time() - t0:.1f}s; {len(CHECKS)} checks passed')

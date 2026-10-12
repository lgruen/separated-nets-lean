#!/usr/bin/env python3
"""figs_wnet.py -- rev 15.1: Figure fig:wnet (figs/w_net.pdf) and its caption macro (figs/w_captions.tex).

Locked against free phases at m = 3 (Section sec:wnet), drawn from points generated from the generator matrices:
  (a) T_101 (prop:twocoset), a side view with the free coordinate x vertical: the layer step along e_x is exactly 1
      (no drift), the shared pair y = z shears by about 1/8 per layer;
  (b) W_101 (prop:wnet), a side view with the locked coordinate z vertical: the layer step along e_z is 1 + 2 eps
      (drift), and where z wraps, x (and y) wrap too, so the step stays long;
  (c) the same net with the second digit of z shifted by 1 (a digital shift, rem:shiftshared): now z wraps alone at
      some cells, and the step along e_z folds to (4 eps, 4 eps, 2 eps) up to the third digits;
  (d) delta N^{1/3} of W_p (exact, w_exact.json, written by wnet.py), the bound of prop:wnet(2), the pair of (3),
      against T_p (exact, colnets_exact.json) and the limits sqrt(281)/16, sqrt(66)/8, 1; rev 15.3: the family optimum
      mu* = sqrt((72 - 8 sqrt31)/25) of prop:wfamily (dotted).
Every property stated in the caption is asserted here.

    uv run --with numpy --with matplotlib python scripts/figs_wnet.py [--out DIR]      (~2 s; needs bin/shiftmin)
"""
import os
import sys
import json
import math
import subprocess
import time
import numpy as np
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Rectangle
from matplotlib.collections import LineCollection
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
MID = '#9a9a9a'
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


def isprime(n):
    return n > 1 and all(n % k for k in range(2, math.isqrt(n) + 1))


def W(p):
    h, r = (p - 1) // 2, p // 48
    rho = 2 * r + 1
    return [[-rho, -rho, 2 * rho], [-rho, -rho, 2 * rho], [h - r, h - r, rho]], [[0, 1, 2], [1, 0, 1], [0, 1, 0]]


def T(p):
    h, r = (p - 1) // 2, round(p / 8)
    return [[0, h, h], [r, -1, 1], [r, -1, 1]], [[0, 1, 2], [3, 0, 1], [1, 5, 0]]


def points(B, R, p, cells, g2=(0, 0, 0)):
    """cell units: n + (g + f/p)/p, g = (B n + g2) mod p, f = R n mod p"""
    cells = np.asarray(cells, dtype=np.int64)
    Bm, Rm = np.array(B, dtype=np.int64), np.array(R, dtype=np.int64)
    g = (cells @ Bm.T + np.array(g2)) % p
    f = (cells @ Rm.T) % p
    return cells + (g + f / p) / p, g


def tor_dist(a, b, P):
    d = np.abs(a - b) % P
    return np.sqrt((np.minimum(d, P - d) ** 2).sum(-1))


def ftr(x, d=3):
    """rev 15.2: exact and computed values are printed truncated (not rounded) to d decimals (Section sec:conv)"""
    v = math.floor(round(float(x) * 10 ** d, 9))
    return f'%.{d}f' % (v / 10 ** d)


def shiftmin(B, R, p, g2):
    inp = f'{p}\n' + '\n'.join(' '.join(str(x % p) for x in row) for row in B + R) + '\n' + \
        ' '.join(str(x) for x in list(g2) + [0, 0, 0]) + '\n'
    out = subprocess.run([os.path.join(HERE, 'bin', 'shiftmin')], input=inp, capture_output=True, text=True,
                         check=True).stdout.split()
    return int(out[0])


def column_lines(ax, P, cells, axis, lw=0.45):
    """thin grey segments between the points of consecutive cells along `axis` (the layer steps)"""
    idx = {tuple(c): i for i, c in enumerate(cells)}
    segs = []
    for i, c in enumerate(cells):
        nxt = tuple(c + np.eye(3, dtype=int)[axis])
        if nxt in idx:
            segs.append([P[i], P[idx[nxt]]])
    ax.add_collection(LineCollection(segs, colors=MID, linewidths=lw, zorder=2))


def grid(ax, x0, x1, y0, y1):
    segs = [[(x, y0), (x, y1)] for x in range(x0, x1 + 1)] + [[(x0, y), (x1, y)] for y in range(y0, y1 + 1)]
    ax.add_collection(LineCollection(segs, colors=GRID, linewidths=0.35, zorder=0))


def arrow(ax, o, v, col=ACC, lw=1.0, ms=5, z=6):
    ax.annotate('', xy=(o[0] + v[0], o[1] + v[1]), xytext=(o[0], o[1]),
                arrowprops=dict(arrowstyle='-|>', color=col, lw=lw, mutation_scale=ms, shrinkA=0, shrinkB=0), zorder=z)


def label(ax, x, y, s, col=ACC, fs=5.8, ha='center', va='center'):
    ax.text(x, y, s, color=col, fontsize=fs, ha=ha, va=va, zorder=7, bbox=dict(fc='white', ec='none', pad=0.4,
                                                                              alpha=0.9))


def clean(ax, x0, x1, y0, y1):
    ax.set_aspect('equal')
    ax.set_xlim(x0, x1); ax.set_ylim(y0, y1)
    ax.set_xticks([]); ax.set_yticks([])
    for sp in ax.spines.values():
        sp.set_color(MID)


def fig_wnet():
    p = 101
    h, r = (p - 1) // 2, p // 48
    rho = 2 * r + 1
    eps = rho / (2 * p)
    BW, RW = W(p)
    BT, RT = T(p)
    NX, NZ = 5, 6                                   # window: 5 columns, 6 layers
    # ---------------------------------------------------------------- (a) T_101: x vertical, (y, x) plane, n_z fixed
    nz0, y0, x0 = 40, 30, 50
    cellsA = np.array([[x0 + i, y0 + j, nz0] for i in range(NZ) for j in range(NX)])
    PA, gA = points(BT, RT, p, cellsA)
    # along e_x the free coordinate x moves by exactly one cell, up to the jitter (A_xx = 0: no drift)
    stepsx = [(PA[k][0] - PA[i][0]) for i, c in enumerate(cellsA) for k, d in enumerate(cellsA)
              if (d == c + np.array([1, 0, 0])).all()]
    check('wnet', len(stepsx) == (NZ - 1) * NX and max(abs(s - 1) for s in stepsx) < 1 / p,
          f'(a) T_{p}: every layer step along e_x moves x by 1 +- jitter (< 1/p); max deviation '
          f'{max(abs(s - 1) for s in stepsx):.4f}')
    check('wnet', np.all(gA[:, 1] == gA[:, 2]), '(a) y and z read the same digit (they wrap together)')
    # ---------------------------------------------------------------- (b) W_101: z vertical, (x, z) plane, n_y fixed
    zeta = lambda c: (BW[2][0] * c[0] + BW[2][1] * c[1] + BW[2][2] * c[2]) % p
    # pick a window with a wrap of z (and one of x alone) inside, and a z-wrap step whose source point is in the window
    best = None
    for ny in range(0, p, 7):
        for xs in range(0, p - NX, 5):
            for zs in range(0, p - NZ, 3):
                cl = [(xs + i, ny, zs + j) for i in range(NX) for j in range(NZ)]
                zw = [c for c in cl if c[2] < zs + NZ - 1 and zeta(c) + rho >= p]          # z wraps on e_z
                xw = [c for c in cl if c[2] < zs + NZ - 1 and zeta(c) + rho < p and 2 * zeta(c) < p <= 2 * (zeta(c) + rho)]
                if zw and xw and 1 <= zw[0][0] - xs <= NX - 2 and 1 <= zw[0][2] - zs <= NZ - 3:
                    best = (ny, xs, zs, zw[0], xw)
                    break
            if best:
                break
        if best:
            break
    check('wnet', best is not None, '(b) window with a locked wrap of z found')
    ny, xs, zs, cw, xw = best
    cellsB = np.array([[xs + i, ny, zs + j] for i in range(NX) for j in range(NZ)])
    PB, gB = points(BW, RW, p, cellsB)
    check('wnet', np.all(gB[:, 0] == gB[:, 1]) and np.all(gB[:, 0] == (2 * gB[:, 2]) % p),
          '(b) x and y read twice the digit of z (rank-one layer (2,2,1)u^T)')
    idx = {tuple(c): i for i, c in enumerate(cellsB)}
    ordinary, wraps = [], []
    for i, c in enumerate(cellsB):
        j = idx.get((c[0], c[1], c[2] + 1))
        if j is None:
            continue
        P0, P1 = points(BW, RW, p, [c, c + np.array([0, 0, 1])])[0]
        d = P1 - P0
        z_wraps = zeta(c) + rho >= p
        if z_wraps:
            wraps.append((i, d))
            check('wnet', abs(d[2] - 2 * eps) < 1 / p and abs(d[0] - (-1 + 4 * eps)) < 1 / p and abs(d[1] - d[0]) < 1 / p,
                  f'(b) at the wrap of z in cell {tuple(c)} the step is (-1+4eps, -1+4eps, 2eps) +- jitter (x, y wrap too)')
        elif 2 * zeta(c) < p <= 2 * (zeta(c) + rho):
            check('wnet', abs(d[2] - (1 + 2 * eps)) < 1 / p and abs(d[0] - (-1 + 4 * eps)) < 1 / p,
                  f'(b) x, y wrap alone in cell {tuple(c)}: step (-1+4eps, -1+4eps, 1+2eps)')
        else:
            ordinary.append((i, d))
            check('wnet', abs(d[2] - (1 + 2 * eps)) < 1 / p and abs(d[0] - 4 * eps) < 1 / p,
                  f'(b) no wrap in cell {tuple(c)}: step (4eps, 4eps, 1+2eps) +- jitter')
    check('wnet', len(wraps) >= 1, '(b) a locked wrap of z inside the window')
    cW = math.sqrt(json.load(open(os.path.join(HERE, 'w_exact.json')))['W'][str(p)]) / p ** 2
    # ---------------------------------------------------------------- (c) the second digit of z shifted by 1
    g2 = (0, 0, 1)
    # z wraps alone on e_z iff zeta + 1 + rho >= p while 2 zeta + 2 rho < 2p, i.e. zeta = p - 1 - rho
    best = None
    for ny_ in range(0, p, 3):
        for xs_ in range(0, p - NX):
            for zs_ in range(0, p - NZ):
                c0 = [cc for cc in [(xs_ + 1, ny_, zs_ + 2)] if zeta(cc) == p - 1 - rho]
                if c0:
                    best = (ny_, xs_, zs_, c0[0])
                    break
            if best:
                break
        if best:
            break
    check('wnet', best is not None, '(c) a cell where z wraps alone')
    nyc, xsc, zsc, c0 = best
    cellsC = np.array([[xsc + i, nyc, zsc + j] for i in range(NX) for j in range(NZ)])
    PC, gC = points(BW, RW, p, cellsC, g2)
    Pf = points(BW, RW, p, [c0, (c0[0], c0[1], c0[2] + 1)], g2)[0]
    vf = Pf[1] - Pf[0]
    lone = []
    for c in cellsC:
        if c[2] == zsc + NZ - 1:
            continue
        z_, z2 = (zeta(c) + 1) % p, (zeta(c) + 1 + rho) % p
        if (z2 < z_) and ((2 * zeta(c)) % p + 2 * rho < p):
            lone.append(tuple(int(x) for x in c))
    check('wnet', abs(vf[0] - 4 * eps) < 1.5 / p and abs(vf[1] - 4 * eps) < 1.5 / p and abs(vf[2] - 2 * eps) < 1.5 / p,
          f'(c) the step along e_z at the lone wrap of z is ({vf[0]:.4f},{vf[1]:.4f},{vf[2]:.4f}) ~ (4eps,4eps,2eps)')
    check('wnet', tuple(c0) in lone and all(zeta(c) == p - 1 - rho for c in lone),
          f'(c) z wraps alone exactly at the cells with zeta = p-1-rho ({len(lone)} in the window)')
    for c in lone:
        Pl = points(BW, RW, p, [c, (c[0], c[1], c[2] + 1)], g2)[0]
        check('wnet', np.linalg.norm(Pl[1] - Pl[0]) < 0.2, f'(c) fold at {c}: length {np.linalg.norm(Pl[1] - Pl[0]):.4f}')
    lf = float(np.linalg.norm(vf))
    d2S = shiftmin(BW, RW, p, g2)
    cS = math.sqrt(d2S) / p ** 2
    cS_tr = '.%04d' % math.isqrt(d2S * 10 ** 8 // p ** 4)        # floor(10^4 cS), exactly (rev 15.2: truncated)
    check('wnet', cS < 1 and cS_tr == '.1355' and cS < lf + 1e-12,
          f'(c) shifted net: exact delta N^(1/3) = {cS:.6f}, truncated {cS_tr} (printed .1355), drawn fold {lf:.4f}')
    # ---------------------------------------------------------------- (d) delta N^{1/3} against p
    ex = sorted((int(k), math.sqrt(v) / int(k) ** 2) for k, v in json.load(open(os.path.join(HERE, 'w_exact.json')))['W'].items())
    colx = json.load(open(os.path.join(HERE, 'colnets_exact.json')))
    exT = sorted((int(k), v['c']) for k, v in colx['T'].items() if int(k) >= 17)
    LB = lambda q: np.sqrt(281 / 256 - 345 / (128 * q)) - np.sqrt(3) / q

    def dstar(q):
        q = np.asarray(q, dtype=np.int64)
        rr, hh = q // 48, (q - 1) // 2
        return np.sqrt((q * q - (6 * rr + 2) * q - 2) ** 2.0 + ((6 * rr + 3) * q) ** 2.0 + ((hh + 3 * rr + 2) * q) ** 2.0) / q ** 2
    for q_, c_ in ex:
        if q_ >= 53:
            check('wnet', LB(q_) <= c_ < dstar(q_), f'p={q_}: bound {LB(q_):.4f} <= exact {c_:.6f} < pair')
    check('wnet', all(c_ > 1 for q_, c_ in ex if q_ >= 17) and all(c_ < 1 for q_, c_ in ex if q_ <= 13),
          'exact: > 1 exactly from p = 17')
    dT = dict(exT)
    check('wnet', all(c_ > dT[q_] for q_, c_ in ex if q_ in dT), 'exact: W_p ahead of T_p at every computed prime')

    fig = plt.figure(figsize=(WIDTH, 2.45))
    axw, axh, yb = 0.215, 0.74, 0.10
    # (a)
    ax = fig.add_axes([0.005, yb, axw, axh])
    for i, j in [(i, j) for i in range(NZ) for j in range(NX)]:
        if gA[i * NX + j, 0] * 2 >= p:                      # x raised by about 1/2 (the parity glue)
            ax.add_patch(Rectangle((y0 + j, x0 + i), 1, 1, fc='#ececec', ec='none', zorder=0))
    grid(ax, y0, y0 + NX, x0, x0 + NZ)
    PA2 = PA[:, [1, 0]]
    column_lines(ax, PA2, cellsA, 0)
    ax.scatter(PA2[:, 0], PA2[:, 1], s=6, c=INK, lw=0, zorder=5)
    for i_, j_ in [(i_, j_) for i_ in (2, 3, 1, 4) for j_ in (2, 1, 3)]:
        ia = int(np.where((cellsA == [x0 + i_, y0 + j_, nz0]).all(1))[0][0])
        ib = int(np.where((cellsA == [x0 + i_ + 1, y0 + j_, nz0]).all(1))[0][0])
        if 0 < PA2[ib][0] - PA2[ia][0] < 0.25:
            break
    check('wnet', 0 < PA2[ib][0] - PA2[ia][0] < 0.25, '(a) drawn step: shear about 1/8 in y, 1 in x')
    arrow(ax, PA2[ia], PA2[ib] - PA2[ia])
    label(ax, PA2[ia][0] + 0.32, PA2[ia][1] + 0.5, '$1$', fs=6.2)
    clean(ax, y0, y0 + NX, x0, x0 + NZ)
    panel_title(ax, r'(a) $\mathcal{T}_{101}$: $x$ free')
    ax.text(0.5, -0.025, r'$(y,x)$; step $1$ along $x$', transform=ax.transAxes, fontsize=5.8, ha='center', va='top')
    # (b)
    ax = fig.add_axes([0.005 + axw + 0.012, yb, axw, axh])
    grid(ax, xs, xs + NX, zs, zs + NZ)
    PB2 = PB[:, [0, 2]]
    column_lines(ax, PB2, cellsB, 2)
    ax.scatter(PB2[:, 0], PB2[:, 1], s=6, c=INK, lw=0, zorder=5)
    io = [i for i, d in ordinary if cellsB[i][0] - xs in (1, 2, 3) and cellsB[i][2] - zs in (0, 1, 2, 3) and abs(cellsB[i][0] - cellsB[wraps[0][0]][0]) + abs(cellsB[i][2] - cellsB[wraps[0][0]][2]) >= 2][0]
    jo = idx[(cellsB[io][0], ny, cellsB[io][2] + 1)]
    arrow(ax, PB2[io], PB2[jo] - PB2[io])
    label(ax, PB2[io][0] + 0.5, PB2[io][1] + 0.5, r'$1{+}2\varepsilon$', fs=5.8)
    iw, dw = wraps[0]
    jw = idx[(cellsB[iw][0], ny, cellsB[iw][2] + 1)]
    arrow(ax, PB2[iw], PB2[jw] - PB2[iw], lw=1.3)
    label(ax, (PB2[iw][0] + PB2[jw][0]) / 2, PB2[jw][1] + 0.32, 'locked wrap', fs=5.4)
    clean(ax, xs, xs + NX, zs, zs + NZ)
    panel_title(ax, r'(b) $\mathcal{W}_{101}$: $z$ locked')
    ax.text(0.5, -0.025, r'$(x,z)$; at a wrap of $z$, $x,y$ wrap', transform=ax.transAxes, fontsize=5.8, ha='center',
            va='top')
    # (c)
    ax = fig.add_axes([0.005 + 2 * (axw + 0.012), yb, axw, axh])
    grid(ax, xsc, xsc + NX, zsc, zsc + NZ)
    PC2 = PC[:, [0, 2]]
    column_lines(ax, PC2, cellsC, 2)
    ax.scatter(PC2[:, 0], PC2[:, 1], s=6, c=INK, lw=0, zorder=5)
    for c in lone:
        Pl = points(BW, RW, p, [c, (c[0], c[1], c[2] + 1)], g2)[0]
        ax.add_patch(plt.Circle((Pl[0][0], (Pl[0][2] + Pl[1][2]) / 2), 0.28, fc='none', ec=ACC, lw=0.9, zorder=6))
    label(ax, Pf[0][0] + 0.55, Pf[0][2] - 0.62, r'short step $(4\varepsilon,4\varepsilon,2\varepsilon)$', fs=5.4)
    clean(ax, xsc, xsc + NX, zsc, zsc + NZ)
    panel_title(ax, r'(c) $z$ free (shifted)')
    ax.text(0.5, -0.025, r'$(x,z)$; $z$ wraps alone', transform=ax.transAxes, fontsize=5.8, ha='center', va='top')
    # (d)
    ax = fig.add_axes([0.735, 0.17, 0.255, 0.69])
    qq = np.array([q for q in range(53, 30001) if isprime(q)])
    qq = qq[np.unique(np.round(np.log(qq) * 80), return_index=True)[1]]
    ax.axhline(math.sqrt(281) / 16, color=ACC, lw=0.6, ls=(0, (3, 1.5)))
    MUS = math.sqrt((72 - 8 * math.sqrt(31)) / 25)          # rev 15.3: the family optimum mu* (prop:wfamily)
    ax.axhline(MUS, color=INK, lw=0.45, ls=(0, (1, 1.2)))
    ax.axhline(math.sqrt(66) / 8, color=MID, lw=0.6, ls=(0, (3, 1.5)))
    ax.axhline(1.0, color='#7a7a7a', lw=0.5, ls=(0, (1, 1.5)))
    exq = [a for a, _ in ex if a >= 53]
    ax.scatter(exq, dstar(exq), s=7, marker='x', c=MID, linewidths=0.5, zorder=3)
    ax.plot(qq, LB(qq), color=ACC, lw=0.9)
    ax.scatter([a for a, _ in exT], [b for _, b in exT], s=7, facecolors='none', edgecolors=INK, linewidths=0.45,
               zorder=4)
    ax.scatter([a for a, _ in ex if a >= 11], [b for a, b in ex if a >= 11], s=9, c=ACC, lw=0, zorder=5)
    ax.set_xscale('log')
    ax.set_xlim(10, 2e4)
    ax.set_ylim(0.955, 1.072)
    ax.tick_params(length=1.5, pad=1)
    for sp_ in ax.spines.values():
        sp_.set_color(MID)
    ax.set_xlabel('$p$', labelpad=0)
    ax.text(4e3, math.sqrt(281) / 16 - 0.0012, r'$\sqrt{281}/16$', color=ACC, fontsize=5.8, ha='center', va='top')
    ax.text(4e3, MUS + 0.0012, r'$\mu^*$', color=INK, fontsize=5.8, ha='center', va='bottom')
    check('wnet', MUS > math.sqrt(281) / 16 and math.floor((MUS - math.sqrt(281) / 16) * 1e5) == 31,
          '(d) mu* line 3.1e-4 above sqrt281/16 (caption value truncated)')
    ax.text(4e3, math.sqrt(66) / 8 + 0.0015, r'$\sqrt{66}/8$', color=MID, fontsize=5.8, ha='center', va='bottom')
    hl = [Line2D([], [], ls='none', marker='o', ms=2.8, mfc=ACC, mec='none', label=r'$\mathcal{W}_p$ exact'),
          Line2D([], [], color=ACC, lw=0.9, label=r'bound (2)'),
          Line2D([], [], ls='none', marker='x', ms=2.6, mec=MID, mew=0.5, label=r'pair $d_*/p^2$ of (3)'),
          Line2D([], [], ls='none', marker='o', ms=2.6, mfc='none', mec=INK, mew=0.45, label=r'$\mathcal{T}_p$ exact')]
    leg = ax.legend(handles=hl, loc='lower right', fontsize=5.4, framealpha=0.95, borderpad=0.3, labelspacing=0.2,
                    handletextpad=0.3, handlelength=1.4)
    leg.get_frame().set_linewidth(0.3)
    panel_title(ax, r'(d) $\delta N^{1/3}$, $m=3$')
    save(fig, 'w_net')
    return dict(p=p, rho=rho, eps=eps, cW=cW, cS=cS, cS_tr=cS_tr, lf=lf, nlone=len(lone), nwrap=len(wraps), pmax=max(q for q, _ in ex),
                pTmax=max(q for q, _ in exT))


def write_captions(R):
    cap = (
        r"Locked and free wraps at $m=3$, from points generated by the generator matrices, in cell units. "
        r"Grey segments join the points of consecutive cells along the vertical axis. (a) $\mathcal T_{%d}$ "
        r"(Proposition~\ref{prop:twocoset}), a slab $n_z=\mathrm{const}$ seen in the $(y,x)$-plane, with the free "
        r"coordinate $x$ vertical (shaded: cells raised by about $\frac12$ in $x$): the step along $\e_x$ moves $x$ "
        r"by exactly one cell, up to the jitter, whatever the cell. (b) $\mathcal W_{%d}$ (Proposition~\ref{prop:wnet}, "
        r"$\varepsilon=\rho/(2p)=%d/%d$), a slab $n_y=\mathrm{const}$ in the $(x,z)$-plane, with the locked "
        r"coordinate $z$ vertical: the step along $\e_z$ is $(4\varepsilon,4\varepsilon,1+2\varepsilon)$, longer "
        r"than one cell (accent arrow); where $z$ wraps, $x$ and $y$ wrap too and the step becomes "
        r"$(-1+4\varepsilon,-1+4\varepsilon,2\varepsilon)$, still long (thick accent arrow; checked at every cell of "
        r"the window). (c) The same net after the digital shift that adds $1$ to the second digit of $z$: the wraps "
        r"of $z$ are no longer locked, $z$ now wraps alone at some cells (the cells with $\zeta=p-1-\rho$), and the step "
        r"along $\e_z$ there shrinks to $(4\varepsilon,4\varepsilon,2\varepsilon)$ up to the third digits (circles; length $%s$); the shifted net has "
        r"$\delta N^{1/3}=%s\ldots$, against $%s\ldots$ without the shift (computed, Remark~\ref{rem:wshift}). "
        r"(d) $\delta N^{1/3}$ of $\mathcal W_p$ (exact at the primes $11\le p\le%d$ and at $307$, $353$; above $1$ "
        r"exactly from $p=17$ on), the bound of Proposition~\ref{prop:wnet}(2) and the explicit pair of (3), which is "
        r"not a closest pair; open circles: $\mathcal T_p$ (exact, $17\le p\le%d$); dotted: the optimum $\mu^*$ of the "
        r"family (Proposition~\ref{prop:wfamily}), $3.1\cdot10^{-4}$ above $\sqrt{281}/16$."
        % (R['p'], R['p'], R['rho'], 2 * R['p'], ftr(R['lf'], 3), R['cS_tr'],
           f"{math.floor(R['cW'] * 1e4) / 1e4:.4f}", 199, R['pTmax']))
    with open(os.path.join(OUT, 'w_captions.tex'), 'w') as f:
        f.write('% w_captions.tex -- GENERATED by figs_wnet.py (do not edit by hand; rerun the script).\n'
                '% Caption macro for figs/w_net.pdf; every number is asserted by the script.\n')
        f.write('\\newcommand{\\wNetCaption}{%%\n%s}\n' % cap)


if __name__ == '__main__':
    t0 = time.time()
    R = fig_wnet()
    write_captions(R)
    for fg, what in CHECKS:
        print(f'  [ok] {fg:5s} {what}')
    print(f'total {time.time() - t0:.1f}s; {len(CHECKS)} checks passed; {R}')

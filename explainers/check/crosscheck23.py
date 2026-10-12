#!/usr/bin/env python3
"""crosscheck23.py -- check shifts.html (page 2) and beyond.html (page 3) against Python references built from the paper.

Runs explainers/netcore.js under node (check/run_core23.mjs) and compares what the two pages show:
  * digital shifts (def:dshift): every shifted net is rebuilt here by adding the shift digits to the reference points
    digit by digit (no carries); point sets equal, one point per cell, every elementary box holds one point;
    exact toroidal minimum distances by the independent numpy neighbour-cell kernel of crosscheck.py;
  * lem:shift / prop:shift: at the closest pair's cells, the digit differences of the unshifted and the shifted net
    have the same residue mod q and take one of its two representatives; the shifted P_{2,q} keep c(q) of thm:main;
  * prop:colshift: shifted column nets C_q (q <= 43, coprime to 6) against the audited kernel shiftmin.cpp (paper
    scripts; the shift enters as the constants gamma of lem:shift) and numpy; part (1) exact value, (2), (3) bounds;
  * rem:wshift: W_p under shifts of the second digits, full (t, t') grids at p = 11, 13 and the paper's shifts at
    p = 53, 101 (shiftmin.cpp); the bound of prop:wnet(2) for every shift with t = 2t' or 2t'+1 at p = 53;
  * prop:twocoset, prop:wnet: T_p, W_p at every prime 5..101: generator rows typed from the paper, points (p <= 41),
    t = 0 (net_tparam for p <= 41; T_23 is not a net), exact d^2 against the audited data of the paper
    (colnets_exact.json, w_exact.json) and numpy (p <= 29), the bounds (2) and the explicit pairs (3) recomputed from
    the points; the steps along the locked / free axis grouped by wrap pattern, recomputed here from the points;
  * cor:colceil, thm:colmin: the triangle of height steps and g of C_q, d^2 = (2q^4 + 9g^2)/3 = thm:col; g <= 1/3 on
    a grid of step pairs;
  * lem:shiftcert: mu_n by brute force over X; the every-shift minimum of P_{k,b} (b = 2, 3) by brute force over all
    shifts (P_{1,b}), by the lemma's formula here, attained at the page's shift, and below 25 random shifts;
  * prop:half5: Q*_p points (p = 7, 11) and generator matrices, t = 0 (net_tparam, p = 7), exact d^2 against
    half5_exact.json (audited) and numpy (p = 7, 11); LB_2(p) of lem:R2 against half5_qstar.lb_r2_sq at every prime
    29..199; the constants of prop:wfamily.

    uv run --with numpy --with matplotlib python explainers/check/crosscheck23.py      (~50 s)
"""
import itertools
import json
import math
import os
import subprocess
import sys
import tempfile
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import crosscheck as cc  # noqa: E402  (shared numpy kernels, references and paths)
from crosscheck import check, points, as_set, min_dist_np, box_counts_ok  # noqa: E402

SCRIPTS = cc.SCRIPTS
import figs_col  # noqa: E402
import netdefs  # noqa: E402
import half5_qstar as h5q  # noqa: E402
from net_tparam import t_value_matrices  # noqa: E402


def load(name):
    return json.load(open(os.path.join(SCRIPTS, name)))


def shift_points(P, tau, q, m):
    """def:dshift on integer coordinates: digit j (most significant first) of coordinate c plus tau[c][j], mod q."""
    P = np.asarray(P, dtype=np.int64)
    out = np.zeros_like(P)
    for c in range(P.shape[1]):
        for j in range(m):
            w = q ** (m - 1 - j)
            out[:, c] += ((P[:, c] // w + tau[c][j]) % q) * w
    return out


def tor(d, W):
    d = d % W
    return np.where(d > W // 2, d - W, d)


def build_shiftmin(td):
    exe = os.path.join(td, 'shiftmin')
    subprocess.run(['g++', '-O3', '-std=c++17', '-o', exe, os.path.join(SCRIPTS, 'shiftmin.cpp')], check=True)
    return exe


def shiftmin(exe, p, B, R, tau):
    """lem:shift: a shift tau of a graph form with depths (1,1,1) is the graph form with the constants
    gamma_2 = tau_2 - B tau_1, gamma_3 = tau_3 - R tau_1 (cells re-indexed by n + tau_1)."""
    t1 = [tau[c][0] for c in range(3)]
    g2 = [tau[c][1] - sum(B[c][d] * t1[d] for d in range(3)) for c in range(3)]
    g3 = [tau[c][2] - sum(R[c][d] * t1[d] for d in range(3)) for c in range(3)]
    inp = f'{p}\n' + '\n'.join(' '.join(str(x % p) for x in row) for row in list(B) + list(R)) + '\n' + \
        ' '.join(str(x % p) for x in g2 + g3) + '\n'
    return int(subprocess.run([exe], input=inp, capture_output=True, text=True, check=True).stdout.split()[0])


def graph_C(B, R):
    return [[[int(d == c) for d in range(3)], list(B[c]), list(R[c])] for c in range(3)]


def T_rows(p):     # prop:twocoset, typed from core.tex
    h, r = (p - 1) // 2, round(p / 8)
    return [[0, h, h], [r, -1, 1], [r, -1, 1]], [[0, 1, 2], [3, 0, 1], [1, 5, 0]]


def W_rows(p):     # prop:wnet, typed from core.tex
    h, r = (p - 1) // 2, p // 48
    rho = 2 * r + 1
    return [[-rho, -rho, 2 * rho], [-rho, -rho, 2 * rho], [h - r, h - r, rho]], [[0, 1, 2], [1, 0, 1], [0, 1, 0]]


def C_rows(q):     # def:col via figs_col
    a = [int(x) for x in (q + figs_col.col_w(q)) // 3]
    return [a, a, a], [[-1, 1, 0]] * 3


def ref_net(name, q):
    if name.startswith('H2'):
        k = int(name.split('-k')[1])
        return cc.hammersley_ref(k, 'rotated')
    if name.startswith('P'):
        return netdefs.P_mats(int(name.split('-k')[1]))['C']
    B, R = C_rows(q)
    return graph_C(B, R)


def mu_brute(d, b):
    n = len(d)
    Wn = b ** n
    best = None
    for X in range(Wn):
        Y = 0
        for j in range(n):
            w = b ** (n - 1 - j)
            Y += ((X // w + d[j]) % b) * w
        v = abs(int(tor(np.int64(Y - X), Wn)))
        best = v if best is None else min(best, v)
    return best


def min_dist_brute(P, W):
    D = P[:, None, :] - P[None, :, :]
    D = tor(D, W)
    d2 = (D * D).sum(-1)
    np.fill_diagonal(d2, 1 << 62)
    return int(d2.min())


def main():
    t0 = time.time()
    with tempfile.TemporaryDirectory() as td:
        procs, js = [], {}
        for part in ('a', 'b'):                                   # the two halves of the dump run in parallel
            outp = os.path.join(td, f'core23{part}.json')
            procs.append((outp, subprocess.Popen([cc.NODE, os.path.join(HERE, 'run_core23.mjs'),
                                                  os.path.join(cc.EXPL, 'netcore.js'), outp, part],
                                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)))
        for outp, pr in procs:
            so, se = pr.communicate(timeout=120)
            print(so.strip(), se.strip())
            assert pr.returncode == 0
            for key, v in json.load(open(outp)).items():
                if isinstance(v, list):
                    js.setdefault(key, []).extend(v)
                elif isinstance(v, dict):
                    js.setdefault(key, {}).update(v)
                else:
                    js[key] = v
        t_node = time.time() - t0
        exe = build_shiftmin(td)

        # ------------------------------------------------ the pages load the shared file
        for page in ('anatomy.html', 'shifts.html', 'beyond.html'):
            path = os.path.join(cc.EXPL, page)
            if os.path.exists(path):
                h = open(path).read()
                check('<script src="netcore.js"></script>' in h and 'id="netcore"' not in h,
                      f'{page}: loads netcore.js with a relative src, no inline copy')
                check(h.lstrip().startswith('<title>'), f'{page}: starts with <title>')

        # ------------------------------------------------ shifted nets (page 2, sections 1-3)
        for rec in js['shifted'] + js['col']:
            name, q, m, k, tau = rec['name'], rec['q'], rec['m'], rec['k'], rec['tau']
            C = ref_net(name, q)
            check([[[x % q for x in row] for row in Cc] for Cc in C] == rec['C'], f'{name}: generator matrices mod q')
            Pref = points(C, q)
            Ps = shift_points(Pref, tau, q, m)
            if 'X' in rec:
                check(as_set(Ps) == as_set(np.array(rec['X']).T), f'{name} + shift {tau}: point sets equal')
                okb, _ = box_counts_ok(Ps, q, m)
                check(okb and rec['box'], f'{name} + shift: every elementary box holds one point (python and page)')
            check(rec['onePerCell'], f'{name} + shift: one point per cell (page)')
            d2, cnt, ex, G = min_dist_np(Ps, q, m, k, True)
            check(ex and d2 == rec['d2'], f'{name} + shift {tau}: exact toroidal d^2 = {d2} (numpy)')
            if G >= 5:
                check(cnt == rec['count'], f'{name} + shift: {cnt} closest pairs')
            d2u, _, exu, _ = min_dist_np(Pref, q, m, k, True)
            check(exu and d2u == rec['d2un'], f'{name}: unshifted d^2 = {d2u}')
            st = rec['step']
            ok = all(a['residue'] == b['residue'] and a['value'] in a['options'] and b['value'] in b['options']
                     and (a['residue'] - a['value']) % q == 0 for a, b in zip(st['sh']['coords'], st['un']['coords']))
            # recompute the shifted step from the reference points
            cw = q ** (m - k)
            cells = Ps // cw
            ia = int(np.where((cells == st['n']).all(1))[0][0])
            ib = int(np.where((cells == np.array(st['sh']['n2'])).all(1))[0][0])
            dj = (Ps[ib] // q ** (m - k - 1)) % q - (Ps[ia] // q ** (m - k - 1)) % q
            ok = ok and list(map(int, dj)) == [a['value'] for a in st['sh']['coords']]
            check(ok, f'{name} + shift: lem:shift, same residues of digit {k + 1} differences at cells {st["n"]} -> +{st["E"]}')
            if name.startswith('P'):
                check(math.sqrt(d2) / q ** (m - k) >= math.sqrt(float(cc.tab_c.c_main(q))) - 1e-12,
                      f'{name} + shift: c = {math.sqrt(d2) / q ** (m - k):.4f} >= c(q) of thm:main (prop:shift)')
            if name.startswith('C'):
                B, R = C_rows(q)
                d2s = shiftmin(exe, q, B, R, tau)
                check(d2s == d2, f'{name} + shift {tau}: shiftmin.cpp d^2 = {d2s}')
                bd, c = rec['bounds'], math.sqrt(d2) / q ** 2
                W = 2 if q % 3 == 2 else 4
                wmax = max(figs_col.col_w(q))
                lb3 = (1 - (W + 3) / q + 3 / q ** 2) / math.sqrt(3)
                check(abs(bd['lbEvery'] - lb3) < 1e-12 and c >= lb3, f'{name} + shift: c = {c:.4f} >= (3) lower {lb3:.4f}')
                e2 = len({t[1] for t in tau}) == 1
                e3 = len({t[2] for t in tau}) == 1
                check(bd['part'] == (1 if e2 and e3 else 2 if e2 else 3), f'{name} + shift: case of prop:colshift')
                if e2 and e3:
                    check(d2 == figs_col.d2_closed(q), f'{name} + shift: (1) d^2 = thm:col value')
                elif e2:
                    lb2 = 1 - (7 * q - 3) / (math.sqrt(3) * q * q)
                    check(abs(bd['lbEq2'] - lb2) < 1e-12 and c >= lb2, f'{name} + shift: (2) c >= {lb2:.4f}')
                else:
                    ub = (1 + (3 + wmax) / q - 3 / q ** 2) / math.sqrt(3)
                    check(abs(bd['ub'] - ub) < 1e-12 and c <= ub, f'{name} + shift: (3) c <= {ub:.4f}')

        # wrap windows of the shifted column nets (rem:shiftshared): recomputed from the shifted reference points
        for rec in js['col']:
            if 'windows' not in rec:
                continue
            q, tau = rec['q'], rec['tau']
            B, R = C_rows(q)
            a = B[0]
            P = shift_points(points(graph_C(B, R), q), tau, q, 3)
            cells = P // q ** 2
            grid = np.empty((q, q, q, 3), dtype=np.int64)
            grid[cells[:, 0], cells[:, 1], cells[:, 2]] = P
            ok = True
            for c in range(3):
                win = rec['windows'][c]
                ok = ok and win['consistent']
                for n in itertools.product(range(q), repeat=3):
                    if n[c] == q - 1:
                        continue
                    n2 = list(n)
                    n2[c] += 1
                    th = sum(a[d] * (n[d] - tau[d][0]) for d in range(3)) % q
                    dv = (grid[tuple(n2)] // q) % q - (grid[n] // q) % q
                    w = [int(x < 0 and x % q > 0) for x in dv]
                    ok = ok and win['wraps'][th] == w
            e2 = len({t[1] for t in tau}) == 1
            if e2:      # equal second shift digits: the three coordinates wrap together on every step
                ok = ok and all(len(set(rec['windows'][c]['wraps'][th])) == 1 for c in range(3) for th in range(q))
            else:       # proof of prop:colshift(3): on some step a coordinate wraps alone along its own axis
                ok = ok and any(rec['windows'][c]['wraps'][th] == [int(d == c) for d in range(3)]
                                for c in range(3) for th in range(q))
            check(ok, f'C_{q} + shift {tau}: wrap windows by shared digit value, '
                      f'{"one window" if e2 else "a coordinate wraps alone somewhere"} (rem:shiftshared)')
        for e in js['explainShift']:
            q, m, X, t, ex = e['q'], e['m'], e['X'], e['t'], e['ex']
            xd = [X // q ** (m - 1 - j) % q for j in range(m)]
            T = sum(t[j] * q ** (m - 1 - j) for j in range(m))
            S = sum(((xd[j] + t[j]) % q) * q ** (m - 1 - j) for j in range(m))
            ok = ex['xd'] == xd and ex['td'] == list(t) and ex['S'] == S and ex['plain'] == (X + T) % q ** m
            ok = ok and ex['S'] == int(shift_points(np.array([[X]]), [t], q, m)[0, 0])
            carry, cs = 0, []
            for j in range(m - 1, -1, -1):
                v = xd[j] + t[j] + carry
                carry = int(v >= q)
                cs.insert(0, carry)
            ok = ok and ex['carries'] == cs and ex['plainDigits'] == [(X + T) % q ** m // q ** (m - 1 - j) % q for j in range(m)]
            if not ok:
                check(False, f'explainShift q={q} m={m} X={X} t={t}')
        check(True, f'explainShift: {len(js["explainShift"])} digitwise and ordinary sums')

        # ------------------------------------------------ W_p shifts (rem:wshift)
        for g in js['wheat']:
            p = g['p']
            B, R = W_rows(p)
            Pref = points(graph_C(B, R), p)
            bad = 0
            for e in g['grid']:
                tau = [[0, e['t'], 0], [0, e['t'], 0], [0, e['tz'], 0]]
                d2, _, ex, _ = min_dist_np(shift_points(Pref, tau, p, 3), p, 3, 1, True)
                if not (ex and d2 == e['d2'] == shiftmin(exe, p, B, R, tau)):
                    bad += 1
                if e['keeps'] != ((e['t'] - 2 * e['tz']) % p in (0, 1)):
                    bad += 1
            check(bad == 0, f'W_{p}: all {p * p} second-digit shifts (t,t,t\'): d^2 = numpy = shiftmin.cpp, lock rule')
            sm = g['summary']
            cs = [(math.sqrt(e['d2']) / p ** 2, (e['t'] - 2 * e['tz']) % p in (0, 1)) for e in g['grid']]
            want = dict(total=p * p, kept=sum(c > 0.5 for c, _ in cs), keptOff=sum(c > 0.5 and not on for c, on in cs),
                        onLines=2 * p, onMin=min(c for c, on in cs if on), offMax=max(c for c, on in cs if not on))
            check(all(abs(sm[k] - v) < 1e-12 for k, v in want.items()),
                  f'W_{p}: heat summary {sm["kept"]} of {p * p} shifts keep c > 0.5, {sm["keptOff"]} off the two lines')
        for e in js['wshift']:
            p, tau = e['p'], e['tau']
            B, R = W_rows(p)
            d2 = shiftmin(exe, p, B, R, tau)
            check(d2 == e['d2'], f'W_{p} + shift {tau}: d^2 = {d2} (shiftmin.cpp)')
            c = math.sqrt(d2) / p ** 2
            lb = math.sqrt(281 / 256 - 345 / (128 * p)) - math.sqrt(3) / p
            check(abs(e['bounds']['lb'] - lb) < 1e-12, f'W_{p}: bound of prop:wnet(2)')
            if e['keeps']:
                check(c >= lb, f'W_{p} + shift {tau}: t = 2t\' or 2t\'+1, c = {c:.4f} >= bound {lb:.4f}')
            if p == 101 and tau[0][2] == 0 and tau[2][2] == 0:
                want = {(7, 7, 7): '0.1355', (1, 1, 0): '1.0362'}[(tau[0][1], tau[1][1], tau[2][1])]
                check(f'{math.floor(c * 1e4) / 1e4:.4f}' == want, f'W_101 + shift {tau}: c = {want}... (rem:wshift)')

        # ------------------------------------------------ T_p, W_p (page 3)
        wex = load('w_exact.json')['W']
        tex = load('colnets_exact.json')['T']
        n_t = 0
        for rec in js['tw']:
            kind, p = rec['kind'], rec['p']
            B, R = T_rows(p) if kind == 'T' else W_rows(p)
            C = graph_C(B, R)
            check([[[x % p for x in row] for row in Cc] for Cc in C] == rec['C'], f'{kind}_{p}: generator rows of the paper')
            ref = (tex if kind == 'T' else wex).get(str(p))
            if ref is not None:
                d = ref['d2'] if kind == 'T' else ref
                check(d == rec['d2'], f'{kind}_{p}: d^2 = {d} = audited data of the paper')
            if p <= 41:
                Pref = points(C, p)
                check(as_set(Pref) == as_set(np.array(rec['X']).T), f'{kind}_{p}: point sets equal')
                okb, _ = box_counts_ok(Pref, p, 3)
                check(okb == rec['box'] == (not (kind == 'T' and p == 23)), f'{kind}_{p}: t = 0 by box counts '
                      f'({"not a net, as the paper says" if not okb else "net"})')
                if okb:
                    t, f0 = t_value_matrices(p, 3, 3, [[[x % p for x in row] for row in Cc] for Cc in C])
                    check(t == 0, f'{kind}_{p}: net_tparam t = 0')
                    n_t += 1
                if p <= 29:
                    d2, cnt, ex, _ = min_dist_np(Pref, p, 3, 1, True)
                    if not ex:                                          # c > 1: scan |e| <= 2 as well
                        d2 = min_two(Pref, p)
                    check(d2 == rec['d2'], f'{kind}_{p}: d^2 = {d2} (numpy)')
            bd, c = rec['bounds'], math.sqrt(rec['d2']) / p ** 2
            if kind == 'T':
                r_ = round(p / 8)
                if p >= 7:
                    ds = (p * p - 2 * p + 3) ** 2 + ((r_ - 1) * p + 4) ** 2 + ((r_ - 1) * p + 6) ** 2
                    check(bd['dstar2'] == ds and rec['d2'] <= ds, f'T_{p}: explicit pair of (3), d*^2 = {ds} >= d^2')
                    if p <= 41:
                        P = points(C, p)
                        ia = int(np.where((P // p ** 2 == [0, 0, 0]).all(1))[0][0])
                        ib = int(np.where((P // p ** 2 == [p - 1] * 3).all(1))[0][0])
                        D = tor(P[ib] - P[ia], p ** 3)
                        check(int((D * D).sum()) == ds, f'T_{p}: d*^2 = distance of the cells 0 and (p-1)1')
                if p >= 41:
                    lb = math.sqrt(33 / 32 - 41 / (16 * p)) - math.sqrt(3) / p
                    check(abs(bd['lb'] - lb) < 1e-12 and c >= lb, f'T_{p}: c = {c:.4f} >= bound (2) {lb:.4f}')
            else:
                h_, r_ = (p - 1) // 2, p // 48
                check(rec['rho'] == 2 * r_ + 1 and abs(rec['eps'] - (2 * r_ + 1) / (2 * p)) < 1e-15, f'W_{p}: rho, eps')
                if p >= 53:
                    lb = math.sqrt(281 / 256 - 345 / (128 * p)) - math.sqrt(3) / p
                    ds = (p * p - (6 * r_ + 2) * p - 2) ** 2 + (6 * r_ + 3) ** 2 * p * p + (h_ + 3 * r_ + 2) ** 2 * p * p
                    check(abs(bd['lb'] - lb) < 1e-12 and c >= lb, f'W_{p}: c = {c:.4f} >= bound (2) {lb:.4f}')
                    check(bd['dstar2'] == ds and rec['d2'] < ds, f'W_{p}: pair of (3), d*^2 = {ds} > d^2')
                if p >= 17:
                    check(c > 1, f'W_{p}: c > 1 (prop:wnet(4))')
        # steps along the vertical axis of the slab views
        for st in js['steps']:
            kind, p, ax, tau = st['kind'], st['p'], st['ax'], st['tau']
            B, R = T_rows(p) if kind == 'T' else W_rows(p)
            P = points(graph_C(B, R), p)
            if tau:
                P = shift_points(P, tau, p, 3)
            G = p
            cells = P // p ** 2
            grid = np.empty((G, G, G, 3), dtype=np.int64)
            grid[cells[:, 0], cells[:, 1], cells[:, 2]] = P
            nxt = np.roll(grid, -1, axis=ax)
            D = tor(nxt - grid, p ** 3)
            len2 = (D * D).sum(-1)
            g1, g2 = (grid // p) % p, (nxt // p) % p
            dv = g2 - g1
            wrap = (dv < 0) & (dv % p > 0)
            keys = np.zeros((G, G, G), dtype=np.int64)
            for c in range(3):
                keys = keys * 2 + wrap[..., c]
            got = {g['key']: g for g in st['groups']}
            ok = True
            for kk in np.unique(keys):
                key = format(int(kk), '03b')
                msk = keys == kk
                g = got.get(key)
                if g is None or g['count'] != int(msk.sum()) or g['minLen2'] != int(len2[msk].min()):
                    ok = False
            ok = ok and len(got) == len(np.unique(keys))
            for o in st['one']:
                n = tuple(o['n'])
                ok = ok and list(map(int, D[n])) == o['D'] and o['key'] == format(int(keys[n]), '03b')
            label = f'{kind}_{p}{" + shift " + str(tau) if tau else ""}: steps along axis {"xyz"[ax]}'
            check(ok, f'{label}: wrap patterns, counts, shortest steps')
            if kind == 'W' and not tau:
                check('001' not in got, f'{label}: z never wraps alone (locked)')
            if kind == 'W' and tau == [[0, 0, 0], [0, 0, 0], [0, 1, 0]]:
                check('001' in got and got['001']['minLen'] < 0.2, f'{label}: z wraps alone, short step {got["001"]["minLen"]:.4f}')
            if kind == 'T':
                check(all(k[0] == '0' for k in got), f'{label}: x (free) never changes its second digit along e_x')
            if st['d2'] is not None:
                d2 = int(len2.min())
                check(st['d2'] <= d2, f'{label}: page minimum <= shortest axis step')

        # ------------------------------------------------ column ceiling (page 3, section 1)
        for t in js['tri']:
            q, n = t['q'], t['n']
            a, _, phi = figs_col.col_net(q)
            ph = lambda v: int(phi[(v[0] % q) * q * q + (v[1] % q) * q + (v[2] % q)])  # noqa: E731
            m1, m2, m3 = [n[0] + 1, n[1], n[2]], [n[0] + 1, n[1] + 1, n[2]], [n[0] + 1, n[1] + 1, n[2] + 1]
            st = [(ph(m1) - ph(n)) % (q * q), (ph(m2) - ph(m1)) % (q * q), (ph(m3) - ph(m2)) % (q * q)]
            g3 = None
            for v in itertools.product(range(q), repeat=3):
                for i in range(3):
                    w = list(v)
                    w[i] += 1
                    D3 = 3 * ((ph(w) - ph(v)) % (q * q))
                    dd = abs(D3 - 2 * q * q) % (3 * q * q)
                    dd = min(dd, 3 * q * q - dd)
                    g3 = dd if g3 is None else min(g3, dd)
            ok = t['tri']['steps'] == st and t['tri']['sum'] % (q * q) == 0 and t['tri']['g3'] == g3
            ok = ok and t['tri']['d2'] == (2 * q ** 4 + g3 * g3) // 3 == figs_col.d2_closed(q) == t['d2']
            check(ok, f'C_{q}: triangle steps {st} close up, 3g = {g3}, d^2 = (2q^4 + 9g^2)/3 = thm:col (thm:colmin)')
        okc = all(g <= 1 / 3 + 1e-12 and (abs(sm - round(sm)) < 1e-9) for _, _, g, sm in js['ceil'])
        mx = max(g for _, _, g, _ in js['ceil'])
        check(okc and abs(mx - 1 / 3) < 1e-9, f'cor:colceil: g <= 1/3 on a {120}x{120} grid of steps, max {mx:.6f}')

        # ------------------------------------------------ bases two and three (lem:shiftcert)
        bad = sum(1 for e in js['mu'] if not (e['mu'] == e['brute'] == mu_brute(e['d'], e['b'])))
        check(bad == 0, f'mu_n: {len(js["mu"])} digit vectors, subset rule = page brute force = python brute force')
        for rec in js['every']:
            k, b, m = rec['k'], rec['b'], rec['m']
            C = netdefs.P_mats(k)['C']
            check([[[x % b for x in row] for row in Cc] for Cc in C] == rec['C'], f'P_{k},{b}: generator matrices')
            P = points(C, b)
            check(as_set(P) == as_set(np.array(rec['X']).T), f'P_{k},{b}: point sets equal')
            okb, _ = box_counts_ok(P, b, m)
            t, _ = t_value_matrices(b, m, 3, [[[x % b for x in row] for row in Cc] for Cc in C])
            check(okb and rec['box'] and t == 0, f'P_{k},{b}: t = 0 (net_tparam, box counts, page)')
            W = b ** m
            check(min_dist_brute(P, W) == rec['d2un'], f'P_{k},{b}: unshifted d^2')
            # the lemma's formula, here from mu by brute force over X
            mus = {}
            best = None
            for i in range(1, len(P)):
                tot = 0
                for c in range(3):
                    dg = [int(P[i, c]) // b ** (m - 1 - j) % b for j in range(m)]
                    key = tuple(dg)
                    if key not in mus:
                        mus[key] = mu_brute(dg, b)
                    tot += mus[key] ** 2
                best = tot if best is None else min(best, tot)
            ev = rec['every']
            check(ev['d2'] == best, f'P_{k},{b}: every-shift minimum d^2 = {best} (lem:shiftcert(b), formula)')
            Ps = shift_points(P, ev['tau'], b, m)
            check(min_dist_brute(Ps, W) == best == rec['atTau'], f'P_{k},{b}: attained at the page\'s shift {ev["tau"]}')
            check(all(min_dist_brute(shift_points(P, e['tau'], b, m), W) == e['d2'] >= best for e in rec['random']),
                  f'P_{k},{b}: 25 random shifts, exact d^2 >= every-shift minimum')
            if 'brute' in rec:
                taus = list(itertools.product(range(b ** m), repeat=3))
                vals = np.array([[[t // b ** (m - 1 - j) % b for j in range(m)] for t in tt] for tt in taus])
                mn = None
                for tv in vals:
                    v = min_dist_brute(shift_points(P, tv, b, m), W)
                    mn = v if mn is None else min(mn, v)
                check(mn == best == rec['brute']['d2'], f'P_{k},{b}: all {len(taus)} shifts tried: min d^2 = {mn}')

        # ------------------------------------------------ Q*_p (prop:half5)
        hx = load('half5_exact.json')['mind']
        for rec in js['half5']['nets']:
            p = rec['p']
            G5 = h5q.gens_mod(h5q.HQ, (h5q.D1Q, h5q.D2Q, h5q.D3Q), p)
            check(G5 == rec['C'], f'Q*_{p}: generator matrices = half5_qstar.gens_mod')
            check(rec['onePerCell'] and rec['d2'] == hx[str(p)]['d2'], f'Q*_{p}: d^2 = {rec["d2"]} = half5_exact.json')
            if rec['X'] is not None:
                P = points(G5, p)
                check(as_set(P) == as_set(np.array(rec['X']).T), f'Q*_{p}: point sets equal')
                d2, cnt, ex, _ = min_dist_np(P, p, 5, 1, True)
                check(ex and d2 == rec['d2'] and cnt == rec['count'], f'Q*_{p}: numpy d^2 = {d2}, {cnt} closest pairs')
            if rec['box'] is not None:
                t, _ = t_value_matrices(p, 5, 5, G5)
                check(rec['box'] and t == 0, f'Q*_{p}: t = 0 (net_tparam and page)')
        stq = h5q.Steps(h5q.HQ, h5q.D1Q)
        for e in js['half5']['lb2']:
            p = e['p']
            sq, arg = h5q.lb_r2_sq(stq, p)
            lb = min(2.0, math.sqrt(sq) / p ** 2)
            ub = math.sqrt(5) / 2 + 4 * math.sqrt(5) / p if p > 32 else None
            check(e['sq'] == sq and abs(e['lb'] - lb) < 1e-15 and (e['ub'] is None) == (ub is None)
                  and (ub is None or abs(e['ub'] - ub) < 1e-12), f'Q*_{p}: LB_2 = {lb:.4f} = half5_qstar.lb_r2_sq')
        l31 = next(e['lb'] for e in js['half5']['lb2'] if e['p'] == 31)
        l37 = next(e['lb'] for e in js['half5']['lb2'] if e['p'] == 37)
        check(l31 < 1 < l37 and all(e['lb'] > 1 for e in js['half5']['lb2'] if e['p'] >= 37),
              f'LB_2 crosses 1 between 31 ({l31:.4f}) and 37 ({l37:.4f}), stays above for 37..199')

        # ------------------------------------------------ W_p without its third digits (prop:wfamily(1), (2))
        exact_w = {r['p']: math.sqrt(r['d2']) / r['p'] ** 2 for r in js['tw'] if r['kind'] == 'W'}
        for p, v in js['wnoj']:
            e = (2 * (p // 48) + 1) / (2 * p)
            want = math.sqrt(min(5 / 4 - 9 * e + 81 * e * e, 1 + 4 * e + 36 * e * e))
            ok = abs(v - want) < 1e-14
            if p in (53, 59):
                B, R = W_rows(p)
                P = points(graph_C(B, R), p)
                P = P - P % p                                    # drop the third digits
                ok = ok and abs(math.sqrt(min_two(P, p)) / p ** 2 - v) < 1e-12
            if p in exact_w:
                ok = ok and abs(exact_w[p] - v) < math.sqrt(3) / p
            check(ok, f'W_{p}: value without third digits sqrt(min(q_a, q_b)) = {v:.6f}'
                      f'{" = brute force" if p in (53, 59) else ""}{", within sqrt3/p of the exact value" if p in exact_w else ""}')
        for a, b_, r in js['ceilC']:
            check(abs(r['c'] - math.sqrt(2 / 3 + 3 * r['g'] ** 2)) < 1e-15 and r['c'] <= 1 + 1e-12,
                  f'cor:colceil: steps ({a}, {b_}): g = {r["g"]:.4f}, c = sqrt(2/3 + 3g^2) = {r["c"]:.4f} <= 1')

        # ------------------------------------------------ constants
        bd = js['bounds']
        es = (13 - 2 * math.sqrt(31)) / 90
        check(abs(bd['EPS_STAR'] - es) < 1e-15 and abs(bd['MU_STAR'] - math.sqrt((72 - 8 * math.sqrt(31)) / 25)) < 1e-15
              and abs(5 / 4 - 9 * es + 81 * es ** 2 - (1 + 4 * es + 36 * es ** 2)) < 1e-12
              and abs(bd['MU_STAR'] ** 2 - (1 + 4 * es + 36 * es ** 2)) < 1e-12, 'prop:wfamily: eps*, mu*, q_a = q_b at eps*')
        check(all(abs(a - (5 / 4 - 9 * e + 81 * e * e)) < 1e-15 and abs(b_ - (1 + 4 * e + 36 * e * e)) < 1e-15
                  for e, a, b_ in bd['qa']), 'Table tab:wcontacts rows (a), (b): q_a, q_b')
        check(abs(5 / 4 - 9 / 48 + 81 / 48 ** 2 - 281 / 256) < 1e-15 and abs(1 + 4 / 48 + 36 / 48 ** 2 - 211 / 192) < 1e-15,
              'q_a(1/48) = 281/256, q_b(1/48) = 211/192')

    print(f'node {t_node:.1f}s, total {time.time() - t0:.1f}s; t = 0 by net_tparam for {n_t} T/W nets')
    print(f'{len(cc.OKS)} checks passed, {len(cc.FAILS)} failed')
    sys.exit(1 if cc.FAILS else 0)


def min_two(P, p):
    """exact toroidal minimum over cell steps |e| <= 2 (enough when the minimum is below 2 cells)."""
    G, W = p, p ** 3
    cells = P // p ** 2
    grid = np.empty((G, G, G, 3), dtype=np.int64)
    grid[cells[:, 0], cells[:, 1], cells[:, 2]] = P
    best = None
    for e in itertools.product(range(-2, 3), repeat=3):
        if not any(e):
            continue
        D = tor(np.roll(grid, shift=tuple(-x for x in e), axis=(0, 1, 2)) - grid, W)
        v = int((D * D).sum(-1).min())
        best = v if best is None else min(best, v)
    assert best <= 4 * p ** 4
    return best


if __name__ == '__main__':
    main()

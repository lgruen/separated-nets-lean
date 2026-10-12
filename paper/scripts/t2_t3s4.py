"""t2_t3s4.py -- Table tab:t3s4 / Proposition prop:t3s4 of core.tex: M_p and lambda_inf(kappa) for the 20 primes
7..83, recomputed from the definition in the proof of prop:t3s4 from the designs in t3_s4.json (the fixed data of
the Lean entry S2T3S4).  Used by truncate_bounds.py.
  M_p = min |a|_inf over nonzero a = (a_x, a_z1, a_z2, a_z3) with |a_x| < p/2, prefix fault patterns
  xi_c = sigma_c * ([l_c >= 1], [l_c >= 2]), l_c in {0,1,2}, sigma_c = sgn a_c (l_c = 0 if a_c = 0),
  a_z = centred residue mod p of  kappa a_x + beta xi_x1 + eta xi_x2 + G xi_z1 + H xi_z2,
  G = (g_ij) off the diagonal, own o_i on the diagonal; sign consistency sgn(a_zj) = sigma_zj if l_zj > 0.
  lambda_inf(kappa) = min |u|_inf over nonzero u in {u in Z^4 : u_zi = kappa_i u_x mod p}.
"""
import itertools
import os

HERE = os.path.dirname(os.path.abspath(__file__))
WIT = os.path.join(HERE, 't3_s4.json')
PRIMES = [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83]
PRINTED = {7: (2, 3), 11: (3, 4), 13: (4, 5), 17: (5, 6), 19: (6, 7), 23: (6, 8), 29: (8, 10), 31: (8, 10),
           37: (11, 12), 41: (12, 12), 43: (13, 13), 47: (13, 14), 53: (15, 15), 59: (17, 17), 61: (17, 17),
           67: (17, 19), 71: (18, 20), 73: (18, 19), 79: (21, 21), 83: (22, 23)}
PAIRS = [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]


def cen(v, p):
    v %= p
    return v - p if 2 * v > p else v


def sgn(x):
    return (x > 0) - (x < 0)


# ---------------------------------------------------------------- (1) certificate from the definition
def Mp(p, d):
    G = [[0] * 3 for _ in range(3)]
    for (i, j), v in zip(PAIRS, d['g']):
        G[i][j] = v
    for i in range(3):
        G[i][i] = d['own'][i]
    kap, beta, eta, H = d['kappa'], d['beta'], d['eta'], d['H']
    # per-coordinate (xi1, xi2) for level count l and sign sg
    def xi(l, sg):
        return (sg * (l >= 1), sg * (l >= 2))
    zopts = [(0, 1)] + [(l, sg) for l in (1, 2) for sg in (1, -1)]   # (l, sigma)
    best, arg = None, None
    h = (p - 1) // 2
    for ax in range(-h, h + 1):
        sx = sgn(ax)
        for lx in ((0,) if sx == 0 else (0, 1, 2)):
            x1, x2 = xi(lx, sx)
            base = [kap[i] * ax + beta[i] * x1 + eta[i] * x2 for i in range(3)]
            for zo in itertools.product(zopts, repeat=3):
                X = [xi(l, sg) for (l, sg) in zo]
                az = [cen(base[i] + sum(G[i][j] * X[j][0] + H[i][j] * X[j][1] for j in range(3)), p) for i in range(3)]
                if any(zo[j][0] > 0 and sgn(az[j]) != zo[j][1] for j in range(3)):
                    continue
                if ax == 0 and not any(az):
                    continue
                M = max(abs(ax), *(abs(v) for v in az))
                if best is None or M < best:
                    best, arg = M, (ax, az, lx, zo)
    return best, arg


def lam_inf(kap, p):
    # u_x = 0 forces u_z in pZ^3, so a nonzero such u has |u|_inf >= p > p/2 >= the u_x = 1 candidate
    return min(max(abs(u), *(abs(cen(k * u, p)) for k in kap)) for u in range(1, (p - 1) // 2 + 1))

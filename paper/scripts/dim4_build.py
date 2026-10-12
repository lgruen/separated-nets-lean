"""dim4_build -- exact (over Q) builder for the s=4 frame-(a) nets of the DIM4 probe.

Frame (a): places (0, -1, inf, 1) = orbit of t -> (t-1)/(t+1). Design F = [F0, F1, F2] (first offset row,
levels k-1, k-2, k-3; diagonal = own block). Gauge (Lemma 2 of SGEN / lem:gauge (a),(c)):
Phi'_cd = diag(lam_c,1,..) Phi_cd U_d (U_d lower-triangular), Phi'_cc := first row from F, deeper rows 0.
Solved EXACTLY over Q; then
  * units:    lam_c and diag(U_d) must be +-2^j, every entry of Phi' must lie in Z[1/2];
  * t = 0:    every box minor of the final generator matrices is computed over Q and must be +-2^j
              => (0,4k,4)-net over Z/q for EVERY odd q (Niederreiter unit-minor criterion, lem:nie).
Writes 'q m s' + s m x m generator matrices mod q (index = cell vector).

usage: python dim4_build.py DESIGN.json[:key] k [q OUT.txt] [--minors]
"""
import sys
import json
from fractions import Fraction as Fr
from itertools import combinations
from dim4_frame import gen_mats, graph_form, blk, det_q, inv_q, INF, frac_primes

PLACES = [0, -1, INF, 1]


def solve_exact(A, b):
    n = len(A[0])
    M = [list(map(Fr, A[r])) + [Fr(b[r])] for r in range(len(A))]
    rk = 0
    for col in range(n):
        piv = next((r for r in range(rk, len(M)) if M[r][col] != 0), None)
        if piv is None:
            raise ValueError('singular')
        M[rk], M[piv] = M[piv], M[rk]
        iv = 1 / M[rk][col]
        M[rk] = [x * iv for x in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[rk])]
        rk += 1
    for r in range(rk, len(M)):
        if M[r][n] != 0:
            raise ValueError('inconsistent (target not in the gauge orbit)')
    return [M[r][n] for r in range(n)]


def build(F, k, places=None):
    """places: the four places in coordinate order (default PLACES = frame (a)); 'inf' or a rational."""
    s = 4
    m = s * k
    Phi, _ = graph_form(gen_mats(PLACES if places is None else places, m), k)
    L = min(k, len(F))
    T = [[[Fr(0)] * k for _ in range(s)] for _ in range(s)]
    for l in range(L):
        for c in range(s):
            for d in range(s):
                T[c][d][k - 1 - l] = Fr(F[l][c][d])
    first = [[blk(Phi, c, d, k)[0] if c != d else None for d in range(s)] for c in range(s)]
    lam, u = [Fr(1)] + [None] * 3, [None] * 4
    changed = True
    while changed:
        changed = False
        for c in range(s):
            for d in range(s):
                if c == d:
                    continue
                f, t = first[c][d][k - 1], T[c][d][k - 1]
                if lam[c] is not None and u[d] is None:
                    u[d] = t / (lam[c] * f)
                    changed = True
                elif u[d] is not None and lam[c] is None:
                    lam[c] = t / (u[d] * f)
                    changed = True
    for c in range(s):
        for d in range(s):
            if c != d and lam[c] * first[c][d][k - 1] * u[d] != T[c][d][k - 1]:
                raise ValueError('level-0 layer not diagonally equivalent to the frame layer')
    Us = []
    for d in range(s):
        U = [[Fr(0)] * k for _ in range(k)]
        U[k - 1][k - 1] = u[d]
        rows_c = [c for c in range(s) if c != d]
        for j in range(k - 2, -1, -1):
            unk = list(range(j, k))
            b = [T[c][d][j] for c in rows_c]
            if len(unk) > 3:
                free = unk[-3:]
                A2 = [[lam[c] * first[c][d][i] for i in free] for c in rows_c]
                b2 = [b[r] - lam[c] * first[c][d][j] for r, c in enumerate(rows_c)]
                x = solve_exact(A2, b2)
                U[j][j] = Fr(1)
                for i, xi in zip(free, x):
                    U[i][j] += xi
            else:
                A = [[lam[c] * first[c][d][i] for i in unk] for c in rows_c]
                x = solve_exact(A, b)
                for i, xi in zip(unk, x):
                    U[i][j] = xi
            if U[j][j] == 0:
                raise ValueError('zero pivot')
        Us.append(U)
    newPhi = []
    for c in range(s):
        rows = [[Fr(0)] * m for _ in range(m - k)]
        for d in range(s):
            if c == d:
                for l in range(L):
                    rows[0][d * k + k - 1 - l] = Fr(F[l][c][c])
                continue
            B = blk(Phi, c, d, k)
            for r in range(m - k):
                sc = lam[c] if r == 0 else 1
                for j in range(k):
                    rows[r][d * k + j] = sc * sum(B[r][i] * Us[d][i][j] for i in range(j, k))
        for d in range(s):
            if d != c:
                assert all(rows[0][d * k + j] == T[c][d][j] for j in range(k))
        newPhi.append(rows)
    Cs = []
    for c in range(s):
        C = [[Fr(int(i == c * k + j)) for i in range(m)] for j in range(k)] + newPhi[c]
        Cs.append(C)
    units = list(lam) + [Us[d][j][j] for d in range(s) for j in range(k)]
    up = set().union(*(frac_primes(x) for x in units))
    ep = set()
    for C in Cs:
        for row in C:
            for x in row:
                ep |= frac_primes(Fr(x).denominator)
    return Cs, up, ep


def compositions(m, s):
    if s == 1:
        yield (m,)
        return
    for d in range(m + 1):
        for rest in compositions(m - d, s - 1):
            yield (d,) + rest


def minor_primes(Cs):
    s, m = len(Cs), len(Cs[0])
    ps = set()
    nb = 0
    for d in compositions(m, s):
        rows = [Cs[c][j] for c in range(s) for j in range(d[c])]
        D = det_q(rows)
        if D == 0:
            return None, d
        ps |= frac_primes(D)
        nb += 1
    return ps, nb


def write_mats(Cs, q, fn):
    s, m = len(Cs), len(Cs[0])
    with open(fn, 'w') as f:
        f.write('%d %d %d\n' % (q, m, s))
        for C in Cs:
            for row in C:
                vals = []
                for x in row:
                    x = Fr(x)
                    vals.append(x.numerator * pow(x.denominator, -1, q) % q)
                f.write(' '.join(map(str, vals)) + '\n')


if __name__ == '__main__':
    spec = sys.argv[1]
    fn, key = (spec.split(':') + [None])[:2]
    D = json.load(open(fn))
    if key is not None:
        D = D[key]
    F = D['F'] if isinstance(D, dict) else D
    k = int(sys.argv[2])
    Cs, up, ep = build(F, k)
    print('k=%d m=%d: unit primes %s, entry-denominator primes %s' % (k, 4 * k, sorted(up), sorted(ep)))
    if '--minors' in sys.argv:
        ps, nb = minor_primes(Cs)
        print('  box minors: %s' % ('ZERO at %s' % (nb,) if ps is None else 'all nonzero, %d boxes, primes %s' % (nb, sorted(ps))))
    args = [a for a in sys.argv[3:] if not a.startswith('--')]
    if len(args) >= 2:
        write_mats(Cs, int(args[0]), args[1])
        print('  wrote', args[1])

#!/usr/bin/env python3
r"""net_tparam.py -- the CANONICAL exact t-value computer for digital (t,m,s)-nets over F_b.

WHY THIS FILE EXISTS (the bug it fixes)
---------------------------------------
`algs_mind2.cpp` (research repository) prints 5 fields:  d2  c  gensum_rank  triple_min_rank  triple_def_count.
The 5th field `tdef` (= triple_def_count, code lines 57-60) counts the generator-matrix TRIPLES
whose SUM is rank-deficient mod b.  For s=3 that is exactly  [ rank(C1+C2+C3) < m ]  -- a
RESONANCE / structure-factor diagnostic, redundant with field 3 (gensum_rank).  It is NOT the
(t,m,s)-net t-parameter.  The docs that said "tdef=0 => t=0" were WRONG.

PROOF it is wrong (single counterexample, decisive): the classical Faure (0,m,3)-net
(C1=I, C2=P, C3=P^2 with P the base-b Pascal upper-triangular matrix) is GENUINELY t=0, yet
I+P+P^2 is rank-deficient over F_b => algs_mind2 reports tdef>=1.  Verified below (m=3,4,5,b=3):
net_tparam says t=0, algs_mind2 says tdef=1.  A resonance flag and the t-parameter are different
objects; use THIS file for t, use gensum_rank/tdef for resonance.

THE CORRECT DEFINITION (Niederreiter, digital (t,m,s)-net over F_b)
------------------------------------------------------------------
Given s generator matrices C_1..C_s (each m x m over F_b), the digital net is a (t,m,s)-net iff
for EVERY composition (d_1,...,d_s) of (m-t) into s non-negative integer parts, the (m-t) x m
matrix stacking [the first d_j rows of C_j, j=1..s] has full row rank (m-t) over F_b.
  * t = 0  <=>  this holds for every composition of m (the stacked m x m matrix is nonsingular).
  * The property is MONOTONE in k = m - t: if every composition of k has full rank k, then so
    does every composition of k-1 (drop one row from an independent set -> still independent, and
    every (k-1)-composition is a row-subset of some k-composition).  PROOF in the module docstring
    of `t_value_matrices`.  Hence the set of good k is {0,1,...,k*} and the EXACT t = m - k*, where
    k* = the largest k in {0..m} for which every composition of k gives full rank k.

ROW-ORIENTATION CONVENTION (calibrated against Faure -- see the research notes)
---------------------------------------------------------------------------
"First d_j rows" = the TOP rows, indices 0..d_j-1 (row 0 = MOST-significant output digit).
This is THE repo convention: it is the exact match to the point-generation used by algs_mind2.cpp
and lab.py, where a coordinate's output digit vector is  e = C . d  with e[0] the MOST-significant
digit (MSB-first), so the top d rows of C produce the top d output digits.  With this convention
the classical base-3 Faure (I, P, P^2) comes out t=0 at m=3,4,5 (VERIFIED).  The equivalence
"top d rows full-rank  <=>  every order-k elementary interval holds exactly b^(m-k) points" is a
theorem, not a fit (derivation in the research notes); it is additionally cross-checked here against
an independent brute point-enumeration t-checker (`t_value_points`).

USAGE
-----
Drop-in t-oracle, SAME STDIN format as algs_mind2 (`b m s` then s*m*m ints, row-major):
    echo "3 3 3  <27 ints>" | uv run --with numpy python net_tparam.py
    -> prints:  t=<int> t0=<0|1>
(numpy is only needed for the optional point-based validation path; the matrix t-checker is
pure Python.)

Library:
    from net_tparam import t_value_matrices, t_value_points, faure_matrices
    t, t0 = t_value_matrices(b, m, s, [C1, C2, ...])   # C_j = m x m list-of-lists over F_b
"""
import sys
from itertools import product


# ------------------------------------------------------------------ rank mod prime
def rank_mod_p(rows, ncols, p):
    """Row rank over F_p of the given list of row-vectors (each length ncols). p prime.
    Non-destructive (copies).  Plain Gaussian elimination."""
    a = [[int(v) % p for v in r] for r in rows]   # coerce (handles numpy ints) + reduce mod p
    nrows = len(a)
    r = 0
    for c in range(ncols):
        if r >= nrows:
            break
        piv = -1
        for i in range(r, nrows):
            if a[i][c] % p != 0:
                piv = i
                break
        if piv < 0:
            continue
        a[r], a[piv] = a[piv], a[r]
        inv = pow(a[r][c] % p, p - 2, p)          # Fermat inverse (p prime)
        a[r] = [(v * inv) % p for v in a[r]]
        for i in range(nrows):
            if i == r:
                continue
            f = a[i][c] % p
            if f:
                a[i] = [(a[i][j] - f * a[r][j]) % p for j in range(ncols)]
        r += 1
    return r


# ------------------------------------------------------------------ compositions
def compositions(total, parts):
    """Yield all compositions of `total` into exactly `parts` non-negative integer parts."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


# ------------------------------------------------------------------ the matrix t-checker
def _leading_rows(C, d, top_rows=True):
    """The first `d` rows of generator matrix C (d>=0). top_rows=True -> rows 0..d-1 (the repo
    convention, row 0 = MSB output digit).  top_rows=False -> the bottom d rows (only used to
    demonstrate the calibration in the research notes)."""
    if d == 0:
        return []
    if top_rows:
        return [C[i] for i in range(d)]
    m = len(C)
    return [C[i] for i in range(m - d, m)]


def _all_compositions_full_rank(k, m, s, Cs, p, top_rows=True):
    """True iff EVERY composition of k into s parts gives a stacked leading-rows matrix of rank k."""
    for comp in compositions(k, s):
        if any(d > m for d in comp):
            continue
        rows = []
        for j in range(s):
            rows.extend(_leading_rows(Cs[j], comp[j], top_rows))
        if rank_mod_p(rows, m, p) < k:
            return False
    return True


def t_value_matrices(b, m, s, Cs, top_rows=True):
    r"""Exact t-parameter of the digital (t,m,s)-net with generator matrices Cs (each m x m over F_b).

    Returns (t, t0_flag) where t0_flag is True iff t == 0.

    MONOTONICITY (why scanning k from m downward and returning at the first success is exact):
    Claim: if every composition of k gives full rank k, then every composition of k-1 gives full
    rank k-1.  Proof: let (d_1,...,d_s) be a composition of k-1.  Pick any part i with d_i < m and
    form the composition (d_1,...,d_i+1,...,d_s) of k (possible since sum = k-1 < k <= m, so some
    part is < m).  Its stacked leading-rows matrix has rank k => its k rows are independent.  The
    (k-1)-composition's stacked matrix is obtained by deleting exactly one of those rows (the
    (d_i+1)-th, i.e. the last row of block i), so its k-1 rows are a subset of an independent set,
    hence independent => rank k-1.  Therefore the good-k set is a down-closed interval {0..k*} and
    t = m - k*.  (k=0 trivially holds: empty matrix, rank 0.)
    """
    for k in range(m, -1, -1):
        if _all_compositions_full_rank(k, m, s, Cs, b, top_rows):
            return m - k, (k == m)
    return m, False  # unreachable (k=0 always holds), kept for totality


# ------------------------------------------------------------------ Faure reference matrices
def pascal_upper(m, b):
    """Upper-triangular Pascal matrix P over F_b: P[i][j] = C(j,i) mod b for 0<=i<=j<m, else 0."""
    from math import comb
    return [[(comb(j, i) % b) if j >= i else 0 for j in range(m)] for i in range(m)]


def matmul_mod(A, C, b):
    m = len(A)
    n = len(C[0])
    kdim = len(C)
    return [[sum(A[i][t] * C[t][j] for t in range(kdim)) % b for j in range(n)] for i in range(m)]


def faure_matrices(m, b, s=3):
    """Classical Faure (0,m,s)-net generator matrices: C_j = P^(j-1), P = upper-tri Pascal.
    Valid (t=0) for prime b >= s.  Returns list of s matrices (each m x m, over F_b)."""
    I = [[1 if i == j else 0 for j in range(m)] for i in range(m)]
    P = pascal_upper(m, b)
    Cs = [I]
    cur = I
    for _ in range(s - 1):
        cur = matmul_mod(cur, P, b)
        Cs.append(cur)
    return Cs


# ------------------------------------------------------------------ point-based brute t-checker
def digital_points(b, m, s, Cs):
    """Generate the N=b^m points of the digital net {(C_1.d, ..., C_s.d)} using the repo MSB
    convention (row 0 = MSB output digit), matching algs_mind2.cpp.  Returns (N, s) int list.
    Uses numpy if available for speed; falls back to pure Python."""
    N = b ** m
    try:
        import numpy as np
        idx = np.arange(N, dtype=np.int64)
        D = np.zeros((N, m), dtype=np.int64)
        for r in range(m):
            D[:, r] = (idx // b ** (m - 1 - r)) % b      # D[:,0] = MSB input digit
        w = (b ** (m - 1 - np.arange(m))).astype(np.int64)  # w[0] weights MSB output digit
        cols = []
        for C in Cs:
            E = (D @ np.asarray(C, dtype=np.int64).T) % b   # E[:,i] = i-th output digit (row i of C)
            cols.append((E * w).sum(1))
        return np.stack(cols, axis=1).tolist()
    except ImportError:
        pts = []
        for x in range(N):
            d = [(x // b ** (m - 1 - r)) % b for r in range(m)]
            row = []
            for C in Cs:
                val = 0
                for i in range(m):
                    e = sum(C[i][j] * d[j] for j in range(m)) % b
                    val += e * b ** (m - 1 - i)
                row.append(val)
            pts.append(row)
        return pts


def t_value_points(P, b, m, s):
    r"""Exact t-parameter from the POINT SET P (N x s, entries in [0, b^m)) by brute elementary-
    interval enumeration -- INDEPENDENT of the matrix machinery, and works for NONLINEAR nets too.
    k* = largest k such that for every composition (a_1..a_s) of k, fixing the top a_i digits of
    coord i partitions the N points into b^k equal classes of size b^(m-k).  t = m - k*."""
    N = b ** m
    Pl = [list(row) for row in P]
    assert len(Pl) == N and all(len(r) == s for r in Pl)
    for k in range(m, -1, -1):
        ok = True
        for comp in compositions(k, s):
            counts = {}
            for row in Pl:
                key = 0
                for i in range(s):
                    top = row[i] // (b ** (m - comp[i]))   # top comp[i] digits of coord i
                    key = key * (b ** comp[i]) + top
                counts[key] = counts.get(key, 0) + 1
            target = b ** (m - k)
            if len(counts) != b ** k or any(v != target for v in counts.values()):
                ok = False
                break
        if ok:
            return m - k, (k == m)
    return m, False


# ------------------------------------------------------------------ STDIN drop-in
def _read_matrices_stdin():
    toks = sys.stdin.read().split()
    it = iter(toks)
    b = int(next(it)); m = int(next(it)); s = int(next(it))
    Cs = []
    for _ in range(s):
        C = [[int(next(it)) % b for _ in range(m)] for _ in range(m)]
        Cs.append(C)
    return b, m, s, Cs


def main():
    b, m, s, Cs = _read_matrices_stdin()
    t, t0 = t_value_matrices(b, m, s, Cs, top_rows=True)
    print(f"t={t} t0={1 if t0 else 0}")


if __name__ == "__main__":
    main()

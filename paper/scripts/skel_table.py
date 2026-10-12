#!/usr/bin/env python3
"""skel_table.py -- Table tab:skel of core.tex: the lower bounds of Theorems thm:S1 and thm:S2 for delta N^{1/s}.

Evaluations of the proved formulas, in exact integer arithmetic, truncated to three digits:
  thm:S1 (r = s-1):  (rho-1) p^{-1/s},  rho = max{rho : rho^s < p};  p_0 = least prime with rho >= 2 (p > 2^s);
                     "--" where p <= 2^s.
  thm:S2 (r = s-2):  s = 4:  (rho-4) p^{-1/2},  rho = max{rho : rho^2 - 4 < p};
                     s >= 5: (B(p) - F) p^{-2/s},  F = 1 + ceil((s-2)/2),  B(p) = the largest B >= 1 with
                     B (1 + max_j ||A_j(B)||_1) < p  (Definition def:G2rule: the Gaussian mixed radix of Lemma lem:G2N1,
                     c_1 = floor(sqrt2 B) + 1, c_l = floor(sqrt B) + 1 for l >= 2);
                     p_0 = least prime from which on the bound is positive; printed 0 below p_0.
Every cell of the table is asserted.

    uv run python scripts/skel_table.py      (~1 s)
"""
import math
import sys

S1COLS = [37, 101, 1009, 10007, 10 ** 6 + 3]
S2COLS = [101, 1009, 10007, 10 ** 5 + 3, 10 ** 6 + 3]
PAPER = {  # s: (S1 p_0, S1 values, S2 p_0, S2 values)   -- as printed in tab:skel
    3: ('11', ['.600', '.644', '.897', '.928', '.989'], None, None),
    4: ('17', ['.405', '.630', '.709', '.899', '.948'], '23', ['.597', '.849', '.959', '.986', '.995']),
    5: ('37', ['.485', '.397', '.501', '.792', '.883'], '137', ['0', '.440', '.652', '.759', '.796']),
    6: ('67', ['--', '.463', '.631', '.646', '.899'], '443', ['0', '.299', '.556', '.689', '.769']),
    7: ('131', ['--', '--', '.372', '.536', '.833'], '2179', ['0', '0', '.287', '.484', '.617']),
    8: ('257', ['--', '--', '.421', '.632', '.711'], '6101', ['0', '0', '.199', '.449', '.632']),
}


def isprime(n):
    return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))


def iroot(y, s):  # floor(y^(1/s)), y >= 0 an integer
    x = int(round(y ** (1.0 / s))) if y < 10 ** 300 else 1 << (y.bit_length() // s)
    while x ** s > y:
        x -= 1
    while (x + 1) ** s <= y:
        x += 1
    return x


def trunc3(v, den, s):  # floor(1000 * (v^s/den)^(1/s)) for v >= 0, formatted
    n = iroot((1000 * v) ** s // den, s)
    return '0' if n == 0 else ('.%03d' % n if n < 1000 else '%d.%03d' % divmod(n, 1000))


def rho_S1(p, s):
    r = 1
    while (r + 1) ** s < p:
        r += 1
    return r


def S1(p, s):
    rho = rho_S1(p, s)
    return '--' if rho < 2 else trunc3(rho - 1, p, s)


def rho_S2_4(p):
    r = 1
    while (r + 1) ** 2 < p + 4:
        r += 1
    return r


def G2_norm(B, s):  # max_j ||A_j(B)||_1 of the Gaussian mixed radix (Lemma lem:G2N1, Definition def:G2rule)
    r = s - 2
    cs = [math.isqrt(2 * B * B) + 1] + [math.isqrt(B) + 1] * (r - 2)
    Om, z = [], (1, 0)
    for c in cs:
        z = (z[0] * c - z[1], z[0] + z[1] * c)          # z * (c + i)
        Om.append(z)
    cols = [Om[l] for l in range(r - 2)] + [Om[r - 2], (-Om[r - 2][1], Om[r - 2][0])]
    return max(sum(abs(c[0]) for c in cols), sum(abs(c[1]) for c in cols))


def Bp(p, s):
    """largest B >= 1 with B(1 + max_j ||A_j(B)||_1) < p (None if none); the scan stops once sqrt2 B^2 >= p, after
    which the condition fails (||A_j||_1 >= c_1 > sqrt2 B)"""
    best, B = None, 1
    while 2 * B ** 4 < p * p:
        if B * (1 + G2_norm(B, s)) < p:
            best = B
        B += 1
    return best


def F_of(s):
    return 1 + -(-(s - 2) // 2)


def S2_positive(p, s):
    if s == 4:
        return rho_S2_4(p) - 4 > 0
    return (Bp(p, s) or 0) - F_of(s) > 0


def S2(p, s):
    if s == 4:
        v = rho_S2_4(p) - 4
        return trunc3(v, p, 2) if v > 0 else '0'
    v = (Bp(p, s) or 0) - F_of(s)
    return trunc3(v, p * p, s) if v > 0 else '0'


def first_prime(pred):
    p = 2
    while not (isprime(p) and pred(p)):
        p += 1
    return p


def main():
    bad = 0
    for s, (p0, v1, q0, v2) in PAPER.items():
        g0 = str(first_prime(lambda p: rho_S1(p, s) >= 2))
        g1 = [S1(p, s) for p in S1COLS]
        line = f's={s}  S1: p0={g0} ' + ' '.join(g1)
        ok = g0 == p0 and g1 == v1
        if q0 is not None:
            h0 = str(first_prime(lambda p: S2_positive(p, s)))
            h1 = [S2(p, s) for p in S2COLS]
            line += f'   S2: p0={h0} ' + ' '.join(h1)
            ok &= h0 == q0 and h1 == v2
        bad += not ok
        print(f'  {line}   {"ok" if ok else "MISMATCH (paper: %s %s %s %s)" % (p0, v1, q0, v2)}')
    print('skel_table:', 'all cells agree with Table tab:skel' if not bad else f'{bad} row(s) MISMATCH')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()

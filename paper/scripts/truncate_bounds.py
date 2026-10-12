#!/usr/bin/env python3
"""Systematic truncation sweep for core.tex (+ figs/arc_captions.tex): recompute every printed certified
LOWER bound from its defining formula / certificate, compare with the printed digits, and list what must
change.  Lower bounds and exact (or computed) values must be TRUNCATED, upper bounds ROUNDED UP (rev 15.2:
exact values were rounded to nearest before; a rounded value is now a failure, see Section sec:conv).

Run (from anywhere; ~5 s):
    uv run --with mpmath --with numpy python scripts/truncate_bounds.py      (exit status 1 on any discrepancy)
(stable mpmath 1.3 suffices: no mpf is compared with a Fraction.)

Arithmetic.  Values are exact wherever possible:
  * Q(x)            a rational (fractions.Fraction);
  * Root(n, r, sg)  sg * r**(1/n) with r a nonnegative rational: floor(x*10^d) is computed with an exact
                    integer n-th root of floor(r*10^(n*d)) (floor(floor(y)^(1/n)) = floor(y^(1/n))), and the
                    round-to-nearest / round-up decisions by exact rational comparisons;
  * MP(f)           anything else (sums with roots, arctan, pi): mpmath at 80 digits, and the script refuses
                    to decide a digit if x*10^d is within 1e-50 of an integer (AMBIGUOUS is printed).
The relaxations (Proposition prop:Hk(1), and the half-integer layer of sec:halfms) are evaluated in exact
integer arithmetic (numpy int64, values < 2^40) and give sum-of-squares integers S, so the bound is
Root(2, S/(scale)) exactly.  numpy is only needed for those; without it they are reported CANNOT-RECOMPUTE.

Helpers and data (rev 14.1; all exact arithmetic):
  s1e_certs.py (+ codesaudit_e1.py, e1_*.txt)  prop:S1E / tab:S1E exact J2 = lambda_jit^2 (exact LLL + complete
                   enumeration);
  twocoset_exact.json  (rev 11.4) exact minima of T_p / E_p for prop:twocoset, computed with cellmin.cpp (rerun by
                   twocoset.py); the pair formula of prop:twocoset(3) is asserted equal to them;
  llg_s5_design.json  the split-frame design of prop:HL5 (rev 14.3: the s = 8 sentence of sec:halfms was cut);
  Z3Net/KNDefs.lean of the Lean library (rev 15.1; ../lean or $LEAN_DIR)  the integers T_p of tab:perprime.
Checked elsewhere: tab:c (tab_c.py), tab:astar (as_table.py), tab:Kdesigns, tab:practical, prop:4D2
(deficit_tables.py), tab:skel (skel_table.py), the values after prop:twocoset (twocoset.py).
(rev 13.0 removed the checks that used t2_seqcert.py, t2_limit3.py/.json, t2_dim56_dist.py/.json.  rev 14.1 retired,
because the results are no longer in core.tex: tab:two, cor:rows and rem:q11 (t2_ic2digit.py), prop:4DK2
(dim4_designs.json), cor:dim4, tab:t3s4 and its overview range (t2_t3s4.py, t3_s4.json), tab:half / prop:half
(eis_link_t0_witnesses.json; now one sentence, checked by its s = 5 scan), rem:E1exact, the intro values 1.0352 and
1.219, prop:s5r2 / tab:s5r2 (codesaudit_e2cert.cpp, e2_s5r2_frameorbit_designs.txt), the printed B of the s = 8
design, the app:proofs values .578/.817, and the proof estimates of prop:twocoset.  It added: thm:HL B_4, B_5;
prop:HL5 max|sigma| = 253; rem:S1Elim sqrt(gamma_s); the s = 5 half-integer scan behind "p >= 89"; thm:main
c(q) = 1-1/q for q >= 8; Q_D < 5a+4 for dominant designs; the l_inf mesh ratio < 10/3; thm:base23 constants vs
tab:base23.  A snippet that is no longer in core.tex is now a failure (SNIPPET-MISSING).)

Locations are found at run time by searching for a quoted snippet (the paper is being edited, so line
numbers move); the reported line number is the current one.

Status vocabulary (one line per number):
  OK                  printed == correctly directed rounding (truncation for LB and EX, ceiling for UB)
  ROUNDED-UP          lower bound printed above its truncation  -> CHANGE
  ROUNDED-DOWN-wrong  lower bound printed below its truncation (harmless, reported)
  UB-NOT-ROUNDED-UP   upper bound printed below its ceiling     -> CHANGE
  UB-LOOSE            upper bound printed above its ceiling (valid, loose)
  EXACT-VALUE         exact value, printed digits == its truncation
  EXACT-MISROUNDED    exact value printed rounded (not its truncation) -> CHANGE
  ELLIPSIS-WRONG      exact value written "x\\ldots" whose digits are not the truncation -> CHANGE
  STRICT-OK / STRICT-FAILS   a claim "> X" / "< X" checked exactly
  HEURISTIC           labelled heuristic in the paper; reported only
  CANNOT-RECOMPUTE    with the reason
"""
import json
import math
import os
import re
import sys
import time
from fractions import Fraction as Fr

T0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))             # scripts/ (helpers and data files)
PAPER = os.path.dirname(HERE)                                  # core.tex, figs/
CORE = os.path.join(PAPER, 'core.tex')
CAPS = os.path.join(PAPER, 'figs', 'arc_captions.tex')
# the Lean project: the repository root (deposit), ../lean (source repository), or $LEAN_DIR
# rev 15.1: the restructured Lean library keeps the certified designs (rows and T_p) in Z3Net/KNDefs.lean
_lean_dirs = [os.environ.get('LEAN_DIR', ''), os.path.join(PAPER, 'lean'), os.path.join(os.path.dirname(PAPER), 'lean'), os.path.dirname(PAPER)]
LEAN_KN = next((os.path.join(d, 'Z3Net', 'KNDefs.lean') for d in _lean_dirs
                if d and os.path.exists(os.path.join(d, 'Z3Net', 'KNDefs.lean'))), None)
if LEAN_KN is None:
    sys.exit('Lean file Z3Net/KNDefs.lean not found: set LEAN_DIR to the Lean library directory')

try:
    import mpmath
    from mpmath import mp, mpf
    mp.dps = 80
except ImportError:  # pragma: no cover
    sys.exit("needs mpmath: uv run --with mpmath --with numpy python truncate_bounds.py")
try:
    import numpy as np
except ImportError:
    np = None

TEX = {CORE: open(CORE).read().split('\n'), CAPS: open(CAPS).read().split('\n')}


# ----------------------------------------------------------------------------------------------- arithmetic
def iroot(n, k):
    """floor(n**(1/k)) for an integer n >= 0."""
    if n < 0:
        raise ValueError
    if n < 2:
        return n
    x = 1 << -(-n.bit_length() // k)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    while x ** k > n:
        x -= 1
    while (x + 1) ** k <= n:
        x += 1
    return x


def ffloor(q):
    return q.numerator // q.denominator


class Q:
    def __init__(self, x):
        self.x = Fr(x)

    def mpv(self):
        return mpf(self.x.numerator) / self.x.denominator

    def floor10(self, d):
        return ffloor(self.x * 10 ** d)

    def exact10(self, d):
        return (self.x * 10 ** d).denominator == 1

    def ge_half(self, d, f):  # x*10^d >= f + 1/2 ?
        return self.x * 10 ** d >= Fr(2 * f + 1, 2)

    def gt(self, c):
        return self.x > Fr(c)


class Root:
    """sg * r^(1/n), r >= 0 rational."""

    def __init__(self, n, r, sg=1):
        self.n, self.r, self.sg = n, Fr(r), sg
        assert self.r >= 0

    def mpv(self):
        return self.sg * mpmath.root(mpf(self.r.numerator) / self.r.denominator, self.n)

    def _pos_floor(self, d):  # floor(r^(1/n) * 10^d)
        y = self.r * 10 ** (self.n * d)
        return iroot(ffloor(y), self.n), y

    def floor10(self, d):
        f, y = self._pos_floor(d)
        if self.sg > 0:
            return f
        exact = (y.denominator == 1 and f ** self.n == y)
        return -f if exact else -f - 1

    def exact10(self, d):
        f, y = self._pos_floor(d)
        return y.denominator == 1 and f ** self.n == y

    def ge_half(self, d, f):
        # x*10^d >= f+1/2 ?
        t = Fr(2 * f + 1, 2)
        if self.sg > 0:
            return t <= 0 or self.r * 10 ** (self.n * d) >= t ** self.n
        # negative: -y >= t  <=>  y <= -t
        return t <= 0 and self.r * 10 ** (self.n * d) <= (-t) ** self.n

    def gt(self, c):
        c = Fr(c)
        if self.sg > 0:
            return c < 0 or self.r > c ** self.n
        return c < 0 and self.r < (-c) ** self.n


class MP:
    def __init__(self, f):
        self.v = f()

    def mpv(self):
        return self.v

    def _chk(self, y):
        fr = y - mpmath.floor(y)
        if fr < mpf('1e-50') or fr > 1 - mpf('1e-50'):
            raise ArithmeticError('AMBIGUOUS')

    def floor10(self, d):
        y = self.v * 10 ** d
        self._chk(y)
        return int(mpmath.floor(y))

    def exact10(self, d):
        return False

    def ge_half(self, d, f):
        y = self.v * 10 ** d - (f + mpf(1) / 2)
        if abs(y) < mpf('1e-50'):
            raise ArithmeticError('AMBIGUOUS')
        return y > 0

    def gt(self, c):
        y = self.v - mpf(Fr(c).numerator) / Fr(c).denominator
        if abs(y) < mpf('1e-50'):
            raise ArithmeticError('AMBIGUOUS')
        return y > 0


def vmin(a, b):
    return a if a.mpv() <= b.mpv() else b


def fmt_dec(k, d):
    """integer k representing k/10^d -> decimal string in the paper's style (.xxxx if |x|<1)."""
    neg = k < 0
    k = abs(k)
    s = str(k).rjust(d + 1, '0')
    ip, fp = s[:-d] if d else s, s[-d:] if d else ''
    ip = ip.lstrip('0')
    out = (ip if ip else '') + ('.' + fp if d else '')
    if not ip and not d:
        out = '0'
    return ('-' if neg else '') + out


def parse_printed(s):
    s = s.strip()
    neg = s.startswith('-')
    s = s.lstrip('-')
    if '.' in s:
        ip, fp = s.split('.')
        d = len(fp)
        k = int(ip or '0') * 10 ** d + int(fp)
    else:
        d, k = 0, int(s)
    return (-k if neg else k), d


# ------------------------------------------------------------------------------------------- locators
MISSING = []


def find_line(snippet, path=CORE, nth=0, need=True):
    """current line number of the nth line containing snippet.  A snippet that is not (or no longer) in the paper
    is recorded as SNIPPET-MISSING (a failure: the check it locates would otherwise run against nothing)."""
    hits = [i + 1 for i, l in enumerate(TEX[path]) if snippet in l]
    if len(hits) <= nth:
        if need:
            COUNTS['SNIPPET-MISSING'] = COUNTS.get('SNIPPET-MISSING', 0) + 1
            MISSING.append(snippet)
            print(f"    ? | SNIPPET-MISSING: {snippet!r}")
        return None
    return hits[nth]


def count(snippet, path=CORE):
    return sum(l.count(snippet) for l in TEX[path])


def table_block(label):
    L = TEX[CORE]
    i = next(i for i, l in enumerate(L) if '\\label{%s}' % label in l)
    j = i
    while '\\begin{table}' not in L[j]:
        j -= 1
    return [(k + 1, L[k]) for k in range(j, i + 1)]


def row_cells(line):
    t = line.strip()
    if t.endswith('\\\\'):
        t = t[:-2]
    return [c.strip() for c in t.split('&')]


def clean(c):
    c = c.replace('$^*$', '').replace('^*', '').replace('$', '').strip()
    return c


# ------------------------------------------------------------------------------------------- recording
ROWS = []      # printed table lines
CHANGES = []   # (where, line, old, new, note)
CANNOT = []
COUNTS = {}


def classify(kind, val, printed):
    st, sug, trs, ref = _classify(kind, val, printed)
    if sug and printed.startswith('0.') and sug.startswith('.'):
        sug = '0' + sug          # keep the paper's leading-zero style
    return st, sug, trs, ref


def row_replace(line, repl):
    """replace cell values in a table row, keeping the row's formatting.  repl: {cell index: (old, new)}."""
    t = line.strip()
    end = ''
    if t.endswith('\\\\'):
        t, end = t[:-2], '\\\\'
    parts = t.split('&')
    for i, pairs in repl.items():
        for old, new in pairs:
            assert old in parts[i], (old, parts[i])
            parts[i] = parts[i].replace(old, new, 1)
    return '&'.join(parts) + end


def mkrow(line, old_cells, new_cells):
    repl = {}
    for i, (a, b) in enumerate(zip(old_cells, new_cells)):
        if a != b:
            ta = [x.strip() for x in clean(a).split('/')]
            tb = [x.strip() for x in clean(b).split('/')]
            repl[i] = [(x, y) for x, y in zip(ta, tb) if x != y]
    return row_replace(line, repl)


def _classify(kind, val, printed):
    """returns (status, suggested string or None, truncated string, ref string)."""
    k, d = parse_printed(printed)
    try:
        fl = val.floor10(d)
        ex = val.exact10(d)
        ce = fl if ex else fl + 1
        nr = fl + 1 if val.ge_half(d, fl) else fl
    except ArithmeticError:
        return 'AMBIGUOUS', None, '?', '?'
    trs, ces, nrs = fmt_dec(fl, d), fmt_dec(ce, d), fmt_dec(nr, d)
    if kind == 'LB':
        if k == 0 and d == 0 and val.mpv() <= 0:
            return 'OK', None, trs, 'bound <= 0, printed 0'
        if k == fl:
            return 'OK', None, trs, trs
        if k > fl:
            return 'ROUNDED-UP', trs, trs, trs
        return 'ROUNDED-DOWN-wrong', trs, trs, trs
    if kind == 'UB':
        if k == ce:
            return 'OK', None, trs, 'ceil ' + ces
        if k > ce:
            return 'UB-LOOSE', None, trs, 'ceil ' + ces
        return 'UB-NOT-ROUNDED-UP', ces, trs, 'ceil ' + ces
    if kind == 'EX':  # rev 15.2: exact and computed values are printed TRUNCATED, like lower bounds
        if k == fl:
            return 'EXACT-VALUE', None, trs, 'trunc ' + trs
        return 'EXACT-MISROUNDED', trs, trs, 'trunc ' + trs
    if kind == 'EXT':  # exact value written with \ldots: digits must be the truncation
        if k == fl:
            return 'EXACT-VALUE', None, trs, 'ellipsis ok'
        return 'ELLIPSIS-WRONG', trs, trs, trs
    if kind == 'HEUR':
        return 'HEURISTIC', None, trs, 'nearest ' + nrs
    raise ValueError(kind)


def rec(loc, line, printed, val, kind, note='', old=None, new_fn=None, change=True):
    """one printed number.  old: exact snippet containing the number (for find-replace)."""
    st, sug, trs, ref = classify(kind, val, printed)
    # If the snippet with the recorded value is no longer in the paper but the corrected snippet is, the
    # paper has been fixed: re-classify with the value actually printed now.
    if sug and old is not None and not any(count(old, P) for P in TEX):
        new = new_fn(sug) if new_fn else old.replace(printed, sug, 1)
        if any(count(new, P) for P in TEX):
            printed = sug
            st, sug, trs, ref = classify(kind, val, printed)
    try:
        tv = mpmath.nstr(val.mpv(), 15)
    except Exception:
        tv = '?'
    COUNTS[st] = COUNTS.get(st, 0) + 1
    ln = '%5s' % (line if line else '?')
    print(f"{ln} | {loc:44s} | {printed:>9s} | {tv:>19s} | trunc {trs:>9s} | {kind:4s} | {st}"
          + (f" -> {sug}" if sug and st not in ('ROUNDED-DOWN-wrong',) else '') + (f"  [{note}]" if note else ''))
    if sug and change and st in ('ROUNDED-UP', 'UB-NOT-ROUNDED-UP', 'EXACT-MISROUNDED', 'ELLIPSIS-WRONG'):
        if old is not None:
            CHANGES.append((loc, line, old, new_fn(sug) if new_fn else old.replace(printed, sug, 1), note))
        else:
            CHANGES.append((loc, line, printed, sug, note))
    return st, sug


def rec_strict(loc, line, claim, ok, note=''):
    st = 'STRICT-OK' if ok else 'STRICT-FAILS'
    COUNTS[st] = COUNTS.get(st, 0) + 1
    print(f"{'%5s' % (line or '?')} | {loc:44s} | {claim:>9s} | {'':19s} | {'':15s} | strc | {st}  [{note}]")


def rec_cannot(loc, line, printed, why):
    COUNTS['CANNOT-RECOMPUTE'] = COUNTS.get('CANNOT-RECOMPUTE', 0) + 1
    CANNOT.append((loc, line, printed, why))
    print(f"{'%5s' % (line or '?')} | {loc:44s} | {printed:>9s} | {'':19s} | {'':15s} |      | CANNOT-RECOMPUTE  [{why}]")


def rec_info(loc, line, text):
    print(f"{'%5s' % (line or '?')} | {loc:44s} | INFO: {text}")


def rec_snip(loc, snip, printed, val, kind, note=''):
    """record a printed number located by a snippet; the CHANGE (if any) replaces it inside that snippet."""
    ln = find_line(snip)              # records SNIPPET-MISSING if absent
    if ln is None:
        rec_info(loc, None, f'snippet not found: {snip!r}')
        return None, None
    return rec(loc, ln, printed, val, kind, note=note, old=snip)


def section(t):
    print('\n' + '=' * 8 + ' ' + t + ' ' + '=' * max(0, 100 - len(t)))


# ------------------------------------------------------------------------------------------- number theory
def primes_upto(n):
    s = bytearray([1]) * (n + 1)
    s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** .5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(n + 1) if s[i]]


def isprime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


PR = primes_upto(2_000_000)


# ------------------------------------------------------------------------------------------- formulas
def c3(q):  # thm:main c(q)
    q = Fr(q)
    return Root(2, min((1 - 1 / q) ** 2, (1 - 2 / q) ** 2 + (1 - 4 / q) ** 2, 3 * (1 - 3 / q) ** 2))


def rho_B2(p, s=3):  # max rho with rho^s < p (thm:S1 / rem:B2)
    r = 1
    while (r + 1) ** s < p:
        r += 1
    return r


def rho_B1(p):  # max rho with rho^2 (rho+1) <= p
    r = 1
    while (r + 1) ** 2 * (r + 2) <= p:
        r += 1
    return r


def S1(p, s, rho=None):
    rho = rho_B2(p, s) if rho is None else rho
    if rho < 2:
        return None
    return Root(s, Fr((rho - 1) ** s, p))


def B1(p, rho=None):
    rho = rho_B1(p) if rho is None else rho
    v = rho * rho - 4
    return Root(3, Fr(abs(v) ** 3, p * p), 1 if v >= 0 else -1)


def g_allm(rho):
    return Fr((rho - 2) ** 3 * (rho + 2), (rho + 1) ** 4)


def col_d2(q):  # thm:col(2): exact d^2 of the column net C_q at integer scale q^3
    tau = q * q - q - 3 if q % 3 == 2 else q * q - 2 * q
    return Fr(2 * q ** 4 + tau * tau, 3)


def col_c(q):  # thm:col(2): exact delta N^{1/3} of C_q
    return Root(2, col_d2(q) / q ** 4)


def colshift_LB(q):  # prop:colshift(3): (1 - (W+3)/q + 3/q^2)/sqrt3, W = 2 (q = 2 mod 3), 4 (q = 1 mod 3)
    W = 2 if q % 3 == 2 else 4
    return Root(2, (1 - Fr(W + 3, q) + Fr(3, q * q)) ** 2 / 3)


def E1(p):  # (rev 14.3) thm:E1 bound 1 - sqrt3((1+|g|)p-1)/p^2; no longer printed
    a = p // 3
    g = 3 * a - p
    c = (1 + abs(g)) * p - 1
    return MP(lambda: 1 - mpmath.sqrt(3) * c / mpf(p) ** 2)


def S2_rho4(p):
    r = 1
    while (r + 1) ** 2 < p + 4:
        r += 1
    return r


def S2_s4(p):
    r = S2_rho4(p)
    v = r - 4
    return Root(2, Fr(v * v, p), 1 if v >= 0 else -1)


def G2_norm(B, s):
    r = s - 2
    cs = [math.isqrt(2 * B * B) + 1] + [math.isqrt(B) + 1] * (r - 2)
    Om = []
    z = (1, 0)
    for c in cs:
        z = (z[0] * c - z[1], z[0] + z[1] * c)  # z * (c + i)
        Om.append(z)
    cols = [Om[l] for l in range(r - 2)] + [Om[r - 2], (-Om[r - 2][1], Om[r - 2][0])]
    n1 = sum(abs(c[0]) for c in cols)
    n2 = sum(abs(c[1]) for c in cols)
    return max(n1, n2), cs


def Bp(p, s):
    """def:G2rule: largest B >= 1 with B(1 + max_j ||A_j(B)||_1) < p (None if none).  Exact linear scan,
    stopped once sqrt2*B^2 >= p (then ||A_j||_1 >= |Omega_{r-1}| >= c_1 > sqrt2 B makes it fail)."""
    best, B = None, 1
    while 2 * B ** 4 < p * p:
        if B * (1 + G2_norm(B, s)[0]) < p:
            best = B
        B += 1
    return best


def S2_big(p, s):
    F = 1 + -(-(s - 2) // 2)
    B = Bp(p, s)
    if B is None:
        return Q(0), None
    v = B - F
    return Root(s, Fr(abs(v) ** s, p * p), 1 if v >= 0 else -1), B


# ------------------------------------------------------------------------------------------- relaxations
def axis_options_lemSs(F, L, s):
    """per-axis (e_d, column contribution) options for Lemma lem:Ss with L levels."""
    Ms, acc = [], [[0] * s for _ in range(s)]
    for j in range(L):
        acc = [[acc[c][d] + F[j][c][d] for d in range(s)] for c in range(s)]
        Ms.append(acc)
    opts = []
    for d in range(s):
        o = [(0, [0] * s)]
        for e in (1, -1):
            for j in range(L):
                o.append((e, [e * Ms[j][c][d] for c in range(s)]))
        opts.append(o)
    return opts


def combine(opts, s):
    SIG = np.zeros((1, s), dtype=np.int64)
    EV = np.zeros((1, 0), dtype=np.int64)
    for d in range(s):
        C = np.array([o[1] for o in opts[d]], dtype=np.int64)
        Ev = np.array([o[0] for o in opts[d]], dtype=np.int64)
        n_old, n_opt = SIG.shape[0], C.shape[0]
        SIG = (SIG[:, None, :] + C[None, :, :]).reshape(-1, s)
        EV = np.concatenate([np.repeat(EV, n_opt, axis=0), np.tile(Ev, n_old)[:, None]], axis=1)
    keep = np.any(EV != 0, axis=1)
    return SIG[keep], EV[keep]


def lemSs_S(F, q, L, cache={}):
    """min over (e,j) of sum b_i^2 (Lemma lem:Ss), exact integer."""
    s = len(F[0])
    key = (repr(F), L)
    if key not in cache:
        cache[key] = combine(axis_options_lemSs(F, L, s), s)
    SIG, EV = cache[key]
    mov = (EV != 0).sum(1)
    jit = np.ones_like(EV)
    jit[(mov == 1)[:, None] & (EV != 0)] = 0
    dl = np.mod(SIG, q)
    o1 = np.abs(EV * q + dl)
    o2 = np.where(dl != 0, np.abs(EV * q + dl - q), o1)
    b = np.maximum(0, np.minimum(o1, o2) - jit)
    return int((b * b).sum(1).min())


def lemSs_LB(F, q, L):
    S = lemSs_S(F, q, L)
    return Q(1) if S >= q * q else Root(2, Fr(S, q * q))


def axis_options_hk(F2, L, s):
    """prop:Hk: options per axis, doubled sigma.  F2[n] = 2*F_n (F2[0] odd)."""
    opts = []
    for d in range(s):
        o = [(0, [0] * s)]
        for E in (1, -1, 2, -2):
            sg = 1 if E > 0 else -1
            for j in range(L):
                col = [E * F2[0][c][d] + sg * sum(F2[x][c][d] for x in range(1, j + 1)) for c in range(s)]
                o.append((E, col))
        opts.append(o)
    return opts


def hk_S(F2, p, L, mode='per', cache={}):
    """mode 'per': Proposition prop:Hk(1) per-option relaxation; 'coarse': Proposition prop:half(1) form
    (odd options replaced by p*min|E+-1/2| - |sigma|); 'star': the monotone LB* (every option |alpha p+sigma|
    replaced by |alpha| p - |sigma|).  Returns (S, max|2 sigma|) with LB = min(2, sqrt(S)/(2p))."""
    s = len(F2[0])
    key = (repr(F2), L)
    if key not in cache:
        cache[key] = combine(axis_options_hk(F2, L, s), s)
    S2, EV = cache[key]
    odd = (EV.sum(1) % 2 != 0)[:, None]
    if mode == 'per':
        vo = np.minimum(np.abs(2 * p * EV + S2 + p), np.abs(2 * p * EV + S2 - p))
    else:
        vo = p * np.minimum(np.abs(2 * EV + 1), np.abs(2 * EV - 1)) - np.abs(S2)
    sg = np.sign(S2)
    if mode == 'star':
        e1 = 2 * np.abs(EV) * p - np.abs(S2)
        e2 = np.where(sg != 0, 2 * np.abs(EV - sg) * p - np.abs(S2), e1)
    else:
        e1 = np.abs(2 * p * EV + S2)
        e2 = np.where(sg != 0, np.abs(2 * p * EV + S2 - 2 * p * sg), e1)
    ve = np.minimum(e1, e2)
    b2 = np.maximum(0, np.where(odd, vo, ve) - 2)
    return int((b2 * b2).sum(1).min()), int(np.abs(S2).max())


def hk_LB(F2, p, L, mode='per'):
    S, mx = hk_S(F2, p, L, mode)
    v = Q(2) if S >= 16 * p * p else Root(2, Fr(S, 4 * p * p))
    return v, mx


def frac_mat(rows):
    return [[Fr(x) for x in r] for r in rows]


def doubled(M):
    out = [[int(2 * x) for x in r] for r in M]
    assert all((2 * x).denominator == 1 for r in M for x in r)
    return out


# ===================================================================================================
print("truncate_bounds.py -- systematic truncation sweep of core.tex (rev. on disk at run time)")
print("columns: core.tex line | location | printed | true value (15 sig. digits) | truncation at printed "
      "precision | kind (LB lower bound, UB upper bound, EX exact, EXT exact with \\ldots, HEUR) | status")

# ------------------------------------------------------------------------------------------- tab:c
section('tab:c  (Theorem thm:main c(q); P_{2,q} exact values)')
blk = table_block('tab:c')
qrow = next((n, l) for n, l in blk if l.strip().startswith('$q$ &'))
qs = [int(x) for x in row_cells(qrow[1])[1:]]
n, l = next((n, l) for n, l in blk if l.strip().startswith('certified $c(q)$, all'))
cells = row_cells(l)
newcells = list(cells)
for i, q in enumerate(qs):
    pv = clean(cells[i + 1])
    st, sug = rec(f'tab:c c(q) q={q}', n, pv, c3(q), 'LB', change=False)
    if st == 'ROUNDED-UP':
        newcells[i + 1] = sug
if newcells != cells:
    CHANGES.append(('tab:c row c(q)', n, l.strip(), mkrow(l, cells, newcells), 'whole row'))
# P_{2,q} exact values: 6-digit values of an earlier independent scan -- rounding check only (tab_c_two.py
# recomputes all of them exactly with netmind.cpp)
adv_P2 = {4: '.596455', 5: '.732230', 7: '.857840', 8: '.875380', 9: '.889113', 10: '.900141', 11: '.909184',
          12: '.916730', 13: '.923122'}
n, l = next((n, l) for n, l in blk if l.strip().startswith('exact $c$ of $\\mathcal P_{2,q}$'))
cells = row_cells(l)
for i, q in enumerate(qs):
    pv = clean(cells[i + 1])
    if q in adv_P2:
        k, d = parse_printed(adv_P2[q])
        v = Q(Fr(k, 10 ** d))
        rec(f'tab:c P_2,q exact q={q}', n, pv, v, 'EX', note='exact value (6 digits) of an independent scan; '
            'recomputed exactly by tab_c_two.py', change=False)
    else:
        rec_info(f'tab:c P_2,q exact q={q}', n, f'{pv}: exact min-distance value, not recomputed here')

# (rev 14.1: the checks of tab:two, cor:rows (t2_ic2digit.py), rem:q11, prop:4DK2 (dim4_designs.json) were retired:
# those results are no longer in the paper.  Proposition prop:4D2 and the tables of Part II are checked by
# deficit_tables.py.)

# ------------------------------------------------------------------------------------------- lem:G2N1 etc
section('lem:G2N1, thm:S2 thresholds')
ln = find_line('arctangent sums below $0.487$')
cs_tab = {5: (6, 3), 6: (6, 3, 3), 7: (8, 3, 3, 3), 8: (8, 3, 3, 3, 3)}
for s, pv in zip((5, 6, 7, 8), ('0.487', '0.809', '1.090', '1.412')):
    F = 1 + -(-(s - 2) // 2)
    cs = tuple(G2_norm(F + 1, s)[1])
    assert cs == cs_tab[s], (s, cs)
    rec(f'lem:G2N1(c) arctan sum s={s} (UPPER)', ln, pv, MP(lambda cs=cs: sum(mpmath.atan(mpf(1) / c) for c in cs)),
        'UB', note=f'c_j at B=F+1: {cs}')
ln = find_line('$1.7194\\ldots>\\pi/2$')
cs9 = tuple(G2_norm(6, 9)[1])
rec('after lem:G2N1 arctan sum s=9 at B=F+1', ln, '1.7194', MP(lambda: sum(mpmath.atan(mpf(1) / c) for c in cs9)),
    'EXT', note=f'c_j={cs9}', old='$1.7194\\ldots>\\pi/2$')
ln = find_line('exactly for $p>132$')
thr = []
for s in (5, 6, 7, 8):
    F = 1 + -(-(s - 2) // 2)
    p = 2
    while (Bp(p, s) or 0) < F + 1:
        p += 1
    thr.append(p - 1)
rec_strict('proof thm:S2 "B(p)>=F+1 exactly for p>132,440,2170,6095"', ln, 'ints', thr == [132, 440, 2170, 6095],
           f'computed {thr}')
nxt = [next(q for q in PR if q > t) for t in thr]
rec_strict('thm:S2 least primes 137,443,2179,6101', ln, 'ints', nxt == [137, 443, 2179, 6101], f'computed {nxt}')

# ------------------------------------------------------------------------------------------- tab:skel
section('tab:skel  (Theorems thm:S1 and thm:S2)')
blk = table_block('tab:skel')
S1cols = [37, 101, 1009, 10007, 10 ** 6 + 3]
S2cols = [101, 1009, 10007, 10 ** 5 + 3, 10 ** 6 + 3]
for n, l in blk:
    c = row_cells(l)
    if len(c) < 7 or not c[0].isdigit():
        continue
    s = int(c[0])
    newc = list(c)
    p0 = next(q for q in PR if q > 2 ** s)
    rec_strict(f'tab:skel S1 p_0 s={s}', n, c[1], int(c[1]) == p0, f'least prime > 2^s = {p0}')
    for i, p in enumerate(S1cols):
        pv = clean(c[2 + i])
        v = S1(p, s)
        if pv == '--':
            rec_strict(f'tab:skel S1 s={s} p={p} "--"', n, '--', v is None, 'p <= 2^s')
            continue
        st, sug = rec(f'tab:skel S1 s={s} p={p}', n, pv, v, 'LB', change=False, note=f'rho={rho_B2(p, s)}')
        if st == 'ROUNDED-UP':
            newc[2 + i] = sug
    if s >= 4 and len(c) >= 13:
        if s == 4:
            q0 = next(q for q in PR if S2_rho4(q) >= 5)
        else:
            F = 1 + -(-(s - 2) // 2)
            q0 = next(q for q in PR if (Bp(q, s) or 0) >= F + 1)
        rec_strict(f'tab:skel S2 p_0 s={s}', n, c[7], int(c[7]) == q0, f'computed {q0}')
        for i, p in enumerate(S2cols):
            pv = clean(c[8 + i])
            if s == 4:
                v, note = S2_s4(p), f'rho={S2_rho4(p)}'
            else:
                v, B = S2_big(p, s)
                note = f'B(p)={B}, F={1 + -(-(s - 2) // 2)}'
                if p < q0:
                    v = Q(min(Fr(0), Fr(0)))  # theorem does not apply below p_0; printed 0
                    note += ' (p < p_0)'
            st, sug = rec(f'tab:skel S2 s={s} p={p}', n, pv, v, 'LB', change=False, note=note)
            if st == 'ROUNDED-UP':
                newc[8 + i] = sug
    if newc != c:
        CHANGES.append((f'tab:skel row s={s}', n, l.strip(), mkrow(l, c, newc), 'whole row'))

# ------------------------------------------------------------------------------------------- rem:B2, thm:allm
section('rem:B2, thm:allm, cor:allm (dimension three skeletons; rev 13.0: tab:B and the thm:S1 / rem:skelconst / '
        'thm:allm sampled values were cut)')
# .717--.738: B^2 at p=67,71,73 with rho=4 (intro, tab:overview footnote, tab:perprime caption)
vals = [S1(p, 3, 4) for p in (67, 71, 73)]
lo = min(vals, key=lambda v: v.mpv())
hi = max(vals, key=lambda v: v.mpv())
for occ in range(count('$.717$--$.738$')):
    ln = find_line('$.717$--$.738$', nth=occ)
    st1, s1 = rec(f'.717--.738 low end (B^2,rho=4,p=73) #{occ + 1}', ln, '.717', lo, 'LB', change=False)
    st2, s2 = rec(f'.717--.738 high end (B^2,rho=4,p=67) #{occ + 1}', ln, '.738', hi, 'LB', change=False)
    if 'ROUNDED-UP' in (st1, st2):
        CHANGES.append((f'.717--.738 occurrence #{occ + 1}', ln, '$.717$--$.738$',
                        '$%s$--$%s$' % (s1 or '.717', s2 or '.738'), 'B^2 at p=67,71,73, rho=4: 3p^(-1/3)'))
rec_strict('".717--.738" printed (2 occurrences)', find_line('$.717$--$.738$'), 'count', count('$.717$--$.738$') == 2,
           f"count = {count('$.717$--$.738$')} (tab:overview footnote, tab:perprime caption)")
ln = find_line('$G(27)^{1/3}=0.9033\\ldots$')
rec('proof thm:allm g(27)^{1/3}', ln, '0.9033', Root(3, g_allm(27)), 'LB',
    note='"=" value used as a lower bound ("exceeds 0.9"); nearest rounding would keep .9034', old='$G(27)^{1/3}=0.9033\\ldots$')
# thresholds
P30 = [q for q in PR if q < 40000]
b2 = lambda p: S1(p, 3).mpv() if rho_B2(p) >= 2 else mpf(0)
b1 = lambda p: B1(p).mpv() if rho_B1(p) >= 2 else mpf(-1)
f2 = next(q for q in P30 if b2(q) > mpf('0.9'))
l2 = max(q for q in P30 if b2(q) <= mpf('0.9'))
f1 = next(q for q in P30 if b1(q) > mpf('0.9'))
l1 = max(q for q in P30 if b1(q) <= mpf('0.9'))
ln = find_line('$p\\ge6863$ ($\\rho\\ge19$)')
rec_strict('rem:B2 "exceeds 0.9 for every prime p>=6863", first prime 1361', ln, 'ints',
           f2 == 1361 and l2 < 6863 and next(q for q in PR if q >= 6863) == 6863 and rho_B2(6863) == 19
           and rho_B2(6857) == 18,
           f'first prime >0.9: {f2}; last prime <=0.9 below 40000: {l2}; rho(6863)={rho_B2(6863)}')
ln = find_line('$\\rho\\ge27$ iff $p\\ge20412$')
rec_strict('thm:allm "exceeds 0.9 for p>=20412" (rho>=27 iff p>=20412)', ln, 'ints',
           l1 < 20412 and 27 ** 2 * 28 == 20412 and rho_B1(20412) == 27 and rho_B1(20411) == 26,
           f'first prime >0.9: {f1}; last prime <=0.9 below 40000: {l1}')
# cor:allm constants
section('cor:allm and its proof')
t = time.time()
P = [q for q in PR if q >= 37]
r1 = r2 = 1
mins = []
for p in P:
    while (r1 + 1) ** 2 * (r1 + 2) <= p:
        r1 += 1
    while (r2 + 1) ** 3 < p:
        r2 += 1
    e1 = float(col_c(p).mpv())                                   # rev 15.0: the column net C_p at m = 3
    vb1 = (r1 * r1 - 4) / p ** (2 / 3)
    vb2 = (r2 - 1) / p ** (1 / 3)
    mins.append((min(e1, vb1, vb2, 1 - 1 / p), p, min(((e1, 'E1'), (vb1, 'B1'), (vb2, 'B2'), (1 - 1 / p, 'P')))[1]))
m_all = min(mins)
m_83 = min(x for x in mins if x[1] >= 83)
ln = find_line('\\delta N^{1/3}>0.2715,\\quad')
pa = m_all[1]
vexact = {'B1': B1(pa), 'B2': S1(pa, 3), 'E1': E1(pa), 'P': Q(1 - Fr(1, pa))}[m_all[2]]
rec_strict('cor:allm "delta N^{1/3} > 0.2715" (p>=37)', ln, '0.2715', vexact.gt(Fr(2715, 10000)),
           f'min over primes 37..2e6 of all four bounds = {m_all[0]:.6f} ({m_all[2]} at p={pa}); '
           f'large p covered by g(rho)')
pb = m_83[1]
vexact = {'B1': B1(pb), 'B2': S1(pb, 3), 'E1': E1(pb), 'P': Q(1 - Fr(1, pb))}[m_83[2]]
rec_strict('cor:allm "> 0.4250 if p>=83"', ln, '0.4250', vexact.gt(Fr(4250, 10000)),
           f'min over primes 83..2e6 = {m_83[0]:.6f} ({m_83[2]} at p={pb})')
ln = find_line('5\\cdot79^{-2/3}=0.27157\\ldots$')
rec('proof cor:allm 5*79^{-2/3}', ln, '0.27157', Root(3, Fr(125, 79 ** 2)), 'EXT')
rec_strict('proof cor:allm 2*61^{-1/3} > 0.508', ln, '0.508', Root(3, Fr(8, 61)).gt(Fr(508, 1000)),
           mpmath.nstr(Root(3, Fr(8, 61)).mpv(), 10))
rec_strict('proof cor:allm 1-1/p > 0.97 (p>=37)', ln, '0.97', Fr(36, 37) > Fr(97, 100), '36/37')
rec_strict('proof cor:allm g(4)^{1/3}=(48/625)^{1/3} > 0.4250', ln, '0.4250', Root(3, Fr(48, 625)).gt(Fr(425, 1000)),
           mpmath.nstr(Root(3, Fr(48, 625)).mpv(), 10))
rec_snip('proof cor:allm C_p for p>=37 (min at p=37)', 'for $p\\ge37$, $\\delta N^{1/3}>0.9823$', '0.9823', col_c(37), 'LB')
# mesh maxima
mx_h = mx_r = (0, 0)
r = 1
for p in PR:
    if p < 11:
        continue
    while (r + 1) ** 3 < p:
        r += 1
    mu = -(-p // (r * r))
    hv = math.sqrt(3) * (mu + 1) / p ** (1 / 3)
    rv = math.sqrt(3) * (mu + 1) / (r - 1)
    mx_h = max(mx_h, (hv, p))
    mx_r = max(mx_r, (rv, p))
rec('proof cor:allm max h N^{1/3} (p=23)', ln, '4.2633', Root(6, Fr(27 * 7 ** 6, 23 ** 2)), 'EXT',
    note=f'scan primes 11..2e6: max {mx_h[0]:.6f} at p={mx_h[1]}')
rec_strict('proof cor:allm 4.2633... < 4.264 and cor:allm 4.264', ln, 'UB',
           not Root(6, Fr(27 * 7 ** 6, 23 ** 2)).gt(Fr(4264, 1000)) and mx_h[1] == 23,
           f'max mesh ratio {mx_r[0]:.6f} at p={mx_r[1]} vs 7sqrt3={7 * math.sqrt(3):.6f}')
rec_info('cor:allm scan time', ln, '%.1f s' % (time.time() - t))
# (rev 14.1: cor:dim4 (1/sqrt31) and tab:t3s4 with its tab:overview range .23--.76 were retired: no longer printed.)

# ------------------------------------------------------------------------------------------- tab:perprime
section('tab:perprime  (sqrt(T_p) p^{-5/3} resp. p^{-4/3}, T_p from the Lean library, Z3Net/KNDefs.lean)')
lean = open(LEAN_KN).read()
T1 = {int(a): int(b) for a, b in re.findall(r'\((\d+),\s*(\d+),\s*rows1_\d+\)', lean)}
T2 = {int(a): int(b) for a, b in re.findall(r'\((\d+),\s*(\d+),\s*rows2_\d+\)', lean)}
blk = table_block('tab:perprime')
prows = [(n, l) for n, l in blk if l.strip().startswith('$p$ &')]
r1rows = [(n, l) for n, l in blk if l.strip().startswith('$m\\equiv1$')]
r2rows = [(n, l) for n, l in blk if l.strip().startswith('$m\\equiv2$')]
pp_all = []
for (pn, pl), (n1, l1), (n2, l2) in zip(prows, r1rows, r2rows):
    ps_ = [int(x) for x in row_cells(pl)[1:]]
    for (nn, ll, T, ex, tag) in ((n1, l1, T1, 10, 'm=1'), (n2, l2, T2, 8, 'm=2')):
        c = row_cells(ll)
        newc = list(c)
        for i, p in enumerate(ps_):
            pv = clean(c[i + 1])
            if pv == '--':
                rec_strict(f'tab:perprime {tag} p={p} "--"', nn, '--', p not in T, 'no design in Lean table')
                continue
            v = Root(6, Fr(T[p] ** 3, p ** ex))
            pp_all.append((tag, p, v))
            st, sug = rec(f'tab:perprime {tag} p={p} T_p={T[p]}', nn, pv, v, 'LB', change=False)
            if st == 'ROUNDED-UP':
                newc[i + 1] = sug
        if newc != c:
            CHANGES.append((f'tab:perprime row {tag}', nn, ll.strip(), mkrow(ll, c, newc), 'whole row'))
mx = max((v for t_, p, v in pp_all), key=lambda v: v.mpv())
ln = find_line('$.50$--$1.03$ per prime')
rec('tab:overview .50--1.03 low end', ln, '.50', min((v for t_, p, v in pp_all), key=lambda v: v.mpv()), 'LB')
rec('tab:overview .50--1.03 high end', ln, '1.03', mx, 'LB')

# ------------------------------------------------------------------------------------------- column nets (rev 15.0)
section('sec:m3 column nets: thm:col, prop:colshift, cor:allmshift (rev 15.0; thm:E1 and its checks were removed)')
QC = [q for q in range(5, 200001) if q % 2 and q % 3]
for q in (5, 7, 11, 13, 37, 41, 101, 307, 1009):
    d2 = col_d2(q)
    assert d2.denominator == 1
    tau = q * q - q - 3 if q % 3 == 2 else q * q - 2 * q
    assert d2 == (Fr(q ** 4) - Fr(2, 3) * q ** 3 - Fr(5, 3) * q * q + 2 * q + 3 if q % 3 == 2 else
                  Fr(q ** 4) - Fr(4, 3) * q ** 3 + Fr(4, 3) * q * q)
mono = all(col_c(q).mpv() < col_c(q + 6).mpv() for q in QC[:4000])
rec_strict('thm:col(3): c(q) increases within each residue class mod 3', None, 'mono', mono,
           'q coprime to 6, q < 24000 (tau/q^2 = 1-1/q-3/q^2 resp. 1-2/q increasing)')
rec_snip('thm:col(3) c(5) = sqrt(513)/25', '$0.9059\\ldots$ at $q=5$', '0.9059', col_c(5), 'EXT')
rec_snip('thm:col(3) c(7) = sqrt(2009)/49', '$0.9147\\ldots$ at $q=7$', '0.9147', col_c(7), 'EXT')
rec_strict('thm:col(3) c(5) = 513/625 squared and c(7)^2 = 2009/2401', None, 'exact',
           col_d2(5) == 513 and col_d2(7) == 2009, '')
rec_snip('thm:col(3) "> 0.9059 for every such q" (rev 15.3: strict)', '$\\delta N^{1/3}>0.9059$ for every such $q$', '0.9059',
         col_c(5), 'LB')
rec_snip('thm:col(3) "> 0.9823 for q >= 37" (rev 15.3: strict)', '$\\delta N^{1/3}>0.9823$ for every such $q\\ge37$', '0.9823',
         col_c(37), 'LB')
rec_snip('proof thm:col(3): c(41) (least in the class q = 2, q >= 37)', 'with $0.9913\\ldots$', '0.9913', col_c(41), 'EXT')
rec_snip('proof thm:col(3): c(37)', 'it is $0.9823\\ldots$.', '0.9823', col_c(37), 'EXT')
rec_snip('intro bullet m = 3: > 0.9059', 'and $\\delta N^{1/3}>0.9059$ (Theorem~\\ref{thm:col})', '0.9059', col_c(5), 'LB')
rec_snip('sec:everym: m = 3, > 0.9059', 'gives $\\delta N^{1/3}>0.9059$, and Theorem', '0.9059', col_c(5), 'LB')
rec_snip('tab:overview thm:col > .9059', 'exact; $>.9059$', '.9059', col_c(5), 'LB')
rec_strict('thm:col(3): the constants are strict (c(5) > 0.9059, c(37) > 0.9823; rev 15.3, Lean S9)', None, '>',
           col_c(5).mpv() > mpf('0.9059') and col_c(37).mpv() > mpf('0.9823'), '')
mS = min(QC[:20000], key=lambda q: colshift_LB(q).mpv() if q >= 37 else 9)
rec_strict('prop:colshift(3): least value over q >= 37 at q = 37', None, '37', mS == 37, '')
for snip in ('which exceeds $0.4693$ for every $q\\ge37$', 'for every shift, $\\delta N^{1/3}>0.4693$',
             'gives the lower bound $0.4693>0.4250$'):
    rec_snip(f'prop:colshift / cor:allmshift: 0.4693 ({snip[:30]})', snip, '0.4693', colshift_LB(37), 'LB')
rec_snip('proof prop:colshift: 0.4693... at q = 37', 'least value is $0.4693\\ldots$ at $q=37$', '0.4693',
         colshift_LB(37), 'EXT')
rec_snip('proof prop:colshift: 0.5079... at q = 41', 'and $0.5079\\ldots$ at $q=41$', '0.5079', colshift_LB(41), 'EXT')
rec_strict('cor:allmshift: the two m=3 bounds lie within 7/(sqrt3 p) resp. 5/(sqrt3 p) of 1/sqrt3', None, 'interval',
           all(Fr(W + 3, 1) <= 7 and 3 + wm <= 5 for W, wm in ((2, 1), (4, 2))), 'W <= 4, w_max <= 2')
rec_strict('cor:dgs(5) shifts: p^2-(W+6)p+3 >= 0 for p >= 10 (W <= 4)', None, '10',
           all(q * q - 10 * q + 3 >= 0 for q in range(10, 10000)) and 9 * 9 - 90 + 3 < 0, '')
rec_strict('cor:dgs(5): p sqrt(2/3) >= sqrt3 for p >= 3/sqrt2', None, '3/sqrt2', 5 * 5 * 2 >= 9, '')
rec_snip('sec:twocoset: exact c(C_101)', 'exactly, $0.9966\\ldots$ at $p=101$', '0.9966', col_c(101), 'EXT')
rec_snip('sec:twocoset: exact c(C_307)', 'and $0.9978\\ldots$ at $p=307$', '0.9978', col_c(307), 'EXT')
rec_strict('rem:shiftshared: (1+(3+w_max)/p-3/p^2)/sqrt3 < c(C_p) for p >= 11', None, '11',
           all((1 + Fr(3 + (1 if q % 3 == 2 else 2), q) - Fr(3, q * q)) ** 2 / 3 < col_d2(q) / q ** 4 for q in QC
               if 11 <= q < 5000) and not ((1 + Fr(4, 5) - Fr(3, 25)) ** 2 / 3 < col_d2(5) / 625), 'and not at q = 5')
# ------------------------------------------------------------------------------------------- half-integer layers
section('sec:halfms: prop:half5 (the layer F_0^* and the net Q*_p, rev 15.0), rem:M5')
import half5_qstar as H5
stq, stm = H5.steps()
r2 = {pp: H5.lb_r2_sq(stq, pp)[0] for pp in (31, 37)}
rec_snip('prop:half5(2): LB_2(37)', 'the least value is $1.0127\\ldots$, at $p=37$', '1.0127', Root(2, Fr(r2[37], 37 ** 4)), 'EXT')
rec_snip('prop:half5(2): LB_2(31)', '$\\mathrm{LB}_2(31)=0.9918\\ldots$', '0.9918', Root(2, Fr(r2[31], 31 ** 4)), 'EXT')
rec_snip('prop:half5(2): tail LB_2*(200)^2', '$\\mathrm{LB}_2^*(200)^2=1.1877\\ldots>1$', '1.1877', Q(H5.tail_r2_sq(stq, 200)), 'EXT')
hk = {pp: H5.lb_hk_sq(stq, pp)[0] for pp in (47, 53)}
rec_snip('prop:half5(3): LB(47)', '$\\mathrm{LB}(47)=0.9906\\ldots$', '0.9906', Root(2, Fr(hk[47], 47 ** 2)), 'EXT')
rec_snip('prop:half5(3): LB(53)', '$\\mathrm{LB}(53)=1.0049\\ldots$', '1.0049', Root(2, Fr(hk[53], 53 ** 2)), 'EXT')
rec_snip('prop:half5(3): tail LB*(200)^2', '$\\mathrm{LB}^*(200)^2=1.1689\\ldots>1$', '1.1689', Q(H5.tail_hk_sq(stq, 200)), 'EXT')
hm = {pp: H5.lb_hk_sq(stm, pp)[0] for pp in (83, 89)}
rec_snip('rem:M5: LB(83)', '$\\mathrm{LB}(83)=0.9975\\ldots$', '0.9975', Root(2, Fr(hm[83], 83 ** 2)), 'EXT')
rec_snip('rem:M5: LB(89)', '$\\mathrm{LB}(89)=1.0056\\ldots$', '1.0056', Root(2, Fr(hm[89], 89 ** 2)), 'EXT')
HX = json.load(open(os.path.join(HERE, 'half5_exact.json')))['mind']
for pp, pv in ((31, '0.9928'), (37, '1.0134')):        # rev 15.2: truncated (rev 15.1 printed .9929, 1.0135 rounded)
    rec_snip(f'after prop:half5: exact c(Q*_{pp}) (computed)', f'${pv}$ at $p={pp}$', pv,
             Root(2, Fr(HX[str(pp)]['d2'], pp ** 8)), 'EX', note='half5_exact.json, half5_mind.cpp')
rec_snip('prop:half5(2): sqrt5/2', '$\\delta N^{1/5}\\to\\sqrt5/2=1.1180\\ldots$', '1.1180', Root(2, Fr(5, 4)), 'EXT')
rec_strict('prop:half5(2): Hk(3) with C = 3/2: sqrt5 (2C+1)/p = 4 sqrt5/p, p > 4sC+2 = 32', None, '32',
           4 * 5 * Fr(3, 2) + 2 == 32, '')
rec_strict('rem:accounting: 2/(5(1-2/sqrt5)) ~ 3.79; 3.79*(17/2+5) ~ 51, 3.79*17/2 ~ 32', None, '3.79',
           abs(2 / (5 * (1 - 2 / math.sqrt(5))) - 3.789) < 1e-3 and round(2 / (5 * (1 - 2 / math.sqrt(5))) * 13.5) == 51
           and round(2 / (5 * (1 - 2 / math.sqrt(5))) * 8.5) == 32, '')
# (rev 15.0: the checks of thm:E1 and of the layer M_5 of rev 14.3 were replaced by those above.)
section('certificates and exact values formerly not recomputed (rev 10.3)')




# ---- rev 10.3: coding-theory material (prop:S1E / tab:S1E, prop:s5r2 / tab:s5r2, intro, tab:overview)
section('codes: prop:S1E, tab:S1E, prop:s5r2, tab:s5r2 (rev 10.3)')
import s1e_certs as S1E
_C1 = {}
for r in S1E.certs():  # exact J2 = lambda_jit^2 by exact LLL + complete enumeration (codesaudit_e1.analyse)
    _C1[(r['src'], r['s'], r['p'])] = r['J2']


def c_s1e(src, s_, p_):
    """lambda_jit p^{-1/s} = (J2^s / p^2)^{1/(2s)} exactly."""
    J2 = _C1[(src, s_, p_)]
    return Root(2 * s_, Fr(J2 ** s_, p_ ** 2)), J2


_ROUNDKEY = {3: 'A3', 4: 'D4', 5: 'D5', 6: 'E6', 7: 'E7', 8: 'E8'}
_SQGAM = {3: Root(6, 2), 4: Root(4, 2), 5: Root(10, 8), 6: Root(12, Fr(64, 3)), 7: Root(14, 64), 8: Root(2, 2)}
_P1 = {}
for src, s_, p_ in _C1:
    if src.startswith('round:') and src.endswith(':1e6'):
        _P1[(s_, '1e6')] = p_
    if src.startswith('round:') and src.endswith(':1e10'):
        _P1[(s_, '1e10')] = p_
blk = table_block('tab:S1E')
for n_, l in blk:
    cells = row_cells(l)
    if len(cells) != 9 or not cells[0].strip().isdigit():
        continue
    s_ = int(cells[0])
    cols = [('search', 1009), ('search', 10007), ('search', 1000003), ('search', 100000007),
            ('round:%s:1e6' % _ROUNDKEY[s_], _P1[(s_, '1e6')]), ('round:%s:1e10' % _ROUNDKEY[s_], _P1[(s_, '1e10')])]
    for (src, p_), cell in zip(cols, cells[1:7]):
        v, J2 = c_s1e(src, s_, p_)
        rec(f'tab:S1E s={s_} {src} p={p_}', n_, clean(cell), v, 'LB', note=f'J2={J2} exact')
    rec(f'tab:S1E sqrt(gamma_{s_})', n_, clean(cells[7]), _SQGAM[s_], 'EX')
# primes p' listed in the caption = the primes of the witness files
_capl = [l for n_, l in blk if 'the primes are' in l]
_ok = bool(_capl) and all(str(_P1[(s_, e)]) in _capl[0] for s_ in range(3, 9) for e in ('1e6', '1e10'))
rec_strict("tab:S1E caption primes p' = witness primes", find_line('the primes are $p\'=996001$'), "p'", _ok,
           'all 12 primes of e1_rootlattice_rounding.txt (1e6, 1e10 rows) appear in the caption')
# the * cell: kappa_d = rho^d at (8, 10007) gives (rho-1) p^{-1/8}, rho = 3
_r = iroot(10007, 8)
rec('tab:S1E caption kappa=rho^d value at (8,10007)', find_line('which gives $.632$'), '.632',
    Root(8, Fr((_r - 1) ** 8, 10007)), 'LB', note='rho = %d' % _r)
_v7 = c_s1e('round:E7:1e10', 7, 10660100951)[0]
rec_snip('tab:overview prop:S1E up to 1.238 (s=7)', 'up to $1.238$ ($s=7$) & Lean', '1.238', _v7, 'LB')
_mxS1E = max((c_s1e(*k)[0] for k in _C1), key=lambda v: v.mpv())
rec_strict('tab:overview "up to 1.238 (s=7)" is the largest tab:S1E entry', find_line('up to $1.238$ ($s=7$) & Lean'),
           '1.238', _mxS1E.mpv() == _v7.mpv(), mpmath.nstr(_mxS1E.mpv(), 10))
rec_snip('rem:S1Elim sqrt(gamma_s) list', '$1.122$, $1.189$, $1.231$, $1.290$, $1.345$, $\\sqrt2$ for $s=3,\\dots,8$',
         '1.122', _SQGAM[3], 'EX')
for _s, _pv in zip((4, 5, 6, 7), ('1.189', '1.231', '1.290', '1.345')):
    rec_snip(f'rem:S1Elim sqrt(gamma_{_s})', '$1.122$, $1.189$, $1.231$, $1.290$, $1.345$, $\\sqrt2$', _pv, _SQGAM[_s], 'EX')
# rev 15.2: the same constants and the ratios of D_s^+ to them in sec:halfms (not checked before; .91, .95 and 1.346
# were rounded)
_SNIP_HM = 'normalized minima $1.189$, $1.231$, $1.290$, $1.345$, and $D_s^+$ reaches the fractions $.84$, $.90$, $.94$, $.98$'
for _s, _pv, _pr in zip((4, 5, 6, 7), ('1.189', '1.231', '1.290', '1.345'), ('.84', '.90', '.94', '.98')):
    rec_snip(f'sec:halfms sqrt(gamma_{_s})', _SNIP_HM, _pv, _SQGAM[_s], 'EX')
    rec_snip(f'sec:halfms D_{_s}^+ / sqrt(gamma_{_s})', _SNIP_HM, _pr,
             MP(lambda s_=_s: min(mpmath.sqrt(2), mpmath.sqrt(s_) / 2) / _SQGAM[s_].mpv()), 'EX')

# (rev 14.1: prop:s5r2 / tab:s5r2 (codesaudit_e2cert.cpp, e2_s5r2_frameorbit_designs.txt) and the tab:overview range
# .54--.89 were retired: no longer in the paper.)

# ------------------------------------------------------------------------------------------- prop:twocoset (rev 11.4)
section('Proposition prop:twocoset (two-coset nets T_p, m = 3)')


def tc_LB(p):  # prop:twocoset(2): sqrt(33/32 - 41/(16p)) - sqrt3/p
    return MP(lambda: mpmath.sqrt(mpf(33) / 32 - mpf(41) / (16 * p)) - mpmath.sqrt(3) / p)


def tc_dstar2(p):  # prop:twocoset(3): the pair of cells 0 and (p-1)1, integer scale p^3
    r = (p + 4) // 8                                   # nearest integer to p/8 (p odd)
    assert abs(8 * r - p) <= 3
    return (p * p - 2 * p + 3) ** 2 + ((r - 1) * p + 4) ** 2 + ((r - 1) * p + 6) ** 2


TCW = json.load(open(os.path.join(HERE, 'twocoset_exact.json')))
for ps_, rc_ in TCW['twocoset'].items():
    assert rc_['d2'] == tc_dstar2(int(ps_)), ps_      # oracle minimum = pair value at every listed prime
R66 = Root(2, Fr(66, 64))
rec_snip('prop:twocoset(2) 3.014 (UB on 41/32+sqrt3)', 'exceeds $\\sqrt{66}/8-3.014/p$ for $p\\ge83$', '3.014',
         MP(lambda: mpf(41) / 32 + mpmath.sqrt(3)), 'UB')
rec_strict('prop:twocoset(2) LB(p) > sqrt66/8 - 3.014/p for p >= 83 (numerical cross-check)',
           find_line('exceeds $\\sqrt{66}/8-3.014/p$ for $p\\ge83$'), '83',
           all(tc_LB(p).mpv() > R66.mpv() - mpf('3.014') / p for p in PR if 83 <= p < 200000),
           'all primes 83..2e5 (mpmath); the proof (sqrt(1-x) >= 1-x, 41/32+sqrt3 < 3.014) was printed in earlier revisions')
ln = find_line('and it exceeds $1$ for $p\\ge197$')
mono = all(tc_LB(p).mpv() < tc_LB(q).mpv() for p, q in zip(PR[:-1], PR[1:]) if p >= 41 and q < 5000)
rec_strict('prop:twocoset(2) "exceeds 1 for p>=197"', ln, '197', tc_LB(197).gt(1) and not tc_LB(193).gt(1) and mono,
           'LB(197) > 1 > LB(193); LB increasing in p (checked on primes 41..5000; both terms increase)')
for loc, snip in (('prop:twocoset(3) sqrt66/8', '\\to\\sqrt{66}/8=1.0155\\ldots$ as $p\\to\\infty$'),
                  ('sec:dim3 sqrt66/8', 'with the limit $\\sqrt{66}/8=1.0155\\ldots$'),
                  ('sec:wnet sqrt66/8', 'below $\\sqrt{66}/8=1.01550\\ldots$ at $p=89$')):
    rec_snip(loc, snip, '1.01550' if 'sec:wnet' in loc else '1.0155', R66, 'EXT')
rec_snip('tab:overview prop:twocoset sqrt66/8', '\\to\\frac{\\sqrt{66}}8=1.0155$', '1.0155', R66, 'EX')
_tcv = {101: '0.9949', 1009: '1.0132'}     # rev 14.1: only the two ends of the range are printed
_tcp = sorted(int(x) for x in TCW['twocoset'])
rec_strict('sec:twocoset "at eight primes 101<=p<=1009 the exact minimum is attained by the pair of (3)"',
           find_line('At eight primes $101\\le p\\le1009$'), '8', len(_tcp) == 8 and _tcp[0] == 101 and _tcp[-1] == 1009,
           f'twocoset_exact.json primes {_tcp} (d2 = pair value asserted above; rerun by twocoset.py)')
for p_, pv_ in _tcv.items():
    rec_snip(f'sec:twocoset exact c(T_{p_}) (oracle = pair)', f'{pv_}\\ldots$', pv_,
             Root(2, Fr(tc_dstar2(p_), p_ ** 4)), 'EXT', note='twocoset_exact.json, cellmin.cpp')
# (rev 14.1: the limit-range values 2.12/2.31 and the numerical estimates of the proof of prop:twocoset were retired:
# the proof is no longer printed.)
ub_ok = all(Root(2, Fr(tc_dstar2(p), p ** 4)).mpv() < R66.mpv() - mpf(2) / p for p in PR if 53 <= p < 200000)
rec_strict('prop:twocoset(3) d_*/p^2 < sqrt66/8 - 2/p (numerical cross-check)', find_line('$d_*/p^2<\\sqrt{66}/8-2/p$ for $p\\ge53$'),
           '53', ub_ok, 'all primes 53..2e5 (mpmath)')
ln = find_line('every point is within $0.01$', CAPS)
rec_info('arc_captions fig:arctwocoset "within 0.01"', ln,
         'rounded UP (up2) from the measured deviation in figs_arc.py (asserted there: 0.0069)')

# ------------------------------------------------------------------------------------------- sec:whylat (rev 12.0)
section('Section sec:whylat (rem:glue, prop:cube, rem:cubecost; rev 13.0: the 2D/hexagonal values and the '
        'rem:open (11) values were cut)')
rec_snip('rem:glue 1/sqrt3', '$1/\\sqrt3=.5773\\ldots$', '.5773', Root(2, Fr(1, 3)), 'EXT')
rec_snip('rem:cubecost 3D one-per-cube max sqrt(29/25) (exact, e=10)', '$\\sqrt{29/25}=1.0770\\ldots$', '1.0770',
         Root(2, Fr(29, 25)), 'EXT', note='cubecost.py (whylat_cube.cpp, whylat_check.py)')
rec_snip('rem:cubecost lower bound 1.0770 for the largest minimum', 'lies between $1.0770$ and $2^{1/6}', '1.0770',
         Root(2, Fr(29, 25)), 'LB')
rec_snip('rem:cubecost FCC 2^(1/6)', '$2^{1/6}=1.1224\\ldots$', '1.1224', Root(6, Fr(2)), 'EXT')

# ------------------------------------------------------------------------------------------- rev 14.1 additions
section('rev 14.1: Part I closed forms (thm:main for q>=8, prop:D / prop:Dprime thresholds, mesh ratio, thm:base23)')
# thm:main: c(q) = 1 - 1/q exactly for q >= 8 (intro, tab:overview, after thm:main); not for q = 7
_d1 = lambda q: (1 - Fr(2, q)) ** 2 + (1 - Fr(4, q)) ** 2 - (1 - Fr(1, q)) ** 2     # = 1 - 10/q + 19/q^2
_d2 = lambda q: 3 * (1 - Fr(3, q)) ** 2 - (1 - Fr(1, q)) ** 2                         # = 2 - 16/q + 26/q^2
rec_strict('thm:main "c(q) = 1-1/q for all q >= 8" (and not at q = 7)', find_line('$c(q)=1-1/q$ for all $q\\ge8$'),
           '8', all(_d1(q) >= 0 and _d2(q) >= 0 for q in range(8, 10001)) and min(_d1(7), _d2(7)) < 0,
           'exact for 8 <= q <= 10^4; q^2 d1 = q^2 - 10q + 19 has roots 5 +- sqrt6 < 8 and q^2 d2 = 2q^2 - 16q + 26 has '
           'roots 4 +- sqrt3 < 8, so both stay >= 0 beyond')
for snip in ('$\\delta N^{1/3}\\ge1-1/q$ for $q\\ge8$', '$1-1/q$ ($q\\ge8$)'):
    find_line(snip)
# prop:Dprime for a dominant design (K = a, S <= 2a): Q_D <= ceil(((2sqrt2-1)a+sqrt2)/(sqrt2-1)) = ceil((3+sqrt2)a + 2+sqrt2) < 5a+4
ln = find_line('$q_{\\mathrm{tail}}\\le\\lceil((2\\sqrt2-1)a+\\sqrt2)/(\\sqrt2-1)\\rceil<5a+4$ for $a\\ge1$')
def _qd(K, S):
    x = S + 1 - K
    c = math.isqrt(2 * x * x)
    c += c * c < 2 * x * x
    return max(S + 1, 2 * (S + 1) - K + c)                   # ceil((sqrt2 (S+1) - K)/(sqrt2-1)) = 2(S+1)-K+ceil(sqrt2(S+1-K))
_r2 = mpmath.sqrt(2)
_X = lambda a: ((2 * _r2 - 1) * a + _r2) / (_r2 - 1)        # = (3+sqrt2)a + 2+sqrt2
rec_strict('after prop:Dprime: dominant designs (K = a, S <= 2a) have Q_D < 5a+4', ln, '5a+4',
           all(_qd(a, 2 * a) <= math.ceil(x) and x < 5 * a + 4 and _qd(a, 2 * a) < 5 * a + 4
               for a, x in ((a, _X(a)) for a in range(1, 3001))),
           'exact ceil, a = 1..3000, S = 2a (Q_D is nondecreasing in S); (3+sqrt2 < 5, 2+sqrt2 < 4)')
# prop:linf remark: l_inf mesh ratio 2q/(q-2a-1) < 10/3 for q >= 5a+4 (Theorem A(2))
ln = find_line('in particular below $10/3$ for the nets of Theorem~\\ref{thm:A}(2)')
rec_strict('after prop:linf: 2q/(q-2a-1) < 10/3 for every q >= 5a+4', ln, '10/3',
           all(Fr(2 * q, q - 2 * a - 1) < Fr(10, 3) for a in range(1, 200) for q in (5 * a + 4, 5 * a + 5, 10 * a)),
           'decreasing in q; at q = 5a+4 it is 2(5a+4)/(3a+3) = 10/3 - 2/(3a+3)')
# thm:base23: the constants of (1), (2) are the minima of the columns of tab:base23 per base; intro and tab:overview
blk = table_block('tab:base23')
_b23 = {}
for n_, l in blk:
    c = row_cells(l)
    if len(c) == 7 and c[0].strip() in ('2', '3'):        # rev 15.7: column (3) every shift added
        _b23.setdefault(int(c[0]), []).append((clean(c[4]), clean(c[5]), clean(c[6])))
_mins = {b: tuple(min(r[i] for r in v) for i in range(3)) for b, v in _b23.items()}
ln = find_line('\\label{thm:base23}')
rec_strict('thm:base23 (1)/(2)/(3) = column minima of tab:base23', ln, '6 consts',
           _mins == {2: ('.4129', '.1718', '.1718'), 3: ('.3538', '.0770', '.0770')}
           and count('\\ge0.1718$ for $b=2$ and $\\ge0.0770$ for $b=3$') == 2
           and find_line('\\ge0.4129$ for $b=2$ and $\\ge0.3538$ for $b=3$') is not None
           and find_line('\\ge0.1718$ for $b=2$ and $\\ge0.0770$ for $b=3$') is not None,
           f'table minima {_mins} (the table values themselves are computer-assisted certificates, not recomputed here)')
rec_strict('intro / tab:overview reprint the thm:base23 constants', find_line('$\\delta N^{1/3}\\ge0.4129$ resp.\\ $0.3538$'),
           '4 consts', find_line('$\\ge0.1718$ resp.\\ $0.0770$ without a shift') is not None
           and find_line('& $.4129$, $.3538$ (explicit shift) &') is not None
           and find_line('$.1718$, $.0770$ (every shift)') is not None, '')

# ------------------------------------------------------------------------------------------- prop:wnet (rev 15.1)
section('Proposition prop:wnet (rank-one nets W_p, m = 3; the bounds; wnet.py checks the tables and exact values)')


def w_LB(p):  # prop:wnet(2): sqrt(281/256 - 345/(128p)) - sqrt3/p
    return MP(lambda: mpmath.sqrt(mpf(281) / 256 - mpf(345) / (128 * p)) - mpmath.sqrt(3) / p)


R281 = Root(2, Fr(281, 256))
for loc, snip in (('prop:wnet(3) sqrt281/16', '\\to\\sqrt{281}/16=1.0476\\ldots$ as $p\\to\\infty$'),
                  ('intro sqrt281/16', '$\\delta N^{1/3}\\to\\sqrt{281}/16=1.0476\\ldots$ (Proposition'),
                  ('after cor:allm sqrt281/16', 'the limit $\\sqrt{281}/16=1.0476\\ldots$ (Proposition'),
                  ('rem:cubecost sqrt281/16', 'value at $m=3$ in this paper is $\\sqrt{281}/16=1.0476\\ldots$')):
    rec_snip(loc, snip, '1.0476', R281, 'EXT')
rec_snip('tab:overview prop:wnet sqrt281/16', '\\to\\frac{\\sqrt{281}}{16}=1.0476$', '1.0476', R281, 'EX')
rec_snip('prop:wnet(2) bound at p=67', 'it is $1.0024\\ldots$ at $p=67$', '1.0024', w_LB(67), 'LB')
rec_snip('prop:wnet(2) bound at p=97', '$1.0164\\ldots$ at $p=97$', '1.0164', w_LB(97), 'LB')
monoW = all(w_LB(p).mpv() < w_LB(q).mpv() for p, q in zip(PR[:-1], PR[1:]) if p >= 53 and q < 5000)
rec_strict('prop:wnet(2) "exceeds 1 for p>=67 and sqrt66/8 for p>=97"', find_line('it exceeds $1$ for $p\\ge67$ and'),
           '67/97', w_LB(67).gt(1) and not w_LB(61).gt(1) and w_LB(97).mpv() > R66.mpv() > w_LB(89).mpv() and monoW,
           'LB(67) > 1 > LB(61); LB(97) > sqrt66/8 > LB(89); LB increasing (primes 53..5000; both terms increase)')
ln = find_line('$d_*/p^2<\\sqrt{281}/16+5/(2p)$')
rec_strict('prop:wnet(3) d_*/p^2 < sqrt281/16 + 5/(2p) (numerical cross-check)', ln, '5/2',
           all(MP(lambda p=p: mpmath.sqrt(mpf((p * p - (6 * (p // 48) + 2) * p - 2) ** 2 + ((6 * (p // 48) + 3) * p) ** 2
                                             + (((p - 1) // 2 + 3 * (p // 48) + 2) * p) ** 2)) / p ** 2).mpv()
               < R281.mpv() + mpf(5) / (2 * p) for p in PR if 53 <= p < 20000), 'all primes 53..2e4 (mpmath)')
rec_snip('prop:wnet(3) proof 3.05', '<\\frac{281}{256}+\\frac{3.05}p$', '3.05',
         MP(lambda: mpf(345) / 128 + mpf(4761) / (256 * 53)), 'UB')
rec_snip('prop:wnet(3) proof 2.46', '<\\sqrt{281}/16+2.46/p$', '2.46',
         MP(lambda: 1 + mpf('3.05') / (2 * mpmath.sqrt(mpf(281) / 256))), 'UB')
rec_strict('prop:wnet(2) proof (1-9sqrt6/100)|A|-9/50 > 1.05 for |A|^2 >= 3', find_line('\\frac9{50}>1.05$'), '1.05',
           (1 - 9 * mpmath.sqrt(6) / 100) * mpmath.sqrt(3) - mpf(9) / 50 > mpf('1.05'), 'a deliberately rounded constant')
rec_strict('prop:wnet(2) proof 1.05^2 > 281/256 and 19/636 < 3/100', find_line('$1.05^2>\\frac{281}{256}$'), 'ok',
           Fr(105, 100) ** 2 > Fr(281, 256) and Fr(19, 636) < Fr(3, 100) and Fr(1, 48) + Fr(23, 48 * 53) == Fr(19, 636), '')
EPSS = MP(lambda: (13 - 2 * mpmath.sqrt(31)) / 90)
rec_snip('sec:wnet eps* = (13-2sqrt31)/90', '$\\varepsilon^*=(13-2\\sqrt{31})/90=0.02071\\ldots$', '0.02071', EPSS, 'EXT')
MUS = MP(lambda: mpmath.sqrt((72 - 8 * mpmath.sqrt(31)) / 25))
for loc, snip in (('sec:wnet balance mu*', '$\\mu^*=\\sqrt{(72-8\\sqrt{31})/25}=1.0480\\ldots$; on'),
                  ('intro mu*', '$\\mu^*=\\sqrt{(72-8\\sqrt{31})/25}=1.0480\\ldots$, reached'),
                  ('rem:open(7) mu*', '$\\mu^*=1.0480\\ldots$ (Remark~\\ref{rem:wstar})')):
    rec_snip(loc, snip, '1.0480', MUS, 'EXT')
rec_snip('tab:overview prop:wfamily mu*', '\\to\\mu^*=1.0480$', '1.0480', MUS, 'EX')
rec_snip('rem:wstar K = (9sqrt31-36)/5', '\\frac{9\\sqrt{31}-36}5=2.8219\\ldots', '2.8219',
         MP(lambda: (9 * mpmath.sqrt(31) - 36) / 5), 'EXT')
rec_snip('proof prop:wfamily 246/225', '$\\frac{246}{225}=1.0933\\ldots$', '1.0933', Q(Fr(246, 225)), 'EXT')
rec_snip('proof prop:wfamily mu*^2', '$\\mu^{*2}=1.0983\\ldots$', '1.0983', MP(lambda: (72 - 8 * mpmath.sqrt(31)) / 25), 'EXT')
for v_, f_ in (('1.1081', Fr(11081, 10000)), ('1.1681', Fr(11681, 10000)), ('1.5524', Fr(15524, 10000))):
    rec_snip(f'proof prop:wfamily(2) rows at 3/100: {v_}', 'to $1.1081$, $1.1681$ and $1.5524$', v_, Q(f_), 'EX')
rec_snip('proof prop:wfamily(2) 1.05^2 = 1.1025', '$1.05^2=1.1025$', '1.1025', Q(Fr(11025, 10000)), 'EX')
rec_strict('rem:wstar mu*^2 - 281/256 < 7e-4', find_line('$\\mu^{*2}-\\frac{281}{256}<7\\cdot10^{-4}$'), '7e-4',
           (72 - 8 * mpmath.sqrt(31)) / 25 - mpf(281) / 256 < mpf(7) / 10000, 'upper bound (6.59e-4)')
rec_snip('sec:wnet 1/48', '$\\varepsilon=\\frac1{48}=0.02083\\ldots$', '0.02083', MP(lambda: mpf(1) / 48), 'EXT')
# rev 15.2: "about 0.03 %" (the relative gap is 0.03001 %, a hair above 0.03 %: "within" was wrong); truncated
_gap = 100 * (1 - R281.mpv() / mpmath.sqrt((72 - 8 * mpmath.sqrt(31)) / 25))
rec_strict('sec:wnet "0.030 %" below mu* (rev 15.3: truncated to three digits)', find_line('$0.030\\,\\%$ below $\\mu^*$'),
           '0.030 %', int(mpmath.floor(_gap * 1000)) == 30, f'relative gap {mpmath.nstr(_gap, 6)} %')
rec_snip('sec:wnet sqrt233/15 (model)', '$\\sqrt{233}/15=1.0176\\ldots$', '1.0176', Root(2, Fr(233, 225)), 'EXT')
# rev 15.4/15.5: rem:gk2d(iii), the re-scrambled two-dimensional GK nets, tiling metric (computed; gk2d_rescramble.py)
rec_snip('rem:gk2d(iii) sqrt977/32', '$\\delta\\sqrt N=0.9767\\ldots$ against $0.9702\\ldots$', '0.9767',
         Root(2, Fr(977, 1024)), 'EXT')
rec_snip('rem:gk2d(iii) sqrt241/16', '$\\delta\\sqrt N=0.9767\\ldots$ against $0.9702\\ldots$', '0.9702',
         Root(2, Fr(241, 256)), 'EXT')

# ------------------------------------------------------------------------------------------- figures
section('figures: figs/arc_captions.tex (generated by figs_arc.py) and in-figure labels')
mgk = re.search(r'\(1-\\frac1Q\)=([0-9.]+)\$', '\n'.join(TEX[CAPS]))
ln = find_line(mgk.group(0), CAPS)
rec('arc_captions.tex fig:arcgk caption (4/sqrt17)(1-1/Q)', ln, mgk.group(1), Root(2, Fr(16 * 225, 17 * 256)), 'LB',
    old=mgk.group(0), note='line in figs/arc_captions.tex (generated); Q=16. Same number in the panel-(b) title of '
                           'arc_gk2d.pdf')
FA_SRC = open(os.path.join(HERE, 'figs_arc.py')).read()
lam = mpmath.sqrt(65) / 9
lab_v = float(lam - mpmath.sqrt(2) / 9)
lab_pr = ('%.3f' % (math.floor(lab_v * 1000 + 1e-12) / 1000)) if 'ffloor(lam - np.sqrt(2) / q)' in FA_SRC \
    else '%.3f' % lab_v
rec('arc_anatomy.pdf panel (b) label lambda_1-sqrt2/q (q=9)', None, lab_pr, MP(lambda: lam - mpmath.sqrt(2) / 9),
    'LB', note='in-figure text of arc_anatomy.pdf; printed value = what the current figs_arc.py source prints')
_CAPTXT = '\n'.join(TEX[CAPS])


def cap_val(rx, what):
    """(printed value, line) of a number in figs/arc_captions.tex, read at run time (rev 15.2: not hard-coded)"""
    m_ = re.search(rx, _CAPTXT)
    if not m_:
        rec_cannot(what, None, '?', 'pattern not found in arc_captions.tex: ' + rx)
        return None, None
    return m_.group(1), find_line(m_.group(0), CAPS)


_pv, ln = cap_val(r'minimum \$\\lambda_1=([0-9.]+)\$', 'fig:arc lambda_1')
if _pv:
    rec('arc_captions fig:arc lambda_1 = sqrt65/9 (exact)', ln, _pv, Root(2, Fr(65, 81)), 'EX')
_pv, ln = cap_val(r'\$\\lambda_1\(\\Lambda_q\)=([0-9.]+)\$', 'fig:arcsmall lambda_1')
if _pv:
    rec('arc_captions fig:arcsmall lambda_1 (q=11)', ln, _pv, Root(2, 1 - Fr(2, 11) + Fr(3, 121)), 'EX')
_pv, ln = cap_val(r'\$\\det\(I\+\\frac Mq\)=([0-9.]+)\\approx', 'fig:arcsmall det')
if _pv:
    rec('arc_captions fig:arcsmall det(I+M/q) (q=11)', ln, _pv, Q(Fr(10, 11) * (Fr(100, 121) + Fr(3, 121))), 'EX')
_pv, ln = cap_val(r'\(\$\\lambda_1=([0-9.]+)\$\)\. Despite', 'fig:arcsmall(b) lambda_1')
if _pv:
    rec('arc_captions fig:arcsmall(b) lambda_1 of (I+F_0/q)Z^4 (q=17; column e_inf: (15/17)^2+3/17^2)', ln, _pv,
        Root(2, Fr(228, 289)), 'EX')
# rev 15.2: the in-figure label lambda_1 of arc_anatomy.pdf (q = 9) is an exact value: truncated, not '%.3f'
_lam_pr = ('%.3f' % (math.floor(float(lam) * 1000) / 1000)) if "r'$\\lambda_1=%s$' % ftr(lam, 3)" in FA_SRC \
    else '%.3f' % float(lam)
rec('arc_anatomy.pdf panel (b) label lambda_1 = sqrt65/9', None, _lam_pr, Root(2, Fr(65, 81)), 'EX',
    note='in-figure text; printed value = what the current figs_arc.py source prints')

# ------------------------------------------------------------------------------------------- summary
print('\n' + '=' * 110)
print('COUNTS:', ', '.join(f'{k} {v}' for k, v in sorted(COUNTS.items())))
print('\nCHANGES: (location | core.tex line (or file) | old -> new)')
for i, (loc, line, old, new, note) in enumerate(CHANGES, 1):
    print(f"[{i:2d}] {loc} | line {line}" + (f" | {note}" if note else ''))
    print(f"      OLD: {old}")
    print(f"      NEW: {new}")
print(f'\n{len(CHANGES)} change entries')
print('\nCANNOT-RECOMPUTE:')
for loc, line, pv, why in CANNOT:
    print(f'  - {loc} (line {line}) [{pv}]: {why}')
print('\nfigs_arc.py: format strings that print LOWER bounds (must use a floor formatter, not %.3f):')
for i, l in enumerate(FA_SRC.split('\n'), 1):
    if ('lam - np.sqrt(2) / q' in l and ('%.3f' in l or 'ffloor' in l or '%s' in l)) \
            or 'frac{1}{Q})=%' in l or 'frac1Q)=%' in l or "ffloor(bound)" in l or "% bound" in l \
            or "G['bound']" in l or l.startswith('def ffloor'):
        print(f'  figs_arc.py:{i}: {l.strip()[:160]}')
print('\ntotal %.1f s' % (time.time() - T0))
BAD_STATUS = ('ROUNDED-UP', 'UB-NOT-ROUNDED-UP', 'EXACT-MISROUNDED', 'ELLIPSIS-WRONG', 'STRICT-FAILS', 'AMBIGUOUS', 'SNIPPET-MISSING')
_bad = {k: v for k, v in COUNTS.items() if k in BAD_STATUS}
if CHANGES or CANNOT or _bad:
    print(f'truncate_bounds: FAILED ({len(CHANGES)} change entries, {len(CANNOT)} cannot-recompute, {_bad})')
    sys.exit(1)
print('truncate_bounds: every recomputed printed bound agrees with its convention (0 change entries)')

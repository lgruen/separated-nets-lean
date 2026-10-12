#!/usr/bin/env python3
"""half5_exact.py -- exact minimum distances of Q*_p, Theorem D's enumeration, and the data of the s = 5 figure.

  (1) exact toroidal minimum distance of Q*_p (one resolution, N = p^5) by the pruned exact kernel half5_mind.cpp,
      for every prime 7 <= p <= 61: d2 (units p^-10), c = sqrt(d2)/p^4, argmin cell step E.  Asserted: recomputed
      d2 == stored d2 in half5_exact.json; d2(7), d2(11), d2(13) equal the values that `algs_mind2.cpp` (research repository) gives
      (1720717, 121318230, 542292439; audit cross-check); c(31) < 1 < c(37) by the exact integer test d2 vs p^8;
      the 6-digit roundings for 7 <= p <= 47 equal the audited values (the research notes).
  (2) Theorem D's computer-assisted part: runs half5_thmD (which asserts its own counts; exit status 0 iff OK).
  (3) figure data ("curves"), every prime 7 <= p <= 211, exact (the stored 'sq' is the exact integer sum of squares
      at scale 'scale', i.e. LB = min(2, sqrt(sq/scale))):
        r2   : LB_R2(p) of Q* (Lemma R2) for p >= 29 where its hypotheses hold ('hyp': true); for p < 29 the
               residue-reduced, hypothesis-free variant (both residues reduced mod p; equal to LB_R2 wherever the
               hypotheses hold, which is asserted at every p >= 29), flagged 'hyp': false;
        hkF  : LB_Hk(p) of F0* (prop:Hk(1), k = 1, blanket jitter), p >= 23 (hypothesis p > max|2F0* E| = 22);
        hkM  : LB_Hk(p) of M5 (prop:half5), p >= 29 (hypothesis p > max|2M5 E| = 26).
      Each recomputed value must equal the stored one.
What is covered: (1) is an exact finite computation for the listed primes only; (2) is complete for the finite
families described in half5_thmD.cpp; (3) are exact evaluations of the relaxations at the listed primes.

    g++ -O3 -std=c++17 -o scripts/bin/half5_mind scripts/half5_mind.cpp
    g++ -O3 -std=c++17 -o scripts/bin/half5_thmD scripts/half5_thmD.cpp
    uv run python scripts/half5_exact.py            (~6 s on 10 cores; recomputes everything and compares)
    uv run python scripts/half5_exact.py --quick    (min distance only at p = 7, 13, 31, 37; stored rest checked)
    uv run python scripts/half5_exact.py --write    (recompute and (re)write half5_exact.json)
Exit status 0 iff everything agrees; last line 'half5_exact: ALL OK'.
"""
import json
import os
import subprocess
import sys
import time
from math import isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from half5_qstar import (HQ, D1Q, D2Q, D3Q, HM, D1M, Steps, gens_mod, lb_r2_sq, lb_hk_sq, primes_in, trunc,  # noqa
                         canon_sign)

MIND = os.path.join(HERE, 'bin', 'half5_mind')
THMD = os.path.join(HERE, 'bin', 'half5_thmD')
JSON = os.path.join(HERE, 'half5_exact.json')
MIND_PRIMES = primes_in(7, 62)
QUICK_PRIMES = (7, 13, 31, 37)
CURVE_PRIMES = primes_in(7, 212)
ALGS_MIND2 = {7: 1720717, 11: 121318230, 13: 542292439}
AUDIT_C = {7: '0.546339', 11: '0.752302', 13: '0.815349', 17: '0.887360', 19: '0.912036', 23: '0.948460',
           29: '0.984107', 31: '0.992890', 37: '1.013479', 41: '1.023821', 43: '1.028262', 47: '1.035999'}
FAILS = []


def check(ok, msg):
    print(('  OK    ' if ok else '  FAIL  ') + msg, flush=True)
    if not ok:
        FAILS.append(msg)
    return ok


def rounded6(d2, p):
    """sqrt(d2)/p^4 rounded half-up to 6 digits, exactly"""
    f = isqrt(d2 * 10 ** 14 // p ** 8)          # floor of 10^7 * c (floor of floor is floor)
    r = (f + 5) // 10
    return f'{r // 10 ** 6}.{r % 10 ** 6:06d}'


def mind(p):
    G = gens_mod(HQ, (D1Q, D2Q, D3Q), p)
    inp = f'{p} 5 5\n' + '\n'.join(' '.join(str(x) for r in G[c] for x in r) for c in range(5)) + '\n'
    t = time.time()
    out = subprocess.run([MIND], input=inp, capture_output=True, text=True, check=True).stdout.strip()
    el = time.time() - t
    kv = dict(tok.split('=', 1) for tok in out.split() if '=' in tok)
    E = tuple(int(x) for x in kv['argE'].strip('()').split(','))
    return {'d2': int(kv['d2']), 'c': isqrt(int(kv['d2']) * 10 ** 24 // p ** 8) / 1e12,
            'c_trunc6': trunc(int(kv['d2']), p ** 8), 'argE': list(E)}, el, out


def curve_entry(sq, scale):
    return {'sq': sq, 'scale': scale, 'val': min(2.0, isqrt(sq * 10 ** 24 // scale) / 1e12),
            'trunc6': trunc(sq, scale)}


def curves():
    stq, stm = Steps(HQ, D1Q), Steps(HM, D1M)
    assert stq.maxh == 22 and stq.maxv == 24 and stm.maxh == 26
    r2, hkF, hkM = {}, {}, {}
    for p in CURVE_PRIMES:
        hyp = p > stq.maxh and p > stq.maxv
        sq_free = lb_r2_sq(stq, p, free=True)[0]
        if hyp:
            sq = lb_r2_sq(stq, p)[0]
            if sq != sq_free:
                FAILS.append(f'residue-reduced bound differs from LB_R2 at p = {p}')
        r2[str(p)] = dict(curve_entry(sq_free, p ** 4), hyp=hyp)
        if p > stq.maxh:
            hkF[str(p)] = curve_entry(lb_hk_sq(stq, p)[0], p ** 2)
        if p > stm.maxh:
            hkM[str(p)] = curve_entry(lb_hk_sq(stm, p)[0], p ** 2)
    return {'r2': r2, 'hkF': hkF, 'hkM': hkM}


def main():
    write = '--write' in sys.argv
    quick = '--quick' in sys.argv and not write
    for b in (MIND, THMD):
        if not os.path.exists(b):
            print(f'missing binary {b}; build with g++ -O3 -std=c++17 -o {b} {os.path.join(HERE, os.path.basename(b))}.cpp')
            sys.exit(1)
    stored = None if write else json.load(open(JSON))
    T0 = time.time()

    print('(1) exact minimum distance of Q*_p (half5_mind)')
    res = {}
    for p in MIND_PRIMES:
        if quick and p not in QUICK_PRIMES:
            res[p] = dict(stored['mind'][str(p)])
            print(f'        p={p:2d}  d2={res[p]["d2"]}  (stored, not recomputed: --quick)')
            continue
        r, el, raw = mind(p)
        res[p] = r
        same = write or r['d2'] == stored['mind'][str(p)]['d2']
        check(same, f'p={p:2d}  d2={r["d2"]:<17d} c={r["c_trunc6"]}...  argE=+-{tuple(canon_sign(r["argE"]))}  '
                    f'{"" if write else "== stored"}  ({el:.2f} s)')
    for p, d2 in ALGS_MIND2.items():
        check(res[p]['d2'] == d2, f'p={p}: d2 = {res[p]["d2"]} equals the algs_mind2 value {d2}')
    check(all(rounded6(res[p]['d2'], p) == c for p, c in AUDIT_C.items()),
          'c(Q*_p) rounded to 6 digits equals the audited values at every prime 7 <= p <= 47')
    check(res[31]['d2'] < 31 ** 8 < 37 ** 8 and res[37]['d2'] > 37 ** 8,
          f'exact: c(31) = {res[31]["c_trunc6"]}... < 1 < c(37) = {res[37]["c_trunc6"]}...')
    above = [p for p in MIND_PRIMES if res[p]['d2'] > p ** 8]
    check(above == [p for p in MIND_PRIMES if p >= 37], f'c(Q*_p) > 1 exactly for the computed primes {above}')
    check(all(tuple(canon_sign(res[p]['argE'])) == (1, 1, 0, 0, -1) for p in MIND_PRIMES if p >= 17),
          'argmin step +-(1,1,0,0,-1) for every computed p >= 17')

    print('(2) Theorem D (half5_thmD)')
    t = time.time()
    pr = subprocess.run([THMD], capture_output=True, text=True)
    for line in pr.stdout.strip().splitlines():
        print('        ' + line)
    check(pr.returncode == 0 and pr.stdout.strip().endswith('half5_thmD: ALL OK'),
          f'half5_thmD exit status {pr.returncode} ({time.time() - t:.2f} s)')

    print('(3) figure data: LB_R2 (Q*), LB_Hk (F0*), LB_Hk (M5) at every prime 7 <= p <= 211')
    t = time.time()
    cv = curves()
    if not write:
        for key in ('r2', 'hkF', 'hkM'):
            same = cv[key] == stored['curves'][key]
            check(same, f'{key}: {len(cv[key])} primes {min(map(int, cv[key]))}..{max(map(int, cv[key]))}, '
                        f'all exact values == stored')
    first = {key: min(int(p) for p, e in cv[key].items()
                      if all(e2['sq'] > e2['scale'] for p2, e2 in cv[key].items() if int(p2) >= int(p)))
             for key in cv}
    check(first == {'r2': 37, 'hkF': 53, 'hkM': 89},
          f'first prime from which each curve stays > 1 up to 211: {first} (expected r2 37, hkF 53, hkM 89)')
    print(f'        [curves: {time.time() - t:.1f} s]')

    if write:
        data = {'description': 'Q*_p (s = 5, one resolution): exact toroidal min distance (d2 in units p^-10, '
                               'c = sqrt(d2)/p^4) and the relaxation curves LB = min(2, sqrt(sq/scale)); see '
                               'half5_exact.py',
                'mind': {str(p): res[p] for p in MIND_PRIMES}, 'curves': cv}
        with open(JSON, 'w') as f:
            json.dump(data, f, indent=1)
        print(f'        wrote {JSON}')
    print(f'total {time.time() - T0:.1f} s')
    if FAILS:
        print(f'half5_exact: {len(FAILS)} FAILURE(S):')
        for m in FAILS:
            print('   ', m)
        sys.exit(1)
    print('half5_exact: ALL OK')


if __name__ == '__main__':
    main()

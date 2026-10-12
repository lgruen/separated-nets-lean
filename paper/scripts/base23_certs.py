#!/usr/bin/env python3
"""base23_certs.py -- reruns the finite certificates of Theorem thm:base23 / Table tab:base23 (bases 2 and 3).

It drives the audited checker of the research notes (folder certificates/base23_audit/ of the paper folder, or $BASE23_DIR;
witness chains in certificates/witnesses/r1/, or $WITNESS_DIR) and compares its exact results with core.tex:

  (1) build ba (own toolkit) and ba_dump (replay of the witness chains only); with OpenMP if the compiler has it;
  (2) replay the six chains from their seeds up to the certificate levels; the seed read from its point file by ba
      equals the seed of the replay (same point set); every level, shifted and with the shift removed, has t = 0
      (ba info, all compositions);
  (3) ba_cert.py: exact integers v*_L and exact minima d2 at every level from the seed to L, the same-ancestor proviso,
      and the family floors min(c_seed, ..., c_{L-3}, gsep_L), both with the witness shift and without it;
  (4) the explicit witnesses below the seed levels (base23_audit/witness_smallm; rev 15.7: for b = 2, m = 6, 7 the
      replacement witnesses base23_everyshift/witness_smallm_es/b2_m{6,7}_everyshift.net): t = 0 and exact minima;
  (5) core.tex: every entry of Table tab:base23 (seed level, certificate level, both constants) equals the exact
      floor at that certificate level, truncated to four digits; the constants of Theorem thm:base23 are the minima
      of the columns; every small-m witness exceeds the constants of its residue class (exact comparison);
  (6) rev 15.7, part (3) (every digital shift, Lemma lem:shiftcert): builds es (base23_everyshift/es.cpp, own code
      of the research notes) and runs its exact certifier es_cert.py on the same replayed chains and witnesses;
      column (3) of tab:base23 equals its per-class floors (with the replacement witnesses), the constants of
      thm:base23(3) are their per-base minima, and every small-m witness has every-shift c above column (3).

Run: uv run python scripts/base23_certs.py     (about 30 s wall on 10 cores with OpenMP; about 4 min of CPU)
"""
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)
ROOT = os.path.dirname(PAPER)
B23 = os.environ.get('BASE23_DIR', os.path.join(PAPER, 'certificates', 'base23_audit'))
ES = os.environ.get('EVERYSHIFT_DIR', os.path.join(PAPER, 'certificates', 'base23_everyshift'))
WIT = os.environ.get('WITNESS_DIR', os.path.join(PAPER, 'certificates', 'witnesses'))
TEX = open(os.path.join(PAPER, 'core.tex'), encoding='utf-8').read()
FAIL = []


def check(ok, what):
    print(('  ok    ' if ok else '  FAIL  ') + what)
    if not ok:
        FAIL.append(what)


def sh(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=True).stdout


def build(tmp):
    cands = [os.environ['CXX']] if os.environ.get('CXX') else []
    cands += ['g++-16', 'g++-15', 'g++-14', 'g++-13', 'g++']
    cands = [c for c in cands if shutil.which(c)]
    if not cands:
        sys.exit('no C++ compiler found')
    ba, dump = os.path.join(tmp, 'ba'), os.path.join(tmp, 'ba_dump')
    for cxx in cands:
        r = subprocess.run([cxx, '-O3', '-fopenmp', '-std=c++17', '-o', ba, os.path.join(B23, 'ba.cpp')],
                           capture_output=True, text=True)
        if r.returncode == 0:
            print(f'  built ba with {cxx} -fopenmp')
            break
    else:  # no OpenMP: a stub header; the pragmas are ignored and ba runs on one core
        cxx = cands[0]
        stub = os.path.join(tmp, 'stub')
        os.makedirs(stub)
        open(os.path.join(stub, 'omp.h'), 'w').write('#pragma once\ninline void omp_set_max_active_levels(int){}\n')
        sh([cxx, '-O3', '-std=c++17', '-Wno-unknown-pragmas', '-I', stub, '-o', ba, os.path.join(B23, 'ba.cpp')])
        print(f'  built ba with {cxx} WITHOUT OpenMP (one core; expect a few minutes)')
    sh([cxx, '-O3', '-std=c++17', '-o', dump, os.path.join(B23, 'ba_dump.cpp')])
    es = os.path.join(tmp, 'es')                      # every-shift tool (part (3)); OpenMP optional
    r = subprocess.run([cxx, '-O3', '-fopenmp', '-std=c++17', '-o', es, os.path.join(ES, 'es.cpp')],
                       capture_output=True, text=True)
    if r.returncode != 0:
        stub = os.path.join(tmp, 'stub_es')
        os.makedirs(stub, exist_ok=True)
        open(os.path.join(stub, 'omp.h'), 'w').write('#pragma once\ninline int omp_get_max_threads(){return 1;}\n'
                                                     'inline int omp_get_thread_num(){return 0;}\n')
        sh([cxx, '-O3', '-std=c++17', '-Wno-unknown-pragmas', '-I', stub, '-o', es, os.path.join(ES, 'es.cpp')])
    return ba, dump


FAMS = [('b2_mod0', 9, 7), ('b2_mod1', 10, 6), ('b2_mod2', 11, 6), ('b3_mod0', 6, 4), ('b3_mod1', 7, 5),
        ('b3_mod2', 8, 4)]   # family, seed level, number of lifts replayed (as in base23_audit/run_audit.sh)


def parse_cert(out):
    floors, sec = {}, None
    for line in out.splitlines():
        if line.startswith('=== WITH'):
            sec = 'shifted'
        elif line.startswith('=== SHIFT-FREE'):
            sec = 'unshifted'
        elif line.startswith('=== '):
            sec = None
        m = re.match(r'(b\d_mod\d): c per level', line)
        if m:
            fam = m.group(1)
        m = re.match(r'\s+L=(\d+): v\*=(\d+) gsep=\S+ floor=\S+ \(trunc ([\d.]+)\)', line)
        if m and sec:
            floors[(sec, fam, int(m.group(1)))] = m.group(3)
    return floors


def main():
    t0 = time.time()
    if not os.path.exists(os.path.join(B23, 'ba.cpp')) or not os.path.isdir(os.path.join(WIT, 'r1')):
        sys.exit(f'base23_audit or witnesses not found ({B23}, {WIT}); set BASE23_DIR / WITNESS_DIR')
    tmp = tempfile.mkdtemp(prefix='base23_')
    nets = os.path.join(tmp, 'nets')
    os.makedirs(os.path.join(nets, 'u'))
    print('(1) build')
    ba, dump = build(tmp)
    print('(2) replay the chains; t = 0 at every level')
    nlev = 0
    for fam, m0, nl in FAMS:
        seed = os.path.join(WIT, 'r1', f'{fam}_seed_m{m0}.txt')
        own = os.path.join(nets, f'own_{fam}.net')
        sh([ba, 'frompts', seed, own])
        sh([dump, seed, os.path.join(WIT, 'r1', f'{fam}_params.txt'), str(nl), os.path.join(nets, fam)])
        out = sh([ba, 'cmpsets', own, os.path.join(nets, f'{fam}_m{m0}.net')])
        check('SAME point set' in out, f'{fam}: seed point file == seed of the replayed chain')
    for f in sorted(glob.glob(os.path.join(nets, 'b*_m*.net'))):
        u = os.path.join(nets, 'u', 'u_' + os.path.basename(f))
        sh([ba, 'setshift', f, 'zero', '0', u])
        for g in (f, u):
            nlev += 1
            if 't0=1' not in sh([ba, 'info', g]):
                check(False, f't = 0 at {os.path.basename(g)}')
    check(not any('t = 0' in x for x in FAIL), f't = 0 at all {nlev} replayed levels (shifted and unshifted)')
    print('(3) exact certificates (ba_cert.py)')
    out = subprocess.run([sys.executable, os.path.join(B23, 'ba_cert.py'), nets], cwd=tmp, capture_output=True,
                         text=True, check=True).stdout
    floors = parse_cert(out)
    print('(4) small-m witnesses')
    wit = {}
    repl = {(2, 6), (2, 7)}                           # rev 15.7: replaced by the every-shift witnesses
    files = [f for f in sorted(glob.glob(os.path.join(B23, 'witness_smallm', 'b*_m*.net')))
             if tuple(map(int, re.search(r'b(\d)_m(\d+)\.net', f).groups())) not in repl]
    files += [os.path.join(ES, 'witness_smallm_es', f'b{b}_m{m}_everyshift.net') for b, m in sorted(repl)]
    for f in files:
        b, m = map(int, re.search(r'b(\d)_m(\d+)(?:_everyshift)?\.net', f).groups())
        ok = 't0=1' in sh([ba, 'info', f])
        d2 = int(re.search(r'd2=(\d+)', sh([ba, 'mind', f])).group(1))
        check(ok, f'witness b={b} m={m}: t = 0')
        wit[(b, m)] = d2
    print('(5) core.tex')
    i = TEX.index('\\label{tab:base23}')
    blk = TEX[TEX.rfind('\\begin{table}', 0, i):i]
    rows = []
    for line in blk.split('\\\\'):
        c = [x.strip() for x in line.strip().split('\n')[-1].split('&')]
        if len(c) == 7 and c[0] in ('2', '3'):
            rows.append((int(c[0]), int(c[1]), int(c[2]), int(c[3]), c[4], c[5], c[6]))
    check(len(rows) == 6, f'tab:base23: {len(rows)} rows parsed')
    seedlev = {fam: m0 for fam, m0, _ in FAMS}
    for b, res, sl, L, v1, v2, v3 in rows:
        fam = f'b{b}_mod{res}'
        check(seedlev[fam] == sl, f'tab:base23 {fam}: seed level {sl}')
        for sec, v in (('shifted', v1), ('unshifted', v2)):
            got = floors.get((sec, fam, L))
            check(got is not None and Fr(got) == Fr('0' + v if v.startswith('.') else v),
                  f'tab:base23 {fam} {sec}: printed {v}, exact floor at L={L} truncated {got}')
    thm = TEX[TEX.index('\\label{thm:base23}'):TEX.index('\\end{theorem}', TEX.index('\\label{thm:base23}'))]
    consts = {}
    for b in (2, 3):
        consts[(b, 1)] = min(Fr('0' + r[4]) for r in rows if r[0] == b)
        consts[(b, 2)] = min(Fr('0' + r[5]) for r in rows if r[0] == b)
    for b in (2, 3):
        consts[(b, 3)] = min(Fr('0' + r[6]) for r in rows if r[0] == b)
    want = [('1', 2, '0.4129'), ('1', 3, '0.3538'), ('2', 2, '0.1718'), ('2', 3, '0.0770'), ('3', 2, '0.1718'),
            ('3', 3, '0.0770')]
    for part, b, v in want:
        check(consts[(b, int(part))] == Fr(v) and thm.count(v) >= 1, f'thm:base23 ({part}) b={b}: {v} = column minimum')
    for (b, m), d2 in sorted(wit.items()):
        r = next(r for r in rows if r[0] == b and r[1] == m % 3)
        for v in (r[4], r[5]):
            vv = Fr('0' + v)
            check(Fr(d2) ** 3 > vv ** 6 * b ** (4 * m), f'witness b={b} m={m}: c > {v} (exact)')
    print('(6) part (3): every digital shift (es_cert.py of base23_everyshift, on the same nets)')
    out = subprocess.run([sys.executable, os.path.join(ES, 'es_cert.py'), nets, os.path.join(B23, 'witness_smallm'),
                          os.path.join(ES, 'witness_smallm_es')], cwd=tmp, capture_output=True, text=True,
                         check=True).stdout
    es3, fam = {}, None
    for line in out.splitlines():
        mm = re.match(r'(b\d_mod\d): levels', line)
        if mm:
            fam = mm.group(1)
        mm = re.search(r'PROVED floor incl\. the small-m witnesses .*-> trunc ([\d.]+)', line)
        if mm and fam not in es3:
            es3[fam] = mm.group(1)
        mm = re.search(r'with the replacement witnesses .*-> trunc ([\d.]+)', line)
        if mm:
            es3[fam] = mm.group(1)                    # the replacement witnesses are the paper's (rev 15.7)
    for b, res, sl, L, v1, v2, v3 in rows:
        fam = f'b{b}_mod{res}'
        check(fam in es3 and Fr(es3[fam]) == Fr('0' + v3), f'tab:base23 {fam} (3): printed {v3}, exact every-shift floor '
              f'truncated {es3.get(fam)}')
    for (b, m), d2 in sorted(wit.items()):
        f = next(f for f in files if re.search(rf'b{b}_m{m}(_everyshift)?\.net$', f))
        d2u = int(re.search(r'd2_unif=(\d+)', sh([os.path.join(tmp, 'es'), 'cunif', f])).group(1))
        r = next(r for r in rows if r[0] == b and r[1] == m % 3)
        vv = Fr('0' + r[6])
        check(Fr(d2u) ** 3 > vv ** 6 * b ** (4 * m), f'witness b={b} m={m}: every-shift c > {r[6]} (exact)')
    shutil.rmtree(tmp, ignore_errors=True)
    print(f'base23_certs: {len(FAIL)} failures ({time.time() - t0:.0f} s)')
    sys.exit(1 if FAIL else 0)


if __name__ == '__main__':
    main()

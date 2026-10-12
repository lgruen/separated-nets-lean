"""Generate Lean data modules Z3Net/SkCertD*.lean for tab:S1E + ChallengeS1E statements.
usage: uv run python gen_lean.py [only_tag]"""
import sys, os, re, math, json
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, '`geo` (research repository)')
sys.path.insert(0, '`paper` (research repository)')
from gen import cert, jit2, dot
from s1e_certs import rows
from codesaudit_e1 import analyse, is_prime

LEAN = 'the Lean project (repository root)'
TEX = '`paper/core.tex`'


def table():
    t = open(TEX).read()
    a = t.index(r'\label{tab:S1E}')
    blk = t[t.rindex(r'\begin{tabular}', 0, a):a]
    vals = {}
    for line in blk.splitlines():
        m = re.match(r'^(\d) & (.*)\\\\', line.strip())
        if m:
            s = int(m.group(1))
            cells = [c.strip() for c in m.group(2).split('&')][:6]
            vals[s] = [c.replace('$', '').replace('^*', '') for c in cells]
    return vals


def cells():
    tab = table()
    rs = rows()
    out = []
    for s in range(3, 9):
        for col, p in enumerate([1009, 10007, 1000003, 100000007]):
            r = [x for x in rs if x[0] == 'search' and x[1] == s and x[2] == p]
            assert len(r) == 1
            out.append((s, p, r[0][3], tab[s][col], 'searched'))
        for col, e in ((4, '1e6'), (5, '1e10')):
            r = [x for x in rs if x[0].startswith('round') and x[0].endswith(':' + e) and x[1] == s]
            assert len(r) == 1
            out.append((s, r[0][2], r[0][3], tab[s][col], 'rounded ' + e))
    return out


def lst(v):
    return '[' + ', '.join(str(x) for x in v) + ']'


def gen_entry(s, p, kap, printed, digits=3, suffix=''):
    r = analyse(p, kap)
    J = r['lamjit2']
    c = cert(p, kap, J)
    assert c['ok']
    # witness
    cand = [list(b) for b in c['B']] + ([r['argmin']] if r['argmin'] else [])
    wit = None
    for v in cand:
        if any(v) and jit2(v) == J and (v[s - 1] - sum(k * x for k, x in zip(kap, v[:s - 1]))) % p == 0:
            wit = v; break
    assert wit is not None
    r0 = math.isqrt(s * (J - 1))
    assert s * (J - 1) < (r0 + 1) ** 2
    # printed value check: c^(2s) p^2 <= J^s exactly
    cv = Fraction(printed) if not printed.startswith('.') else Fraction('0' + printed)
    assert cv ** (2 * s) * p * p <= Fraction(J) ** s, (s, p, printed, J)
    # and next value up (truncation, not too low)
    nxt = cv + Fraction(1, 10 ** digits)
    trunc_ok = not (nxt ** (2 * s) * p * p <= Fraction(J) ** s)
    tag = 's%d_p%d%s' % (s, p, suffix)
    Ls = list(reversed(c['levels']))
    lv = '[' + ',\n  '.join('(%d, %s)' % (d, '[' + ', '.join(lst(v) for v in P) + ']') for d, P in Ls) + ']'
    data = []
    data.append('def B_%s : List (List ℤ) :=\n  [%s]' % (tag, ',\n   '.join(lst(b) for b in c['B'])))
    data.append('def W_%s : List (List ℤ) :=\n  [%s]' % (tag, ',\n   '.join(lst(b) for b in c['W'])))
    data.append('def L_%s : List (ℤ × List (List ℤ)) :=\n  %s' % (tag, lv))
    data.append('def wit_%s : List ℤ := %s' % (tag, lst(wit)))
    kl = lst(kap)
    pv = printed if not printed.startswith('.') else '0' + printed
    stmt = ('theorem S1E_tab_%s :\n    Nat.Prime %d ∧ (∀ d < %d, kapL %d %s d ≠ 0) ∧\n      lamJit2 %d %d (kapL %d %s) = %d ∧\n      (%s : ℝ) ≤ Real.sqrt (lamJit2 %d %d (kapL %d %s)) * (%d : ℝ) ^ (-(1 / (%d : ℝ)))'
            % (tag, p, s - 1, p, kl, s, p, p, kl, J, pv, s, p, p, kl, p, s))
    proof = ('theorem cert_%s : certOK %d %d %s %d %d B_%s W_%s L_%s = true := by decide +kernel\n\n'
             'theorem witok_%s : witOK %d %d %s %d wit_%s = true := by decide +kernel\n\n'
             '%s := by\n'
             '  have h := lamJit2_of_cert %d %d %s %d %d B_%s W_%s L_%s wit_%s cert_%s witok_%s\n'
             '  refine ⟨by norm_num, units_of_ok %d %s %d (by decide +kernel), h, ?_⟩\n'
             '  rw [h]\n'
             '  exact trunc_le %d %d %d %s (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n'
             % (tag, s, p, kl, J, r0, tag, tag, tag,
                tag, s, p, kl, J, tag,
                stmt.replace('theorem S1E_tab_', 'theorem S1E_tab_'),
                s, p, kl, J, r0, tag, tag, tag, tag, tag, tag,
                p, kl, s - 1,
                J, p, s, pv))
    return dict(tag=tag, s=s, p=p, J=J, data='\n\n'.join(data), proof=proof, stmt=stmt,
                trunc_ok=trunc_ok, prime=is_prime(p), nodes=c['stats']['nodes'])


EXTRAS = [
    (8, 10007, [3, 9, 27, 81, 243, 729, 2187], '.632', 'caption footnote: kappa_d = rho^d, rho = 3', 3, '_rho'),
    (3, 101, [88, 66], '.7742', 'app:verify: kappa = (88, 66)', 4, ''),
    (3, 101, [4, 16], '.6441', 'app:verify: kappa = (4, 16) = rho^d, rho = 4', 4, '_rho'),
]

HDR = '''/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(draft; LaTeX source `paper/core.tex`). Results are cited by their `\\label` names, never by numbers.
Entry S1E: kernel certificates for the values of `tab:S1E` (`prop:S1E`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.SkCertSound

@[expose] public section

/-! # Entry S1E: certificates for `tab:S1E`, %s (generated by the SkCert generator `gen_lean.py`, which recomputes `J` with `codesaudit_e1.py` (research repository))

Data per cell: an LLL-reduced basis `B` of `Λ_κ`, `W` with `W B = E`, the projection levels
(`levOK`), and a witness of `lamJit2 = J`; checked by `decide +kernel` (`certOK`, `witOK`). -/

namespace Z3NetF.Proofs

set_option maxRecDepth 200000

open SkCert

'''


if __name__ == '__main__':
    only = sys.argv[1] if len(sys.argv) > 1 else None
    cs = cells()
    ents = []
    cs = [c + (3, '') for c in cs] + EXTRAS
    for s, p, kap, printed, kind, digits, suffix in cs:
        e = gen_entry(s, p, kap, printed, digits, suffix)
        e['kind'] = kind
        e['printed'] = printed
        ents.append(e)
        print(e['tag'], kind, 'J=%d' % e['J'], 'printed', printed, 'trunc_ok', e['trunc_ok'], 'prime', e['prime'], 'nodes', e['nodes'])
    json.dump([{k: v for k, v in e.items() if k not in ('data', 'proof')} for e in ents],
              open(os.path.join(HERE, 'cells.json'), 'w'), indent=1)
    groups = {}
    for e in ents:
        groups.setdefault(e['s'], []).append(e)
    for s, es in groups.items():
        if only and only != str(s):
            continue
        name = 'SkCertD%d' % s
        body = HDR % ('`s = %d`' % s)
        for e in es:
            body += '/-! ## `%s` (%s) -/\n\n' % (e['tag'], e['kind'])
            body += e['data'] + '\n\n' + e['proof'] + '\n'
        body += 'end Z3NetF.Proofs\n'
        open(os.path.join(LEAN, 'Z3Net', name + '.lean'), 'w').write(body)
        print('wrote', name, len(body.splitlines()), 'lines')
    open(os.path.join(HERE, 'stmts.lean'), 'w').write('\n\n'.join(
        '/-- `tab:S1E`, %s, `s = %d`, `p = %d`: `λ_jit(κ)² = %d` and the printed value `%s`. -/\n%s := by\n  sorry'
        % (e['kind'], e['s'], e['p'], e['J'], e['printed'], e['stmt']) for e in ents))

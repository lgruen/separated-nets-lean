"""llg_dump.py -- build the gauged split-frame net for a design JSON at (k, q) and print generator
matrices mod q in the 'p m s + s row-major m x m matrices' format (or with header 's k q')."""
import sys, json
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from fractions import Fraction as Fr
from llg_lib import split_graph_form, gauge_to_design, build_net, to_mod

def build(path, k):
    W = json.load(open(path))
    s, u, v = W['s'], W['u'], W['v']
    F = [[[Fr(x, 2) for x in r] for r in Fn] for Fn in W['F2']]
    Phi = split_graph_form(u, v, k)
    T = F[:min(s - 1, k)]
    lam, U, ok, msg = gauge_to_design(Phi, s, k, T)
    assert ok, msg
    C, _ = build_net(Phi, s, k, T, lam, U)
    return s, C

if __name__ == '__main__':
    path, k, q, fmt = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    s, C = build(path, k)
    Cq = to_mod(C, q)
    m = s * k
    print(f"{q} {m} {s}" if fmt == 'mind2' else f"{s} {k} {q}")
    for M in Cq:
        for r in M:
            print(" ".join(str(x) for x in r))

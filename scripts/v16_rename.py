#!/usr/bin/env python3
"""V14 stage S16′: the legacy-name rename (the research notes; the map is recorded in the research notes).

The Eisenstein nets left the paper in revision 14.0, the net 𝓔_p (`thm:E1`) in revision 15.0. Their namespace,
directory and library `EisensteinNet` still held live material: the two-coset net 𝒯_p (`prop:twocoset`), the
rank-one layers 𝒲_p (`sec:wnet`), the digital point sets at `m = 3` and the lemmas these reuse. This pass

* renames the namespace `EisensteinNet` → `QUNetsM3` (the nets at `m = 3` of the statement library `QUNets`), a
  pure prefix map of declaration names (`NS_PREFIX`); no compared theorem or reachable definition changes its last
  name component;
* moves the live modules from `EisensteinNet/` to `QUNetsM3/` (library `QUNetsM3`), splitting the legacy modules
  `Defs`, `Box`, `E1Defs`, `E1Net`, `E1Sep`, `E1Core` into their live part (`MODULES`) and a retired part;
* moves every retired-only module (and the retired parts) to the retired Eisenstein development (research history) (library `Retired`, not a
  default target; namespace `EisensteinNet` kept there, with `open QUNetsM3`), together with `ChecksEis.lean`,
  `ChecksE1.lean`.

Used by `gen_v14_statements.py` (the stage-13c texts of the kept theorems are renamed with `apply_text`, so the
byte comparison of `check_statements.py` is modulo this map) and by `check_statement_identity.py check-renamed`
(the inverse prefix map is applied to the dump of the renamed library before it is compared with the old
baseline).
"""
import re

NS_PREFIX = {'EisensteinNet': 'QUNetsM3'}

# live modules: old module name -> new module name (only those that exist after the rename)
MODULES = {
    'EisensteinNet.Defs': 'QUNetsM3.Defs',  # live part: digits, coord
    'EisensteinNet.Digits': 'QUNetsM3.Digits',  # + div_lt_of_lt_cube (from Box)
    'EisensteinNet.E1Defs': 'QUNetsM3.NetDefs',  # live part: digitalPt, IsDigitalNet033, sepSqG
    'EisensteinNet.TCCore': 'QUNetsM3.TCCore',
    'EisensteinNet.TCDefs': 'QUNetsM3.TCDefs',
    'EisensteinNet.TCMain': 'QUNetsM3.TCMain',
    'EisensteinNet.TCNet': 'QUNetsM3.TCNet',
    'EisensteinNet.TCPair': 'QUNetsM3.TCPair',
    'EisensteinNet.TCParams': 'QUNetsM3.TCParams',
    'EisensteinNet.TCSep': 'QUNetsM3.TCSep',
    'EisensteinNet.TCShift': 'QUNetsM3.TCShift',
    'EisensteinNet.WCore': 'QUNetsM3.WCore',
    'EisensteinNet.WDefs': 'QUNetsM3.WDefs',
    'EisensteinNet.WExact': 'QUNetsM3.WExact',
    'EisensteinNet.WExactCore': 'QUNetsM3.WExactCore',
    'EisensteinNet.WFamCert': 'QUNetsM3.WFamCert',
    'EisensteinNet.WFamOne': 'QUNetsM3.WFamOne',
    'EisensteinNet.WFamThree': 'QUNetsM3.WFamThree',
    'EisensteinNet.WFamTwo': 'QUNetsM3.WFamTwo',
    'EisensteinNet.WFour': 'QUNetsM3.WFour',
    'EisensteinNet.WMain': 'QUNetsM3.WMain',
    'EisensteinNet.WNet': 'QUNetsM3.WNet',
    'EisensteinNet.WPair': 'QUNetsM3.WPair',
    'EisensteinNet.WReduce': 'QUNetsM3.WReduce',
    'EisensteinNet.WSep': 'QUNetsM3.WSep',
    'EisensteinNet.WShiftLink': 'QUNetsM3.WShiftLink',
    'EisensteinNet.WStar': 'QUNetsM3.WStar',
    'EisensteinNet.WWrap': 'QUNetsM3.WWrap',
    'EisensteinNet.WWrapOne': 'QUNetsM3.WWrapOne',
}
# live declarations moved out of the retired modules E1Net, E1Sep, E1Core (into `QUNetsM3.NetBasic`), renamed:
# cellE1 -> cellDigits, e1_tri -> sq_tri_lower; digitalPt_eq, isDigitalNet033_of_inj keep their names.
DECL_RENAMES = {'EisensteinNet.cellE1': 'QUNetsM3.cellDigits', 'EisensteinNet.e1_tri': 'QUNetsM3.sq_tri_lower'}


def new_name(n):
    """Declaration name after the rename (prefix map)."""
    for a, b in NS_PREFIX.items():
        if n == a or n.startswith(a + '.'):
            return b + n[len(a):]
    return n


def apply_text(t):
    """Rename module paths of live modules, then the namespace, in a Lean/doc text."""
    for a, b in sorted(MODULES.items(), key=lambda kv: -len(kv[0])):
        t = re.sub(r'(?<![A-Za-z0-9_.])' + re.escape(a) + r'(?![A-Za-z0-9_])', b, t)
    for a, b in NS_PREFIX.items():
        t = re.sub(r'(?<![A-Za-z0-9_])' + re.escape(a) + r'(?![A-Za-z0-9_])', b, t)
    return t

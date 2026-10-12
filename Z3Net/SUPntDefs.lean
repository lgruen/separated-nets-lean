/-
Definition `PNTpsi` (stage 11, entry PPInvU), moved verbatim from `Z3Net/SUPntS11.lean` (stage 13b)
so that statement and proof modules import the same constant.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib

@[expose] public section

/-!
# The prime number theorem as a hypothesis (`PNTpsi`)

Verbatim copy of the definition of `ChallengePPInvU.lean`; used by `Z3NetU.U_growth_pnt` and
`Z3NetU.U_bound_growth_pnt` (`Z3Net/SUPntS11.lean`).
-/

namespace Z3NetU

/-- The prime number theorem in Chebyshev's form, `ψ(x) ~ x` (`Chebyshev.psi x = ∑_{n ≤ x} Λ(n)`,
Mathlib). A theorem (Hadamard, de la Vallée Poussin), but not in Mathlib at the pinned version;
used as an explicit hypothesis, so `U_growth_pnt` and `U_bound_growth_pnt` are reductions. -/
def PNTpsi : Prop :=
  Filter.Tendsto (fun x : ℝ => Chebyshev.psi x / x) Filter.atTop (nhds 1)

end Z3NetU

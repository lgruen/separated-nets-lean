/-
Development copy (Solution side) of the new definitions of ChallengeS1E (entry S1E).
Keep in sync with the block `## New definitions (entry S1E)` of `ChallengeS1E.lean`; the other
definitions of that Challenge (`InLatK`, `jitNorm2`, `lamJit2`, `lam2Sq`) are verbatim copies of
those of `ChallengeSkel.lean` and live in `Z3Net/SkelDefs.lean`.
-/
module
public import Z3Net.SkelDefs

@[expose] public section

namespace Z3NetF

open Matrix Finset

/-! ## New definitions (entry S1E) -/

/-- The coefficients `κ` of `prop:S1E` given by the list `L = [κ_0, …, κ_{s-2}]` of residues
(`κ_d` the coefficient of the full coordinate `d`; entries beyond the list are `0`). -/
def kapL (p : ℕ) (L : List ℕ) : ℕ → ZMod p := fun d => (L.getD d 0 : ZMod p)

end Z3NetF

module
public import Mathlib
public import Z3Net.D4Case

@[expose] public section

/-!
# 4D entry: the kernel-checked enumerations of Proposition C

Ordinary kernel `decide` (`decide +kernel`, no `native_decide`); about 35 s in total.
-/

namespace Z3NetD4.Proofs

/-- The kernel-checked enumerations (about 35 s in total). -/
theorem checkPoly_eq : checkPoly = true := by decide +kernel
theorem checkSmall5 : checkSmall 5 = true := by decide +kernel
theorem checkSmall7 : checkSmall 7 = true := by decide +kernel
theorem checkSmall9 : checkSmall 9 = true := by decide +kernel
theorem checkSigBound_eq : checkSigBound = true := by decide +kernel

end Z3NetD4.Proofs

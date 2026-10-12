module
public import Mathlib
public import Z3Net.HLB5Cert

@[expose] public section

/-!
# Entry HL, part 12: the `s = 5` certificate, kernel check (`decide +kernel`, no `native_decide`)

Split by the first cell step `e₀ ∈ {-2, …, 2}` (about 45 s of kernel time in total).
-/

namespace Z3NetHL.Proofs

set_option maxRecDepth 100000

theorem checkE0_m2 : checkE0 (-2) = true := by decide +kernel
theorem checkE0_m1 : checkE0 (-1) = true := by decide +kernel
theorem checkE0_0 : checkE0 0 = true := by decide +kernel
theorem checkE0_1 : checkE0 1 = true := by decide +kernel
theorem checkE0_2 : checkE0 2 = true := by decide +kernel

theorem check_all : ∀ e0 ∈ vals, checkE0 e0 = true := by
  intro e0 he
  simp only [vals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h | h | h | h | h <;> subst h
  · exact checkE0_m2
  · exact checkE0_m1
  · exact checkE0_0
  · exact checkE0_1
  · exact checkE0_2

end Z3NetHL.Proofs

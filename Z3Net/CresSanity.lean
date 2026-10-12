module
public import Z3Net.Defs

@[expose] public section

/-!
# Reviewer sanity lemma for `cres`

`cres N u` (the distance from the integer `u` to the lattice `N ℤ`, defined in the Challenge
as `min (u mod N) (N - u mod N)`) agrees with Mathlib's minimal-absolute-value representative:
`cres N u = |valMinAbs (u mod N)|`.  This is not used by the proofs; it only lets a reader
check the Challenge definition against a standard Mathlib notion.
-/

namespace Z3Net

/-- `cres N u = ((u : ZMod N).valMinAbs).natAbs` for every `N > 0`. -/
theorem cres_eq_natAbs_valMinAbs (N : ℕ) (hN : 0 < N) (u : ℤ) :
    cres N u = ((u : ZMod N).valMinAbs).natAbs := by
  have : NeZero N := ⟨hN.ne'⟩
  have hval : (((u : ZMod N).val : ℕ) : ℤ) = u % (N : ℤ) := ZMod.val_intCast u
  have hnn : 0 ≤ u % (N : ℤ) := Int.emod_nonneg u (by exact_mod_cast hN.ne')
  have hlt : u % (N : ℤ) < N := Int.emod_lt_of_pos u (by exact_mod_cast hN)
  rw [ZMod.valMinAbs_def_pos]
  unfold cres
  split_ifs with h <;> omega

end Z3Net

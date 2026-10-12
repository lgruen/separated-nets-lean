/-
`def:dshift` for the nets of `prop:twocoset` and `sec:wnet`: the shifted point set `digitalPtS` of V14 stage S12′ is
the digit-by-digit shift `Z3NetF.dshiftPt` of V14 stage S10′ applied to the unshifted point set `digitalPt`
(`paper/core.tex`). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WDefs
public import QUNetsM3.Digits
public import Z3Net.DShiftDefs

@[expose] public section

namespace QUNetsM3

open Matrix

/-- One coordinate: shifting the three base-`p` digits of `coord p w` by `t` (`dshiftCoord`) gives `coord p (w + t)`. -/
theorem dshiftCoord_coord {p : ℕ} [NeZero p] (w t : Fin 3 → ZMod p) :
    Z3NetF.dshiftCoord p 3 t (coord p w) = coord p (w + t) := by
  have hd : ∀ j : Fin 3, ((((coord p w / p ^ (3 - 1 - (j : ℕ))) % p : ℕ) : ZMod p)) = w j := by
    intro j
    rw [ZMod.natCast_mod]
    have := congrFun (digits_coord w) j
    fin_cases j <;> simpa [digits] using this
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  norm_num at h0 h1 h2
  simp only [Z3NetF.dshiftCoord, Fin.sum_univ_three, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  rw [h0, h1, h2]
  simp [coord_def]

/-- **`def:dshift` for `digitalPtS`**: the shifted point set of `rem:shiftshared` (V14 stage S12′) is the digit-by-digit
shift of `def:dshift` (`Z3NetF.dshiftPt`, V14 stage S10′) of the unshifted point set `digitalPt`, for every `p ≥ 1`. -/
theorem digitalPtS_eq_dshiftPt_core (p : ℕ) [NeZero p] (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p))
    (τ : Fin 3 → Fin 3 → ZMod p) (x : ℕ) :
    digitalPtS p C τ x = Z3NetF.dshiftPt p 3 τ (digitalPt p C x) := by
  funext c
  simp only [digitalPtS, Z3NetF.dshiftPt, digitalPt]
  exact (dshiftCoord_coord _ _).symm

end QUNetsM3

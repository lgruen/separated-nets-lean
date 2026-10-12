/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColFree
public import Z3Net.DShiftDefs

@[expose] public section

/-!
# V14 stage S9′: every digital shift of `𝒞_q` (`prop:colshift`)

Shifted digits (the paragraph "Shifted digits" of the proof): after re-indexing by the cells
`n = v + τ₁`, coordinate `c` of the point of `𝒞_q ⊕ τ` has the digits `n_c`, `a·n + β_c`,
`ℓ·n + β'_c` (`shiftPt_eq`), `β_c = τ_{c,2} - a·τ₁`, `β'_c = τ_{c,3} - ℓ·τ₁`.

* (1) equal second and third shift digits: a column point set with heights `φ(n + u)`
  (`a·u = β`, `ℓ·u = β'`; `(a, ℓ)` is onto since `a_x + a_y` is a unit), the same `3g = τ`.
* (2) equal second digits: `prop:colfree` with `‖w‖₁ = 4`.
* (3) every shift: `3U_c ≡ qσ_E + w·E (mod 3q)` for `U = qE + Δh` (`shift_lower_core`); the upper
  bound by the arc argument of the printed proof (`arc_exists`): a cell where exactly the
  coordinate `c` wraps its shared digit along `e_c` gives the difference `q a_c 𝟏 + Δj`.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-! ## Shifted digits -/

lemma colH_add (w : Fin 3 → ℤ) (x y : Fin 3 → ZMod q) : colH q w (x + y) = colH q w x + colH q w y := by
  simp [colH, mul_add, Finset.sum_add_distrib]

lemma colJ_add (ℓ : Fin 3 → ℤ) (x y : Fin 3 → ZMod q) : colJ q ℓ (x + y) = colJ q ℓ x + colJ q ℓ y := by
  simp [colJ, mul_add, Finset.sum_add_distrib]

/-- The first shift digits `τ₁ = (τ_{c,1})_c`. -/
def sh0 (sh : Fin 3 → Fin 3 → ZMod q) : Fin 3 → ZMod q := fun c => sh c 0

/-- `β_c = τ_{c,2} - a·τ₁`. -/
def shB (sh : Fin 3 → Fin 3 → ZMod q) (c : Fin 3) : ZMod q := sh c 1 - colH q (wCol q) (sh0 sh)

/-- `β'_c = τ_{c,3} - ℓ·τ₁`. -/
def shB' (sh : Fin 3 → Fin 3 → ZMod q) (c : Fin 3) : ZMod q := sh c 2 - colJ q ellCol (sh0 sh)

lemma shiftPt_eq (sh : Fin 3 → Fin 3 → ZMod q) (v : Fin 3 → ZMod q) (c : Fin 3) :
    digPointShift q 3 (colGen q) sh v c =
      q ^ 2 * ((v + sh0 sh) c).val + q * (colH q (wCol q) (v + sh0 sh) + shB sh c).val +
        (colJ q ellCol (v + sh0 sh) + shB' sh c).val := by
  obtain ⟨h0, h1, h2⟩ := colGenW_mulVec q (wCol q) ellCol c v
  simp only [digPointShift, Fin.sum_univ_three, Pi.add_apply, colGen]
  rw [h0, h1, h2]
  simp only [shB, shB', colH_add, colJ_add]
  have e1 : colH q (wCol q) v + colH q (wCol q) (sh0 sh) + (sh c 1 - colH q (wCol q) (sh0 sh)) =
      colH q (wCol q) v + sh c 1 := by ring
  have e2 : colJ q ellCol v + colJ q ellCol (sh0 sh) + (sh c 2 - colJ q ellCol (sh0 sh)) =
      colJ q ellCol v + sh c 2 := by ring
  rw [e1, e2]
  simp [sh0]; ring

/-! ## (1) equal second and third shift digits -/

lemma colGap_translate (φ : (Fin 3 → ZMod q) → ℕ) (u : Fin 3 → ZMod q) :
    colGap q (fun n => φ (n + u)) = colGap q φ := by
  have hstep : ∀ i n, colStep q (fun n => φ (n + u)) i n = colStep q φ i (n + u) := by
    intro i n; simp only [colStep]; rw [add_right_comm]
  apply le_antisymm
  · obtain ⟨⟨i, n⟩, -, hmin⟩ := Finset.exists_mem_eq_inf'
      (s := (univ : Finset (Fin 3 × (Fin 3 → ZMod q)))) univ_nonempty
      (fun x => cres (3 * q ^ 2) (3 * colStep q φ x.1 x.2 - 2 * q ^ 2))
    have := colGap_le (fun n => φ (n + u)) i (n - u)
    rw [hstep, sub_add_cancel] at this
    exact this.trans (le_of_eq hmin.symm)
  · obtain ⟨⟨i, n⟩, -, hmin⟩ := Finset.exists_mem_eq_inf'
      (s := (univ : Finset (Fin 3 × (Fin 3 → ZMod q)))) univ_nonempty
      (fun x => cres (3 * q ^ 2) (3 * colStep q (fun n => φ (n + u)) x.1 x.2 - 2 * q ^ 2))
    have := colGap_le φ i (n + u)
    rw [← hstep] at this
    exact this.trans (le_of_eq hmin.symm)

lemma colA01_unit (h6 : Nat.Coprime q 6) :
    IsUnit (((colA q (wCol q) 0 : ℤ) : ZMod q) + ((colA q (wCol q) 1 : ℤ) : ZMod q)) := by
  obtain ⟨hw0, hw3, -, hwu⟩ := wCol_props (q := q) h6
  have e : (3 : ZMod q) * (((colA q (wCol q) 0 : ℤ) : ZMod q) + ((colA q (wCol q) 1 : ℤ) : ZMod q)) =
      -((wCol q 2 : ℤ) : ZMod q) := by
    rw [mul_add, three_colA _ hw3, three_colA _ hw3]
    have : ((wCol q 0 + wCol q 1 + wCol q 2 : ℤ) : ZMod q) = 0 := by
      rw [show wCol q 0 + wCol q 1 + wCol q 2 = ∑ c, wCol q c by simp [Fin.sum_univ_three], hw0]
      simp
    push_cast at this
    linear_combination this
  have := (hwu 2).neg
  rw [← e] at this
  exact isUnit_of_mul_isUnit_right this

/-- `(a, ℓ)` is onto `(ℤ/qℤ)²`. -/
lemma colHJ_onto (h6 : Nat.Coprime q 6) (β β' : ZMod q) :
    ∃ u : Fin 3 → ZMod q, colH q (wCol q) u = β ∧ colJ q ellCol u = β' := by
  obtain ⟨μ, hμ⟩ := colA01_unit (q := q) h6
  set a0 := ((colA q (wCol q) 0 : ℤ) : ZMod q)
  set a1 := ((colA q (wCol q) 1 : ℤ) : ZMod q)
  set u0 := (↑μ⁻¹ : ZMod q) * (β - a1 * β')
  refine ⟨![u0, u0 + β', 0], ?_, ?_⟩
  · simp only [colH, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero, add_zero]
    have : (a0 + a1) * u0 = β - a1 * β' := by
      simp only [u0]; rw [← hμ, ← mul_assoc, Units.mul_inv, one_mul]
    linear_combination this
  · simp [colJ, ellCol, Fin.sum_univ_three]

/-- **`prop:colshift`(1)**: equal second and third shift digits give a column point set with the
heights of `𝒞_q` translated by a cell `u`. -/
lemma shift_column (h6 : Nat.Coprime q 6) (sh : Fin 3 → Fin 3 → ZMod q)
    (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) (h3 : sh 0 2 = sh 1 2 ∧ sh 1 2 = sh 2 2) :
    ∃ u : Fin 3 → ZMod q, ∀ v, digPointShift q 3 (colGen q) sh v =
      colPt q (fun n => phiC q (n + u)) (v + sh0 sh) := by
  obtain ⟨u, hu1, hu2⟩ := colHJ_onto h6 (shB sh 0) (shB' sh 0)
  refine ⟨u, fun v => funext fun c => ?_⟩
  have hB : shB sh c = shB sh 0 := by
    fin_cases c <;> simp [shB, h2.1, h2.2]
  have hB' : shB' sh c = shB' sh 0 := by
    fin_cases c <;> simp [shB', h3.1, h3.2]
  rw [shiftPt_eq, hB, hB', ← hu1, ← hu2, ← colH_add, ← colJ_add]
  simp only [colPt, phiC, colPhi]
  ring

/-- **`prop:colshift`(1)**. -/
lemma colshift_eq (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (sh : Fin 3 → Fin 3 → ZMod q)
    (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) (h3 : sh 0 2 = sh 1 2 ∧ sh 1 2 = sh 2 2) :
    (∀ v w : Fin 3 → ZMod q, v ≠ w → 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ≤
      3 * (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℤ)) ∧
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧
      3 * (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℤ) = 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
  obtain ⟨u, hu⟩ := shift_column h6 sh h2 h3
  have hH : IsHeight q (fun n => phiC q (n + u)) := by
    obtain ⟨h1, h2⟩ := isHeight_phiC (q := q) h6
    exact ⟨fun n => h1 _, fun n => by simp only; rw [add_right_comm, h2]⟩
  have hG : (colGap q (fun n => phiC q (n + u)) : ℤ) = tauCol q := by
    rw [colGap_translate]; exact col_gap h6 hq
  refine ⟨fun v w hvw => ?_, ?_⟩
  · rw [hu, hu]
    have := colmin_lower (by omega) _ hH (v + sh0 sh) (w + sh0 sh) (by
      intro h; exact hvw (add_right_cancel h))
    rwa [hG] at this
  · obtain ⟨i, n, t, hne, heq⟩ := colmin_attained (by omega) _ hH
    refine ⟨n - sh0 sh, n + Pi.single i 1 + (fun _ => t) - sh0 sh, fun h => hne (by
      have := congrArg (· + sh0 sh) h; simpa using this.symm), ?_⟩
    rw [hu, hu, sub_add_cancel, sub_add_cancel, ← hG]
    exact_mod_cast heq

/-! ## (2) equal second shift digits -/

lemma shift_free (sh : Fin 3 → Fin 3 → ZMod q) (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1)
    (v : Fin 3 → ZMod q) :
    digPointShift q 3 (colGen q) sh v =
      freePt q (fun n => (colH q (wCol q) n + shB sh 0).val)
        (fun n c => (colJ q ellCol n + shB' sh c).val) (v + sh0 sh) := by
  funext c
  have hB : shB sh c = shB sh 0 := by
    fin_cases c <;> simp [shB, h2.1, h2.2]
  rw [shiftPt_eq, hB]
  rfl

/-- **`prop:colshift`(2)**. -/
lemma colshift_agree2 (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (sh : Fin 3 → Fin 3 → ZMod q)
    (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) (v w : Fin 3 → ZMod q) (hvw : v ≠ w) :
    (q : ℝ) ^ 2 - (7 * q - 3) / Real.sqrt 3 ≤
      Real.sqrt (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℝ) := by
  obtain ⟨hw0, hw3, -, -⟩ := wCol_props (q := q) h6
  have hw1 : ∑ c, |wCol q c| = 4 := by
    rcases q_mod3 h6 with h | h <;> simp [wCol, h, Fin.sum_univ_three]
  rw [shift_free sh h2, shift_free sh h2]
  have := colfree_core (by omega) (wCol q) hw0 hw3 ((shB sh 0).val : ℤ)
    (fun n => (colH q (wCol q) n + shB sh 0).val) (fun n c => (colJ q ellCol n + shB' sh c).val)
    (fun n => ZMod.val_lt _) (fun n => by simp) (fun n c => ZMod.val_lt _)
    (v + sh0 sh) (w + sh0 sh) (by intro h; exact hvw (add_right_cancel h))
  rw [hw1] at this
  push_cast at this
  convert this using 2
  ring

end Z3NetC.Proofs

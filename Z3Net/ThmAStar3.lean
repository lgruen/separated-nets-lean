/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmAUstar

@[expose] public section

/-!
# Theorem A, part 6: the design `U*_3` and `a*_3 = 2`

V14 stage S4 (an S5 item taken early). For `s = 3` (places `∞, 0, 1`, `S = ∅`, `R_S = ℤ`) every
`γ_j` is `1` (`gam3`), the printed columns satisfy the characterization of `def:Ustar`
(`isUstar3`), so they are the columns of `U*_3` by uniqueness (`Ustar_cols_unique`), and the
printed `F_0`, `F_1` and `a*_3 = 2` follow by evaluation (`Ustar3_display_core`, `aStar_three_core`).
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

/-- The printed `F_0` of `U*_3` (coordinate order `∞, 0, 1`). -/
def F0_3 : Fin 3 → Fin 3 → ℤ := ![![-2, 1, 1], ![1, -2, -1], ![1, 1, -2]]

/-- The partial sums `M^(1) = F_0 + F_1` of the printed `U*_3`. -/
def M1_3 : Fin 3 → Fin 3 → ℤ := ![![-2, -1, 0], ![-1, -2, 1], ![0, 0, -2]]

/-- The printed columns `E_{d,0}`, `E_{d,1}` (and `0` beyond level `1`). -/
def B3 (d : Fin 3) (j : ℕ) (c : Fin 3) : ℤ :=
  if c = d then 0 else if j = 0 then F0_3 c d else if j = 1 then M1_3 c d else 0

/-- The polynomial of `E_{d,j}`: `1` at level `0`; `X - 1` (columns `∞`, `0`) or `X` (column `1`)
at level `1`. -/
def g3 (d : Fin 3) (j : ℕ) : Polynomial ℚ :=
  if j = 0 then 1 else X - C (if d = 2 then 0 else 1)

lemma g3_natDegree (d : Fin 3) (j : ℕ) (hj : j ≤ 1) : (g3 d j).natDegree ≤ j := by
  by_cases h : j = 0
  · simp [g3, h]
  · simp only [g3, h, ite_false]; rw [natDegree_X_sub_C]; omega

lemma g3_coeff (d : Fin 3) (j : ℕ) (hj : j ≤ 1) : (g3 d j).coeff j = 1 := by
  by_cases h : j = 0
  · subst h; simp [g3]
  · simp only [g3, h, ite_false]; rw [show j = 1 by omega]; split_ifs <;> simp [coeff_X, coeff_one]

lemma B3_rep (d : Fin 3) (j : ℕ) (hj : j ≤ 1) (c : Fin 3) (hc : c ≠ d) :
    (B3 d j c : ℚ) = wQ c d * (g3 d j).eval (yQ c d) := by
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>
    fin_cases d <;> fin_cases c <;> simp_all [B3, g3, F0_3, M1_3, wQ, yQ, wN, yN, placeA] <;>
    norm_num

lemma B3_inLam (d : Fin 3) (j : ℕ) (hj : j ≤ 1) : InLam d j (B3 d j) :=
  ⟨by simp [B3], g3 d j, g3_natDegree d j hj, B3_rep d j hj⟩

lemma B3_kappa (d : Fin 3) (j : ℕ) (hj : j ≤ 1) : kappa d j (B3 d j) = 1 := by
  rw [kappa_eq (by norm_num) (by omega) _ (g3 d j) (g3_natDegree d j hj) (B3_rep d j hj),
    g3_coeff d j hj]

/-- For `s = 3` every `γ_j` is `1` (`R_S = ℤ`). -/
lemma gam3 (d : Fin 3) (j : ℕ) (hj : j ≤ 1) : gamS d j = 1 := by
  obtain ⟨hpos, hspec⟩ := gamS_spec (s := 3) (by norm_num) d j hj
  obtain ⟨z, hz⟩ := (hspec 1).1 ⟨B3 d j, B3_inLam d j hj, B3_kappa d j hj⟩
  obtain ⟨E, hE, hEk⟩ := (hspec (gamS d j)).2 ⟨1, by simp⟩
  obtain ⟨w, e, hw⟩ := kappa_RS (by norm_num) d j E
  have hw' : gamS d j = w := by rw [← hEk, hw]; simp
  rw [hw'] at hz hpos
  have hw0 : (0 : ℤ) < w := by exact_mod_cast hpos
  have hzw : z * w = 1 := by exact_mod_cast hz.symm
  have : w = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hzw with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · omega
  rw [hw', this]; simp

/-- The printed columns satisfy the characterization of `def:Ustar` (for `s = 3`). -/
lemma isUstar3 (d : Fin 3) : IsUstarCols d (B3 d) := by
  refine ⟨fun j hj => ⟨B3_inLam d j hj, by rw [B3_kappa d j hj, gam3 d j hj],
    fun _ => -1 / 2, ?_, fun i hi => ?_⟩, fun j hj => ?_⟩
  · intro i hi
    have hj1 : j = 1 := by omega
    have hi0 : i = 0 := by omega
    subst hj1 hi0
    fin_cases d <;> simp [Fin.sum_univ_three, B3, F0_3, M1_3] <;> norm_num
  · norm_num
  · funext c; simp [B3, show j ≠ 0 by omega, show j ≠ 1 by omega]

lemma Ecol3 (d : Fin 3) : Ecol d = B3 d :=
  (Ustar_cols_unique_core (s := 3) (by norm_num) d (B3 d) (isUstar3 d)).symm

lemma alphaS3 (c : Fin 3) : alphaS c = 2 := by
  unfold alphaS
  simp only [Ecol3]
  fin_cases c <;> decide

theorem aStar_three_core : aStar 3 = 2 := by
  unfold aStar
  simp only [alphaS3]
  decide

/-- The display after `def:Ustar`: `U*_3 = (F_0, F_1)` with the printed matrices. -/
theorem Ustar3_display_core :
    (∀ c d : Fin 3, UstarF 3 0 c d = ![![-2, 1, 1], ![1, -2, -1], ![1, 1, -2]] c d) ∧
      (∀ c d : Fin 3, UstarF 3 1 c d = ![![0, -2, -1], ![-2, 0, 2], ![-1, -1, 0]] c d) ∧
      ∀ n, 2 ≤ n → ∀ c d : Fin 3, UstarF 3 n c d = 0 := by
  refine ⟨fun c d => ?_, fun c d => ?_, fun n hn c d => ?_⟩
  · unfold UstarF; simp only [Ecol3, alphaS3]
    fin_cases c <;> fin_cases d <;> decide
  · unfold UstarF; simp only [Ecol3, alphaS3]
    fin_cases c <;> fin_cases d <;> decide
  · unfold UstarF
    split_ifs <;> first | rfl | omega

end

end Z3NetA.Proofs

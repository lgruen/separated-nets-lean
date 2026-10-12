/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmAUstar
public import Z3Net.DeficitDefs

@[expose] public section

/-!
# The level-`0` layer of `U*_4` is the printed `s = 4` frame layer (`prop:k1designs`(1))

V14 stage S4 (an S5 item taken early). For `s = 4` (places `∞, 0, 1, 2`, `S = {2}`) the
level-`0` columns of `U*_4` are the generators of `Λ_0` with `κ_0 > 0`; `γ_0 = 1, 2, 1, 2` for the
columns `∞, 0, 1, 2` (`gam4`), and the off-diagonal part of the printed layer `k1Frame4`
(`app:designs`, used for `K₁ = 2` in `prop:k1designs`(1)) is the level-`0` layer of `U*_4`
(`Ustar4_level0_core`).
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

/-- The column `d` of the printed layer (entry `0` at the row `d`). -/
def V4 (d : Fin 4) (c : Fin 4) : ℤ := if c = d then 0 else k1Frame4 c d

/-- `γ_0` of the columns `∞, 0, 1, 2`. -/
def gam4v (d : Fin 4) : ℚ := if d = 1 ∨ d = 3 then 2 else 1

lemma V4_rep (d c : Fin 4) (hc : c ≠ d) :
    (V4 d c : ℚ) = wQ c d * (C (gam4v d) : Polynomial ℚ).eval (yQ c d) := by
  fin_cases d <;> fin_cases c <;> simp_all [V4, gam4v, k1Frame4, wQ, wN, placeA] <;> norm_num

lemma V4_inLam (d : Fin 4) : InLam d 0 (V4 d) :=
  ⟨by simp [V4], C (gam4v d), by simp, V4_rep d⟩

lemma V4_kappa (d : Fin 4) : kappa d 0 (V4 d) = gam4v d := by
  rw [kappa_eq (by norm_num) (by norm_num) _ _ (by simp) (V4_rep d), coeff_C_zero]

/-- Every `κ_0(E)`, `E ∈ Λ_0`, is an integer multiple of `gam4v d`. -/
lemma kappa4_mul (d : Fin 4) (E : Fin 4 → ℤ) (hE : InLam d 0 E) :
    ∃ m : ℤ, kappa d 0 E = m * gam4v d := by
  obtain ⟨_, g, hg, hrep⟩ := hE
  have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_le_zero hg
  have hk : kappa d 0 E = g.coeff 0 := kappa_eq (by norm_num) (by norm_num) E g hg hrep
  have hr : ∀ c, c ≠ d → (E c : ℚ) = wQ c d * g.coeff 0 := by
    intro c hc; rw [hrep c hc, hgC, eval_C, coeff_C_zero]
  rw [hk]
  fin_cases d
  · refine ⟨E 1, ?_⟩
    have := hr 1 (by decide); simp [wQ, wN, gam4v] at this ⊢; linarith
  · refine ⟨E 3, ?_⟩
    have := hr 3 (by decide); simp [wQ, wN, placeA, gam4v] at this ⊢; norm_num at this; linarith
  · refine ⟨E 0, ?_⟩
    have := hr 0 (by decide); simp [wQ, wN, gam4v] at this ⊢; linarith
  · refine ⟨-E 1, ?_⟩
    have := hr 1 (by decide); simp [wQ, wN, placeA, gam4v] at this ⊢; norm_num at this; linarith

lemma gam4 (d : Fin 4) : gamS d 0 = gam4v d := by
  obtain ⟨hpos, hspec⟩ := gamS_spec (s := 4) (by norm_num) d 0 (by norm_num)
  have ha : 0 < gam4v d := by unfold gam4v; split_ifs <;> norm_num
  obtain ⟨z, hz⟩ := (hspec (gam4v d)).1 ⟨V4 d, V4_inLam d, V4_kappa d⟩
  obtain ⟨E, hE, hEk⟩ := (hspec (gamS d 0)).2 ⟨1, by simp⟩
  obtain ⟨m, hm⟩ := kappa4_mul d E hE
  rw [hEk] at hm
  -- `a = z γ`, `γ = m a`
  have h1 : (z : ℚ) * m = 1 := by
    have : gam4v d = z * (m * gam4v d) := by rw [← hm]; exact hz
    have h2 : gam4v d * ((z : ℚ) * m - 1) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h ha.ne'
    · linarith
  have hm0 : (0 : ℚ) < m := by
    by_contra h; push Not at h
    have : gamS d 0 ≤ 0 := by rw [hm]; exact mul_nonpos_of_nonpos_of_nonneg h ha.le
    linarith
  have hzm : z * m = 1 := by exact_mod_cast h1
  have hm1 : m = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hzm with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · have : (m : ℚ) = -1 := by exact_mod_cast h
      linarith
  rw [hm, hm1]; simp

lemma Ecol4_zero (d : Fin 4) : Ecol d 0 = V4 d := by
  have hE := (isUstarCols_iff d _).1 (Ustar_cols_core (s := 4) (by norm_num) d)
  have hBel : Below d (Ecol d) 0 := fun i hi => absurd hi (by omega)
  refine (level_unique (by norm_num) d (Ecol d) 0 (by norm_num) hBel _ _ (hE.1 0 (by norm_num))
    ⟨V4_inLam d, by rw [V4_kappa, gam4], fun _ => 0, fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩)

/-- `prop:k1designs`(1): the off-diagonal part of the printed `s = 4` frame layer is the level-`0`
layer of `U*_4`. -/
theorem Ustar4_level0_core (c d : Fin 4) (hcd : c ≠ d) : UstarF 4 0 c d = k1Frame4 c d := by
  have : UstarF 4 0 c d = Ecol d 0 c := by simp [UstarF, hcd]
  rw [this, Ecol4_zero]
  simp [V4, hcd]

end

end Z3NetA.Proofs

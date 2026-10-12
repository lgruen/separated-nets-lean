/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmAAdelic

@[expose] public section

/-!
# Theorem A, part 5: Babai rounding along the flag (`lem:babai`) and the design `U*_s`

V14 stage S4.

* `babai_core`: the rounded vector `E_j = v − ∑_{i<j} ⌊c_i + 1/2⌋ E_i` lies in `Λ_j`, has
  `κ_j(E_j) = γ_j` and `‖E_j‖ ≤ h_j + ½ ∑_{i<j} ‖E_i‖`.
* `babai_growth_core`, `babai_flag_core`: the consequence `‖E_i‖ ≤ (3/2)^i H`.
* `U*_s`: the projection of `def:Ustar` is Mathlib's orthogonal projection onto `V_{j-1} ⊗ ℝ`
  (`Ustar_proj_core`), its columns satisfy the bound of `lem:babai` (`Ustar_babai_core`),
  `‖E_{d,i}‖ ≤ (3/2)^i H` if `h_{d,i} ≤ H` (`Ustar_growth_core`), and
  `a*_s ≤ (s-1)(3/2)^{s-2} H` if every `h_{d,j} ≤ H` (`aStar_le_core`).
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

variable {s : ℕ} [NeZero s]

lemma round_abs (x : ℝ) : |x - ⌊x + 1 / 2⌋| ≤ 1 / 2 := by
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]; constructor <;> linarith

/-- **`lem:babai`**. -/
theorem babai_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (B : ℕ → Fin s → ℤ)
    (hB : ∀ i < j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) (v : Fin s → ℤ)
    (hv : InLam d j v) (hvk : kappa d j v = gamS d j) :
    (∃ cf : ℕ → ℝ, (Vlt d j).starProjection (colE v) = ∑ i ∈ range j, cf i • colE (B i)) ∧
      ∀ cf : ℕ → ℝ, (Vlt d j).starProjection (colE v) = ∑ i ∈ range j, cf i • colE (B i) →
        InLam d j (v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • B i) ∧
        kappa d j (v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • B i) = gamS d j ∧
        ‖colE (v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • B i)‖ ≤
          hS d j + 1 / 2 * ∑ i ∈ range j, ‖colE (B i)‖ := by
  refine ⟨?_, fun cf hcf => ?_⟩
  · obtain ⟨cf, hcf⟩ := proj_exists hs d B j (by omega) hB v
    exact ⟨fun i => cf i, proj_of_projCoef hs d B j (by omega) hB v cf hcf⟩
  set t : ℕ → ℤ := fun i => ⌊cf i + 1 / 2⌋
  have hsum : InLam d j (∑ i ∈ range j, t i • B i) :=
    inLam_sum _ _ B fun i hi => inLam_mono (by simp at hi; omega) (hB i (by simpa using hi)).1
  refine ⟨inLam_sub hv hsum, ?_, ?_⟩
  · rw [kappa_sub, kappa_sum, hvk]
    have : ∑ i ∈ range j, (t i : ℚ) * kappa d j (B i) = 0 :=
      sum_eq_zero fun i hi => by
        rw [kappa_low hs (show i < j by simpa using hi) hj (hB i (by simpa using hi)).1, mul_zero]
    rw [this, sub_zero]
  · set B' : ℕ → Fin s → ℤ := fun i => if i = j then v else B i
    have hB' : Flag d B' j := by
      intro i hi
      by_cases h : i = j
      · subst h; simp only [B', ite_true]; exact ⟨hv, hvk⟩
      · simp only [B', h, ite_false]; exact hB i (by omega)
    have hu : uvec d B' j = colE v - (Vlt d j).starProjection (colE v) := by
      simp [uvec, B']
    have hE : colE (v - ∑ i ∈ range j, t i • B i) =
        uvec d B' j + ∑ i ∈ range j, (cf i - t i) • colE (B i) := by
      rw [hu, hcf, colE_sub, colE_sum]
      simp only [sub_smul, sum_sub_distrib]
      abel
    rw [hE, hS_eq hs d B' j hj hB']
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (round_abs (cf i)) (norm_nonneg _)

/-- The recursion of `lem:babai`: `x_i ≤ H + ½ ∑_{l<i} x_l` for `i ≤ j` gives `x_i ≤ (3/2)^i H`. -/
theorem babai_growth_core (x : ℕ → ℝ) (H : ℝ) (j : ℕ)
    (hx : ∀ i ≤ j, x i ≤ H + 1 / 2 * ∑ l ∈ range i, x l) : ∀ i ≤ j, x i ≤ (3 / 2) ^ i * H := by
  have hT : ∀ i ≤ j + 1, ∑ l ∈ range i, x l ≤ 2 * H * ((3 / 2) ^ i - 1) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hx i (by omega)
      rw [sum_range_succ, pow_succ]
      nlinarith
  intro i hi
  have h1 := hT i (by omega)
  have h2 := hx i hi
  nlinarith

/-- **`lem:babai`**, the consequence: if `E_0, …, E_j` are all obtained by Babai rounding along the
flag and `h_i ≤ H` for every `i ≤ j`, then `‖E_i‖ ≤ (3/2)^i H` for every `i ≤ j`. -/
theorem babai_flag_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (B : ℕ → Fin s → ℤ)
    (hB : ∀ i ≤ j, ∃ v : Fin s → ℤ, ∃ cf : ℕ → ℝ, InLam d i v ∧ kappa d i v = gamS d i ∧
      (Vlt d i).starProjection (colE v) = ∑ l ∈ range i, cf l • colE (B l) ∧
      B i = v - ∑ l ∈ range i, ⌊cf l + 1 / 2⌋ • B l)
    (H : ℝ) (hH : ∀ i ≤ j, hS d i ≤ H) : ∀ i ≤ j, ‖colE (B i)‖ ≤ (3 / 2) ^ i * H := by
  have key : ∀ i ≤ j, (InLam d i (B i) ∧ kappa d i (B i) = gamS d i) ∧
      ‖colE (B i)‖ ≤ hS d i + 1 / 2 * ∑ l ∈ range i, ‖colE (B l)‖ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      obtain ⟨v, cf, hv, hvk, hP, hBi⟩ := hB i hi
      have hbel : ∀ l < i, InLam d l (B l) ∧ kappa d l (B l) = gamS d l :=
        fun l hl => (ih l hl (by omega)).1
      obtain ⟨h1, h2, h3⟩ := (babai_core hs d i (by omega) B hbel v hv hvk).2 cf hP
      rw [← hBi] at h1 h2 h3
      exact ⟨⟨h1, h2⟩, h3⟩
  refine babai_growth_core (fun i => ‖colE (B i)‖) H j fun i hi => ?_
  exact (key i hi).2.trans (by linarith [hH i hi])

/-! ## The design `U*_s` -/

theorem Ustar_proj_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (E : Fin s → ℤ)
    (cf : ℕ → ℚ) :
    ProjCoef (Ecol d) j E cf ↔
      (Vlt d j).starProjection (colE E) = ∑ i ∈ range j, (cf i : ℝ) • colE (Ecol d i) := by
  have hB : ∀ i < j, InLam d i (Ecol d i) ∧ kappa d i (Ecol d i) = gamS d i :=
    fun i hi => Ecol_spec hs d i (by omega)
  exact ⟨proj_of_projCoef hs d _ j (by omega) hB E cf, projCoef_of_proj hs d _ j (by omega) hB E cf⟩

theorem Ustar_babai_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ‖colE (Ecol d j)‖ ≤ hS d j + 1 / 2 * ∑ i ∈ range j, ‖colE (Ecol d i)‖ := by
  have hB : ∀ i < j, InLam d i (Ecol d i) ∧ kappa d i (Ecol d i) = gamS d i :=
    fun i hi => Ecol_spec hs d i (by omega)
  obtain ⟨hl, hk, cf, hcf, hb⟩ := (Ustar_cols_core hs d).1 j hj
  have hP := proj_of_projCoef hs d _ j (by omega) hB _ cf hcf
  have h := ((babai_core hs d j hj (Ecol d) hB _ hl hk).2 (fun i => cf i) hP).2.2
  have h0 : ∑ i ∈ range j, ⌊(cf i : ℝ) + 1 / 2⌋ • Ecol d i = 0 := by
    refine sum_eq_zero fun i hi => ?_
    have hbi := hb i (by simpa using hi)
    have : ⌊(cf i : ℝ) + 1 / 2⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      have a1 : (((-1 / 2 : ℚ)) : ℝ) ≤ cf i := Rat.cast_le.2 hbi.1
      have a2 : (cf i : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.2 hbi.2
      push_cast at a1 a2
      constructor <;> linarith
    rw [this, zero_smul]
  rw [h0, sub_zero] at h
  exact h

theorem Ustar_growth_core (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (H : ℝ)
    (hH : ∀ i ≤ j, hS d i ≤ H) : ∀ i ≤ j, ‖colE (Ecol d i)‖ ≤ (3 / 2) ^ i * H :=
  babai_growth_core (fun i => ‖colE (Ecol d i)‖) H j fun i hi =>
    (Ustar_babai_core hs d i (by omega)).trans (by linarith [hH i hi])

lemma hS_nonneg (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) : 0 ≤ hS d j := by
  rw [hS_eq hs d (Ecol d) j hj (flag_Ecol hs d j hj)]; exact norm_nonneg _

/-- The reduction of the bound on `a*_s` to the local bounds (proof of `thm:A`): if `h_{d,j} ≤ H`
for every column `d` and level `j ≤ s - 2`, then `a*_s ≤ (s - 1)(3/2)^{s-2} H`. -/
theorem aStar_le_core (hs : 3 ≤ s) (H : ℝ) (hH : ∀ d : Fin s, ∀ j ≤ s - 2, hS d j ≤ H) :
    (∀ d c : Fin s, ∀ j ≤ s - 2, |(Ecol d j c : ℝ)| ≤ (3 / 2) ^ (s - 2) * H) ∧
      (aStar s : ℝ) ≤ ((s : ℝ) - 1) * ((3 / 2) ^ (s - 2) * H) := by
  have hH0 : 0 ≤ H := (hS_nonneg hs 0 0 (by omega)).trans (hH 0 0 (by omega))
  have hent : ∀ d : Fin s, ∀ j ≤ s - 2, ∀ c : Fin s,
      (((Ecol d j c).natAbs : ℕ) : ℝ) ≤ (3 / 2) ^ (s - 2) * H := by
    intro d j hj c
    have h1 : (((Ecol d j c).natAbs : ℕ) : ℝ) ≤ ‖colE (Ecol d j)‖ := by
      have := PiLp.norm_apply_le (colE (Ecol d j)) c
      rw [colE_apply, Real.norm_eq_abs] at this
      rw [Nat.cast_natAbs, Int.cast_abs]; exact this
    refine h1.trans ((Ustar_growth_core hs d j hj H (fun i _ => hH d i (by omega)) j le_rfl).trans ?_)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hH0
  have hal : ∀ c : Fin s, (alphaS c : ℝ) ≤ ((s : ℝ) - 1) * ((3 / 2) ^ (s - 2) * H) := by
    intro c
    unfold alphaS
    push_cast
    have hcard : ((univ.filter fun d : Fin s => d ≠ c).card : ℝ) = (s : ℝ) - 1 := by
      rw [card_rows]; push_cast [show 1 ≤ s by omega]; ring
    rw [← hcard, ← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun d _ => ?_
    obtain ⟨j, hj, hjs⟩ := exists_mem_eq_sup (range (s - 1)) (nonempty_range_iff.2 (by omega))
      fun j => (Ecol d j c).natAbs
    rw [hjs]
    exact hent d j (by simp at hj; omega) c
  refine ⟨fun d c j hj => ?_, ?_⟩
  · have := hent d j hj c
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  obtain ⟨c, -, hc⟩ := exists_mem_eq_sup (univ : Finset (Fin s)) univ_nonempty fun c => alphaS c
  unfold aStar
  rw [hc]
  exact hal c

end

end Z3NetA.Proofs

module
public import Mathlib
public import Z3Net.S2Defs
public import Z3Net.SkGBase
public import Z3Net.SkGArg

@[expose] public section

/-!
# Entry S2, `lem:G2N1`: (N1) for the Gaussian matrix `A(B)`

* `G2N1_a`: `c_j² + 1 < p` (from `‖A_j‖₁ ≥ |Ω_{r-1}|` and `c_1² + 1 ≤ 5 B²`);
* `G2N1_b`: entries and `2 × 2` minors of `A(B)` are nonzero mod `p`: a minor is
  `N(Ω_l) · w` with `w = Im` resp. `Re` of `ω_{l+1} ⋯ ω_{l'}`, which is positive by
  `gauss_prod_pos` (the arctangent condition) and `< p`, and `N(Ω_l)` is a product of the
  `c_j² + 1 ∈ (0, p)`;
* `G2N1_c`: the arctangent condition for `s ≤ 8`, `B ≥ F + 1`, and for `B > (2(s-3)/π)²`.
-/

namespace Z3NetF.Proofs

open Finset

namespace SkG

/-- `c_0² + 1 ≤ 5 B²` for `B ≥ 1`. -/
lemma cG0_sq_le (B : ℕ) (hB : 1 ≤ B) : cG B 0 ^ 2 + 1 ≤ 5 * (B : ℤ) ^ 2 := by
  rw [cG_zero]
  set q := Nat.sqrt (2 * B ^ 2) with hq
  have h1 : q * q ≤ 2 * B ^ 2 := Nat.sqrt_le (2 * B ^ 2)
  have : (q + 1) ^ 2 + 1 ≤ 5 * B ^ 2 := by
    rcases le_or_gt q B with h | h
    · nlinarith
    · have hB2 : 2 ≤ B := by
        by_contra hc
        have : B = 1 := by omega
        subst this
        nlinarith
      have : q < 2 * B := by nlinarith
      nlinarith
  exact_mod_cast this

/-- `B · ‖A‖ ≥ c_0² + 1` (the core of `lem:G2N1`(a)). -/
lemma cG0_le_BnormA (s B : ℕ) (hs : 5 ≤ s) (hB : 1 ≤ B) :
    cG B 0 ^ 2 + 1 ≤ (B : ℤ) * normA s B := by
  set Ω := gaussOmega (cG B) (s - 3) with hΩ
  have hT := normA_ge s B (by omega)
  have hN := norm_le_abs_sq Ω
  have hNe : Ω.norm = (cG B 0 ^ 2 + 1) * (cG B 1 ^ 2 + 1) ^ (s - 4) := by
    rw [hΩ, show s - 3 = (s - 4) + 1 by omega, norm_gaussOmega_cG]
  have hc1 : 2 ≤ cG B 1 := cGj_ge B 1 (by omega) hB
  have h5 : (5 : ℤ) ≤ (cG B 1 ^ 2 + 1) ^ (s - 4) := by
    have : (5 : ℤ) ≤ cG B 1 ^ 2 + 1 := by nlinarith
    calc (5 : ℤ) ≤ cG B 1 ^ 2 + 1 := this
      _ = (cG B 1 ^ 2 + 1) ^ 1 := (pow_one _).symm
      _ ≤ (cG B 1 ^ 2 + 1) ^ (s - 4) := pow_le_pow_right₀ (by nlinarith) (by omega)
  have hc0 := cG0_sq_le B hB
  have hpos : 0 < cG B 0 ^ 2 + 1 := by positivity
  have hT0 : 0 ≤ |Ω.re| + |Ω.im| := by positivity
  have hnA := normA_nonneg s B
  have hBz : (1 : ℤ) ≤ B := by exact_mod_cast hB
  -- (B ‖A‖)² ≥ B² · 5 (c_0² + 1) ≥ (c_0² + 1)²
  have h1 : 5 * (cG B 0 ^ 2 + 1) ≤ normA s B ^ 2 := by
    have : 5 * (cG B 0 ^ 2 + 1) ≤ Ω.norm := by rw [hNe]; nlinarith
    nlinarith
  have h2 : (cG B 0 ^ 2 + 1) ^ 2 ≤ ((B : ℤ) * normA s B) ^ 2 := by
    have : (cG B 0 ^ 2 + 1) ^ 2 ≤ (5 * (B : ℤ) ^ 2) * (cG B 0 ^ 2 + 1) := by nlinarith
    nlinarith
  exact (pow_le_pow_iff_left₀ hpos.le (mul_nonneg (by positivity) hnA) two_ne_zero).mp h2

end SkG

theorem G2N1_a (s B p : ℕ) (hs : 5 ≤ s) (hB : 1 ≤ B) (hp : (B : ℤ) * (1 + normA s B) < p) (j : ℕ)
    (hj : j + 4 ≤ s) : cG B j ^ 2 + 1 < p := by
  have h := SkG.cG0_le_BnormA s B hs hB
  have hj0 := SkG.cGj_le_cG0 B j
  have hjpos := SkG.cG_pos B j
  have : cG B j ^ 2 ≤ cG B 0 ^ 2 := by nlinarith
  nlinarith

namespace SkG

lemma zmod_ne_zero_of_abs_lt {p : ℕ} (w : ℤ) (h0 : w ≠ 0) (hw : |w| < p) :
    ((w : ℤ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hd; exact h0 (Int.eq_zero_of_abs_lt_dvd hd hw)

lemma abs_lt_of_sq_le {w n : ℤ} {p : ℕ} (h : w ^ 2 ≤ n) (hn : n < (p : ℤ) ^ 2) : |w| < p :=
  abs_lt_of_sq_lt_sq (lt_of_le_of_lt h hn) (by positivity)

lemma im_star_mul (u v : GaussianInt) : (star u * v).im = u.re * v.im - v.re * u.im := by
  simp [Zsqrtd.im_mul]; ring

lemma star_mul_self_mul (u w : GaussianInt) : star u * (u * w) = (u.norm : GaussianInt) * w := by
  rw [Zsqrtd.norm_eq_mul_conj]; ring

lemma norm_gaussOmega_split (c : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    gaussOmega c b = gaussOmega c a * ∏ j ∈ Ico a b, (⟨c j, 1⟩ : GaussianInt) := by
  rw [gaussOmega, gaussOmega, prod_range_mul_prod_Ico _ hab]

lemma norm_nonneg' (z : GaussianInt) : 0 ≤ z.norm := by
  rw [norm_eq]; positivity

lemma norm_pos_of_gaussOmega (c : ℕ → ℤ) (l : ℕ) : 1 ≤ (gaussOmega c l).norm := by
  rw [norm_gaussOmega]
  exact one_le_prod₀ fun j _ => by nlinarith [sq_nonneg (c j)]

end SkG

theorem G2N1_b (s B p : ℕ) [Fact p.Prime] (hs : 5 ≤ s) (hB : 1 ≤ B)
    (hp : (B : ℤ) * (1 + normA s B) < p)
    (harc : ∑ j ∈ range (s - 3), Real.arctan (1 / (cG B j : ℝ)) < Real.pi / 2) :
    (∀ (i : Fin 2) (d : ℕ), d + 2 < s → ((AG s B i d : ℤ) : ZMod p) ≠ 0) ∧
      ∀ d d', d + 2 < s → d' + 2 < s → d ≠ d' →
        ((AG s B 0 d * AG s B 1 d' - AG s B 0 d' * AG s B 1 d : ℤ) : ZMod p) ≠ 0 := by
  classical
  set c := cG B with hc
  set Ω := gaussOmega c (s - 3) with hΩ
  have hT := SkG.normA_ge s B (by omega)
  have hN := SkG.norm_le_abs_sq Ω
  have hnA := SkG.normA_nonneg s B
  have hBz : (1 : ℤ) ≤ B := by exact_mod_cast hB
  have hnp : normA s B < p := by nlinarith
  have hNp : Ω.norm < (p : ℤ) ^ 2 := by
    have h0 : 0 ≤ |Ω.re| + |Ω.im| := by positivity
    nlinarith
  have harcS : ∀ S ⊆ range (s - 3), ∑ j ∈ S, Real.arctan (1 / (c j : ℝ)) < Real.pi / 2 :=
    fun S hS => lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg hS fun j _ _ =>
      (Real.arctan_pos.mpr (by have := SkG.cG_pos B j; positivity)).le) harc
  have hposS : ∀ S ⊆ range (s - 3), 0 < (∏ j ∈ S, (⟨c j, 1⟩ : GaussianInt)).re ∧
      (S.Nonempty → 0 < (∏ j ∈ S, (⟨c j, 1⟩ : GaussianInt)).im) :=
    fun S hS => SkG.gauss_prod_pos S c (fun j _ => SkG.cG_pos B j) (harcS S hS)
  have hbnd : ∀ w : ℤ, w ^ 2 ≤ Ω.norm → |w| < p := fun w hw => SkG.abs_lt_of_sq_le hw hNp
  -- the columns
  have hcol : ∀ d, d + 2 < s → (SkG.gcol (s - 2) c d).re ≠ 0 ∧ (SkG.gcol (s - 2) c d).im ≠ 0 ∧
      (SkG.gcol (s - 2) c d).norm ≤ Ω.norm := by
    intro d hd
    refine ⟨?_, ?_, by have := SkG.norm_gcol_le (s - 2) c d; rwa [show s - 2 - 1 = s - 3 by omega] at this⟩
    all_goals
      unfold SkG.gcol
      split_ifs with h
      · have := hposS (range (d + 1)) (range_subset_range.mpr (by omega))
        have hne : (range (d + 1)).Nonempty := ⟨0, by simp⟩
        first
          | exact (this.1).ne'
          | exact (this.2 hne).ne'
      · have := hposS (range (s - 3)) (subset_refl _)
        have hne : (range (s - 3)).Nonempty := ⟨0, by simp; omega⟩
        have e : s - 2 - 1 = s - 3 := by omega
        simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, e]
        have := this.2 hne
        simp only [gaussOmega] at *
        omega
  refine ⟨fun i d hd => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hcol d hd
    fin_cases i
    · simp only [Fin.zero_eta, SkG.AG_zero]
      exact SkG.zmod_ne_zero_of_abs_lt _ h1 (hbnd _ ((SkG.re_sq_le_norm _).trans h3))
    · simp only [Fin.mk_one, SkG.AG_one]
      exact SkG.zmod_ne_zero_of_abs_lt _ h2 (hbnd _ ((SkG.im_sq_le_norm _).trans h3))
  · -- the minors
    have key : ∀ d d', d < d' → d' + 2 < s →
        ((AG s B 0 d * AG s B 1 d' - AG s B 0 d' * AG s B 1 d : ℤ) : ZMod p) ≠ 0 := by
      intro d d' hdd hd'
      set u := gaussOmega c (d + 1) with hu
      have hgu : SkG.gcol (s - 2) c d = u := by
        unfold SkG.gcol; rw [if_pos (by omega)]
      have hmin : AG s B 0 d * AG s B 1 d' - AG s B 0 d' * AG s B 1 d =
          (star u * SkG.gcol (s - 2) c d').im := by
        rw [SkG.im_star_mul, SkG.AG_zero, SkG.AG_one, SkG.AG_zero, SkG.AG_one, hgu]
      -- `star u * v = N(u) * w` with `0 < w`, `w² ≤ N(Ω)`
      obtain ⟨w, hw, hw0, hwb⟩ : ∃ w : ℤ, (star u * SkG.gcol (s - 2) c d').im = u.norm * w ∧
          0 < w ∧ w ^ 2 ≤ Ω.norm := by
        have hNu := SkG.norm_pos_of_gaussOmega c (d + 1)
        by_cases h' : d' + 1 < s - 2
        · set P := ∏ j ∈ Ico (d + 1) (d' + 1), (⟨c j, 1⟩ : GaussianInt) with hP
          have hv : SkG.gcol (s - 2) c d' = u * P := by
            unfold SkG.gcol; rw [if_pos h', hu, hP, SkG.norm_gaussOmega_split c (show d + 1 ≤ d' + 1 by omega)]
          have hpp := hposS (Ico (d + 1) (d' + 1)) (by
            intro x hx; simp at hx ⊢; omega)
          refine ⟨P.im, ?_, hpp.2 ⟨d + 1, by simp; omega⟩, ?_⟩
          · rw [hv, SkG.star_mul_self_mul, Zsqrtd.im_smul]
          · have e1 : (gaussOmega c (d' + 1)).norm = u.norm * P.norm := by
              rw [SkG.norm_gaussOmega_split c (show d + 1 ≤ d' + 1 by omega), Zsqrtd.norm_mul]
            have e2 := SkG.norm_gaussOmega_mono c (show d' + 1 ≤ s - 3 by omega)
            have e3 := SkG.im_sq_le_norm P
            have e4 := SkG.norm_nonneg' P
            nlinarith
        · have hd'e : d' = s - 3 := by omega
          set P := ∏ j ∈ Ico (d + 1) (s - 3), (⟨c j, 1⟩ : GaussianInt) with hP
          have hv : SkG.gcol (s - 2) c d' = (⟨0, 1⟩ : GaussianInt) * (u * P) := by
            unfold SkG.gcol; rw [if_neg h', show s - 2 - 1 = s - 3 by omega, hu, hP,
              SkG.norm_gaussOmega_split c (show d + 1 ≤ s - 3 by omega)]
          have hpp := hposS (Ico (d + 1) (s - 3)) (by
            intro x hx; simp at hx ⊢; omega)
          refine ⟨P.re, ?_, hpp.1, ?_⟩
          · rw [hv, mul_left_comm, SkG.star_mul_self_mul]
            simp [Zsqrtd.im_mul]
          · have e1 : Ω.norm = u.norm * P.norm := by
              rw [hΩ, SkG.norm_gaussOmega_split c (show d + 1 ≤ s - 3 by omega), Zsqrtd.norm_mul]
            have e3 := SkG.re_sq_le_norm P
            have e4 := SkG.norm_nonneg' P
            nlinarith
      rw [hmin, hw, Int.cast_mul]
      refine mul_ne_zero ?_ (SkG.zmod_ne_zero_of_abs_lt _ hw0.ne' (hbnd _ hwb))
      rw [hu, SkG.norm_gaussOmega, Int.cast_prod, prod_ne_zero_iff]
      intro j hj
      simp only [mem_range] at hj
      have ha := G2N1_a s B p hs hB hp j (by omega)
      exact SkG.zmod_ne_zero_of_abs_lt _ (by nlinarith [sq_nonneg (c j)])
        (by rw [abs_of_nonneg (by positivity)]; exact ha)
    intro d d' hd hd' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key d d' h hd'
    · have := key d' d h hd
      rw [show AG s B 0 d * AG s B 1 d' - AG s B 0 d' * AG s B 1 d =
        -(AG s B 0 d' * AG s B 1 d - AG s B 0 d * AG s B 1 d') by ring, Int.cast_neg]
      exact neg_ne_zero.mpr this

theorem G2N1_c (s B : ℕ) (hs : 5 ≤ s)
    (h : (s ≤ 8 ∧ Fs s + 1 ≤ B) ∨ (2 * ((s : ℝ) - 3) / Real.pi) ^ 2 < B) :
    ∑ j ∈ range (s - 3), Real.arctan (1 / (cG B j : ℝ)) < Real.pi / 2 := by
  have hterm : ∀ j, Real.arctan (1 / (cG B j : ℝ)) ≤ 1 / (cG B j : ℝ) := fun j =>
    Real.arctan_le_self (by have := SkG.cG_pos B j; positivity)
  rcases h with ⟨h8, hF⟩ | h
  · have hB : 4 ≤ B := by unfold Fs at hF; omega
    have hc0 : (6 : ℝ) ≤ cG B 0 := by
      rw [SkG.cG_zero]
      have : 5 ≤ Nat.sqrt (2 * B ^ 2) := Nat.le_sqrt.mpr (by nlinarith)
      have : (6 : ℤ) ≤ ((Nat.sqrt (2 * B ^ 2) + 1 : ℕ) : ℤ) := by push_cast; omega
      exact_mod_cast this
    have hcj : ∀ j, j ≠ 0 → (3 : ℝ) ≤ cG B j := by
      intro j hj
      rw [SkG.cG_pos' B j hj]
      have : 2 ≤ Nat.sqrt B := Nat.le_sqrt.mpr (by omega)
      have : (3 : ℤ) ≤ ((Nat.sqrt B + 1 : ℕ) : ℤ) := by push_cast; omega
      exact_mod_cast this
    obtain ⟨n, hn⟩ : ∃ n, s - 3 = n + 1 := ⟨s - 4, by omega⟩
    rw [hn, sum_range_succ']
    have h1 : ∑ j ∈ range n, Real.arctan (1 / (cG B (j + 1) : ℝ)) ≤ ∑ _j ∈ range n, (1 / 3 : ℝ) :=
      sum_le_sum fun j _ => (hterm _).trans (by
        have := hcj (j + 1) (by omega)
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
    have h2 : Real.arctan (1 / (cG B 0 : ℝ)) ≤ 1 / 6 := (hterm _).trans (by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
    simp only [sum_const, card_range, nsmul_eq_mul] at h1
    have hn4 : (n : ℝ) ≤ 4 := by exact_mod_cast (show n ≤ 4 by omega)
    linarith [Real.pi_gt_three]
  · have hB0 : (0 : ℝ) < B := lt_of_le_of_lt (sq_nonneg _) h
    have hBn : 1 ≤ B := by
      rcases Nat.eq_zero_or_pos B with h0 | h0
      · subst h0; simp at hB0
      · exact h0
    have hsq : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
    -- every `c_j > √B`
    have hcj : ∀ j, Real.sqrt B < cG B j := by
      intro j
      have hpos : (0 : ℝ) < cG B j := by exact_mod_cast SkG.cG_pos B j
      rw [Real.sqrt_lt' hpos]
      by_cases hj : j = 0
      · subst hj
        have := SkG.cG0_sq_gt B
        have h' : (B : ℤ) ≤ 2 * (B : ℤ) ^ 2 := by nlinarith
        have : (B : ℤ) < cG B 0 ^ 2 := by omega
        exact_mod_cast this
      · exact_mod_cast SkG.cGj_sq_gt B j hj
    have hlt : ∑ j ∈ range (s - 3), Real.arctan (1 / (cG B j : ℝ)) <
        ∑ _j ∈ range (s - 3), 1 / Real.sqrt B := by
      apply sum_lt_sum_of_nonempty ⟨0, by simp; omega⟩
      intro j _
      refine lt_of_le_of_lt (hterm j) ?_
      exact one_div_lt_one_div_of_lt hsq (hcj j)
    simp only [sum_const, card_range, nsmul_eq_mul] at hlt
    have hs3 : ((s - 3 : ℕ) : ℝ) = (s : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hs3] at hlt
    have hroot : 2 * ((s : ℝ) - 3) / Real.pi < Real.sqrt B := by
      rw [Real.lt_sqrt (by
        have : (3 : ℝ) ≤ s := by exact_mod_cast (show 3 ≤ s by omega)
        have := Real.pi_pos
        positivity)]
      exact h
    have hpi := Real.pi_pos
    rw [div_lt_iff₀ hpi] at hroot
    have : ((s : ℝ) - 3) * (1 / Real.sqrt B) < Real.pi / 2 := by
      rw [mul_one_div, div_lt_iff₀ hsq]; nlinarith
    linarith

end Z3NetF.Proofs

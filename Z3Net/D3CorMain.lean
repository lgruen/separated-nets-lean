/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(`paper/core.tex`), `cor:allm`. Entry Dim3
(`ChallengeDim3.lean`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.D3Cor

@[expose] public section

/-!
# Entry Dim3, part 8: `cor:allm` (deliverables)

`cor_allm_consts` (the `m ≡ 2` constants `4.264`, `7`), `bndDim3_gt`, `bndDim3_tendsto`,
`cor_allm`, `cor_allm_mesh`, `cor_allm_mesh2`.

For `ρ = ρ_3(p) ≥ 3` the covering constant is bounded without case analysis: with
`x = p^(1/3) ∈ (ρ, ρ+1)`, `(μ + 1)ρ² < p + 2ρ² ≤ x((ρ+1)² + 2ρ) ≤ (22/9) x ρ²`, so
`√3 (μ + 1)/x < √3 · 22/9 < 4.264`; the five primes `11 ≤ p ≤ 23` (`ρ = 2`) are checked one by
one (the maximum `4.2633…` is at `p = 23`).
-/

namespace Z3NetKN.Proofs

open Matrix Finset Filter Topology D3

/-- **`cor:allm`, the `m ≡ 2` constants.** -/
theorem cor_allm_consts :
    (∀ p : ℕ, p.Prime → 11 ≤ p →
      Real.sqrt 3 * ((muS 3 p (rhoS 3 p) : ℝ) + 1) * (p : ℝ) ^ (-(1 / (3 : ℝ))) < 4.264 ∧
      ((muS 3 p (rhoS 3 p) : ℝ) + 1) / ((rhoS 3 p : ℝ) - 1) ≤ 7) ∧
    4.2633 < Real.sqrt 3 * ((muS 3 23 (rhoS 3 23) : ℝ) + 1) * (23 : ℝ) ^ (-(1 / (3 : ℝ))) ∧
    ((muS 3 23 (rhoS 3 23) : ℝ) + 1) / ((rhoS 3 23 : ℝ) - 1) = 7 := by
  have hs1 := sqrt3_lt
  have hs2 := sqrt3_gt
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcube : ∀ a : ℝ, (Real.sqrt 3 * a) ^ 3 = 3 * Real.sqrt 3 * a ^ 3 := by
    intro a
    rw [mul_pow, show Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring, hsq]
  have h23 : rhoS 3 23 = 2 := rhoS3_eq 23 2 (by norm_num) (by norm_num)
  have hm23 : muS 3 23 2 = 6 := by norm_num [muS]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp h11
    obtain ⟨h2, hρp, hpρ, -, -, -⟩ := Z3NetS1.S1_const 3 p (by norm_num) hp (by norm_num; omega)
    have e : Z3NetS1.rhoS 3 p = rhoS 3 p := rfl
    rw [e] at h2 hρp hpρ
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hμ1 : muS 3 p (rhoS 3 p) * rhoS 3 p ^ 2 ≤ p + rhoS 3 p ^ 2 - 1 := by
      show (p + rhoS 3 p ^ 2 - 1) / rhoS 3 p ^ 2 * rhoS 3 p ^ 2 ≤ p + rhoS 3 p ^ 2 - 1
      exact Nat.div_mul_le_self _ _
    rcases Nat.lt_or_ge (rhoS 3 p) 3 with hlt | hge
    · -- `ρ = 2`: the primes `11, 13, 17, 19, 23`
      have hρ2 : rhoS 3 p = 2 := by omega
      rw [hρ2] at hpρ hμ1 ⊢
      have hp26 : p ≤ 26 := by norm_num at hpρ; omega
      interval_cases p <;> norm_num at hp <;>
        exact ⟨mul_rpow_neg_third_lt _ _ _ (by norm_num) (by norm_num)
          (by rw [hcube]; unfold muS; norm_num <;> nlinarith), by unfold muS; norm_num⟩
    · -- `ρ ≥ 3`
      set ρ := rhoS 3 p with hρ
      set μ := muS 3 p ρ with hμ
      have hR3 : (3 : ℝ) ≤ ρ := by exact_mod_cast hge
      have hμR : ((μ : ℝ) + 1) * (ρ : ℝ) ^ 2 + 1 ≤ (p : ℝ) + 2 * (ρ : ℝ) ^ 2 := by
        have h1 : μ * ρ ^ 2 + 1 ≤ p + ρ ^ 2 := by
          have : 1 ≤ p + ρ ^ 2 := by omega
          omega
        have h1' : ((μ * ρ ^ 2 + 1 : ℕ) : ℝ) ≤ ((p + ρ ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at h1'; nlinarith
      have hpR : (p : ℝ) < ((ρ : ℝ) + 1) ^ 3 := by exact_mod_cast hpρ
      have hρR : (ρ : ℝ) ^ 3 < p := by exact_mod_cast hρp
      constructor
      · set x := (p : ℝ) ^ (1 / (3 : ℝ)) with hx
        have hx0 : 0 < x := by positivity
        have hx3 : x ^ 3 = p := rpow_third_cube _ hp0.le
        have hρx : (ρ : ℝ) < x := by
          apply lt_of_pow_lt_pow_left₀ 3 hx0.le; rw [hx3]; exact hρR
        have hxρ : x < (ρ : ℝ) + 1 := by
          apply lt_of_pow_lt_pow_left₀ 3 (by positivity); rw [hx3]; exact hpR
        have hneg : (p : ℝ) ^ (-(1 / (3 : ℝ))) = x⁻¹ := by rw [Real.rpow_neg hp0.le]
        rw [hneg]
        have key : ((μ : ℝ) + 1) < 22 / 9 * x := by
          have hx2 : x ^ 2 < ((ρ : ℝ) + 1) ^ 2 := by
            apply pow_lt_pow_left₀ hxρ hx0.le (by norm_num)
          have hA : x ^ 3 ≤ x * ((ρ : ℝ) + 1) ^ 2 := by
            rw [show x ^ 3 = x * x ^ 2 by ring]
            exact mul_le_mul_of_nonneg_left hx2.le hx0.le
          have hB : 9 * ((ρ : ℝ) + 1) ^ 2 + 18 * ρ ≤ 22 * (ρ : ℝ) ^ 2 := by nlinarith
          have hC : ((μ : ℝ) + 1) * (ρ : ℝ) ^ 2 < 22 / 9 * x * (ρ : ℝ) ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left hρx.le (by positivity : (0 : ℝ) ≤ 2 * ρ)]
          exact lt_of_mul_lt_mul_right hC (by positivity)
        calc Real.sqrt 3 * ((μ : ℝ) + 1) * x⁻¹ < Real.sqrt 3 * (22 / 9 * x) * x⁻¹ := by
              have : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
              gcongr
          _ = Real.sqrt 3 * (22 / 9) := by field_simp
          _ < 4.264 := by nlinarith
      · have hρ1 : (0 : ℝ) < (ρ : ℝ) - 1 := by linarith
        rw [div_le_iff₀ hρ1]
        have hkey : ((μ : ℝ) + 1) * (ρ : ℝ) ^ 2 ≤ 7 * ((ρ : ℝ) - 1) * (ρ : ℝ) ^ 2 := by nlinarith
        have := le_of_mul_le_mul_right hkey (by positivity)
        linarith
  · rw [h23, hm23]
    apply lt_mul_rpow_neg_third _ _ _ (by norm_num) (by positivity)
    rw [hcube]; norm_num; nlinarith
  · rw [h23, hm23]; norm_num

/-- `bndDim3 p ≤` each family bound. -/
lemma D3.bndDim3_le (p : ℕ) : bndDim3 p ≤ Z3NetC.cCol p ∧ bndDim3 p ≤ 1 - 1 / (p : ℝ) ∧
    bndDim3 p ≤ bndB1 p ∧ bndDim3 p ≤ bndB2 p := by
  unfold bndDim3
  exact ⟨le_trans (min_le_left _ _) (min_le_left _ _), le_trans (min_le_left _ _) (min_le_right _ _),
    le_trans (min_le_right _ _) (min_le_left _ _), le_trans (min_le_right _ _) (min_le_right _ _)⟩

/-- **`cor:allm`, the uniform constants.** -/
theorem bndDim3_gt (p : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) :
    0.2715 < bndDim3 p ∧ (83 ≤ p → 0.4250 < bndDim3 p) := by
  have hE : 0.874 < Z3NetC.cCol p := by
    have := ((Z3NetC.col_values.2.2.2.2.2.2.2.2.2 p (coprime6_of_prime p hp (by omega)) (by omega)).2 hp37)
    linarith
  have hP : (36 : ℝ) / 37 ≤ 1 - 1 / (p : ℝ) := by
    have : (37 : ℝ) ≤ p := by exact_mod_cast hp37
    rw [div_le_iff₀ (by norm_num)]
    have : 1 / (p : ℝ) ≤ 1 / 37 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    nlinarith
  have hB2 := bndB2_gt_half p hp (by omega)
  unfold bndDim3
  constructor
  · have hB1 : 0.2715 < bndB1 p := by
      by_cases h : p ≤ 79
      · exact bndB1_gt_small p (by omega) h
      · exact lt_trans (by norm_num) (bndB1_gt_large p (by omega))
    simp only [lt_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, hB1, by linarith⟩
  · intro h83
    have hB1 := bndB1_gt_large p (by omega)
    simp only [lt_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, hB1, by linarith⟩

/-- **`cor:allm`: the lower bound tends to `1`.** -/
theorem bndDim3_tendsto : Filter.Tendsto bndDim3 Filter.atTop (nhds 1) := by
  have h1 : Tendsto Z3NetC.cCol atTop (𝓝 1) := Z3NetC.Proofs.cCol_tendsto
  have h2 : Tendsto (fun p : ℕ => 1 - 1 / (p : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
  have h3 := B1_tendsto
  have h4 : Tendsto bndB2 atTop (𝓝 1) := Z3NetS1.S1_const_tendsto 3 (by norm_num)
  have := (h1.min h2).min (h3.min h4)
  have e : bndDim3 = fun p => min (min (Z3NetC.cCol p) (1 - 1 / (p : ℝ))) (min (bndB1 p) (bndB2 p)) :=
    rfl
  rw [e]
  simpa only [min_self] using this

/-- **`cor:allm`.** -/
theorem cor_allm (p m : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) (hm : 3 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p),
      IsNet0 p m (digPoint p m C) ∧
      (∀ v w : Fin m → ZMod p, v ≠ w →
        bndDim3 p * ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (p ^ m) ((digPoint p m C v c : ℤ) - (digPoint p m C w c : ℤ)) : ℝ)
            / (p : ℝ) ^ m) ^ 2)) ∧
      (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin m → ZMod p,
        Real.sqrt (∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
          (if m % 3 = 0 then Real.sqrt 3
           else if m % 3 = 1 then (p : ℝ) ^ (1 / (3 : ℝ)) * Real.sqrt (2 + 1 / (p : ℝ) ^ 2)
           else min ((p : ℝ) ^ (2 / (3 : ℝ)) * Real.sqrt (1 + 2 / (p : ℝ) ^ 2)) 4.264) *
            ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ)))) := by
  obtain ⟨hlE, -, hlB1, hlB2⟩ := bndDim3_le p
  rcases (show m = 3 ∨ (m % 3 = 0 ∧ 6 ≤ m) ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with
    h | ⟨h, h6⟩ | h | h
  · subst h
    obtain ⟨hn, hs, hc⟩ := famCol p hp hp37
    refine ⟨Z3NetC.colGen p, hn, hs, fun y hy => ?_⟩
    obtain ⟨v, hv⟩ := hc y hy
    exact ⟨v, by rw [if_pos (by norm_num)]; exact hv⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k := ⟨m / 3, by omega⟩
    obtain ⟨hn, hs, hc⟩ := famP p k hp hp37 (by omega)
    refine ⟨_, hn, hs, fun y hy => ?_⟩
    obtain ⟨v, hv⟩ := hc y hy
    exact ⟨v, by rw [if_pos (by omega)]; exact hv⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k + 1 := ⟨m / 3, by omega⟩
    obtain ⟨hn, hs, hc⟩ := famB1 p k hp hp37 (by omega)
    refine ⟨_, hn, hs, fun y hy => ?_⟩
    obtain ⟨v, hv⟩ := hc y hy
    exact ⟨v, by rw [if_neg (by omega), if_pos (by omega)]; exact hv⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
    have hk : 1 ≤ k := by omega
    obtain ⟨hn, hsk, hs, hc⟩ := famB2 p k hp (by omega) hk
    refine ⟨_, hn, fun v w hvw => le_trans ?_ (hs v w hvw), fun y hy => ?_⟩
    · gcongr
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases hA : (p : ℝ) ^ (2 / (3 : ℝ)) * Real.sqrt (1 + 2 / (p : ℝ) ^ 2) ≤ 4.264
    · obtain ⟨v, hv⟩ := hc y hy
      exact ⟨v, by rw [min_eq_left hA]; exact hv⟩
    · push Not at hA
      rw [min_eq_right hA.le]
      have hS1 : Z3NetS1.IsS1skel 3 p k (Z3NetS1.rhoS 3 p) (B2gen p k (rhoS 3 p)) :=
        (B2_skel_iff p k _ _).2 hsk
      obtain ⟨v, hv⟩ := Z3NetS1.S1_cover 3 p k (le_refl 3) hp (by norm_num; omega) _ hS1 y hy
      simp only [Nat.cast_ofNat] at hv
      refine ⟨v, le_trans hv.le ?_⟩
      have hc4 := (cor_allm_consts.1 p hp (by omega)).1
      have hq : 0 ≤ ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ))) := by positivity
      exact mul_le_mul_of_nonneg_right hc4.le hq

/-- **`cor:allm`: quasi-uniformity, the mesh ratio bounded uniformly in `m`.** -/
theorem cor_allm_mesh (p : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) :
    ∃ M : ℝ, ∀ m : ℕ, 3 ≤ m → ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p),
      IsNet0 p m (digPoint p m C) ∧
      ∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin m → ZMod p,
        ∀ w w' : Fin m → ZMod p, w ≠ w' →
          Real.sqrt (∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
            M * Real.sqrt (∑ c, ((cres (p ^ m)
              ((digPoint p m C w c : ℤ) - (digPoint p m C w' c : ℤ)) : ℝ) / (p : ℝ) ^ m) ^ 2) := by
  have hb := (bndDim3_gt p hp hp37).1
  have hb0 : 0 < bndDim3 p := lt_trans (by norm_num) hb
  set K : ℝ := Real.sqrt 3 + (p : ℝ) ^ (1 / (3 : ℝ)) * Real.sqrt (2 + 1 / (p : ℝ) ^ 2) + 4.264
    with hK
  have hK1 : 0 ≤ (p : ℝ) ^ (1 / (3 : ℝ)) * Real.sqrt (2 + 1 / (p : ℝ) ^ 2) := by positivity
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K / bndDim3 p, fun m hm => ?_⟩
  obtain ⟨C, hn, hs, hc⟩ := cor_allm p m hp hp37 hm
  refine ⟨C, hn, fun y hy => ?_⟩
  obtain ⟨v, hv⟩ := hc y hy
  refine ⟨v, fun w w' hww => ?_⟩
  have hδ := hs w w' hww
  have hq : 0 ≤ ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ))) := by positivity
  have hcov : (if m % 3 = 0 then Real.sqrt 3
      else if m % 3 = 1 then (p : ℝ) ^ (1 / (3 : ℝ)) * Real.sqrt (2 + 1 / (p : ℝ) ^ 2)
      else min ((p : ℝ) ^ (2 / (3 : ℝ)) * Real.sqrt (1 + 2 / (p : ℝ) ^ 2)) 4.264) ≤ K := by
    have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    split_ifs
    · linarith
    · linarith
    · exact le_trans (min_le_right _ _) (by linarith)
  calc Real.sqrt (∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2)
      ≤ K * ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ))) := le_trans hv (mul_le_mul_of_nonneg_right hcov hq)
    _ = K / bndDim3 p * (bndDim3 p * ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ)))) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hδ (div_nonneg hK0 hb0.le)

/-- **`cor:allm`, `m ≡ 2`: covering `< 4.264 N^(-1/3)` and mesh ratio `≤ 7√3`, every prime
`p ≥ 11`.** -/
theorem cor_allm_mesh2 (p k : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hk : 1 ≤ k) :
    IsNet0 p (3 * k + 2) (digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p))) ∧
    ∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin (3 * k + 2) → ZMod p,
      Real.sqrt (∑ c, (y c - (digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p)) v c : ℝ)
          / (p : ℝ) ^ (3 * k + 2)) ^ 2) < 4.264 * ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ))) ∧
      ∀ w w' : Fin (3 * k + 2) → ZMod p, w ≠ w' →
        Real.sqrt (∑ c, (y c - (digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p)) v c : ℝ)
          / (p : ℝ) ^ (3 * k + 2)) ^ 2) ≤
        7 * Real.sqrt 3 * Real.sqrt (∑ c, ((cres (p ^ (3 * k + 2))
          ((digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p)) w c : ℤ) -
            (digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p)) w' c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k + 2)) ^ 2) := by
  obtain ⟨hn, hsk, hs, -⟩ := famB2 p k hp hp11 hk
  obtain ⟨h2, -, -, -, -, -⟩ := Z3NetS1.S1_const 3 p (by norm_num) hp (by norm_num; omega)
  have e : Z3NetS1.rhoS 3 p = rhoS 3 p := rfl
  rw [e] at h2
  obtain ⟨hc4, h7⟩ := cor_allm_consts.1 p hp hp11
  refine ⟨hn, fun y hy => ?_⟩
  have hS1 : Z3NetS1.IsS1skel 3 p k (Z3NetS1.rhoS 3 p) (B2gen p k (rhoS 3 p)) :=
    (B2_skel_iff p k _ _).2 hsk
  obtain ⟨v, hv⟩ := Z3NetS1.S1_cover 3 p k (le_refl 3) hp (by norm_num; omega) _ hS1 y hy
  simp only [Nat.cast_ofNat] at hv
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set q : ℝ := (p : ℝ) ^ (-(1 / (3 : ℝ))) * ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ))) with hqdef
  have hq : 0 < q := by positivity
  have hN : 0 < ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ))) := by positivity
  refine ⟨v, ?_, fun w w' hww => ?_⟩
  · calc _ < _ := hv
      _ ≤ 4.264 * ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ))) :=
        mul_le_mul_of_nonneg_right hc4.le hN.le
  · have hδ := hs w w' hww
    unfold bndB2 at hδ
    have hρ1 : (0 : ℝ) < (rhoS 3 p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ rhoS 3 p := by exact_mod_cast h2
      linarith
    have hμ7 : (muS 3 p (rhoS 3 p) : ℝ) + 1 ≤ 7 * ((rhoS 3 p : ℝ) - 1) := by
      rwa [div_le_iff₀ hρ1] at h7
    have hδ' : ((rhoS 3 p : ℝ) - 1) * q ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k + 2))
          ((digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p)) w c : ℤ) -
            (digPoint p (3 * k + 2) (B2gen p k (rhoS 3 p)) w' c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k + 2)) ^ 2) := by
      rw [hqdef, ← mul_assoc]; simpa only [Nat.cast_ofNat] using hδ
    have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    calc _ ≤ Real.sqrt 3 * ((muS 3 p (rhoS 3 p) : ℝ) + 1) * (p : ℝ) ^ (-(1 / (3 : ℝ))) *
          ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ))) := hv.le
      _ = Real.sqrt 3 * ((muS 3 p (rhoS 3 p) : ℝ) + 1) * q := by rw [hqdef]; ring
      _ ≤ Real.sqrt 3 * (7 * ((rhoS 3 p : ℝ) - 1)) * q := by gcongr
      _ = 7 * Real.sqrt 3 * (((rhoS 3 p : ℝ) - 1) * q) := by ring
      _ ≤ _ := by gcongr

end Z3NetKN.Proofs

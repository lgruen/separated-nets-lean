module
public import Mathlib
public import Z3Net.S2Defs
public import Z3Net.SkGBase
public import Z3Net.SkGThr

@[expose] public section

/-!
# Entry S2, `thm:S2`: the constants for `s = 4`, eventual validity for `s ≥ 5`, `B(p) ≍ p^(2/s)`

* `rhoT_sq_lt`, `rhoT_max`: `ρ² < p + 4 ≤ (ρ + 1)²` for `p ≥ 2`; **`S2_const4`**: `ρ ≥ 5 ⟺ p ≥ 23`
  for primes `p ≥ 5`, and `1 - 5/√p ≤ (ρ - 4)/√p ≤ 1`;
* **`S2_eventually`**: a fixed `B* > max(F, (2(s-3)/π)²)` is admissible for all `p > g(B*)`;
* **`Bp_asymp`**: `2 B^s ≤ g(B)² ≤ K B^s` (`K = 40 (s-2)² 5^(s-4)`, `g(B) = B (1 + ‖A(B)‖)`)
  give `(1/2) K^(-1/s) p^(2/s) ≤ B(p) ≤ p^(2/s)` for `p ≥ 2^s K`.
-/

namespace Z3NetF.Proofs

open Finset Filter Topology

namespace SkG

/-! ### `s = 4` -/

lemma rhoT_sq_lt (p : ℕ) : rhoT p ^ 2 < p + 4 :=
  Nat.findGreatest_spec (P := fun ρ => ρ ^ 2 < p + 4) (Nat.zero_le p) (by simp)

lemma rhoT_max (p : ℕ) (hp : 2 ≤ p) : p + 4 ≤ (rhoT p + 1) ^ 2 := by
  by_contra h
  push Not at h
  rcases Nat.lt_or_ge (rhoT p) p with h1 | h1
  · exact Nat.findGreatest_is_greatest (P := fun ρ => ρ ^ 2 < p + 4) (Nat.lt_succ_self _)
      (by unfold rhoT at h1; omega) h
  · have h2 : rhoT p ≤ p := Nat.findGreatest_le p
    have : rhoT p = p := le_antisymm h2 h1
    rw [this] at h
    nlinarith

lemma le_rhoT (p ρ : ℕ) (hρ : ρ ≤ p) (h : ρ ^ 2 < p + 4) : ρ ≤ rhoT p :=
  Nat.le_findGreatest (P := fun ρ => ρ ^ 2 < p + 4) hρ h

lemma rpow_neg_half (x : ℝ) (hx : 0 ≤ x) : x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow]

/-! ### `s ≥ 5`: two-sided bounds on `g(B)` -/

/-- `g(B)² ≤ K B^s`, `K = 40 (s-2)² 5^(s-4)`. -/
lemma g_sq_le (s B : ℕ) (hs : 5 ≤ s) (hB : 1 ≤ B) :
    ((B : ℤ) * (1 + normA s B)) ^ 2 ≤ (40 * ((s - 2 : ℕ) : ℤ) ^ 2 * 5 ^ (s - 4)) * (B : ℤ) ^ s := by
  have h1 := normA_sq_le s B
  have h2 := norm_gaussOmega_le B (s - 4) hB
  rw [show s - 4 + 1 = s - 3 by omega, show s - 4 + 2 = s - 2 by omega] at h2
  have h3 := BnormA_sq_ge s B hs
  have hn := normA_nonneg s B
  have hBz : (1 : ℤ) ≤ B := by exact_mod_cast hB
  -- `‖A‖ ≥ 1`
  have hn1 : 1 ≤ normA s B := by
    by_contra hc
    push Not at hc
    have : normA s B = 0 := by omega
    rw [this] at h3
    have : (0 : ℤ) < 2 * (B : ℤ) ^ s := by positivity
    nlinarith
  have hs2 : (0 : ℤ) ≤ ((s - 2 : ℕ) : ℤ) ^ 2 := by positivity
  have h4 : normA s B ^ 2 ≤ ((s - 2 : ℕ) : ℤ) ^ 2 * (10 * 5 ^ (s - 4) * (B : ℤ) ^ (s - 2)) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hs2)
  have h5 : ((B : ℤ) * (1 + normA s B)) ^ 2 ≤ 4 * (B : ℤ) ^ 2 * normA s B ^ 2 := by
    have h6 : (1 + normA s B) ^ 2 ≤ 4 * normA s B ^ 2 := by nlinarith
    calc ((B : ℤ) * (1 + normA s B)) ^ 2 = (B : ℤ) ^ 2 * (1 + normA s B) ^ 2 := by ring
      _ ≤ (B : ℤ) ^ 2 * (4 * normA s B ^ 2) := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = 4 * (B : ℤ) ^ 2 * normA s B ^ 2 := by ring
  calc ((B : ℤ) * (1 + normA s B)) ^ 2 ≤ 4 * (B : ℤ) ^ 2 * normA s B ^ 2 := h5
    _ ≤ 4 * (B : ℤ) ^ 2 * (((s - 2 : ℕ) : ℤ) ^ 2 * (10 * 5 ^ (s - 4) * (B : ℤ) ^ (s - 2))) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (40 * ((s - 2 : ℕ) : ℤ) ^ 2 * 5 ^ (s - 4)) * ((B : ℤ) ^ 2 * (B : ℤ) ^ (s - 2)) := by ring
    _ = (40 * ((s - 2 : ℕ) : ℤ) ^ 2 * 5 ^ (s - 4)) * (B : ℤ) ^ s := by
      rw [← pow_add, show 2 + (s - 2) = s by omega]

lemma rpow_two_div_pow (x : ℝ) (hx : 0 ≤ x) (s : ℕ) (hs : s ≠ 0) :
    (x ^ (2 / (s : ℝ))) ^ s = x ^ 2 := by
  rw [← Real.rpow_mul_natCast hx, div_mul_cancel₀ _ (by exact_mod_cast hs), Real.rpow_two]

lemma rpow_one_div_pow (x : ℝ) (hx : 0 ≤ x) (s : ℕ) (hs : s ≠ 0) :
    (x ^ (1 / (s : ℝ))) ^ s = x := by
  rw [← Real.rpow_mul_natCast hx, one_div_mul_cancel (by exact_mod_cast hs), Real.rpow_one]

end SkG

theorem S2_const4 :
    (∀ p : ℕ, p.Prime → 5 ≤ p → (5 ≤ rhoT p ↔ 23 ≤ p)) ∧
      Filter.Tendsto (fun p : ℕ => ((rhoT p : ℝ) - 4) * (p : ℝ) ^ (-(1 / 2 : ℝ)))
        Filter.atTop (nhds 1) := by
  constructor
  · intro p hp h5
    constructor
    · intro h
      have h1 := SkG.rhoT_sq_lt p
      have h2 : 25 ≤ rhoT p ^ 2 := by nlinarith
      have h22 : p ≠ 22 := by rintro rfl; norm_num at hp
      omega
    · intro h
      exact SkG.le_rhoT p 5 (by omega) (by omega)
  · -- squeeze between `1 - 5/√p` and `1`
    have hlow : Tendsto (fun p : ℕ => 1 - 5 * (Real.sqrt (p : ℝ))⁻¹) atTop (𝓝 1) := by
      have h1 : Tendsto (fun p : ℕ => Real.sqrt (p : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      have h2 := (tendsto_inv_atTop_zero.comp h1).const_mul 5
      have h3 := h2.const_sub 1
      simpa using h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with p hp
      have hmax := SkG.rhoT_max p hp
      have hpos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < p))
      rw [SkG.rpow_neg_half _ (by positivity)]
      -- `√p < ρ + 1`
      have hlt : Real.sqrt p < (rhoT p : ℝ) + 1 := by
        rw [Real.sqrt_lt' (by positivity)]
        have : (p : ℝ) + 4 ≤ ((rhoT p : ℝ) + 1) ^ 2 := by exact_mod_cast hmax
        linarith
      have : 1 - 5 * (Real.sqrt p)⁻¹ = (Real.sqrt p - 5) * (Real.sqrt p)⁻¹ := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with p hp
      have h1 := SkG.rhoT_sq_lt p
      have hpos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < p))
      rw [SkG.rpow_neg_half _ (by positivity)]
      have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (by positivity)
      have hp1 : (1 : ℝ) ≤ Real.sqrt p := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]; simp; exact_mod_cast hp
      -- `ρ < √p + 2`
      have hρ : (rhoT p : ℝ) < Real.sqrt p + 2 := by
        have h2 : ((rhoT p : ℝ)) ^ 2 < (Real.sqrt p + 2) ^ 2 := by
          have : ((rhoT p : ℝ)) ^ 2 < (p : ℝ) + 4 := by exact_mod_cast h1
          nlinarith
        exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
      have : ((rhoT p : ℝ) - 4) ≤ Real.sqrt p := by linarith
      calc ((rhoT p : ℝ) - 4) * (Real.sqrt p)⁻¹ ≤ Real.sqrt p * (Real.sqrt p)⁻¹ :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 1 := mul_inv_cancel₀ hpos.ne'

theorem S2_eventually (s : ℕ) (hs : 5 ≤ s) :
    ∃ p0 : ℕ, ∀ p, p0 ≤ p → Fs s + 1 ≤ Bp s p ∧ (2 * ((s : ℝ) - 3) / Real.pi) ^ 2 < Bp s p := by
  set B0 : ℕ := Fs s + 1 + s ^ 2 with hB0
  refine ⟨((B0 : ℤ) * (1 + normA s B0)).toNat + 1, fun p hp => ?_⟩
  have hle : B0 ≤ Bp s p := by
    apply SkG.le_Bp s p B0 (by omega)
    have := Int.self_le_toNat ((B0 : ℤ) * (1 + normA s B0))
    have : (((B0 : ℤ) * (1 + normA s B0)).toNat : ℤ) + 1 ≤ p := by exact_mod_cast hp
    omega
  refine ⟨by omega, ?_⟩
  have hpi := Real.pi_gt_three
  have hs3 : (3 : ℝ) ≤ s := by exact_mod_cast (show 3 ≤ s by omega)
  have h1 : 2 * ((s : ℝ) - 3) / Real.pi ≤ s := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h0 : 0 ≤ 2 * ((s : ℝ) - 3) / Real.pi := by
    apply div_nonneg <;> linarith
  have h2 : (2 * ((s : ℝ) - 3) / Real.pi) ^ 2 ≤ (s : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (s : ℝ) ^ 2 < B0 := by
    rw [hB0]; push_cast; have : (0 : ℝ) ≤ Fs s := by positivity
    linarith
  have h4 : (B0 : ℝ) ≤ Bp s p := by exact_mod_cast hle
  linarith

theorem Bp_asymp (s : ℕ) (hs : 5 ≤ s) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ p0 : ℕ, ∀ p, p0 ≤ p →
      c₁ * (p : ℝ) ^ (2 / (s : ℝ)) ≤ Bp s p ∧ (Bp s p : ℝ) ≤ c₂ * (p : ℝ) ^ (2 / (s : ℝ)) := by
  set K : ℕ := 40 * (s - 2) ^ 2 * 5 ^ (s - 4) with hK
  have hKpos : 0 < K := Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by omega) 2)) (by positivity)
  have hs0 : s ≠ 0 := by omega
  refine ⟨(1 / 2) * (1 / (K : ℝ)) ^ (1 / (s : ℝ)), 1,
    mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _), one_pos, 2 ^ s * K, ?_⟩
  intro p hp
  have hp1 : 1 ≤ p := by
    have : 0 < 2 ^ s * K := Nat.mul_pos (by positivity) hKpos
    omega
  have hpr : (0 : ℝ) ≤ p := by positivity
  have hy0 : (0 : ℝ) ≤ (p : ℝ) ^ (2 / (s : ℝ)) := by positivity
  constructor
  · -- lower bound: `k = B(p) + 1` has `p ≤ g(k)`, so `p² ≤ K k^s`
    set k := Bp s p + 1 with hk
    have hkp : k ≤ p := SkG.Bp_lt s p hp1
    have hg := SkG.Bp_max s p k (by omega) hkp
    have hg2 := SkG.g_sq_le s k hs (by omega)
    have hpk : (p : ℤ) ^ 2 ≤ (K : ℤ) * (k : ℤ) ^ s := by
      have h0 : (0 : ℤ) ≤ p := by positivity
      have := pow_le_pow_left₀ h0 hg 2
      have hKz : ((K : ℕ) : ℤ) = 40 * ((s - 2 : ℕ) : ℤ) ^ 2 * 5 ^ (s - 4) := by
        rw [hK]; push_cast; rfl
      rw [hKz]; linarith
    have hpkN : p ^ 2 ≤ K * k ^ s := by exact_mod_cast hpk
    -- `k ≥ 2`
    have hk2 : 2 ≤ k := by
      have h1 : 2 ^ s * K ≤ p ^ 2 := le_trans hp (by nlinarith)
      have h2 : 2 ^ s ≤ k ^ s := by
        have := le_trans h1 hpkN
        rw [mul_comm] at this
        exact Nat.le_of_mul_le_mul_left this hKpos
      exact (Nat.pow_le_pow_iff_left hs0).mp h2
    -- `y = K^(-1/s) p^(2/s) ≤ k`
    set y : ℝ := (1 / (K : ℝ)) ^ (1 / (s : ℝ)) * (p : ℝ) ^ (2 / (s : ℝ)) with hy
    have hyk : y ≤ k := by
      have hys : y ^ s = (1 / (K : ℝ)) * (p : ℝ) ^ 2 := by
        rw [hy, mul_pow, SkG.rpow_one_div_pow _ (by positivity) s hs0,
          SkG.rpow_two_div_pow _ hpr s hs0]
      have hyk' : y ^ s ≤ (k : ℝ) ^ s := by
        rw [hys]
        have : ((p : ℝ)) ^ 2 ≤ (K : ℝ) * (k : ℝ) ^ s := by exact_mod_cast hpkN
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) hs0).mp hyk'
    have hBk : (Bp s p : ℝ) = (k : ℝ) - 1 := by rw [hk]; push_cast; ring
    have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    rw [hBk]
    calc 1 / 2 * (1 / (K : ℝ)) ^ (1 / (s : ℝ)) * (p : ℝ) ^ (2 / (s : ℝ)) = y / 2 := by
          rw [hy]; ring
      _ ≤ (k : ℝ) - 1 := by linarith
  · -- upper bound: `2 B^s ≤ g(B)² < p²`
    rcases Nat.eq_zero_or_pos (Bp s p) with h0 | h0
    · rw [h0]; simp; positivity
    have hg := SkG.Bp_spec s p h0
    have h2 := SkG.BnormA_sq_ge s (Bp s p) hs
    have hn := SkG.normA_nonneg s (Bp s p)
    have hBs : (Bp s p : ℤ) ^ s < (p : ℤ) ^ 2 := by
      have h3 : (Bp s p : ℤ) * normA s (Bp s p) < p := by nlinarith
      have h4 : ((Bp s p : ℤ) * normA s (Bp s p)) ^ 2 < (p : ℤ) ^ 2 :=
        pow_lt_pow_left₀ h3 (mul_nonneg (by positivity) hn) two_ne_zero
      have : (0 : ℤ) ≤ (Bp s p : ℤ) ^ s := by positivity
      linarith
    have hBsr : (Bp s p : ℝ) ^ s < ((p : ℝ) ^ (2 / (s : ℝ))) ^ s := by
      rw [SkG.rpow_two_div_pow _ hpr s hs0]; exact_mod_cast hBs
    rw [one_mul]
    exact ((pow_lt_pow_iff_left₀ (by positivity) hy0 hs0).mp hBsr).le

end Z3NetF.Proofs

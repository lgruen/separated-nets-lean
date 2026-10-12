module
public import Mathlib
public import Z3Net.HLDom

@[expose] public section

/-!
# Entry HL, part 8: `HL_relax`, `HL_dom` and the real forms

`HL_relax` is `relax_core` with the entry-HL `torusDist2`; `HL_dom` combines it with
`dom_arith` (the far case gives `D² ≥ 4 q^(2(s-1)k)`, which exceeds the bound). `real_form`
converts an integer bound `q^(2(sk-k-1)) · min(a², b²) ≤ 4 D²` into
`min(a, b)/(2q) · N^(-1/s) ≤ δ`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

lemma cres_eq : Z3NetHL.cres = Z3NetU.cres := rfl

lemma torusDist2_cast {s : ℕ} (N : ℕ) (X Y : Fin s → ℕ) :
    (torusDist2 N X Y : ℤ) = ∑ c, ((Z3NetU.cres N ((X c : ℤ) - (Y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  simp [torusDist2, cres_eq]

theorem HL_relax (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hq7 : 7 ≤ q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d) (hk : 1 ≤ k)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤
        (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) := by
  haveI : NeZero q := ⟨by omega⟩
  rw [torusDist2_cast]
  exact relax_core s q k u v lam gco dg hs hq hden hq7 F2 hF2 hk x y hxy

theorem HL_dom (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    (q : ℤ) ^ (2 * (s * k - k - 1)) *
        min ((s : ℤ) * ((q : ℤ) - 2 * Bdom s F2 - 2) ^ 2) (8 * ((q : ℤ) - Bdom s F2 - 1) ^ 2) ≤
      4 * (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) := by
  -- `B ≥ 2`, so `q ≥ 7`
  have hB2 : 2 ≤ Bdom s F2 := by
    obtain ⟨c0⟩ : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
    obtain ⟨d0, hd0⟩ : ∃ d0 : Fin s, d0 ≠ c0 := by
      by_cases h : (c0 : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
      · exact ⟨⟨0, by omega⟩, fun h' => h (by rw [← h'])⟩
    have hBc := Bdom_ge F2 c0 (hdom c0)
    have hA : (1 : ℤ) ≤ A2 s F2 c0 := by
      rw [A2_eq]
      have h1 : (1 : ℤ) ≤ (mx F2 c0 d0 : ℤ) := by
        have := M2_le_mx F2 0 (by omega) c0 d0
        have e0 : M2 F2 0 c0 d0 = F2 0 c0 d0 := by simp [M2]
        rw [e0] at this
        obtain ⟨t, ht⟩ := hhalf0 c0 d0
        have : (1 : ℤ) ≤ |F2 0 c0 d0| := Int.one_le_abs (by omega)
        linarith
      have := Finset.single_le_sum (f := fun d => (mx F2 c0 d : ℤ)) (fun d _ => by positivity)
        (mem_erase.mpr ⟨hd0, mem_univ d0⟩)
      linarith
    have := hdom c0
    have : (2 : ℤ) ≤ Bdom s F2 := by linarith
    exact_mod_cast this
  have hq7 : 7 ≤ q := by obtain ⟨t, ht⟩ := hqodd; omega
  rcases HL_relax s q k u v lam gco dg F2 hs hq hden hq7 hF2 hk x y hxy with hfar | ⟨E, J, Δ, hE, hne, hJ, hdvd, hΔ, hbd⟩
  · have hM : (q : ℤ) ^ (2 * (s * k - k)) = (q : ℤ) ^ (2 * (s * k - k - 1)) * (q : ℤ) ^ 2 := by
      rw [← pow_add]; congr 1
      have := Nat.mul_le_mul_right k (show 2 ≤ s from hs); omega
    have hq0 : (0 : ℤ) ≤ q := by positivity
    have hmin : min ((s : ℤ) * ((q : ℤ) - 2 * Bdom s F2 - 2) ^ 2) (8 * ((q : ℤ) - Bdom s F2 - 1) ^ 2) ≤
        16 * (q : ℤ) ^ 2 := by
      refine (min_le_right _ _).trans ?_
      have h1 : 0 ≤ (q : ℤ) - Bdom s F2 - 1 := by
        have : (2 * Bdom s F2 + 2 : ℤ) ≤ q := by exact_mod_cast hqB
        have : (0 : ℤ) ≤ Bdom s F2 := by positivity
        linarith
      have hB0 : (0 : ℤ) ≤ Bdom s F2 := by positivity
      have h2 : (q : ℤ) - Bdom s F2 - 1 ≤ q := by linarith
      nlinarith
    calc (q : ℤ) ^ (2 * (s * k - k - 1)) * min _ _ ≤ (q : ℤ) ^ (2 * (s * k - k - 1)) * (16 * (q : ℤ) ^ 2) :=
          mul_le_mul_of_nonneg_left hmin (by positivity)
      _ = 4 * (4 * (q : ℤ) ^ (2 * (s * k - k))) := by rw [hM]; ring
      _ ≤ _ := by linarith
  · have hJ' : ∀ c, J c < s - 1 := fun c => lt_of_lt_of_le (hJ c) (min_le_right _ _)
    have hqB' : 2 * (Bdom s F2 : ℤ) + 2 ≤ q := by exact_mod_cast hqB
    have hqodd' : Odd (q : ℤ) := by
      obtain ⟨t, ht⟩ := hqodd; exact ⟨t, by rw [ht]; push_cast; ring⟩
    have h := dom_arith F2 hs hhalf0 hhalf hdiag hdom (q : ℤ) hqodd' hqB' E J Δ hE hne hJ' hdvd hΔ
    calc (q : ℤ) ^ (2 * (s * k - k - 1)) * min _ _ ≤
          (q : ℤ) ^ (2 * (s * k - k - 1)) * (4 * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 4 * ((q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2) := by ring
      _ ≤ _ := by linarith

/-! ## Real form -/

lemma real_form (s q k : ℕ) (hs : 2 ≤ s) (hk : 1 ≤ k) (hq : 1 ≤ q) (S : ℝ) (hS0 : 0 ≤ S)
    (a b : ℝ) (hint : (q : ℝ) ^ (2 * (s * k - k - 1)) * min (a ^ 2) (b ^ 2) ≤ 4 * S) :
    min (a / (2 * q)) (b / (2 * q)) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (S / ((q : ℝ) ^ (s * k)) ^ 2) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : (s : ℝ) ≠ 0 := by
    have h0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    exact h0.ne'
  have hrp : ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) = 1 / (q : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, show ((s * k : ℕ) : ℝ) * (-(1 / (s : ℝ))) =
      -(k : ℝ) by push_cast; field_simp, Real.rpow_neg hq0.le, Real.rpow_natCast, one_div]
  rw [hrp]
  by_cases hm : min a b ≤ 0
  · have : min (a / (2 * q)) (b / (2 * q)) ≤ 0 := by
      rcases min_le_iff.mp hm with h | h
      · exact (min_le_left _ _).trans (div_nonpos_of_nonpos_of_nonneg h (by positivity))
      · exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg h (by positivity))
    calc min (a / (2 * q)) (b / (2 * q)) * (1 / (q : ℝ) ^ k) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg this (by positivity)
      _ ≤ _ := Real.sqrt_nonneg _
  push_neg at hm
  have ha : 0 < a := lt_of_lt_of_le hm (min_le_left _ _)
  have hb : 0 < b := lt_of_lt_of_le hm (min_le_right _ _)
  have e1 : min (a / (2 * q)) (b / (2 * q)) = min a b / (2 * q) := by
    have h2q : (0 : ℝ) < 2 * q := by positivity
    rcases le_total a b with h | h
    · rw [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right h h2q.le)]
    · rw [min_eq_right h, min_eq_right (div_le_div_of_nonneg_right h h2q.le)]
  have e2 : min (a ^ 2) (b ^ 2) = (min a b) ^ 2 := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, min_eq_left (pow_le_pow_left₀ ha.le h 2)]
    · rw [min_eq_right h, min_eq_right (pow_le_pow_left₀ hb.le h 2)]
  rw [e1]
  apply Real.le_sqrt_of_sq_le
  rw [e2] at hint
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have eN : ((q : ℝ) ^ (s * k)) = (q : ℝ) ^ (s * k - k - 1) * (q : ℝ) * (q : ℝ) ^ k := by
    rw [← pow_succ, ← pow_add]; congr 1
    have := Nat.mul_le_mul_right k (show 2 ≤ s from hs); omega
  have eP : (q : ℝ) ^ (2 * (s * k - k - 1)) = ((q : ℝ) ^ (s * k - k - 1)) ^ 2 := by
    rw [← pow_mul]; ring_nf
  rw [eP] at hint
  rw [eN, le_div_iff₀ (by positivity)]
  have hP : (0 : ℝ) < (q : ℝ) ^ (s * k - k - 1) := by positivity
  have : (min a b / (2 * q) * (1 / (q : ℝ) ^ k)) ^ 2 * ((q : ℝ) ^ (s * k - k - 1) * (q : ℝ) *
      (q : ℝ) ^ k) ^ 2 = ((q : ℝ) ^ (s * k - k - 1)) ^ 2 * (min a b) ^ 2 / 4 := by
    field_simp; ring
  rw [this]
  linarith

theorem HL_dom_real (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((Bdom s F2 : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((Bdom s F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((HLpoint s q k u v lam gco dg x c : ℤ) - (HLpoint s q k u v lam gco dg y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) := by
  have hZ := HL_dom s q k u v lam gco dg F2 hs hq hden hqodd hF2 hhalf0 hhalf hdiag hdom hqB hk x y hxy
  have hq1 : 1 ≤ q := by have := hq.1; omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  set S : ℝ := ∑ c, ((cres (q ^ (s * k))
      ((HLpoint s q k u v lam gco dg x c : ℤ) - (HLpoint s q k u v lam gco dg y c : ℤ)) : ℝ)) ^ 2 with hS
  have hsum : ∑ c, ((cres (q ^ (s * k))
      ((HLpoint s q k u v lam gco dg x c : ℤ) - (HLpoint s q k u v lam gco dg y c : ℤ)) : ℝ)
        / (q : ℝ) ^ (s * k)) ^ 2 = S / ((q : ℝ) ^ (s * k)) ^ 2 := by
    rw [hS, Finset.sum_div]; refine Finset.sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum]
  set B : ℝ := (Bdom s F2 : ℝ)
  have hR : (q : ℝ) ^ (2 * (s * k - k - 1)) *
      min ((Real.sqrt s * ((q : ℝ) - 2 * B - 2)) ^ 2) ((2 * Real.sqrt 2 * ((q : ℝ) - B - 1)) ^ 2) ≤ 4 * S := by
    have h1 : (Real.sqrt s * ((q : ℝ) - 2 * B - 2)) ^ 2 = (s : ℝ) * ((q : ℝ) - 2 * B - 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h2 : (2 * Real.sqrt 2 * ((q : ℝ) - B - 1)) ^ 2 = 8 * ((q : ℝ) - B - 1) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [h1, h2]
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this
    rw [torusDist2] at this
    push_cast at this
    simpa [hS, B] using this
  have := real_form s q k hs hk hq1 S (by positivity) _ _ hR
  have e1 : Real.sqrt s * ((q : ℝ) - 2 * B - 2) / (2 * q) = Real.sqrt s * (1 / 2 - (B + 1) / q) := by
    field_simp; ring
  have e2 : 2 * Real.sqrt 2 * ((q : ℝ) - B - 1) / (2 * q) = Real.sqrt 2 * (1 - (B + 1) / q) := by
    field_simp; ring
  rw [e1, e2] at this
  exact this

end

end Z3NetHL.Proofs

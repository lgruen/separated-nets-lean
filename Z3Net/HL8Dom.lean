module
public import Mathlib
public import Z3Net.HL8Lev

@[expose] public section

/-!
# Entry HL8, part 2: `prop:Hk`(2) with level-truncated admissibility

`HL_dom_lev` and `HL_dom_lev_real` are the proofs of `HL_dom` and `HL_dom_real` (entry HL,
`Z3Net/HLSep.lean`) verbatim, with `HL_relax` replaced by `HL_relax_lev`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

theorem HL_dom_lev (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdmL s q (min k (s - 1)) u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
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
  rcases HL_relax_lev s q k u v lam gco dg F2 hs hq hden hq7 hF2 hk x y hxy with hfar | ⟨E, J, Δ, hE, hne, hJ, hdvd, hΔ, hbd⟩
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

theorem HL_dom_lev_real (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdmL s q (min k (s - 1)) u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((Bdom s F2 : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((Bdom s F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((HLpoint s q k u v lam gco dg x c : ℤ) - (HLpoint s q k u v lam gco dg y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) := by
  have hZ := HL_dom_lev s q k u v lam gco dg F2 hs hq hden hqodd hF2 hhalf0 hhalf hdiag hdom hqB hk x y hxy
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

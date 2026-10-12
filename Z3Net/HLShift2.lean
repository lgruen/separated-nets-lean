/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.HLShift
public import Z3Net.HLGFDom
public import Z3Net.HLUpMain

@[expose] public section

/-!
# V14 stage S10′: `prop:Hk` and `thm:HL` under digital shifts (`prop:shift`)

Everything downstream of the carry relaxation uses the points only through it: `prop:Hk`(1), (2)
(`GF_relax_core`, `GF_dom_core`, `GF_dom_real_core`, `Z3Net/HLGFDom.lean`), Prop H_k(a), (b) for the
split-frame nets (`HL_relax`, `HL_dom`, `HL_dom_real`, `Z3Net/HLSep.lean`) and `thm:HL`
(`Z3Net/HLMainH.lean`). With the relaxation for the shifted net (`relaxG_shift`,
`Z3Net/HLShift.lean`) in place of `relaxG` / `relax_core`, the proofs go through verbatim. Generator
families: `Z3NetHL.graphGen s k Φ` for `GFpoint s q k Φ` (`GFpoint_shift_zero`) and
`HLGen s q k u v lam gco dg = graphGen s k (HLPhi …)` for `HLpoint` (`HLpoint_shift_zero`); the
split-frame relaxation is obtained from the graph-form one through `HL_rowDesign_core` (row `0` of
`HLPhi` is the design). The net part of `thm:HL` for the shifted net is `digPointShift_net`
(`lem:shift`).
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-! ## `prop:Hk` for every digital shift -/

/-- **`prop:shift`, `prop:Hk`(2)**, integer form, for every digital shift. -/
theorem GF_dom_shift_core (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 + 2 ≤ q) (τ : Fin s → Fin (s * k) → ZMod q)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    (q : ℤ) ^ (2 * (s * k - k - 1)) *
        min ((s : ℤ) * ((q : ℤ) - 2 * BdomL s (min k (s - 1)) F2 - 2) ^ 2)
          (8 * ((q : ℤ) - BdomL s (min k (s - 1)) F2 - 1) ^ 2) ≤
      4 * (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x) (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ y) : ℤ) := by
  set L := min k (s - 1) with hLdef
  have hL1 : 1 ≤ L := le_min hk (by omega)
  have hLs : L ≤ s - 1 := min_le_right _ _
  set G := F2T L F2 with hG
  have hG0 : ∀ c d, G 0 c d = F2 0 c d := fun c d => by simp [hG, F2T, show 0 < L by omega]
  have hGhalf0 : ∀ c d, Odd (G 0 c d) := fun c d => by rw [hG0]; exact hhalf0 c d
  have hGhalf : ∀ x c d, 1 ≤ x → Even (G x c d) := by
    intro x c d hx
    simp only [hG, F2T]
    split_ifs with h
    · exact hhalf x c d hx h
    · exact ⟨0, by ring⟩
  have hGdiag : ∀ x c, 1 ≤ x → G x c c = 0 := by
    intro x c hx
    simp only [hG, F2T]
    split_ifs with h
    · exact hdiag x c hx h
    · rfl
  have hGdom : ∀ c, (A2 s G c : ℤ) ≤ -G 0 c c := by
    intro c; rw [hG, A2_F2T F2 L hL1 hLs, ← hG, hG0]; exact hdom c
  have hBG : Bdom s G = BdomL s L F2 := Bdom_F2T F2 L hL1 hLs
  have hrowG : RowDesign s q k Φ G := rowDesign_F2T F2 q k Φ hrow
  haveI : NeZero q := ⟨by obtain ⟨t, ht⟩ := hqodd; omega⟩
  -- `B ≥ 2`, so `q ≥ 7`
  have hB2 : 2 ≤ Bdom s G := by
    obtain ⟨c0⟩ : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
    obtain ⟨d0, hd0⟩ : ∃ d0 : Fin s, d0 ≠ c0 := by
      by_cases h : (c0 : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
      · exact ⟨⟨0, by omega⟩, fun h' => h (by rw [← h'])⟩
    have hBc := Bdom_ge G c0 (hGdom c0)
    have hA : (1 : ℤ) ≤ A2 s G c0 := by
      rw [A2_eq]
      have h1 : (1 : ℤ) ≤ (mx G c0 d0 : ℤ) := by
        have := M2_le_mx G 0 (by omega) c0 d0
        have e0 : M2 G 0 c0 d0 = G 0 c0 d0 := by simp [M2]
        rw [e0] at this
        obtain ⟨t, ht⟩ := hGhalf0 c0 d0
        have : (1 : ℤ) ≤ |G 0 c0 d0| := Int.one_le_abs (by omega)
        linarith
      have := Finset.single_le_sum (f := fun d => (mx G c0 d : ℤ)) (fun d _ => by positivity)
        (mem_erase.mpr ⟨hd0, mem_univ d0⟩)
      linarith
    have := hGdom c0
    have : (2 : ℤ) ≤ Bdom s G := by linarith
    exact_mod_cast this
  rw [← hBG] at hqB ⊢
  have hq7 : 7 ≤ q := by obtain ⟨t, ht⟩ := hqodd; omega
  rw [torusDist2_cast]
  rcases relaxG_shift s q k Φ hs hq7 G hrowG hk τ x y hxy with hfar | ⟨E, J, Δ, hE, hne, hJ, hdvd, hΔ, hbd⟩
  · have hM : (q : ℤ) ^ (2 * (s * k - k)) = (q : ℤ) ^ (2 * (s * k - k - 1)) * (q : ℤ) ^ 2 := by
      rw [← pow_add]; congr 1
      have := Nat.mul_le_mul_right k (show 2 ≤ s from hs); omega
    have hmin : min ((s : ℤ) * ((q : ℤ) - 2 * Bdom s G - 2) ^ 2) (8 * ((q : ℤ) - Bdom s G - 1) ^ 2) ≤
        16 * (q : ℤ) ^ 2 := by
      refine (min_le_right _ _).trans ?_
      have h1 : 0 ≤ (q : ℤ) - Bdom s G - 1 := by
        have : (2 * Bdom s G + 2 : ℤ) ≤ q := by exact_mod_cast hqB
        have : (0 : ℤ) ≤ Bdom s G := by positivity
        linarith
      have hB0 : (0 : ℤ) ≤ Bdom s G := by positivity
      have h2 : (q : ℤ) - Bdom s G - 1 ≤ q := by linarith
      nlinarith
    calc (q : ℤ) ^ (2 * (s * k - k - 1)) * min _ _ ≤ (q : ℤ) ^ (2 * (s * k - k - 1)) * (16 * (q : ℤ) ^ 2) :=
          mul_le_mul_of_nonneg_left hmin (by positivity)
      _ = 4 * (4 * (q : ℤ) ^ (2 * (s * k - k))) := by rw [hM]; ring
      _ ≤ _ := by linarith
  · have hJ' : ∀ c, J c < s - 1 := fun c => lt_of_lt_of_le (hJ c) (min_le_right _ _)
    have hqB' : 2 * (Bdom s G : ℤ) + 2 ≤ q := by exact_mod_cast hqB
    have hqodd' : Odd (q : ℤ) := by
      obtain ⟨t, ht⟩ := hqodd; exact ⟨t, by rw [ht]; push_cast; ring⟩
    have h := dom_arith G hs hGhalf0 hGhalf hGdiag hGdom (q : ℤ) hqodd' hqB' E J Δ hE hne hJ' hdvd hΔ
    calc (q : ℤ) ^ (2 * (s * k - k - 1)) * min _ _ ≤
          (q : ℤ) ^ (2 * (s * k - k - 1)) * (4 * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 4 * ((q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2) := by ring
      _ ≤ _ := by linarith


/-- **`prop:shift`, `prop:Hk`(2)**, real form, for every digital shift. -/
theorem GF_dom_real_shift_core (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 < q) (τ : Fin s → Fin (s * k) → ZMod q)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q))
        (Real.sqrt 2 * (1 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  set B := BdomL s (min k (s - 1)) F2 with hBdef
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  rcases Nat.lt_or_ge (2 * B + 1) q with hqB2 | hqB2
  · -- `q ≥ 2B + 2`
    have hZ := GF_dom_shift_core s q k Φ F2 hs hqodd hk hrow hhalf0 hhalf hdiag hdom (by omega) τ x y hxy
    set S : ℝ := ∑ c, ((cres (q ^ (s * k))
        ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ y c : ℤ)) : ℝ)) ^ 2 with hS
    rw [sum_div_sq, ← hS]
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
  · -- `q = 2B + 1`: the bound is negative
    have hq : q = 2 * B + 1 := by omega
    have hneg : Real.sqrt s * (1 / 2 - ((B : ℝ) + 1) / q) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _)
      rw [hq]; push_cast
      rw [sub_nonpos, div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    calc min _ _ * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg ((min_le_left _ _).trans hneg) (by positivity)
      _ ≤ _ := Real.sqrt_nonneg _

/-- **`prop:shift`, `prop:Hk`(1)** for every digital shift. -/
theorem GF_relax_shift_core (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 3 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hσ : ∀ (E : Fin s → ℤ) (J : Fin s → ℕ) (c : Fin s), (∀ d, |E d| ≤ 2) →
      (∀ d, J d < min k (s - 1)) → |sig2 F2 E J c| < q)
    (LB : ℝ) (hLB : ∀ (E : Fin s → ℤ) (J : Fin s → ℕ), (∀ d, |E d| ≤ 2) → (∃ d, E d ≠ 0) →
      (∀ d, J d < min k (s - 1)) →
      LB ≤ min 2 (Real.sqrt (∑ c, ((bOpt2 q F2 E J c : ℤ) : ℝ) ^ 2) / (2 * q)))
    (τ : Fin s → Fin (s * k) → ZMod q)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    LB * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  set L := min k (s - 1) with hLdef
  have hL1 : 1 ≤ L := le_min hk (by omega)
  have hLs : L ≤ s - 1 := min_le_right _ _
  set G := F2T L F2 with hG
  have hG0 : ∀ c d, G 0 c d = F2 0 c d := fun c d => by simp [hG, F2T, show 0 < L by omega]
  have hGhalf0 : ∀ c d, Odd (G 0 c d) := fun c d => by rw [hG0]; exact hhalf0 c d
  have hGhalf : ∀ x c d, 1 ≤ x → Even (G x c d) := by
    intro x c d hx
    simp only [hG, F2T]
    split_ifs with h
    · exact hhalf x c d hx h
    · exact ⟨0, by ring⟩
  have hrowG : RowDesign s q k Φ G := rowDesign_F2T F2 q k Φ hrow
  -- `q ≥ 7`
  have hq7 : 7 ≤ q := by
    set c0 : Fin s := ⟨0, by omega⟩
    have h := hσ (fun d => 2 * Int.sign (F2 0 c0 d)) (fun _ => 0) c0
      (fun d => by
        rcases Int.sign_trichotomy (F2 0 c0 d) with h | h | h <;> rw [h] <;> norm_num)
      (fun d => by omega)
    have hval : sig2 F2 (fun d => 2 * Int.sign (F2 0 c0 d)) (fun _ => 0) c0 =
        ∑ d, 2 * |F2 0 c0 d| := by
      unfold sig2
      refine sum_congr rfl fun d _ => ?_
      rw [Finset.Icc_eq_empty_of_lt (by norm_num), sum_empty, mul_zero, add_zero, mul_assoc,
        Int.sign_mul_self_eq_abs]
    rw [hval] at h
    have hge : (s : ℤ) * 2 ≤ ∑ d, 2 * |F2 0 c0 d| := by
      have : ∑ _d : Fin s, (2 : ℤ) ≤ ∑ d, 2 * |F2 0 c0 d| := Finset.sum_le_sum fun d _ => by
        obtain ⟨t, ht⟩ := hhalf0 c0 d
        have : (1 : ℤ) ≤ |F2 0 c0 d| := Int.one_le_abs (by omega)
        linarith
      simpa [mul_comm] using this
    have hs' : (3 : ℤ) ≤ s := by exact_mod_cast hs
    have : abs (∑ d, 2 * |F2 0 c0 d|) = ∑ d, 2 * |F2 0 c0 d| :=
      abs_of_nonneg (Finset.sum_nonneg fun d _ => by positivity)
    rw [this] at h
    have : (6 : ℤ) < q := by linarith
    obtain ⟨t, ht⟩ := hqodd
    omega
  haveI : NeZero q := ⟨by omega⟩
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  set S : ℝ := ∑ c, ((cres (q ^ (s * k))
      ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ y c : ℤ)) : ℝ)) ^ 2 with hS
  rw [sum_div_sq, ← hS]
  have hSZ : (S : ℝ) = ((∑ c : Fin s, ((Z3NetU.cres (q ^ (s * k)) ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x c : ℤ) -
      (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ y c : ℤ)) : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) := by
    rw [hS]; push_cast; rfl
  have hN : (0 : ℝ) < ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by positivity
  rcases relaxG_shift s q k Φ (by omega) hq7 G hrowG hk τ x y hxy with hfar | ⟨E, J, Δ, hE, hne, hJ, hdvd, hΔ, hbd⟩
  · have hR : (q : ℝ) ^ (2 * (s * k - k - 1)) * min ((4 * (q : ℝ)) ^ 2) ((4 * (q : ℝ)) ^ 2) ≤ 4 * S := by
      rw [min_self, hSZ]
      have := (Int.cast_le (R := ℝ)).mpr hfar
      push_cast at this ⊢
      have hM : (q : ℝ) ^ (2 * (s * k - k)) = (q : ℝ) ^ (2 * (s * k - k - 1)) * (q : ℝ) ^ 2 := by
        rw [← pow_add]; congr 1
        have := Nat.mul_le_mul_right k (show 2 ≤ s by omega); omega
      rw [hM] at this
      nlinarith
    have h := real_form s q k (by omega) hk hq1 S (by positivity) _ _ hR
    rw [min_self, show 4 * (q : ℝ) / (2 * q) = 2 by field_simp; ring] at h
    have hLB2 : LB ≤ 2 := by
      set c0 : Fin s := ⟨0, by omega⟩
      refine (hLB (fun d => if d = c0 then 1 else 0) (fun _ => 0) (fun d => by split_ifs <;> norm_num)
        ⟨c0, by simp⟩ (fun d => by omega)).trans (min_le_left _ _)
    exact (mul_le_mul_of_nonneg_right hLB2 hN.le).trans h
  · set a : ℝ := Real.sqrt (∑ c, ((bOpt2 q F2 E J c : ℤ) : ℝ) ^ 2) with ha
    have hJ' : ∀ d, J d < L := hJ
    have hcoord : ∀ c, bOpt2 q F2 E J c ≤ 2 * max 0 (|(q : ℤ) * E c + Δ c| - 1) := by
      intro c
      have hpar := sig2_parity G hGhalf0 hGhalf E J c
      rw [sig2_F2T F2 L hL1 E J hJ' c] at hpar
      have hdvd' := hdvd c
      rw [sig2_F2T F2 L hL1 E J hJ' c] at hdvd'
      exact bOpt2_le q (by omega) hqodd F2 E J c (Δ c) hpar hdvd' (hΔ c) (hσ E J c hE hJ')
    have hsumZ : ∑ c, (bOpt2 q F2 E J c) ^ 2 ≤ 4 * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      have := hcoord c
      have h0 := bOpt2_nonneg q F2 E J c
      nlinarith
    have hR : (q : ℝ) ^ (2 * (s * k - k - 1)) * min (a ^ 2) (a ^ 2) ≤ 4 * S := by
      rw [min_self, ha, Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _), hSZ]
      have h1 : (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (bOpt2 q F2 E J c) ^ 2 ≤
          4 * ∑ c : Fin s, ((Z3NetU.cres (q ^ (s * k)) ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x c : ℤ) -
            (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
        calc (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (bOpt2 q F2 E J c) ^ 2 ≤
            (q : ℤ) ^ (2 * (s * k - k - 1)) * (4 * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2) :=
              mul_le_mul_of_nonneg_left hsumZ (by positivity)
          _ = 4 * ((q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2) := by
              ring
          _ ≤ _ := by linarith
      have := (Int.cast_le (R := ℝ)).mpr h1
      push_cast at this ⊢
      exact this
    have h := real_form s q k (by omega) hk hq1 S (by positivity) _ _ hR
    rw [min_self] at h
    have hLBa : LB ≤ a / (2 * q) := (hLB E J hE hne hJ).trans (min_le_right _ _)
    exact (mul_le_mul_of_nonneg_right hLBa hN.le).trans h

/-! ## Prop H_k for the split-frame nets and `thm:HL`, for every digital shift -/

/-- **`prop:shift`, Prop H_k(a)** (the carry relaxation) for every digital shift of a split-frame
net. -/
theorem HL_relax_shift_core (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hq7 : 7 ≤ q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d) (hk : 1 ≤ k)
    (τ : Fin s → Fin (s * k) → ZMod q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤
        (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x)
          (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y) : ℤ) ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x)
            (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y) : ℤ) := by
  haveI : NeZero q := ⟨by omega⟩
  rw [torusDist2_cast]
  have hrow := (HL_rowDesign_core s q k u v lam gco dg F2 hs hq hden (fun x c d _ => hF2 x c d) hk).1
  exact relaxG_shift s q k (HLPhi s q k u v lam gco dg) hs hq7 F2 hrow hk τ x y hxy

/-- **`prop:shift`, Prop H_k(b)** (integer form) for every digital shift. -/
theorem HL_dom_shift_core (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    (q : ℤ) ^ (2 * (s * k - k - 1)) *
        min ((s : ℤ) * ((q : ℤ) - 2 * Bdom s F2 - 2) ^ 2) (8 * ((q : ℤ) - Bdom s F2 - 1) ^ 2) ≤
      4 * (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y) : ℤ) := by
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
  rcases HL_relax_shift_core s q k u v lam gco dg F2 hs hq hden hq7 hF2 hk τ x y hxy with hfar | ⟨E, J, Δ, hE, hne, hJ, hdvd, hΔ, hbd⟩
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

/-- **`prop:shift`, Prop H_k(b)** (real form) for every digital shift. -/
theorem HL_dom_real_shift_core (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((Bdom s F2 : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((Bdom s F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) := by
  have hZ := HL_dom_shift_core s q k u v lam gco dg F2 hs hq hden hqodd hF2 hhalf0 hhalf hdiag hdom hqB hk τ x y hxy
  have hq1 : 1 ≤ q := by have := hq.1; omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  set S : ℝ := ∑ c, ((cres (q ^ (s * k))
      ((Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y c : ℤ)) : ℝ)) ^ 2 with hS
  have hsum : ∑ c, ((cres (q ^ (s * k))
      ((Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y c : ℤ)) : ℝ)
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

/-- **`prop:shift`, `thm:HL`**: every digital shift of the net of `H_s` is a `(0,sk,s)`-net, with the
same separation bound. -/
theorem HL_main_shift_core (s q k : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q) (hqB : 2 * BH s + 2 ≤ q)
    (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q) :
    Z3NetHL.IsNet0 s q (s * k) (Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ) ∧
      ∀ x y : Fin (s * k) → ZMod q, x ≠ y →
        (q : ℤ) ^ (2 * (s * k - k - 1)) *
            min ((s : ℤ) * ((q : ℤ) - 2 * BH s - 2) ^ 2) (8 * ((q : ℤ) - BH s - 1) ^ 2) ≤
          4 * (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ x)
            (Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ y) : ℤ) := by
  have hadm := adm_H hs q hq hqs
  have hq2 : q ≠ 2 := by omega
  have hden := den_H (s := s) q hq hq2
  haveI : NeZero q := ⟨hq.ne_zero⟩
  refine ⟨Z3NetF.Proofs.digPointShift_net _ τ (HL_net s q k uH vH (lamH s) gcoH (dgH s) hs hadm hk),
    fun x y hxy => ?_⟩
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have h := HL_dom_shift_core s q k uH vH (lamH s) gcoH (dgH s) (F2Hf s) hs hadm hden hqodd
    (fun x c d => hF2_H x c d) (F2Hf_half0 hs) (fun x c d hx => F2Hf_half x c d hx)
    (fun x c hx => F2Hf_diag x c hx) (dom_H hs) (by rw [Bdom_H hs]; exact hqB) hk τ x y hxy
  rw [Bdom_H hs] at h
  exact h

/-- **`prop:shift`, `thm:HL`**, real form, for every digital shift. -/
theorem HL_main_real_shift_core (s q k : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q)
    (hqB : 2 * BH s + 2 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BH s : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((BH s : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ x c : ℤ) -
            (Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  have hadm := adm_H hs q hq hqs
  have hq2 : q ≠ 2 := by omega
  have hden := den_H (s := s) q hq hq2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have h := HL_dom_real_shift_core s q k uH vH (lamH s) gcoH (dgH s) (F2Hf s) hs hadm hden hqodd
    (fun x c d => hF2_H x c d) (F2Hf_half0 hs) (fun x c d hx => F2Hf_half x c d hx)
    (fun x c hx => F2Hf_diag x c hx) (dom_H hs) (by rw [Bdom_H hs]; exact hqB) hk τ x y hxy
  rw [Bdom_H hs] at h
  exact h

/-- **`prop:shift`, Prop H_k(2) as printed, for the split-frame nets** (real form), for every digital
shift. -/
theorem HL_domL_real_shift_core (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, x < min k (s - 1) → 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 < q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q))
        (Real.sqrt 2 * (1 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x c : ℤ) -
            (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) :=
  GF_dom_real_shift_core s q k (HLPhi s q k u v lam gco dg) F2 hs hqodd hk
    (HL_rowDesign_core s q k u v lam gco dg F2 hs hq hden hF2 hk).1 hhalf0 hhalf hdiag hdom hqB τ x y hxy

end

end Z3NetHL.Proofs

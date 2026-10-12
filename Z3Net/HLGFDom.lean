module
public import Mathlib
public import Z3Net.HLGF

@[expose] public section

/-!
# Entry HL, stage 1, part 2: Prop H_k(1), (2) for an arbitrary graph form, levels `< L`

The design enters the relaxation only through the levels `x < L = min(k, s-1)` (the carry
lengths satisfy `J_d < L`). Truncating the doubled design to these levels (`F2T`) turns the
hypotheses of Prop H_k on the levels `< L` into the all-level hypotheses of `dom_arith`
(`Z3Net/HLDom.lean`), with `A2 s (F2T L F2) = A2L s L F2` and `Bdom s (F2T L F2) = BdomL s L F2`.

* `GF_dom_core`, `GF_dom_real_core` — Prop H_k(2) as printed (integer and real forms).
* `GF_relax_core` — Prop H_k(1): the per-option bound `b_c` (`bOpt2`): `2Δ_c` is one of the two
  options, so `2 max(0, |qE_c + Δ_c| - 1) ≥ 2b_c`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-! ## Truncation of the design -/

/-- The doubled design truncated to the levels `< L`. -/
def F2T {s : ℕ} (L : ℕ) (F2 : ℕ → Fin s → Fin s → ℤ) (x : ℕ) (c d : Fin s) : ℤ :=
  if x < L then F2 x c d else 0

variable {s : ℕ} (F2 : ℕ → Fin s → Fin s → ℤ)

lemma sig2_F2T (L : ℕ) (hL : 1 ≤ L) (E : Fin s → ℤ) (J : Fin s → ℕ) (hJ : ∀ d, J d < L)
    (c : Fin s) : sig2 (F2T L F2) E J c = sig2 F2 E J c := by
  unfold sig2
  refine sum_congr rfl fun d _ => ?_
  have h0 : F2T L F2 0 c d = F2 0 c d := by simp [F2T, show 0 < L by omega]
  rw [h0]
  congr 2
  refine sum_congr rfl fun x hx => ?_
  have := (mem_Icc.mp hx).2; have := hJ d
  simp [F2T, show x < L by omega]

lemma M2_F2T (L : ℕ) (hL : 1 ≤ L) (j : ℕ) (c d : Fin s) :
    M2 (F2T L F2) j c d = M2 F2 (min j (L - 1)) c d := by
  unfold M2
  rcases le_or_gt j (L - 1) with h | h
  · rw [min_eq_left h]
    refine sum_congr rfl fun x hx => ?_
    have := mem_range.mp hx
    simp [F2T, show x < L by omega]
  · rw [min_eq_right h.le]
    rw [← Finset.sum_range_add_sum_Ico _ (show L ≤ j + 1 by omega)]
    have e2 : ∑ x ∈ Ico L (j + 1), F2T L F2 x c d = 0 :=
      Finset.sum_eq_zero fun x hx => by simp [F2T, show ¬ x < L by have := (mem_Ico.mp hx).1; omega]
    rw [e2, add_zero, show L - 1 + 1 = L by omega]
    refine sum_congr rfl fun x hx => ?_
    have := mem_range.mp hx
    simp [F2T, this]

lemma A2_F2T (L : ℕ) (hL : 1 ≤ L) (hLs : L ≤ s - 1) (c : Fin s) :
    A2 s (F2T L F2) c = A2L s L F2 c := by
  unfold A2 A2L
  refine sum_congr rfl fun d _ => ?_
  apply le_antisymm
  · refine Finset.sup_le fun j hj => ?_
    rw [M2_F2T F2 L hL]
    exact Finset.le_sup (f := fun j => (M2 F2 j c d).natAbs)
      (mem_range.mpr (by have := min_le_right j (L - 1); omega))
  · refine Finset.sup_le fun j hj => ?_
    have hj' := mem_range.mp hj
    have := Finset.le_sup (f := fun j => (M2 (F2T L F2) j c d).natAbs)
      (mem_range.mpr (show j < s - 1 by omega))
    rwa [M2_F2T F2 L hL, min_eq_left (by omega)] at this

lemma Bdom_F2T (L : ℕ) (hL : 1 ≤ L) (hLs : L ≤ s - 1) :
    Bdom s (F2T L F2) = BdomL s L F2 := by
  unfold Bdom BdomL
  congr 1; funext c
  rw [A2_F2T F2 L hL hLs]
  simp [F2T, show 0 < L by omega]

lemma rowDesign_F2T (q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hrow : RowDesign s q k Φ F2) : RowDesign s q k Φ (F2T (min k (s - 1)) F2) := by
  intro c d r hr j
  rw [hrow c d r hr j]
  split_ifs with h
  · have := j.isLt
    simp [F2T, show k - 1 - (j : ℕ) < min k (s - 1) from lt_min (by omega) h]
  · rfl

/-! ## Prop H_k(2) as printed -/

theorem GF_dom_core (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 + 2 ≤ q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    (q : ℤ) ^ (2 * (s * k - k - 1)) *
        min ((s : ℤ) * ((q : ℤ) - 2 * BdomL s (min k (s - 1)) F2 - 2) ^ 2)
          (8 * ((q : ℤ) - BdomL s (min k (s - 1)) F2 - 1) ^ 2) ≤
      4 * (torusDist2 (q ^ (s * k)) (GFpoint s q k Φ x) (GFpoint s q k Φ y) : ℤ) := by
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
  rcases relaxG s q k Φ hs hq7 G hrowG hk x y hxy with hfar | ⟨E, J, Δ, hE, hne, hJ, hdvd, hΔ, hbd⟩
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

/-- Sum of squared real cres terms, rewritten. -/
lemma sum_div_sq {s : ℕ} (N : ℝ) (f : Fin s → ℝ) :
    ∑ c, (f c / N) ^ 2 = (∑ c, f c ^ 2) / N ^ 2 := by
  rw [Finset.sum_div]; exact Finset.sum_congr rfl fun c _ => by rw [div_pow]

theorem GF_dom_real_core (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 < q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q))
        (Real.sqrt 2 * (1 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((GFpoint s q k Φ x c : ℤ) - (GFpoint s q k Φ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  set B := BdomL s (min k (s - 1)) F2 with hBdef
  have hq1 : 1 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  rcases Nat.lt_or_ge (2 * B + 1) q with hqB2 | hqB2
  · -- `q ≥ 2B + 2`
    have hZ := GF_dom_core s q k Φ F2 hs hqodd hk hrow hhalf0 hhalf hdiag hdom (by omega) x y hxy
    set S : ℝ := ∑ c, ((cres (q ^ (s * k))
        ((GFpoint s q k Φ x c : ℤ) - (GFpoint s q k Φ y c : ℤ)) : ℝ)) ^ 2 with hS
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

/-! ## Prop H_k(1): the options -/

lemma opt_odd (q E Δ σ : ℤ) (hq : 0 < q) (hσ : Odd σ) (hdvd : q ∣ 2 * Δ - σ) (hΔ : |Δ| < q)
    (hσq : |σ| < q) : 2 * Δ = σ + q ∨ 2 * Δ = σ - q := by
  obtain ⟨t, ht⟩ := hdvd
  have htodd : Odd t := by
    by_contra h
    rw [Int.not_odd_iff_even] at h
    obtain ⟨r, hr⟩ := h
    obtain ⟨w, hw⟩ := hσ
    have : 2 * Δ - σ = 2 * (q * r) := by rw [ht, hr]; ring
    omega
  rw [abs_lt] at hΔ hσq
  have h3 : -3 < t := by
    by_contra h; push_neg at h; nlinarith
  have h4 : t < 3 := by
    by_contra h; push_neg at h; nlinarith
  obtain ⟨w, hw⟩ := htodd
  have : t = 1 ∨ t = -1 := by omega
  rcases this with h | h <;> subst h
  · left; linarith
  · right; linarith

lemma opt_even (q E Δ σ : ℤ) (hq : 0 < q) (hqodd : Odd q) (hσ : Even σ) (hdvd : q ∣ 2 * Δ - σ)
    (hΔ : |Δ| < q) (hσq : |σ| < q) : 2 * Δ = σ ∨ 2 * Δ = σ - 2 * q * Int.sign σ := by
  obtain ⟨σ', hσ'⟩ := hσ
  obtain ⟨t, ht⟩ := hdvd
  have hteven : Even t := by
    by_contra h
    rw [Int.not_even_iff_odd] at h
    have hprod : Odd (q * t) := hqodd.mul h
    rw [← ht] at hprod
    obtain ⟨w, hw⟩ := hprod
    omega
  obtain ⟨κ, hκ⟩ := hteven
  have hΔe : Δ = σ' + κ * q := by
    have h2 : 2 * Δ - σ = 2 * (κ * q) := by rw [ht, hκ]; ring
    omega
  rw [abs_lt] at hΔ hσq
  have hκ1 : κ = -1 ∨ κ = 0 ∨ κ = 1 := by
    have h1 : κ * q < 2 * q := by nlinarith
    have h2 : -(2 * q) < κ * q := by nlinarith
    have : κ < 2 := by
      by_contra h; push_neg at h; nlinarith
    have : -2 < κ := by
      by_contra h; push_neg at h; nlinarith
    omega
  rcases hκ1 with h | h | h <;> subst h
  · right
    have hpos : 0 < σ := by nlinarith
    rw [Int.sign_eq_one_of_pos hpos]; linarith
  · left; linarith
  · right
    have hneg : σ < 0 := by nlinarith
    rw [Int.sign_eq_neg_one_of_neg hneg]; linarith

lemma bOpt2_le (q : ℕ) (hq : 0 < q) (hqodd : Odd q) (F2 : ℕ → Fin s → Fin s → ℤ)
    (E : Fin s → ℤ) (J : Fin s → ℕ) (c : Fin s) (Δ : ℤ)
    (hpar : Even (sig2 F2 E J c - ∑ d, E d)) (hdvd : (q : ℤ) ∣ 2 * Δ - sig2 F2 E J c)
    (hΔ : |Δ| < q) (hσq : |sig2 F2 E J c| < q) :
    bOpt2 q F2 E J c ≤ 2 * max 0 (|(q : ℤ) * E c + Δ| - 1) := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hqodd' : Odd (q : ℤ) := by
    obtain ⟨t, ht⟩ := hqodd; exact ⟨t, by rw [ht]; push_cast; ring⟩
  have key : ∀ t : ℤ, t = 2 * ((q : ℤ) * E c + Δ) →
      max 0 (|t| - 2) = 2 * max 0 (|(q : ℤ) * E c + Δ| - 1) := by
    intro t ht
    rw [ht, abs_mul, abs_two]
    rcases le_total (|(q : ℤ) * E c + Δ| - 1) 0 with h | h
    · rw [max_eq_left (by linarith), max_eq_left h]; ring
    · rw [max_eq_right (by linarith), max_eq_right h]; ring
  unfold bOpt2
  split_ifs with hodd
  · have hσodd : Odd (sig2 F2 E J c) := by
      have hE : Odd (∑ d, E d) := Int.odd_iff.mpr hodd
      have : sig2 F2 E J c = (sig2 F2 E J c - ∑ d, E d) + ∑ d, E d := by ring
      rw [this]; exact hpar.add_odd hE
    rcases opt_odd q (E c) Δ _ hq' hσodd hdvd hΔ hσq with h | h
    · exact (min_le_left _ _).trans (le_of_eq (key _ (by linarith)))
    · exact (min_le_right _ _).trans (le_of_eq (key _ (by linarith)))
  · have hσeven : Even (sig2 F2 E J c) := by
      have hE : Even (∑ d, E d) := by
        rw [Int.even_iff]; have := Int.emod_two_eq_zero_or_one (∑ d, E d); omega
      have : sig2 F2 E J c = (sig2 F2 E J c - ∑ d, E d) + ∑ d, E d := by ring
      rw [this]; exact hpar.add hE
    rcases opt_even q (E c) Δ _ hq' hqodd' hσeven hdvd hΔ hσq with h | h
    · exact (min_le_left _ _).trans (le_of_eq (key _ (by linarith)))
    · exact (min_le_right _ _).trans (le_of_eq (key _ (by linarith)))

lemma bOpt2_nonneg (q : ℕ) (F2 : ℕ → Fin s → Fin s → ℤ) (E : Fin s → ℤ) (J : Fin s → ℕ)
    (c : Fin s) : 0 ≤ bOpt2 q F2 E J c := by
  unfold bOpt2; split_ifs <;> exact le_min (le_max_left _ _) (le_max_left _ _)

theorem GF_relax_core (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 3 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hσ : ∀ (E : Fin s → ℤ) (J : Fin s → ℕ) (c : Fin s), (∀ d, |E d| ≤ 2) →
      (∀ d, J d < min k (s - 1)) → |sig2 F2 E J c| < q)
    (LB : ℝ) (hLB : ∀ (E : Fin s → ℤ) (J : Fin s → ℕ), (∀ d, |E d| ≤ 2) → (∃ d, E d ≠ 0) →
      (∀ d, J d < min k (s - 1)) →
      LB ≤ min 2 (Real.sqrt (∑ c, ((bOpt2 q F2 E J c : ℤ) : ℝ) ^ 2) / (2 * q)))
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    LB * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((GFpoint s q k Φ x c : ℤ) - (GFpoint s q k Φ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
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
      ((GFpoint s q k Φ x c : ℤ) - (GFpoint s q k Φ y c : ℤ)) : ℝ)) ^ 2 with hS
  rw [sum_div_sq, ← hS]
  have hSZ : (S : ℝ) = ((∑ c : Fin s, ((Z3NetU.cres (q ^ (s * k)) ((GFpoint s q k Φ x c : ℤ) -
      (GFpoint s q k Φ y c : ℤ)) : ℕ) : ℤ) ^ 2 : ℤ) : ℝ) := by
    rw [hS]; push_cast; rfl
  have hN : (0 : ℝ) < ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by positivity
  rcases relaxG s q k Φ (by omega) hq7 G hrowG hk x y hxy with hfar | ⟨E, J, Δ, hE, hne, hJ, hdvd, hΔ, hbd⟩
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
          4 * ∑ c : Fin s, ((Z3NetU.cres (q ^ (s * k)) ((GFpoint s q k Φ x c : ℤ) -
            (GFpoint s q k Φ y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
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

end

end Z3NetHL.Proofs

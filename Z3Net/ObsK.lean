/-
Proof module of entry Obs: the sentence after `def:Ktrue` (the ceiling `1 - K_pair/q + O(q^-2)`
with an explicit constant) and the "hence" clause of `thm:L`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsL

@[expose] public section

/-!
# Entry Obs: the ceilings in terms of `K_pair`

By `cor:ceils`(i) for the diagonal entry realizing `K_pair` and `prop:P2` for a two-axis
configuration realizing it (and `cor:ceils`(ii), `prop:P2` second statement if `K_pair = ∞`), with
`k ≥ 3`, `3k + 4 ≤ sk`, `|M̃| ≤ C`, `q > 4sC`: `δ N^(1/s) < 1 - K_pair/q + 6sC²/q²`, resp.
`< 3√s C/q`. The constant `6` comes from `√(α² + β) ≤ α + β/(2α)` with `α ≥ 7/8`.
-/

namespace Z3NetF.Proofs

open Matrix Finset ObsCount ObsStep ObsCeil ObsP2 ObsL

noncomputable section

namespace ObsK

lemma fin_bound (x t δ β : ℝ) (ht0 : 0 ≤ t) (htd : t ≤ δ) (hx : x ≤ 1)
    (hβ : β ≤ (δ - t) * (2 - 2 * x)) : (1 - x + t) ^ 2 + β ≤ (1 - x + δ) ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr htd) (add_nonneg ht0 (le_trans ht0 htd))]

lemma abs_sig_le {s : ℕ} (M : Fin s → Fin s → ℤ) (C : ℕ) (hC : ∀ c d, |M c d| ≤ C) (a b : Fin s)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (c : Fin s) : |Z3NetF.sig M a b ε c| ≤ 2 * C := by
  unfold Z3NetF.sig
  calc |M c a + ε * M c b| ≤ |M c a| + |ε * M c b| := abs_add_le _ _
    _ = |M c a| + |M c b| := by
        rw [abs_mul, show |ε| = 1 by rcases hε with rfl | rfl <;> simp, one_mul]
    _ ≤ 2 * C := by have := hC c a; have := hC c b; linarith

lemma sum_sig_lt {s q : ℕ} (M : Fin s → Fin s → ℤ) (C : ℕ) (hC : ∀ c d, |M c d| ≤ C)
    (hq : 4 * s * C < q) (a b : Fin s) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∑ c, |Z3NetF.sig M a b ε c| < q := by
  calc ∑ c, |Z3NetF.sig M a b ε c| ≤ ∑ _c : Fin s, (2 * (C : ℤ)) :=
        Finset.sum_le_sum fun c _ => abs_sig_le M C hC a b ε hε c
    _ = 2 * s * C := by simp; ring
    _ < q := by
        have : ((4 * s * C : ℕ) : ℤ) < q := by exact_mod_cast hq
        push_cast at this
        have : (0 : ℤ) ≤ s * C := by positivity
        linarith

lemma col_lt {s q : ℕ} (M : Fin s → Fin s → ℤ) (C : ℕ) (hC : ∀ c d, |M c d| ≤ C)
    (hq : 4 * s * C < q) (a : Fin s) : ∑ u ∈ univ.erase a, |M u a| < q := by
  calc ∑ u ∈ univ.erase a, |M u a| ≤ ∑ u : Fin s, |M u a| :=
        Finset.sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ _u : Fin s, (C : ℤ) := Finset.sum_le_sum fun u _ => hC u a
    _ = s * C := by simp
    _ < q := by
        have : ((4 * s * C : ℕ) : ℤ) < q := by exact_mod_cast hq
        push_cast at this
        have : (0 : ℤ) ≤ s * C := by positivity
        linarith

variable {s q k : ℕ}

theorem Ktrue_ceiling {C : ℕ} (hs : 4 ≤ s) (hk : 3 ≤ k) (h3k : 3 * k + 4 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (hdiag : ∀ a, Z3NetF.Mt Φ a a ≠ 0)
    (hC : ∀ c d, |Z3NetF.Mt Φ c d| ≤ C) (hq : 4 * s * C < q) :
    (Z3NetF.Kpair (Z3NetF.Mt Φ) = ⊤ →
        Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ) (9 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2)) ∧
      ∀ K : ℕ, Z3NetF.Kpair (Z3NetF.Mt Φ) = K → Z3NetF.PairBelow q (s * k) k
        (Z3NetF.gfPoint q k Φ) ((1 - (K : ℝ) / q + 6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2) ^ 2) := by
  classical
  set M := Z3NetF.Mt Φ with hM
  have hC1 : 1 ≤ C := by
    have h1 := hC ⟨0, by omega⟩ ⟨0, by omega⟩
    have h2 := hdiag ⟨0, by omega⟩
    have : (1 : ℤ) ≤ C := le_trans (Int.one_le_abs h2) h1
    exact_mod_cast this
  have hq16 : 16 ≤ q := by nlinarith
  haveI : NeZero q := ⟨by omega⟩
  have hq3 : 3 ≤ q := by omega
  have hk2 : 2 ≤ k := by omega
  have hsk3 : 3 * k + 3 ≤ s * k := by omega
  -- real facts
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC1
  have hsr : (4 : ℝ) ≤ s := by exact_mod_cast hs
  have hqC : 4 * (s : ℝ) * C < q := by exact_mod_cast hq
  set u : ℝ := (C : ℝ) ^ 2 / (q : ℝ) ^ 2 with hu
  have hu0 : 0 < u := by positivity
  have hinvq : 1 / (q : ℝ) ^ 2 ≤ u := by
    rw [hu]; apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  have hCq : (C : ℝ) / q ≤ 1 / 16 := by
    rw [div_le_iff₀ hqr]; nlinarith
  constructor
  · intro htop
    have hP := (Kpair_eq_top_iff M).1 htop
    rcases hP with ⟨a, ha⟩ | ⟨a, b, hab, ε, hε, ha, hb⟩
    · refine PairBelow_mono ?_ (ceils_pos_C (by omega) hq3 hk2 Φ hnet a (col_lt M C hC hq a)
        ha hC)
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h : ((C : ℝ) + 1) ^ 2 ≤ 9 * (C : ℝ) ^ 2 := by nlinarith
      calc (s : ℝ) * ((C : ℝ) + 1) ^ 2 ≤ s * (9 * (C : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = 9 * s * (C : ℝ) ^ 2 := by ring
    · have hε' : ε = 1 ∨ ε = -1 := by simpa using hε
      refine PairBelow_mono ?_ (P2_forward_C hs hsk3 Φ hnet a b hab ε hε' ha hb
        (sum_sig_lt M C hC hq a b ε hε') hC)
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h : (2 * (C : ℝ) + 1) ^ 2 ≤ 9 * (C : ℝ) ^ 2 := by nlinarith
      calc (s : ℝ) * (2 * (C : ℝ) + 1) ^ 2 ≤ s * (9 * (C : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = 9 * s * (C : ℝ) ^ 2 := by ring
  · intro K hK
    have hP : ¬ Z3NetF.PairInf M := fun h => by
      rw [Kpair_top M h] at hK; exact ENat.top_ne_natCast K hK
    have hKv : K = Z3NetF.pairVal M := by
      rw [Kpair_fin M hP] at hK; exact_mod_cast hK.symm
    have hδ : (6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2) = 6 * s * u := by rw [hu]; ring
    rcases pairVal_attained M (by omega) with ⟨a, ha⟩ | ⟨a, b, hab, ε, hε, hσa, hσb, hval⟩
    · -- the diagonal entry
      have hneg : M a a ≤ -1 := by
        have h1 : ¬ 0 < M a a := fun h => hP (Or.inl ⟨a, h⟩)
        have := hdiag a; omega
      have hKa : ((|M a a| : ℤ) : ℝ) = K := by
        rw [hKv, ha, Nat.cast_natAbs]
      refine PairBelow_mono ?_ (ceils_neg (by omega) hq3 hk2 Φ hnet a (col_lt M C hC hq a) hneg)
      rw [hKa, hδ]
      have ht0 : (0 : ℝ) ≤ 1 / (q : ℝ) ^ (k - 1) := by positivity
      have ht : 1 / (q : ℝ) ^ (k - 1) ≤ u := by
        refine le_trans ?_ hinvq
        apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ q by omega)) (by omega)
      have hKC : (K : ℝ) ≤ C := by
        have := hC a a; rw [← hKa]; exact_mod_cast this
      have hx : (K : ℝ) / q ≤ 1 / 16 := le_trans (div_le_div_of_nonneg_right hKC hqr.le) hCq
      have hβ : ∑ u ∈ univ.erase a, (((|M u a| : ℤ) : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ≤
          4 * ((s : ℝ) - 1) * u := by
        calc ∑ u ∈ univ.erase a, (((|M u a| : ℤ) : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2
            ≤ ∑ _u ∈ univ.erase a, 4 * u := Finset.sum_le_sum fun c _ => by
              rw [hu, ← mul_div_assoc]
              apply div_le_div_of_nonneg_right _ (by positivity)
              have h1 : ((|M c a| : ℤ) : ℝ) ≤ C := by exact_mod_cast hC c a
              have h0 : (0 : ℝ) ≤ ((|M c a| : ℤ) : ℝ) := by positivity
              nlinarith
          _ = 4 * ((s : ℝ) - 1) * u := by
              rw [Finset.sum_const, card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin,
                nsmul_eq_mul, Nat.cast_sub (by omega)]
              push_cast; ring
      refine fin_bound _ _ _ _ ht0 (by nlinarith) (by linarith) ?_
      have h1 : (6 * (s : ℝ) - 1) * u ≤ 6 * s * u - 1 / (q : ℝ) ^ (k - 1) := by linarith [ht]
      have h2 : (15 / 8 : ℝ) ≤ 2 - 2 * ((K : ℝ) / q) := by linarith
      calc _ ≤ 4 * ((s : ℝ) - 1) * u := hβ
        _ ≤ (6 * (s : ℝ) - 1) * u * (15 / 8) := by
            nlinarith [mul_nonneg hu0.le (by positivity : (0 : ℝ) ≤ s)]
        _ ≤ (6 * s * u - 1 / (q : ℝ) ^ (k - 1)) * (2 - 2 * ((K : ℝ) / q)) := by
            have : 0 ≤ (6 * (s : ℝ) - 1) * u := mul_nonneg (by linarith) hu0.le
            apply mul_le_mul h1 h2 (by norm_num) (by linarith)
    · -- a two-axis configuration
      have hε' : ε = 1 ∨ ε = -1 := by simpa using hε
      have hKb : ((|Z3NetF.sig M a b ε b| : ℤ) : ℝ) = K := by
        rw [hKv, hval, Nat.cast_natAbs]
      refine PairBelow_mono ?_ (P2_ceiling hs h3k Φ hnet a b hab ε hε' hσa hσb
        (sum_sig_lt M C hC hq a b ε hε'))
      rw [hKb, hδ]
      have hsig := abs_sig_le M C hC a b ε hε'
      have ht0 : (0 : ℝ) ≤ 1 / (q : ℝ) ^ 2 := by positivity
      have hKC : (K : ℝ) ≤ 2 * C := by
        have := hsig b; rw [← hKb]; exact_mod_cast this
      have hx : (K : ℝ) / q ≤ 1 / 8 := by
        rw [div_le_iff₀ hqr]; nlinarith
      have hterm : ∀ c, (((|Z3NetF.sig M a b ε c| : ℤ) : ℝ) + 1) ^ 2 ≤ 9 * (C : ℝ) ^ 2 := by
        intro c
        have h1 : ((|Z3NetF.sig M a b ε c| : ℤ) : ℝ) ≤ 2 * C := by exact_mod_cast hsig c
        have h0 : (0 : ℝ) ≤ ((|Z3NetF.sig M a b ε c| : ℤ) : ℝ) := by positivity
        nlinarith
      have hβ : ((((Z3NetF.sig M a b ε a + 1 : ℤ)) : ℝ) ^ 2 +
          ∑ u ∈ (univ.erase a).erase b, (((|Z3NetF.sig M a b ε u| : ℤ) : ℝ) + 1) ^ 2) /
            (q : ℝ) ^ 2 ≤ 9 * ((s : ℝ) - 1) * u := by
        have ha' := hterm a
        rw [abs_of_pos hσa] at ha'
        have hsum : ∑ u ∈ (univ.erase a).erase b, (((|Z3NetF.sig M a b ε u| : ℤ) : ℝ) + 1) ^ 2 ≤
            ((s : ℝ) - 2) * (9 * (C : ℝ) ^ 2) := by
          calc _ ≤ ∑ _u ∈ (univ.erase a).erase b, 9 * (C : ℝ) ^ 2 :=
                Finset.sum_le_sum fun c _ => hterm c
            _ = ((s : ℝ) - 2) * (9 * (C : ℝ) ^ 2) := by
                rw [Finset.sum_const, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩),
                  card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin, nsmul_eq_mul]
                rw [show s - 1 - 1 = s - 2 by omega, Nat.cast_sub (by omega)]
                push_cast; ring
        rw [hu, div_le_iff₀ (by positivity)]
        push_cast at ha' hsum ⊢
        have : 9 * ((s : ℝ) - 1) * ((C : ℝ) ^ 2 / (q : ℝ) ^ 2) * (q : ℝ) ^ 2 =
            9 * ((s : ℝ) - 1) * (C : ℝ) ^ 2 := by field_simp
        rw [this]
        linarith [ha', hsum]
      refine fin_bound _ _ _ _ ht0 (by nlinarith) (by linarith) ?_
      have h1 : (6 * (s : ℝ) - 1) * u ≤ 6 * s * u - 1 / (q : ℝ) ^ 2 := by linarith [hinvq]
      have h2 : (7 / 4 : ℝ) ≤ 2 - 2 * ((K : ℝ) / q) := by linarith
      calc _ ≤ 9 * ((s : ℝ) - 1) * u := hβ
        _ ≤ (6 * (s : ℝ) - 1) * u * (7 / 4) := by
            nlinarith [mul_nonneg hu0.le (by positivity : (0 : ℝ) ≤ s)]
        _ ≤ (6 * s * u - 1 / (q : ℝ) ^ 2) * (2 - 2 * ((K : ℝ) / q)) := by
            have : 0 ≤ (6 * (s : ℝ) - 1) * u := mul_nonneg (by linarith) hu0.le
            apply mul_le_mul h1 h2 (by norm_num) (by linarith)

/-- The two cases of the sentence after `def:Ktrue` combined with a lower bound `K_min` on
`K_pair` (used for `thm:L` with `K_min = √((s-3)/8)` and for `thm:O5` with `K_min = 2`). -/
theorem ceiling_of_Kmin {C : ℕ} (hs : 4 ≤ s) (hk : 3 ≤ k) (h3k : 3 * k + 4 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (hdiag : ∀ a, Z3NetF.Mt Φ a a ≠ 0)
    (hC : ∀ c d, |Z3NetF.Mt Φ c d| ≤ C) (hq : 4 * s * C < q) (Kmin : ℝ) (hK0 : 0 ≤ Kmin)
    (hKs : Kmin ≤ s)
    (hKmin : Z3NetF.Kpair (Z3NetF.Mt Φ) = ⊤ ∨
      ∃ K : ℕ, Z3NetF.Kpair (Z3NetF.Mt Φ) = K ∧ Kmin ≤ K) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      ((1 - Kmin / q + 6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2) ^ 2) := by
  have hC1 : 1 ≤ C := by
    have h1 := hC ⟨0, by omega⟩ ⟨0, by omega⟩
    have h2 := hdiag ⟨0, by omega⟩
    have : (1 : ℤ) ≤ C := le_trans (Int.one_le_abs h2) h1
    exact_mod_cast this
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC1
  have hsr : (4 : ℝ) ≤ s := by exact_mod_cast hs
  have hqC : 4 * (s : ℝ) * C < q := by exact_mod_cast hq
  have hδ : 0 ≤ 6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2 := by positivity
  have hKq : Kmin / q ≤ 1 / 4 := by
    rw [div_le_iff₀ hqr]; nlinarith
  obtain ⟨htop, hfin⟩ := Ktrue_ceiling hs hk h3k Φ hnet hdiag hC hq
  rcases hKmin with h | ⟨K, hK, hKK⟩
  · refine PairBelow_mono ?_ (htop h)
    have h1 : 9 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2 ≤ 9 / 16 := by
      rw [div_le_iff₀ (by positivity)]
      have hq2 : (4 * (s : ℝ) * C) ^ 2 ≤ (q : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hqC.le 2
      have : (s : ℝ) * (C : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 * (C : ℝ) ^ 2 := by nlinarith
      nlinarith
    have h2 : (3 / 4 : ℝ) ≤ 1 - Kmin / q + 6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2 := by linarith
    calc 9 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2 ≤ (3 / 4) ^ 2 := by linarith
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h2 2
  · refine PairBelow_mono ?_ (hfin K hK)
    have hKv : K ≤ 2 * C := by
      have hP : ¬ Z3NetF.PairInf (Z3NetF.Mt Φ) := fun h => by
        rw [ObsL.Kpair_top _ h] at hK; exact ENat.top_ne_natCast K hK
      rw [ObsL.Kpair_fin _ hP] at hK
      have : K = Z3NetF.pairVal (Z3NetF.Mt Φ) := by exact_mod_cast hK.symm
      rw [this]; exact ObsL.pairVal_le _ C hC
    have hKr : (K : ℝ) ≤ 2 * C := by exact_mod_cast hKv
    have hKq' : (K : ℝ) / q ≤ 1 / 2 := by
      rw [div_le_iff₀ hqr]; nlinarith
    have h0 : 0 ≤ 1 - (K : ℝ) / q + 6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2 := by linarith
    have h1 : 1 - (K : ℝ) / q + 6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2 ≤
        1 - Kmin / q + 6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2 := by
      have : Kmin / q ≤ (K : ℝ) / q := div_le_div_of_nonneg_right hKK hqr.le
      linarith
    exact pow_le_pow_left₀ h0 h1 2

theorem L_ceiling {C : ℕ} (hs : 4 ≤ s) (hk : 3 ≤ k) (h3k : 3 * k + 4 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (hdiag : ∀ a, Z3NetF.Mt Φ a a ≠ 0)
    (hC : ∀ c d, |Z3NetF.Mt Φ c d| ≤ C) (hq : 4 * s * C < q) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      ((1 - Real.sqrt (((s : ℝ) - 3) / 8) / q + 6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2) ^ 2) := by
  have hC1 : 1 ≤ C := by
    have h1 := hC ⟨0, by omega⟩ ⟨0, by omega⟩
    have h2 := hdiag ⟨0, by omega⟩
    have : (1 : ℤ) ≤ C := le_trans (Int.one_le_abs h2) h1
    exact_mod_cast this
  haveI : NeZero q := ⟨Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hq)⟩
  have hsr : (4 : ℝ) ≤ s := by exact_mod_cast hs
  refine ceiling_of_Kmin hs hk h3k Φ hnet hdiag hC hq _ (Real.sqrt_nonneg _) ?_
    (ObsL.L_Kpair hs (by nlinarith) (by omega) Φ hnet hdiag)
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

end ObsK

alias Ktrue_ceiling := ObsK.Ktrue_ceiling
alias L_ceiling := ObsK.L_ceiling

end

end Z3NetF.Proofs

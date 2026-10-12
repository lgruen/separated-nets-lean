module
public import Mathlib
public import Z3Net.HL8B8
public import Z3Net.HLUpMain

@[expose] public section

/-!
# Entry HL8, part 5: the `s = 8` limit `δ N^(1/8) → √2`

Lower bound: `B8_sep_real` (for `q` above all exceptional primes), with
`min(√8 (1/2 - η), √2 (1 - η)) ≥ √2 - 3η`. Upper bound: entry HL's `prop:Hk`(3) for graph forms
(`GF_upper_core`) applied to the split-frame net through `HL_rowDesign_core`, with
`min(√8/2, √2) = √2` and `C2max 8 F2B8 = 164091931`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

lemma B8_C2max : C2max 8 F2B8 = 164091931 := by decide +kernel

lemma sqrt8_eq : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

lemma sqrt2_le : Real.sqrt 2 ≤ 1.5 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem B8_limit (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ q k : ℕ, q.Prime → P ≤ q → 1 ≤ k →
      (∀ x y : Fin (8 * k) → ZMod q, x ≠ y →
        (Real.sqrt 2 - ε) * ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ)))
          ≤ Real.sqrt (∑ c, ((cres (q ^ (8 * k))
              ((HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 x c : ℤ) -
                (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 y c : ℤ)) : ℝ) / (q : ℝ) ^ (8 * k)) ^ 2)) ∧
      ∃ x y : Fin (8 * k) → ZMod q, x ≠ y ∧
        Real.sqrt (∑ c, (((HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 x c : ℝ) -
            (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 y c : ℝ)) / (q : ℝ) ^ (8 * k)) ^ 2)
          ≤ (Real.sqrt 2 + ε) * ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ))) := by
  set K : ℝ := 3 * ((328183863 : ℝ) + 164091932) / ε
  refine ⟨⌈K⌉₊ + 3061420595774, fun q k hq hP hk => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hKq : K ≤ q := by
    have := Nat.le_ceil K
    have : (⌈K⌉₊ : ℝ) ≤ q := by exact_mod_cast (show ⌈K⌉₊ ≤ q by omega)
    linarith
  have hKe : 3 * ((328183863 : ℝ) + 164091932) ≤ ε * q := by
    have := mul_le_mul_of_nonneg_left hKq hε.le
    simp only [K] at this
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  have hNp : (0 : ℝ) < ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ))) := by positivity
  have hs2 := sqrt2_le
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  constructor
  · intro x y hxy
    have h := B8_sep_real q k hq (by omega) hk (fun _ => by omega)
      (fun _ => by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) x y hxy
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hNp.le) h
    have hη : 3 * (((328183862 : ℝ) + 1) / q) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hq0]; nlinarith
    have hη0 : 0 ≤ ((328183862 : ℝ) + 1) / q := by positivity
    rw [sqrt8_eq]
    apply le_min <;> nlinarith
  · have hadmL := adm_B8 q 7 hq (by omega) (fun _ => by omega)
      (fun _ => by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
    have hadm : HLAdm 8 q uB8 vB8 lamB8 gcoB8 :=
      ⟨hadmL.1, hadmL.2.1, hadmL.2.2.1, fun d n hn => hadmL.2.2.2 d n (by simpa using hn)⟩
    obtain ⟨hrow, hpt⟩ := HL_rowDesign_core 8 q k uB8 vB8 lamB8 gcoB8 dgB8 F2B8 (by norm_num) hadm
      (den_B8 q hq (by omega)) (fun x c d _ => B8_design x c d) hk
    have hqC : 2 * 8 * C2max 8 F2B8 + 2 < q := by rw [B8_C2max]; omega
    obtain ⟨x, y, hxy, h⟩ := GF_upper_core 8 q k (HLPhi 8 q k uB8 vB8 lamB8 gcoB8 dgB8) F2B8
      (by norm_num) hq hk hrow B8_dom.1 hqC
    refine ⟨x, y, hxy, ?_⟩
    simp only [← hpt] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hNp.le)
    rw [B8_C2max, show ((8 : ℕ) : ℝ) = 8 by norm_num, sqrt8_eq]
    have hmin : min (2 * Real.sqrt 2 / 2) (Real.sqrt 2) = Real.sqrt 2 := by
      rw [show 2 * Real.sqrt 2 / 2 = Real.sqrt 2 by ring, min_self]
    rw [hmin]
    have : 2 * Real.sqrt 2 * ((164091931 : ℕ) + 1 : ℝ) / q ≤ ε := by
      rw [div_le_iff₀ hq0]; push_cast; nlinarith
    push_cast at this ⊢
    linarith

end

end Z3NetHL.Proofs

/-
Proof module (V14 stage S16′): `rem:accounting`, the expansion of `LB` of `prop:Hk`(1) at `k = 1`, `s = 5`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.AcctTwo

@[expose] public section

/-!
# `rem:accounting`: `LB = (√5/2)(1 − 2(dr + 5)/(5p)) + O(p⁻²)` for `prop:Hk`(1) under (Gap)

At `k = 1` (`L = 1`, no carries) the options of `prop:Hk`(1) are those of `lem:R2` without the second digit, and the
jitter costs `1` in every coordinate (doubled: `2b_c = max(0, |2pE_c + 2t| − 2)`, `bOpt2` with `J = 0`).

* `hk_opt_bind`, `hk_opt_bind_up`: on a binding step every option is `≥ p − 2dr_c(E)`, and the shorter one is
  `≤ p − 2dr_c(E)` (doubled); `hk_opt_gen`: on any step every option is `≥ p · 2ℓ_c(E) − |2β_c|`.
* `sum_hk_ge` (with (Gap) on the non-binding steps): `∑_c (2b_c)² ≥ 5p² − 2p (2dr + 10)` on every step for `p ≥ P`;
  `sum_hk_up`: on the binding step attaining `dr`, `∑_c (2b_c)² ≤ 5p² − 2p (2dr + 10) + C`.
* `LBgen_ge`, `LBgen_le`: the real bookkeeping (as `LB2R_ge`, `LB2R_le` of `Z3Net/AcctUp.lean`, `Z3Net/AcctTwo.lean`,
  for any family of step values); `acct_LBHk_core`: both halves.
-/

namespace Z3NetHL.Proofs.Acct

open Finset Matrix Z3NetHL Z3NetHL.Proofs

noncomputable section

/-! ## The options at `k = 1` -/

lemma sig2_k1 (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) :
    sig2 (fun _ => F2) E (fun _ => 0) c = dotR F2 E c := by
  unfold sig2 dotR
  refine Finset.sum_congr rfl fun d _ => ?_
  have : (Icc 1 0 : Finset ℕ) = ∅ := by decide
  rw [this, Finset.sum_empty, mul_zero, add_zero, mul_comm]

lemma bOpt2_k1 (q : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) :
    bOpt2 q (fun _ => F2) E (fun _ => 0) c =
      if (∑ d, E d) % 2 = 1 then
        min (max 0 (|2 * (q : ℤ) * E c + dotR F2 E c + q| - 2)) (max 0 (|2 * (q : ℤ) * E c + dotR F2 E c - q| - 2))
      else
        min (max 0 (|2 * (q : ℤ) * E c + dotR F2 E c| - 2))
          (max 0 (|2 * (q : ℤ) * E c + dotR F2 E c - 2 * q * Int.sign (dotR F2 E c)| - 2)) := by
  unfold bOpt2; rw [sig2_k1]

lemma bOpt2_k1_nonneg (q : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) :
    0 ≤ bOpt2 q (fun _ => F2) E (fun _ => 0) c := by
  rw [bOpt2_k1]; split_ifs <;> exact le_min (le_max_left _ _) (le_max_left _ _)

/-- **Binding steps, every option**: `|2pE_c + 2t| ≥ p − 2dr_c(E)` for `E_c ∈ {-1, 0, 1}`, `2t ∈ {B + p, B − p}`,
`B = 2β_c ≠ 0`, `|B| + 2 ≤ p`. -/
lemma hk_opt_bind (p e B : ℤ) (he : e = -1 ∨ e = 0 ∨ e = 1) (hBp : |B| + 2 ≤ p) (t2 : ℤ)
    (ht : t2 = B + p ∨ t2 = B - p) :
    p - (if e = 0 then |B| else -(e * B)) ≤ |2 * p * e + t2| := by
  rcases abs_cases B with ⟨hB1, hB2⟩ | ⟨hB1, hB2⟩ <;> rw [hB1] at hBp ⊢ <;>
    rcases he with rfl | rfl | rfl <;> rcases ht with rfl | rfl <;> split_ifs with h0 <;>
    rw [le_abs] <;> omega

/-- **Binding steps, the shorter option**: some `2t ∈ {B + p, B − p}` has `|2pE_c + 2t| ≤ p − 2dr_c(E)`. -/
lemma hk_opt_bind_up (p e B : ℤ) (he : e = -1 ∨ e = 0 ∨ e = 1) (hB : B ≠ 0) (hBp : |B| + 2 ≤ p) :
    ∃ t2 : ℤ, (t2 = B + p ∨ t2 = B - p) ∧ |2 * p * e + t2| ≤ p - (if e = 0 then |B| else -(e * B)) := by
  rcases lt_or_gt_of_ne hB with hb | hb
  · rw [abs_of_neg hb] at hBp ⊢
    rcases he with rfl | rfl | rfl
    · exact ⟨B + p, Or.inl rfl, by rw [abs_le]; constructor <;> norm_num <;> omega⟩
    · exact ⟨B + p, Or.inl rfl, by rw [abs_le]; constructor <;> norm_num <;> omega⟩
    · exact ⟨B - p, Or.inr rfl, by rw [abs_le]; constructor <;> norm_num <;> omega⟩
  · rw [abs_of_pos hb] at hBp ⊢
    rcases he with rfl | rfl | rfl
    · exact ⟨B + p, Or.inl rfl, by rw [abs_le]; constructor <;> norm_num <;> omega⟩
    · exact ⟨B - p, Or.inr rfl, by rw [abs_le]; constructor <;> omega⟩
    · exact ⟨B - p, Or.inr rfl, by rw [abs_le]; constructor <;> norm_num <;> omega⟩

lemma abs_lin_ge (p g B : ℤ) (hp : 0 < p) : p * |g| - |B| ≤ |p * g + B| := by
  have h := abs_add_le (p * g + B) (-B)
  rw [add_neg_cancel_right, abs_neg, abs_mul, abs_of_pos hp] at h
  linarith

/-- **Binding steps**: `2b_c ≥ p − 2dr_c(E) − 2`. -/
lemma bOpt2_bind (p : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (hE : E ∈ bind5) (c : Fin 5)
    (hB : |dotR F2 E c| + 2 ≤ p) :
    (p : ℤ) - drc2 F2 E c - 2 ≤ bOpt2 p (fun _ => F2) E (fun _ => 0) c := by
  rw [TD.mem_bind5] at hE
  have hs : (∑ d, E d) % 2 = 1 := by rw [Fin.sum_univ_five]; exact hE.2
  have he : E c = -1 ∨ E c = 0 ∨ E c = 1 := by have := hE.1 c; omega
  rw [bOpt2_k1]
  simp only [hs, ↓reduceIte]
  have h1 := hk_opt_bind p (E c) (dotR F2 E c) he hB _ (Or.inl rfl)
  have h2 := hk_opt_bind p (E c) (dotR F2 E c) he hB _ (Or.inr rfl)
  unfold drc2
  refine le_min (le_max_of_le_right ?_) (le_max_of_le_right ?_)
  · rw [show 2 * (p : ℤ) * E c + dotR F2 E c + p = 2 * p * E c + (dotR F2 E c + p) by ring]; linarith
  · rw [show 2 * (p : ℤ) * E c + dotR F2 E c - p = 2 * p * E c + (dotR F2 E c - p) by ring]; linarith

/-- **The binding step from above**: `2b_c ≤ p − 2dr_c(E) − 2` for odd `F2`. -/
lemma bOpt2_bind_up (p : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (E : Fin 5 → ℤ)
    (hE : E ∈ bind5) (c : Fin 5) (hB : |dotR F2 E c| + 2 ≤ p) :
    bOpt2 p (fun _ => F2) E (fun _ => 0) c ≤ (p : ℤ) - drc2 F2 E c - 2 := by
  rw [TD.mem_bind5] at hE
  have hs : (∑ d, E d) % 2 = 1 := by rw [Fin.sum_univ_five]; exact hE.2
  have he : E c = -1 ∨ E c = 0 ∨ E c = 1 := by have := hE.1 c; omega
  have hB0 : dotR F2 E c ≠ 0 := by
    intro h0; have := dotR_odd_of_bind F2 hodd E hs c; rw [h0] at this; exact absurd this (by decide)
  obtain ⟨t2, ht, hle⟩ := hk_opt_bind_up p (E c) (dotR F2 E c) he hB0 hB
  have hlo := hk_opt_bind p (E c) (dotR F2 E c) he hB t2 ht
  have hdr : drc2 F2 E c ≤ |dotR F2 E c| := by
    unfold drc2; split_ifs
    · exact le_rfl
    · have h2 : |E c| ≤ 1 := by rcases he with h | h | h <;> rw [h] <;> norm_num
      have := neg_abs_le (E c * dotR F2 E c)
      rw [abs_mul] at this
      nlinarith [abs_nonneg (dotR F2 E c)]
  rw [bOpt2_k1]
  simp only [hs, ↓reduceIte]
  unfold drc2 at hdr ⊢
  rcases ht with rfl | rfl
  · refine (min_le_left _ _).trans (max_le (by linarith) ?_)
    rw [show 2 * (p : ℤ) * E c + dotR F2 E c + p = 2 * p * E c + (dotR F2 E c + p) by ring]; linarith
  · refine (min_le_right _ _).trans (max_le (by linarith) ?_)
    rw [show 2 * (p : ℤ) * E c + dotR F2 E c - p = 2 * p * E c + (dotR F2 E c - p) by ring]; linarith

/-- **Any step**: `2b_c ≥ p · 2ℓ_c(E) − |2β_c| − 2`. -/
lemma bOpt2_gen (p : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) (hp : 0 < p) :
    (p : ℤ) * ell2 F2 E c - |dotR F2 E c| - 2 ≤ bOpt2 p (fun _ => F2) E (fun _ => 0) c := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  rw [bOpt2_k1]
  unfold ell2
  split_ifs with hs
  · have h1 := abs_lin_ge p (2 * E c + 1) (dotR F2 E c) hp'
    have h2 := abs_lin_ge p (2 * E c - 1) (dotR F2 E c) hp'
    have m1 := min_le_left |2 * E c + 1| |2 * E c - 1|
    have m2 := min_le_right |2 * E c + 1| |2 * E c - 1|
    refine le_min (le_max_of_le_right ?_) (le_max_of_le_right ?_)
    · rw [show 2 * (p : ℤ) * E c + dotR F2 E c + p = p * (2 * E c + 1) + dotR F2 E c by ring]; nlinarith
    · rw [show 2 * (p : ℤ) * E c + dotR F2 E c - p = p * (2 * E c - 1) + dotR F2 E c by ring]; nlinarith
  · have h1 := abs_lin_ge p (2 * E c) (dotR F2 E c) hp'
    have h2 := abs_lin_ge p (2 * E c - 2 * Int.sign (dotR F2 E c)) (dotR F2 E c) hp'
    have m1 := min_le_left |2 * E c| |2 * E c - 2 * Int.sign (dotR F2 E c)|
    have m2 := min_le_right |2 * E c| |2 * E c - 2 * Int.sign (dotR F2 E c)|
    refine le_min (le_max_of_le_right ?_) (le_max_of_le_right ?_)
    · rw [show 2 * (p : ℤ) * E c + dotR F2 E c = p * (2 * E c) + dotR F2 E c by ring]; nlinarith
    · rw [show 2 * (p : ℤ) * E c + dotR F2 E c - 2 * p * Int.sign (dotR F2 E c) =
        p * (2 * E c - 2 * Int.sign (dotR F2 E c)) + dotR F2 E c by ring]; nlinarith

/-! ## Summed over the coordinates -/

lemma drc2_bounds (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (hE : E ∈ bind5) (c : Fin 5) :
    drc2 F2 E c ≤ |dotR F2 E c| ∧ -|dotR F2 E c| ≤ drc2 F2 E c := by
  have h2 : |E c| ≤ 1 := by
    rw [TD.mem_bind5] at hE; have := hE.1 c; rw [abs_le]; constructor <;> linarith
  have h3 : |E c * dotR F2 E c| ≤ |dotR F2 E c| := by
    rw [abs_mul]; nlinarith [abs_nonneg (dotR F2 E c), abs_nonneg (E c)]
  unfold drc2; split_ifs
  · exact ⟨le_rfl, by linarith [abs_nonneg (dotR F2 E c)]⟩
  · constructor
    · linarith [neg_abs_le (E c * dotR F2 E c)]
    · linarith [le_abs_self (E c * dotR F2 E c)]

lemma sum_drc2 (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (p : ℤ) :
    ∑ c : Fin 5, (p ^ 2 - 2 * p * (drc2 F2 E c + 2)) = 5 * p ^ 2 - 2 * p * (drift2E F2 E + 10) := by
  unfold drift2E
  rw [Fin.sum_univ_five, Fin.sum_univ_five]; ring

/-- On a binding step: `∑_c (2b_c)² ≥ 5p² − 2p (2dr(E) + 10)`. -/
lemma sum_hk_bind (p : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (hE : E ∈ bind5) (A : ℤ)
    (hA : ∀ c, |dotR F2 E c| ≤ A) (hpA : A + 4 ≤ p) :
    5 * (p : ℤ) ^ 2 - 2 * p * (drift2E F2 E + 10) ≤ ∑ c, bOpt2 p (fun _ => F2) E (fun _ => 0) c ^ 2 := by
  have key : ∀ c, (p : ℤ) ^ 2 - 2 * p * (drc2 F2 E c + 2) ≤ bOpt2 p (fun _ => F2) E (fun _ => 0) c ^ 2 := by
    intro c
    have hb := bOpt2_bind p F2 E hE c (by linarith [hA c])
    have hd := drc2_bounds F2 E hE c
    have hpos : 0 ≤ (p : ℤ) - drc2 F2 E c - 2 := by linarith [hA c]
    have hsq := pow_le_pow_left₀ hpos hb 2
    nlinarith [sq_nonneg (drc2 F2 E c + 2)]
  rw [← sum_drc2]
  exact Finset.sum_le_sum fun c _ => key c

/-- On a step with `∑_c (2ℓ_c)² ≥ 6`: `∑_c (2b_c)² ≥ 6p² − 50 (A + 2) p`. -/
lemma sum_hk_gen (p : ℕ) (hp : 0 < p) (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (hE : ∀ d, |E d| ≤ 2) (A : ℤ)
    (hA : ∀ c, |dotR F2 E c| ≤ A) (hl : 6 ≤ ∑ c, ell2 F2 E c ^ 2) :
    6 * (p : ℤ) ^ 2 - 50 * (A + 2) * p ≤ ∑ c, bOpt2 p (fun _ => F2) E (fun _ => 0) c ^ 2 := by
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have key : ∀ c, (p : ℤ) ^ 2 * ell2 F2 E c ^ 2 - 10 * (A + 2) * p ≤ bOpt2 p (fun _ => F2) E (fun _ => 0) c ^ 2 := by
    intro c
    have hb := bOpt2_gen p F2 E c hp
    have hl0 := ell2_nonneg F2 E c
    have hl5 := ell2_le F2 E hE c
    have hB := hA c
    have hA0 : 0 ≤ A := (abs_nonneg _).trans hB
    have hb0 := bOpt2_k1_nonneg p F2 E c
    have hb2 : (p : ℤ) * ell2 F2 E c - (A + 2) ≤ bOpt2 p (fun _ => F2) E (fun _ => 0) c := by linarith
    have hK : 2 * (A + 2) * p * ell2 F2 E c ≤ 10 * (A + 2) * p := by
      have : 0 ≤ 2 * (A + 2) * (p : ℤ) := by positivity
      nlinarith
    rcases le_total 0 ((p : ℤ) * ell2 F2 E c - (A + 2)) with h | h
    · have := pow_le_pow_left₀ h hb2 2
      nlinarith [sq_nonneg (A + 2)]
    · have h0 : 0 ≤ (p : ℤ) * ell2 F2 E c := by positivity
      have h3 : ((p : ℤ) * ell2 F2 E c) ^ 2 ≤ (A + 2) * ((p : ℤ) * ell2 F2 E c) := by nlinarith
      nlinarith [sq_nonneg (bOpt2 p (fun _ => F2) E (fun _ => 0) c)]
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ (univ : Finset (Fin 5))) => key c
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h6 := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℤ) ≤ (p : ℤ) ^ 2)
  push_cast at hsum
  linarith

lemma le_drift2 (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (hE : E ∈ bind5) : drift2E F2 E ≤ drift2 F2 :=
  Finset.le_sup' (drift2E F2) hE

/-- **Every step** (with (Gap) on the non-binding steps): for `p ≥ P`, `∑_c (2b_c)² ≥ 5p² − 2p (2dr + 10)`. -/
lemma sum_hk_ge (F2 : Fin 5 → Fin 5 → ℤ) (hΛ : LamHyp F2) (p : ℕ)
    (hp : 50 * (2 * (halfA2 F2 : ℤ) + 2) + 2 * |drift2 F2| + 2 * (halfA2 F2 : ℤ) + 24 ≤ p) :
    ∀ E ∈ halfSteps 5, 5 * (p : ℤ) ^ 2 - 2 * p * (drift2 F2 + 10) ≤
      ∑ c, bOpt2 p (fun _ => F2) E (fun _ => 0) c ^ 2 := by
  intro E hE
  have hE2 := (mem_halfSteps.mp hE).1
  have hA : ∀ c, |dotR F2 E c| ≤ 2 * (halfA2 F2 : ℤ) := fun c => abs_beta2_le F2 E hE2 c
  have hA0 : (0 : ℤ) ≤ 2 * (halfA2 F2 : ℤ) := by positivity
  generalize 2 * (halfA2 F2 : ℤ) = A at hA hA0 hp
  have hd0 := abs_nonneg (drift2 F2)
  have hp1 : (1 : ℤ) ≤ p := by linarith
  by_cases hb : E ∈ bind5
  · have h := sum_hk_bind p F2 E hb A hA (by linarith)
    have hle := le_drift2 F2 E hb
    have := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℤ) ≤ 2 * (p : ℤ))
    linarith
  · have hl := hΛ E hE hb
    have h := sum_hk_gen p (by exact_mod_cast hp1) F2 E hE2 A hA (by linarith)
    have hdj := neg_abs_le (drift2 F2)
    have hbig : 50 * (A + 2) * (p : ℤ) + 2 * p * |drift2 F2| + 20 * p ≤ (p : ℤ) ^ 2 := by
      have : (50 * (A + 2) + 2 * |drift2 F2| + 20) * (p : ℤ) ≤ p * p :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      nlinarith
    have h2 : -(2 * (p : ℤ) * drift2 F2) ≤ 2 * p * |drift2 F2| := by
      have := mul_le_mul_of_nonneg_left hdj (by linarith : (0 : ℤ) ≤ 2 * (p : ℤ))
      linarith
    linarith

/-- **The binding step attaining `dr`, from above**: `∑_c (2b_c)² ≤ 5p² − 2p (2dr(E) + 10) + 5 (A + 2)²`. -/
lemma sum_hk_up (p : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (E : Fin 5 → ℤ) (hE : E ∈ bind5)
    (A : ℤ) (hA : ∀ c, |dotR F2 E c| ≤ A) (hpA : A + 4 ≤ p) :
    ∑ c, bOpt2 p (fun _ => F2) E (fun _ => 0) c ^ 2 ≤ 5 * (p : ℤ) ^ 2 - 2 * p * (drift2E F2 E + 10) + 5 * (A + 2) ^ 2 := by
  have key : ∀ c, bOpt2 p (fun _ => F2) E (fun _ => 0) c ^ 2 ≤
      (p : ℤ) ^ 2 - 2 * p * (drc2 F2 E c + 2) + (A + 2) ^ 2 := by
    intro c
    have hb := bOpt2_bind_up p F2 hodd E hE c (by linarith [hA c])
    have hb0 := bOpt2_k1_nonneg p F2 E c
    have hd := drc2_bounds F2 E hE c
    have hsq := pow_le_pow_left₀ hb0 hb 2
    have hX : (drc2 F2 E c + 2) ^ 2 ≤ (A + 2) ^ 2 := by
      have h1 : drc2 F2 E c + 2 ≤ A + 2 := by linarith [hA c]
      have h2 : -(A + 2) ≤ drc2 F2 E c + 2 := by linarith [hA c, abs_nonneg (dotR F2 E c)]
      nlinarith
    nlinarith
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ (univ : Finset (Fin 5))) => key c
  have e : ∑ c : Fin 5, ((p : ℤ) ^ 2 - 2 * p * (drc2 F2 E c + 2) + (A + 2) ^ 2) =
      5 * (p : ℤ) ^ 2 - 2 * p * (drift2E F2 E + 10) + 5 * (A + 2) ^ 2 := by
    rw [Finset.sum_add_distrib, sum_drc2]; simp
  linarith

/-! ## Real bookkeeping -/

/-- **From below**, for any family of step values `Y E ≥ 0` with `Y E² ≥ 5/4 − D/(2p) − C/(4p²)`:
`min(2, min_E Y E) ≥ (√5/2)(1 − D/(5p)) − C'/p²` (the argument of `LB2R_ge`). -/
lemma LBgen_ge (Y : halfSteps 5 → ℝ) (hY0 : ∀ E, 0 ≤ Y E) (p : ℕ) (D C : ℤ) (hC : 0 ≤ C)
    (hp : |D| + C + 1 ≤ p) (h : ∀ E, 5 / 4 - ((D : ℝ) / (2 * p) + (C : ℝ) / (4 * p ^ 2)) ≤ Y E ^ 2) :
    Real.sqrt 5 / 2 * (1 - (D : ℝ) / (5 * p)) - ((C : ℝ) / 8 + ((|D| : ℝ) / 2 + (C : ℝ) / 4) ^ 2 / 2) / p ^ 2
      ≤ min 2 (⨅ E, Y E) := by
  set a : ℝ := Real.sqrt 5 / 2 with ha
  have ha1 := one_le_a
  have ha2 := a_sq
  rw [← ha] at ha1 ha2
  have ha0 : 0 < a := by linarith
  have hp1 : (1 : ℝ) ≤ p := by
    have : (1 : ℤ) ≤ p := by linarith [abs_nonneg D]
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by linarith
  have hpR : (|D| : ℝ) + C + 1 ≤ p := by exact_mod_cast hp
  set u : ℝ := (D : ℝ) / (2 * p) + (C : ℝ) / (4 * p ^ 2) with hu
  have hDabs : |(D : ℝ)| = (|D| : ℝ) := by norm_cast
  have hC0 : (0 : ℝ) ≤ C := by exact_mod_cast hC
  have hD0 : (0 : ℝ) ≤ (|D| : ℝ) := by positivity
  have hub : |u| ≤ ((|D| : ℝ) / 2 + (C : ℝ) / 4) / p := by
    rw [hu]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_div, hDabs, abs_of_pos (by positivity : (0 : ℝ) < 2 * p),
      abs_of_nonneg hC0, abs_of_pos (by positivity : (0 : ℝ) < 4 * p ^ 2)]
    have : (C : ℝ) / (4 * p ^ 2) ≤ (C : ℝ) / (4 * p) := by
      apply div_le_div_of_nonneg_left hC0 (by positivity); nlinarith
    calc (|D| : ℝ) / (2 * p) + C / (4 * p ^ 2) ≤ (|D| : ℝ) / (2 * p) + C / (4 * p) := by linarith
      _ = _ := by field_simp
  have hu1 : |u| ≤ a ^ 2 := by
    refine hub.trans ?_
    rw [div_le_iff₀ hp0, ha2]; nlinarith
  set T : ℝ := a - u / (2 * a) - u ^ 2 / (2 * a ^ 3) with hT
  have hstep : ∀ E, T ≤ Y E := fun E => lower_of_sq a _ u ha0 (hY0 E) (by rw [ha2]; exact h E) hu1
  have hT2 : T ≤ 2 := by
    have h1 : -(u / (2 * a)) ≤ a / 2 := by
      have : |u / (2 * a)| ≤ a / 2 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * a), div_le_iff₀ (by positivity)]
        nlinarith
      linarith [neg_abs_le (u / (2 * a))]
    have h2 : 0 ≤ u ^ 2 / (2 * a ^ 3) := by positivity
    have ha3 : a ≤ 5 / 4 := by nlinarith
    linarith
  have hLB : T ≤ min 2 (⨅ E, Y E) := by
    have : Nonempty (halfSteps 5) := (halfSteps_nonempty (by norm_num)).to_subtype
    exact le_min hT2 (le_ciInf hstep)
  refine le_trans ?_ hLB
  have e1 : a - u / (2 * a) = a * (1 - (D : ℝ) / (5 * p)) - (C : ℝ) / (8 * a * p ^ 2) := by
    have h4a : 1 / (4 * a) = a / 5 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]; nlinarith [ha2]
    have : u / (2 * a) = (D : ℝ) / p * (1 / (4 * a)) + (C : ℝ) / (8 * a * p ^ 2) := by
      rw [hu]; field_simp; ring
    rw [this, h4a]; ring
  have e2 : (C : ℝ) / (8 * a * p ^ 2) ≤ (C : ℝ) / 8 / p ^ 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hC0 (by positivity); nlinarith
  have e3 : u ^ 2 / (2 * a ^ 3) ≤ ((|D| : ℝ) / 2 + (C : ℝ) / 4) ^ 2 / 2 / p ^ 2 := by
    have hu2 : u ^ 2 ≤ (((|D| : ℝ) / 2 + (C : ℝ) / 4) / p) ^ 2 := by
      rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg _) hub 2
    have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha1
    calc u ^ 2 / (2 * a ^ 3) ≤ u ^ 2 / 2 := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num); linarith
      _ ≤ (((|D| : ℝ) / 2 + (C : ℝ) / 4) / p) ^ 2 / 2 := by linarith
      _ = _ := by field_simp
  rw [hT]
  have : ((C : ℝ) / 8 + ((|D| : ℝ) / 2 + (C : ℝ) / 4) ^ 2 / 2) / p ^ 2 =
      (C : ℝ) / 8 / p ^ 2 + ((|D| : ℝ) / 2 + (C : ℝ) / 4) ^ 2 / 2 / p ^ 2 := by ring
  rw [this]
  linarith

/-- **From above**, from one step `E` with `Y E² ≤ 5/4 − D/(2p) + C/(4p²)`:
`min(2, min_E Y E) ≤ (√5/2)(1 − D/(5p)) + C/(4p²)` (the argument of `LB2R_le`). -/
lemma LBgen_le (Y : halfSteps 5 → ℝ) (hY0 : ∀ E, 0 ≤ Y E) (p : ℕ) (hp : 1 ≤ p) (D C : ℤ) (hC : 0 ≤ C)
    (E : halfSteps 5) (h : Y E ^ 2 ≤ 5 / 4 - (D : ℝ) / (2 * p) + (C : ℝ) / (4 * p ^ 2)) :
    min 2 (⨅ E, Y E) ≤ Real.sqrt 5 / 2 * (1 - (D : ℝ) / (5 * p)) + (C : ℝ) / 4 / p ^ 2 := by
  set a : ℝ := Real.sqrt 5 / 2 with ha
  have ha1 := one_le_a
  have ha2 := a_sq
  rw [← ha] at ha1 ha2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set X : ℝ := Y E with hXdef
  have hLE : min 2 (⨅ E, Y E) ≤ X :=
    (min_le_right _ _).trans (ciInf_le ⟨0, by rintro _ ⟨E', rfl⟩; exact hY0 E'⟩ E)
  refine hLE.trans ?_
  have hamgm : 2 * a * X ≤ X ^ 2 + a ^ 2 := by nlinarith [sq_nonneg (X - a)]
  have hC0 : (0 : ℝ) ≤ C := by exact_mod_cast hC
  have h4a : 2 * a * (a * (1 - (D : ℝ) / (5 * p))) = 5 / 2 - (D : ℝ) / (2 * p) := by
    have : 2 * a * (a * (1 - (D : ℝ) / (5 * p))) = 2 * a ^ 2 * (1 - (D : ℝ) / (5 * p)) := by ring
    rw [this, ha2]; field_simp; ring
  have hCa : (C : ℝ) / (4 * p ^ 2) ≤ 2 * a * ((C : ℝ) / 4 / p ^ 2) := by
    rw [show (C : ℝ) / 4 / p ^ 2 = C / (4 * p ^ 2) by rw [div_div]]
    have : 0 ≤ (C : ℝ) / (4 * p ^ 2) := by positivity
    nlinarith
  have h2a : 0 < 2 * a := by linarith
  have : 2 * a * X ≤ 2 * a * (a * (1 - (D : ℝ) / (5 * p)) + (C : ℝ) / 4 / p ^ 2) := by
    rw [mul_add, h4a]; linarith
  exact le_of_mul_le_mul_left this h2a

/-! ## The expansion -/

set_option maxRecDepth 8000 in
/-- **`rem:accounting`, the expansion for `prop:Hk`(1)**: under (Gap) (`LamHyp`), for odd `F2`, the bound `LB(p)` of
`prop:Hk`(1) at `k = 1` (`bOpt2` with the design `F₀ = F2/2` and no carries) satisfies
`|LB(p) − (√5/2)(1 − (2dr + 10)/(5p))| ≤ C/p²` for every `p ≥ P` (`drift2 = 2dr`). -/
theorem acct_LBHk_core (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (hΛ : LamHyp F2) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, P ≤ p →
      |min 2 (⨅ E : halfSteps 5,
          Real.sqrt (∑ c, ((bOpt2 p (fun _ => F2) (E : Fin 5 → ℤ) (fun _ => 0) c : ℤ) : ℝ) ^ 2) / (2 * p)) -
        Real.sqrt 5 / 2 * (1 - ((drift2 F2 + 10 : ℤ) : ℝ) / (5 * p))| ≤ C / (p : ℝ) ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = 2 * (halfA2 F2 : ℤ) := ⟨_, rfl⟩
  obtain ⟨Cu, hCu⟩ : ∃ Cu : ℤ, Cu = 5 * (A + 2) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Es, hEs, hEsq⟩ := Finset.exists_mem_eq_sup' bind5_nonempty (drift2E F2)
  have hEq : drift2 F2 = drift2E F2 Es := hEsq
  have hA0 : (0 : ℤ) ≤ A := by have := Int.natCast_nonneg (halfA2 F2); linarith
  have hCu0 : 0 ≤ Cu := by have := sq_nonneg (A + 2); linarith
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = drift2 F2 + 10 := ⟨_, rfl⟩
  rw [← hD]
  refine ⟨(((|D| : ℤ) : ℝ) / 2) ^ 2 / 2 + (Cu : ℝ) / 4,
    (50 * (A + 2) + 2 * |drift2 F2| + A + 24 + |D| + 1).toNat, fun p hPp => ?_⟩
  have hPp' : 50 * (A + 2) + 2 * |drift2 F2| + A + 24 + |D| + 1 ≤ (p : ℤ) := by
    have := Int.self_le_toNat (50 * (A + 2) + 2 * |drift2 F2| + A + 24 + |D| + 1)
    have h2 : ((50 * (A + 2) + 2 * |drift2 F2| + A + 24 + |D| + 1).toNat : ℤ) ≤ p := by exact_mod_cast hPp
    linarith
  have hd0 := abs_nonneg (drift2 F2)
  have hD0 := abs_nonneg D
  have hp1 : 1 ≤ p := by
    have : (1 : ℤ) ≤ p := by linarith
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  obtain ⟨Y, hY⟩ : ∃ Y : halfSteps 5 → ℝ, Y = fun E : halfSteps 5 =>
    Real.sqrt (∑ c, ((bOpt2 p (fun _ => F2) (E : Fin 5 → ℤ) (fun _ => 0) c : ℤ) : ℝ) ^ 2) / (2 * p) := ⟨_, rfl⟩
  have hY0 : ∀ E, 0 ≤ Y E := fun E => by rw [hY]; positivity
  have hYsq : ∀ E, Y E ^ 2 = (∑ c, ((bOpt2 p (fun _ => F2) (E : Fin 5 → ℤ) (fun _ => 0) c : ℤ) : ℝ) ^ 2) /
      (4 * (p : ℝ) ^ 2) := by
    intro E
    rw [hY, div_pow, Real.sq_sqrt (by positivity)]; ring
  have hgoal : min 2 (⨅ E : halfSteps 5,
      Real.sqrt (∑ c, ((bOpt2 p (fun _ => F2) (E : Fin 5 → ℤ) (fun _ => 0) c : ℤ) : ℝ) ^ 2) / (2 * p)) =
      min 2 (⨅ E, Y E) := by rw [hY]
  rw [hgoal]
  -- lower half
  have hstep := sum_hk_ge F2 hΛ p (by rw [← hA]; linarith)
  rw [← hD] at hstep
  have hLB := LBgen_ge Y hY0 p D 0 le_rfl (by linarith) (fun E => by
    rw [hYsq, le_div_iff₀ (by positivity)]
    have hZ : ((5 * (p : ℤ) ^ 2 - 2 * p * D : ℤ) : ℝ) ≤
        ((∑ c, bOpt2 p (fun _ => F2) (E : Fin 5 → ℤ) (fun _ => 0) c ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast hstep E.1 E.2
    push_cast at hZ
    have e : (5 / 4 - ((D : ℝ) / (2 * p) + ((0 : ℤ) : ℝ) / (4 * p ^ 2))) * (4 * (p : ℝ) ^ 2) =
        5 * (p : ℝ) ^ 2 - 2 * p * D := by push_cast; field_simp; ring
    rw [e]; exact hZ)
  -- upper half
  have hEs2 : ∀ d, |Es d| ≤ 2 := (mem_halfSteps.mp (bind_sub_halfSteps Es hEs)).1
  have hup := sum_hk_up p F2 hodd Es hEs A (fun c => hA ▸ abs_beta2_le F2 Es hEs2 c) (by linarith)
  rw [← hEq, ← hD, ← hCu] at hup
  have hUB := LBgen_le Y hY0 p hp1 D Cu hCu0 ⟨Es, bind_sub_halfSteps Es hEs⟩ (by
    rw [hYsq, div_le_iff₀ (by positivity)]
    have hZ : ((∑ c, bOpt2 p (fun _ => F2) Es (fun _ => 0) c ^ 2 : ℤ) : ℝ) ≤
        ((5 * (p : ℤ) ^ 2 - 2 * p * D + Cu : ℤ) : ℝ) := by exact_mod_cast hup
    push_cast at hZ
    have e : (5 / 4 - (D : ℝ) / (2 * p) + (Cu : ℝ) / (4 * p ^ 2)) * (4 * (p : ℝ) ^ 2) =
        5 * (p : ℝ) ^ 2 - 2 * p * D + Cu := by field_simp; ring
    rw [e]; exact hZ)
  have hDabs : |((D : ℤ) : ℝ)| = ((|D| : ℤ) : ℝ) := by push_cast; rfl
  rw [hDabs] at hLB
  rw [abs_le]
  have hCu' : (0 : ℝ) ≤ (Cu : ℝ) := by exact_mod_cast hCu0
  have hpp : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have e : ((((|D| : ℤ) : ℝ) / 2) ^ 2 / 2 + (Cu : ℝ) / 4) / (p : ℝ) ^ 2 =
      (((0 : ℤ) : ℝ) / 8 + (((|D| : ℤ) : ℝ) / 2 + ((0 : ℤ) : ℝ) / 4) ^ 2 / 2) / p ^ 2 + (Cu : ℝ) / 4 / p ^ 2 := by
    push_cast; ring
  rw [e]
  have h1 : 0 ≤ (Cu : ℝ) / 4 / p ^ 2 := div_nonneg (div_nonneg hCu' (by norm_num)) hpp.le
  have h2 : 0 ≤ (((0 : ℤ) : ℝ) / 8 + (((|D| : ℤ) : ℝ) / 2 + ((0 : ℤ) : ℝ) / 4) ^ 2 / 2) / p ^ 2 := by
    push_cast
    have h3 := sq_nonneg (((|D| : ℤ) : ℝ) / 2)
    positivity
  constructor <;> linarith

end

end Z3NetHL.Proofs.Acct

/-
Proof module (V14 stage S16′): `rem:accounting`, the two-sided expansion of `LB₂(p)` under (Gap).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.AcctUp

@[expose] public section

/-!
# `rem:accounting`: `LB₂(p) = (√5/2)(1 − 2dj/(5p)) + O(p⁻²)` under (Gap)

The lower half is `LB2R_ge` with `sum_bR2_ge` (`Z3Net/AcctUp.lean`). The upper half:

* `bind_opt_up`: on a binding step, for `E_c ∈ {-1, 0, 1}` and `B = 2β_c ≠ 0`, some option of `lem:R2` (the shorter
  first-digit option, and the wrap of the second digit if `c` is harmful) has
  `|2p²E_c + p·2t + 2u| ≤ p² − p (2dr_c(E) + 2[c harmful]) + 2|v|`.
* `sum_bind_up`: on a binding step, `∑_c (2b_c)² ≤ 5p⁴ − 2p³ (2dr(E) + 2#harmful) + C p²`.
* `LB2R_le`: with the binding step that attains `dj`, `LB₂(p) ≤ (√5/2)(1 − 2dj/(5p)) + C'/p²`.
* `acct_LB2_core`: both halves.
-/

namespace Z3NetHL.Proofs.Acct

open Finset Matrix Z3NetHL Z3NetHL.Proofs

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

set_option maxHeartbeats 2000000 in
/-- **The shorter option on a binding step.** -/
lemma bind_opt_up (p e B v : ℤ) (hp : 0 < p) (he : e = -1 ∨ e = 0 ∨ e = 1) (hB : B ≠ 0)
    (hBp : |B| + 2 ≤ p) (hvp : |v| < p) :
    ∃ t2 u : ℤ, (t2 = B + p ∨ t2 = B - p) ∧ (u = v ∨ u = v - p * Int.sign v) ∧
      |2 * p ^ 2 * e + p * t2 + 2 * u| ≤
        p ^ 2 - p * ((if e = 0 then |B| else -(e * B)) +
          2 * (if v ≠ 0 ∧ Int.sign v = (if e = 0 then -Int.sign B else e) then 1 else 0)) + 2 * |v| := by
  rw [abs_lt] at hvp
  rcases lt_or_gt_of_ne hB with hb | hb <;> rcases lt_trichotomy v 0 with hv | hv | hv
  · have hsB : Int.sign B = -1 := Int.sign_eq_neg_one_of_neg hb
    have hsv : Int.sign v = -1 := Int.sign_eq_neg_one_of_neg hv
    rw [abs_of_neg hb] at hBp ⊢; rw [abs_of_neg hv]
    rcases he with rfl | rfl | rfl <;> simp only [hsB, hsv] <;>
      first
      | (refine ⟨B + p, v, Or.inl rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B + p, v - p * -1, Or.inl rfl, Or.inr rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, v, Or.inr rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, v - p * -1, Or.inr rfl, Or.inr rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
  · have hsB : Int.sign B = -1 := Int.sign_eq_neg_one_of_neg hb
    subst hv
    rw [abs_of_neg hb] at hBp ⊢
    rcases he with rfl | rfl | rfl <;> simp only [hsB, Int.sign_zero, abs_zero] <;>
      first
      | (refine ⟨B + p, 0, Or.inl rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, 0, Or.inr rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
  · have hsB : Int.sign B = -1 := Int.sign_eq_neg_one_of_neg hb
    have hsv : Int.sign v = 1 := Int.sign_eq_one_of_pos hv
    rw [abs_of_neg hb] at hBp ⊢; rw [abs_of_pos hv]
    rcases he with rfl | rfl | rfl <;> simp only [hsB, hsv] <;>
      first
      | (refine ⟨B + p, v, Or.inl rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B + p, v - p * 1, Or.inl rfl, Or.inr rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, v, Or.inr rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, v - p * 1, Or.inr rfl, Or.inr rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
  · have hsB : Int.sign B = 1 := Int.sign_eq_one_of_pos hb
    have hsv : Int.sign v = -1 := Int.sign_eq_neg_one_of_neg hv
    rw [abs_of_pos hb] at hBp ⊢; rw [abs_of_neg hv]
    rcases he with rfl | rfl | rfl <;> simp only [hsB, hsv] <;>
      first
      | (refine ⟨B + p, v, Or.inl rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B + p, v - p * -1, Or.inl rfl, Or.inr rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, v, Or.inr rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, v - p * -1, Or.inr rfl, Or.inr rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
  · have hsB : Int.sign B = 1 := Int.sign_eq_one_of_pos hb
    subst hv
    rw [abs_of_pos hb] at hBp ⊢
    rcases he with rfl | rfl | rfl <;> simp only [hsB, Int.sign_zero, abs_zero] <;>
      first
      | (refine ⟨B + p, 0, Or.inl rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, 0, Or.inr rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
  · have hsB : Int.sign B = 1 := Int.sign_eq_one_of_pos hb
    have hsv : Int.sign v = 1 := Int.sign_eq_one_of_pos hv
    rw [abs_of_pos hb] at hBp ⊢; rw [abs_of_pos hv]
    rcases he with rfl | rfl | rfl <;> simp only [hsB, hsv] <;>
      first
      | (refine ⟨B + p, v, Or.inl rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B + p, v - p * 1, Or.inl rfl, Or.inr rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, v, Or.inr rfl, Or.inl rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))
      | (refine ⟨B - p, v - p * 1, Or.inr rfl, Or.inr rfl, ?_⟩; split_ifs <;> (first | (rw [abs_le]; constructor <;> nlinarith) | (exfalso; norm_num at *; done) | (exfalso; norm_num at *; omega)))


/-- `2b_c` is at most every option on a step with `σ_E` odd (`max(0, |x| − 2) ≤ |x|`). -/
lemma bR2_le_odd (q : ℕ) (F2 D1 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) (hs : (∑ d, E d) % 2 = 1)
    (t2 u : ℤ) (ht : t2 = dotR F2 E c + q ∨ t2 = dotR F2 E c - q)
    (hu : u = dotR D1 E c ∨ u = dotR D1 E c - q * Int.sign (dotR D1 E c)) :
    bR2 q F2 D1 E c ≤ |2 * (q : ℤ) ^ 2 * E c + q * t2 + 2 * u| := by
  have hm : ∀ x : ℤ, max 0 (|x| - 2) ≤ |x| := fun x => max_le (abs_nonneg x) (by linarith)
  unfold bR2 oR2
  simp only [hs, ↓reduceIte]
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (hm _))
  · exact (min_le_left _ _).trans ((min_le_right _ _).trans (hm _))
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (hm _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (hm _))

/-- **Binding steps, from above**: `2b_c ≤ p² − p (2dr_c(E) + 2[c harmful]) + 2|v_c|`. -/
lemma bR2_bind_up (p : ℕ) (hp : 0 < p) (F2 D1 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (E : Fin 5 → ℤ) (hE : E ∈ bind5) (c : Fin 5) (hB : |dotR F2 E c| + 2 ≤ p) (hv : |dotR D1 E c| < p) :
    bR2 p F2 D1 E c ≤ (p : ℤ) ^ 2 - p * (drc2 F2 E c + 2 * harmI F2 D1 E c) + 2 * |dotR D1 E c| := by
  rw [TD.mem_bind5] at hE
  have hs : (∑ d, E d) % 2 = 1 := by rw [Fin.sum_univ_five]; exact hE.2
  have he : E c = -1 ∨ E c = 0 ∨ E c = 1 := by have := hE.1 c; omega
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hB0 : dotR F2 E c ≠ 0 := by
    intro h0; have := dotR_odd_of_bind F2 hodd E hs c; rw [h0] at this; exact absurd this (by decide)
  obtain ⟨t2, u, ht, hu, hle⟩ := bind_opt_up p (E c) (dotR F2 E c) (dotR D1 E c) hp' he hB0 hB hv
  refine (bR2_le_odd p F2 D1 E c hs t2 u ht hu).trans ?_
  unfold drc2 harmI sgnS
  exact hle

set_option maxHeartbeats 1000000 in
/-- On a binding step: `∑_c (2b_c)² ≤ 5p⁴ − 2p³ (2dr(E) + 2#harmful) + 5((A + 2 + 2V)² + 4V) p²`. -/
lemma sum_bind_up (p : ℕ) (F2 D1 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (E : Fin 5 → ℤ) (hE : E ∈ bind5) (A V : ℤ) (hA : ∀ c, |dotR F2 E c| ≤ A) (hV : ∀ c, |dotR D1 E c| ≤ V)
    (hpA : A + 4 * V + 4 ≤ p) :
    ∑ c, bR2 p F2 D1 E c ^ 2 ≤
      5 * (p : ℤ) ^ 4 - 2 * p ^ 3 * (drift2E F2 E + 2 * (nHarm F2 D1 E : ℤ)) + 5 * ((A + 2 + 2 * V) ^ 2 + 4 * V) * p ^ 2 := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hp1 : (1 : ℤ) ≤ p := by linarith
  have hp : 0 < p := by exact_mod_cast hp1
  have hE1 : ∀ c, |E c| ≤ 1 := by
    intro c; rw [TD.mem_bind5] at hE; have := hE.1 c; rw [abs_le]; constructor <;> linarith
  have key : ∀ c, bR2 p F2 D1 E c ^ 2 ≤
      (p : ℤ) ^ 4 - 2 * p ^ 3 * (drc2 F2 E c + 2 * harmI F2 D1 E c) + ((A + 2 + 2 * V) ^ 2 + 4 * V) * p ^ 2 := by
    intro c
    have hB := hA c
    have hv := hV c
    have hb := bR2_bind_up p hp F2 D1 hodd E hE c (by linarith) (by linarith)
    have : NeZero p := ⟨by omega⟩
    have hb0 := bR2_nonneg (p : ℕ) F2 D1 E c
    set X := drc2 F2 E c + 2 * harmI F2 D1 E c with hX
    have hd1 : drc2 F2 E c ≤ |dotR F2 E c| ∧ -|dotR F2 E c| ≤ drc2 F2 E c := by
      unfold drc2; split_ifs
      · exact ⟨le_rfl, by linarith [abs_nonneg (dotR F2 E c)]⟩
      · have h2 := hE1 c
        have h3 : |E c * dotR F2 E c| ≤ |dotR F2 E c| := by
          rw [abs_mul]; nlinarith [abs_nonneg (dotR F2 E c), abs_nonneg (E c)]
        constructor
        · linarith [neg_abs_le (E c * dotR F2 E c)]
        · linarith [le_abs_self (E c * dotR F2 E c)]
    have hh : 0 ≤ harmI F2 D1 E c ∧ harmI F2 D1 E c ≤ 1 := by
      unfold harmI; split_ifs <;> norm_num
    have hXu : X ≤ A + 2 := by linarith
    have hXl : -(A + 2) ≤ X := by linarith
    set K := 2 * |dotR D1 E c| with hK
    have hK0 : 0 ≤ K := by positivity
    have hK1 : K ≤ 2 * V := by linarith
    have hY : bR2 p F2 D1 E c ≤ (p : ℤ) ^ 2 - p * X + K := hb
    have hsq : bR2 p F2 D1 E c ^ 2 ≤ ((p : ℤ) ^ 2 - p * X + K) ^ 2 := pow_le_pow_left₀ hb0 hY 2
    have hX2 : X ^ 2 ≤ (A + 2) ^ 2 := by nlinarith
    have hK2 : K ^ 2 ≤ 4 * V ^ 2 * (p : ℤ) ^ 2 := by
      have h1 : K ^ 2 ≤ (2 * V) ^ 2 := pow_le_pow_left₀ hK0 hK1 2
      have h2 : (1 : ℤ) ≤ (p : ℤ) ^ 2 := by nlinarith
      have h3 : 0 ≤ V ^ 2 := sq_nonneg V
      nlinarith
    have hpK : 2 * (p : ℤ) ^ 2 * K ≤ 4 * V * (p : ℤ) ^ 2 := by nlinarith
    have hXK : -(2 * p * X * K) ≤ 4 * (A + 2) * V * (p : ℤ) ^ 2 := by
      have h1 : -(X * K) ≤ (A + 2) * K := by nlinarith
      have h2 : (A + 2) * K ≤ (A + 2) * (2 * V) := by nlinarith
      have h3 : (p : ℤ) ≤ (p : ℤ) ^ 2 := by nlinarith
      have h4 : 0 ≤ (A + 2) * (2 * V) := by positivity
      nlinarith
    have hexp : ((p : ℤ) ^ 2 - p * X + K) ^ 2 =
        (p : ℤ) ^ 4 - 2 * p ^ 3 * X + (p : ℤ) ^ 2 * X ^ 2 + K ^ 2 + 2 * (p : ℤ) ^ 2 * K - 2 * p * X * K := by ring
    have hp2 : (0 : ℤ) ≤ (p : ℤ) ^ 2 := by positivity
    have hX2p : (p : ℤ) ^ 2 * X ^ 2 ≤ (p : ℤ) ^ 2 * (A + 2) ^ 2 := mul_le_mul_of_nonneg_left hX2 hp2
    nlinarith
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ (univ : Finset (Fin 5))) => key c
  have heq : ∑ c : Fin 5, ((p : ℤ) ^ 4 - 2 * p ^ 3 * (drc2 F2 E c + 2 * harmI F2 D1 E c) +
      ((A + 2 + 2 * V) ^ 2 + 4 * V) * p ^ 2) =
      5 * (p : ℤ) ^ 4 - 2 * p ^ 3 * (drift2E F2 E + 2 * (nHarm F2 D1 E : ℤ)) +
        5 * ((A + 2 + 2 * V) ^ 2 + 4 * V) * p ^ 2 := by
    have hs := sum_harmI F2 D1 E
    rw [Fin.sum_univ_five] at hs ⊢
    linear_combination (-2 * (p : ℤ) ^ 3) * hs
  exact hsum.trans heq.le

/-- **`LB₂(p) ≤ (√5/2)(1 − D/(5p)) + C/(4p²)`** from one step `E` with `∑_c (2b_c)² ≤ 5p⁴ − 2p³D + Cp²`. -/
lemma LB2R_le (F2 D1 : Fin 5 → Fin 5 → ℤ) (p : ℕ) (hp : 1 ≤ p) (D C : ℤ) (hC : 0 ≤ C)
    (E : Fin 5 → ℤ) (hE : E ∈ halfSteps 5)
    (h : ∑ c, bR2 p F2 D1 E c ^ 2 ≤ 5 * (p : ℤ) ^ 4 - 2 * p ^ 3 * D + C * p ^ 2) :
    LB2R p F2 D1 ≤ Real.sqrt 5 / 2 * (1 - (D : ℝ) / (5 * p)) + (C : ℝ) / 4 / p ^ 2 := by
  set a : ℝ := Real.sqrt 5 / 2 with ha
  have ha1 := one_le_a
  have ha2 := a_sq
  rw [← ha] at ha1 ha2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set X : ℝ := Real.sqrt (∑ c, ((bR2 p F2 D1 E c : ℤ) : ℝ) ^ 2) / (2 * (p : ℝ) ^ 2) with hXdef
  have hLE : LB2R p F2 D1 ≤ X := by
    unfold LB2R
    refine (min_le_right _ _).trans ?_
    refine ciInf_le_of_le ⟨0, ?_⟩ (⟨E, hE⟩ : halfSteps 5) le_rfl
    rintro _ ⟨E', rfl⟩
    positivity
  refine hLE.trans ?_
  have hX0 : 0 ≤ X := by positivity
  have hS : (∑ c, ((bR2 p F2 D1 E c : ℤ) : ℝ) ^ 2) ≤ 5 * (p : ℝ) ^ 4 - 2 * p ^ 3 * D + C * p ^ 2 := by
    exact_mod_cast h
  have hX2 : X ^ 2 ≤ 5 / 4 - (D : ℝ) / (2 * p) + (C : ℝ) / (4 * p ^ 2) := by
    rw [hXdef, div_pow, Real.sq_sqrt (by positivity), div_le_iff₀ (by positivity)]
    have e : (5 / 4 - (D : ℝ) / (2 * p) + C / (4 * p ^ 2)) * (2 * (p : ℝ) ^ 2) ^ 2 =
        5 * (p : ℝ) ^ 4 - 2 * p ^ 3 * D + C * p ^ 2 := by field_simp; ring
    rw [e]; exact hS
  have hamgm : 2 * a * X ≤ X ^ 2 + a ^ 2 := by nlinarith [sq_nonneg (X - a)]
  have hC0 : (0 : ℝ) ≤ C := by exact_mod_cast hC
  have hCt : 0 ≤ (C : ℝ) / (4 * p ^ 2) := by positivity
  have h4a : 2 * a * (a * (1 - (D : ℝ) / (5 * p))) = 5 / 2 - (D : ℝ) / (2 * p) := by
    have : 2 * a * (a * (1 - (D : ℝ) / (5 * p))) = 2 * a ^ 2 * (1 - (D : ℝ) / (5 * p)) := by ring
    rw [this, ha2]; field_simp; ring
  have hCa : (C : ℝ) / (4 * p ^ 2) ≤ 2 * a * ((C : ℝ) / 4 / p ^ 2) := by
    rw [show (C : ℝ) / 4 / p ^ 2 = C / (4 * p ^ 2) by rw [div_div]]
    nlinarith
  have h2a : 0 < 2 * a := by linarith
  have : 2 * a * X ≤ 2 * a * (a * (1 - (D : ℝ) / (5 * p)) + (C : ℝ) / 4 / p ^ 2) := by
    rw [mul_add, h4a]; linarith
  exact le_of_mul_le_mul_left this h2a

/-- **`rem:accounting`, the two-sided expansion**: under (Gap) (`LamHyp`), for odd `F2` and any integer `D1`,
`|LB₂(p) − (√5/2)(1 − 2dj/(5p))| ≤ C/p²` for every `p ≥ P`. -/
theorem acct_LB2_core (F2 D1 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (hΛ : LamHyp F2) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, P ≤ p →
      |LB2R p F2 D1 - Real.sqrt 5 / 2 * (1 - (dj2 F2 D1 : ℝ) / (5 * p))| ≤ C / (p : ℝ) ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = 2 * (halfA2 F2 : ℤ) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℤ, V = 2 * (halfA2 D1 : ℤ) := ⟨_, rfl⟩
  obtain ⟨Cz, hCz⟩ : ∃ Cz : ℤ, Cz = 10 * (2 * V + 2) := ⟨_, rfl⟩
  obtain ⟨Cu, hCu⟩ : ∃ Cu : ℤ, Cu = 5 * ((A + 2 + 2 * V) ^ 2 + 4 * V) := ⟨_, rfl⟩
  obtain ⟨Es, hEs, hEsq⟩ := Finset.exists_mem_eq_sup' bind5_nonempty
    (fun E => drift2E F2 E + 2 * (nHarm F2 D1 E : ℤ))
  have hEq : dj2 F2 D1 = drift2E F2 Es + 2 * (nHarm F2 D1 Es : ℤ) := hEsq
  have hA0 : (0 : ℤ) ≤ A := by have := Int.natCast_nonneg (halfA2 F2); linarith
  have hV0 : (0 : ℤ) ≤ V := by have := Int.natCast_nonneg (halfA2 D1); linarith
  have hCz0 : 0 ≤ Cz := by linarith
  have hCu0 : 0 ≤ Cu := by have := sq_nonneg (A + 2 + 2 * V); linarith
  have hdz := abs_nonneg (dj2 F2 D1)
  refine ⟨(Cz : ℝ) / 8 + (|(dj2 F2 D1 : ℝ)| / 2 + (Cz : ℝ) / 4) ^ 2 / 2 + (Cu : ℝ) / 4,
    (A + 4 * V + 4 + 50 * (A + 4) + 3 * |dj2 F2 D1| + Cz + 2 + A + 4 * V + 4).toNat, fun p hPp => ?_⟩
  have hPp' : A + 4 * V + 4 + 50 * (A + 4) + 3 * |dj2 F2 D1| + Cz + 2 + A + 4 * V + 4 ≤ (p : ℤ) := by
    have := Int.self_le_toNat (A + 4 * V + 4 + 50 * (A + 4) + 3 * |dj2 F2 D1| + Cz + 2 + A + 4 * V + 4)
    have h2 : ((A + 4 * V + 4 + 50 * (A + 4) + 3 * |dj2 F2 D1| + Cz + 2 + A + 4 * V + 4).toNat : ℤ) ≤ p := by
      exact_mod_cast hPp
    linarith
  have hp1 : 1 ≤ p := by
    have : (1 : ℤ) ≤ p := by linarith
    exact_mod_cast this
  -- lower half
  have hstep := sum_bR2_ge F2 D1 hodd hΛ p (by rw [← hA, ← hV]; linarith)
  rw [← hV, ← hCz] at hstep
  have hLB := LB2R_ge F2 D1 p (dj2 F2 D1) Cz hCz0 (by linarith) hstep
  -- upper half
  have hEs2 : ∀ d, |Es d| ≤ 2 := (mem_halfSteps.mp (bind_sub_halfSteps Es hEs)).1
  have hup := sum_bind_up p F2 D1 hodd Es hEs A V (fun c => hA ▸ abs_beta2_le F2 Es hEs2 c)
    (fun c => hV ▸ abs_beta2_le D1 Es hEs2 c) (by linarith)
  rw [← hEq, ← hCu] at hup
  have hUB := LB2R_le F2 D1 p hp1 (dj2 F2 D1) Cu hCu0 Es (bind_sub_halfSteps Es hEs) hup
  have hDabs : |((dj2 F2 D1 : ℤ) : ℝ)| = ((|dj2 F2 D1| : ℤ) : ℝ) := by push_cast; rfl
  rw [hDabs]
  rw [hDabs] at hLB
  rw [abs_le]
  have hCz' : (0 : ℝ) ≤ (Cz : ℝ) := by exact_mod_cast hCz0
  have hCu' : (0 : ℝ) ≤ (Cu : ℝ) := by exact_mod_cast hCu0
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hpp : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have e : ((Cz : ℝ) / 8 + (((|dj2 F2 D1| : ℤ) : ℝ) / 2 + (Cz : ℝ) / 4) ^ 2 / 2 + (Cu : ℝ) / 4) / (p : ℝ) ^ 2 =
      ((Cz : ℝ) / 8 + (((|dj2 F2 D1| : ℤ) : ℝ) / 2 + (Cz : ℝ) / 4) ^ 2 / 2) / p ^ 2 + (Cu : ℝ) / 4 / p ^ 2 := by
    ring
  rw [e]
  have h1 : 0 ≤ (Cu : ℝ) / 4 / p ^ 2 := div_nonneg (div_nonneg hCu' (by norm_num)) hpp.le
  have h2 : 0 ≤ ((Cz : ℝ) / 8 + (((|dj2 F2 D1| : ℤ) : ℝ) / 2 + (Cz : ℝ) / 4) ^ 2 / 2) / p ^ 2 := by
    have h3 := sq_nonneg (((|dj2 F2 D1| : ℤ) : ℝ) / 2 + (Cz : ℝ) / 4)
    exact div_nonneg (by linarith) hpp.le
  constructor <;> linarith

end

end Z3NetHL.Proofs.Acct

/-
Proof module (stage 6, main entry): `def:R` (the nets `ℛ_{k,p}`, `p = 5, 7`) and `cor:Rrows`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.TwoRows
public import Z3Net.NetQ

@[expose] public section

/-!
# `def:R`, `cor:Rrows`

As for `cor:rows` (`TwoRows`): rows `0` and `1 + (k-1)·0` of `B U_0` are `1 - x`, `-x + x²`, those
of `C U_0` are `-1`, `(1-x)⁻¹`; `R_p` mixes rows `0, 1` with `a, b`; `Γ_p` acts column by column on
the reverse-level generating function (`GVrow`). The net property is the gauge argument of
`def:Q` (`NetQ.gauge_transfer`) with all block signs `+1`.
-/

namespace Z3Net.Two

open Polynomial Finset Matrix

noncomputable section

namespace RNets

lemma Rpm_row0 (k : ℕ) (hk : 1 ≤ k) (a b : ℤ) (B : Matrix (Fin (2 * k)) (Fin k) ℤ) (j : Fin k) :
    (Rpm k a b * B) ⟨0, by omega⟩ j = B ⟨0, by omega⟩ j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single ⟨0, by omega⟩]
  · simp [Rpm]
  · intro i hi
    have : (i : ℕ) ≠ 0 := fun e => hi (Fin.ext e)
    simp only [Rpm, Fin.ext_iff]; split_ifs <;> first | omega | simp

lemma Rpm_row1 (k : ℕ) (hk : 1 ≤ k) (a b : ℤ) (B : Matrix (Fin (2 * k)) (Fin k) ℤ) (j : Fin k) :
    (Rpm k a b * B) ⟨1, by omega⟩ j =
      a * (B ⟨1, by omega⟩ j + ((k : ℤ) - 1) * B ⟨0, by omega⟩ j) + b * B ⟨0, by omega⟩ j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add ⟨1, by omega⟩ ⟨0, by omega⟩ (by simp [Fin.ext_iff])]
  · simp [Rpm]; ring
  · intro i ⟨hi1, hi0⟩
    have h1 : (i : ℕ) ≠ 1 := fun e => hi1 (Fin.ext e)
    have h0 : (i : ℕ) ≠ 0 := fun e => hi0 (Fin.ext e)
    simp only [Rpm, Fin.ext_iff]; split_ifs <;> first | omega | simp

/-- The effect of `Γ_p` on the reverse-level generating function `h` (at `c = k-1-l`). -/
def GVrow (s3 v4 w : ℤ) (h : ℕ → ℤ) (c : ℕ) : ℤ :=
  if c = 0 then -h 0 else if c = 1 then h 1 + h 0 else if c = 2 then s3 * h 2
  else if c = 3 then v4 * h 3 + w * h 2 else h c - h 3

set_option maxHeartbeats 2000000 in
lemma sum_mul_Gamp (k : ℕ) (s3 v4 w : ℤ) (h : ℕ → ℤ) (l : Fin k) :
    ∑ i : Fin k, h (k - 1 - i) * Gamp k s3 v4 w i l = GVrow s3 v4 w h (k - 1 - l) := by
  have hl := l.isLt
  unfold GVrow
  by_cases c0 : k - 1 - (l : ℕ) = 0
  · rw [if_pos c0, Fintype.sum_eq_single l]
    · rw [show Gamp k s3 v4 w l l = -1 by simp only [Gamp]; split_ifs <;> omega, c0]; ring
    · intro i hi; have hi' : (i : ℕ) ≠ l := fun e => hi (Fin.ext e)
      rw [show Gamp k s3 v4 w i l = 0 by simp only [Gamp, Fin.ext_iff]; split_ifs <;> omega, mul_zero]
  by_cases c1 : k - 1 - (l : ℕ) = 1
  · rw [if_neg c0, if_pos c1,
      Fintype.sum_eq_add l ⟨(l : ℕ) + 1, by omega⟩ (fun e => by simp [Fin.ext_iff] at e)]
    · rw [show Gamp k s3 v4 w l l = 1 by simp only [Gamp]; split_ifs <;> omega,
        show Gamp k s3 v4 w ⟨(l : ℕ) + 1, by omega⟩ l = 1 by simp only [Gamp]; split_ifs <;> omega,
        c1, show k - 1 - ((l : ℕ) + 1) = 0 by omega]
      ring
    · intro i ⟨hi1, hi2⟩
      have hi1' : (i : ℕ) ≠ l := fun e => hi1 (Fin.ext e)
      have hi2' : (i : ℕ) ≠ (l : ℕ) + 1 := fun e => hi2 (Fin.ext e)
      rw [show Gamp k s3 v4 w i l = 0 by simp only [Gamp, Fin.ext_iff]; split_ifs <;> omega, mul_zero]
  by_cases c2 : k - 1 - (l : ℕ) = 2
  · rw [if_neg c0, if_neg c1, if_pos c2, Fintype.sum_eq_single l]
    · rw [show Gamp k s3 v4 w l l = s3 by simp only [Gamp]; split_ifs <;> omega, c2]; ring
    · intro i hi; have hi' : (i : ℕ) ≠ l := fun e => hi (Fin.ext e)
      rw [show Gamp k s3 v4 w i l = 0 by simp only [Gamp, Fin.ext_iff]; split_ifs <;> omega, mul_zero]
  by_cases c3 : k - 1 - (l : ℕ) = 3
  · rw [if_neg c0, if_neg c1, if_neg c2, if_pos c3,
      Fintype.sum_eq_add l ⟨(l : ℕ) + 1, by omega⟩ (fun e => by simp [Fin.ext_iff] at e)]
    · rw [show Gamp k s3 v4 w l l = v4 by simp only [Gamp]; split_ifs <;> omega,
        show Gamp k s3 v4 w ⟨(l : ℕ) + 1, by omega⟩ l = w by simp only [Gamp]; split_ifs <;> omega,
        c3, show k - 1 - ((l : ℕ) + 1) = 2 by omega]
      ring
    · intro i ⟨hi1, hi2⟩
      have hi1' : (i : ℕ) ≠ l := fun e => hi1 (Fin.ext e)
      have hi2' : (i : ℕ) ≠ (l : ℕ) + 1 := fun e => hi2 (Fin.ext e)
      rw [show Gamp k s3 v4 w i l = 0 by simp only [Gamp, Fin.ext_iff]; split_ifs <;> omega, mul_zero]
  · rw [if_neg c0, if_neg c1, if_neg c2, if_neg c3,
      Fintype.sum_eq_add l ⟨k - 4, by omega⟩ (fun e => by simp [Fin.ext_iff] at e; omega)]
    · rw [show Gamp k s3 v4 w l l = 1 by simp only [Gamp]; split_ifs <;> omega,
        show Gamp k s3 v4 w ⟨k - 4, by omega⟩ l = -1 by simp only [Gamp]; split_ifs <;> omega,
        show k - 1 - (k - 4) = 3 by omega]
      ring
    · intro i ⟨hi1, hi2⟩
      have hi1' : (i : ℕ) ≠ l := fun e => hi1 (Fin.ext e)
      have hi2' : (i : ℕ) ≠ k - 4 := fun e => hi2 (Fin.ext e)
      rw [show Gamp k s3 v4 w i l = 0 by simp only [Gamp, Fin.ext_iff]; split_ifs <;> omega, mul_zero]

/-- A row with reverse-level generating function `F`, after the gauge `U_p = U_0 Γ_p`. -/
lemma gauge_rowG (k : ℕ) (hk : 1 ≤ k) (s3 v4 w : ℤ) (M : Matrix (Fin (2 * k)) (Fin k) ℤ)
    (r : Fin (2 * k)) (F : PowerSeries ℤ)
    (hM : ∀ j : Fin k, M r j = PowerSeries.coeff (k - 1) (PowerSeries.X ^ (j : ℕ) * F)) (l : Fin k) :
    (M * (U0 k * Gamp k s3 v4 w)) r l =
      GVrow s3 v4 w (fun c => PowerSeries.coeff c (F * (1 - PowerSeries.X) ^ (k + 1))) (k - 1 - l) := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply, ← sum_mul_Gamp]
  refine sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, ← sum_mul_U0 k hk F i]
  simp only [hM]

/-- Reverse-level coefficients after `U_0` of the four frame rows mixed by `R_p`. -/
def hB0 (c : ℕ) : ℤ := if c = 0 then 1 else if c = 1 then -1 else 0
def hB1 (a b : ℤ) (c : ℕ) : ℤ :=
  a * (if c = 1 then -1 else if c = 2 then 1 else 0) + b * (if c = 0 then 1 else if c = 1 then -1 else 0)
def hC0 (c : ℕ) : ℤ := if c = 0 then -1 else 0
def hC1 (a b : ℤ) (c : ℕ) : ℤ := a - b * (if c = 0 then 1 else 0)

lemma RB_row0 (k : ℕ) (hk : 2 ≤ k) (a b s3 v4 w : ℤ) (l : Fin k) :
    (Rpm k a b * frameB k * (U0 k * Gamp k s3 v4 w)) ⟨0, by omega⟩ l = GVrow s3 v4 w hB0 (k - 1 - l) := by
  rw [gauge_rowG k (by omega) s3 v4 w _ _ (E1 ^ k) (fun j => by
    rw [Rpm_row0 k (by omega), frameB_row0 k hk])]
  rw [pow_succ (1 - PowerSeries.X), ← mul_assoc, E1_pow_mul_one_sub_pow, one_mul]
  congr 1
  funext c
  rw [PS_coeff_one_sub_X]; rfl

lemma RB_row1 (k : ℕ) (hk : 2 ≤ k) (a b s3 v4 w : ℤ) (l : Fin k) :
    (Rpm k a b * frameB k * (U0 k * Gamp k s3 v4 w)) ⟨1, by omega⟩ l =
      GVrow s3 v4 w (hB1 a b) (k - 1 - l) := by
  rw [gauge_rowG k (by omega) s3 v4 w _ _
    (PowerSeries.C a * (-(PowerSeries.X * E1 ^ k)) + PowerSeries.C b * E1 ^ k) (fun j => by
      rw [Rpm_row1 k (by omega), frameB_row1' k hk, frameB_row0 k hk, mul_add, map_add,
        mul_left_comm, PowerSeries.coeff_C_mul, mul_left_comm, PowerSeries.coeff_C_mul])]
  congr 1
  funext c
  rw [show (PowerSeries.C a * (-(PowerSeries.X * E1 ^ k)) + PowerSeries.C b * E1 ^ k) *
      (1 - PowerSeries.X) ^ (k + 1) = (PowerSeries.C a * (-(PowerSeries.X * (1 - PowerSeries.X))) +
        PowerSeries.C b * (1 - PowerSeries.X)) * (E1 ^ k * (1 - PowerSeries.X) ^ k) by ring,
    E1_pow_mul_one_sub_pow, mul_one, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PS_coeff_one_sub_X]
  unfold hB1
  congr 2
  rcases c with _ | c
  · simp
  · rw [map_neg, PowerSeries.coeff_succ_X_mul, PS_coeff_one_sub_X]
    split_ifs <;> simp_all

lemma RC_row0 (k : ℕ) (hk : 2 ≤ k) (a b s3 v4 w : ℤ) (l : Fin k) :
    (Rpm k a b * frameC k * (U0 k * Gamp k s3 v4 w)) ⟨0, by omega⟩ l = GVrow s3 v4 w hC0 (k - 1 - l) := by
  rw [gauge_rowG k (by omega) s3 v4 w _ _ (-(E1 ^ (k + 1))) (fun j => by
    rw [Rpm_row0 k (by omega), frameC_row0 k hk])]
  rw [neg_mul, ← mul_pow, E1_mul_one_sub, one_pow]
  congr 1
  funext c
  simp only [map_neg, PowerSeries.coeff_one, hC0]
  split_ifs <;> simp

lemma RC_row1 (k : ℕ) (hk : 2 ≤ k) (a b s3 v4 w : ℤ) (l : Fin k) :
    (Rpm k a b * frameC k * (U0 k * Gamp k s3 v4 w)) ⟨1, by omega⟩ l =
      GVrow s3 v4 w (hC1 a b) (k - 1 - l) := by
  rw [gauge_rowG k (by omega) s3 v4 w _ _
    (PowerSeries.C a * E1 ^ (k + 2) + PowerSeries.C b * (-(E1 ^ (k + 1)))) (fun j => by
      rw [Rpm_row1 k (by omega), frameC_row1' k hk, frameC_row0 k hk, mul_add, map_add,
        mul_left_comm, PowerSeries.coeff_C_mul, mul_left_comm, PowerSeries.coeff_C_mul])]
  congr 1
  funext c
  rw [show (PowerSeries.C a * E1 ^ (k + 2) + PowerSeries.C b * (-(E1 ^ (k + 1)))) *
      (1 - PowerSeries.X) ^ (k + 1) = (PowerSeries.C a * E1 - PowerSeries.C b) *
        (E1 * (1 - PowerSeries.X)) ^ (k + 1) by rw [mul_pow]; ring,
    E1_mul_one_sub, one_pow, mul_one, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C]
  simp only [E1, PowerSeries.coeff_mk, hC1]
  split_ifs <;> simp

lemma vals (p : ℕ) (hp : p = 5 ∨ p = 7) (c : ℕ) :
    ((GVrow (Rpar p 2) (Rpar p 3) (Rpar p 4) hB0 c : ℤ) : ZMod p) = ((tabR0 1 c : ℤ) : ZMod p) ∧
    ((GVrow (Rpar p 2) (Rpar p 3) (Rpar p 4) (hB1 (Rpar p 0) (Rpar p 1)) c : ℤ) : ZMod p) =
      ((tabR1 p 1 c : ℤ) : ZMod p) ∧
    ((GVrow (Rpar p 2) (Rpar p 3) (Rpar p 4) hC0 c : ℤ) : ZMod p) = ((tabR0 2 c : ℤ) : ZMod p) ∧
    ((GVrow (Rpar p 2) (Rpar p 3) (Rpar p 4) (hC1 (Rpar p 0) (Rpar p 1)) c : ℤ) : ZMod p) =
      ((tabR1 p 2 c : ℤ) : ZMod p) := by
  rcases hp with rfl | rfl <;> rcases c with _ | _ | _ | _ | c <;>
    simp [GVrow, hB0, hB1, hC0, hC1, tabR0, tabR1, Rpar] <;> decide

lemma RPhi_rel (p k : ℕ) (B C : Matrix (Fin (2 * k)) (Fin k) ℤ) (c : Fin 3) :
    RPhiOf p k B C c c = Astar k ∧
    RPhiOf p k B C c (c + 1) = Rpm k (Rpar p 0) (Rpar p 1) * B * (U0 k * Gamp k (Rpar p 2) (Rpar p 3) (Rpar p 4)) ∧
    RPhiOf p k B C c (c + 2) = Rpm k (Rpar p 0) (Rpar p 1) * C * (U0 k * Gamp k (Rpar p 2) (Rpar p 3) (Rpar p 4)) := by
  refine ⟨by simp [RPhiOf], ?_, ?_⟩ <;> fin_cases c <;> simp [RPhiOf] <;> decide

/-- **`cor:Rrows`**: rows `0` and `1` of the blocks of `ℛ_{k,p}`, modulo `p`, by relative position
`d - c` and level `k-1-l`. -/
theorem R_rows (p k : ℕ) (hp : p = 5 ∨ p = 7) (hk : 2 ≤ k) (c d : Fin 3) (l : Fin k) :
    ((RPhiOf p k (frameB k) (frameC k) c d ⟨0, by omega⟩ l : ℤ) : ZMod p) =
        ((tabR0 (d - c) (k - 1 - l) : ℤ) : ZMod p) ∧
      ((RPhiOf p k (frameB k) (frameC k) c d ⟨1, by omega⟩ l : ℤ) : ZMod p) =
        ((tabR1 p (d - c) (k - 1 - l) : ℤ) : ZMod p) := by
  have hl := l.isLt
  obtain ⟨i, rfl⟩ : ∃ i : Fin 3, d = c + i := ⟨d - c, by abel⟩
  rw [show c + i - c = i by abel]
  obtain ⟨h0, h1, h2⟩ := RPhi_rel p k (frameB k) (frameC k) c
  have hv := vals p hp (k - 1 - l)
  fin_cases i
  · simp only [Fin.zero_eta, add_zero, h0, Astar, tabR0, tabR1]
    constructor
    · by_cases h : (l : ℕ) + 1 = k
      · simp [h, show k - 1 - (l : ℕ) = 0 by omega]
      · simp [h, show k - 1 - (l : ℕ) ≠ 0 by omega]
    · simp
  · simp only [Fin.mk_one, h1]
    rw [RB_row0 k hk, RB_row1 k hk]
    exact ⟨hv.1, hv.2.1⟩
  · simp only [Fin.reduceFinMk, h2]
    rw [RC_row0 k hk, RC_row1 k hk]
    exact ⟨hv.2.2.1, hv.2.2.2⟩

/-- **`cor:Rrows`**: all rows `≥ 1` of the own blocks `Φ_cc = A_*` vanish. -/
theorem R_self_row (p k : ℕ) (c : Fin 3) (r : Fin (2 * k)) (hr : (r : ℕ) ≠ 0) (l : Fin k) :
    RPhiOf p k (frameB k) (frameC k) c c r l = 0 := by
  simp [(RPhi_rel p k (frameB k) (frameC k) c).1, Astar, hr]

lemma Gamp_lower (k : ℕ) (s3 v4 w : ℤ) : ∀ i j : Fin k, i < j → Gamp k s3 v4 w i j = 0 := by
  intro i j h
  have h' : (i : ℕ) < j := h
  simp only [Gamp]
  split_ifs <;> first | omega | (subst_vars; omega) | rfl
  all_goals (rename_i hh; exact absurd (Fin.ext_iff.mp hh) (by omega))

lemma Gamp_diag (k : ℕ) (s3 v4 w : ℤ) (j : Fin k) :
    Gamp k s3 v4 w j j = -1 ∨ Gamp k s3 v4 w j j = s3 ∨ Gamp k s3 v4 w j j = v4 ∨
      Gamp k s3 v4 w j j = 1 := by
  simp only [Gamp]
  split_ifs <;> first | omega | simp

/-- **`def:R`**: `ℛ_{k,p}` is a `(0,3k,3)`-net over `𝔽_p` (`p = 5, 7`, `k ≥ 2`). -/
theorem R_net (p k : ℕ) (hp : p = 5 ∨ p = 7) (hk : 2 ≤ k) : Z3Net.IsNet0 p (3 * k) (Rpoint p k) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI := Fact.mk hpp
  have hunit : ∀ z : ℤ, z ∈ ({-1, 1, Rpar p 0, Rpar p 2, Rpar p 3} : Finset ℤ) → IsUnit (z : ZMod p) := by
    intro z hz
    rw [isUnit_iff_ne_zero, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rcases hp with rfl | rfl <;> simp [Rpar] at hz <;> rcases hz with rfl | rfl | rfl | rfl | rfl <;>
      decide
  apply Z3Net.Proofs.isNet0_of_box_injective
  intro d hd
  apply Z3Net.Proofs.mulVec_injective_of_ker
  have hgen : (fun c => (RGen p k c).map (Int.cast : ℤ → ZMod p)) =
      graphGen k (fun c e => (RPhiOf p k (frameB k) (frameC k) c e).map (Int.cast : ℤ → ZMod p)) := by
    funext c
    exact Z3Net.Proofs.graphGen_map_int k _ c
  rw [hgen]
  set Lr := Rpm k (Rpar p 0) (Rpar p 1)
  set Uz := U0 k * Gamp k (Rpar p 2) (Rpar p 3) (Rpar p 4)
  have hLlow : ∀ i j : Fin (2 * k), i < j → Lr i j = 0 := by
    intro i j h
    have h' : (i : ℕ) < j := h
    simp only [Lr, Rpm]
    rw [if_neg (ne_of_lt h), if_neg (by omega)]
  have hUlow : ∀ i j : Fin k, i < j → Uz i j = 0 :=
    Z3Net.Proofs.lower_mul _ _ (Z3Net.Proofs.U0_lower k) (Gamp_lower k _ _ _)
  refine Z3Net.Proofs.gauge_transfer k (by omega) _
    (fun c e => (graphBlock k (frameGen k) c e).map (Int.cast : ℤ → ZMod p))
    (Lr.map Int.cast) (fun i j h => by rw [map_apply, hLlow i j h, Int.cast_zero])
    (fun i => by
      rw [map_apply]
      simp only [Lr, Rpm, if_true]
      split_ifs
      · exact hunit _ (by simp)
      · simp)
    (Uz.map Int.cast) (fun i j h => by rw [map_apply, hUlow i j h, Int.cast_zero])
    (fun i => by
      rw [map_apply, show Uz i i = Gamp k (Rpar p 2) (Rpar p 3) (Rpar p 4) i i by
        simp only [Uz]
        rw [Z3Net.Proofs.diag_mul_of_lower _ _ (Z3Net.Proofs.U0_lower k) (Gamp_lower k _ _ _),
          Z3Net.Proofs.U0_diag, one_mul]]
      rcases Gamp_diag k (Rpar p 2) (Rpar p 3) (Rpar p 4) i with h | h | h | h <;> rw [h] <;>
        exact hunit _ (by simp))
    (fun _ _ => 1) (fun c e hce => ?_) d hd 1 1 (fun _ => isUnit_one) (fun _ => isUnit_one)
    (fun _ _ _ _ _ => by simp)
    (fun n' hn' => Z3Net.Proofs.frameGraph_box_kernel k (by omega) d hd n' hn')
  have hm : ∀ (A : Matrix (Fin (2 * k)) (Fin (2 * k)) ℤ) (B : Matrix (Fin (2 * k)) (Fin k) ℤ)
      (C : Matrix (Fin k) (Fin k) ℤ), (A * B * C).map (Int.cast : ℤ → ZMod p) =
        A.map Int.cast * B.map Int.cast * C.map Int.cast := by
    intro A B C
    rw [show (Int.cast : ℤ → ZMod p) = ⇑(Int.castRingHom (ZMod p)) from rfl, Matrix.map_mul,
      Matrix.map_mul]
    rfl
  have key : RPhiOf p k (frameB k) (frameC k) c e = Lr * graphBlock k (frameGen k) c e * Uz := by
    obtain ⟨h0, h1, h2⟩ := RPhi_rel p k (frameB k) (frameC k) c
    by_cases he1 : e = c + 1
    · rw [he1, h1, Z3Net.Proofs.frameB_eq k (by omega) c]
    · have he2 : e = c + 2 := by
        fin_cases c <;> fin_cases e <;> simp_all
      rw [he2, h2, Z3Net.Proofs.frameC_eq k (by omega) c]
  rw [one_smul, key]
  exact hm _ _ _

lemma Gamp_diag_val (k : ℕ) (s3 v4 w : ℤ) (j : ℕ) (hj : j < k) :
    Gamp k s3 v4 w ⟨j, hj⟩ ⟨j, hj⟩ =
      if j + 1 = k then -1 else if j + 3 = k then s3 else if j + 4 = k then v4 else 1 := by
  simp only [Gamp]
  split_ifs <;> first | omega | rfl

/-- `def:R`: `Γ_p` is lower triangular with determinant `-s_3 v_4` (`k ≥ 4`), i.e. `∓2`. -/
theorem R_Gamma_det (p k : ℕ) (hk : 4 ≤ k) :
    (∀ i j : Fin k, i < j → Gamp k (Rpar p 2) (Rpar p 3) (Rpar p 4) i j = 0) ∧
      (Gamp k (Rpar p 2) (Rpar p 3) (Rpar p 4)).det = -(Rpar p 2 * Rpar p 3) := by
  refine ⟨Gamp_lower k _ _ _, ?_⟩
  rw [Matrix.det_of_lowerTriangular _ (fun i j h => Gamp_lower k _ _ _ i j h)]
  set g : ℕ → ℤ := fun j => if j + 1 = k then -1 else if j + 3 = k then Rpar p 2
    else if j + 4 = k then Rpar p 3 else 1 with hg
  rw [show (∏ i : Fin k, Gamp k (Rpar p 2) (Rpar p 3) (Rpar p 4) i i) = ∏ i : Fin k, g i from
    Finset.prod_congr rfl fun i _ => Gamp_diag_val k _ _ _ i i.isLt]
  rw [Fin.prod_univ_eq_prod_range g]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 4 := ⟨k - 4, by omega⟩
  rw [show n + 4 = n + 1 + 1 + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_eq_one (fun j hj => by
      simp only [Finset.mem_range] at hj
      simp only [hg]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)])]
  simp only [hg]
  split_ifs <;> first | omega | ring

end RNets

end

end Z3Net.Two

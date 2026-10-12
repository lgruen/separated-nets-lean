/-
Proof module of entry Obs: `prop:shared` (shared generator rows).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsDefs
public import Z3Net.FNie

@[expose] public section

/-!
# Entry Obs: `prop:shared`

The proof of the paper: if `2(j+1) ≤ m`, the box with depth `m - (j+1)` on `a` and `j + 1` on `b`
(the remaining rows taken from `a`) contains row `j` of both coordinates, so it is singular
(`lem:nie` over a field).
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

namespace ObsShared

theorem shared_row {K : Type*} [Field K] {q s m : ℕ} (e : K ≃ Fin q)
    (C : Fin s → Matrix (Fin m) (Fin m) K) (hC : Z3NetF.IsNet0E e C) (a b : Fin s) (hab : a ≠ b)
    (j : Fin m) (hj : C a j = C b j) : m < 2 * ((j : ℕ) + 1) := by
  by_contra hle
  push Not at hle
  let d : Fin s → ℕ := fun c => if c = a then m - ((j : ℕ) + 1) else if c = b then (j : ℕ) + 1
    else 0
  have hd : ∑ c, d c = m := by
    have e1 : ∀ c, d c = (if c = a then m - ((j : ℕ) + 1) else 0) +
        (if c = b then (j : ℕ) + 1 else 0) := by
      intro c
      by_cases hca : c = a
      · subst hca; simp [d, hab]
      · simp [d, hca]
    simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, if_true]
    omega
  have hja : (j : ℕ) < d a := by simp only [d, if_pos rfl]; omega
  have hjb : (j : ℕ) < d b := by simp [d, Ne.symm hab]
  have hdet := (nie_net_field e C).1 hC d hd
  apply hdet
  have ra := box_row_pre C d hd a j hja
  have rb := box_row_pre C d hd b j hjb
  have hne : (⟨pre d a + j, pre_add_lt d hd a j hja⟩ : Fin m) ≠
      ⟨pre d b + j, pre_add_lt d hd b j hjb⟩ := by
    intro h
    have h' : Z3NetU.Proofs.pre d a = Z3NetU.Proofs.pre d b := by
      have := congrArg Fin.val h; simp only [pre] at this; omega
    have hda : 0 < d a := by omega
    have hdb : 0 < d b := by omega
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
    · have h1 := Z3NetU.Proofs.pre_mono d (show (a : ℕ) + 1 ≤ b by omega)
      have h2 := Z3NetU.Proofs.pre_succ d a
      omega
    · have h1 := Z3NetU.Proofs.pre_mono d (show (b : ℕ) + 1 ≤ a by omega)
      have h2 := Z3NetU.Proofs.pre_succ d b
      omega
  apply Matrix.det_zero_of_row_eq hne
  rw [ra, rb]
  convert hj using 2

theorem shared_only {K : Type*} [Field K] {q s m : ℕ} (hs : 3 ≤ s) (e : K ≃ Fin q)
    (C : Fin s → Matrix (Fin m) (Fin m) K) (hC : Z3NetF.IsNet0E e C) (a b : Fin s) (hab : a ≠ b)
    (j : Fin m) (hjk : (j : ℕ) = m / s) (hj : C a j = C b j) :
    m < 2 * (m / s + 1) ∧ (m = 1 ∨ (s = 3 ∧ m = 3)) := by
  have h1 := shared_row e C hC a b hab j hj
  rw [hjk] at h1
  refine ⟨h1, ?_⟩
  have hm : 1 ≤ m := by have := j.isLt; omega
  have hdm := Nat.div_add_mod m s
  have hr := Nat.mod_lt m (show 0 < s by omega)
  set k := m / s
  set r := m % s
  rcases Nat.eq_zero_or_pos k with hk | hk
  · left
    rw [hk] at h1
    omega
  · right
    have h3 : 3 * k ≤ s * k := Nat.mul_le_mul_right k hs
    have hk1 : k = 1 := by omega
    rw [hk1] at hdm h3
    omega

end ObsShared

alias shared_row := ObsShared.shared_row
alias shared_only := ObsShared.shared_only

end

end Z3NetF.Proofs

module
public import Mathlib
public import Z3Net.D4Defs
public import Z3Net.D4Graph
public import Z3Net.D4Rows
public import Z3Net.TwoGeom

@[expose] public section

/-!
# 4D entry, part 7: digits, cells and carries of `𝒫⁴_{k,q}` (Lemma S, geometric part)

The point `D4point q k v` has, in coordinate `c`, digits `D_c(v) = D4Gen q k c · v`: the first `k`
are the cell digits `v_{ck+i}` (graph form), digit `k + r` is `∑_{d,l} Φ'_cd[r,l] v_{dk+l}`.
Adapted from the 3D entry (`Z3Net/TwoGeom.lean`) to four coordinates, one offset digit and an
arbitrary modulus `q`.
-/

namespace Z3NetD4.Proofs

open Finset Matrix Z3NetD4

noncomputable section

lemma two_mul_inv_two' (q : ℕ) (hq : Odd q) : (2 : ZMod q) * (2 : ZMod q)⁻¹ = 1 := by
  apply ZMod.mul_inv_of_unit
  have : IsUnit ((2 : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  simpa using this

variable (q : ℕ)

/-- Digit vector of coordinate `c` of the point with index `v`. -/
def Dg (k : ℕ) (c : Fin 4) (v : Fin (4 * k) → ZMod q) : Fin (4 * k) → ZMod q := D4Gen q k c *ᵥ v

lemma D4point_eq (k : ℕ) (v : Fin (4 * k) → ZMod q) (c : Fin 4) :
    D4point q k v c = ∑ j : Fin (4 * k), (Dg q k c v j).val * q ^ (4 * k - 1 - (j : ℕ)) := rfl

lemma Dg_cell (k : ℕ) (c : Fin 4) (v : Fin (4 * k) → ZMod q) (i : ℕ) (hi : i < k) :
    Dg q k c v ⟨i, by omega⟩ = v (ix k c ⟨i, hi⟩) :=
  graphGen_cell k _ c v i hi

lemma Dg_off (k : ℕ) (c : Fin 4) (v : Fin (4 * k) → ZMod q) (r : Fin (3 * k)) :
    Dg q k c v ⟨k + r, by omega⟩ =
      ∑ d : Fin 4, ∑ l : Fin k, D4Phi (ZMod q) (2 : ZMod q)⁻¹ k c d r l * v (ix k d l) :=
  graphGen_off k _ c v r

/-! ## Decomposition of a coordinate -/

variable [NeZero q]

/-- Total digit accessor (as natural numbers). -/
def dv (k : ℕ) (D : Fin (4 * k) → ZMod q) (j : ℕ) : ℕ := if h : j < 4 * k then (D ⟨j, h⟩).val else 0

lemma dv_lt (k : ℕ) (D : Fin (4 * k) → ZMod q) (j : ℕ) : dv q k D j < q := by
  unfold dv; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero q

/-- Tail of the expansion (digits `k+1, …, 4k-1`). -/
def tail (k : ℕ) (D : Fin (4 * k) → ZMod q) : ℕ :=
  ∑ j ∈ Ico (k + 1) (4 * k), dv q k D j * q ^ (4 * k - 1 - j)

lemma tail_lt (k : ℕ) (hk : 1 ≤ k) (D : Fin (4 * k) → ZMod q) : tail q k D < q ^ (3 * k - 1) := by
  unfold tail
  rw [sum_Ico_eq_sum_range, show 4 * k - (k + 1) = 3 * k - 1 by omega]
  have := Z3Net.Two.sum_digits_be_lt q (Nat.pos_of_neZero q) (fun t => dv q k D (k + 1 + t))
    (fun t => dv_lt q k D _) (3 * k - 1)
  convert this using 2 with t ht
  simp only [mem_range] at ht
  rw [show 4 * k - 1 - (k + 1 + t) = 3 * k - 1 - 1 - t by omega]

lemma coord_split (k : ℕ) (hk : 1 ≤ k) (D : Fin (4 * k) → ZMod q) :
    ∑ j : Fin (4 * k), (D j).val * q ^ (4 * k - 1 - (j : ℕ)) =
      q ^ (3 * k) * (∑ i ∈ range k, dv q k D i * q ^ (k - 1 - i)) + q ^ (3 * k - 1) * dv q k D k +
        tail q k D := by
  rw [show ∑ j : Fin (4 * k), (D j).val * q ^ (4 * k - 1 - (j : ℕ)) =
      ∑ j : Fin (4 * k), dv q k D j * q ^ (4 * k - 1 - (j : ℕ)) by
        refine sum_congr rfl fun j _ => ?_; simp [dv, j.isLt],
    Fin.sum_univ_eq_sum_range (fun j => dv q k D j * q ^ (4 * k - 1 - j)),
    ← sum_range_add_sum_Ico _ (show k ≤ 4 * k by omega),
    sum_eq_sum_Ico_succ_bot (show k < 4 * k by omega), tail, mul_sum]
  rw [show 4 * k - 1 - k = 3 * k - 1 by omega]
  have : ∑ i ∈ range k, dv q k D i * q ^ (4 * k - 1 - i) =
      ∑ i ∈ range k, q ^ (3 * k) * (dv q k D i * q ^ (k - 1 - i)) := by
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    rw [show 4 * k - 1 - i = 3 * k + (k - 1 - i) by omega, pow_add]; ring
  rw [this]; ring

/-! ## Cells and carries -/

/-- Level `i` digit (as a natural number) of the cell of axis `d`. -/
def ad (k : ℕ) (v : Fin (4 * k) → ZMod q) (d : Fin 4) (i : ℕ) : ℕ :=
  if h : i < k then (v (ix k d ⟨i, h⟩)).val else 0

lemma ad_lt (k : ℕ) (v : Fin (4 * k) → ZMod q) (d : Fin 4) (i : ℕ) : ad q k v d i < q := by
  unfold ad; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero q

/-- The cell `n_d ∈ [0, q^k)` of axis `d`. -/
def cellN (k : ℕ) (v : Fin (4 * k) → ZMod q) (d : Fin 4) : ℕ :=
  ∑ i ∈ range k, ad q k v d i * q ^ (k - 1 - i)

lemma cellN_lt (k : ℕ) (v : Fin (4 * k) → ZMod q) (d : Fin 4) : cellN q k v d < q ^ k :=
  Z3Net.Two.sum_digits_be_lt q (Nat.pos_of_neZero q) _ (ad_lt q k v d) k

lemma cell_part (k : ℕ) (v : Fin (4 * k) → ZMod q) (c : Fin 4) :
    ∑ i ∈ range k, dv q k (Dg q k c v) i * q ^ (k - 1 - i) = cellN q k v c := by
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  congr 1
  simp only [dv, ad, dif_pos hi, dif_pos (show i < 4 * k by omega)]
  rw [Dg_cell q k c v i hi]

lemma cellN_digit (hq : 1 < q) (k : ℕ) (v : Fin (4 * k) → ZMod q) (d : Fin 4) (l : Fin k) :
    cellN q k v d / q ^ (k - 1 - (l : ℕ)) % q = (v (ix k d l)).val := by
  have hl := l.isLt
  unfold cellN
  rw [Z3Net.Two.digit_extract_be q hq k _ (ad_lt q k v d) _ (by omega),
    show k - 1 - (k - 1 - (l : ℕ)) = l by omega]
  simp [ad, hl]

lemma zmod_digit (hq : 1 < q) (k : ℕ) (v : Fin (4 * k) → ZMod q) (d : Fin 4) (l : Fin k) :
    v (ix k d l) = ((cellN q k v d / q ^ (k - 1 - (l : ℕ)) : ℕ) : ZMod q) := by
  rw [← ZMod.natCast_mod, cellN_digit q hq, ZMod.natCast_zmod_val]

lemma digits_eq_of_cellN_eq (hq : 1 < q) (k : ℕ) (v w : Fin (4 * k) → ZMod q) (d : Fin 4)
    (h : cellN q k w d = cellN q k v d) (l : Fin k) : w (ix k d l) = v (ix k d l) := by
  rw [zmod_digit q hq k w, zmod_digit q hq k v, h]

/-- **Carry lemma.** If the cell of axis `d` steps by `+1` (mod `q^k`), the level-`l` digit changes
by `1` iff `q^(k-1-l)` divides `n + 1`. -/
lemma carry_digits (hq : 1 < q) (k : ℕ) (v w : Fin (4 * k) → ZMod q) (d : Fin 4)
    (h : cellN q k w d = (cellN q k v d + 1) % q ^ k) (l : Fin k) :
    w (ix k d l) - v (ix k d l) =
      if q ^ (k - 1 - (l : ℕ)) ∣ cellN q k v d + 1 then 1 else 0 := by
  have hl := l.isLt
  set s := k - 1 - (l : ℕ) with hs
  have hsk : s < k := by omega
  rw [zmod_digit q hq k w, zmod_digit q hq k v, h, ← hs]
  have e1 : (cellN q k v d + 1) % q ^ k / q ^ s = (cellN q k v d + 1) / q ^ s % q ^ (k - s) := by
    rw [show q ^ k = q ^ s * q ^ (k - s) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self]
  rw [e1, ← ZMod.natCast_mod, Nat.mod_mod_of_dvd _ (dvd_pow_self q (by omega)), ZMod.natCast_mod,
    Nat.succ_div]
  split_ifs <;> simp

/-- Carry class (capped at `2`, and `< k`). -/
def Jof (k n : ℕ) : ℕ :=
  if 2 < k ∧ q ^ 2 ∣ n + 1 then 2 else if 1 < k ∧ q ∣ n + 1 then 1 else 0

lemma Jof_le (k n : ℕ) : Jof q k n ≤ 2 := by unfold Jof; split_ifs <;> omega

lemma Jof_lt (k n : ℕ) (hk : 1 ≤ k) : Jof q k n < k := by unfold Jof; split_ifs <;> omega

lemma dvd_iff_le_Jof (k n s : ℕ) (hs : s ≤ 2) (hsk : s < k) :
    q ^ s ∣ n + 1 ↔ s ≤ Jof q k n := by
  have d21 : q ^ 2 ∣ n + 1 → q ∣ n + 1 := fun h => (dvd_pow_self q (by omega)).trans h
  unfold Jof
  interval_cases s
  · simp
  · simp only [pow_one]; split_ifs <;> simp_all <;> omega
  · split_ifs <;> simp_all <;> omega

/-- Per-axis step data: the low levels (`k-1-l ≤ 2`) of the cell of axis `d` change by
`e · [k-1-l ≤ J]`. -/
def AxisStep (k : ℕ) (v w : Fin (4 * k) → ZMod q) (d : Fin 4) (e : ℤ) (J : ℕ) : Prop :=
  ∀ l : Fin k, k - 1 - (l : ℕ) ≤ 2 →
    w (ix k d l) - v (ix k d l) = (e : ZMod q) * (if k - 1 - (l : ℕ) ≤ J then 1 else 0)

lemma axisStep_plus (hq : 1 < q) (k : ℕ) (hk : 1 ≤ k) (v w : Fin (4 * k) → ZMod q) (d : Fin 4)
    (h : cellN q k w d = (cellN q k v d + 1) % q ^ k) :
    AxisStep q k v w d 1 (Jof q k (cellN q k v d)) := by
  intro l hl
  rw [carry_digits q hq k v w d h l]
  have := dvd_iff_le_Jof q k (cellN q k v d) (k - 1 - l) hl (by have := l.isLt; omega)
  by_cases h' : q ^ (k - 1 - (l : ℕ)) ∣ cellN q k v d + 1
  · rw [if_pos h', if_pos (this.mp h')]; simp
  · rw [if_neg h', if_neg (fun h2 => h' (this.mpr h2))]; simp

lemma axisStep_minus (hq : 1 < q) (k : ℕ) (hk : 1 ≤ k) (v w : Fin (4 * k) → ZMod q) (d : Fin 4)
    (h : cellN q k v d = (cellN q k w d + 1) % q ^ k) :
    AxisStep q k v w d (-1) (Jof q k (cellN q k w d)) := by
  intro l hl
  have := axisStep_plus q hq k hk w v d h l hl
  rw [← neg_sub, this]; push_cast; ring

lemma axisStep_zero (hq : 1 < q) (k : ℕ) (v w : Fin (4 * k) → ZMod q) (d : Fin 4)
    (h : cellN q k w d = cellN q k v d) : AxisStep q k v w d 0 0 := by
  intro l _
  rw [digits_eq_of_cellN_eq q hq k v w d h l]; simp

/-! ## Change of the first offset digit -/

lemma sum_tab_indicator (t : ℕ → ℤ) (k J : ℕ) (hJ : J < k) :
    ∑ l : Fin k, t (k - 1 - (l : ℕ)) * (if k - 1 - (l : ℕ) ≤ J then 1 else 0) =
      ∑ s ∈ range (J + 1), t s := by
  rw [Fin.sum_univ_eq_sum_range (fun l => t (k - 1 - l) * (if k - 1 - l ≤ J then 1 else 0)) k,
    sum_range_reflect (fun s => t s * (if s ≤ J then 1 else 0)) k,
    ← sum_range_add_sum_Ico _ (show J + 1 ≤ k by omega)]
  rw [sum_eq_zero (s := Ico (J + 1) k) (fun s hs => by simp only [mem_Ico] at hs; rw [if_neg (by omega)]; simp),
    add_zero]
  refine sum_congr rfl fun s hs => ?_
  simp only [mem_range] at hs; rw [if_pos (by omega), mul_one]

/-- Change of the first offset digit (digit `k`) of coordinate `c` under per-axis steps:
`σ_c = ∑_d e_d ∑_{s ≤ J_d} F_s[c][d]` (mod `q`). -/
lemma Dg_off_sub (hq : Odd q) (k : ℕ) (hk : 2 ≤ k) (c : Fin 4) (v w : Fin (4 * k) → ZMod q)
    (e : Fin 4 → ℤ) (J : Fin 4 → ℕ) (hJk : ∀ d, J d < k)
    (hstep : ∀ d, AxisStep q k v w d (e d) (J d)) :
    Dg q k c w ⟨k + 0, by omega⟩ - Dg q k c v ⟨k + 0, by omega⟩ =
      ∑ d : Fin 4, (e d : ZMod q) * ((∑ s ∈ range (J d + 1), Fdes s c d : ℤ) : ZMod q) := by
  have hrow := row0 ((2 : ZMod q)⁻¹) (two_mul_inv_two' q hq) k hk
  rw [show (⟨k + 0, by omega⟩ : Fin (4 * k)) = ⟨k + ((⟨0, by omega⟩ : Fin (3 * k)) : ℕ), by simp; omega⟩
    from rfl, Dg_off, Dg_off, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_sub_distrib, ← sum_tab_indicator (fun s => Fdes s c d) k (J d) (hJk d)]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [← mul_sub, hrow c d l]
  by_cases hl : k - 1 - (l : ℕ) ≤ 2
  · rw [hstep d l hl]; ring
  · have : Fdes (k - 1 - (l : ℕ)) c d = 0 := by
      simp [Fdes, show k - 1 - (l : ℕ) ≠ 0 by omega, show k - 1 - (l : ℕ) ≠ 1 by omega,
        show k - 1 - (l : ℕ) ≠ 2 by omega]
    rw [this]; simp

/-- If no other axis moves, offset digits `k + r` with `r ≥ 1` of coordinate `c` do not change
(hypothesis (H2)). -/
lemma Dg_off_eq_of_only (hq : 1 < q) (k : ℕ) (c : Fin 4) (v w : Fin (4 * k) → ZMod q)
    (hother : ∀ d, d ≠ c → cellN q k w d = cellN q k v d) (r : Fin (3 * k)) (hr : (r : ℕ) ≠ 0) :
    Dg q k c w ⟨k + r, by omega⟩ = Dg q k c v ⟨k + r, by omega⟩ := by
  rw [Dg_off, Dg_off]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  by_cases hd : d = c
  · subst hd; rw [diag_deep _ k d r hr l]; simp
  · rw [digits_eq_of_cellN_eq q hq k v w d (hother d hd) l]

end

end Z3NetD4.Proofs

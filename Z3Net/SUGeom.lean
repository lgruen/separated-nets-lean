module
public import Mathlib
public import Z3Net.SURows
public import Z3Net.SUThm1
public import Z3Net.TwoGeom

@[expose] public section

/-!
# Entry U, part 6: digits, cells and carries of `𝒫^s_{k,q}` (Lemma S_s, geometric part)

The point `Upoint s q k v` has, in coordinate `c`, digits `D_c(v) = UGen s q k c · v`: the first
`k` are the cell digits `v_{ck+i}` (graph form), digit `k + r` is `∑_{d,l} Φ'_cd[r,l] v_{dk+l}`.
Adapted from the 4D entry (`Z3Net/D4Geom.lean`) to `s` coordinates; carry classes are capped at
`min(s-2, k-1)`.
-/

namespace Z3NetU.Proofs

open Finset Matrix Z3NetU

noncomputable section

variable (s q : ℕ)

/-- Digit vector of coordinate `c` of the point with index `v`. -/
def Dg (k : ℕ) (c : Fin s) (v : Fin (s * k) → ZMod q) : Fin (s * k) → ZMod q := UGen s q k c *ᵥ v

lemma Upoint_eq (k : ℕ) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    Upoint s q k v c = ∑ j : Fin (s * k), (Dg s q k c v j).val * q ^ (s * k - 1 - (j : ℕ)) := rfl

lemma Dg_cell (k : ℕ) (c : Fin s) (v : Fin (s * k) → ZMod q) (i : ℕ) (hi : i < k) :
    Dg s q k c v ⟨i, lt_of_lt_of_le hi (k_le_sk k c)⟩ = v (ix k c ⟨i, hi⟩) :=
  graphGen_cell k _ c v i hi

lemma Dg_off (k : ℕ) (c : Fin s) (v : Fin (s * k) → ZMod q) (r : Fin (s * k - k)) :
    Dg s q k c v ⟨k + r, sk_sub_add r⟩ =
      ∑ d : Fin s, ∑ l : Fin k, UPhi (ZMod q) (fun i => ((i : ℕ) : ZMod q)⁻¹) k c d r l * v (ix k d l) :=
  graphGen_off k _ c v r

/-! ## Decomposition of a coordinate -/

variable [NeZero q]

/-- Total digit accessor (as natural numbers). -/
def dv (k : ℕ) (D : Fin (s * k) → ZMod q) (j : ℕ) : ℕ :=
  if h : j < s * k then (D ⟨j, h⟩).val else 0

lemma dv_lt (k : ℕ) (D : Fin (s * k) → ZMod q) (j : ℕ) : dv s q k D j < q := by
  unfold dv; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero q

/-- Tail of the expansion (digits `k+1, …, sk-1`). -/
def tail (k : ℕ) (D : Fin (s * k) → ZMod q) : ℕ :=
  ∑ j ∈ Ico (k + 1) (s * k), dv s q k D j * q ^ (s * k - 1 - j)

lemma tail_lt (k : ℕ) (hsk : k + 1 ≤ s * k) (D : Fin (s * k) → ZMod q) :
    tail s q k D < q ^ (s * k - k - 1) := by
  unfold tail
  rw [sum_Ico_eq_sum_range, show s * k - (k + 1) = s * k - k - 1 by omega]
  have := Z3Net.Two.sum_digits_be_lt q (Nat.pos_of_neZero q) (fun t => dv s q k D (k + 1 + t))
    (fun t => dv_lt s q k D _) (s * k - k - 1)
  convert this using 2 with t ht
  simp only [mem_range] at ht
  rw [show s * k - 1 - (k + 1 + t) = s * k - k - 1 - 1 - t by omega]

lemma coord_split (k : ℕ) (hsk : k + 1 ≤ s * k) (D : Fin (s * k) → ZMod q) :
    ∑ j : Fin (s * k), (D j).val * q ^ (s * k - 1 - (j : ℕ)) =
      q ^ (s * k - k) * (∑ i ∈ range k, dv s q k D i * q ^ (k - 1 - i)) +
        q ^ (s * k - k - 1) * dv s q k D k + tail s q k D := by
  rw [show ∑ j : Fin (s * k), (D j).val * q ^ (s * k - 1 - (j : ℕ)) =
      ∑ j : Fin (s * k), dv s q k D j * q ^ (s * k - 1 - (j : ℕ)) by
        refine sum_congr rfl fun j _ => ?_; simp [dv, j.isLt],
    Fin.sum_univ_eq_sum_range (fun j => dv s q k D j * q ^ (s * k - 1 - j)),
    ← sum_range_add_sum_Ico _ (show k ≤ s * k by omega),
    sum_eq_sum_Ico_succ_bot (show k < s * k by omega), tail, mul_sum]
  rw [show s * k - 1 - k = s * k - k - 1 by omega]
  have : ∑ i ∈ range k, dv s q k D i * q ^ (s * k - 1 - i) =
      ∑ i ∈ range k, q ^ (s * k - k) * (dv s q k D i * q ^ (k - 1 - i)) := by
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    rw [show s * k - 1 - i = (s * k - k) + (k - 1 - i) by omega, pow_add]; ring
  rw [this]; ring

/-! ## Cells and carries -/

/-- Level `i` digit (as a natural number) of the cell of axis `d`. -/
def ad (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) (i : ℕ) : ℕ :=
  if h : i < k then (v (ix k d ⟨i, h⟩)).val else 0

lemma ad_lt (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) (i : ℕ) : ad s q k v d i < q := by
  unfold ad; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero q

/-- The cell `n_d ∈ [0, q^k)` of axis `d`. -/
def cellN (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) : ℕ :=
  ∑ i ∈ range k, ad s q k v d i * q ^ (k - 1 - i)

lemma cellN_lt (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) : cellN s q k v d < q ^ k :=
  Z3Net.Two.sum_digits_be_lt q (Nat.pos_of_neZero q) _ (ad_lt s q k v d) k

lemma cell_part (k : ℕ) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    ∑ i ∈ range k, dv s q k (Dg s q k c v) i * q ^ (k - 1 - i) = cellN s q k v c := by
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  congr 1
  have hik : i < s * k := lt_of_lt_of_le hi (k_le_sk k c)
  simp only [dv, ad, dif_pos hi, dif_pos hik]
  rw [Dg_cell s q k c v i hi]

lemma cellN_digit (hq : 1 < q) (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) (l : Fin k) :
    cellN s q k v d / q ^ (k - 1 - (l : ℕ)) % q = (v (ix k d l)).val := by
  have hl := l.isLt
  unfold cellN
  rw [Z3Net.Two.digit_extract_be q hq k _ (ad_lt s q k v d) _ (by omega),
    show k - 1 - (k - 1 - (l : ℕ)) = l by omega]
  simp [ad, hl]

lemma zmod_digit (hq : 1 < q) (k : ℕ) (v : Fin (s * k) → ZMod q) (d : Fin s) (l : Fin k) :
    v (ix k d l) = ((cellN s q k v d / q ^ (k - 1 - (l : ℕ)) : ℕ) : ZMod q) := by
  rw [← ZMod.natCast_mod, cellN_digit s q hq, ZMod.natCast_zmod_val]

lemma digits_eq_of_cellN_eq (hq : 1 < q) (k : ℕ) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (h : cellN s q k w d = cellN s q k v d) (l : Fin k) : w (ix k d l) = v (ix k d l) := by
  rw [zmod_digit s q hq k w, zmod_digit s q hq k v, h]

/-- **Carry lemma.** If the cell of axis `d` steps by `+1` (mod `q^k`), the level-`l` digit changes
by `1` iff `q^(k-1-l)` divides `n + 1`. -/
lemma carry_digits (hq : 1 < q) (k : ℕ) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (h : cellN s q k w d = (cellN s q k v d + 1) % q ^ k) (l : Fin k) :
    w (ix k d l) - v (ix k d l) =
      if q ^ (k - 1 - (l : ℕ)) ∣ cellN s q k v d + 1 then 1 else 0 := by
  have hl := l.isLt
  set t := k - 1 - (l : ℕ) with ht
  have htk : t < k := by omega
  rw [zmod_digit s q hq k w, zmod_digit s q hq k v, h, ← ht]
  have e1 : (cellN s q k v d + 1) % q ^ k / q ^ t = (cellN s q k v d + 1) / q ^ t % q ^ (k - t) := by
    rw [show q ^ k = q ^ t * q ^ (k - t) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self]
  rw [e1, ← ZMod.natCast_mod, Nat.mod_mod_of_dvd _ (dvd_pow_self q (by omega)), ZMod.natCast_mod,
    Nat.succ_div]
  split_ifs <;> simp

/-- Carry class: the largest `t ≤ min(s-2, k-1)` with `q^t ∣ n + 1`. -/
def Jof (k n : ℕ) : ℕ := Nat.findGreatest (fun t => q ^ t ∣ n + 1) (min (s - 2) (k - 1))

lemma Jof_le (k n : ℕ) : Jof s q k n ≤ min (s - 2) (k - 1) := Nat.findGreatest_le _

lemma dvd_iff_le_Jof (k n t : ℕ) (ht : t ≤ min (s - 2) (k - 1)) :
    q ^ t ∣ n + 1 ↔ t ≤ Jof s q k n := by
  constructor
  · intro h; exact Nat.le_findGreatest ht h
  · intro h
    have hJ : q ^ Jof s q k n ∣ n + 1 :=
      Nat.findGreatest_spec (P := fun t => q ^ t ∣ n + 1) (Nat.zero_le _) (by simp)
    exact (pow_dvd_pow q h).trans hJ

/-- Per-axis step data: the low levels (`k-1-l ≤ s-2`) of the cell of axis `d` change by
`e · [k-1-l ≤ J]`. -/
def AxisStep (k : ℕ) (v w : Fin (s * k) → ZMod q) (d : Fin s) (e : ℤ) (J : ℕ) : Prop :=
  ∀ l : Fin k, k - 1 - (l : ℕ) ≤ s - 2 →
    w (ix k d l) - v (ix k d l) = (e : ZMod q) * (if k - 1 - (l : ℕ) ≤ J then 1 else 0)

lemma axisStep_plus (hq : 1 < q) (k : ℕ) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (h : cellN s q k w d = (cellN s q k v d + 1) % q ^ k) :
    AxisStep s q k v w d 1 (Jof s q k (cellN s q k v d)) := by
  intro l hl
  rw [carry_digits s q hq k v w d h l]
  have := dvd_iff_le_Jof s q k (cellN s q k v d) (k - 1 - l)
    (le_min hl (by have := l.isLt; omega))
  by_cases h' : q ^ (k - 1 - (l : ℕ)) ∣ cellN s q k v d + 1
  · rw [if_pos h', if_pos (this.mp h')]; simp
  · rw [if_neg h', if_neg (fun h2 => h' (this.mpr h2))]; simp

lemma axisStep_minus (hq : 1 < q) (k : ℕ) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (h : cellN s q k v d = (cellN s q k w d + 1) % q ^ k) :
    AxisStep s q k v w d (-1) (Jof s q k (cellN s q k w d)) := by
  intro l hl
  have := axisStep_plus s q hq k w v d h l hl
  rw [← neg_sub, this]; push_cast; ring

lemma axisStep_zero (hq : 1 < q) (k : ℕ) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (h : cellN s q k w d = cellN s q k v d) : AxisStep s q k v w d 0 0 := by
  intro l _
  rw [digits_eq_of_cellN_eq s q hq k v w d h l]; simp

/-! ## Change of the first offset digit -/

lemma sum_tab_indicator (t : ℕ → ℤ) (k J : ℕ) (hJ : J < k) :
    ∑ l : Fin k, t (k - 1 - (l : ℕ)) * (if k - 1 - (l : ℕ) ≤ J then 1 else 0) =
      ∑ i ∈ range (J + 1), t i := by
  rw [Fin.sum_univ_eq_sum_range (fun l => t (k - 1 - l) * (if k - 1 - l ≤ J then 1 else 0)) k,
    sum_range_reflect (fun i => t i * (if i ≤ J then 1 else 0)) k,
    ← sum_range_add_sum_Ico _ (show J + 1 ≤ k by omega)]
  rw [sum_eq_zero (s := Ico (J + 1) k) (fun i hi => by simp only [mem_Ico] at hi; rw [if_neg (by omega)]; simp),
    add_zero]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi; rw [if_pos (by omega), mul_one]

lemma Fdes_high (n : ℕ) (hn : s - 1 ≤ n) (hs : 3 ≤ s) (c d : Fin s) : Fdes s n c d = 0 := by
  unfold Fdes
  split_ifs with h1 h2
  · omega
  · rfl
  · rw [Foff, if_pos hn]

/-- `P(i,d,J) = ∑_{t ≤ J} F_t[i][d]`. -/
def PJ (i d : Fin s) (J : ℕ) : ℤ := ∑ t ∈ range (J + 1), Fdes s t i d

/-- Change of the first offset digit (digit `k`) of coordinate `c` under per-axis steps:
`σ_c = ∑_d e_d ∑_{t ≤ J_d} F_t[c][d]` (mod `q`). -/
lemma Dg_off_sub (hs : 3 ≤ s) (hq : Admissible s q) (k : ℕ) (hk : 2 ≤ k) (c : Fin s)
    (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ) (J : Fin s → ℕ) (hJk : ∀ d, J d < k)
    (hJs : ∀ d, J d ≤ s - 2) (hstep : ∀ d, AxisStep s q k v w d (e d) (J d)) (r : Fin (s * k - k))
    (hr : (r : ℕ) = 0) :
    Dg s q k c w ⟨k + r, sk_sub_add r⟩ - Dg s q k c v ⟨k + r, sk_sub_add r⟩ =
      ∑ d : Fin s, (e d : ZMod q) * ((PJ s c d (J d) : ℤ) : ZMod q) := by
  have hrow := row0 hs (ivOK_zmod s q hq) k c
  rw [Dg_off, Dg_off, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_sub_distrib, PJ, ← sum_tab_indicator (fun t => Fdes s t c d) k (J d) (hJk d)]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [← mul_sub, hrow d r hr l]
  by_cases hl : k - 1 - (l : ℕ) ≤ s - 2
  · rw [hstep d l hl]; ring
  · rw [Fdes_high s (k - 1 - (l : ℕ)) (by omega) hs c d]; simp

/-- If no other axis moves, offset digits `k + r` with `r ≥ 1` of coordinate `c` do not change
(hypothesis (H2)). -/
lemma Dg_off_eq_of_only (hq : 1 < q) (k : ℕ) (c : Fin s) (v w : Fin (s * k) → ZMod q)
    (hother : ∀ d, d ≠ c → cellN s q k w d = cellN s q k v d) (r : Fin (s * k - k))
    (hr : (r : ℕ) ≠ 0) :
    Dg s q k c w ⟨k + r, sk_sub_add r⟩ = Dg s q k c v ⟨k + r, sk_sub_add r⟩ := by
  rw [Dg_off, Dg_off]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  by_cases hd : d = c
  · subst hd; simp [UPhi, hr]
  · rw [digits_eq_of_cellN_eq s q hq k v w d (hother d hd) l]

end

end Z3NetU.Proofs

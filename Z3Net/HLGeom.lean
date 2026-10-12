module
public import Mathlib
public import Z3Net.HLRows
public import Z3Net.SUSep

@[expose] public section

/-!
# Entry HL, part 5: digits, cells and carries (cell steps `e ∈ {1, 2}`)

The point `HLpoint` has, in coordinate `c`, digits `Dg c x = HLGen c · x`: the first `k` are the
cell digits `x_{ck+i}` (graph form), digit `k + r` is `∑_{d,l} Φ'_cd[r,l] x_{dk+l}`. Adapted from
entry U (`Z3Net/SUGeom.lean`); the carry lemma covers steps `+1` and `+2`: digit `x`-index `t`
(level `k-1-t`) changes by `e` for `t = 0` and by `[t ≤ J]` for `t ≥ 1` (the carry reaches all
levels up to the carry length `J`).
-/

namespace Z3NetHL.Proofs

open Finset Matrix

noncomputable section

variable (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
  (dg : Fin s → ℕ → ℚ)

open Z3NetU.Proofs (ix ix_surj sk_sub_add graphGen_cell graphGen_off)

/-- Digit vector of coordinate `c` of the point with index `x`. -/
def Dg (c : Fin s) (x : Fin (s * k) → ZMod q) : Fin (s * k) → ZMod q :=
  HLGen s q k u v lam gco dg c *ᵥ x

lemma HLpoint_eq (x : Fin (s * k) → ZMod q) (c : Fin s) :
    HLpoint s q k u v lam gco dg x c =
      ∑ j : Fin (s * k), (Dg s q k u v lam gco dg c x j).val * q ^ (s * k - 1 - (j : ℕ)) := rfl

lemma Dg_cell (c : Fin s) (x : Fin (s * k) → ZMod q) (i : ℕ) (hi : i < k) :
    Dg s q k u v lam gco dg c x ⟨i, lt_of_lt_of_le hi (k_le_sk' k c)⟩ = x (ix k c ⟨i, hi⟩) :=
  graphGen_cell k _ c x i hi

lemma Dg_off (c : Fin s) (x : Fin (s * k) → ZMod q) (r : Fin (s * k - k)) :
    Dg s q k u v lam gco dg c x ⟨k + r, sk_sub_add r⟩ =
      ∑ d : Fin s, ∑ l : Fin k, HLPhi s q k u v lam gco dg c d r l * x (ix k d l) :=
  graphGen_off k _ c x r

/-! ## Decomposition of a coordinate -/

variable [NeZero q]

/-- Total digit accessor (as natural numbers). -/
def dv (D : Fin (s * k) → ZMod q) (j : ℕ) : ℕ :=
  if h : j < s * k then (D ⟨j, h⟩).val else 0

lemma dv_lt (D : Fin (s * k) → ZMod q) (j : ℕ) : dv s q k D j < q := by
  unfold dv; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero q

/-- Tail of the expansion (digits `k+1, …, sk-1`). -/
def tail (D : Fin (s * k) → ZMod q) : ℕ :=
  ∑ j ∈ Ico (k + 1) (s * k), dv s q k D j * q ^ (s * k - 1 - j)

lemma tail_lt (hsk : k + 1 ≤ s * k) (D : Fin (s * k) → ZMod q) :
    tail s q k D < q ^ (s * k - k - 1) := by
  unfold tail
  rw [sum_Ico_eq_sum_range, show s * k - (k + 1) = s * k - k - 1 by omega]
  have := Z3Net.Two.sum_digits_be_lt q (Nat.pos_of_neZero q) (fun t => dv s q k D (k + 1 + t))
    (fun t => dv_lt s q k D _) (s * k - k - 1)
  convert this using 2 with t ht
  simp only [mem_range] at ht
  rw [show s * k - 1 - (k + 1 + t) = s * k - k - 1 - 1 - t by omega]

lemma coord_split (hsk : k + 1 ≤ s * k) (D : Fin (s * k) → ZMod q) :
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
def ad (x : Fin (s * k) → ZMod q) (d : Fin s) (i : ℕ) : ℕ :=
  if h : i < k then (x (ix k d ⟨i, h⟩)).val else 0

lemma ad_lt (x : Fin (s * k) → ZMod q) (d : Fin s) (i : ℕ) : ad s q k x d i < q := by
  unfold ad; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero q

/-- The cell `n_d ∈ [0, q^k)` of axis `d`. -/
def cellN (x : Fin (s * k) → ZMod q) (d : Fin s) : ℕ :=
  ∑ i ∈ range k, ad s q k x d i * q ^ (k - 1 - i)

lemma cellN_lt (x : Fin (s * k) → ZMod q) (d : Fin s) : cellN s q k x d < q ^ k :=
  Z3Net.Two.sum_digits_be_lt q (Nat.pos_of_neZero q) _ (ad_lt s q k x d) k

lemma cell_part (x : Fin (s * k) → ZMod q) (c : Fin s) :
    ∑ i ∈ range k, dv s q k (Dg s q k u v lam gco dg c x) i * q ^ (k - 1 - i) = cellN s q k x c := by
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  congr 1
  have hik : i < s * k := lt_of_lt_of_le hi (k_le_sk' k c)
  simp only [dv, ad, dif_pos hi, dif_pos hik]
  rw [Dg_cell s q k u v lam gco dg c x i hi]

lemma cellN_digit (hq : 1 < q) (x : Fin (s * k) → ZMod q) (d : Fin s) (l : Fin k) :
    cellN s q k x d / q ^ (k - 1 - (l : ℕ)) % q = (x (ix k d l)).val := by
  have hl := l.isLt
  unfold cellN
  rw [Z3Net.Two.digit_extract_be q hq k _ (ad_lt s q k x d) _ (by omega),
    show k - 1 - (k - 1 - (l : ℕ)) = l by omega]
  simp [ad, hl]

lemma zmod_digit (hq : 1 < q) (x : Fin (s * k) → ZMod q) (d : Fin s) (l : Fin k) :
    x (ix k d l) = ((cellN s q k x d / q ^ (k - 1 - (l : ℕ)) : ℕ) : ZMod q) := by
  rw [← ZMod.natCast_mod, cellN_digit s q k hq, ZMod.natCast_zmod_val]

lemma digits_eq_of_cellN_eq (hq : 1 < q) (x y : Fin (s * k) → ZMod q) (d : Fin s)
    (h : cellN s q k y d = cellN s q k x d) (l : Fin k) : y (ix k d l) = x (ix k d l) := by
  rw [zmod_digit s q k hq y, zmod_digit s q k hq x, h]

/-- The carry from a step `+e` reaches `x`-index `t`. -/
abbrev Car (e n t : ℕ) : Prop := n / q ^ t < (n + e) / q ^ t

lemma car_mono (e n t t' : ℕ) (h : t' ≤ t) (hc : Car q e n t) : Car q e n t' := by
  unfold Car at hc ⊢
  by_contra hne
  push_neg at hne
  have hle : (n + e) / q ^ t' ≤ n / q ^ t' := hne
  have h2 : (n + e) / q ^ t = (n + e) / q ^ t' / q ^ (t - t') := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega
  have h3 : n / q ^ t = n / q ^ t' / q ^ (t - t') := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega
  have := Nat.div_le_div_right (c := q ^ (t - t')) hle
  omega

lemma car_step (hq : 2 < q) (e n t : ℕ) (he : e ≤ 2) (ht : 1 ≤ t) :
    (n + e) / q ^ t ≤ n / q ^ t + 1 := by
  have hqt : e ≤ q ^ t := by
    calc e ≤ 2 := he
      _ ≤ q := by omega
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ t := Nat.pow_le_pow_right (by omega) ht
  calc (n + e) / q ^ t ≤ (n + q ^ t) / q ^ t := Nat.div_le_div_right (by omega)
    _ = n / q ^ t + 1 := Nat.add_div_right _ (by positivity)

/-- **Carry lemma** (steps `+1`, `+2`). -/
lemma carry_digits2 (hq : 2 < q) (x y : Fin (s * k) → ZMod q) (d : Fin s) (e : ℕ) (he1 : 1 ≤ e)
    (he : e ≤ 2) (h : cellN s q k y d = (cellN s q k x d + e) % q ^ k) (l : Fin k) :
    y (ix k d l) - x (ix k d l) =
      if k - 1 - (l : ℕ) = 0 then (e : ZMod q)
      else if Car q e (cellN s q k x d) (k - 1 - (l : ℕ)) then 1 else 0 := by
  have hl := l.isLt
  set t := k - 1 - (l : ℕ) with ht
  have htk : t < k := by omega
  rw [zmod_digit s q k (by omega) y, zmod_digit s q k (by omega) x, h, ← ht]
  have e1 : (cellN s q k x d + e) % q ^ k / q ^ t = (cellN s q k x d + e) / q ^ t % q ^ (k - t) := by
    rw [show q ^ k = q ^ t * q ^ (k - t) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self]
  rw [e1, ← ZMod.natCast_mod, Nat.mod_mod_of_dvd _ (dvd_pow_self q (by omega)), ZMod.natCast_mod]
  split_ifs with h0 hc
  · rw [h0]; simp only [pow_zero, Nat.div_one]; push_cast; ring
  · unfold Car at hc
    have := car_step q hq e (cellN s q k x d) t he (by omega)
    have heq : (cellN s q k x d + e) / q ^ t = cellN s q k x d / q ^ t + 1 := by omega
    rw [heq]; push_cast; ring
  · unfold Car at hc
    have heq : (cellN s q k x d + e) / q ^ t = cellN s q k x d / q ^ t := by
      have := Nat.div_le_div_right (c := q ^ t) (show cellN s q k x d ≤ cellN s q k x d + e by omega)
      omega
    rw [heq, sub_self]

/-- Carry length: the largest `t ≤ min(s-2, k-1)` reached by the carry of a step `+e`. -/
def Jof2 (e n : ℕ) : ℕ := Nat.findGreatest (fun t => Car q e n t) (min (s - 2) (k - 1))

lemma Jof2_le (e n : ℕ) : Jof2 s q k e n ≤ min (s - 2) (k - 1) := Nat.findGreatest_le _

lemma car_iff_le_Jof2 (e n t : ℕ) (he1 : 1 ≤ e) (ht : t ≤ min (s - 2) (k - 1)) :
    Car q e n t ↔ t ≤ Jof2 s q k e n := by
  constructor
  · intro h; exact Nat.le_findGreatest ht h
  · intro h
    have hJ : Car q e n (Jof2 s q k e n) := by
      apply Nat.findGreatest_spec (P := fun t => Car q e n t) (Nat.zero_le _)
      unfold Car; simp; omega
    exact car_mono q e n _ t h hJ

/-- Per-axis step data: on `x`-indices `t ≤ s-2`, the cell of axis `d` changes by `E` at `t = 0`
and by `sgn(E) [t ≤ J]` for `t ≥ 1`. -/
def AxisStep2 (x y : Fin (s * k) → ZMod q) (d : Fin s) (E : ℤ) (J : ℕ) : Prop :=
  ∀ l : Fin k, k - 1 - (l : ℕ) ≤ s - 2 →
    y (ix k d l) - x (ix k d l) =
      if k - 1 - (l : ℕ) = 0 then (E : ZMod q)
      else (E.sign : ZMod q) * (if k - 1 - (l : ℕ) ≤ J then 1 else 0)

lemma axisStep2_plus (hq : 2 < q) (x y : Fin (s * k) → ZMod q) (d : Fin s) (e : ℕ) (he1 : 1 ≤ e)
    (he : e ≤ 2) (h : cellN s q k y d = (cellN s q k x d + e) % q ^ k) :
    AxisStep2 s q k x y d (e : ℤ) (Jof2 s q k e (cellN s q k x d)) := by
  intro l hl
  rw [carry_digits2 s q k hq x y d e he1 he h l]
  have hsg : ((e : ℤ).sign : ZMod q) = 1 := by
    rw [Int.sign_natCast_of_ne_zero (by omega)]; simp
  split_ifs with h0 hc hJ hJ
  · push_cast; ring
  · rw [hsg, mul_one]
  · exact absurd ((car_iff_le_Jof2 s q k e _ _ he1 (le_min hl (by have := l.isLt; omega))).mp hc) hJ
  · exact absurd ((car_iff_le_Jof2 s q k e _ _ he1 (le_min hl (by have := l.isLt; omega))).mpr hJ) hc
  · rw [mul_zero]

lemma axisStep2_minus (hq : 2 < q) (x y : Fin (s * k) → ZMod q) (d : Fin s) (e : ℕ) (he1 : 1 ≤ e)
    (he : e ≤ 2) (h : cellN s q k x d = (cellN s q k y d + e) % q ^ k) :
    AxisStep2 s q k x y d (-(e : ℤ)) (Jof2 s q k e (cellN s q k y d)) := by
  intro l hl
  have := axisStep2_plus s q k hq y x d e he1 he h l hl
  rw [← neg_sub, this]
  split_ifs <;> simp only [Int.sign_neg, Int.cast_neg, Int.cast_natCast] <;> ring

lemma axisStep2_zero (hq : 1 < q) (x y : Fin (s * k) → ZMod q) (d : Fin s)
    (h : cellN s q k y d = cellN s q k x d) : AxisStep2 s q k x y d 0 0 := by
  intro l _
  rw [digits_eq_of_cellN_eq s q k hq x y d h l]; simp

end

end Z3NetHL.Proofs

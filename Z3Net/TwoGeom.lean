module
public import Mathlib
public import Z3Net.Defs
public import Z3Net.TwoRows

@[expose] public section

/-!
# Theorem 2 (`thm:two`), part 4: digits, cells and carries of `𝒬_{k,p}`

The point `Qpoint p k v` has, in coordinate `c`, digits `D_c(v) = QGen k c · v`: the first `k`
are the cell digits `v_{ck+i}` (graph form), digit `k + r` is `∑_{d,l} Φ_cd[r,l] v_{dk+l}`.
-/

namespace Z3Net.Two

open Finset Matrix

noncomputable section

lemma idx_lt (k : ℕ) (d : Fin 3) (l : Fin k) : (d : ℕ) * k + l < 3 * k := by
  have := d.isLt; have := l.isLt
  calc (d : ℕ) * k + l < (d : ℕ) * k + k := by omega
    _ = ((d : ℕ) + 1) * k := by ring
    _ ≤ 3 * k := Nat.mul_le_mul_right _ (by omega)

/-- The index digit `v_{dk+l}` (level `l` of the cell of axis `d`). -/
def ix (k : ℕ) (d : Fin 3) (l : Fin k) : Fin (3 * k) := ⟨(d : ℕ) * k + l, idx_lt k d l⟩

lemma sum_fin3k {M : Type*} [AddCommMonoid M] (k : ℕ) (f : Fin (3 * k) → M) :
    ∑ j, f j = ∑ d : Fin 3, ∑ l : Fin k, f (ix k d l) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  congr 1; ext; simp [finProdFinEquiv, ix]; ring

lemma ix_div (k : ℕ) (d : Fin 3) (l : Fin k) : ((ix k d l : ℕ)) / k = d := by
  have := l.isLt
  simp only [ix]; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt this]
  simp

lemma ix_mod (k : ℕ) (d : Fin 3) (l : Fin k) : ((ix k d l : ℕ)) % k = l := by
  have := l.isLt
  simp only [ix]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt this]

variable (p : ℕ)

/-- The graph-form blocks of `𝒬_{k,p}` (over `ℤ`). -/
def QPhi (k : ℕ) : Fin 3 → Fin 3 → Matrix (Fin (2 * k)) (Fin k) ℤ := QPhiOf k (frameB k) (frameC k)

/-- Digit vector of coordinate `c` of the point with index `v`. -/
def Dg (k : ℕ) (c : Fin 3) (v : Fin (3 * k) → ZMod p) : Fin (3 * k) → ZMod p :=
  ((QGen k c).map (Int.cast : ℤ → ZMod p)) *ᵥ v

lemma Qpoint_eq (k : ℕ) (v : Fin (3 * k) → ZMod p) (c : Fin 3) :
    Qpoint p k v c = ∑ j : Fin (3 * k), (Dg p k c v j).val * p ^ (3 * k - 1 - (j : ℕ)) := rfl

lemma Dg_cell (k : ℕ) (c : Fin 3) (v : Fin (3 * k) → ZMod p) (i : Fin (3 * k)) (hi : (i : ℕ) < k) :
    Dg p k c v i = v (ix k c ⟨i, hi⟩) := by
  simp only [Dg, mulVec, dotProduct, Matrix.map_apply, QGen, graphGen, if_pos hi]
  rw [Fintype.sum_eq_single (ix k c ⟨i, hi⟩)]
  · simp [ix]
  · intro j hj
    rw [if_neg]; · simp
    intro h; apply hj; ext; simp [ix, h]

lemma Dg_off (k : ℕ) (c : Fin 3) (v : Fin (3 * k) → ZMod p) (r : Fin (2 * k)) :
    Dg p k c v ⟨k + r, by omega⟩ =
      ∑ d : Fin 3, ∑ l : Fin k, ((QPhi k c d r l : ℤ) : ZMod p) * v (ix k d l) := by
  simp only [Dg, mulVec, dotProduct, Matrix.map_apply, QGen, graphGen]
  rw [sum_fin3k]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  rw [if_neg (by omega)]
  congr 2
  have h1 : (⟨(ix k d l : ℕ) / k, Nat.div_lt_of_lt_mul (by have := (ix k d l).isLt; omega)⟩ : Fin 3) = d :=
    Fin.ext (ix_div k d l)
  rw [ent, dif_pos ⟨by omega, by rw [ix_mod]; exact l.isLt⟩]
  simp only [QPhi]
  congr 1
  · ext; simp
  · ext; simp [ix_mod]

/-! ## Base-`p` digit expansions -/

lemma sum_digits_lt (hp : 0 < p) (g : ℕ → ℕ) (hg : ∀ t, g t < p) (n : ℕ) :
    ∑ t ∈ range n, g t * p ^ t < p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ]
    have := hg n
    have h1 : g n * p ^ n ≤ (p - 1) * p ^ n := Nat.mul_le_mul_right _ (by omega)
    have h2 : (p - 1) * p ^ n + p ^ n = p ^ n * p := by
      rw [mul_comm (p ^ n) p, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    omega

lemma reflect_digits (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range n, f i * p ^ (n - 1 - i) = ∑ t ∈ range n, f (n - 1 - t) * p ^ t := by
  rw [← sum_range_reflect (fun i => f i * p ^ (n - 1 - i)) n]
  refine sum_congr rfl fun t ht => ?_
  simp only [mem_range] at ht
  rw [show n - 1 - (n - 1 - t) = t by omega]

lemma sum_digits_be_lt (hp : 0 < p) (f : ℕ → ℕ) (hf : ∀ t, f t < p) (n : ℕ) :
    ∑ i ∈ range n, f i * p ^ (n - 1 - i) < p ^ n := by
  rw [reflect_digits]; exact sum_digits_lt p hp _ (fun t => hf _) n

lemma digit_extract (hp : 1 < p) (k : ℕ) (g : ℕ → ℕ) (hg : ∀ t, g t < p) (s : ℕ) :
    (∑ t ∈ range k, g t * p ^ t) / p ^ s % p = if s < k then g s else 0 := by
  induction k generalizing g s with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ']
    have e : ∑ t ∈ range k, g (t + 1) * p ^ (t + 1) = p * ∑ t ∈ range k, g (t + 1) * p ^ t := by
      rw [mul_sum]; refine sum_congr rfl fun t _ => by ring
    rw [e, pow_zero, mul_one]
    rcases s with _ | s
    · rw [pow_zero, Nat.div_one, if_pos (Nat.succ_pos k), Nat.add_comm, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (hg 0)]
    · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt (hg 0), zero_add, ih (fun t => g (t + 1)) (fun t => hg _) s]
      simp only [Nat.add_lt_add_iff_right]

lemma digit_extract_be (hp : 1 < p) (k : ℕ) (f : ℕ → ℕ) (hf : ∀ t, f t < p) (s : ℕ) (hs : s < k) :
    (∑ i ∈ range k, f i * p ^ (k - 1 - i)) / p ^ s % p = f (k - 1 - s) := by
  rw [reflect_digits, digit_extract p hp k _ (fun t => hf _) s, if_pos hs]

/-! ## Decomposition of a coordinate -/

variable [NeZero p]

/-- Total digit accessor (as natural numbers). -/
def dv (k : ℕ) (D : Fin (3 * k) → ZMod p) (j : ℕ) : ℕ := if h : j < 3 * k then (D ⟨j, h⟩).val else 0

lemma dv_lt (k : ℕ) (D : Fin (3 * k) → ZMod p) (j : ℕ) : dv p k D j < p := by
  unfold dv; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero p

/-- Tail of the expansion (digits `k+2, …, 3k-1`). -/
def tail (k : ℕ) (D : Fin (3 * k) → ZMod p) : ℕ :=
  ∑ j ∈ Ico (k + 2) (3 * k), dv p k D j * p ^ (3 * k - 1 - j)

lemma tail_lt (k : ℕ) (hk : 1 ≤ k) (D : Fin (3 * k) → ZMod p) : tail p k D < p ^ (2 * k - 2) := by
  unfold tail
  rw [sum_Ico_eq_sum_range, show 3 * k - (k + 2) = 2 * k - 2 by omega]
  have := sum_digits_be_lt p (Nat.pos_of_neZero p) (fun t => dv p k D (k + 2 + t))
    (fun t => dv_lt p k D _) (2 * k - 2)
  convert this using 2 with t ht
  simp only [mem_range] at ht
  rw [show 3 * k - 1 - (k + 2 + t) = 2 * k - 2 - 1 - t by omega]

lemma coord_split (k : ℕ) (hk : 1 ≤ k) (D : Fin (3 * k) → ZMod p) :
    ∑ j : Fin (3 * k), (D j).val * p ^ (3 * k - 1 - (j : ℕ)) =
      p ^ (2 * k) * (∑ i ∈ range k, dv p k D i * p ^ (k - 1 - i)) + p ^ (2 * k - 1) * dv p k D k +
        p ^ (2 * k - 2) * dv p k D (k + 1) + tail p k D := by
  rw [show ∑ j : Fin (3 * k), (D j).val * p ^ (3 * k - 1 - (j : ℕ)) =
      ∑ j : Fin (3 * k), dv p k D j * p ^ (3 * k - 1 - (j : ℕ)) by
        refine sum_congr rfl fun j _ => ?_; simp [dv, j.isLt],
    Fin.sum_univ_eq_sum_range (fun j => dv p k D j * p ^ (3 * k - 1 - j)),
    ← sum_range_add_sum_Ico _ (show k ≤ 3 * k by omega),
    sum_eq_sum_Ico_succ_bot (show k < 3 * k by omega),
    sum_eq_sum_Ico_succ_bot (show k + 1 < 3 * k by omega), tail, mul_sum]
  rw [show 3 * k - 1 - k = 2 * k - 1 by omega, show 3 * k - 1 - (k + 1) = 2 * k - 2 by omega]
  have : ∑ i ∈ range k, dv p k D i * p ^ (3 * k - 1 - i) =
      ∑ i ∈ range k, p ^ (2 * k) * (dv p k D i * p ^ (k - 1 - i)) := by
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    rw [show 3 * k - 1 - i = 2 * k + (k - 1 - i) by omega, pow_add]; ring
  rw [this]; ring

/-! ## Cells and carries -/

/-- Level `i` digit (as a natural number) of the cell of axis `d`. -/
def ad (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) (i : ℕ) : ℕ :=
  if h : i < k then (v (ix k d ⟨i, h⟩)).val else 0

lemma ad_lt (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) (i : ℕ) : ad p k v d i < p := by
  unfold ad; split_ifs
  · exact ZMod.val_lt _
  · exact Nat.pos_of_neZero p

/-- The cell `n_d ∈ [0, p^k)` of axis `d`. -/
def cellN (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) : ℕ :=
  ∑ i ∈ range k, ad p k v d i * p ^ (k - 1 - i)

lemma cellN_lt (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) : cellN p k v d < p ^ k :=
  sum_digits_be_lt p (Nat.pos_of_neZero p) _ (ad_lt p k v d) k

lemma cell_part (k : ℕ) (v : Fin (3 * k) → ZMod p) (c : Fin 3) :
    ∑ i ∈ range k, dv p k (Dg p k c v) i * p ^ (k - 1 - i) = cellN p k v c := by
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  congr 1
  simp only [dv, ad, dif_pos hi, dif_pos (show i < 3 * k by omega)]
  rw [Dg_cell p k c v ⟨i, by omega⟩ hi]

lemma cellN_digit (hp : 1 < p) (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) (l : Fin k) :
    cellN p k v d / p ^ (k - 1 - (l : ℕ)) % p = (v (ix k d l)).val := by
  have hl := l.isLt
  unfold cellN
  rw [digit_extract_be p hp k _ (ad_lt p k v d) _ (by omega), show k - 1 - (k - 1 - (l : ℕ)) = l by omega]
  simp [ad, hl]

lemma zmod_digit (hp : 1 < p) (k : ℕ) (v : Fin (3 * k) → ZMod p) (d : Fin 3) (l : Fin k) :
    v (ix k d l) = ((cellN p k v d / p ^ (k - 1 - (l : ℕ)) : ℕ) : ZMod p) := by
  rw [← ZMod.natCast_mod, cellN_digit p hp, ZMod.natCast_zmod_val]

/-- Equal cells have equal digits. -/
lemma digits_eq_of_cellN_eq (hp : 1 < p) (k : ℕ) (v w : Fin (3 * k) → ZMod p) (d : Fin 3)
    (h : cellN p k w d = cellN p k v d) (l : Fin k) : w (ix k d l) = v (ix k d l) := by
  rw [zmod_digit p hp k w, zmod_digit p hp k v, h]

/-- **Carry lemma.** If the cell of axis `d` steps by `+1` (mod `p^k`), the level-`l` digit changes by
`1` iff `p^(k-1-l)` divides `n + 1`. -/
lemma carry_digits (hp : 1 < p) (k : ℕ) (v w : Fin (3 * k) → ZMod p) (d : Fin 3)
    (h : cellN p k w d = (cellN p k v d + 1) % p ^ k) (l : Fin k) :
    w (ix k d l) - v (ix k d l) =
      if p ^ (k - 1 - (l : ℕ)) ∣ cellN p k v d + 1 then 1 else 0 := by
  have hl := l.isLt
  set s := k - 1 - (l : ℕ) with hs
  have hsk : s < k := by omega
  rw [zmod_digit p hp k w, zmod_digit p hp k v, h, ← hs]
  have e1 : (cellN p k v d + 1) % p ^ k / p ^ s = (cellN p k v d + 1) / p ^ s % p ^ (k - s) := by
    rw [show p ^ k = p ^ s * p ^ (k - s) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self]
  rw [e1, ← ZMod.natCast_mod, Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega)), ZMod.natCast_mod,
    Nat.succ_div]
  split_ifs <;> simp

/-- Carry length (capped at `3`, and `< k`). -/
def Jof (k n : ℕ) : ℕ :=
  if 3 < k ∧ p ^ 3 ∣ n + 1 then 3 else if 2 < k ∧ p ^ 2 ∣ n + 1 then 2
  else if 1 < k ∧ p ∣ n + 1 then 1 else 0

lemma Jof_le (k n : ℕ) : Jof p k n ≤ 3 := by unfold Jof; split_ifs <;> omega

lemma Jof_lt (k n : ℕ) (hk : 1 ≤ k) : Jof p k n < k := by unfold Jof; split_ifs <;> omega

lemma dvd_iff_le_Jof (k n s : ℕ) (hs : s ≤ 3) (hsk : s < k) :
    p ^ s ∣ n + 1 ↔ s ≤ Jof p k n := by
  have d32 : p ^ 3 ∣ n + 1 → p ^ 2 ∣ n + 1 := fun h => (pow_dvd_pow p (by omega)).trans h
  have d21 : p ^ 2 ∣ n + 1 → p ∣ n + 1 := fun h => (dvd_pow_self p (by omega)).trans h
  unfold Jof
  interval_cases s
  · simp
  · simp only [pow_one]; split_ifs <;> simp_all <;> omega
  · split_ifs <;> simp_all <;> omega
  · split_ifs <;> simp_all <;> omega

/-- Per-axis step data: the low levels (`k-1-l ≤ 3`) of the cell of axis `d` change by
`e · [k-1-l ≤ J]`. -/
def AxisStep (k : ℕ) (v w : Fin (3 * k) → ZMod p) (d : Fin 3) (e : ℤ) (J : ℕ) : Prop :=
  ∀ l : Fin k, k - 1 - (l : ℕ) ≤ 3 →
    w (ix k d l) - v (ix k d l) = (e : ZMod p) * (if k - 1 - (l : ℕ) ≤ J then 1 else 0)

lemma axisStep_plus (hp : 1 < p) (k : ℕ) (hk : 1 ≤ k) (v w : Fin (3 * k) → ZMod p) (d : Fin 3)
    (h : cellN p k w d = (cellN p k v d + 1) % p ^ k) :
    AxisStep p k v w d 1 (Jof p k (cellN p k v d)) := by
  intro l hl
  rw [carry_digits p hp k v w d h l]
  have := dvd_iff_le_Jof p k (cellN p k v d) (k - 1 - l) hl (by have := l.isLt; omega)
  by_cases h' : p ^ (k - 1 - (l : ℕ)) ∣ cellN p k v d + 1
  · rw [if_pos h', if_pos (this.mp h')]; simp
  · rw [if_neg h', if_neg (fun h2 => h' (this.mpr h2))]; simp

lemma axisStep_minus (hp : 1 < p) (k : ℕ) (hk : 1 ≤ k) (v w : Fin (3 * k) → ZMod p) (d : Fin 3)
    (h : cellN p k v d = (cellN p k w d + 1) % p ^ k) :
    AxisStep p k v w d (-1) (Jof p k (cellN p k w d)) := by
  intro l hl
  have := axisStep_plus p hp k hk w v d h l hl
  rw [← neg_sub, this]; push_cast; ring

lemma axisStep_zero (hp : 1 < p) (k : ℕ) (v w : Fin (3 * k) → ZMod p) (d : Fin 3)
    (h : cellN p k w d = cellN p k v d) : AxisStep p k v w d 0 0 := by
  intro l _
  rw [digits_eq_of_cellN_eq p hp k v w d h l]; simp

/-! ## Change of the first offset digits -/

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

/-- Change of offset digit `k + r` of coordinate `c` under per-axis steps, when row `r` of the blocks
is given by a table vanishing beyond the last four levels. -/
lemma Dg_off_sub (k : ℕ) (c : Fin 3) (v w : Fin (3 * k) → ZMod p) (r : Fin (2 * k))
    (tab : Fin 3 → ℕ → ℤ) (hΦ : ∀ d l, QPhi k c d r l = tab (d - c) (k - 1 - (l : ℕ)))
    (htab : ∀ rel s, 4 ≤ s → tab rel s = 0) (e : Fin 3 → ℤ) (J : Fin 3 → ℕ)
    (hJk : ∀ d, J d < k) (hstep : ∀ d, AxisStep p k v w d (e d) (J d)) :
    Dg p k c w ⟨k + r, by omega⟩ - Dg p k c v ⟨k + r, by omega⟩ =
      ∑ d : Fin 3, (e d : ZMod p) * ((∑ s ∈ range (J d + 1), tab (d - c) s : ℤ) : ZMod p) := by
  rw [Dg_off, Dg_off, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_sub_distrib, ← sum_tab_indicator _ k (J d) (hJk d)]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [← mul_sub, hΦ]
  by_cases hl : k - 1 - (l : ℕ) ≤ 3
  · rw [hstep d l hl]; ring
  · rw [htab _ _ (by omega)]; simp

lemma tab0_vanish (rel : Fin 3) (s : ℕ) (hs : 4 ≤ s) : tab0 rel s = 0 := by
  unfold tab0 tabB0 tabC0; split_ifs <;> omega

lemma tab1_vanish (rel : Fin 3) (s : ℕ) (hs : 4 ≤ s) : tab1 rel s = 0 := by
  unfold tab1 tabB1 tabC1; split_ifs <;> omega

lemma QPhi_row0' (k : ℕ) (hk : 2 ≤ k) (c d : Fin 3) (l : Fin k) :
    QPhi k c d ⟨0, by omega⟩ l = tab0 (d - c) (k - 1 - (l : ℕ)) := QPhi_row0 k hk c d l

lemma QPhi_row1' (k : ℕ) (hk : 2 ≤ k) (c d : Fin 3) (l : Fin k) :
    QPhi k c d ⟨1, by omega⟩ l = tab1 (d - c) (k - 1 - (l : ℕ)) := QPhi_row1 k hk c d l

/-- If no other axis moves, offset digits `k + r` with `r ≥ 1` of coordinate `c` do not change. -/
lemma Dg_off_eq_of_only (hp : 1 < p) (k : ℕ) (c : Fin 3) (v w : Fin (3 * k) → ZMod p)
    (hother : ∀ d, d ≠ c → cellN p k w d = cellN p k v d) (r : Fin (2 * k)) (hr : (r : ℕ) ≠ 0) :
    Dg p k c w ⟨k + r, by omega⟩ = Dg p k c v ⟨k + r, by omega⟩ := by
  rw [Dg_off, Dg_off]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  by_cases hd : d = c
  · subst hd; rw [show QPhi k d d r l = 0 from QPhi_self_row k d r hr l]; simp
  · rw [digits_eq_of_cellN_eq p hp k v w d (hother d hd) l]

/-! ## Toroidal residues -/

omit [NeZero p] in
lemma cres_add_mul (N : ℕ) (u z : ℤ) : cres N (u + z * N) = cres N u := by
  unfold cres; rw [Int.add_mul_emod_self_right]

omit [NeZero p] in
lemma cres_eq_abs (N : ℕ) (u : ℤ) (h : 2 * |u| ≤ N) : (cres N u : ℤ) = |u| := by
  unfold cres
  rcases lt_trichotomy u 0 with hu | hu | hu
  · rw [abs_of_neg hu] at h ⊢
    have hm : u % (N : ℤ) = u + N := by
      rw [show u = (u + N) + (-1) * N by ring, Int.add_mul_emod_self_right,
        Int.emod_eq_of_lt (by omega) (by omega)]; ring
    rw [hm]
    have : N - (u + N).toNat ≤ (u + N).toNat := by omega
    rw [min_eq_right this]; omega
  · subst hu; simp
  · rw [abs_of_pos hu] at h ⊢
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    have : u.toNat ≤ N - u.toNat := by omega
    rw [min_eq_left this]; omega

omit [NeZero p] in
lemma cres_eq_abs_sub (N : ℕ) (hN : 0 < N) (u : ℤ) : ∃ z : ℤ, (cres N u : ℤ) = |u - z * N| := by
  have h0 := Int.emod_nonneg u (show (N : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos u (show (0 : ℤ) < N by omega)
  have hd := Int.mul_ediv_add_emod u (N : ℤ)
  unfold cres
  rcases le_total (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) with h | h
  · refine ⟨u / N, ?_⟩
    rw [min_eq_left h, abs_of_nonneg (by nlinarith)]
    have : ((u % (N : ℤ)).toNat : ℤ) = u % N := Int.toNat_of_nonneg h0
    rw [this]; linarith
  · refine ⟨u / N + 1, ?_⟩
    rw [min_eq_right h, abs_of_nonpos (by nlinarith)]
    have : ((u % (N : ℤ)).toNat : ℤ) = u % N := Int.toNat_of_nonneg h0
    push_cast [Nat.cast_sub (show (u % (N : ℤ)).toNat ≤ N by omega), this]
    linarith

omit [NeZero p] in
/-- Cell-step trichotomy on `ℤ/Pℤ` (`P ≥ 3`). -/
lemma step_cases (P a b : ℕ) (hP : 3 ≤ P) (ha : a < P) (hb : b < P) :
    b = a ∨ b = (a + 1) % P ∨ a = (b + 1) % P ∨ ∀ z : ℤ, 2 ≤ |(b : ℤ) - a - z * P| := by
  by_cases h0 : b = a; · exact Or.inl h0
  by_cases h1 : b = a + 1; · right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h1
  by_cases h2 : a = b + 1; · right; right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h2
  by_cases h3 : b = 0 ∧ a = P - 1
  · right; left; rw [h3.1, h3.2, Nat.sub_add_cancel (by omega), Nat.mod_self]
  by_cases h4 : a = 0 ∧ b = P - 1
  · right; right; left; rw [h4.1, h4.2, Nat.sub_add_cancel (by omega), Nat.mod_self]
  right; right; right
  intro z
  rw [le_abs]
  rcases lt_trichotomy z 0 with hz | hz | hz
  · rcases eq_or_lt_of_le (show z ≤ -1 by omega) with hz1 | hz1
    · subst hz1; left; omega
    · left; nlinarith
  · subst hz; simp only [zero_mul, sub_zero]; omega
  · rcases eq_or_lt_of_le (show 1 ≤ z by omega) with hz1 | hz1
    · subst hz1; right; omega
    · right; nlinarith

end

end Z3Net.Two

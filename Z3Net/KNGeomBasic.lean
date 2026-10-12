module
public import Mathlib
public import Z3Net.KNDefs

@[expose] public section

/-!
# KN separation, part 1: base-`p` prefixes, centred residues, toroidal lower bound

* `pre p f a = ∑_{j<a} f j · p^(a-1-j)` (big-endian prefix value), defined recursively.
* `cen P x`: centred residue of `x` mod `P` (`2|cen| ≤ P`, `cen ≡ x`).
* `cres_lower`: for `N = M U`, `x = δ U + e + z N`, `2|δ| ≤ M`, `|e| ≤ E`:
  `|δ| U - E ≤ cres N x`.
-/

namespace Z3NetKN.Geom

open Finset

/-- Big-endian prefix value of the digit function `f` (first `a` digits). -/
def pre (p : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | a + 1 => pre p f a * p + f a

@[simp] lemma pre_zero (p : ℕ) (f : ℕ → ℕ) : pre p f 0 = 0 := rfl

lemma pre_succ (p : ℕ) (f : ℕ → ℕ) (a : ℕ) : pre p f (a + 1) = pre p f a * p + f a := rfl

lemma pre_one (p : ℕ) (f : ℕ → ℕ) : pre p f 1 = f 0 := by simp [pre]

lemma pre_two (p : ℕ) (f : ℕ → ℕ) : pre p f 2 = f 0 * p + f 1 := by simp [pre]

lemma pre_eq_sum (p : ℕ) (f : ℕ → ℕ) (a : ℕ) :
    pre p f a = ∑ j ∈ range a, f j * p ^ (a - 1 - j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pre_succ, ih, sum_range_succ, sum_mul]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      simp only [mem_range] at hj
      rw [show a + 1 - 1 - j = (a - 1 - j) + 1 by omega, pow_succ]; ring
    · simp

lemma pre_congr (p : ℕ) (f g : ℕ → ℕ) (a : ℕ) (h : ∀ j < a, f j = g j) : pre p f a = pre p g a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [pre_succ, pre_succ, ih (fun j hj => h j (by omega)), h a (by omega)]

lemma pre_add (p : ℕ) (f : ℕ → ℕ) (a b : ℕ) :
    pre p f (a + b) = pre p f a * p ^ b + pre p (fun j => f (a + j)) b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, pre_succ, ih, pre_succ, pow_succ]; ring

lemma pre_lt (p : ℕ) (_hp : 0 < p) (f : ℕ → ℕ) (a : ℕ) (hf : ∀ j < a, f j < p) :
    pre p f a < p ^ a := by
  induction a with
  | zero => simp [pre]
  | succ a ih =>
    rw [pre_succ, pow_succ]
    have h1 := ih (fun j hj => hf j (by omega))
    have h2 := hf a (by omega)
    have : pre p f a * p + f a < (pre p f a + 1) * p := by nlinarith
    calc pre p f a * p + f a < (pre p f a + 1) * p := this
      _ ≤ p ^ a * p := Nat.mul_le_mul_right _ h1

lemma pre_digit (p : ℕ) (hp : 0 < p) (f : ℕ → ℕ) (a : ℕ) (hf : ∀ j < a, f j < p) (i : ℕ)
    (hi : i < a) : pre p f a / p ^ i % p = f (a - 1 - i) := by
  induction a generalizing i with
  | zero => omega
  | succ a ih =>
    rw [pre_succ]
    rcases i with _ | i
    · rw [pow_zero, Nat.div_one, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (hf a (by omega))]
      simp
    · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_right _ _ hp,
        Nat.div_eq_of_lt (hf a (by omega)), zero_add, ih (fun j hj => hf j (by omega)) i (by omega)]
      congr 1; omega

/-- Equal prefixes have equal digits. -/
lemma pre_inj_digit (p : ℕ) (hp : 0 < p) (f g : ℕ → ℕ) (a : ℕ) (hf : ∀ j < a, f j < p)
    (hg : ∀ j < a, g j < p) (h : pre p f a = pre p g a) (j : ℕ) (hj : j < a) : f j = g j := by
  have e1 := pre_digit p hp f a hf (a - 1 - j) (by omega)
  have e2 := pre_digit p hp g a hg (a - 1 - j) (by omega)
  rw [h, e2, show a - 1 - (a - 1 - j) = j by omega] at e1
  rw [show a - 1 - (a - 1 - j) = j by omega] at e2
  exact e1.symm

/-! ## Centred residues -/

/-- Centred residue of `x` modulo `P`. -/
def cen (P : ℕ) (x : ℤ) : ℤ := if 2 * (x % (P : ℤ)) ≤ P then x % (P : ℤ) else x % (P : ℤ) - P

lemma cen_abs (P : ℕ) (hP : 0 < P) (x : ℤ) : 2 * |cen P x| ≤ P := by
  have h0 := Int.emod_nonneg x (show (P : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < P by omega)
  unfold cen; split_ifs with h
  · rw [abs_of_nonneg h0]; exact h
  · rw [abs_of_neg (by omega)]; omega

lemma cen_spec (P : ℕ) (x : ℤ) : ∃ z : ℤ, x = cen P x + z * P := by
  have hd := Int.mul_ediv_add_emod x (P : ℤ)
  unfold cen; split_ifs
  · exact ⟨x / P, by linarith⟩
  · exact ⟨x / P + 1, by linarith⟩

/-- If `|x| < P`-wise the difference of two numbers in `[0, P)` is `0` mod `P`, they are equal. -/
lemma eq_of_sub_eq_mul (P a b : ℕ) (ha : a < P) (hb : b < P) (z : ℤ)
    (h : (a : ℤ) - b = z * P) : a = b := by
  have : z = 0 := by
    rcases lt_trichotomy z 0 with hz | hz | hz
    · have : z * (P : ℤ) ≤ -P := by nlinarith
      omega
    · exact hz
    · have : (P : ℤ) ≤ z * P := by nlinarith
      omega
  subst this; omega

/-! ## Toroidal residues -/

lemma cres_add_mul' (N : ℕ) (u z : ℤ) : cres N (u + z * N) = cres N u := by
  unfold cres; rw [Int.add_mul_emod_self_right]

lemma cres_eq_abs_sub' (N : ℕ) (hN : 0 < N) (u : ℤ) : ∃ z : ℤ, (cres N u : ℤ) = |u - z * N| := by
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

/-- **Toroidal lower bound.** -/
lemma cres_lower (M U : ℕ) (hM : 0 < M) (hU : 0 < U) (δ e z E : ℤ) (hδ : 2 * |δ| ≤ M)
    (he : |e| ≤ E) : |δ| * U - E ≤ (cres (M * U) (δ * U + e + z * ((M * U : ℕ) : ℤ)) : ℤ) := by
  rw [cres_add_mul']
  obtain ⟨t, ht⟩ := cres_eq_abs_sub' (M * U) (Nat.mul_pos hM hU) (δ * U + e)
  rw [ht]
  push_cast
  have key : |δ| ≤ |δ - t * M| := by
    rcases eq_or_ne t 0 with h | h
    · simp [h]
    · have h1 : (M : ℤ) ≤ |t * M| := by
        rw [abs_mul, abs_of_pos (show (0 : ℤ) < M by omega)]
        have : 1 ≤ |t| := Int.one_le_abs h
        nlinarith
      have h2 : |t * M| ≤ |δ - t * M| + |δ| := by
        calc |t * (M : ℤ)| = |δ - (δ - t * M)| := by ring_nf
          _ ≤ |δ| + |δ - t * M| := abs_sub _ _
          _ = _ := by ring
      linarith
  have e1 : δ * U + e - t * (M * U) = (δ - t * M) * U + e := by ring
  rw [e1]
  have hU' : (0 : ℤ) < U := by omega
  calc |δ| * U - E ≤ |δ - t * M| * U - |e| := by nlinarith
    _ = |(δ - t * M) * U| - |e| := by rw [abs_mul, abs_of_pos hU']
    _ ≤ |(δ - t * M) * U + e| := by
        have := abs_sub_abs_le_abs_sub ((δ - t * M) * U) (-e)
        rw [abs_neg, sub_neg_eq_add] at this; exact this

end Z3NetKN.Geom

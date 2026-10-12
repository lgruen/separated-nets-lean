module
public import Mathlib
public import Z3Net.D4Defs

@[expose] public section

/-!
# 4D entry, part 6: Proposition C (value of the separation relaxation), by reflection

For a cell step `e ∈ {-1,0,1}⁴ \ {0}` with carry classes `J_d ∈ {0,1,2}` (`J_d = min(j_d, 2)`),
the first offset digit of coordinate `i` changes mod `q` by `σ_i = ∑_d e_d P(i,d,J_d)`, where
`P(i,d,J) = F_0[i][d] + … + F_J[i][d]` (Lemma S of the note). The real change of coordinate `i`
in units of `q^(-1)` cells is `e_i q + δ_i + (jitter)`, `δ_i ≡ σ_i (mod q)`, `|δ_i| < q`.

* `checkPoly` enumerates all `2400` configurations `(e, J)` and all `16` choices of the
  representatives `δ_i ∈ {σ_i, σ_i - q sgn σ_i}` and certifies `∑_i x_i² ≥ q² - 10q + 29` for every
  `q ≥ 11` by nonnegative Taylor coefficients at `q = 11` (`max |σ| = 10 < q`).
* `checkSmall q` (`q = 5, 7, 9`) certifies `∑_i x_i² ≥ K4 q` with the exact representative sets
  `δ_i ∈ {σ_i mod q, σ_i mod q - q}`.
* `key_ineq` is the soundness theorem.
-/

namespace Z3NetD4.Proofs

open Finset Z3NetD4

/-! ## The partial sums `P(i,d,J)` -/

/-- `P(i,d,J) = ∑_{l ≤ J} F_l[i][d]`. -/
def PJ (i d : Fin 4) (J : ℕ) : ℤ := ∑ l ∈ range (J + 1), Fdes l i d

/-- Explicit table of `P(i,d,J)` (`J ≤ 2`), for fast kernel evaluation. -/
def PJt (i d J : ℕ) : ℤ :=
  ((([[[-1, -1, -1], [-1, 1, 0], [-1, -1, -1], [-1, -1, -1]],
      [[-2, -4, -4], [-1, -1, -1], [2, 0, 0], [1, 0, -1]],
      [[1, 1, 1], [1, 1, -1], [-1, -1, -1], [-1, 1, 1]],
      [[-2, 0, -1], [-1, 0, 0], [-2, -4, -6], [-1, -1, -1]]] : List (List (List ℤ))).getD i []).getD
    d []).getD J 0

lemma PJ_eq_PJt_aux : ∀ i d : Fin 4, ∀ J : Fin 3, PJ i d J = PJt i d J := by decide

lemma PJ_eq_PJt (i d : Fin 4) (J : ℕ) (hJ : J ≤ 2) : PJ i d J = PJt i d J :=
  PJ_eq_PJt_aux i d ⟨J, by omega⟩

/-- `σ_i = ∑_d e_d P(i,d,J_d)`. -/
def sigt (e0 e1 e2 e3 : ℤ) (J0 J1 J2 J3 : ℕ) (i : ℕ) : ℤ :=
  e0 * PJt i 0 J0 + e1 * PJt i 1 J1 + e2 * PJt i 2 J2 + e3 * PJt i 3 J3

/-! ## Linear and quadratic polynomials in `q` -/

structure L1 where
  a0 : ℤ
  a1 : ℤ

structure Q2 where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ

def L1.eval (p : L1) (q : ℤ) : ℤ := p.a0 + p.a1 * q
def Q2.eval (p : Q2) (q : ℤ) : ℤ := p.c0 + p.c1 * q + p.c2 * q ^ 2

/-- Taylor coefficients at `q = 11` are nonnegative. -/
def L1.nonneg (p : L1) : Bool := 0 ≤ p.a0 + 11 * p.a1 && 0 ≤ p.a1
def Q2.nonneg (p : Q2) : Bool := 0 ≤ p.c0 + 11 * p.c1 + 121 * p.c2 && 0 ≤ p.c1 + 22 * p.c2 && 0 ≤ p.c2

def L1.neg (p : L1) : L1 := ⟨-p.a0, -p.a1⟩
def L1.subOne (p : L1) : L1 := ⟨p.a0 - 1, p.a1⟩
def L1.sq (p : L1) : Q2 := ⟨p.a0 * p.a0, 2 * p.a0 * p.a1, p.a1 * p.a1⟩
def Q2.add (p r : Q2) : Q2 := ⟨p.c0 + r.c0, p.c1 + r.c1, p.c2 + r.c2⟩
def Q2.sub (p r : Q2) : Q2 := ⟨p.c0 - r.c0, p.c1 - r.c1, p.c2 - r.c2⟩
def Q2.zero : Q2 := ⟨0, 0, 0⟩
/-- `q² - 10 q + 29 = (q - 5)² + 4`. -/
def Kq : Q2 := ⟨29, -10, 1⟩

def contribL (L : L1) : Q2 := if L.nonneg then L.sq else Q2.zero

/-- Certified lower bound (a quadratic in `q`) for `x²` given `V = e q + δ` as a linear polynomial;
`only` = no jitter. -/
def contrib (V : L1) (only : Bool) : Q2 :=
  if V.nonneg then contribL (if only then V else V.subOne)
  else if V.neg.nonneg then contribL (if only then V.neg else V.neg.subOne)
  else Q2.zero

/-- `V = e q + δ` with `δ = σ - (a ? q sgn σ : 0)`. -/
def VR (e s : ℤ) (a : Bool) : L1 := ⟨s, e - (if a then Int.sign s else 0)⟩

def onlyB (e0 e1 e2 e3 : ℤ) (i : ℕ) : Bool :=
  if i = 0 then e0 != 0 && e1 == 0 && e2 == 0 && e3 == 0
  else if i = 1 then e1 != 0 && e0 == 0 && e2 == 0 && e3 == 0
  else if i = 2 then e2 != 0 && e0 == 0 && e1 == 0 && e3 == 0
  else e3 != 0 && e0 == 0 && e1 == 0 && e2 == 0

def eAt (e0 e1 e2 e3 : ℤ) (i : ℕ) : ℤ := if i = 0 then e0 else if i = 1 then e1 else if i = 2 then e2 else e3

def contribI (e0 e1 e2 e3 : ℤ) (J0 J1 J2 J3 : ℕ) (i : ℕ) (a : Bool) : Q2 :=
  contrib (VR (eAt e0 e1 e2 e3 i) (sigt e0 e1 e2 e3 J0 J1 J2 J3 i) a) (onlyB e0 e1 e2 e3 i)

def chkPoly (e0 e1 e2 e3 : ℤ) (J0 J1 J2 J3 : ℕ) (a0 a1 a2 a3 : Bool) : Bool :=
  ((((contribI e0 e1 e2 e3 J0 J1 J2 J3 0 a0).add (contribI e0 e1 e2 e3 J0 J1 J2 J3 1 a1)).add
    (contribI e0 e1 e2 e3 J0 J1 J2 J3 2 a2)).add (contribI e0 e1 e2 e3 J0 J1 J2 J3 3 a3)).sub Kq
    |>.nonneg

def eList : List ℤ := [-1, 0, 1]
def jList (e : ℤ) : List ℕ := if e = 0 then [0] else [0, 1, 2]
def bools : List Bool := [false, true]

def checkPolyE (e0 e1 e2 e3 : ℤ) : Bool :=
  (jList e0).all fun J0 => (jList e1).all fun J1 => (jList e2).all fun J2 => (jList e3).all fun J3 =>
    bools.all fun a0 => bools.all fun a1 => bools.all fun a2 => bools.all fun a3 =>
      chkPoly e0 e1 e2 e3 J0 J1 J2 J3 a0 a1 a2 a3

def checkPoly : Bool :=
  eList.all fun e0 => eList.all fun e1 => eList.all fun e2 => eList.all fun e3 =>
    (e0 == 0 && e1 == 0 && e2 == 0 && e3 == 0) || checkPolyE e0 e1 e2 e3

/-! ## Small bases `q = 5, 7, 9` -/

/-- `max(0, |e q + t| - jit)²`. -/
def vsq (q e t : ℤ) (only : Bool) : ℤ :=
  let v := |e * q + t| - (if only then 0 else 1)
  if v ≤ 0 then 0 else v * v

/-- Minimum of `vsq` over the representatives `t ≡ s (mod q)`, `|t| < q`. -/
def minv (q e s : ℤ) (only : Bool) : ℤ :=
  if s % q = 0 then vsq q e 0 only else min (vsq q e (s % q) only) (vsq q e (s % q - q) only)

def K4i (q : ℤ) : ℤ := if q = 5 then 1 else if q = 7 then 5 else (q - 5) ^ 2 + 4

def chkSmall (q : ℤ) (e0 e1 e2 e3 : ℤ) (J0 J1 J2 J3 : ℕ) : Bool :=
  decide (K4i q ≤
    minv q e0 (sigt e0 e1 e2 e3 J0 J1 J2 J3 0) (onlyB e0 e1 e2 e3 0) +
    minv q e1 (sigt e0 e1 e2 e3 J0 J1 J2 J3 1) (onlyB e0 e1 e2 e3 1) +
    minv q e2 (sigt e0 e1 e2 e3 J0 J1 J2 J3 2) (onlyB e0 e1 e2 e3 2) +
    minv q e3 (sigt e0 e1 e2 e3 J0 J1 J2 J3 3) (onlyB e0 e1 e2 e3 3))

def checkSmall (q : ℤ) : Bool :=
  eList.all fun e0 => eList.all fun e1 => eList.all fun e2 => eList.all fun e3 =>
    (e0 == 0 && e1 == 0 && e2 == 0 && e3 == 0) ||
    ((jList e0).all fun J0 => (jList e1).all fun J1 => (jList e2).all fun J2 =>
      (jList e3).all fun J3 => chkSmall q e0 e1 e2 e3 J0 J1 J2 J3)

def checkSigBound : Bool :=
  eList.all fun e0 => eList.all fun e1 => eList.all fun e2 => eList.all fun e3 =>
    (jList e0).all fun J0 => (jList e1).all fun J1 => (jList e2).all fun J2 =>
      (jList e3).all fun J3 => (List.range 4).all fun i => decide (|sigt e0 e1 e2 e3 J0 J1 J2 J3 i| ≤ 10)

/-! ## Soundness -/

lemma L1.nonneg_sound (p : L1) (h : p.nonneg = true) (q : ℤ) (hq : 11 ≤ q) : 0 ≤ p.eval q := by
  simp only [L1.nonneg, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  have e : p.eval q = (p.a0 + 11 * p.a1) + p.a1 * (q - 11) := by simp only [L1.eval]; ring
  rw [e]; have := mul_nonneg h1 (show (0 : ℤ) ≤ q - 11 by omega); linarith

lemma Q2.nonneg_sound (p : Q2) (h : p.nonneg = true) (q : ℤ) (hq : 11 ≤ q) : 0 ≤ p.eval q := by
  simp only [Q2.nonneg, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have e : p.eval q = (p.c0 + 11 * p.c1 + 121 * p.c2) + (p.c1 + 22 * p.c2) * (q - 11) +
      p.c2 * (q - 11) ^ 2 := by simp only [Q2.eval]; ring
  have hs : 0 ≤ q - 11 := by omega
  rw [e]
  have := mul_nonneg h1 hs; have := mul_nonneg h2 (sq_nonneg (q - 11))
  linarith

lemma L1.eval_neg (p : L1) (q : ℤ) : p.neg.eval q = -p.eval q := by simp only [L1.neg, L1.eval]; ring
lemma L1.eval_subOne (p : L1) (q : ℤ) : p.subOne.eval q = p.eval q - 1 := by
  simp only [L1.subOne, L1.eval]; ring
lemma L1.eval_sq (p : L1) (q : ℤ) : p.sq.eval q = (p.eval q) ^ 2 := by
  simp only [L1.sq, Q2.eval, L1.eval]; ring
lemma Q2.eval_add (p r : Q2) (q : ℤ) : (p.add r).eval q = p.eval q + r.eval q := by
  simp only [Q2.add, Q2.eval]; ring
lemma Q2.eval_sub (p r : Q2) (q : ℤ) : (p.sub r).eval q = p.eval q - r.eval q := by
  simp only [Q2.sub, Q2.eval]; ring
lemma Kq_eval (q : ℤ) : Kq.eval q = (q - 5) ^ 2 + 4 := by simp only [Kq, Q2.eval]; ring

lemma contribL_le (L : L1) (q : ℤ) (hq : 11 ≤ q) (x : ℤ) (hx : 0 ≤ x) (hL : L.eval q ≤ x) :
    (contribL L).eval q ≤ x ^ 2 := by
  unfold contribL
  split_ifs with h
  · rw [L1.eval_sq]; exact pow_le_pow_left₀ (L1.nonneg_sound _ h q hq) hL 2
  · simp only [Q2.zero, Q2.eval]; nlinarith

lemma contrib_le (V : L1) (only : Bool) (q : ℤ) (hq : 11 ≤ q) (x : ℤ) (hx : 0 ≤ x)
    (hA : (if only then |V.eval q| else |V.eval q| - 1) ≤ x) : (contrib V only).eval q ≤ x ^ 2 := by
  unfold contrib
  by_cases h1 : V.nonneg = true
  · rw [if_pos h1]
    apply contribL_le _ q hq x hx
    cases only <;> simp only [Bool.false_eq_true, if_false, if_true, L1.eval_subOne] at hA ⊢ <;>
      linarith [le_abs_self (V.eval q)]
  rw [if_neg h1]
  by_cases h2 : V.neg.nonneg = true
  · rw [if_pos h2]
    apply contribL_le _ q hq x hx
    cases only <;> simp only [Bool.false_eq_true, if_false, if_true, L1.eval_subOne, L1.eval_neg]
      at hA ⊢ <;> linarith [neg_le_abs (V.eval q)]
  · rw [if_neg h2]; simp only [Q2.zero, Q2.eval]; nlinarith

/-- Representatives of a residue class in `(-q, q)` when `|σ| < q`. -/
lemma rep_of_modEq (q σ δ : ℤ) (hq : 0 < q) (hσ : |σ| < q) (hδ : |δ| < q) (hmod : δ ≡ σ [ZMOD q]) :
    ∃ a : Bool, δ = σ - (if a then q * Int.sign σ else 0) := by
  obtain ⟨m, hm⟩ := (Int.ModEq.dvd hmod)
  have hs := abs_lt.mp hσ; have hd := abs_lt.mp hδ
  have hm2 : -2 < m ∧ m < 2 := by constructor <;> nlinarith
  have : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  rcases this with rfl | rfl | rfl
  · refine ⟨true, ?_⟩
    have : σ < 0 := by nlinarith
    rw [if_pos rfl, Int.sign_eq_neg_one_of_neg this]; linarith
  · exact ⟨false, by simp; linarith⟩
  · refine ⟨true, ?_⟩
    have : 0 < σ := by nlinarith
    rw [if_pos rfl, Int.sign_eq_one_of_pos this]; linarith

lemma VR_eval (e s : ℤ) (a : Bool) (q : ℤ) :
    (VR e s a).eval q = e * q + (s - (if a then q * Int.sign s else 0)) := by
  simp only [VR, L1.eval]; split_ifs <;> ring

/-- Small `q`: the actual representative is one of the two (or `0`). -/
lemma minv_le (q e s : ℤ) (only : Bool) (hq : 0 < q) (δ : ℤ) (hδ : δ ≡ s [ZMOD q]) (hδq : |δ| < q)
    (x : ℤ) (hx0 : 0 ≤ x) (hx : (if only then |e * q + δ| else |e * q + δ| - 1) ≤ x) :
    minv q e s only ≤ x ^ 2 := by
  have hv : vsq q e δ only ≤ x ^ 2 := by
    have hv' : |e * q + δ| - (if only then 0 else 1) ≤ x := by
      cases only <;> simp only [Bool.false_eq_true, if_false, if_true] at hx ⊢ <;> linarith
    unfold vsq
    simp only
    generalize |e * q + δ| - (if only then 0 else 1) = v at hv' ⊢
    split_ifs with hle
    · positivity
    · nlinarith
  have hd := abs_lt.mp hδq
  have hmod : δ % q = s % q := hδ
  unfold minv
  by_cases h0 : s % q = 0
  · rw [if_pos h0]
    have : δ = 0 := by
      rcases le_or_gt 0 δ with h | h
      · rw [Int.emod_eq_of_lt h hd.2] at hmod; omega
      · have : (δ + q) % q = δ + q := Int.emod_eq_of_lt (by omega) (by omega)
        rw [Int.add_emod_right, hmod, h0] at this; omega
    rw [← this]; exact hv
  · rw [if_neg h0]
    rcases le_or_gt 0 δ with h | h
    · rw [Int.emod_eq_of_lt h hd.2] at hmod
      rw [← hmod]; exact (min_le_left _ _).trans hv
    · have e1 : (δ + q) % q = δ + q := Int.emod_eq_of_lt (by omega) (by omega)
      rw [Int.add_emod_right, hmod] at e1
      rw [show s % q - q = δ by omega]; exact (min_le_right _ _).trans hv

/-! ## From the enumeration to the inequality -/

/-- Normalised carry class (`0` on a still axis). -/
def nz (e : ℤ) (J : ℕ) : ℕ := if e = 0 then 0 else J

lemma unit_cases (e : ℤ) (h : -1 ≤ e ∧ e ≤ 1) : e = -1 ∨ e = 0 ∨ e = 1 := by omega

lemma mem_eList (e : ℤ) (h : -1 ≤ e ∧ e ≤ 1) : e ∈ eList := by
  unfold eList; rcases unit_cases e h with rfl | rfl | rfl <;> simp

lemma nz_mem (e : ℤ) (J : ℕ) (hJ : J ≤ 2) : nz e J ∈ jList e := by
  unfold nz jList; split_ifs <;> simp; omega

lemma mem_bools (b : Bool) : b ∈ bools := by cases b <;> simp [bools]

lemma sig_eq (e : Fin 4 → ℤ) (J : Fin 4 → ℕ) (hJ : ∀ c, J c ≤ 2) (i : Fin 4) :
    ∑ d, e d * PJ i d (J d) = sigt (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1))
      (nz (e 2) (J 2)) (nz (e 3) (J 3)) i := by
  have h : ∀ d, e d * PJ i d (J d) = e d * PJt i d (nz (e d) (J d)) := by
    intro d; unfold nz; split_ifs with h
    · simp [h]
    · rw [PJ_eq_PJt i d (J d) (hJ d)]
  rw [Fin.sum_univ_four, h, h, h, h]
  rfl

lemma eAt_eq (e : Fin 4 → ℤ) (i : Fin 4) : eAt (e 0) (e 1) (e 2) (e 3) i = e i := by
  fin_cases i <;> rfl

lemma onlyB_iff (e : Fin 4 → ℤ) (i : Fin 4) :
    onlyB (e 0) (e 1) (e 2) (e 3) i = true ↔ (e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0) := by
  fin_cases i <;> simp [onlyB, Fin.forall_fin_succ, and_assoc]

lemma chkPoly_of (hc : checkPoly = true) (e0 e1 e2 e3 : ℤ) (h0 : e0 ∈ eList) (h1 : e1 ∈ eList)
    (h2 : e2 ∈ eList) (h3 : e3 ∈ eList) (hne : ¬(e0 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0))
    (J0 J1 J2 J3 : ℕ) (hJ0 : J0 ∈ jList e0) (hJ1 : J1 ∈ jList e1) (hJ2 : J2 ∈ jList e2)
    (hJ3 : J3 ∈ jList e3) (a0 a1 a2 a3 : Bool) :
    chkPoly e0 e1 e2 e3 J0 J1 J2 J3 a0 a1 a2 a3 = true := by
  unfold checkPoly at hc
  simp only [List.all_eq_true] at hc
  have := hc e0 h0 e1 h1 e2 h2 e3 h3
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  rcases this with h | h
  · exact absurd ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩ hne
  · unfold checkPolyE at h
    simp only [List.all_eq_true] at h
    exact h J0 hJ0 J1 hJ1 J2 hJ2 J3 hJ3 a0 (mem_bools _) a1 (mem_bools _) a2 (mem_bools _) a3
      (mem_bools _)

lemma chkSmall_of (q : ℤ) (hc : checkSmall q = true) (e0 e1 e2 e3 : ℤ) (h0 : e0 ∈ eList)
    (h1 : e1 ∈ eList) (h2 : e2 ∈ eList) (h3 : e3 ∈ eList)
    (hne : ¬(e0 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0))
    (J0 J1 J2 J3 : ℕ) (hJ0 : J0 ∈ jList e0) (hJ1 : J1 ∈ jList e1) (hJ2 : J2 ∈ jList e2)
    (hJ3 : J3 ∈ jList e3) : chkSmall q e0 e1 e2 e3 J0 J1 J2 J3 = true := by
  unfold checkSmall at hc
  simp only [List.all_eq_true] at hc
  have := hc e0 h0 e1 h1 e2 h2 e3 h3
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
  rcases this with h | h
  · exact absurd ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩ hne
  · exact h J0 hJ0 J1 hJ1 J2 hJ2 J3 hJ3

lemma sigBound_of (hc : checkSigBound = true) (e0 e1 e2 e3 : ℤ) (h0 : e0 ∈ eList)
    (h1 : e1 ∈ eList) (h2 : e2 ∈ eList) (h3 : e3 ∈ eList)
    (J0 J1 J2 J3 : ℕ) (hJ0 : J0 ∈ jList e0) (hJ1 : J1 ∈ jList e1) (hJ2 : J2 ∈ jList e2)
    (hJ3 : J3 ∈ jList e3) (i : ℕ) (hi : i < 4) : |sigt e0 e1 e2 e3 J0 J1 J2 J3 i| ≤ 10 := by
  unfold checkSigBound at hc
  simp only [List.all_eq_true, decide_eq_true_eq] at hc
  exact hc e0 h0 e1 h1 e2 h2 e3 h3 J0 hJ0 J1 hJ1 J2 hJ2 J3 hJ3 i (List.mem_range.mpr hi)

/-- **Proposition C, soundness.** For every cell step `e ∈ {-1,0,1}⁴ \ {0}` with carry classes
`J ≤ 2`, first-offset-digit changes `δ_i ≡ σ_i (mod q)`, `|δ_i| < q`, and `x_i ≥ 0` bounding
`|e_i q + δ_i|` (minus `1` for the jitter unless only axis `i` moves):
`∑ x_i² ≥ K4(q)` (`q = 5, 7, 9` or `q ≥ 11`). -/
theorem key_ineq (hP : checkPoly = true) (h5 : checkSmall 5 = true) (h7 : checkSmall 7 = true)
    (h9 : checkSmall 9 = true) (hB : checkSigBound = true)
    (q : ℤ) (hq : q = 5 ∨ q = 7 ∨ q = 9 ∨ 11 ≤ q) (e : Fin 4 → ℤ)
    (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0) (J : Fin 4 → ℕ) (hJ : ∀ c, J c ≤ 2)
    (δ x : Fin 4 → ℤ) (hδ : ∀ i, δ i ≡ ∑ d, e d * PJ i d (J d) [ZMOD q] ∧ |δ i| < q)
    (hx0 : ∀ i, 0 ≤ x i)
    (hx : ∀ i, (if (e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0) then |e i * q + δ i|
      else |e i * q + δ i| - 1) ≤ x i) :
    K4i q ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  have hq0 : 0 < q := by omega
  have hm : ∀ c, e c ∈ eList := fun c => mem_eList _ (he c)
  have hJm : ∀ c, nz (e c) (J c) ∈ jList (e c) := fun c => nz_mem _ _ (hJ c)
  have hne' : ¬(e 0 = 0 ∧ e 1 = 0 ∧ e 2 = 0 ∧ e 3 = 0) := by
    rintro ⟨z0, z1, z2, z3⟩
    obtain ⟨c, hc⟩ := hne
    fin_cases c <;> simp_all
  have hsig : ∀ i, δ i ≡ sigt (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1))
      (nz (e 2) (J 2)) (nz (e 3) (J 3)) i [ZMOD q] := fun i => by rw [← sig_eq e J hJ i]; exact (hδ i).1
  have hxi : ∀ i : Fin 4, (if onlyB (e 0) (e 1) (e 2) (e 3) i then
      |eAt (e 0) (e 1) (e 2) (e 3) i * q + δ i| else |eAt (e 0) (e 1) (e 2) (e 3) i * q + δ i| - 1)
        ≤ x i := by
    intro i
    have := hx i
    rw [eAt_eq]
    by_cases ho : onlyB (e 0) (e 1) (e 2) (e 3) i = true
    · rw [if_pos ho]; rw [if_pos ((onlyB_iff e i).mp ho)] at this; exact this
    · rw [if_neg ho]; rw [if_neg (fun h => ho ((onlyB_iff e i).mpr h))] at this; exact this
  by_cases hq11 : 11 ≤ q
  · -- q ≥ 11: polynomial certificate
    have hc : ∀ i : Fin 4, ∃ a : Bool,
        (contribI (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1)) (nz (e 2) (J 2))
          (nz (e 3) (J 3)) i a).eval q ≤ x i ^ 2 := by
      intro i
      have hb := sigBound_of hB _ _ _ _ (hm 0) (hm 1) (hm 2) (hm 3) _ _ _ _ (hJm 0) (hJm 1) (hJm 2)
        (hJm 3) i i.isLt
      obtain ⟨a, ha⟩ := rep_of_modEq q _ (δ i) hq0 (by omega) (hδ i).2 (hsig i)
      refine ⟨a, contrib_le _ _ q hq11 _ (hx0 i) ?_⟩
      rw [VR_eval, ← ha]
      exact hxi i
    obtain ⟨a0, c0⟩ := hc 0
    obtain ⟨a1, c1⟩ := hc 1
    obtain ⟨a2, c2⟩ := hc 2
    obtain ⟨a3, c3⟩ := hc 3
    have c0' : (contribI (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1)) (nz (e 2) (J 2))
        (nz (e 3) (J 3)) 0 a0).eval q ≤ x 0 ^ 2 := c0
    have c1' : (contribI (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1)) (nz (e 2) (J 2))
        (nz (e 3) (J 3)) 1 a1).eval q ≤ x 1 ^ 2 := c1
    have c2' : (contribI (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1)) (nz (e 2) (J 2))
        (nz (e 3) (J 3)) 2 a2).eval q ≤ x 2 ^ 2 := c2
    have c3' : (contribI (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1)) (nz (e 2) (J 2))
        (nz (e 3) (J 3)) 3 a3).eval q ≤ x 3 ^ 2 := c3
    have hchk := chkPoly_of hP _ _ _ _ (hm 0) (hm 1) (hm 2) (hm 3) hne' _ _ _ _ (hJm 0) (hJm 1)
      (hJm 2) (hJm 3) a0 a1 a2 a3
    have := Q2.nonneg_sound _ hchk q hq11
    rw [Q2.eval_sub, Q2.eval_add, Q2.eval_add, Q2.eval_add, Kq_eval] at this
    have hK : K4i q = (q - 5) ^ 2 + 4 := by unfold K4i; rw [if_neg (by omega), if_neg (by omega)]
    rw [hK]
    linarith
  · have hsmall : checkSmall q = true := by
      rcases hq with rfl | rfl | rfl | h
      · exact h5
      · exact h7
      · exact h9
      · omega
    have hchk := chkSmall_of q hsmall _ _ _ _ (hm 0) (hm 1) (hm 2) (hm 3) hne' _ _ _ _
      (hJm 0) (hJm 1) (hJm 2) (hJm 3)
    unfold chkSmall at hchk
    rw [decide_eq_true_eq] at hchk
    have hc : ∀ i : Fin 4, minv q (eAt (e 0) (e 1) (e 2) (e 3) i) (sigt (e 0) (e 1) (e 2) (e 3)
        (nz (e 0) (J 0)) (nz (e 1) (J 1)) (nz (e 2) (J 2)) (nz (e 3) (J 3)) i)
        (onlyB (e 0) (e 1) (e 2) (e 3) i) ≤ x i ^ 2 := fun i =>
      minv_le q _ _ _ hq0 (δ i) (hsig i) (hδ i).2 (x i) (hx0 i) (hxi i)
    have c0 : minv q (e 0) (sigt (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1))
        (nz (e 2) (J 2)) (nz (e 3) (J 3)) 0) (onlyB (e 0) (e 1) (e 2) (e 3) 0) ≤ x 0 ^ 2 := hc 0
    have c1 : minv q (e 1) (sigt (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1))
        (nz (e 2) (J 2)) (nz (e 3) (J 3)) 1) (onlyB (e 0) (e 1) (e 2) (e 3) 1) ≤ x 1 ^ 2 := hc 1
    have c2 : minv q (e 2) (sigt (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1))
        (nz (e 2) (J 2)) (nz (e 3) (J 3)) 2) (onlyB (e 0) (e 1) (e 2) (e 3) 2) ≤ x 2 ^ 2 := hc 2
    have c3 : minv q (e 3) (sigt (e 0) (e 1) (e 2) (e 3) (nz (e 0) (J 0)) (nz (e 1) (J 1))
        (nz (e 2) (J 2)) (nz (e 3) (J 3)) 3) (onlyB (e 0) (e 1) (e 2) (e 3) 3) ≤ x 3 ^ 2 := hc 3
    linarith

end Z3NetD4.Proofs

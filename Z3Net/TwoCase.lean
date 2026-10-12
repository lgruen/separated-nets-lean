module
public import Mathlib
public import Z3Net.Defs
public import Z3Net.TwoRows

@[expose] public section

/-!
# Theorem 2 (`thm:two`), part 3: the case analysis, by reflection

For a cell step `e ∈ {-1,0,1}³ \ {0}` with carry lengths `J_d = min(j_d, 3)`, the first two offset
digits of coordinate `c` change modulo `p` by `σ_c = ∑_d e_d P₀(d-c, J_d)` and
`τ_c = ∑_d e_d P₁(d-c, J_d)` (partial sums of the `cor:rows` table).  The real change in units of
`p^(-2)` cells is `V_c = e_c p² + δ_c p + δ'_c` with `δ ∈ {σ, σ - p sgn σ}`, `δ' ∈ {τ, τ - p sgn τ}`.
`checkAll` enumerates all `728 · 64` configurations and certifies `∑_c a_c² ≥ T(p)` for all `p ≥ 11`
by nonnegativity of the Taylor coefficients at `p = 11`; `checkAll_sound` turns this into the
integer statement `key_ineq`.
-/

namespace Z3Net.Two

open Finset

/-- Partial sums of the row-0 / row-1 tables (`J` = number of extra carried levels, `≤ 3`). -/
def P0 (rel : Fin 3) (J : ℕ) : ℤ := ∑ s ∈ range (J + 1), tab0 rel s
def P1 (rel : Fin 3) (J : ℕ) : ℤ := ∑ s ∈ range (J + 1), tab1 rel s

def sig (e : Fin 3 → ℤ) (J : Fin 3 → ℕ) (c : Fin 3) : ℤ := ∑ d : Fin 3, e d * P0 (d - c) (J d)
def tau' (e : Fin 3 → ℤ) (J : Fin 3 → ℕ) (c : Fin 3) : ℤ := ∑ d : Fin 3, e d * P1 (d - c) (J d)

/-- Quadratic / quartic polynomials in `p` with integer coefficients. -/
structure Q2 where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ

structure Q4 where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  c4 : ℤ

def Q2.eval (q : Q2) (p : ℤ) : ℤ := q.a0 + q.a1 * p + q.a2 * p ^ 2
def Q4.eval (q : Q4) (p : ℤ) : ℤ := q.c0 + q.c1 * p + q.c2 * p ^ 2 + q.c3 * p ^ 3 + q.c4 * p ^ 4

/-- Taylor coefficients at `p = 11` are all nonnegative. -/
def Q2.nonneg (q : Q2) : Bool :=
  0 ≤ q.a0 + 11 * q.a1 + 121 * q.a2 && 0 ≤ q.a1 + 22 * q.a2 && 0 ≤ q.a2

def Q4.nonneg (q : Q4) : Bool :=
  0 ≤ q.c0 + 11 * q.c1 + 121 * q.c2 + 1331 * q.c3 + 14641 * q.c4 &&
  0 ≤ q.c1 + 22 * q.c2 + 363 * q.c3 + 5324 * q.c4 &&
  0 ≤ q.c2 + 33 * q.c3 + 726 * q.c4 &&
  0 ≤ q.c3 + 44 * q.c4 && 0 ≤ q.c4

def Q2.neg (q : Q2) : Q2 := ⟨-q.a0, -q.a1, -q.a2⟩
def Q2.subOne (q : Q2) : Q2 := ⟨q.a0 - 1, q.a1, q.a2⟩
def Q2.sq (q : Q2) : Q4 :=
  ⟨q.a0 * q.a0, 2 * q.a0 * q.a1, q.a1 * q.a1 + 2 * q.a0 * q.a2, 2 * q.a1 * q.a2, q.a2 * q.a2⟩
def Q4.add (q r : Q4) : Q4 := ⟨q.c0 + r.c0, q.c1 + r.c1, q.c2 + r.c2, q.c3 + r.c3, q.c4 + r.c4⟩
def Q4.zero : Q4 := ⟨0, 0, 0, 0, 0⟩
/-- `T(p) = p²(p-1)² + (p-1)² + (p-2)² = p⁴ - 2p³ + 3p² - 6p + 5`. -/
def Tq : Q4 := ⟨5, -6, 3, -2, 1⟩
def Q4.sub (q r : Q4) : Q4 := ⟨q.c0 - r.c0, q.c1 - r.c1, q.c2 - r.c2, q.c3 - r.c3, q.c4 - r.c4⟩

def contribL (L : Q2) : Q4 := if L.nonneg then L.sq else Q4.zero

/-- The certified lower bound for `a_c²` (a quartic in `p`) given `V_c` as a quadratic. -/
def contrib (V : Q2) (only : Bool) : Q4 :=
  if V.nonneg then contribL (if only then V else V.subOne)
  else if V.neg.nonneg then contribL (if only then V.neg else V.neg.subOne)
  else Q4.zero

/-- Closed forms of the partial sums (`J ≤ 3`). -/
def p0n (J : ℕ) : ℤ := if J = 0 then -1 else -2
def p1n (J : ℕ) : ℤ := if J = 0 then 0 else if J = 1 then -1 else if J = 2 then -3 else -5
def p1f (J : ℕ) : ℤ := if J = 0 then 1 else if J = 1 then 0 else if J = 2 then 2 else 0

/-- `σ_c, τ_c` for a coordinate whose own / next / far axes step by `e`, `e₁`, `e₂`. -/
def sigR (e e₁ e₂ : ℤ) (J₁ : ℕ) : ℤ := -e + e₁ * p0n J₁ - e₂
def tauR (e₁ e₂ : ℤ) (J₁ J₂ : ℕ) : ℤ := e₁ * p1n J₁ + e₂ * p1f J₂

/-- `V_c` (as a quadratic in `p`) for representative choices `ε, ε'`. -/
def VR (e s t : ℤ) (ε ε' : Bool) : Q2 :=
  ⟨t, s - (if ε' then Int.sign t else 0), e - (if ε then Int.sign s else 0)⟩

def contribR (e e₁ e₂ : ℤ) (J₁ J₂ : ℕ) (ε ε' : Bool) : Q4 :=
  contrib (VR e (sigR e e₁ e₂ J₁) (tauR e₁ e₂ J₁ J₂) ε ε') (e != 0 && e₁ == 0 && e₂ == 0)

def chkR (e0 e1 e2 : ℤ) (J0 J1 J2 : ℕ) (a0 a1 a2 b0 b1 b2 : Bool) : Bool :=
  (((contribR e0 e1 e2 J1 J2 a0 b0).add (contribR e1 e2 e0 J2 J0 a1 b1)).add
    (contribR e2 e0 e1 J0 J1 a2 b2)).sub Tq |>.nonneg

def jList (e : ℤ) : List ℕ := if e = 0 then [0] else [0, 1, 2, 3]

def bools : List Bool := [false, true]

def checkE (e0 e1 e2 : ℤ) : Bool :=
  (jList e0).all fun J0 => (jList e1).all fun J1 => (jList e2).all fun J2 =>
    bools.all fun a0 => bools.all fun a1 => bools.all fun a2 =>
    bools.all fun b0 => bools.all fun b1 => bools.all fun b2 =>
      chkR e0 e1 e2 J0 J1 J2 a0 a1 a2 b0 b1 b2

def eList : List ℤ := [-1, 0, 1]

def checkAll : Bool :=
  eList.all fun e0 => eList.all fun e1 => eList.all fun e2 =>
    (e0 == 0 && e1 == 0 && e2 == 0) || checkE e0 e1 e2

/-- The kernel-checked enumeration of all `728 · 64` configurations (about 40 s). -/
theorem checkAll_eq : checkAll = true := by decide +kernel

/-! ## Soundness -/

lemma Q2.nonneg_sound (q : Q2) (h : q.nonneg = true) (p : ℤ) (hp : 11 ≤ p) : 0 ≤ q.eval p := by
  simp only [Q2.nonneg, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have e : q.eval p = (q.a0 + 11 * q.a1 + 121 * q.a2) + (q.a1 + 22 * q.a2) * (p - 11) +
      q.a2 * (p - 11) ^ 2 := by simp only [Q2.eval]; ring
  have hs : 0 ≤ p - 11 := by omega
  rw [e]
  have := mul_nonneg h1 hs; have := mul_nonneg h2 (sq_nonneg (p - 11))
  linarith

lemma Q4.nonneg_sound (q : Q4) (h : q.nonneg = true) (p : ℤ) (hp : 11 ≤ p) : 0 ≤ q.eval p := by
  simp only [Q4.nonneg, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  set s := p - 11 with hs_def
  have hs : 0 ≤ s := by omega
  have e : q.eval p = (q.c0 + 11 * q.c1 + 121 * q.c2 + 1331 * q.c3 + 14641 * q.c4) +
      (q.c1 + 22 * q.c2 + 363 * q.c3 + 5324 * q.c4) * s + (q.c2 + 33 * q.c3 + 726 * q.c4) * s ^ 2 +
      (q.c3 + 44 * q.c4) * s ^ 3 + q.c4 * s ^ 4 := by
    simp only [Q4.eval, hs_def]; ring
  rw [e]
  have := mul_nonneg h1 hs; have := mul_nonneg h2 (pow_nonneg hs 2)
  have := mul_nonneg h3 (pow_nonneg hs 3); have := mul_nonneg h4 (pow_nonneg hs 4)
  linarith

lemma Q2.eval_neg (q : Q2) (p : ℤ) : q.neg.eval p = -q.eval p := by
  simp only [Q2.neg, Q2.eval]; ring

lemma Q2.eval_subOne (q : Q2) (p : ℤ) : q.subOne.eval p = q.eval p - 1 := by
  simp only [Q2.subOne, Q2.eval]; ring

lemma Q2.eval_sq (q : Q2) (p : ℤ) : q.sq.eval p = (q.eval p) ^ 2 := by
  simp only [Q2.sq, Q4.eval, Q2.eval]; ring

lemma Q4.eval_add (q r : Q4) (p : ℤ) : (q.add r).eval p = q.eval p + r.eval p := by
  simp only [Q4.add, Q4.eval]; ring

lemma Q4.eval_sub (q r : Q4) (p : ℤ) : (q.sub r).eval p = q.eval p - r.eval p := by
  simp only [Q4.sub, Q4.eval]; ring

lemma Tq_eval (p : ℤ) : Tq.eval p = p ^ 2 * (p - 1) ^ 2 + (p - 1) ^ 2 + (p - 2) ^ 2 := by
  simp only [Tq, Q4.eval]; ring

lemma contribL_le (L : Q2) (p : ℤ) (hp : 11 ≤ p) (a : ℤ) (ha : 0 ≤ a) (hL : L.eval p ≤ a) :
    (contribL L).eval p ≤ a ^ 2 := by
  unfold contribL
  split_ifs with h
  · rw [Q2.eval_sq]; exact pow_le_pow_left₀ (Q2.nonneg_sound _ h p hp) hL 2
  · simp only [Q4.zero, Q4.eval]; nlinarith

/-- The per-coordinate lower bound is sound. -/
lemma contrib_le (V : Q2) (only : Bool) (p : ℤ) (hp : 11 ≤ p) (a : ℤ) (ha : 0 ≤ a)
    (hA : (if only then |V.eval p| else |V.eval p| - 1) ≤ a) : (contrib V only).eval p ≤ a ^ 2 := by
  unfold contrib
  by_cases h1 : V.nonneg = true
  · rw [if_pos h1]
    apply contribL_le _ p hp a ha
    cases only <;> simp only [Bool.false_eq_true, if_false, if_true, Q2.eval_subOne] at hA ⊢ <;>
      linarith [le_abs_self (V.eval p)]
  rw [if_neg h1]
  by_cases h2 : V.neg.nonneg = true
  · rw [if_pos h2]
    apply contribL_le _ p hp a ha
    cases only <;> simp only [Bool.false_eq_true, if_false, if_true, Q2.eval_subOne, Q2.eval_neg]
      at hA ⊢ <;> linarith [neg_le_abs (V.eval p)]
  · rw [if_neg h2]; simp only [Q4.zero, Q4.eval]; nlinarith

lemma VR_eval (e s t : ℤ) (ε ε' : Bool) (p : ℤ) :
    (VR e s t ε ε').eval p =
      e * p ^ 2 + (s - (if ε then p * Int.sign s else 0)) * p + (t - (if ε' then p * Int.sign t else 0)) := by
  simp only [VR, Q2.eval]; split_ifs <;> ring

lemma contribR_eval_le (e e₁ e₂ : ℤ) (J₁ J₂ : ℕ) (ε ε' : Bool) (p : ℤ) (hp : 11 ≤ p) (x : ℤ)
    (hx0 : 0 ≤ x)
    (hx : (if (e != 0 && e₁ == 0 && e₂ == 0) then
        |(VR e (sigR e e₁ e₂ J₁) (tauR e₁ e₂ J₁ J₂) ε ε').eval p|
      else |(VR e (sigR e e₁ e₂ J₁) (tauR e₁ e₂ J₁ J₂) ε ε').eval p| - 1) ≤ x) :
    (contribR e e₁ e₂ J₁ J₂ ε ε').eval p ≤ x ^ 2 :=
  contrib_le _ _ p hp x hx0 hx

lemma chkR_sound (e0 e1 e2 : ℤ) (J0 J1 J2 : ℕ) (a0 a1 a2 b0 b1 b2 : Bool)
    (h : chkR e0 e1 e2 J0 J1 J2 a0 a1 a2 b0 b1 b2 = true) (p : ℤ) (hp : 11 ≤ p) (x0 x1 x2 : ℤ)
    (h0 : (contribR e0 e1 e2 J1 J2 a0 b0).eval p ≤ x0 ^ 2)
    (h1 : (contribR e1 e2 e0 J2 J0 a1 b1).eval p ≤ x1 ^ 2)
    (h2 : (contribR e2 e0 e1 J0 J1 a2 b2).eval p ≤ x2 ^ 2) :
    p ^ 2 * (p - 1) ^ 2 + (p - 1) ^ 2 + (p - 2) ^ 2 ≤ x0 ^ 2 + x1 ^ 2 + x2 ^ 2 := by
  have := Q4.nonneg_sound _ h p hp
  rw [Q4.eval_sub, Q4.eval_add, Q4.eval_add, Tq_eval] at this
  linarith

/-- Representatives of a residue class in `(-p, p)`. -/
lemma rep_of_modEq (p σ δ : ℤ) (hp : 0 < p) (hσ : |σ| < p) (hδ : |δ| < p) (hmod : δ ≡ σ [ZMOD p]) :
    ∃ a : Bool, δ = σ - (if a then p * Int.sign σ else 0) := by
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

lemma p0n_bound (J : ℕ) : -2 ≤ p0n J ∧ p0n J ≤ -1 := by unfold p0n; split_ifs <;> omega
lemma p1n_bound (J : ℕ) : -5 ≤ p1n J ∧ p1n J ≤ 0 := by unfold p1n; split_ifs <;> omega
lemma p1f_bound (J : ℕ) : 0 ≤ p1f J ∧ p1f J ≤ 2 := by unfold p1f; split_ifs <;> omega

lemma unit_cases (e : ℤ) (h : -1 ≤ e ∧ e ≤ 1) : e = -1 ∨ e = 0 ∨ e = 1 := by omega

lemma sigR_bound (e e₁ e₂ : ℤ) (J₁ : ℕ) (he : -1 ≤ e ∧ e ≤ 1) (he₁ : -1 ≤ e₁ ∧ e₁ ≤ 1)
    (he₂ : -1 ≤ e₂ ∧ e₂ ≤ 1) : |sigR e e₁ e₂ J₁| ≤ 4 := by
  have := p0n_bound J₁
  unfold sigR; rw [abs_le]
  rcases unit_cases e₁ he₁ with rfl | rfl | rfl <;> constructor <;> linarith [he.1, he.2, he₂.1, he₂.2]

lemma tauR_bound (e₁ e₂ : ℤ) (J₁ J₂ : ℕ) (he₁ : -1 ≤ e₁ ∧ e₁ ≤ 1) (he₂ : -1 ≤ e₂ ∧ e₂ ≤ 1) :
    |tauR e₁ e₂ J₁ J₂| ≤ 7 := by
  have := p1n_bound J₁; have := p1f_bound J₂
  unfold tauR; rw [abs_le]
  rcases unit_cases e₁ he₁ with rfl | rfl | rfl <;> rcases unit_cases e₂ he₂ with rfl | rfl | rfl <;>
    constructor <;> linarith

/-- Normalizing the carry length of a still axis. -/
def nz (e : ℤ) (J : ℕ) : ℕ := if e = 0 then 0 else J

lemma sigR_nz (e e₁ e₂ : ℤ) (J₁ : ℕ) : sigR e e₁ e₂ (nz e₁ J₁) = sigR e e₁ e₂ J₁ := by
  unfold sigR nz; split_ifs with h <;> simp [h]

lemma tauR_nz (e₁ e₂ : ℤ) (J₁ J₂ : ℕ) : tauR e₁ e₂ (nz e₁ J₁) (nz e₂ J₂) = tauR e₁ e₂ J₁ J₂ := by
  unfold tauR nz; split_ifs with h1 h2 h2 <;> simp [h1, h2]

lemma nz_mem (e : ℤ) (J : ℕ) (hJ : J ≤ 3) : nz e J ∈ jList e := by
  unfold nz jList; split_ifs <;> simp; omega

lemma mem_eList (e : ℤ) (h : -1 ≤ e ∧ e ≤ 1) : e ∈ eList := by
  unfold eList; rcases unit_cases e h with rfl | rfl | rfl <;> simp

lemma chkR_of_checkAll (hc : checkAll = true) (e0 e1 e2 : ℤ) (h0 : e0 ∈ eList) (h1 : e1 ∈ eList)
    (h2 : e2 ∈ eList) (hne : ¬(e0 = 0 ∧ e1 = 0 ∧ e2 = 0)) (J0 J1 J2 : ℕ) (hJ0 : J0 ∈ jList e0)
    (hJ1 : J1 ∈ jList e1) (hJ2 : J2 ∈ jList e2) (a0 a1 a2 b0 b1 b2 : Bool) :
    chkR e0 e1 e2 J0 J1 J2 a0 a1 a2 b0 b1 b2 = true := by
  have hb : ∀ b : Bool, b ∈ bools := fun b => by cases b <;> simp [bools]
  unfold checkAll at hc
  simp only [List.all_eq_true] at hc
  have := hc e0 h0 e1 h1 e2 h2
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  rcases this with h | h
  · exact absurd ⟨h.1.1, h.1.2, h.2⟩ hne
  · unfold checkE at h
    simp only [List.all_eq_true] at h
    exact h J0 hJ0 J1 hJ1 J2 hJ2 a0 (hb _) a1 (hb _) a2 (hb _) b0 (hb _) b1 (hb _) b2 (hb _)

lemma coord_bound (p : ℤ) (hp : 11 ≤ p) (e e₁ e₂ : ℤ) (he : -1 ≤ e ∧ e ≤ 1)
    (he₁ : -1 ≤ e₁ ∧ e₁ ≤ 1) (he₂ : -1 ≤ e₂ ∧ e₂ ≤ 1) (J₁ J₂ : ℕ) (δ δ' x : ℤ)
    (hδ : δ ≡ sigR e e₁ e₂ J₁ [ZMOD p] ∧ |δ| < p) (hδ' : δ' ≡ tauR e₁ e₂ J₁ J₂ [ZMOD p] ∧ |δ'| < p)
    (hx0 : 0 ≤ x)
    (hx : (if e ≠ 0 ∧ e₁ = 0 ∧ e₂ = 0 then |e * p ^ 2 + δ * p + δ'| else
      |e * p ^ 2 + δ * p + δ'| - 1) ≤ x) :
    ∃ a b : Bool, (contribR e e₁ e₂ (nz e₁ J₁) (nz e₂ J₂) a b).eval p ≤ x ^ 2 := by
  obtain ⟨a, ha⟩ := rep_of_modEq p _ δ (by omega)
    (lt_of_le_of_lt (sigR_bound e e₁ e₂ J₁ he he₁ he₂) (by omega)) hδ.2 hδ.1
  obtain ⟨b, hb⟩ := rep_of_modEq p _ δ' (by omega)
    (lt_of_le_of_lt (tauR_bound e₁ e₂ J₁ J₂ he₁ he₂) (by omega)) hδ'.2 hδ'.1
  refine ⟨a, b, contribR_eval_le _ _ _ _ _ _ _ p hp x hx0 ?_⟩
  rw [sigR_nz, tauR_nz, VR_eval, ← ha, ← hb]
  convert hx using 2
  simp [bne_iff_ne, and_assoc]

/-- **The case analysis of `thm:two`** (integer form, all `p ≥ 11`): for every cell step
`e ∈ {-1,0,1}³ \ {0}` with carry lengths `J ≤ 3`, offset-digit changes `δ, δ'` in the residue classes
`σ, τ` (representatives in `(-p, p)`) and `x_c ≥ 0` bounding `|V_c|` (minus `1` for the jitter
unless only axis `c` moves), `∑ x_c² ≥ T(p) = p²(p-1)² + (p-1)² + (p-2)²`. -/
theorem key_ineq (hc : checkAll = true) (p : ℤ) (hp : 11 ≤ p) (e : Fin 3 → ℤ)
    (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0) (J : Fin 3 → ℕ) (hJ : ∀ c, J c ≤ 3)
    (δ δ' x : Fin 3 → ℤ)
    (hδ : ∀ c, δ c ≡ sigR (e c) (e (c + 1)) (e (c + 2)) (J (c + 1)) [ZMOD p] ∧ |δ c| < p)
    (hδ' : ∀ c, δ' c ≡ tauR (e (c + 1)) (e (c + 2)) (J (c + 1)) (J (c + 2)) [ZMOD p] ∧ |δ' c| < p)
    (hx0 : ∀ c, 0 ≤ x c)
    (hx : ∀ c, (if e c ≠ 0 ∧ e (c + 1) = 0 ∧ e (c + 2) = 0 then |e c * p ^ 2 + δ c * p + δ' c|
      else |e c * p ^ 2 + δ c * p + δ' c| - 1) ≤ x c) :
    p ^ 2 * (p - 1) ^ 2 + (p - 1) ^ 2 + (p - 2) ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  have f1 : (0 : Fin 3) + 1 = 1 := rfl
  have f2 : (0 : Fin 3) + 2 = 2 := rfl
  have f3 : (1 : Fin 3) + 1 = 2 := rfl
  have f4 : (1 : Fin 3) + 2 = 0 := rfl
  have f5 : (2 : Fin 3) + 1 = 0 := rfl
  have f6 : (2 : Fin 3) + 2 = 1 := rfl
  have hδ0 := hδ 0; have hδ1 := hδ 1; have hδ2 := hδ 2
  have hδ'0 := hδ' 0; have hδ'1 := hδ' 1; have hδ'2 := hδ' 2
  have hx_0 := hx 0; have hx_1 := hx 1; have hx_2 := hx 2
  simp only [f1, f2, f3, f4, f5, f6] at hδ0 hδ1 hδ2 hδ'0 hδ'1 hδ'2 hx_0 hx_1 hx_2
  obtain ⟨a0, b0, h0⟩ := coord_bound p hp _ _ _ (he 0) (he 1) (he 2) _ _ _ _ _ hδ0 hδ'0 (hx0 0) hx_0
  obtain ⟨a1, b1, h1⟩ := coord_bound p hp _ _ _ (he 1) (he 2) (he 0) _ _ _ _ _ hδ1 hδ'1 (hx0 1) hx_1
  obtain ⟨a2, b2, h2⟩ := coord_bound p hp _ _ _ (he 2) (he 0) (he 1) _ _ _ _ _ hδ2 hδ'2 (hx0 2) hx_2
  refine chkR_sound (e 0) (e 1) (e 2) (nz (e 0) (J 0)) (nz (e 1) (J 1)) (nz (e 2) (J 2))
    a0 a1 a2 b0 b1 b2 ?_ p hp _ _ _ h0 h1 h2
  refine chkR_of_checkAll hc _ _ _ (mem_eList _ (he 0)) (mem_eList _ (he 1)) (mem_eList _ (he 2)) ?_
    _ _ _ (nz_mem _ _ (hJ 0)) (nz_mem _ _ (hJ 1)) (nz_mem _ _ (hJ 2)) _ _ _ _ _ _
  obtain ⟨c, hc⟩ := hne
  intro ⟨z0, z1, z2⟩
  fin_cases c <;> simp_all

end Z3Net.Two

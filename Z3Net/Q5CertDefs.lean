/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.R2Sep
public import Z3Net.HalfCertSound
public import Z3Net.HalfCertDet

@[expose] public section

/-!
# V14 stage S11′: `prop:half5`, the checkers

All doubled and in exact integer arithmetic (kernel `decide`; no `native_decide`).
* `bR2c`, `bHkc`: `2b_c` of `lem:R2` and of `prop:Hk`(1) at `k = 1` as functions of `E_c`, `2β_c`, `v_c`
  (`bR2_eq`, `bOpt2_eq`); `bR2s`, `bHks` the monotone lower bounds `LB₂*`, `LB*` of the text after `lem:R2` and
  `prop:Hk` (each option `|α q² + β' q + v| − 1` replaced by `|α| q² − |β'| q − |v| − 1`; `bR2s_le`, `bHks_le`),
  which satisfy `P² bR2s(q) ≥ q² bR2s(P)`, `P bHks(q) ≥ q bHks(P)` for `q ≥ P` (`bR2s_mono`, `bHks_mono`).
* `okR2 p T e`, `okHk p T e`: `T < ∑_c (2b_c)²` at the step `e` (linear forms of `F₀*`, `D₁` written out),
  `chkR2`, `chkHk` over `{-2, …, 2}⁴` for a fixed `e₀`; the same for the starred bounds (`okR2s`, `okHks`) and the
  `p`-free `λ` check (`okLam`); soundness `r2_of_chk`, `hk_of_chk`, `r2s_of_chk`, `hks_of_chk`, `lam_of_chk`.
* `chkDetQ`: the `126` integer box determinants of `𝒬*` (layer row doubled) divide `360 = 2³·3²·5`.
-/

namespace Z3NetHL.Proofs.Q5

open Finset Z3NetHL Z3NetHL.Proofs

set_option maxRecDepth 100000

/-! ## The options as functions of `(E_c, 2β_c, v_c)` -/

/-- `2b_c` of `lem:R2` (`b = 2β_c`, `v = (D₁E)_c`). -/
def bR2c (q : ℕ) (odd : Bool) (e b v : ℤ) : ℤ :=
  if odd then
    min (min (oR2 q e (b + q) v) (oR2 q e (b + q) (v - q * Int.sign v)))
      (min (oR2 q e (b - q) v) (oR2 q e (b - q) (v - q * Int.sign v)))
  else
    min (min (oR2 q e b v) (oR2 q e b (v - q * Int.sign v)))
      (min (oR2 q e (b - 2 * q * Int.sign b) v) (oR2 q e (b - 2 * q * Int.sign b) (v - q * Int.sign v)))

lemma bR2_eq {s : ℕ} (q : ℕ) (F2 D1 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) :
    bR2 q F2 D1 E c = bR2c q (decide ((∑ d, E d) % 2 = 1)) (E c) (dotR F2 E c) (dotR D1 E c) := by
  unfold bR2 bR2c
  by_cases h : (∑ d, E d) % 2 = 1
  · rw [if_pos h, if_pos (decide_eq_true h)]
  · rw [if_neg h, if_neg (by simpa using h)]

/-- `2b_c` of `prop:Hk`(1) at `k = 1` (`b = 2β_c`). -/
def bHkc (q : ℕ) (odd : Bool) (e b : ℤ) : ℤ :=
  if odd then min (max 0 (|2 * (q : ℤ) * e + b + q| - 2)) (max 0 (|2 * (q : ℤ) * e + b - q| - 2))
  else min (max 0 (|2 * (q : ℤ) * e + b| - 2)) (max 0 (|2 * (q : ℤ) * e + b - 2 * q * Int.sign b| - 2))

lemma bOpt2_eq {s : ℕ} (q : ℕ) (F2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) :
    bOpt2 q (fun _ => F2) E (fun _ => 0) c = bHkc q (decide ((∑ d, E d) % 2 = 1)) (E c) (dotR F2 E c) := by
  unfold bOpt2 bHkc
  rw [sig2_k1]
  by_cases h : (∑ d, E d) % 2 = 1
  · rw [if_pos h, if_pos (decide_eq_true h)]
  · rw [if_neg h, if_neg (by simpa using h)]

/-! ## The monotone lower bounds -/

/-- One starred option of `lem:R2`: `max(0, A q² − B q − C)`. -/
def gR2 (q : ℕ) (A B C : ℤ) : ℤ := max 0 (A * (q : ℤ) ^ 2 - B * q - C)

/-- `2b_c*` (the bound `LB₂*` after `lem:R2`): every option `|q²(2E_c + κ) + q(b + μ) + 2v| − 2` replaced by
`|2E_c + κ| q² − |b + μ| q − 2|v| − 2`. -/
def bR2s (q : ℕ) (odd : Bool) (e b v : ℤ) : ℤ :=
  if odd then
    min (min (gR2 q |2 * e + 1| |b| (2 * |v| + 2)) (gR2 q |2 * e + 1| |b - 2 * Int.sign v| (2 * |v| + 2)))
      (min (gR2 q |2 * e - 1| |b| (2 * |v| + 2)) (gR2 q |2 * e - 1| |b - 2 * Int.sign v| (2 * |v| + 2)))
  else
    min (min (gR2 q |2 * e| |b| (2 * |v| + 2)) (gR2 q |2 * e| |b - 2 * Int.sign v| (2 * |v| + 2)))
      (min (gR2 q |2 * e - 2 * Int.sign b| |b| (2 * |v| + 2))
        (gR2 q |2 * e - 2 * Int.sign b| |b - 2 * Int.sign v| (2 * |v| + 2)))

lemma opt_ge (q : ℕ) (e t2 u b v κ μ : ℤ) (ht : t2 = b + q * κ) (hu : 2 * u = 2 * v + q * μ) :
    gR2 q |2 * e + κ| |b + μ| (2 * |v| + 2) ≤ oR2 q e t2 u := by
  unfold gR2 oR2
  have e1 : 2 * (q : ℤ) ^ 2 * e + q * t2 + 2 * u = (q : ℤ) ^ 2 * (2 * e + κ) + (q * (b + μ) + 2 * v) := by
    rw [ht]; linear_combination hu
  rw [e1]
  have h7 := abs_add_le (q * (b + μ)) (2 * v)
  have h8 := abs_sub_abs_le_abs_sub ((q : ℤ) ^ 2 * (2 * e + κ)) (-(q * (b + μ) + 2 * v))
  rw [sub_neg_eq_add, abs_neg] at h8
  have h3 : |(q : ℤ) ^ 2 * (2 * e + κ)| = |2 * e + κ| * (q : ℤ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]; ring
  have h4 : |(q : ℤ) * (b + μ)| = |b + μ| * q := by rw [abs_mul, abs_of_nonneg (by positivity)]; ring
  have h5 : |(2 : ℤ) * v| = 2 * |v| := by rw [abs_mul]; norm_num
  rw [h3] at h8; rw [h4, h5] at h7
  exact max_le_max le_rfl (by linarith)

lemma bR2s_le (q : ℕ) (odd : Bool) (e b v : ℤ) : bR2s q odd e b v ≤ bR2c q odd e b v := by
  have hu1 : 2 * v = 2 * v + q * 0 := by ring
  have hu2 : 2 * (v - q * Int.sign v) = 2 * v + q * (-2 * Int.sign v) := by ring
  have e2 : b - 2 * Int.sign v = b + -2 * Int.sign v := by ring
  unfold bR2s bR2c
  cases odd
  · simp only [Bool.false_eq_true, ite_false]
    have k1 : b = b + q * 0 := by ring
    have k2 : b - 2 * q * Int.sign b = b + q * (-2 * Int.sign b) := by ring
    have a1 := opt_ge q e b v b v 0 0 k1 hu1
    have a2 := opt_ge q e b (v - q * Int.sign v) b v 0 _ k1 hu2
    have a3 := opt_ge q e _ v b v _ 0 k2 hu1
    have a4 := opt_ge q e _ (v - q * Int.sign v) b v _ _ k2 hu2
    simp only [add_zero, mul_zero] at a1 a2 a3 a4
    rw [e2]
    rw [show 2 * e - 2 * Int.sign b = 2 * e + -2 * Int.sign b by ring]
    exact min_le_min (min_le_min a1 a2) (min_le_min a3 a4)
  · simp only [ite_true]
    have k1 : b + q = b + q * 1 := by ring
    have k2 : b - q = b + q * (-1) := by ring
    have a1 := opt_ge q e _ v b v _ 0 k1 hu1
    have a2 := opt_ge q e _ (v - q * Int.sign v) b v _ _ k1 hu2
    have a3 := opt_ge q e _ v b v _ 0 k2 hu1
    have a4 := opt_ge q e _ (v - q * Int.sign v) b v _ _ k2 hu2
    simp only [add_zero, mul_zero] at a1 a2 a3 a4
    rw [e2, show 2 * e - 1 = 2 * e + -1 by ring]
    exact min_le_min (min_le_min a1 a2) (min_le_min a3 a4)

lemma gR2_mono (P q : ℕ) (hP : 1 ≤ P) (hPq : P ≤ q) (A B C : ℤ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (q : ℤ) ^ 2 * gR2 P A B C ≤ (P : ℤ) ^ 2 * gR2 q A B C := by
  unfold gR2
  have hP' : (1 : ℤ) ≤ P := by exact_mod_cast hP
  have hPq' : (P : ℤ) ≤ q := by exact_mod_cast hPq
  rcases le_total (A * (P : ℤ) ^ 2 - B * P - C) 0 with h | h
  · rw [max_eq_left h, mul_zero]
    exact mul_nonneg (by positivity) (le_max_left _ _)
  · rw [max_eq_right h]
    have key : (q : ℤ) ^ 2 * (A * (P : ℤ) ^ 2 - B * P - C) ≤ (P : ℤ) ^ 2 * (A * (q : ℤ) ^ 2 - B * q - C) := by
      have : (P : ℤ) ^ 2 * (A * (q : ℤ) ^ 2 - B * q - C) - (q : ℤ) ^ 2 * (A * (P : ℤ) ^ 2 - B * P - C) =
          B * P * q * (q - P) + C * (q - P) * (q + P) := by ring
      have h1 : 0 ≤ B * P * q * (q - P) := by
        apply mul_nonneg (mul_nonneg (mul_nonneg hB (by linarith)) (by linarith)) (by linarith)
      have h2 : 0 ≤ C * (q - P) * (q + P) := mul_nonneg (mul_nonneg hC (by linarith)) (by linarith)
      linarith
    exact key.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))

lemma min_mono {k l x y x' y' : ℤ} (hk : 0 ≤ k) (hl : 0 ≤ l) (hx : l * x' ≤ k * x) (hy : l * y' ≤ k * y) :
    l * min x' y' ≤ k * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hl).trans hx
  · rw [min_eq_right h]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hl).trans hy

lemma bR2s_mono (P q : ℕ) (hP : 1 ≤ P) (hPq : P ≤ q) (odd : Bool) (e b v : ℤ) :
    (q : ℤ) ^ 2 * bR2s P odd e b v ≤ (P : ℤ) ^ 2 * bR2s q odd e b v := by
  have g := fun x y : ℤ => gR2_mono P q hP hPq |x| |y| (2 * |v| + 2) (abs_nonneg x) (abs_nonneg y) (by positivity)
  have hk : (0 : ℤ) ≤ (P : ℤ) ^ 2 := by positivity
  have hl : (0 : ℤ) ≤ (q : ℤ) ^ 2 := by positivity
  unfold bR2s
  split_ifs <;> exact min_mono hk hl (min_mono hk hl (g _ _) (g _ _)) (min_mono hk hl (g _ _) (g _ _))

lemma gR2_nonneg (q : ℕ) (A B C : ℤ) : 0 ≤ gR2 q A B C := le_max_left _ _

lemma bR2s_nonneg (q : ℕ) (odd : Bool) (e b v : ℤ) : 0 ≤ bR2s q odd e b v := by
  unfold bR2s
  split_ifs <;> exact le_min (le_min (gR2_nonneg _ _ _ _) (gR2_nonneg _ _ _ _))
    (le_min (gR2_nonneg _ _ _ _) (gR2_nonneg _ _ _ _))

/-- One starred option of `prop:Hk`(1): `max(0, A q − B)`. -/
def gHk (q : ℕ) (A B : ℤ) : ℤ := max 0 (A * q - B)

/-- `2b_c*` of `prop:Hk`(1) at `k = 1` (the bound `LB*` after `prop:Hk`). -/
def bHks (q : ℕ) (odd : Bool) (e b : ℤ) : ℤ :=
  if odd then min (gHk q |2 * e + 1| (|b| + 2)) (gHk q |2 * e - 1| (|b| + 2))
  else min (gHk q |2 * e| (|b| + 2)) (gHk q |2 * e - 2 * Int.sign b| (|b| + 2))

lemma optHk_ge (q : ℕ) (e b κ : ℤ) :
    gHk q |2 * e + κ| (|b| + 2) ≤ max 0 (|2 * (q : ℤ) * e + b + q * κ| - 2) := by
  unfold gHk
  have e1 : 2 * (q : ℤ) * e + b + q * κ = (q : ℤ) * (2 * e + κ) + b := by ring
  rw [e1]
  have h8 := abs_sub_abs_le_abs_sub ((q : ℤ) * (2 * e + κ)) (-b)
  rw [sub_neg_eq_add, abs_neg] at h8
  have h3 : |(q : ℤ) * (2 * e + κ)| = |2 * e + κ| * q := by rw [abs_mul, abs_of_nonneg (by positivity)]; ring
  rw [h3] at h8
  exact max_le_max le_rfl (by linarith)

lemma bHks_le (q : ℕ) (odd : Bool) (e b : ℤ) : bHks q odd e b ≤ bHkc q odd e b := by
  unfold bHks bHkc
  cases odd
  · simp only [Bool.false_eq_true, ite_false]
    have a1 := optHk_ge q e b 0
    have a2 := optHk_ge q e b (-2 * Int.sign b)
    simp only [add_zero, mul_zero] at a1
    rw [show 2 * (q : ℤ) * e + b + q * (-2 * Int.sign b) = 2 * q * e + b - 2 * q * Int.sign b by ring] at a2
    rw [show 2 * e - 2 * Int.sign b = 2 * e + -2 * Int.sign b by ring]
    exact min_le_min a1 a2
  · simp only [ite_true]
    have a1 := optHk_ge q e b 1
    have a2 := optHk_ge q e b (-1)
    rw [mul_one] at a1
    rw [show 2 * (q : ℤ) * e + b + q * -1 = 2 * q * e + b - q by ring] at a2
    rw [show 2 * e - 1 = 2 * e + -1 by ring]
    exact min_le_min a1 a2

lemma gHk_mono (P q : ℕ) (hPq : P ≤ q) (A B : ℤ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (q : ℤ) * gHk P A B ≤ (P : ℤ) * gHk q A B := by
  unfold gHk
  have hPq' : (P : ℤ) ≤ q := by exact_mod_cast hPq
  have hP0 : (0 : ℤ) ≤ P := by positivity
  rcases le_total (A * (P : ℤ) - B) 0 with h | h
  · rw [max_eq_left h, mul_zero]
    exact mul_nonneg hP0 (le_max_left _ _)
  · rw [max_eq_right h]
    have : (q : ℤ) * (A * P - B) ≤ P * (A * q - B) := by nlinarith
    exact this.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hP0)

lemma bHks_mono (P q : ℕ) (hPq : P ≤ q) (odd : Bool) (e b : ℤ) :
    (q : ℤ) * bHks P odd e b ≤ (P : ℤ) * bHks q odd e b := by
  have g := fun x : ℤ => gHk_mono P q hPq |x| (|b| + 2) (abs_nonneg x) (by positivity)
  have hk : (0 : ℤ) ≤ (P : ℤ) := by positivity
  have hl : (0 : ℤ) ≤ (q : ℤ) := by positivity
  unfold bHks
  split_ifs <;> exact min_mono hk hl (g _) (g _)

lemma bHks_nonneg (q : ℕ) (odd : Bool) (e b : ℤ) : 0 ≤ bHks q odd e b := by
  unfold bHks; split_ifs <;> exact le_min (le_max_left _ _) (le_max_left _ _)

/-! ## The linear forms of `2F₀*` and `D₁` -/

/-- `(2F₀* e)_c`. -/
def fF (c : ℕ) (e0 e1 e2 e3 e4 : ℤ) : ℤ :=
  match c with
  | 0 => (-3) * e0 + (-3) * e1 + (-3) * e2 + (-1) * e3 + (-1) * e4
  | 1 => (3) * e0 + (-3) * e1 + (-1) * e2 + (-3) * e3 + (1) * e4
  | 2 => (3) * e0 + (1) * e1 + (-3) * e2 + (1) * e3 + (-1) * e4
  | 3 => (1) * e0 + (3) * e1 + (-1) * e2 + (-3) * e3 + (-1) * e4
  | _ => (1) * e0 + (-1) * e1 + (1) * e2 + (1) * e3 + (-1) * e4

/-- `(D₁ e)_c`. -/
def fD (c : ℕ) (e0 e1 e2 e3 e4 : ℤ) : ℤ :=
  match c with
  | 0 => (-2) * e0 + (-1) * e2 + (-1) * e3 + (1) * e4
  | 1 => (-1) * e1 + (-1) * e2 + (-1) * e3 + (-1) * e4
  | 2 => (2) * e0 + (-1) * e1 + (-3) * e2 + (1) * e3
  | 3 => (-1) * e0 + (2) * e1 + (-1) * e2 + (-2) * e3
  | _ => (-1) * e0 + (-1) * e1 + (3) * e2 + (2) * e3 + (-5) * e4

lemma dotF (E : Fin 5 → ℤ) (c : Fin 5) : dotR F2star E c = fF c (E 0) (E 1) (E 2) (E 3) (E 4) := by
  fin_cases c <;> simp [dotR, Fin.sum_univ_five, F2star, fF] <;> try ring

lemma dotD (E : Fin 5 → ℤ) (c : Fin 5) : dotR D1star E c = fD c (E 0) (E 1) (E 2) (E 3) (E 4) := by
  fin_cases c <;> simp [dotR, Fin.sum_univ_five, D1star, fD] <;> try ring

/-! ## Checkers -/

/-- `T < ∑_c (2b_c)²` (`lem:R2`) at the step `e`. -/
def okR2 (p : ℕ) (T e0 e1 e2 e3 e4 : ℤ) : Bool :=
  decide (e0 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧ e4 = 0) ||
  (fun o : Bool => decide (T < bR2c p o e0 (fF 0 e0 e1 e2 e3 e4) (fD 0 e0 e1 e2 e3 e4) ^ 2 +
      bR2c p o e1 (fF 1 e0 e1 e2 e3 e4) (fD 1 e0 e1 e2 e3 e4) ^ 2 +
      bR2c p o e2 (fF 2 e0 e1 e2 e3 e4) (fD 2 e0 e1 e2 e3 e4) ^ 2 +
      bR2c p o e3 (fF 3 e0 e1 e2 e3 e4) (fD 3 e0 e1 e2 e3 e4) ^ 2 +
      bR2c p o e4 (fF 4 e0 e1 e2 e3 e4) (fD 4 e0 e1 e2 e3 e4) ^ 2)) (decide ((e0 + e1 + e2 + e3 + e4) % 2 = 1))

def chkR2 (p : ℕ) (T e0 : ℤ) : Bool :=
  vals5.all fun e1 => vals5.all fun e2 => vals5.all fun e3 => vals5.all fun e4 => okR2 p T e0 e1 e2 e3 e4

/-- `T < ∑_c (2b_c)²` (`prop:Hk`(1), `k = 1`) at the step `e`. -/
def okHk (p : ℕ) (T e0 e1 e2 e3 e4 : ℤ) : Bool :=
  decide (e0 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧ e4 = 0) ||
  (fun o : Bool => decide (T < bHkc p o e0 (fF 0 e0 e1 e2 e3 e4) ^ 2 +
      bHkc p o e1 (fF 1 e0 e1 e2 e3 e4) ^ 2 +
      bHkc p o e2 (fF 2 e0 e1 e2 e3 e4) ^ 2 +
      bHkc p o e3 (fF 3 e0 e1 e2 e3 e4) ^ 2 +
      bHkc p o e4 (fF 4 e0 e1 e2 e3 e4) ^ 2)) (decide ((e0 + e1 + e2 + e3 + e4) % 2 = 1))

def chkHk (p : ℕ) (T e0 : ℤ) : Bool :=
  vals5.all fun e1 => vals5.all fun e2 => vals5.all fun e3 => vals5.all fun e4 => okHk p T e0 e1 e2 e3 e4

/-- The starred `lem:R2` check at the step `e`. -/
def okR2s (p : ℕ) (T e0 e1 e2 e3 e4 : ℤ) : Bool :=
  decide (e0 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧ e4 = 0) ||
  (fun o : Bool => decide (T < bR2s p o e0 (fF 0 e0 e1 e2 e3 e4) (fD 0 e0 e1 e2 e3 e4) ^ 2 +
      bR2s p o e1 (fF 1 e0 e1 e2 e3 e4) (fD 1 e0 e1 e2 e3 e4) ^ 2 +
      bR2s p o e2 (fF 2 e0 e1 e2 e3 e4) (fD 2 e0 e1 e2 e3 e4) ^ 2 +
      bR2s p o e3 (fF 3 e0 e1 e2 e3 e4) (fD 3 e0 e1 e2 e3 e4) ^ 2 +
      bR2s p o e4 (fF 4 e0 e1 e2 e3 e4) (fD 4 e0 e1 e2 e3 e4) ^ 2)) (decide ((e0 + e1 + e2 + e3 + e4) % 2 = 1))

def chkR2s (p : ℕ) (T e0 : ℤ) : Bool :=
  vals5.all fun e1 => vals5.all fun e2 => vals5.all fun e3 => vals5.all fun e4 => okR2s p T e0 e1 e2 e3 e4

/-- The starred `prop:Hk`(1) check at the step `e`. -/
def okHks (p : ℕ) (T e0 e1 e2 e3 e4 : ℤ) : Bool :=
  decide (e0 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧ e4 = 0) ||
  (fun o : Bool => decide (T < bHks p o e0 (fF 0 e0 e1 e2 e3 e4) ^ 2 +
      bHks p o e1 (fF 1 e0 e1 e2 e3 e4) ^ 2 +
      bHks p o e2 (fF 2 e0 e1 e2 e3 e4) ^ 2 +
      bHks p o e3 (fF 3 e0 e1 e2 e3 e4) ^ 2 +
      bHks p o e4 (fF 4 e0 e1 e2 e3 e4) ^ 2)) (decide ((e0 + e1 + e2 + e3 + e4) % 2 = 1))

def chkHks (p : ℕ) (T e0 : ℤ) : Bool :=
  vals5.all fun e1 => vals5.all fun e2 => vals5.all fun e3 => vals5.all fun e4 => okHks p T e0 e1 e2 e3 e4

lemma ne_zero5 (E : Fin 5 → ℤ) (hE : E ≠ 0) : ¬ (E 0 = 0 ∧ E 1 = 0 ∧ E 2 = 0 ∧ E 3 = 0 ∧ E 4 = 0) := by
  rintro ⟨h0, h1, h2, h3, h4⟩; apply hE; funext i; fin_cases i <;> simp [*]

lemma odd5 (E : Fin 5 → ℤ) : decide ((∑ d, E d) % 2 = 1) = decide ((E 0 + E 1 + E 2 + E 3 + E 4) % 2 = 1) := by
  rw [Fin.sum_univ_five]

lemma vals5_of (E : Fin 5 → ℤ) (hE : E ∈ halfSteps 5) : ∀ c, E c ∈ vals5 := fun c => by
  obtain ⟨-, hb⟩ := halfSteps_mem hE; exact mem_vals5 _ (hb c).1 (hb c).2

theorem r2_of_chk (p : ℕ) (T : ℤ) (hchk : ∀ e0 ∈ vals5, chkR2 p T e0 = true) :
    ∀ E ∈ halfSteps 5, T < ∑ c, bR2 p F2star D1star E c ^ 2 := by
  intro E hE
  have m := vals5_of E hE
  have h := hchk (E 0) (m 0)
  simp only [chkR2, List.all_eq_true] at h
  have h' := h _ (m 1) _ (m 2) _ (m 3) _ (m 4)
  simp only [okR2, Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h' | h'
  · exact absurd h' (ne_zero5 E (halfSteps_mem hE).1)
  · simp only [Fin.sum_univ_five, bR2_eq, dotF, dotD, odd5]
    exact h'

theorem hk_of_chk (p : ℕ) (T : ℤ) (hchk : ∀ e0 ∈ vals5, chkHk p T e0 = true) :
    ∀ E ∈ halfSteps 5, T < ∑ c, bOpt2 p (fun _ => F2star) E (fun _ => 0) c ^ 2 := by
  intro E hE
  have m := vals5_of E hE
  have h := hchk (E 0) (m 0)
  simp only [chkHk, List.all_eq_true] at h
  have h' := h _ (m 1) _ (m 2) _ (m 3) _ (m 4)
  simp only [okHk, Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h' | h'
  · exact absurd h' (ne_zero5 E (halfSteps_mem hE).1)
  · simp only [Fin.sum_univ_five, bOpt2_eq, dotF, odd5]
    exact h'

theorem r2s_of_chk (p : ℕ) (T : ℤ) (hchk : ∀ e0 ∈ vals5, chkR2s p T e0 = true) :
    ∀ E ∈ halfSteps 5, T < ∑ c, bR2s p (decide ((∑ d, E d) % 2 = 1)) (E c) (dotR F2star E c)
      (dotR D1star E c) ^ 2 := by
  intro E hE
  have m := vals5_of E hE
  have h := hchk (E 0) (m 0)
  simp only [chkR2s, List.all_eq_true] at h
  have h' := h _ (m 1) _ (m 2) _ (m 3) _ (m 4)
  simp only [okR2s, Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h' | h'
  · exact absurd h' (ne_zero5 E (halfSteps_mem hE).1)
  · simp only [Fin.sum_univ_five, dotF, dotD, odd5]
    exact h'

theorem hks_of_chk (p : ℕ) (T : ℤ) (hchk : ∀ e0 ∈ vals5, chkHks p T e0 = true) :
    ∀ E ∈ halfSteps 5, T < ∑ c, bHks p (decide ((∑ d, E d) % 2 = 1)) (E c) (dotR F2star E c) ^ 2 := by
  intro E hE
  have m := vals5_of E hE
  have h := hchk (E 0) (m 0)
  simp only [chkHks, List.all_eq_true] at h
  have h' := h _ (m 1) _ (m 2) _ (m 3) _ (m 4)
  simp only [okHks, Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h' | h'
  · exact absurd h' (ne_zero5 E (halfSteps_mem hE).1)
  · simp only [Fin.sum_univ_five, dotF, odd5]
    exact h'

end Z3NetHL.Proofs.Q5

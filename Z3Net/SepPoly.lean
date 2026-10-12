/-
Separation bound of Theorem `thm:sep`: polynomial model of the frame and the scramble.
(Paper: Well-separated (0,3k,3)-nets in every base q ≥ 4; cite by `\label`.)
-/
module
public import Mathlib

@[expose] public section

/-!
# Polynomial model

Over any commutative ring `R`:

* `tauP N F = (reflect N F).comp (1 - X)` is the Möbius map `τ` on polynomials of degree `≤ N`,
  `(τF)(t) = (1-t)^N F(1/(1-t))`. It is multiplicative in the graded sense
  (`tauP_mul`), which replaces all binomial bookkeeping.
* `kap k j W` is the `j`-th coefficient of the power series `W · (1-t)^(-k)`, i.e. the
  `j`-th entry of `K e(W)` (`K` of Definition `def:net`).
-/

namespace Z3Net.Sep

open Polynomial

variable {R : Type*} [CommRing R]

/-! ## The map `τ` -/

/-- `τ_N F = (1-t)^N F(1/(1-t))`, for `natDegree F ≤ N`. -/
noncomputable def tauP (N : ℕ) (F : R[X]) : R[X] := (reflect N F).comp (1 - X)

theorem tauP_add (N : ℕ) (F G : R[X]) : tauP N (F + G) = tauP N F + tauP N G := by
  simp [tauP, reflect_add, add_comp]

theorem tauP_C_mul (N : ℕ) (c : R) (F : R[X]) : tauP N (C c * F) = C c * tauP N F := by
  simp [tauP, reflect_C_mul, mul_comp]

theorem tauP_zero (N : ℕ) : tauP N (0 : R[X]) = 0 := by simp [tauP]

theorem tauP_neg (N : ℕ) (F : R[X]) : tauP N (-F) = -tauP N F := by
  simp [tauP, reflect_neg, neg_comp]

theorem tauP_sub (N : ℕ) (F G : R[X]) : tauP N (F - G) = tauP N F - tauP N G := by
  simp [tauP, reflect_sub, sub_comp]

theorem tauP_sum {ι : Type*} (s : Finset ι) (N : ℕ) (F : ι → R[X]) :
    tauP N (∑ i ∈ s, F i) = ∑ i ∈ s, tauP N (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tauP_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tauP_add, ih]

theorem tauP_mul {F G : R[X]} {a b : ℕ} (hF : F.natDegree ≤ a) (hG : G.natDegree ≤ b) :
    tauP (a + b) (F * G) = tauP a F * tauP b G := by
  simp [tauP, reflect_mul F G hF hG, mul_comp]

theorem tauP_X_pow {N j : ℕ} (h : j ≤ N) : tauP N ((X : R[X]) ^ j) = (1 - X) ^ (N - j) := by
  simp [tauP, reflect_monomial, revAt_le h]

theorem tauP_one (N : ℕ) : tauP N (1 : R[X]) = (1 - X) ^ N := by
  simpa using tauP_X_pow (R := R) (N := N) (j := 0) (Nat.zero_le _)

theorem natDegree_tauP_le {N : ℕ} {F : R[X]} (hF : F.natDegree ≤ N) :
    (tauP N F).natDegree ≤ N := by
  unfold tauP
  refine le_trans natDegree_comp_le ?_
  have h1 : (reflect N F).natDegree ≤ N := le_trans natDegree_reflect_le (max_le le_rfl hF)
  have h2 : (1 - X : R[X]).natDegree ≤ 1 := by
    refine le_trans (natDegree_sub_le _ _) ?_
    simp [natDegree_X_le]
  calc (reflect N F).natDegree * (1 - X : R[X]).natDegree ≤ N * 1 := Nat.mul_le_mul h1 h2
    _ = N := by ring

theorem comp_one_sub_X_twice (F : R[X]) : (F.comp (1 - X)).comp (1 - X) = F := by
  rw [comp_assoc]; simp

/-- `τ_N` is invertible on polynomials of degree `≤ N`. -/
theorem tauP_inv {N : ℕ} {F : R[X]} : reflect N ((tauP N F).comp (1 - X)) = F := by
  simp [tauP, comp_one_sub_X_twice]

theorem tauP_injective {N : ℕ} {F G : R[X]} (h : tauP N F = tauP N G) : F = G := by
  have := congrArg (fun H => reflect N (H.comp (1 - X))) h
  simpa [tauP_inv] using this

theorem tauP_eq_zero {N : ℕ} {F : R[X]} (h : tauP N F = 0) : F = 0 :=
  tauP_injective (h.trans (tauP_zero N).symm)

/-- Degree-1 values. -/
theorem tauP1_one_sub_X : tauP 1 (1 - X : R[X]) = -X := by
  simp [tauP, reflect_sub, reflect_one]

theorem tauP1_X : tauP 1 (X : R[X]) = 1 := by
  simp [tauP]

theorem tauP1_X_sub_one : tauP 1 (X - 1 : R[X]) = X := by
  rw [tauP_sub, tauP1_X, tauP_one]; ring

theorem tauP1_neg_X : tauP 1 (-X : R[X]) = -1 := by
  rw [tauP_neg, tauP1_X]

theorem tauP_pow {F : R[X]} {a : ℕ} (hF : F.natDegree ≤ a) (n : ℕ) :
    tauP (a * n) (F ^ n) = (tauP a F) ^ n := by
  induction n with
  | zero => simp [tauP]
  | succ n ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ,
      tauP_mul (le_trans natDegree_pow_le (by rw [mul_comm]; exact Nat.mul_le_mul_right n hF)) hF,
      ih]

theorem natDegree_one_sub_X_le : (1 - X : R[X]).natDegree ≤ 1 :=
  le_trans (natDegree_sub_le _ _) (by simp [natDegree_X_le])

theorem natDegree_X_sub_one_le : (X - 1 : R[X]).natDegree ≤ 1 :=
  le_trans (natDegree_sub_le _ _) (by simp [natDegree_X_le])

theorem natDegree_neg_X_le : (-X : R[X]).natDegree ≤ 1 := by
  rw [natDegree_neg]; exact natDegree_X_le

theorem tauP_X_sub_one_pow (k : ℕ) : tauP k ((X - 1 : R[X]) ^ k) = X ^ k := by
  have := tauP_pow (natDegree_X_sub_one_le (R := R)) k
  rw [one_mul] at this; rw [this, tauP1_X_sub_one]

theorem tauP_one_sub_X_pow (k : ℕ) : tauP k ((1 - X : R[X]) ^ k) = (-X) ^ k := by
  have := tauP_pow (natDegree_one_sub_X_le (R := R)) k
  rw [one_mul] at this; rw [this, tauP1_one_sub_X]

theorem tauP_neg_X_pow (k : ℕ) : tauP k ((-X : R[X]) ^ k) = (-1) ^ k := by
  have := tauP_pow (natDegree_neg_X_le (R := R)) k
  rw [one_mul] at this; rw [this, tauP1_neg_X]

theorem tauP_X_pow_self (k : ℕ) : tauP k ((X : R[X]) ^ k) = 1 := by
  rw [tauP_X_pow le_rfl]; simp

/-- `(τ_N F)(1) = F_N`. -/
theorem eval_one_tauP (N : ℕ) (F : R[X]) : (tauP N F).eval 1 = F.coeff N := by
  simp only [tauP, eval_comp, eval_sub, eval_one, eval_X, sub_self]
  rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero]

theorem eval_one_reflect {N : ℕ} {F : R[X]} (hF : F.natDegree ≤ N) :
    (reflect N F).eval 1 = F.eval 1 := by
  let _ : Invertible (1 : R) := invertibleOne
  have h := eval₂_reflect_mul_pow (RingHom.id R) (1 : R) N F hF
  simp only [invOf_one, one_pow, mul_one] at h
  exact h

/-- `(τ_N τ_N F)(0) = F_N` for `natDegree F ≤ N`. -/
theorem coeff_zero_tauP_tauP {N : ℕ} {F : R[X]} (hF : F.natDegree ≤ N) :
    (tauP N (tauP N F)).coeff 0 = F.coeff N := by
  rw [coeff_zero_eq_eval_zero]
  conv_lhs => rw [tauP]
  rw [eval_comp]
  simp only [eval_sub, eval_one, eval_X, sub_zero]
  rw [eval_one_reflect (natDegree_tauP_le hF), eval_one_tauP]

/-! ## `K`: coefficients of `W (1-t)^(-k)` -/

/-- The `j`-th coefficient of the power series `W · (1-t)^(-k)`. -/
noncomputable def kap (k j : ℕ) (W : R[X]) : R :=
  PowerSeries.coeff j ((W : PowerSeries R) * ((PowerSeries.invOneSubPow R k : (PowerSeries R)ˣ) :
    PowerSeries R))

theorem kap_add (k j : ℕ) (F G : R[X]) : kap k j (F + G) = kap k j F + kap k j G := by
  simp [kap, add_mul]

theorem kap_C_mul (k j : ℕ) (c : R) (F : R[X]) : kap k j (C c * F) = c * kap k j F := by
  simp [kap, mul_assoc]

theorem kap_neg (k j : ℕ) (F : R[X]) : kap k j (-F) = -kap k j F := by
  simp [kap]

theorem kap_sub (k j : ℕ) (F G : R[X]) : kap k j (F - G) = kap k j F - kap k j G := by
  simp [kap, sub_mul]

theorem kap_zero (k j : ℕ) : kap k j (0 : R[X]) = 0 := by simp [kap]

/-- `kap` of `(1-t)^k G` is the coefficient of `G`. -/
theorem kap_one_sub_pow_mul (k j : ℕ) (G : R[X]) : kap k j ((1 - X) ^ k * G) = G.coeff j := by
  unfold kap
  have h : ((1 - PowerSeries.X : PowerSeries R) ^ k) *
      ((PowerSeries.invOneSubPow R k : (PowerSeries R)ˣ) : PowerSeries R) = 1 := by
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow R k).inv_val
  have : (((1 - X) ^ k * G : R[X]) : PowerSeries R) *
      ((PowerSeries.invOneSubPow R k : (PowerSeries R)ˣ) : PowerSeries R) = (G : PowerSeries R) := by
    rw [coe_mul, coe_pow, coe_sub, coe_one, coe_X, mul_comm, ← mul_assoc, mul_comm _ (_ ^ k), h,
      one_mul]
  rw [this, coeff_coe]

/-- `kap` vanishes below `k` on multiples of `t^k`. -/
theorem kap_X_pow_mul {k j : ℕ} (hj : j < k) (G : R[X]) : kap k j (X ^ k * G) = 0 := by
  unfold kap
  rw [coe_mul, coe_pow, coe_X, mul_assoc, PowerSeries.coeff_X_pow_mul', ite_eq_right_iff.mpr (fun h => absurd h (by omega))]

theorem kap_X_pow_mul_shift (k a j : ℕ) (G : R[X]) :
    kap k (j + a) (X ^ a * G) = kap k j G := by
  unfold kap
  rw [coe_mul, coe_pow, coe_X, mul_assoc, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    Nat.add_sub_cancel]

theorem kap_zero_eq (k : ℕ) (hk : 0 < k) (W : R[X]) : kap k 0 W = W.coeff 0 := by
  unfold kap
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos R k hk,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
  simp

/-- The low coefficients of `W` vanish if the low `kap`'s do. -/
theorem X_pow_dvd_of_kap {k : ℕ} {W : R[X]} (h : ∀ j < k, kap k j W = 0) : X ^ k ∣ W := by
  rw [X_pow_dvd_iff]
  intro d hd
  -- W = (W (1-t)^(-k)) (1-t)^k as power series
  have hW : (W : PowerSeries R) = ((W : PowerSeries R) *
      ((PowerSeries.invOneSubPow R k : (PowerSeries R)ˣ) : PowerSeries R)) *
        (1 - PowerSeries.X) ^ k := by
    rw [mul_assoc, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow,
      (PowerSeries.invOneSubPow R k).val_inv, mul_one]
  rw [← coeff_coe, hW, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have : kap k x.1 W = 0 := h x.1 (by omega)
  unfold kap at this
  rw [this, zero_mul]

/-- Partial sums: `∑_{i<k} kap_i W = (1-t)^(-k-1)`-coefficient; we only need the special case
`W = (1-t)^k G`, `natDegree G < k`. -/
theorem sum_kap_one_sub_pow_mul {k : ℕ} (G : R[X]) (hG : G.natDegree < k) :
    ∑ i ∈ Finset.range k, kap k i ((1 - X) ^ k * G) = G.eval 1 := by
  rw [eval_eq_sum_range' hG]
  simp [kap_one_sub_pow_mul]

end Z3Net.Sep

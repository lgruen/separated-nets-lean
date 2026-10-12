module
public import Z3Net.FEbasis

@[expose] public section

/-!
# Entry F, part 8: `lem:Rs` (generating functions of row 0 of `Φ^F`)

Row `0` of `Φ^F_cd · Toep(uN_d)` is `Q_c^k w_cd y_cd^n` at the `x`-index `n` (`key_Psi`,
`off_Evec`); multiplying its generating function by the linear factor `den'` (`1`, `1 - a_c x`,
`a_c - a_d - x`) telescopes to `Q_c^k` modulo `x^k`, and `uN_d den'` is a unit power series.
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R]

/-- Generating polynomial `ρ(x) = ∑_j ρ_j x^(k-1-j)` of a level-indexed row. -/
def genPoly {k : ℕ} (f : Fin k → R) : R[X] := ∑ l : Fin k, C (f l) * X ^ (k - 1 - (l : ℕ))

lemma coeff_genPoly {k : ℕ} (f : Fin k → R) (j : Fin k) :
    (genPoly f).coeff (k - 1 - (j : ℕ)) = f j := by
  rw [genPoly, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro l _ hl
    rw [coeff_C_mul_X_pow, if_neg]
    intro h; apply hl; ext; have := l.isLt; have := j.isLt; omega
  · simp

lemma toep_gen {k : ℕ} (f : Fin k → R) (u : R[X]) (j : Fin k) :
    ∑ l : Fin k, f l * Z3NetF.toep k u l j = (genPoly f * u).coeff (k - 1 - (j : ℕ)) := by
  rw [genPoly, Finset.sum_mul, finset_sum_coeff]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', Z3NetF.toep]
  have hl := l.isLt; have hj := j.isLt
  by_cases h : j ≤ l
  · have h' : (j : ℕ) ≤ l := h
    rw [if_pos h, if_pos (by omega)]
    congr 2; omega
  · have h' : ¬ (j : ℕ) ≤ l := h
    rw [if_neg h, if_neg (by omega), mul_zero]

variable {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)

/-- The extra linear factor of `lem:Rs`. -/
def denP (c d : Fin s) : R[X] :=
  if c = inf then 1 else if d = inf then 1 - C (x c) * X else C (x c - x d) - X

lemma denP_coe (c d : Fin s) :
    ((denP inf x c d : R[X]) : PowerSeries R) =
      (if c = inf then 1
       else if d = inf then 1 - PowerSeries.C (x c) * PowerSeries.X
       else PowerSeries.C (x c - x d) - PowerSeries.X) := by
  unfold denP
  split_ifs <;> simp [Polynomial.coe_sub, Polynomial.coe_C, Polynomial.coe_X]

/-- The telescoping: `(Q^k ∑_{n<k} w y^n x^n) · den' ≡ Q^k` modulo `x^k`. -/
lemma telescope (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) (hcd : c ≠ d) (P : R[X])
    (hP : ∀ n < k, P.coeff n = Z3NetF.Qf inf x c ^ k * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ n))
    (n : ℕ) (hn : n < k) :
    (P * denP inf x c d).coeff n = if n = 0 then Z3NetF.Qf inf x c ^ k else 0 := by
  unfold denP
  by_cases hc : c = inf
  · have hw : Z3NetF.wN inf x c d = 1 := by simp [Z3NetF.wN, hc]
    have hy : Z3NetF.yN inf x c d = 0 := by simp [Z3NetF.yN, hc]
    rw [if_pos hc, mul_one, hP n hn, hw, hy, one_mul]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · rw [zero_pow (by omega), mul_zero, if_neg (by omega)]
  · rw [if_neg hc]
    by_cases hd : d = inf
    · have hw : Z3NetF.wN inf x c d = 1 := by simp [Z3NetF.wN, hd]
      have hy : Z3NetF.yN inf x c d = x c := by simp [Z3NetF.yN, hc, hd]
      rw [if_pos hd, mul_sub, mul_one, coeff_sub, mul_comm (C (x c)), ← mul_assoc, coeff_mul_C,
        hP n hn, hw, hy, one_mul]
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        rw [coeff_mul_X, hP n' (by omega), hw, hy, one_mul, if_neg (by omega), pow_succ]
        ring
    · have hw : Z3NetF.wN inf x c d = Ring.inverse (x c - x d) := by simp [Z3NetF.wN, hc, hd]
      have hy : Z3NetF.yN inf x c d = Ring.inverse (x c - x d) := by simp [Z3NetF.yN, hc, hd]
      have hD := Ring.mul_inverse_cancel (x c - x d) (hx c d hc hd hcd)
      rw [if_neg hd, mul_sub, coeff_sub, coeff_mul_C, hP n hn, hw, hy]
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        rw [coeff_mul_X_zero, pow_zero, mul_one, if_pos rfl, sub_zero, mul_assoc,
          mul_comm (Ring.inverse _), hD, mul_one]
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        rw [coeff_mul_X, hP n' (by omega), hw, hy, if_neg (by omega), pow_succ]
        rw [show Z3NetF.Qf inf x c ^ k * (Ring.inverse (x c - x d) *
            (Ring.inverse (x c - x d) ^ n' * Ring.inverse (x c - x d))) * (x c - x d) =
            Z3NetF.Qf inf x c ^ k * (Ring.inverse (x c - x d) * Ring.inverse (x c - x d) ^ n') *
              ((x c - x d) * Ring.inverse (x c - x d)) by ring, hD, mul_one, sub_self]

lemma uN_unit (hx : Z3NetF.PlacesOK inf x) (d : Fin s) : IsUnit ((Z3NetF.uN k inf x d).coeff 0) := by
  rw [coeff_zero_eq_eval_zero, Z3NetF.uN]
  split_ifs with hd
  · simp [eval_prod]
  · simp only [eval_prod, eval_pow, eval_add, eval_C, eval_X, add_zero]
    rw [IsUnit.prod_iff]
    intro b hb
    obtain ⟨-, hb1, hb2⟩ := mem_filter.mp hb
    exact (hx d b hd hb1 (Ne.symm hb2)).pow _

lemma denP_unit (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) (hcd : c ≠ d) :
    IsUnit ((denP inf x c d).coeff 0) := by
  unfold denP
  split_ifs with hc hd
  · simp
  · simp
  · simpa using hx c d hc hd hcd

theorem Rs_row0_core (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) (hcd : c ≠ d)
    (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) (j : Fin k) :
    Z3NetF.frameGraph R k inf x c d r j =
      PowerSeries.coeff (k - 1 - (j : ℕ)) (Z3NetF.rsGen k inf x c d) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hs : 2 ≤ s := by
    by_contra h; push_neg at h
    exact hcd (Fin.ext (by have := c.isLt; have := d.isLt; omega))
  set ρ := genPoly (Z3NetF.frameGraph R k inf x c d r)
  -- coefficients of `ρ · uN`
  have hP : ∀ n < k, (ρ * Z3NetF.uN k inf x d).coeff n =
      Z3NetF.Qf inf x c ^ k * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ n) := by
    intro n hn
    have e := toep_gen (Z3NetF.frameGraph R k inf x c d r) (Z3NetF.uN k inf x d) ⟨k - 1 - n, by omega⟩
    simp only [show k - 1 - (k - 1 - n) = n by omega] at e
    rw [← e]
    have e2 := key_Psi k inf x hs hx c d ⟨k - 1 - n, by omega⟩ r
    rw [mul_apply] at e2
    rw [e2]
    have hidx : (⟨k + (r : ℕ), by omega⟩ : Fin (s * k)) = ⟨k, by have := r.isLt; omega⟩ :=
      Fin.ext (by simp [hr])
    rw [hidx, off_Evec k inf x hs hx c d hcd _ (by simp; omega)]
    simp only
    congr 3; omega
  -- the total denominator
  set D : R[X] := Z3NetF.uN k inf x d * denP inf x c d
  have hDu : IsUnit (D : PowerSeries R) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, coeff_zero_eq_eval_zero, eval_mul, ← coeff_zero_eq_eval_zero,
      ← coeff_zero_eq_eval_zero]
    exact (uN_unit k inf x hx d).mul (denP_unit inf x hx c d hcd)
  have hρD : ∀ n < k, ((ρ : PowerSeries R) * (D : PowerSeries R)).coeff n =
      (PowerSeries.C (Z3NetF.Qf inf x c ^ k)).coeff n := by
    intro n hn
    rw [← Polynomial.coe_mul, Polynomial.coeff_coe, ← mul_assoc, telescope k inf x hx c d hcd _ hP n hn,
      PowerSeries.coeff_C]
  have hrs : Z3NetF.rsGen k inf x c d =
      PowerSeries.C (Z3NetF.Qf inf x c ^ k) * Ring.inverse (D : PowerSeries R) := by
    rw [Z3NetF.rsGen, Polynomial.coe_mul, denP_coe]
  -- conclude coefficientwise
  have hcoef : ∀ n < k, (ρ : PowerSeries R).coeff n =
      (PowerSeries.C (Z3NetF.Qf inf x c ^ k) * Ring.inverse (D : PowerSeries R)).coeff n := by
    intro n hn
    have e : (ρ : PowerSeries R) = ((ρ : PowerSeries R) * (D : PowerSeries R)) * Ring.inverse (D : PowerSeries R) := by
      rw [mul_assoc, Ring.mul_inverse_cancel _ hDu, mul_one]
    rw [e, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [hρD p.1 (by omega)]
  rw [hrs, ← hcoef _ (by omega), Polynomial.coeff_coe, coeff_genPoly]

end

end Z3NetF.Proofs

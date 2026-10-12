module
public import Z3Net.SplitEbasis
public import Z3Net.FRs

@[expose] public section

/-!
# Entry Split, part 2: `lem:Rsplit` (generating functions of row 0 of `Φ^S`)

Row `0` of `Φ^S_cd · Toep(Π_d(v_d + x))` is `P_c^k w_cd y_cd^n` at the `x`-index `n` (`skey_Psi`,
`soff`); multiplying its generating function by `ϑ_cd - x` telescopes to `P_c^k` modulo `x^k`,
and `Π_d(v_d + x) (ϑ_cd - x)` is a unit power series.
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s : ℕ}

/-- The telescoping: `(P^k ∑_{n<k} y^(n+1) x^n) · (ϑ - x) ≡ P^k` modulo `x^k` (`y = 1/ϑ`). -/
lemma stelescope (k : ℕ) (u v : Fin s → R) (huv : Z3NetF.SplitOK u v) (c d : Fin s) (P : R[X])
    (hP : ∀ n < k, P.coeff n =
      Z3NetF.Psplit u v c ^ k * (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ n))
    (n : ℕ) (hn : n < k) :
    (P * (C (u c - v d) - X)).coeff n = if n = 0 then Z3NetF.Psplit u v c ^ k else 0 := by
  have hD := Ring.mul_inverse_cancel (u c - v d) (split_uv huv c d)
  rw [mul_sub, coeff_sub, coeff_mul_C, hP n hn, Z3NetF.ySplit]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [coeff_mul_X_zero, pow_zero, mul_one, if_pos rfl, sub_zero, mul_assoc,
      mul_comm (Ring.inverse _), hD, mul_one]
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [coeff_mul_X, hP n' (by omega), Z3NetF.ySplit, if_neg (by omega), pow_succ]
    rw [show Z3NetF.Psplit u v c ^ k * (Ring.inverse (u c - v d) *
        (Ring.inverse (u c - v d) ^ n' * Ring.inverse (u c - v d))) * (u c - v d) =
        Z3NetF.Psplit u v c ^ k * (Ring.inverse (u c - v d) * Ring.inverse (u c - v d) ^ n') *
          ((u c - v d) * Ring.inverse (u c - v d)) by ring, hD, mul_one, sub_self]

lemma piSplit_unit (k : ℕ) (u v : Fin s → R) (huv : Z3NetF.SplitOK u v) (d : Fin s) :
    IsUnit ((Z3NetF.piSplit k v d).coeff 0) := by
  rw [coeff_zero_eq_eval_zero, Z3NetF.piSplit]
  simp only [eval_prod, eval_pow, eval_add, eval_C, eval_X, add_zero]
  rw [IsUnit.prod_iff]
  intro b hb
  exact (split_vv huv d b (Ne.symm (mem_filter.mp hb).2)).pow _

theorem Rsplit_row0 (k : ℕ) (u v : Fin s → R)
    (huv : Z3NetF.SplitOK u v) (c d : Fin s) (hcd : c ≠ d) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0)
    (j : Fin k) :
    Z3NetF.splitGraph R k u v c d r j =
      PowerSeries.coeff (k - 1 - (j : ℕ)) (Z3NetF.rsSplit k u v c d) := by
  have hs := two_le_of_ne hcd
  set ρ := genPoly (Z3NetF.splitGraph R k u v c d r)
  -- coefficients of `ρ · Π_d(v_d + x)`
  have hP : ∀ n < k, (ρ * Z3NetF.piSplit k v d).coeff n =
      Z3NetF.Psplit u v c ^ k * (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ n) := by
    intro n hn
    have e := toep_gen (Z3NetF.splitGraph R k u v c d r) (Z3NetF.piSplit k v d) ⟨k - 1 - n, by omega⟩
    simp only [show k - 1 - (k - 1 - n) = n by omega] at e
    rw [← e]
    have e2 := skey_Psi k u v huv c d ⟨k - 1 - n, by omega⟩ r
    rw [mul_apply] at e2
    rw [e2]
    have hidx : (⟨k + (r : ℕ), by omega⟩ : Fin (s * k)) = ⟨k, by have := r.isLt; omega⟩ :=
      Fin.ext (by simp [hr])
    rw [hidx, soff k u v hs huv c d _ (by simp; omega)]
    simp only
    congr 3; omega
  -- the total denominator
  set D : R[X] := Z3NetF.piSplit k v d * (C (u c - v d) - X)
  have hDu : IsUnit (D : PowerSeries R) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, coeff_zero_eq_eval_zero, eval_mul, ← coeff_zero_eq_eval_zero]
    refine (piSplit_unit k u v huv d).mul ?_
    simpa using split_uv huv c d
  have hρD : ∀ n < k, ((ρ : PowerSeries R) * (D : PowerSeries R)).coeff n =
      (PowerSeries.C (Z3NetF.Psplit u v c ^ k)).coeff n := by
    intro n hn
    rw [← Polynomial.coe_mul, Polynomial.coeff_coe, ← mul_assoc,
      stelescope k u v huv c d _ hP n hn, PowerSeries.coeff_C]
  have hden : ((C (u c - v d) - X : R[X]) : PowerSeries R) =
      PowerSeries.C (u c - v d) - PowerSeries.X := by
    simp [Polynomial.coe_sub, Polynomial.coe_C, Polynomial.coe_X]
  have hrs : Z3NetF.rsSplit k u v c d =
      PowerSeries.C (Z3NetF.Psplit u v c ^ k) * Ring.inverse (D : PowerSeries R) := by
    rw [Z3NetF.rsSplit, Polynomial.coe_mul, hden]
  -- conclude coefficientwise
  have hcoef : ∀ n < k, (ρ : PowerSeries R).coeff n =
      (PowerSeries.C (Z3NetF.Psplit u v c ^ k) * Ring.inverse (D : PowerSeries R)).coeff n := by
    intro n hn
    have e : (ρ : PowerSeries R) =
        ((ρ : PowerSeries R) * (D : PowerSeries R)) * Ring.inverse (D : PowerSeries R) := by
      rw [mul_assoc, Ring.mul_inverse_cancel _ hDu, mul_one]
    rw [e, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [hρD p.1 (by omega)]
  rw [hrs, ← hcoef _ (by omega), Polynomial.coeff_coe, coeff_genPoly]

end

end Z3NetF.Proofs

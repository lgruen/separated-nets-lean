/-
Separation bound of Theorem `thm:sep`: Proposition `prop:cell` (the geometric digit and the
locality of the offset digits), over any nontrivial commutative ring.
-/
module
public import Z3Net.SepBridge

@[expose] public section

/-!
# Proposition `prop:cell`

The proof follows the paper's CRT split, made algebraic: every `V` of degree `< 3k` is
`V = A (t-1)^k + B t^k + Q t^k (t-1)^k` with `deg A, B, Q < k` (`decomp`, over any commutative
ring, via division by the monic `t^k (t-1)^k` and a Bézout identity for `t^k, (t-1)^k`).
Graded multiplicativity of `τ` (`tauP_mul`) then gives

* `τV  = τA · t^k (1-t)^k + τB · (1-t)^k + τQ · t^k`,
* `τ²V = τ²A · (-t)^k + τ²B · (-t)^k (1-t)^k + τ²Q · (1-t)^k`,

and (a) reduces to `(τ²A)(0) = A_{k-1}`, `(τ²B)(0) = B_{k-1}`, `(τB)(1) = B_{k-1}` — the residue
identity `p_{2k-1} = Res_0 ω + Res_1 ω` of the paper in polynomial form.
-/

namespace Z3Net.Sep

open Polynomial Matrix

variable {R : Type*} [CommRing R]

theorem isCoprime_X_pow_X_sub_one_pow (k : ℕ) : IsCoprime ((X : R[X]) ^ k) ((X - 1) ^ k) :=
  IsCoprime.pow ⟨1, -1, by ring⟩

theorem isCoprime_X_pow_one_sub_X_pow (k : ℕ) : IsCoprime ((X : R[X]) ^ k) ((1 - X) ^ k) :=
  IsCoprime.pow ⟨1, 1, by ring⟩

theorem eq_zero_of_X_pow_dvd {k : ℕ} {A : R[X]} (hk : 1 ≤ k) (hA : A.natDegree ≤ k - 1)
    (h : X ^ k ∣ A) : A = 0 := by
  ext d
  rw [coeff_zero]
  rcases lt_or_ge d k with hd | hd
  · exact (X_pow_dvd_iff.mp h) d hd
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem natDegree_X_sub_one_pow_le (k : ℕ) : ((X - 1 : R[X]) ^ k).natDegree ≤ k := by
  simpa using natDegree_pow_le_of_le k (natDegree_X_sub_one_le (R := R))

theorem natDegree_one_sub_X_pow_le (k : ℕ) : ((1 - X : R[X]) ^ k).natDegree ≤ k := by
  simpa using natDegree_pow_le_of_le k (natDegree_one_sub_X_le (R := R))

theorem natDegree_neg_X_pow_le (k : ℕ) : ((-X : R[X]) ^ k).natDegree ≤ k := by
  simpa using natDegree_pow_le_of_le k (natDegree_neg_X_le (R := R))

/-! ## The CRT decomposition -/

theorem decomp [Nontrivial R] (k : ℕ) (hk : 1 ≤ k) (V : R[X]) (hV : V.natDegree ≤ 3 * k - 1) :
    ∃ A B Q : R[X], A.natDegree ≤ k - 1 ∧ B.natDegree ≤ k - 1 ∧ Q.natDegree ≤ k - 1 ∧
      V = A * (X - 1) ^ k + B * X ^ k + Q * X ^ k * (X - 1) ^ k := by
  have hm1 : ((X - 1 : R[X]) ^ k).Monic := by
    have : (X - 1 : R[X]) = X - C 1 := by simp
    rw [this]; exact (monic_X_sub_C 1).pow k
  have hmX : ((X : R[X]) ^ k).Monic := monic_X_pow k
  have hDm : ((X : R[X]) ^ k * (X - 1) ^ k).Monic := hmX.mul hm1
  have hdeg1 : ((X - 1 : R[X]) ^ k).natDegree = k := by
    have : (X - 1 : R[X]) = X - C 1 := by simp
    rw [this, (monic_X_sub_C (1 : R)).natDegree_pow k, natDegree_X_sub_C, mul_one]
  have hDdeg : ((X : R[X]) ^ k * (X - 1) ^ k).natDegree = 2 * k := by
    rw [hmX.natDegree_mul hm1, natDegree_X_pow, hdeg1]; ring
  set D : R[X] := X ^ k * (X - 1) ^ k with hD
  have hD1 : D ≠ 1 := by
    intro h; rw [h, natDegree_one] at hDdeg; omega
  set Q := V /ₘ D with hQdef
  set P := V %ₘ D with hPdef
  have hVPQ : P + D * Q = V := modByMonic_add_div V D
  have hQ : Q.natDegree ≤ k - 1 := by
    rw [hQdef, natDegree_divByMonic V hDm, hDdeg]; omega
  have hP : P.natDegree < 2 * k := by
    rw [← hDdeg]; exact natDegree_modByMonic_lt V hDm hD1
  obtain ⟨α, β, hαβ⟩ := isCoprime_X_pow_X_sub_one_pow (R := R) k
  have hXk1 : (X : R[X]) ^ k ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_X_pow, natDegree_one] at this; omega
  set A := (P * β) %ₘ X ^ k with hAdef
  have hA : A.natDegree < k := by
    have := natDegree_modByMonic_lt (P * β) hmX hXk1
    rwa [natDegree_X_pow] at this
  have hAeq : A + X ^ k * ((P * β) /ₘ X ^ k) = P * β := modByMonic_add_div _ _
  set B := P * α + ((P * β) /ₘ X ^ k) * (X - 1) ^ k with hBdef
  have hPAB : P = A * (X - 1) ^ k + B * X ^ k := by
    rw [hBdef]
    linear_combination (-P) * hαβ - (X - 1) ^ k * hAeq
  have hB : B.natDegree ≤ k - 1 := by
    by_cases hB0 : B = 0
    · rw [hB0]; simp
    have h1 : (B * X ^ k).natDegree = B.natDegree + k := by
      rw [mul_comm]; exact natDegree_X_pow_mul k hB0
    have h2 : (B * X ^ k).natDegree ≤ 2 * k - 1 := by
      have : B * X ^ k = P - A * (X - 1) ^ k := by rw [hPAB]; ring
      rw [this]
      refine le_trans (natDegree_sub_le _ _) (max_le (by omega) ?_)
      refine le_trans natDegree_mul_le ?_
      rw [hdeg1]; omega
    omega
  refine ⟨A, B, Q, by omega, hB, hQ, ?_⟩
  rw [← hVPQ, hPAB, hD]; ring

/-! ## `τ` and `τ²` of the three parts (`n = 3k-1`) -/

section Parts

variable {k : ℕ}

theorem tau3 (hk : 1 ≤ k) {F G H : R[X]} (hF : F.natDegree ≤ k - 1) (hG : G.natDegree ≤ k)
    (hH : H.natDegree ≤ k) :
    tauP (3 * k - 1) (F * G * H) = tauP (k - 1) F * tauP k G * tauP k H := by
  have e : 3 * k - 1 = (k - 1 + k) + k := by omega
  rw [e, tauP_mul (le_trans natDegree_mul_le (Nat.add_le_add hF hG)) hH, tauP_mul hF hG]

theorem natDegree_tau_le (_hk : 1 ≤ k) {F : R[X]} (hF : F.natDegree ≤ k - 1) :
    (tauP (k - 1) F).natDegree ≤ k - 1 := natDegree_tauP_le hF

theorem tau_partA (hk : 1 ≤ k) {A : R[X]} (hA : A.natDegree ≤ k - 1) :
    tauP (3 * k - 1) (A * (X - 1) ^ k) = tauP (k - 1) A * X ^ k * (1 - X) ^ k := by
  rw [show A * (X - 1) ^ k = A * (X - 1) ^ k * 1 by ring,
    tau3 hk hA (natDegree_X_sub_one_pow_le k) (by simp), tauP_X_sub_one_pow, tauP_one]

theorem tau2_partA (hk : 1 ≤ k) {A : R[X]} (hA : A.natDegree ≤ k - 1) :
    tauP (3 * k - 1) (tauP (3 * k - 1) (A * (X - 1) ^ k)) =
      tauP (k - 1) (tauP (k - 1) A) * (-X) ^ k := by
  rw [tau_partA hk hA, tau3 hk (natDegree_tau_le hk hA) (natDegree_X_pow_le k)
    (natDegree_one_sub_X_pow_le k), tauP_X_pow_self, tauP_one_sub_X_pow, mul_one]

theorem tau_partB (hk : 1 ≤ k) {B : R[X]} (hB : B.natDegree ≤ k - 1) :
    tauP (3 * k - 1) (B * X ^ k) = tauP (k - 1) B * (1 - X) ^ k := by
  rw [show B * X ^ k = B * X ^ k * 1 by ring,
    tau3 hk hB (natDegree_X_pow_le k) (by simp), tauP_X_pow_self, tauP_one, mul_one]

theorem tau2_partB (hk : 1 ≤ k) {B : R[X]} (hB : B.natDegree ≤ k - 1) :
    tauP (3 * k - 1) (tauP (3 * k - 1) (B * X ^ k)) =
      tauP (k - 1) (tauP (k - 1) B) * (-X) ^ k * (1 - X) ^ k := by
  rw [tau_partB hk hB, show tauP (k - 1) B * (1 - X) ^ k = tauP (k - 1) B * (1 - X) ^ k * 1 by ring,
    tau3 hk (natDegree_tau_le hk hB) (natDegree_one_sub_X_pow_le k) (by simp),
    tauP_one_sub_X_pow, tauP_one]

theorem tau_partQ (hk : 1 ≤ k) {Q : R[X]} (hQ : Q.natDegree ≤ k - 1) :
    tauP (3 * k - 1) (Q * X ^ k * (X - 1) ^ k) = tauP (k - 1) Q * X ^ k := by
  rw [tau3 hk hQ (natDegree_X_pow_le k) (natDegree_X_sub_one_pow_le k), tauP_X_pow_self,
    tauP_X_sub_one_pow, mul_one]

theorem tau2_partQ (hk : 1 ≤ k) {Q : R[X]} (hQ : Q.natDegree ≤ k - 1) :
    tauP (3 * k - 1) (tauP (3 * k - 1) (Q * X ^ k * (X - 1) ^ k)) =
      tauP (k - 1) (tauP (k - 1) Q) * (1 - X) ^ k := by
  rw [tau_partQ hk hQ, show tauP (k - 1) Q * X ^ k = tauP (k - 1) Q * X ^ k * 1 by ring,
    tau3 hk (natDegree_tau_le hk hQ) (natDegree_X_pow_le k) (by simp), tauP_X_pow_self,
    tauP_one, mul_one]

end Parts

/-! ## `Ldig` on the cell rows -/

theorem Ldig_k (k : ℕ) (W : R[X]) : Ldig k k W = kap k (k - 1) W + kap k k W := by
  simp [Ldig]

theorem Ldig_km1 (k : ℕ) (hk : 2 ≤ k) (W : R[X]) : Ldig k (k - 1) W = -kap k (k - 1) W := by
  unfold Ldig
  rw [if_neg (by omega), if_pos (by omega)]

theorem Ldig_km2 (k : ℕ) (hk : 2 ≤ k) (W : R[X]) :
    Ldig k (k - 2) W = ∑ i ∈ Finset.range (k - 1), kap k i W := by
  unfold Ldig
  rw [if_pos (by omega)]

theorem Ldig_gt (k j : ℕ) (hj : k < j) (W : R[X]) : Ldig k j W = kap k j W := by
  unfold Ldig
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem kap_low_of_Ldig (k : ℕ) (hk : 2 ≤ k) (W : R[X]) (h : ∀ j < k, Ldig k j W = 0) :
    ∀ j < k, kap k j W = 0 := by
  have low : ∀ j, j + 2 < k → kap k j W = 0 := by
    intro j hj
    have := h j (by omega)
    unfold Ldig at this
    rwa [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at this
  intro j hj
  rcases (show j + 2 < k ∨ j + 2 = k ∨ j + 1 = k by omega) with h1 | h1 | h1
  · exact low j h1
  · have := h j hj
    unfold Ldig at this
    rw [if_pos h1, show k - 1 = j + 1 by omega, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun i hi => low i (by simp at hi; omega)), zero_add] at this
    exact this
  · have := h j hj
    unfold Ldig at this
    rw [if_neg (by omega), if_pos h1, neg_eq_zero] at this
    exact this

/-! ## Proposition `prop:cell` (a) -/

/-- **Proposition `prop:cell`(a)**, polynomial form:
`d^x_k = -d^x_{k-1} - d^y_{k-1} + d^z_{k-1} - d^z_{k-2}`. -/
theorem cell_a [Nontrivial R] (k : ℕ) (hk : 2 ≤ k) (V : R[X]) (hV : V.natDegree ≤ 3 * k - 1) :
    Ldig k k (tauP (3 * k - 1) (tauP (3 * k - 1) V)) =
      -Ldig k (k - 1) (tauP (3 * k - 1) (tauP (3 * k - 1) V)) - Ldig k (k - 1) V
        + Ldig k (k - 1) (C (sk k) * tauP (3 * k - 1) V)
        - Ldig k (k - 2) (C (sk k) * tauP (3 * k - 1) V) := by
  rw [Ldig_k, Ldig_km1 k hk, Ldig_km1 k hk, Ldig_km1 k hk, Ldig_km2 k hk, kap_C_mul]
  simp only [kap_C_mul]
  rw [← Finset.mul_sum]
  -- reduce to `kap_k(τ²V) = kap_{k-1}(V) - s ∑_{i<k} kap_i(τV)`
  suffices H : kap k k (tauP (3 * k - 1) (tauP (3 * k - 1) V)) = kap k (k - 1) V -
      sk k * ∑ i ∈ Finset.range k, kap k i (tauP (3 * k - 1) V) by
    have e : k = (k - 1) + 1 := by omega
    rw [e, Finset.sum_range_succ, ← e] at H
    linear_combination H
  have hk1 : 1 ≤ k := by omega
  obtain ⟨A, B, Q, hA, hB, hQ, rfl⟩ := decomp k hk1 V hV
  simp only [tauP_add, kap_add, Finset.sum_add_distrib]
  rw [tau2_partA hk1 hA, tau2_partB hk1 hB, tau2_partQ hk1 hQ, tau_partA hk1 hA,
    tau_partB hk1 hB, tau_partQ hk1 hQ]
  -- the individual terms
  have hk0 : 0 < k := by omega
  have t1 : kap k k (tauP (k - 1) (tauP (k - 1) A) * (-X) ^ k) = (-1) ^ k * A.coeff (k - 1) := by
    rw [show tauP (k - 1) (tauP (k - 1) A) * (-X : R[X]) ^ k =
        X ^ k * (C ((-1) ^ k) * tauP (k - 1) (tauP (k - 1) A)) by
      rw [neg_pow, C_pow, C_neg, C_1]; ring]
    have hs := kap_X_pow_mul_shift (R := R) k k 0
      (C ((-1) ^ k) * tauP (k - 1) (tauP (k - 1) A))
    rw [zero_add] at hs
    rw [hs, kap_zero_eq k hk0, coeff_C_mul, coeff_zero_tauP_tauP hA]
  have t2 : kap k k (tauP (k - 1) (tauP (k - 1) B) * (-X) ^ k * (1 - X) ^ k) =
      (-1) ^ k * B.coeff (k - 1) := by
    rw [show tauP (k - 1) (tauP (k - 1) B) * (-X : R[X]) ^ k * (1 - X) ^ k =
        (1 - X) ^ k * (C ((-1) ^ k) * (X ^ k * tauP (k - 1) (tauP (k - 1) B))) by
      rw [neg_pow, C_pow, C_neg, C_1]; ring]
    rw [kap_one_sub_pow_mul, coeff_C_mul, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_tauP_tauP hB]
  have t3 : kap k k (tauP (k - 1) (tauP (k - 1) Q) * (1 - X) ^ k) = 0 := by
    rw [mul_comm, kap_one_sub_pow_mul]
    exact coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_tau_le hk1 (natDegree_tau_le hk1 hQ)) (by omega))
  have t4 : kap k (k - 1) (A * (X - 1) ^ k) = (-1) ^ k * A.coeff (k - 1) := by
    rw [show A * (X - 1 : R[X]) ^ k = (1 - X) ^ k * (C ((-1) ^ k) * A) by
      rw [C_pow, C_neg, C_1, show (X - 1 : R[X]) = (-1) * (1 - X) by ring, mul_pow]; ring]
    rw [kap_one_sub_pow_mul, coeff_C_mul]
  have t5 : kap k (k - 1) (B * X ^ k) = 0 := by
    rw [mul_comm]; exact kap_X_pow_mul (by omega) _
  have t6 : kap k (k - 1) (Q * X ^ k * (X - 1) ^ k) = 0 := by
    rw [show Q * X ^ k * (X - 1 : R[X]) ^ k = X ^ k * (Q * (X - 1) ^ k) by ring]
    exact kap_X_pow_mul (by omega) _
  have t7 : ∑ i ∈ Finset.range k, kap k i (tauP (k - 1) A * X ^ k * (1 - X) ^ k) = 0 := by
    apply Finset.sum_eq_zero; intro i hi; simp only [Finset.mem_range] at hi
    rw [show tauP (k - 1) A * X ^ k * (1 - X : R[X]) ^ k = X ^ k * (tauP (k - 1) A * (1 - X) ^ k)
      by ring]
    exact kap_X_pow_mul hi _
  have t8 : ∑ i ∈ Finset.range k, kap k i (tauP (k - 1) B * (1 - X) ^ k) = B.coeff (k - 1) := by
    rw [show tauP (k - 1) B * (1 - X : R[X]) ^ k = (1 - X) ^ k * tauP (k - 1) B by ring,
      sum_kap_one_sub_pow_mul _ (lt_of_le_of_lt (natDegree_tau_le hk1 hB) (by omega)),
      eval_one_tauP]
  have t9 : ∑ i ∈ Finset.range k, kap k i (tauP (k - 1) Q * X ^ k) = 0 := by
    apply Finset.sum_eq_zero; intro i hi; simp only [Finset.mem_range] at hi
    rw [mul_comm]; exact kap_X_pow_mul hi _
  rw [t1, t2, t3, t4, t5, t6, t7, t8, t9, sk]
  ring

/-! ## Proposition `prop:cell` (b) and the cell injectivity -/

/-- **Proposition `prop:cell`(b)** and injectivity of the cells, polynomial form: if the
`y`- and `z`-cell digits of `U` vanish, the `K`-digits `≥ k` of the `x`-reading vanish; if
moreover the `x`-cell digits vanish, `U = 0`. -/
theorem cell_b [Nontrivial R] (k : ℕ) (hk : 2 ≤ k) (U : R[X]) (hU : U.natDegree ≤ 3 * k - 1)
    (hy : ∀ j < k, Ldig k j U = 0) (hz : ∀ j < k, Ldig k j (C (sk k) * tauP (3 * k - 1) U) = 0) :
    (∀ j, k ≤ j → kap k j (tauP (3 * k - 1) (tauP (3 * k - 1) U)) = 0) ∧
      ((∀ j < k, Ldig k j (tauP (3 * k - 1) (tauP (3 * k - 1) U)) = 0) → U = 0) := by
  have hk1 : 1 ≤ k := by omega
  have hXU : X ^ k ∣ U := X_pow_dvd_of_kap (kap_low_of_Ldig k hk U hy)
  have hXτU : X ^ k ∣ tauP (3 * k - 1) U := by
    have h1 := X_pow_dvd_of_kap (kap_low_of_Ldig k hk _ hz)
    have : tauP (3 * k - 1) U = C (sk k) * (C (sk k) * tauP (3 * k - 1) U) := by
      rw [← mul_assoc, ← C_mul, sk_mul_sk, C_1, one_mul]
    rw [this]; exact dvd_mul_of_dvd_right h1 _
  obtain ⟨A, B, Q, hA, hB, hQ, rfl⟩ := decomp k hk1 U hU
  -- A = 0
  have hA0 : A = 0 := by
    apply eq_zero_of_X_pow_dvd hk1 hA
    apply (isCoprime_X_pow_X_sub_one_pow k).dvd_of_dvd_mul_right
    have : A * (X - 1) ^ k = (A * (X - 1) ^ k + B * X ^ k + Q * X ^ k * (X - 1) ^ k) -
        X ^ k * (B + Q * (X - 1) ^ k) := by ring
    rw [this]; exact dvd_sub hXU (dvd_mul_right _ _)
  -- B = 0
  have hB0 : B = 0 := by
    rw [tauP_add, tauP_add, tau_partA hk1 hA, tau_partB hk1 hB, tau_partQ hk1 hQ] at hXτU
    have hdvd : X ^ k ∣ tauP (k - 1) B * (1 - X) ^ k := by
      have : tauP (k - 1) B * (1 - X) ^ k = (tauP (k - 1) A * X ^ k * (1 - X) ^ k +
          tauP (k - 1) B * (1 - X) ^ k + tauP (k - 1) Q * X ^ k) -
          X ^ k * (tauP (k - 1) A * (1 - X) ^ k + tauP (k - 1) Q) := by ring
      rw [this]; exact dvd_sub hXτU (dvd_mul_right _ _)
    have := (isCoprime_X_pow_one_sub_X_pow k).dvd_of_dvd_mul_right hdvd
    exact tauP_eq_zero (eq_zero_of_X_pow_dvd hk1 (natDegree_tau_le hk1 hB) this)
  subst hA0 hB0
  simp only [zero_mul, zero_add]
  rw [tau2_partQ hk1 hQ]
  have hQ2 := natDegree_tau_le hk1 (natDegree_tau_le hk1 hQ)
  refine ⟨fun j hj => ?_, fun hx => ?_⟩
  · rw [mul_comm, kap_one_sub_pow_mul]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  · have hlow := kap_low_of_Ldig k hk _ hx
    have hQ0 : tauP (k - 1) (tauP (k - 1) Q) = 0 := by
      ext d
      rw [coeff_zero]
      rcases lt_or_ge d k with hd | hd
      · have := hlow d hd
        rwa [mul_comm, kap_one_sub_pow_mul] at this
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    rw [tauP_eq_zero (tauP_eq_zero hQ0)]
    ring

/-! ## `τ³ = (-1)^N` and the cyclic symmetry `T³ = 1` -/

theorem tauP_cube_X_pow (a b : ℕ) :
    tauP (a + b) (tauP (a + b) (tauP (a + b) ((X : R[X]) ^ b))) = C ((-1) ^ (a + b)) * X ^ b := by
  rw [tauP_X_pow (by omega), Nat.add_sub_cancel, show (1 - X : R[X]) ^ a = (1 - X) ^ a * 1 by ring,
    tauP_mul (natDegree_one_sub_X_pow_le a) (by simp), tauP_one_sub_X_pow, tauP_one,
    tauP_mul (natDegree_neg_X_pow_le a) (natDegree_one_sub_X_pow_le b), tauP_neg_X_pow,
    tauP_one_sub_X_pow]
  rw [neg_pow (X : R[X]) b, C_pow, C_neg, C_1, pow_add]; ring

theorem tauP_cube {N : ℕ} {F : R[X]} (hF : F.natDegree ≤ N) :
    tauP N (tauP N (tauP N F)) = C ((-1) ^ N) * F := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow F]
  conv_rhs => rw [as_sum_range_C_mul_X_pow F]
  simp only [tauP_sum, tauP_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [← mul_assoc, mul_comm (C ((-1) ^ N)), mul_assoc]
  congr 1
  replace hj : j < N + 1 := by omega
  obtain ⟨a, ha⟩ : ∃ a, N = a + j := ⟨N - j, by omega⟩
  rw [ha, tauP_cube_X_pow]

end Z3Net.Sep

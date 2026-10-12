module
public import Z3Net.NetBasic

@[expose] public section

/-!
# The Möbius frame on polynomials

`τ` acts on `R[t]_{<m}` by `(τ V)(t) = ∑_i V_i (1-t)^(m-1-i)` (= `(1-t)^(m-1) V(1/(1-t))`).
We prove `τ³ = (-1)^(m-1)` and the forward degree/divisibility facts used in the proof of
`thm:t0`, and conclude that the frame `(T², I, T)` (and every lower-triangular `±1`-diagonal
scramble of it, cf. `eq:scr`) has injective box matrices over every field.
-/

namespace Z3Net.Proofs

open Matrix Finset Polynomial

section Poly

variable {R : Type*} [CommRing R]

/-- The polynomial `∑_i v_i t^i` of a coefficient vector. -/
noncomputable def toPoly {m : ℕ} (v : Fin m → R) : R[X] := ∑ i : Fin m, C (v i) * X ^ (i : ℕ)

lemma coeff_toPoly {m : ℕ} (v : Fin m → R) (j : ℕ) :
    (toPoly v).coeff j = if h : j < m then v ⟨j, h⟩ else 0 := by
  simp only [toPoly, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      have : j ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : j ≠ (i : ℕ) := by omega
    simp [this]

lemma toPoly_mem {m : ℕ} (v : Fin m → R) : toPoly v ∈ degreeLT R m := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_toPoly, dif_neg (by omega)]

lemma toPoly_injective {m : ℕ} (v : Fin m → R) (h : toPoly v = 0) : v = 0 := by
  funext i
  have := congrArg (fun P => P.coeff i) h
  simpa [coeff_toPoly] using this

/-- The Möbius operator `τ` with parameter `N = m - 1`. -/
noncomputable def tauL (N : ℕ) : R[X] →ₗ[R] R[X] where
  toFun P := ∑ i ∈ range (N + 1), C (P.coeff i) * (1 - X) ^ (N - i)
  map_add' P Q := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a P := by simp [Finset.mul_sum, smul_eq_C_mul, mul_assoc]

lemma tauL_apply (N : ℕ) (P : R[X]) :
    tauL N P = ∑ i ∈ range (N + 1), C (P.coeff i) * (1 - X) ^ (N - i) := rfl

lemma coeff_one_sub_X_pow (n i : ℕ) :
    ((1 - X : R[X]) ^ n).coeff i = (-1) ^ i * (n.choose i : R) := by
  rw [show (1 - X : R[X]) = -X + 1 by ring, add_pow, finset_sum_coeff]
  have hterm : ∀ j ∈ range (n + 1), ((-X : R[X]) ^ j * 1 ^ (n - j) * (n.choose j : R[X])).coeff i
      = if i = j then (-1) ^ i * (n.choose i : R) else 0 := by
    intro j _
    rw [one_pow, mul_one, neg_pow, mul_comm ((-1 : R[X]) ^ j), mul_assoc,
      show ((-1 : R[X]) ^ j * (n.choose j : R[X])) = C ((-1) ^ j * (n.choose j : R)) by simp,
      mul_comm, coeff_C_mul_X_pow]
    split_ifs with h <;> simp [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simp at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma one_sub_X_pow_mem (j n : ℕ) (h : j < n) : (1 - X : R[X]) ^ j ∈ degreeLT R n := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_one_sub_X_pow, Nat.choose_eq_zero_of_lt (by omega)]
  simp

/-- Shift: `τ_N (t^s Q) = τ_{N-s} Q`. -/
lemma tauL_X_pow_mul (N s : ℕ) (hs : s ≤ N) (Q : R[X]) :
    tauL N (X ^ s * Q) = tauL (N - s) Q := by
  rw [tauL_apply, tauL_apply, show N + 1 = s + (N - s + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero, zero_add]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_X_pow_mul', if_pos (by omega), show s + j - s = j by omega,
      show N - (s + j) = N - s - j by omega]
  · intro j hj
    rw [coeff_X_pow_mul', if_neg (by simp at hj; omega), C_0, zero_mul]

lemma tauL_X_pow (N l : ℕ) (hl : l ≤ N) : tauL N (X ^ l : R[X]) = (1 - X) ^ (N - l) := by
  have := tauL_X_pow_mul (R := R) N l hl 1
  rw [mul_one] at this
  rw [this, tauL_apply, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [coeff_one, if_neg hj, C_0, zero_mul]
  · simp

lemma tauL_one_sub_X_pow (N a : ℕ) (ha : a ≤ N) :
    tauL N ((1 - X : R[X]) ^ a) = (1 - X) ^ (N - a) * (-X) ^ a := by
  rw [tauL_apply, show N + 1 = (a + 1) + (N - a) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := range (N - a)), add_zero]
  · have : (-X : R[X]) = (-1) + (1 - X) := by ring
    rw [this, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp at hi
    rw [coeff_one_sub_X_pow, show N - i = (N - a) + (a - i) by omega, pow_add]
    simp only [C_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  · intro j _
    rw [coeff_one_sub_X_pow, Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma tauL_cube_X_pow (N l : ℕ) (hl : l ≤ N) :
    tauL N (tauL N (tauL N (X ^ l : R[X]))) = (-1 : R) ^ N • X ^ l := by
  rw [tauL_X_pow N l hl, tauL_one_sub_X_pow N (N - l) (by omega),
    show N - (N - l) = l by omega]
  have h1 : ((1 - X : R[X]) ^ l * (-X) ^ (N - l)) =
      ((-1 : R) ^ (N - l)) • (X ^ (N - l) * (1 - X) ^ l) := by
    rw [smul_eq_C_mul, neg_pow]; simp; ring
  rw [h1, map_smul, tauL_X_pow_mul N (N - l) (by omega), show N - (N - l) = l by omega,
    tauL_one_sub_X_pow l l le_rfl, Nat.sub_self, pow_zero, one_mul]
  simp only [smul_eq_C_mul, neg_pow (X : R[X]), map_pow, map_neg, map_one]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hl]

/-- `τ³ = (-1)^N` on polynomials of degree `≤ N`. -/
lemma tauL_cube (N : ℕ) (P : R[X]) (hP : P ∈ degreeLT R (N + 1)) :
    tauL N (tauL N (tauL N P)) = (-1 : R) ^ N • P := by
  have hdeg : P.degree < (N + 1 : ℕ) := mem_degreeLT.mp hP
  have hsum : P = ∑ l ∈ range (N + 1), P.coeff l • (X ^ l : R[X]) := by
    conv_lhs => rw [as_sum_range' P (N + 1) (by
      rcases eq_or_ne P 0 with h | h
      · simp [h]
      · rw [degree_eq_natDegree h] at hdeg; exact_mod_cast hdeg)]
    simp [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
  rw [hsum]
  simp only [map_sum, map_smul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp at hl
  rw [tauL_cube_X_pow N l (by omega), smul_comm]

/-- Forward fact 1: if the first `d` coefficients of `P` vanish, `deg τ P < N + 1 - d`. -/
lemma tauL_mem_of_coeff (N d : ℕ) (P : R[X]) (h : ∀ j < d, P.coeff j = 0) :
    tauL N P ∈ degreeLT R (N + 1 - d) := by
  rw [tauL_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  simp at hi
  by_cases hid : i < d
  · rw [h i hid, C_0, zero_mul]; exact Submodule.zero_mem _
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (one_sub_X_pow_mem _ _ (by omega))

/-- Forward fact 2: if `deg P < N + 1 - e`, then `(1 - t)^e ∣ τ P`. -/
lemma dvd_tauL_of_mem (N e : ℕ) (he : e ≤ N + 1) (P : R[X]) (h : P ∈ degreeLT R (N + 1 - e)) :
    (1 - X) ^ e ∣ tauL N P := by
  rw [tauL_apply]
  refine Finset.dvd_sum fun i hi => ?_
  simp at hi
  by_cases hie : N + 1 - e ≤ i
  · rw [mem_degreeLT, degree_lt_iff_coeff_zero] at h
    rw [h i hie, C_0, zero_mul]; exact dvd_zero _
  · exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _

/-- The matrix `tau m` acts on coefficient vectors as `tauL (m-1)`. -/
lemma toPoly_tau_mulVec (m : ℕ) (hm : 0 < m) (v : Fin m → R) :
    toPoly ((tau m).map (Int.cast : ℤ → R) *ᵥ v) = tauL (m - 1) (toPoly v) := by
  ext j
  rw [coeff_toPoly, tauL_apply, finset_sum_coeff, Nat.sub_add_cancel hm, Finset.sum_range]
  simp only [coeff_C_mul, coeff_one_sub_X_pow, coeff_toPoly, Fin.is_lt, dif_pos, Fin.eta]
  split_ifs with h
  · simp only [mulVec, dotProduct, map_apply, tau]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  · symm
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

end Poly

section Kernel

variable {F : Type*} [Field F]

/-- **Frame kernel** (proof of `thm:t0`, frame part): over a field, if the first `d0, d1, d2`
digits of `τ²V, V, τV` vanish (`d0 + d1 + d2 = m`), then `V = 0`.  Indeed `t^{d1} ∣ V`,
`(1-t)^{d2} ∣ V` (since `V = ±τ(τ²V)` and `deg τ²V < m - d2`), and `deg V < d1 + d2`
(since `V = ±τ(τ²V)` and the first `d0` coefficients of `τ²V` vanish). -/
theorem frame_kernel (m : ℕ) (hm : 0 < m) (v : Fin m → F) (d0 d1 d2 : ℕ)
    (hd : d0 + d1 + d2 = m)
    (h0 : ∀ i : Fin m, (i : ℕ) < d0 →
      ((tau m).map (Int.cast : ℤ → F) *ᵥ ((tau m).map (Int.cast : ℤ → F) *ᵥ v)) i = 0)
    (h1 : ∀ i : Fin m, (i : ℕ) < d1 → v i = 0)
    (h2 : ∀ i : Fin m, (i : ℕ) < d2 → ((tau m).map (Int.cast : ℤ → F) *ᵥ v) i = 0) :
    v = 0 := by
  set N := m - 1 with hN
  have hmN : N + 1 = m := by omega
  set V := toPoly v with hVdef
  have hW : toPoly ((tau m).map (Int.cast : ℤ → F) *ᵥ v) = tauL N V := toPoly_tau_mulVec m hm v
  have hZ : toPoly ((tau m).map (Int.cast : ℤ → F) *ᵥ ((tau m).map (Int.cast : ℤ → F) *ᵥ v)) =
      tauL N (tauL N V) := by rw [toPoly_tau_mulVec m hm, hW]
  have hVmem : V ∈ degreeLT F (N + 1) := by rw [hmN]; exact toPoly_mem v
  have hcube := tauL_cube N V hVmem
  have hVeq : V = (-1 : F) ^ N • tauL N (tauL N (tauL N V)) := by
    rw [hcube, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  have cZ : ∀ j < d0, (tauL N (tauL N V)).coeff j = 0 := by
    intro j hj
    rw [← hZ, coeff_toPoly, dif_pos (by omega)]
    exact h0 ⟨j, by omega⟩ hj
  have cW : ∀ j < d2, (tauL N V).coeff j = 0 := by
    intro j hj
    rw [← hW, coeff_toPoly, dif_pos (by omega)]
    exact h2 ⟨j, by omega⟩ hj
  have cV : ∀ j < d1, V.coeff j = 0 := by
    intro j hj
    rw [hVdef, coeff_toPoly, dif_pos (by omega)]
    exact h1 ⟨j, by omega⟩ hj
  have hdegV : V ∈ degreeLT F (N + 1 - d0) := by
    rw [hVeq]; exact Submodule.smul_mem _ _ (tauL_mem_of_coeff N d0 _ cZ)
  have hZmem : tauL N (tauL N V) ∈ degreeLT F (N + 1 - d2) := tauL_mem_of_coeff N d2 _ cW
  have hdvd2 : (1 - X) ^ d2 ∣ V := by
    rw [hVeq, smul_eq_C_mul]
    exact Dvd.dvd.mul_left (dvd_tauL_of_mem N d2 (by omega) _ hZmem) _
  have hdvd1 : X ^ d1 ∣ V := X_pow_dvd_iff.mpr cV
  have hcop : IsCoprime ((X : F[X]) ^ d1) ((1 - X) ^ d2) :=
    (show IsCoprime (X : F[X]) (1 - X) from ⟨1, 1, by ring⟩).pow
  have hdvd := hcop.mul_dvd hdvd1 hdvd2
  have h1X : (1 - X : F[X]).degree = 1 := by
    rw [show (1 - X : F[X]) = -(X - C 1) by simp, degree_neg, degree_X_sub_C]
  have hV0 : V = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hdvd
    rw [degree_mul, degree_X_pow, degree_pow, h1X, nsmul_one]
    have := mem_degreeLT.mp hdegV
    rw [show N + 1 - d0 = d1 + d2 by omega] at this
    exact_mod_cast this
  exact toPoly_injective v hV0

end Kernel

end Z3Net.Proofs

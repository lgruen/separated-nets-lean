/-
Proof module (stage 6, main entry): `prop:faure`, the frame is the Faure–Hammersley net.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.NetPoly

@[expose] public section

/-!
# `prop:faure`

On coefficient vectors (`toPoly`): `P` is `V(t) ↦ V(t+1)`, `D_±` is `V(t) ↦ V(-t)`, column `j` of
`Λ_m` is `t^j (1-t)^(m-1-j)` and `J` reverses. Then `τ = Λ_m P` is the binomial theorem
`∑_j C(l,j) t^j (1-t)^(l-j) = 1`, `τ² = D_± J P` is `∑_j C(l,j) (-t)^(m-1-j) = (-t)^(m-1-l)(1-t)^l`,
and `(D_± P)² = I` because `V(t) ↦ V(-t-1)` is an involution.
-/

namespace Z3Net.Proofs

open Matrix Finset Polynomial

noncomputable section

namespace Faure

lemma toPoly_inj {m : ℕ} {u v : Fin m → ℤ} (h : toPoly u = toPoly v) : u = v := by
  funext i
  have := congrArg (fun P => P.coeff i) h
  simpa [coeff_toPoly] using this

lemma toPoly_mulVec (m : ℕ) (A : Matrix (Fin m) (Fin m) ℤ) (v : Fin m → ℤ) :
    toPoly (A *ᵥ v) = ∑ j : Fin m, C (v j) * toPoly (fun i => A i j) := by
  unfold toPoly
  simp only [mulVec, dotProduct, map_sum, Finset.sum_mul, Finset.mul_sum, C_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

lemma toPoly_single (m : ℕ) (j : Fin m) (c : ℤ) : toPoly (Pi.single j c : Fin m → ℤ) = C c * X ^ (j : ℕ) := by
  unfold toPoly
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

lemma col_Lam (m : ℕ) (j : Fin m) :
    toPoly (fun i => LamF m i j) = X ^ (j : ℕ) * (1 - X) ^ (m - 1 - (j : ℕ)) := by
  ext n
  rw [coeff_toPoly, coeff_X_pow_mul', coeff_one_sub_X_pow]
  split_ifs with h1 h2 h2
  · simp only [LamF]
    rw [if_pos (show j ≤ (⟨n, h1⟩ : Fin m) from h2)]
  · simp only [LamF]
    rw [if_neg (show ¬ j ≤ (⟨n, h1⟩ : Fin m) from h2)]
  · have := j.isLt
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · rfl

lemma col_P (m : ℕ) (l : Fin m) :
    toPoly (fun i => pascalP m i l) = (X + 1) ^ (l : ℕ) := by
  ext n
  rw [coeff_toPoly, coeff_X_add_one_pow]
  split_ifs with h
  · simp [pascalP]
  · have := l.isLt
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma sum_binom (m l : ℕ) (hl : l < m) :
    ∑ j : Fin m, C ((l.choose j : ℕ) : ℤ) * (X ^ (j : ℕ) * (1 - X : ℤ[X]) ^ (m - 1 - (j : ℕ))) =
      (1 - X) ^ (m - 1 - l) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => C ((l.choose j : ℕ) : ℤ) *
    (X ^ j * (1 - X : ℤ[X]) ^ (m - 1 - j))), show m = (l + 1) + (m - (l + 1)) by omega,
    Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := range (m - (l + 1))), add_zero]
  · have hb : (1 : ℤ[X]) = (X + (1 - X)) ^ l := by ring
    rw [show l + 1 + (m - (l + 1)) - 1 - l = m - 1 - l by omega]
    calc ∑ j ∈ range (l + 1), C ((l.choose j : ℕ) : ℤ) * (X ^ j * (1 - X) ^ (l + 1 + (m - (l + 1)) - 1 - j))
        = (1 - X) ^ (m - 1 - l) * ∑ j ∈ range (l + 1), X ^ j * (1 - X) ^ (l - j) * (l.choose j : ℤ[X]) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp at hj
          rw [show l + 1 + (m - (l + 1)) - 1 - j = (m - 1 - l) + (l - j) by omega, pow_add]
          simp only [map_natCast]
          ring
      _ = (1 - X) ^ (m - 1 - l) := by rw [← add_pow, ← hb, mul_one]
  · intro j _
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem faure_tau (m : ℕ) (hm : 1 ≤ m) : tau m = LamF m * pascalP m := by
  apply Matrix.ext_of_mulVec_single
  intro l
  apply toPoly_inj
  have h1 := toPoly_tau_mulVec (R := ℤ) m (by omega) (Pi.single l 1)
  have hmap : (tau m).map (Int.cast : ℤ → ℤ) = tau m := by ext; simp
  rw [hmap] at h1
  rw [h1, toPoly_single, map_one, one_mul, tauL_X_pow _ _ (by have := l.isLt; omega),
    ← mulVec_mulVec, toPoly_mulVec]
  have : pascalP m *ᵥ Pi.single l 1 = fun i => pascalP m i l := by
    ext i; simp [mulVec, dotProduct, Pi.single_apply]
  rw [this]
  simp only [col_Lam, pascalP]
  rw [sum_binom m l l.isLt]

lemma neg_X_pow_coeff (e n : ℕ) :
    ((-X : ℤ[X]) ^ e).coeff n = if n = e then (-1) ^ e else 0 := by
  rw [_root_.neg_pow, show ((-1 : ℤ[X]) ^ e) = C ((-1) ^ e) by simp, coeff_C_mul_X_pow]

lemma col_DJ (m : ℕ) (j : Fin m) :
    toPoly (fun i => (Dpm m * Jrev m) i j) = (-X : ℤ[X]) ^ (m - 1 - (j : ℕ)) := by
  ext n
  rw [coeff_toPoly, neg_X_pow_coeff]
  have hj := j.isLt
  split_ifs with h1 h2 h2
  · rw [Dpm, diagonal_mul]
    unfold Jrev
    rw [if_pos (by simp only; omega), mul_one]
    show (-1 : ℤ) ^ n = _
    rw [h2]
  · rw [Dpm, diagonal_mul]
    unfold Jrev
    rw [if_neg (by simp only; omega), mul_zero]
  · omega
  · rfl

lemma toPoly_D (m : ℕ) (v : Fin m → ℤ) : toPoly (Dpm m *ᵥ v) = (toPoly v).comp (-X) := by
  unfold toPoly
  rw [Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Dpm, mulVec_diagonal, mul_comp, C_comp, X_pow_comp, _root_.neg_pow (X : ℤ[X]), C_mul]
  simp only [map_pow, map_neg, map_one]
  ring

lemma toPoly_P (m : ℕ) (v : Fin m → ℤ) : toPoly (pascalP m *ᵥ v) = (toPoly v).comp (X + 1) := by
  rw [toPoly_mulVec]
  have h := fun i => col_P m i
  simp only [h]
  unfold toPoly
  rw [Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem faure_DP (m : ℕ) : (Dpm m * pascalP m) * (Dpm m * pascalP m) = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro l
  apply toPoly_inj
  rw [one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    toPoly_D, toPoly_P, toPoly_D, toPoly_P, comp_assoc, comp_assoc, comp_assoc]
  simp

theorem faure_tau2 (m : ℕ) (hm : 1 ≤ m) : tau m ^ 2 = Dpm m * Jrev m * pascalP m := by
  apply Matrix.ext_of_mulVec_single
  intro l
  apply toPoly_inj
  have hl := l.isLt
  have hmap : (tau m).map (Int.cast : ℤ → ℤ) = tau m := by ext; simp
  have h1 := fun v => toPoly_tau_mulVec (R := ℤ) m (by omega) v
  rw [hmap] at h1
  rw [pow_two, ← mulVec_mulVec, h1, h1, toPoly_single, map_one, one_mul,
    tauL_X_pow _ _ (by omega), tauL_one_sub_X_pow _ _ (by omega),
    show m - 1 - (m - 1 - (l : ℕ)) = l by omega]
  rw [← mulVec_mulVec, toPoly_mulVec]
  have : pascalP m *ᵥ Pi.single l 1 = fun i => pascalP m i l := by
    ext i; simp [mulVec, dotProduct, Pi.single_apply]
  rw [this]
  simp only [col_DJ, pascalP]
  rw [Fin.sum_univ_eq_sum_range (fun j => C ((((l : ℕ).choose j : ℕ) : ℤ)) * (-X : ℤ[X]) ^ (m - 1 - j))]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show (l : ℕ) + 1 ≤ m by omega))
    (fun j hj hj' => by
      simp at hj hj'
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
  have hb : (1 - X : ℤ[X]) ^ (l : ℕ) = ∑ j ∈ range ((l : ℕ) + 1),
      1 ^ j * (-X) ^ ((l : ℕ) - j) * (((l : ℕ).choose j : ℕ) : ℤ[X]) := by
    rw [← add_pow]; ring
  rw [hb, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp at hj
  rw [show m - 1 - j = (m - 1 - (l : ℕ)) + ((l : ℕ) - j) by omega, pow_add]
  simp only [map_natCast, one_pow, one_mul]
  ring

lemma D_sq (m : ℕ) : Dpm m * Dpm m = 1 := by
  rw [Dpm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i
  rw [← pow_add, ← two_mul, pow_mul]; simp

lemma PDP (m : ℕ) : pascalP m * Dpm m * pascalP m = Dpm m := by
  have h := faure_DP m
  calc pascalP m * Dpm m * pascalP m = (Dpm m * Dpm m) * (pascalP m * Dpm m * pascalP m) := by
        rw [D_sq, Matrix.one_mul]
    _ = Dpm m * ((Dpm m * pascalP m) * (Dpm m * pascalP m)) := by
        simp only [Matrix.mul_assoc]
    _ = Dpm m := by rw [h, Matrix.mul_one]

lemma DJD (m : ℕ) : Dpm m * Jrev m * Dpm m = (-1 : ℤ) ^ (m - 1) • Jrev m := by
  ext i j
  rw [Dpm, mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  unfold Jrev
  split_ifs with h
  · rw [mul_one, ← pow_add, show m - 1 = (i : ℕ) + j by omega, mul_one]
  · simp

theorem faure_reindex (k : ℕ) (hk : 1 ≤ k) (L : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ) :
    L * T k ^ 2 * (Dpm (3 * k) * pascalP (3 * k)) = (-1 : ℤ) ^ (3 * k - 1) • (L * Jrev (3 * k)) ∧
      L * (Dpm (3 * k) * pascalP (3 * k)) = L * Dpm (3 * k) * pascalP (3 * k) ∧
      L * T k * (Dpm (3 * k) * pascalP (3 * k)) =
        (-1 : ℤ) ^ (k + 1) • (L * LamF (3 * k) * Dpm (3 * k)) := by
  have hT2 : T k ^ 2 = tau (3 * k) ^ 2 := by
    rw [T, _root_.smul_pow, ← pow_mul, show (k + 1) * 2 = 2 * (k + 1) by ring, pow_mul]; simp
  refine ⟨?_, by rw [Matrix.mul_assoc], ?_⟩
  · rw [hT2, faure_tau2 _ (by omega)]
    calc L * (Dpm (3 * k) * Jrev (3 * k) * pascalP (3 * k)) * (Dpm (3 * k) * pascalP (3 * k))
        = L * (Dpm (3 * k) * Jrev (3 * k) * (pascalP (3 * k) * Dpm (3 * k) * pascalP (3 * k))) := by
          simp only [Matrix.mul_assoc]
      _ = L * (Dpm (3 * k) * Jrev (3 * k) * Dpm (3 * k)) := by rw [PDP]
      _ = _ := by rw [DJD, Matrix.mul_smul]
  · rw [T, Matrix.mul_smul, Matrix.smul_mul, faure_tau _ (by omega)]
    congr 1
    calc L * (LamF (3 * k) * pascalP (3 * k)) * (Dpm (3 * k) * pascalP (3 * k))
        = L * LamF (3 * k) * (pascalP (3 * k) * Dpm (3 * k) * pascalP (3 * k)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [PDP]

theorem faure_Lam (m : ℕ) : (∀ i, LamF m i i = 1) ∧ ∀ i j, i < j → LamF m i j = 0 := by
  refine ⟨fun i => by simp [LamF], fun i j h => ?_⟩
  simp only [LamF]
  rw [if_neg (not_le.mpr h)]

end Faure

end

end Z3Net.Proofs

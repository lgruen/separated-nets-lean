/-
Separation bound of Theorem `thm:sep`: bridge between the generator matrices of
Definition `def:net` and the polynomial model of `Z3Net.SepPoly`.
-/
module
public import Z3Net.Defs
public import Z3Net.SepPoly

@[expose] public section

/-!
# Matrices ↔ polynomials

For `v : Fin m → R` put `toP v = ∑ v_i t^i`. Then

* `toP (τ v) = tauP (m-1) (toP v)` (`toP_tau`);
* `(K v)_j = kap k j (toP v)` (`K_mulVec`);
* `(L v)_j = Ldig k j (toP v)` (`L_mulVec`), where `Ldig` applies the three special rows of `E`;
* the digits of the three coordinates of `𝒫_{k,q}` are `Ldig` of `τ²V`, `V`, `s_k τV`
  (`Dg0`, `Dg1`, `Dg2`).
-/

namespace Z3Net.Sep

open Polynomial Matrix

variable {R : Type*} [CommRing R]

theorem coeff_one_sub_X_pow (n j : ℕ) :
    ((1 - X : R[X]) ^ n).coeff j = (-1) ^ j * (n.choose j : R) := by
  have h : (1 - X : R[X]) ^ n = C ((-1) ^ n) * (X + C (-1)) ^ n := by
    rw [C_pow, ← mul_pow]; congr 1; simp; ring
  rw [h, coeff_C_mul, coeff_X_add_C_pow]
  rcases le_or_gt j n with hj | hj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← mul_assoc ((-1 : R) ^ d), ← pow_add,
      ← two_mul, pow_mul]
    simp
  · simp [Nat.choose_eq_zero_of_lt hj]

/-! ## Coefficient vectors as polynomials -/

/-- `toP v = ∑ v_i t^i`. -/
noncomputable def toP {m : ℕ} (v : Fin m → R) : R[X] := ∑ i : Fin m, C (v i) * X ^ (i : ℕ)

theorem coeff_toP {m : ℕ} (v : Fin m → R) (j : ℕ) :
    (toP v).coeff j = if h : j < m then v ⟨j, h⟩ else 0 := by
  simp only [toP, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hh; apply hb; ext; exact hh.symm
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [if_neg, mul_zero]
    omega

theorem coeff_toP_fin {m : ℕ} (v : Fin m → R) (j : Fin m) : (toP v).coeff j = v j := by
  rw [coeff_toP, dif_pos j.isLt]

theorem natDegree_toP_le {m : ℕ} (v : Fin m → R) : (toP v).natDegree ≤ m - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact le_trans (natDegree_C_mul_X_pow_le _ _) (by omega)

theorem toP_sub {m : ℕ} (v w : Fin m → R) : toP (v - w) = toP v - toP w := by
  simp [toP, Finset.sum_sub_distrib, sub_mul]

theorem toP_smul {m : ℕ} (c : R) (v : Fin m → R) : toP (c • v) = C c * toP v := by
  simp [toP, Finset.mul_sum, mul_assoc]

theorem toP_injective {m : ℕ} {v w : Fin m → R} (h : toP v = toP w) : v = w := by
  funext j
  rw [← coeff_toP_fin v j, ← coeff_toP_fin w j, h]

theorem toP_eq_zero {m : ℕ} {v : Fin m → R} (h : toP v = 0) : v = 0 := by
  apply toP_injective
  rw [h]; simp [toP]

/-! ## `τ` -/

theorem tauP_toP {m : ℕ} (v : Fin m → R) :
    tauP (m - 1) (toP v) = ∑ i : Fin m, C (v i) * (1 - X) ^ (m - 1 - (i : ℕ)) := by
  rw [toP, tauP_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tauP_C_mul, tauP_X_pow (by omega)]

theorem toP_tau (m : ℕ) (v : Fin m → R) :
    toP ((tau m).map (Int.cast : ℤ → R) *ᵥ v) = tauP (m - 1) (toP v) := by
  rw [tauP_toP]
  ext j
  rw [coeff_toP, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_one_sub_X_pow]
  split_ifs with h
  · simp only [mulVec, dotProduct, map_apply, tau]
    apply Finset.sum_congr rfl
    intro l _
    push_cast
    ring
  · symm
    apply Finset.sum_eq_zero
    intro l _
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-! ## `K` -/

theorem K_mulVec (k : ℕ) (hk : 1 ≤ k) (v : Fin (3 * k) → R) (j : Fin (3 * k)) :
    ((K k).map (Int.cast : ℤ → R) *ᵥ v) j = kap k j (toP v) := by
  unfold kap
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos R k (by omega),
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (toP v : PowerSeries R) *
        PowerSeries.coeff b (PowerSeries.mk fun n => (((k - 1 + n).choose (k - 1) : ℕ) : R)))]
  simp only [coeff_coe, PowerSeries.coeff_mk]
  simp only [mulVec, dotProduct, map_apply, K]
  have hv : ∀ l : Fin (3 * k), v l = (toP v).coeff l := fun l => (coeff_toP_fin v l).symm
  let g : ℕ → R := fun l =>
    (if l ≤ (j : ℕ) then (((j : ℕ) - l + k - 1).choose (k - 1) : R) else 0) * (toP v).coeff l
  have hL : ∑ l : Fin (3 * k), ((if l ≤ j then ((((j : ℕ) - l + k - 1).choose (k - 1) : ℕ) : ℤ)
      else 0 : ℤ) : R) * v l = ∑ l ∈ Finset.range (3 * k), g l := by
    rw [← Fin.sum_univ_eq_sum_range g]
    apply Finset.sum_congr rfl
    intro l _
    simp only [g, hv l, Fin.le_iff_val_le_val]
    split_ifs <;> simp
  rw [hL]
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range (3 * k) := by
    intro x hx; simp at hx ⊢; omega
  rw [← Finset.sum_subset hsub (fun x _ hx => by
    simp only [Finset.mem_range, not_lt] at hx
    simp only [g]; rw [if_neg (by omega), zero_mul])]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Finset.mem_range] at hl
  simp only [g]
  rw [if_pos (by omega), mul_comm]
  congr 3
  omega

/-! ## `E` and `L = E K` -/

theorem map_cast_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) :
    (A * B).map (Int.cast : ℤ → R) = A.map Int.cast * B.map Int.cast := by
  ext i j; simp [Matrix.mul_apply]

/-- Digit `j` of `L e(W)`: the rows `k-2, k-1, k` of `E` applied to the `K`-digits. -/
noncomputable def Ldig (k j : ℕ) (W : R[X]) : R :=
  if j + 2 = k then ∑ i ∈ Finset.range (k - 1), kap k i W
  else if j + 1 = k then -kap k j W
  else if j = k then kap k (k - 1) W + kap k k W
  else kap k j W

theorem E_mulVec (k : ℕ) (hk : 2 ≤ k) (w : Fin (3 * k) → R) (j : Fin (3 * k)) (f : ℕ → R)
    (hf : ∀ i : Fin (3 * k), w i = f i) :
    ((E k).map (Int.cast : ℤ → R) *ᵥ w) j =
      if (j : ℕ) + 2 = k then ∑ i ∈ Finset.range (k - 1), f i
      else if (j : ℕ) + 1 = k then -f j
      else if (j : ℕ) = k then f (k - 1) + f k
      else f j := by
  simp only [mulVec, dotProduct, map_apply, E]
  by_cases h2 : (j : ℕ) + 2 = k
  · rw [if_pos h2]
    simp only [if_pos h2]
    rw [show (∑ x : Fin (3 * k), ((if (x : ℕ) + 2 ≤ k then 1 else 0 : ℤ) : R) * w x) =
        ∑ x ∈ Finset.range (3 * k), (if x + 2 ≤ k then f x else 0) by
      rw [← Fin.sum_univ_eq_sum_range (fun x => if x + 2 ≤ k then f x else 0)]
      apply Finset.sum_congr rfl; intro x _; rw [hf]; split_ifs <;> simp]
    have hsub : Finset.range (k - 1) ⊆ Finset.range (3 * k) := by
      intro x hx; simp at hx ⊢; omega
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      simp only [Finset.mem_range, not_lt] at hx; rw [if_neg (by omega)])]
    apply Finset.sum_congr rfl
    intro x hx; simp only [Finset.mem_range] at hx; rw [if_pos (by omega)]
  rw [if_neg h2]; simp only [if_neg h2]
  by_cases h1 : (j : ℕ) + 1 = k
  · rw [if_pos h1]; simp only [if_pos h1]
    rw [Finset.sum_eq_single j]
    · simp [hf]
    · intro b _ hb; rw [if_neg hb]; simp
    · simp
  rw [if_neg h1]; simp only [if_neg h1]
  by_cases h0 : (j : ℕ) = k
  · rw [if_pos h0]; simp only [if_pos h0]
    rw [Finset.sum_eq_add (⟨k - 1, by omega⟩ : Fin (3 * k)) ⟨k, by omega⟩]
    · simp only [hf]
      have : k - 1 + 1 = k := by omega
      simp [this]
    · intro h; have := congrArg Fin.val h; simp at this; omega
    · intro c _ hc
      rw [if_neg, Int.cast_zero, zero_mul]
      rintro (h | h)
      · exact hc.1 (Fin.ext (by simp; omega))
      · exact hc.2 (Fin.ext h)
    · simp
    · simp
  rw [if_neg h0]; simp only [if_neg h0]
  rw [Finset.sum_eq_single j]
  · simp [hf]
  · intro b _ hb; rw [if_neg hb]; simp
  · simp

theorem L_mulVec (k : ℕ) (hk : 2 ≤ k) (v : Fin (3 * k) → R) (j : Fin (3 * k)) :
    ((L k).map (Int.cast : ℤ → R) *ᵥ v) j = Ldig k j (toP v) := by
  rw [L, map_cast_mul, ← mulVec_mulVec,
    E_mulVec k hk _ j (fun i => kap k i (toP v)) (K_mulVec k (by omega) v)]
  simp only [Ldig]

/-! ## The three readings -/

/-- `s_k = (-1)^(k+1)`. -/
def sk (k : ℕ) : R := (-1) ^ (k + 1)

theorem sk_mul_sk (k : ℕ) : (sk k : R) * sk k = 1 := by
  rw [sk, ← pow_add, ← two_mul, pow_mul]; simp

theorem T_map (k : ℕ) : (T k).map (Int.cast : ℤ → R) = (sk k : R) • (tau (3 * k)).map Int.cast := by
  ext i j; simp only [T, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, sk]; push_cast; ring

theorem toP_T (k : ℕ) (v : Fin (3 * k) → R) :
    toP ((T k).map (Int.cast : ℤ → R) *ᵥ v) = C (sk k) * tauP (3 * k - 1) (toP v) := by
  rw [T_map, smul_mulVec, toP_smul, toP_tau]

/-- Digit vector of coordinate `c` of `𝒫_{k,q}` (over any commutative ring). -/
noncomputable def Dg (k : ℕ) (c : Fin 3) (v : Fin (3 * k) → R) : Fin (3 * k) → R :=
  ((PGen k c).map (Int.cast : ℤ → R)) *ᵥ v

theorem Dg1 (k : ℕ) (hk : 2 ≤ k) (v : Fin (3 * k) → R) (j : Fin (3 * k)) :
    Dg k 1 v j = Ldig k j (toP v) := by
  simp only [Dg, PGen, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact L_mulVec k hk v j

theorem Dg2 (k : ℕ) (hk : 2 ≤ k) (v : Fin (3 * k) → R) (j : Fin (3 * k)) :
    Dg k 2 v j = Ldig k j (C (sk k) * tauP (3 * k - 1) (toP v)) := by
  simp only [Dg, PGen]
  rw [show (![L k * T k ^ 2, L k, L k * T k] : Fin 3 → Matrix _ _ ℤ) 2 = L k * T k from rfl,
    map_cast_mul, ← mulVec_mulVec, L_mulVec k hk, toP_T]

theorem Dg0 (k : ℕ) (hk : 2 ≤ k) (v : Fin (3 * k) → R) (j : Fin (3 * k)) :
    Dg k 0 v j = Ldig k j (tauP (3 * k - 1) (tauP (3 * k - 1) (toP v))) := by
  simp only [Dg, PGen, Matrix.cons_val_zero]
  rw [map_cast_mul, pow_two, map_cast_mul, ← mulVec_mulVec, ← mulVec_mulVec, L_mulVec k hk,
    toP_T, toP_T, tauP_C_mul, ← mul_assoc, ← C_mul, sk_mul_sk, C_1, one_mul]

end Z3Net.Sep

/-
Separation bound of Theorem `thm:sep`: Proposition `prop:cell` at the level of the digit
vectors of `𝒫_{k,q}` (all three coordinates, via the cyclic symmetry `T³ = 1`).
-/
module
public import Z3Net.SepCell

@[expose] public section

/-!
# `prop:cell` for the digit vectors

`Dg k c v` is the digit vector of coordinate `c` (generator `(PGen k c)` reduced to `R`).

* `Dg_rot`: `Dg c (T v) = Dg (c+1) v` (the frame is cyclic, `T³ = 1`);
* `Dg_geo`: (a) and (c): `d^c_k = -d^c_{k-1} - d^{c+1}_{k-1} + d^{c+2}_{k-1} - d^{c+2}_{k-2}`;
* `Dg_jit`: (b) and (c): the digits `j > k` of coordinate `c` depend only on the cells of
  `c+1, c+2`;
* `Dg_inj`: the three cells determine the index (the `(k,k,k)` box of `thm:t0`).
-/

namespace Z3Net.Sep

open Polynomial Matrix

variable {R : Type*} [CommRing R] [Nontrivial R]

omit [Nontrivial R] in
theorem sk_mul_neg_one_pow (k : ℕ) (hk : 1 ≤ k) : (sk k : R) * (-1) ^ (3 * k - 1) = 1 := by
  rw [sk, ← pow_add, show k + 1 + (3 * k - 1) = 2 * (2 * k) by omega, pow_mul]; simp

omit [Nontrivial R] in
theorem Dg_rot (k : ℕ) (hk : 2 ≤ k) (c : Fin 3) (v : Fin (3 * k) → R) (j : Fin (3 * k)) :
    Dg k c ((T k).map (Int.cast : ℤ → R) *ᵥ v) j = Dg k (c + 1) v j := by
  have hV := natDegree_toP_le v
  fin_cases c
  · show Dg k 0 _ j = Dg k 1 v j
    rw [Dg0 k hk, Dg1 k hk, toP_T, tauP_C_mul, tauP_C_mul, tauP_cube hV, ← mul_assoc, ← C_mul,
      sk_mul_neg_one_pow k (by omega), C_1, one_mul]
  · show Dg k 1 _ j = Dg k 2 v j
    rw [Dg1 k hk, Dg2 k hk, toP_T]
  · show Dg k 2 _ j = Dg k 0 v j
    rw [Dg2 k hk, Dg0 k hk, toP_T, tauP_C_mul, ← mul_assoc, ← C_mul, sk_mul_sk, C_1, one_mul]

/-- (a) of `prop:cell` for the `x`-coordinate. -/
theorem Dg_geo0 (k : ℕ) (hk : 2 ≤ k) (v : Fin (3 * k) → R) :
    Dg k 0 v ⟨k, by omega⟩ = -Dg k 0 v ⟨k - 1, by omega⟩ - Dg k 1 v ⟨k - 1, by omega⟩
      + Dg k 2 v ⟨k - 1, by omega⟩ - Dg k 2 v ⟨k - 2, by omega⟩ := by
  rw [Dg0 k hk, Dg0 k hk, Dg1 k hk, Dg2 k hk, Dg2 k hk]
  exact cell_a k hk (toP v) (natDegree_toP_le v)

/-- (a) + (c) of `prop:cell`. -/
theorem Dg_geo (k : ℕ) (hk : 2 ≤ k) (c : Fin 3) (v : Fin (3 * k) → R) :
    Dg k c v ⟨k, by omega⟩ = -Dg k c v ⟨k - 1, by omega⟩ - Dg k (c + 1) v ⟨k - 1, by omega⟩
      + Dg k (c + 2) v ⟨k - 1, by omega⟩ - Dg k (c + 2) v ⟨k - 2, by omega⟩ := by
  set Tm := (T k).map (Int.cast : ℤ → R)
  fin_cases c
  · exact Dg_geo0 k hk v
  · have h := Dg_geo0 k hk (Tm *ᵥ v)
    simp only [Tm, Dg_rot k hk] at h
    exact h
  · have h := Dg_geo0 k hk (Tm *ᵥ (Tm *ᵥ v))
    simp only [Tm, Dg_rot k hk] at h
    exact h

omit [Nontrivial R] in
theorem Dg_sub (k : ℕ) (c : Fin 3) (v w : Fin (3 * k) → R) :
    Dg k c (v - w) = Dg k c v - Dg k c w := by
  simp [Dg, mulVec_sub]

/-- (b) of `prop:cell` for the `x`-coordinate. -/
theorem Dg_jit0 (k : ℕ) (hk : 2 ≤ k) (v w : Fin (3 * k) → R)
    (hy : ∀ j : Fin (3 * k), (j : ℕ) < k → Dg k 1 v j = Dg k 1 w j)
    (hz : ∀ j : Fin (3 * k), (j : ℕ) < k → Dg k 2 v j = Dg k 2 w j) :
    ∀ j : Fin (3 * k), k < (j : ℕ) → Dg k 0 v j = Dg k 0 w j := by
  have hU := natDegree_toP_le (v - w)
  have h := cell_b k hk (toP (v - w)) hU
    (fun j hj => by
      have := hy ⟨j, by omega⟩ hj
      rw [← Dg1 k hk (v - w) ⟨j, by omega⟩, Dg_sub, Pi.sub_apply, this, sub_self])
    (fun j hj => by
      have := hz ⟨j, by omega⟩ hj
      rw [← Dg2 k hk (v - w) ⟨j, by omega⟩, Dg_sub, Pi.sub_apply, this, sub_self])
  intro j hj
  have := h.1 j (by omega)
  rw [← Ldig_gt k j hj, ← Dg0 k hk, Dg_sub, Pi.sub_apply, sub_eq_zero] at this
  exact this

/-- (b) + (c) of `prop:cell`. -/
theorem Dg_jit (k : ℕ) (hk : 2 ≤ k) (c : Fin 3) (v w : Fin (3 * k) → R)
    (h1 : ∀ j : Fin (3 * k), (j : ℕ) < k → Dg k (c + 1) v j = Dg k (c + 1) w j)
    (h2 : ∀ j : Fin (3 * k), (j : ℕ) < k → Dg k (c + 2) v j = Dg k (c + 2) w j) :
    ∀ j : Fin (3 * k), k < (j : ℕ) → Dg k c v j = Dg k c w j := by
  set Tm := (T k).map (Int.cast : ℤ → R)
  fin_cases c
  · exact Dg_jit0 k hk v w h1 h2
  · have h := Dg_jit0 k hk (Tm *ᵥ v) (Tm *ᵥ w)
    simp only [Tm, Dg_rot k hk] at h
    exact h h1 h2
  · have h := Dg_jit0 k hk (Tm *ᵥ (Tm *ᵥ v)) (Tm *ᵥ (Tm *ᵥ w))
    simp only [Tm, Dg_rot k hk] at h
    exact h h1 h2

/-- The cells determine the index. -/
theorem Dg_inj (k : ℕ) (hk : 2 ≤ k) (v w : Fin (3 * k) → R)
    (h : ∀ c : Fin 3, ∀ j : Fin (3 * k), (j : ℕ) < k → Dg k c v j = Dg k c w j) : v = w := by
  have hU := natDegree_toP_le (v - w)
  have low : ∀ c : Fin 3, ∀ j : Fin (3 * k), (j : ℕ) < k → Dg k c (v - w) j = 0 := by
    intro c j hj; rw [Dg_sub, Pi.sub_apply, h c j hj, sub_self]
  have hb := cell_b k hk (toP (v - w)) hU
    (fun j hj => by rw [← Dg1 k hk (v - w) ⟨j, by omega⟩]; exact low 1 _ hj)
    (fun j hj => by rw [← Dg2 k hk (v - w) ⟨j, by omega⟩]; exact low 2 _ hj)
  have h0 := hb.2 (fun j hj => by rw [← Dg0 k hk (v - w) ⟨j, by omega⟩]; exact low 0 _ hj)
  exact sub_eq_zero.mp (toP_eq_zero h0)

end Z3Net.Sep

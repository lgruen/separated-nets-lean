module
public import Z3Net.NetPoly

@[expose] public section

/-!
# The net property of `𝒫_{k,q}` (Theorem `thm:t0`, Theorem 1(1),(2))

* `L = E K` is lower-triangular with diagonal `±1`;
* every box matrix of `(L T², L, L T)` (any such `L`) has trivial kernel over every field
  (`frame_kernel` + `eq:scr`), hence every box minor over `ℤ` is `±1` (`P_boxMinor`);
* `P_net` by the Niederreiter-type lemma, `P_covering` from the `(k,k,k)` boxes.
-/

namespace Z3Net.Proofs

open Matrix Finset Polynomial

/-! ## The scramble `L` -/

lemma E_lower (k : ℕ) (i j : Fin (3 * k)) (h : i < j) : E k i j = 0 := by
  have h' : i.val < j.val := h
  unfold E
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> first | rfl | omega | (subst_vars; omega)

lemma K_lower (k : ℕ) (i j : Fin (3 * k)) (h : i < j) : K k i j = 0 := by
  unfold K
  rw [if_neg (not_le.mpr h)]

lemma L_lower (k : ℕ) (i j : Fin (3 * k)) (h : i < j) : L k i j = 0 := by
  unfold L
  rw [mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge i l with hil | hli
  · rw [E_lower k i l hil, zero_mul]
  · rw [K_lower k l j (lt_of_le_of_lt hli h), mul_zero]

lemma E_diag (k : ℕ) (i : Fin (3 * k)) : E k i i = 1 ∨ E k i i = -1 := by
  unfold E
  split_ifs <;> first | (left; rfl) | (right; rfl) | omega | simp_all

lemma K_diag (k : ℕ) (i : Fin (3 * k)) : K k i i = 1 := by
  unfold K
  rw [if_pos le_rfl]
  simp

lemma L_diag (k : ℕ) (i : Fin (3 * k)) : L k i i = 1 ∨ L k i i = -1 := by
  have : L k i i = E k i i * K k i i := by
    unfold L
    rw [mul_apply, Finset.sum_eq_single i]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [K_lower k l i h, mul_zero]
      · rw [E_lower k i l h, zero_mul]
    · simp
  rw [this, K_diag, mul_one]
  exact E_diag k i

/-! ## Box kernels of scrambled frames -/

section Field

variable {F : Type*} [Field F]

lemma map_mul_mulVec {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m → F) :
    (A * B).map (Int.cast : ℤ → F) *ᵥ v = A.map (Int.cast : ℤ → F) *ᵥ (B.map Int.cast *ᵥ v) := by
  rw [mulVec_mulVec]
  congr 1
  ext i j
  simp [mul_apply]

lemma T_map_mulVec (k : ℕ) (v : Fin (3 * k) → F) :
    (T k).map (Int.cast : ℤ → F) *ᵥ v =
      ((-1 : F) ^ (k + 1)) • ((tau (3 * k)).map (Int.cast : ℤ → F) *ᵥ v) := by
  rw [← smul_mulVec]
  congr 1
  ext i j
  simp only [T, map_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast; ring

lemma isUnit_map_diag {m : ℕ} (Lz : Matrix (Fin m) (Fin m) ℤ)
    (hdiag : ∀ i, Lz i i = 1 ∨ Lz i i = -1) (i : Fin m) :
    IsUnit (Lz.map (Int.cast : ℤ → F) i i) := by
  rw [map_apply]
  rcases hdiag i with h | h <;> rw [h] <;> simp

lemma map_lower {m : ℕ} (Lz : Matrix (Fin m) (Fin m) ℤ) (hlow : ∀ i j, i < j → Lz i j = 0)
    (i j : Fin m) (h : i < j) : Lz.map (Int.cast : ℤ → F) i j = 0 := by
  rw [map_apply, hlow i j h, Int.cast_zero]

lemma neg_one_pow_smul_eq_zero {m : ℕ} (n : ℕ) (w : Fin m → F) (i : Fin m)
    (h : ((-1 : F) ^ n • w) i = 0) : w i = 0 := by
  rw [Pi.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- **`thm:t0` over a field**: every box matrix of `(L T², L, L T)`, `L` lower-triangular with
diagonal `±1`, has trivial kernel. -/
theorem scrambled_box_kernel (k : ℕ) (hk : 1 ≤ k) (Lz : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ)
    (hlow : ∀ i j, i < j → Lz i j = 0) (hdiag : ∀ i, Lz i i = 1 ∨ Lz i i = -1)
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) (v : Fin (3 * k) → F)
    (hv : boxMatrix (fun c => (![Lz * T k ^ 2, Lz, Lz * T k] c).map (Int.cast : ℤ → F)) d *ᵥ v
      = 0) : v = 0 := by
  rw [boxMatrix_mulVec_eq_zero_iff _ d hd] at hv
  set L' := Lz.map (Int.cast : ℤ → F)
  set τ' := (tau (3 * k)).map (Int.cast : ℤ → F)
  have hkill := lowerTri_kill L' (map_lower Lz hlow) (isUnit_map_diag Lz hdiag)
  -- coordinate y: the first `d 1` digits of `v` vanish
  have h1 : ∀ i : Fin (3 * k), (i : ℕ) < d 1 → v i = 0 :=
    hkill v (d 1) (fun r hr => hv 1 r hr)
  -- coordinate z
  have h2 : ∀ i : Fin (3 * k), (i : ℕ) < d 2 → (τ' *ᵥ v) i = 0 := by
    have := hkill ((T k).map (Int.cast : ℤ → F) *ᵥ v) (d 2) (fun r hr => by
      have := hv 2 r hr
      simpa [map_mul_mulVec] using this)
    intro i hi
    have hi' := this i hi
    rw [T_map_mulVec] at hi'
    exact neg_one_pow_smul_eq_zero _ _ i hi'
  -- coordinate x
  have h0 : ∀ i : Fin (3 * k), (i : ℕ) < d 0 → (τ' *ᵥ (τ' *ᵥ v)) i = 0 := by
    have := hkill ((T k).map (Int.cast : ℤ → F) *ᵥ ((T k).map (Int.cast : ℤ → F) *ᵥ v)) (d 0)
      (fun r hr => by
        have := hv 0 r hr
        simpa [map_mul_mulVec, pow_two] using this)
    intro i hi
    have hi' := this i hi
    rw [T_map_mulVec, T_map_mulVec, mulVec_smul, smul_smul, ← pow_add] at hi'
    exact neg_one_pow_smul_eq_zero _ _ i hi'
  exact frame_kernel (3 * k) (by omega) v (d 0) (d 1) (d 2) hd h0 h1 h2

end Field

/-- An integer that is nonzero modulo every prime is `±1`. -/
lemma int_eq_one_or_neg_one (z : ℤ) (h : ∀ p : ℕ, p.Prime → (z : ZMod p) ≠ 0) :
    z = 1 ∨ z = -1 := by
  by_cases h1 : z.natAbs = 1
  · rcases Int.natAbs_eq_iff.mp h1 with h | h
    · left; simpa using h
    · right; simpa using h
  · obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd h1
    exact absurd ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mpr (Int.ofNat_dvd_left.mpr hdvd))
      (h p hp)

/-- Box minors of `(L T², L, L T)` are `±1`, for `L` lower-triangular with diagonal `±1`. -/
theorem scrambled_boxMinor (k : ℕ) (hk : 1 ≤ k) (Lz : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ)
    (hlow : ∀ i j, i < j → Lz i j = 0) (hdiag : ∀ i, Lz i i = 1 ∨ Lz i i = -1)
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    (boxMatrix ![Lz * T k ^ 2, Lz, Lz * T k] d).det = 1 ∨
      (boxMatrix ![Lz * T k ^ 2, Lz, Lz * T k] d).det = -1 := by
  apply int_eq_one_or_neg_one
  intro p hp hzero
  haveI := Fact.mk hp
  have hmap := boxMatrix_map (Int.castRingHom (ZMod p)) ![Lz * T k ^ 2, Lz, Lz * T k] d
  have hdet : ((boxMatrix ![Lz * T k ^ 2, Lz, Lz * T k] d).map
      (Int.castRingHom (ZMod p))).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; simpa using hzero
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply scrambled_box_kernel k hk Lz hlow hdiag d hd v
  rw [← hv, ← hmap]
  rfl

/-! ## The main statements for `𝒫_{k,q}` -/

/-- **Theorem `thm:t0`, first sentence.** -/
theorem P_boxMinor (k : ℕ) (hk : 1 ≤ k) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    (boxMatrix (PGen k) d).det = 1 ∨ (boxMatrix (PGen k) d).det = -1 :=
  scrambled_boxMinor k hk (L k) (L_lower k) (L_diag k) d hd

/-- **Theorem `thm:t0` / Theorem 1(1).** -/
theorem P_net (q k : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) : IsNet0 q (3 * k) (Ppoint q k) := by
  haveI : NeZero q := ⟨by omega⟩
  apply isNet0_of_box_injective
  intro d hd
  apply mulVec_injective_of_isUnit_det
  have hmap := boxMatrix_map (Int.castRingHom (ZMod q)) (PGen k) d
  have : boxMatrix (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) d =
      (boxMatrix (PGen k) d).map (Int.castRingHom (ZMod q)) := hmap
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rcases P_boxMinor k hk d hd with h | h <;> rw [h] <;> simp

/-- **Theorem 1(2), covering radius.** -/
theorem P_covering (q k : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (x : Fin 3 → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (3 * k) → ZMod q,
      ∑ c, (x c - (Ppoint q k v c : ℝ) / (q : ℝ) ^ (3 * k)) ^ 2 ≤ 3 / ((q : ℝ) ^ k) ^ 2 := by
  have hnet := P_net q k hq hk
  have hG : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  let a : Fin 3 → ℕ := fun c => min ⌊x c * (q : ℝ) ^ k⌋₊ (q ^ k - 1)
  have ha : ∀ c, a c < q ^ (fun _ => k) c := by
    intro c
    show min _ _ < q ^ k
    exact lt_of_le_of_lt (min_le_right _ _) (by omega)
  obtain ⟨v, hv, -⟩ := hnet (fun _ => k) (by ring) a ha
  refine ⟨v, ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hGpos : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hqpos k
  have key : ∀ c, (x c - (Ppoint q k v c : ℝ) / (q : ℝ) ^ (3 * k)) ^ 2 ≤ 1 / ((q : ℝ) ^ k) ^ 2 := by
    intro c
    set X := Ppoint q k v c
    have hdiv : X / q ^ (2 * k) = a c := by
      have := hv c
      rw [show 3 * k - k = 2 * k by omega] at this
      exact this
    set y := x c * (q : ℝ) ^ k
    set z := (X : ℝ) / (q : ℝ) ^ (2 * k)
    have hy0 : 0 ≤ y := mul_nonneg (hx c).1 hGpos.le
    -- a ≤ y ≤ a + 1
    have hay : (a c : ℝ) ≤ y := by
      have : a c ≤ ⌊y⌋₊ := min_le_left _ _
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hy0)
    have hya : y ≤ (a c : ℝ) + 1 := by
      by_cases hfl : ⌊y⌋₊ ≤ q ^ k - 1
      · have : a c = ⌊y⌋₊ := min_eq_left hfl
        rw [this]; exact (Nat.lt_floor_add_one y).le
      · have hfl' : ¬ ⌊x c * (q : ℝ) ^ k⌋₊ ≤ q ^ k - 1 := hfl
        have : a c = q ^ k - 1 := min_eq_right (by omega)
        rw [this, Nat.cast_sub hG]
        have : y ≤ (q : ℝ) ^ k := by
          have := mul_le_mul_of_nonneg_right (hx c).2 hGpos.le
          simpa [y] using this
        push_cast; linarith
    -- a ≤ z < a + 1
    have hQ : (0 : ℝ) < (q : ℝ) ^ (2 * k) := pow_pos hqpos _
    have hXeq : (X : ℝ) = (q : ℝ) ^ (2 * k) * (a c) + (X % q ^ (2 * k) : ℕ) := by
      have := Nat.div_add_mod X (q ^ (2 * k))
      rw [hdiv] at this
      exact_mod_cast this.symm
    have hrem : ((X % q ^ (2 * k) : ℕ) : ℝ) < (q : ℝ) ^ (2 * k) := by
      exact_mod_cast Nat.mod_lt _ (pow_pos (by omega) _)
    have haz : (a c : ℝ) ≤ z := by
      rw [le_div_iff₀ hQ, hXeq]
      have : (0 : ℝ) ≤ ((X % q ^ (2 * k) : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hza : z ≤ (a c : ℝ) + 1 := by
      rw [div_le_iff₀ hQ, hXeq]
      nlinarith
    have hxz : x c - (X : ℝ) / (q : ℝ) ^ (3 * k) = (y - z) / (q : ℝ) ^ k := by
      simp only [y, z]
      rw [show 3 * k = 2 * k + k by ring, pow_add]
      field_simp
    rw [hxz, div_pow, one_div]
    rw [div_eq_mul_inv]
    have hsq : (y - z) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith
    calc (y - z) ^ 2 * (((q : ℝ) ^ k) ^ 2)⁻¹ ≤ 1 * (((q : ℝ) ^ k) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (by positivity))
      _ = (((q : ℝ) ^ k) ^ 2)⁻¹ := by rw [one_mul]
  calc ∑ c, (x c - (Ppoint q k v c : ℝ) / (q : ℝ) ^ (3 * k)) ^ 2
      ≤ ∑ _c : Fin 3, 1 / ((q : ℝ) ^ k) ^ 2 := Finset.sum_le_sum fun c _ => key c
    _ = 3 / ((q : ℝ) ^ k) ^ 2 := by simp; ring

end Z3Net.Proofs

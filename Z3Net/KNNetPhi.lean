module
public import Z3Net.KNNetReal

@[expose] public section

/-!
# The frame read at `∞, 0, 1` and its graph-form columns (KN entry, `KN1_net` / `KN2_net`)

The index of the frame is a polynomial `V = ∑ v_l t^l` of degree `< m`; coordinate `x` reads the
coefficients of `t^(m-1), t^(m-2), …` (place `∞`), coordinate `y` those of `1, t, …` (place `0`)
and coordinate `z` those of `1, (t-1), …` (place `1`, i.e. the coefficients of `V(t+1)`).  These are
the readings `(φ_∞, φ_0, φ_1)` of `app:perprime`, proof of `lem:ppinv`(b).

* `phi_T0`: the frame is `t = 0` (if the first `d_x, d_y, d_z` digits vanish, `t^(d_y) (t-1)^(d_z)`
  divides `V` and `deg V < m - d_x = d_y + d_z`, so `V = 0`);
* `gr_col`: a column of the graph form is the image of the index vector whose coarse digits are a
  unit vector; for the frame this is the coefficient vector of an explicit polynomial (`phi_col`).
-/

namespace Z3NetKN.Phi

open Polynomial Matrix Finset Z3NetKN.Frame Z3NetKN.Realize

variable {F : Type*} [Field F] {m : ℕ}

/-- Reading at `∞`: digit `i` is the coefficient of `t^(m-1-i)`. -/
def phiX (m : ℕ) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun i l => if (i : ℕ) + l + 1 = m then 1 else 0

/-- Reading at `1`: digit `i` is the coefficient of `(t-1)^i`. -/
def phiZ (m : ℕ) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun i l => ((l : ℕ).choose i : F)

/-- The frame `(φ_∞, φ_0, φ_1)`. -/
def phi (m : ℕ) : Fin 3 → Matrix (Fin m) (Fin m) F := ![phiX m, 1, phiZ m]

/-- The polynomial of an index vector. -/
noncomputable def vp (v : Fin m → F) : F[X] := ∑ l : Fin m, C (v l) * X ^ (l : ℕ)

lemma coeff_vp (v : Fin m → F) (j : ℕ) : (vp v).coeff j = if h : j < m then v ⟨j, h⟩ else 0 := by
  simp only [vp, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun e => hb (Fin.ext e.symm)), mul_zero]
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (by omega), mul_zero]

lemma phi0_mulVec (v : Fin m → F) (i : Fin m) : (phi m 0 *ᵥ v) i = (vp v).coeff (m - 1 - i) := by
  rw [coeff_vp, dif_pos (by omega)]
  simp only [phi, Matrix.cons_val_zero, mulVec, dotProduct, phiX, Matrix.of_apply]
  rw [Finset.sum_eq_single ⟨m - 1 - i, by omega⟩]
  · rw [if_pos (by simp; omega), one_mul]
  · intro b _ hb
    rw [if_neg (fun e => hb (Fin.ext (by simp; omega))), zero_mul]
  · simp

lemma phi1_mulVec (v : Fin m → F) (i : Fin m) : (phi m 1 *ᵥ v) i = (vp v).coeff i := by
  rw [coeff_vp, dif_pos i.isLt]
  simp [phi]

lemma phi2_mulVec (v : Fin m → F) (i : Fin m) :
    (phi m 2 *ᵥ v) i = ((vp v).comp (X + 1)).coeff i := by
  simp only [phi, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mulVec, dotProduct, vp,
    Polynomial.sum_comp, mul_comp, C_comp, X_pow_comp, finsetSum_coeff, coeff_C_mul,
    coeff_X_add_one_pow, phiZ, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma vp_eq_zero (v : Fin m → F) (h : vp v = 0) : v = 0 := by
  funext j
  have := coeff_vp v j
  rw [h, coeff_zero, dif_pos j.isLt] at this
  exact this.symm

lemma isCoprime_X_pow_X_sub_one_pow (a b : ℕ) : IsCoprime ((X : F[X]) ^ a) ((X - 1) ^ b) := by
  apply IsCoprime.pow
  exact ⟨1, -1, by ring⟩

/-- **The frame is `t = 0`** (every box, every `m`). -/
theorem phi_T0 (m : ℕ) : T0 (phi (F := F) m) := by
  intro d hd v hv
  apply vp_eq_zero
  set V := vp v with hV
  -- x: all coefficients from `m - d 0` on vanish
  have hx : ∀ j, m - d 0 ≤ j → V.coeff j = 0 := by
    intro j hj
    by_cases hjm : j < m
    · have := hv 0 ⟨m - 1 - j, by omega⟩ (by simp; omega)
      rw [phi0_mulVec] at this
      rwa [show m - 1 - (m - 1 - j) = j by omega] at this
    · rw [hV, coeff_vp, dif_neg hjm]
  -- y: `X ^ d 1 ∣ V`
  have hy : X ^ d 1 ∣ V := by
    rw [X_pow_dvd_iff]
    intro j hj
    have := hv 1 ⟨j, by omega⟩ hj
    rwa [phi1_mulVec] at this
  -- z: `(X - 1) ^ d 2 ∣ V`
  have hz : (X - 1) ^ d 2 ∣ V := by
    have h1 : X ^ d 2 ∣ V.comp (X + 1) := by
      rw [X_pow_dvd_iff]
      intro j hj
      have := hv 2 ⟨j, by omega⟩ hj
      rwa [phi2_mulVec] at this
    obtain ⟨Q, hQ⟩ := h1
    refine ⟨Q.comp (X - 1), ?_⟩
    have : V = (V.comp (X + 1)).comp (X - 1) := by
      rw [comp_assoc]; simp
    rw [this, hQ, mul_comp, pow_comp, X_comp]
  have hdvd : X ^ d 1 * (X - 1) ^ d 2 ∣ V :=
    (isCoprime_X_pow_X_sub_one_pow (d 1) (d 2)).mul_dvd hy hz
  by_contra hne
  have hdeg := natDegree_le_of_dvd hdvd hne
  have hmon : (X ^ d 1 * (X - 1 : F[X]) ^ d 2).natDegree = d 1 + d 2 := by
    have e : (X - 1 : F[X]) = X - C 1 := by simp
    rw [e, natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (X_sub_C_ne_zero 1)),
      natDegree_X_pow, natDegree_pow, natDegree_X_sub_C]
    simp
  have hlead : V.coeff V.natDegree ≠ 0 := by
    rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hne
  exact hlead (hx _ (by omega))

/-- A graph-form column is the image of the index vector with unit coarse digits. -/
lemma gr_col (X : Fin 3 → Matrix (Fin m) (Fin m) F) (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m)
    (hX : T0 X) (u : Fin m → F) (n : Fin m)
    (hu : ∀ c (j : Fin m), (j : ℕ) < K c → (X c *ᵥ u) j = if (n : ℕ) = offK K c + j then 1 else 0)
    (c : Fin 3) (i : Fin m) : gr X K c i n = (X c *ᵥ u) i := by
  have hB := isUnit_box hX K hK
  set B := Z3Net.boxMatrix X K
  have hBu : B *ᵥ u = Pi.single n 1 := by
    funext r
    obtain ⟨hl, hpos⟩ := blk_lev K hK r
    have hrow := boxMatrix_row X K hK (blk K r) ⟨lev K r, by omega⟩ (by simpa using hl)
    have hr : (⟨offK K (blk K r) + lev K r, offK_lt K hK _ _ hl⟩ : Fin m) = r := Fin.ext hpos
    simp only at hrow
    rw [hr] at hrow
    have : (B *ᵥ u) r = (X (blk K r) *ᵥ u) ⟨lev K r, by omega⟩ := by
      simp only [mulVec]
      congr 1
    rw [this, hu _ _ (by simpa using hl), Pi.single_apply]
    by_cases h : r = n
    · subst h; rw [if_pos hpos.symm, if_pos rfl]
    · rw [if_neg (fun e => h (Fin.ext (by rw [← hpos]; exact e.symm))), if_neg h]
  have hinv : B⁻¹ *ᵥ Pi.single n 1 = u := by
    rw [← hBu, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hB), one_mulVec]
  have hcol : ∀ j, B⁻¹ j n = u j := by
    intro j
    have := congrFun hinv j
    rwa [mulVec_single_one] at this
  simp only [gr, mul_apply, mulVec, dotProduct]
  exact Finset.sum_congr rfl (fun j _ => congrArg _ (hcol j))

/-- The frame's graph form. -/
noncomputable def G0 (K : Fin 3 → ℕ) : Fin 3 → Matrix (Fin m) (Fin m) F := gr (phi m) K

lemma G0_T0 (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) : T0 (G0 (F := F) (m := m) K) :=
  T0_gr (phi_T0 m) K hK

lemma G0_GF (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) : IsGF (G0 (F := F) (m := m) K) K :=
  fun c j col hj => gr_coarse (phi_T0 m) K hK c j col hj

/-- The coefficient vector of a polynomial. -/
def cv (W : F[X]) : Fin m → F := fun l => W.coeff l

lemma vp_cv (W : F[X]) (hW : W.natDegree < m) : vp (cv (m := m) W) = W := by
  ext j
  rw [coeff_vp]
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- **Columns of the frame's graph form from polynomials.** If `W` (degree `< m`) has coarse
digits equal to the unit vector at `n`, then column `n` of the graph form reads the digits of `W`. -/
theorem phi_col (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (W : F[X]) (hW : W.natDegree < m)
    (n : Fin m)
    (h0 : ∀ j, j < K 0 → W.coeff (m - 1 - j) = if (n : ℕ) = offK K 0 + j then 1 else 0)
    (h1 : ∀ j, j < K 1 → W.coeff j = if (n : ℕ) = offK K 1 + j then 1 else 0)
    (h2 : ∀ j, j < K 2 → (W.comp (X + 1)).coeff j = if (n : ℕ) = offK K 2 + j then 1 else 0) :
    (∀ i : ℕ, i < m → ent (G0 (F := F) (m := m) K 0) i n = W.coeff (m - 1 - i)) ∧
    (∀ i : ℕ, i < m → ent (G0 (F := F) (m := m) K 1) i n = W.coeff i) ∧
    (∀ i : ℕ, i < m → ent (G0 (F := F) (m := m) K 2) i n = (W.comp (X + 1)).coeff i) := by
  have hcol := gr_col (phi m) K hK (phi_T0 m) (cv W) n (by
    intro c j hj
    match c with
    | 0 => rw [phi0_mulVec, vp_cv W hW]; exact h0 j hj
    | 1 => rw [phi1_mulVec, vp_cv W hW]; exact h1 j hj
    | 2 => rw [phi2_mulVec, vp_cv W hW]; exact h2 j hj)
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;>
  · unfold ent
    rw [dif_pos ⟨hi, n.isLt⟩]
    simp only [G0, Fin.eta]
    rw [hcol]
    first
    | (rw [phi0_mulVec, vp_cv W hW])
    | (rw [phi1_mulVec, vp_cv W hW])
    | (rw [phi2_mulVec, vp_cv W hW])

theorem phi_col' (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (W : F[X]) (hW : W.natDegree < m)
    (n : ℕ) (hn : n < m)
    (h0 : ∀ j, j < K 0 → W.coeff (m - 1 - j) = if n = offK K 0 + j then 1 else 0)
    (h1 : ∀ j, j < K 1 → W.coeff j = if n = offK K 1 + j then 1 else 0)
    (h2 : ∀ j, j < K 2 → (W.comp (X + 1)).coeff j = if n = offK K 2 + j then 1 else 0) :
    (∀ i : ℕ, i < m → ent (G0 (F := F) (m := m) K 0) i n = W.coeff (m - 1 - i)) ∧
    (∀ i : ℕ, i < m → ent (G0 (F := F) (m := m) K 1) i n = W.coeff i) ∧
    (∀ i : ℕ, i < m → ent (G0 (F := F) (m := m) K 2) i n = (W.comp (X + 1)).coeff i) :=
  phi_col K hK W hW ⟨n, hn⟩ h0 h1 h2

end Z3NetKN.Phi

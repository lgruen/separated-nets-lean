module
public import Z3Net.PPInvDefs

@[expose] public section

/-!
# `lem:ppinv` (a): the invariants are unchanged by the gauge moves (entry PPInv)

* `window_mul`: a move (c) `Φ_cd ↦ L_c Φ_cd U_d` (`L_c`, `U_d` lower triangular) acts on the window
  data by `W_cd ↦ L'_c W_cd U'_d` with `L'_c` (the first two rows) lower triangular and `U'_d` (the
  last three levels, in the window index) upper triangular;
* `kap_inv`, `J_inv`: `κ₁, κ₂`, `J₁, …, J₅` are unchanged by `W_cd ↦ μ_cd L_c W_cd U_d` (`c ≠ d`).
  Each tilde quantity (`x̃, ỹ, ζ̃, η̃, ξ̃`, `R_Y`, `R_Z`, `d_x`) is multiplied by a unit, and the units
  cancel.
-/

namespace Z3NetPI.InvA

open Matrix Finset

variable {F : Type*} [Field F]

/-! ## The window of a move (c) -/

lemma sum_range_eq_of_zero (h : ℕ → F) (a n : ℕ) (ha : ∀ x, a ≤ x → h x = 0)
    (hn : ∀ x, n ≤ x → h x = 0) : ∑ x ∈ range a, h x = ∑ x ∈ range n, h x := by
  rcases le_total a n with hle | hle
  · exact Finset.sum_subset (range_subset_range.2 hle) (fun x _ hx => ha x (by simpa using hx))
  · exact (Finset.sum_subset (range_subset_range.2 hle)
      (fun x _ hx => hn x (by simpa using hx))).symm

lemma ent_mul {a n b : ℕ} (P : Matrix (Fin a) (Fin n) F) (Q : Matrix (Fin n) (Fin b) F) (r c : ℕ) :
    ent (P * Q) r c = ∑ x ∈ range n, ent P r x * ent Q x c := by
  by_cases h : r < a ∧ c < b
  · simp only [ent, h, and_self, dite_true, Matrix.mul_apply]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp [x.isLt]
  · rw [ent, dite_eq_right_iff.2 (fun h' => absurd h' h)]
    refine (Finset.sum_eq_zero (fun x _ => ?_)).symm
    simp only [ent]
    by_cases hr : r < a
    · have hc : ¬ c < b := fun hc => h ⟨hr, hc⟩
      simp [hc]
    · simp [hr]

theorem window_mul {a b : ℕ} (A : Matrix (Fin a) (Fin b) F) (L : Matrix (Fin a) (Fin a) F)
    (U : Matrix (Fin b) (Fin b) F) (hL : ∀ i j : Fin a, i < j → L i j = 0)
    (hU : ∀ i j : Fin b, i < j → U i j = 0) (hb : 3 ≤ b) :
    winB (L * A * U) = winL L * winB A * winU U ∧ winL L 0 1 = 0 ∧
      ∀ i i' : Fin 3, i' < i → winU U i i' = 0 := by
  have hL' : ∀ r x : ℕ, r < x → ent L r x = 0 := by
    intro r x hrx
    simp only [ent]
    split_ifs with h
    · exact hL _ _ (by change r < x; exact hrx)
    · rfl
  have hU' : ∀ y z : ℕ, y < z → ent U y z = 0 := by
    intro y z hyz
    simp only [ent]
    split_ifs with h
    · exact hU _ _ (by change y < z; exact hyz)
    · rfl
  refine ⟨?_, ?_, ?_⟩
  · ext ρ i
    simp only [winB, winL, winU, Matrix.mul_apply, Matrix.of_apply]
    have hx : ∀ y : ℕ, ∑ x ∈ range a, ent L (ρ : ℕ) x * ent A x y =
        ∑ x ∈ range 2, ent L (ρ : ℕ) x * ent A x y := fun y =>
      sum_range_eq_of_zero _ a 2
        (fun x hx => by simp [ent, show ¬ x < a by omega])
        (fun x hx => by rw [hL' _ _ (by have := ρ.isLt; omega), zero_mul])
    calc ent (L * A * U) (ρ : ℕ) (b - 1 - (i : ℕ))
        = ∑ y ∈ range b, (∑ x ∈ range a, ent L (ρ : ℕ) x * ent A x y) *
            ent U y (b - 1 - (i : ℕ)) := by
          rw [ent_mul]; simp_rw [ent_mul]
      _ = ∑ j ∈ range b, (∑ x ∈ range 2, ent L (ρ : ℕ) x * ent A x (b - 1 - j)) *
            ent U (b - 1 - j) (b - 1 - (i : ℕ)) := by
          rw [← Finset.sum_range_reflect]; simp_rw [hx]
      _ = ∑ j ∈ range 3, (∑ x ∈ range 2, ent L (ρ : ℕ) x * ent A x (b - 1 - j)) *
            ent U (b - 1 - j) (b - 1 - (i : ℕ)) := by
          refine (Finset.sum_subset (range_subset_range.2 hb) (fun j hj hj3 => ?_)).symm
          simp only [mem_range, not_lt] at hj hj3
          rw [hU' _ _ (by have := i.isLt; omega), mul_zero]
      _ = _ := by
          rw [Fin.sum_univ_eq_sum_range (fun i' => (∑ ρ' : Fin 2, ent L (ρ : ℕ) (ρ' : ℕ) *
            ent A (ρ' : ℕ) (b - 1 - i')) * ent U (b - 1 - i') (b - 1 - (i : ℕ))) 3]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Fin.sum_univ_eq_sum_range (fun ρ' => ent L (ρ : ℕ) ρ' * ent A ρ' (b - 1 - j)) 2]
  · exact hL' 0 1 (by norm_num)
  · intro i i' hii
    exact hU' _ _ (by have := i.isLt; omega)

/-! ## The gauge action on window data -/

/-- The hypotheses of `lem:ppinv` (a): `W'_cd = μ_cd L_c W_cd U_d` off the diagonal. -/
def Gauge (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) (U : Fin 3 → Matrix (Fin 3) (Fin 3) F)
    (μ : Fin 3 → Fin 3 → F) (W W' : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) : Prop :=
  (∀ c, L c 0 1 = 0 ∧ L c 0 0 ≠ 0 ∧ L c 1 1 ≠ 0) ∧
    (∀ d, (∀ i i' : Fin 3, i' < i → U d i i' = 0) ∧ ∀ i, U d i i ≠ 0) ∧
    (∀ c d, c ≠ d → μ c d ≠ 0) ∧ (∀ c d, c ≠ d → W' c d = μ c d • (L c * W c d * U d))

section

variable {L : Fin 3 → Matrix (Fin 2) (Fin 2) F} {U : Fin 3 → Matrix (Fin 3) (Fin 3) F}
  {μ : Fin 3 → Fin 3 → F} {W W' : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F}

lemma Gauge.e (h : Gauge L U μ W W') (c d : Fin 3) (hcd : c ≠ d) (ρ : Fin 2) (i : Fin 3) :
    W' c d ρ i = μ c d * ((L c ρ 0 * W c d 0 0 + L c ρ 1 * W c d 1 0) * U d 0 i +
      (L c ρ 0 * W c d 0 1 + L c ρ 1 * W c d 1 1) * U d 1 i +
      (L c ρ 0 * W c d 0 2 + L c ρ 1 * W c d 1 2) * U d 2 i) := by
  rw [h.2.2.2 c d hcd]
  simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
    smul_eq_mul]

lemma Gauge.e00 (h : Gauge L U μ W W') (c d : Fin 3) (hcd : c ≠ d) :
    W' c d 0 0 = μ c d * L c 0 0 * U d 0 0 * W c d 0 0 := by
  rw [h.e c d hcd, (h.1 c).1, (h.2.1 d).1 1 0 (by decide), (h.2.1 d).1 2 0 (by decide)]; ring

lemma Gauge.e01 (h : Gauge L U μ W W') (c d : Fin 3) (hcd : c ≠ d) :
    W' c d 0 1 = μ c d * L c 0 0 * (W c d 0 0 * U d 0 1 + W c d 0 1 * U d 1 1) := by
  rw [h.e c d hcd, (h.1 c).1, (h.2.1 d).1 2 1 (by decide)]; ring

lemma Gauge.e02 (h : Gauge L U μ W W') (c d : Fin 3) (hcd : c ≠ d) :
    W' c d 0 2 = μ c d * L c 0 0 *
      (W c d 0 0 * U d 0 2 + W c d 0 1 * U d 1 2 + W c d 0 2 * U d 2 2) := by
  rw [h.e c d hcd, (h.1 c).1]; ring

lemma Gauge.e10 (h : Gauge L U μ W W') (c d : Fin 3) (hcd : c ≠ d) :
    W' c d 1 0 = μ c d * (L c 1 0 * W c d 0 0 + L c 1 1 * W c d 1 0) * U d 0 0 := by
  rw [h.e c d hcd, (h.2.1 d).1 1 0 (by decide), (h.2.1 d).1 2 0 (by decide)]; ring

lemma Gauge.e11 (h : Gauge L U μ W W') (c d : Fin 3) (hcd : c ≠ d) :
    W' c d 1 1 = μ c d * ((L c 1 0 * W c d 0 0 + L c 1 1 * W c d 1 0) * U d 0 1 +
      (L c 1 0 * W c d 0 1 + L c 1 1 * W c d 1 1) * U d 1 1) := by
  rw [h.e c d hcd, (h.2.1 d).1 2 1 (by decide)]; ring

lemma Gauge.e12 (h : Gauge L U μ W W') (c d : Fin 3) (hcd : c ≠ d) :
    W' c d 1 2 = μ c d * ((L c 1 0 * W c d 0 0 + L c 1 1 * W c d 1 0) * U d 0 2 +
      (L c 1 0 * W c d 0 1 + L c 1 1 * W c d 1 1) * U d 1 2 +
      (L c 1 0 * W c d 0 2 + L c 1 1 * W c d 1 2) * U d 2 2) := by
  rw [h.e c d hcd]

lemma Gauge.L0 (h : Gauge L U μ W W') (c : Fin 3) : L c 0 0 ≠ 0 := (h.1 c).2.1
lemma Gauge.L1 (h : Gauge L U μ W W') (c : Fin 3) : L c 1 1 ≠ 0 := (h.1 c).2.2
lemma Gauge.U0 (h : Gauge L U μ W W') (d : Fin 3) (i : Fin 3) : U d i i ≠ 0 := (h.2.1 d).2 i
lemma Gauge.mu (h : Gauge L U μ W W') (c d : Fin 3) (hcd : c ≠ d) : μ c d ≠ 0 := h.2.2.1 c d hcd

/-! ### `m ≡ 2` -/

/-- `x̃` is multiplied by `U_x[1,1]`: a row on `x̃` scales like the row. -/
lemma Gauge.tlx2_0 (h : Gauge L U μ W W') (c : Fin 3) (hc : c ≠ 0) (hz : W 2 0 0 0 ≠ 0) :
    tlx2 W' c 0 = μ c 0 * L c 0 0 * U 0 1 1 * tlx2 W c 0 := by
  have h2 := h.mu 2 0 (by decide); have hc0 := h.mu c 0 hc
  have hL := h.L0 2; have hU := h.U0 0 0
  unfold tlx2
  rw [h.e01 c 0 hc, h.e00 c 0 hc, h.e01 2 0 (by decide), h.e00 2 0 (by decide)]
  field_simp
  ring

lemma Gauge.tlx2_1 (h : Gauge L U μ W W') (c : Fin 3) (hc : c ≠ 0) (hz : W 2 0 0 0 ≠ 0) :
    tlx2 W' c 1 = μ c 0 * U 0 1 1 * (L c 1 0 * tlx2 W c 0 + L c 1 1 * tlx2 W c 1) := by
  have h2 := h.mu 2 0 (by decide); have hc0 := h.mu c 0 hc
  have hL := h.L0 2; have hU := h.U0 0 0
  unfold tlx2
  rw [h.e11 c 0 hc, h.e10 c 0 hc, h.e01 2 0 (by decide), h.e00 2 0 (by decide)]
  field_simp
  ring

lemma Gauge.tly2_0 (h : Gauge L U μ W W') (c : Fin 3) (hc : c ≠ 1) (hz : W 2 1 0 0 ≠ 0) :
    tly2 W' c 0 = μ c 1 * L c 0 0 * U 1 1 1 * tly2 W c 0 := by
  have h2 := h.mu 2 1 (by decide); have hc0 := h.mu c 1 hc
  have hL := h.L0 2; have hU := h.U0 1 0
  unfold tly2
  rw [h.e01 c 1 hc, h.e00 c 1 hc, h.e01 2 1 (by decide), h.e00 2 1 (by decide)]
  field_simp
  ring

lemma Gauge.tly2_1 (h : Gauge L U μ W W') (c : Fin 3) (hc : c ≠ 1) (hz : W 2 1 0 0 ≠ 0) :
    tly2 W' c 1 = μ c 1 * U 1 1 1 * (L c 1 0 * tly2 W c 0 + L c 1 1 * tly2 W c 1) := by
  have h2 := h.mu 2 1 (by decide); have hc0 := h.mu c 1 hc
  have hL := h.L0 2; have hU := h.U0 1 0
  unfold tly2
  rw [h.e11 c 1 hc, h.e10 c 1 hc, h.e01 2 1 (by decide), h.e00 2 1 (by decide)]
  field_simp
  ring

lemma tlx2_self (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (hz : W 2 0 0 0 ≠ 0) :
    tlx2 W 2 0 = 0 := by
  unfold tlx2; field_simp; ring

lemma tly2_self (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (hz : W 2 1 0 0 ≠ 0) :
    tly2 W 2 0 = 0 := by
  unfold tly2; field_simp; ring

theorem kap_inv (h : Gauge L U μ W W') (hW : DefK W) :
    DefK W' ∧ kapW1 W' = kapW1 W ∧ kapW2 W' = kapW2 W := by
  obtain ⟨hzx, hzy, hyx, htx, hty⟩ := hW
  have m20 := h.mu 2 0 (by decide); have m21 := h.mu 2 1 (by decide)
  have m10 := h.mu 1 0 (by decide); have m01 := h.mu 0 1 (by decide)
  have l00 := h.L0 0; have l10 := h.L0 1; have l20 := h.L0 2; have l21 := h.L1 2
  have u00 := h.U0 0 0; have u01 := h.U0 0 1; have u10 := h.U0 1 0; have u11 := h.U0 1 1
  have ax : tlx2 W' 2 1 = μ 2 0 * U 0 1 1 * L 2 1 1 * tlx2 W 2 1 := by
    rw [h.tlx2_1 2 (by decide) hzx, tlx2_self W hzx]; ring
  have ay : tly2 W' 2 1 = μ 2 1 * U 1 1 1 * L 2 1 1 * tly2 W 2 1 := by
    rw [h.tly2_1 2 (by decide) hzy, tly2_self W hzy]; ring
  have bx := h.tlx2_0 1 (by decide) hzx
  have by0 := h.tly2_0 0 (by decide) hzy
  have z0 := h.e00 2 0 (by decide); have z1 := h.e00 2 1 (by decide)
  have y0 := h.e00 1 0 (by decide); have x1 := h.e00 0 1 (by decide)
  have zz0 := h.e10 2 0 (by decide); have zz1 := h.e10 2 1 (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [z0]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero m20 l20) u00) hzx
  · rw [z1]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero m21 l20) u10) hzy
  · rw [y0]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero m10 l10) u00) hyx
  · rw [ax]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero m20 u01) l21) htx
  · rw [by0]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero m01 l00) u11) hty
  · unfold kapW1
    rw [ax, ay, bx, by0, z0, z1, y0, x1]
    field_simp
  · unfold kapW2
    rw [ax, bx, z0, z1, y0, zz0, zz1]
    field_simp
    ring

/-! ### `m ≡ 1` -/

lemma RYW_self (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (hy : W 1 0 0 0 ≠ 0) :
    RYW W 0 0 = 0 := by
  unfold RYW; field_simp; ring

lemma RZW_self (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (hz : W 2 0 0 0 ≠ 0) :
    RZW W 0 0 = 0 := by
  unfold RZW; field_simp; ring

lemma Gauge.RY0 (h : Gauge L U μ W W') (d : Fin 3) (hd : d ≠ 1) (hy : W 1 0 0 0 ≠ 0) :
    RYW W' d 0 = μ 1 d * L 1 1 1 * (RYW W d 0 * U d 0 0) := by
  have m1 := h.mu 1 0 (by decide); have m2 := h.mu 1 d (Ne.symm hd)
  have l := h.L0 1; have u := h.U0 0 0
  unfold RYW
  rw [h.e10 1 d (Ne.symm hd), h.e00 1 d (Ne.symm hd), h.e10 1 0 (by decide), h.e00 1 0 (by decide)]
  field_simp; ring

lemma Gauge.RY1 (h : Gauge L U μ W W') (d : Fin 3) (hd : d ≠ 1) (hy : W 1 0 0 0 ≠ 0) :
    RYW W' d 1 = μ 1 d * L 1 1 1 * (RYW W d 0 * U d 0 1 + RYW W d 1 * U d 1 1) := by
  have m1 := h.mu 1 0 (by decide); have m2 := h.mu 1 d (Ne.symm hd)
  have l := h.L0 1; have u := h.U0 0 0
  unfold RYW
  rw [h.e11 1 d (Ne.symm hd), h.e01 1 d (Ne.symm hd), h.e10 1 0 (by decide), h.e00 1 0 (by decide)]
  field_simp; ring

lemma Gauge.RY2 (h : Gauge L U μ W W') (d : Fin 3) (hd : d ≠ 1) (hy : W 1 0 0 0 ≠ 0) :
    RYW W' d 2 = μ 1 d * L 1 1 1 *
      (RYW W d 0 * U d 0 2 + RYW W d 1 * U d 1 2 + RYW W d 2 * U d 2 2) := by
  have m1 := h.mu 1 0 (by decide); have m2 := h.mu 1 d (Ne.symm hd)
  have l := h.L0 1; have u := h.U0 0 0
  unfold RYW
  rw [h.e12 1 d (Ne.symm hd), h.e02 1 d (Ne.symm hd), h.e10 1 0 (by decide), h.e00 1 0 (by decide)]
  field_simp; ring

lemma Gauge.RZ0 (h : Gauge L U μ W W') (d : Fin 3) (hd : d ≠ 2) (hz : W 2 0 0 0 ≠ 0) :
    RZW W' d 0 = μ 2 d * L 2 1 1 * (RZW W d 0 * U d 0 0) := by
  have m1 := h.mu 2 0 (by decide); have m2 := h.mu 2 d (Ne.symm hd)
  have l := h.L0 2; have u := h.U0 0 0
  unfold RZW
  rw [h.e10 2 d (Ne.symm hd), h.e00 2 d (Ne.symm hd), h.e10 2 0 (by decide), h.e00 2 0 (by decide)]
  field_simp; ring

lemma Gauge.RZ1 (h : Gauge L U μ W W') (d : Fin 3) (hd : d ≠ 2) (hz : W 2 0 0 0 ≠ 0) :
    RZW W' d 1 = μ 2 d * L 2 1 1 * (RZW W d 0 * U d 0 1 + RZW W d 1 * U d 1 1) := by
  have m1 := h.mu 2 0 (by decide); have m2 := h.mu 2 d (Ne.symm hd)
  have l := h.L0 2; have u := h.U0 0 0
  unfold RZW
  rw [h.e11 2 d (Ne.symm hd), h.e01 2 d (Ne.symm hd), h.e10 2 0 (by decide), h.e00 2 0 (by decide)]
  field_simp; ring

lemma Gauge.RZ2 (h : Gauge L U μ W W') (d : Fin 3) (hd : d ≠ 2) (hz : W 2 0 0 0 ≠ 0) :
    RZW W' d 2 = μ 2 d * L 2 1 1 *
      (RZW W d 0 * U d 0 2 + RZW W d 1 * U d 1 2 + RZW W d 2 * U d 2 2) := by
  have m1 := h.mu 2 0 (by decide); have m2 := h.mu 2 d (Ne.symm hd)
  have l := h.L0 2; have u := h.U0 0 0
  unfold RZW
  rw [h.e12 2 d (Ne.symm hd), h.e02 2 d (Ne.symm hd), h.e10 2 0 (by decide), h.e00 2 0 (by decide)]
  field_simp; ring

lemma Gauge.dx (h : Gauge L U μ W W') :
    dxW W' = μ 1 0 * μ 2 0 * L 1 0 0 * L 2 0 0 * U 0 0 0 * U 0 1 1 * dxW W := by
  unfold dxW
  rw [h.e00 1 0 (by decide), h.e01 1 0 (by decide), h.e00 2 0 (by decide), h.e01 2 0 (by decide)]
  ring

lemma Gauge.tlz (h : Gauge L U μ W W') (hx : W 0 2 0 0 ≠ 0) (α v0 v1 : F) :
    tlzW W' (α * (v0 * U 2 0 0)) (α * (v0 * U 2 0 1 + v1 * U 2 1 1)) =
      α * U 2 1 1 * tlzW W v0 v1 := by
  have m := h.mu 0 2 (by decide); have l := h.L0 0; have u := h.U0 2 0
  unfold tlzW
  rw [h.e01 0 2 (by decide), h.e00 0 2 (by decide)]
  field_simp; ring

lemma Gauge.tly (h : Gauge L U μ W W') (hx : W 0 1 0 0 ≠ 0) (α v0 v1 : F) :
    tlyW W' (α * (v0 * U 1 0 0)) (α * (v0 * U 1 0 1 + v1 * U 1 1 1)) =
      α * U 1 1 1 * tlyW W v0 v1 := by
  have m := h.mu 0 1 (by decide); have l := h.L0 0; have u := h.U0 1 0
  unfold tlyW
  rw [h.e01 0 1 (by decide), h.e00 0 1 (by decide)]
  field_simp; ring

lemma Gauge.tlx (h : Gauge L U μ W W') (hd : dxW W ≠ 0) (α v0 v1 v2 : F) :
    tlxW W' (α * (v0 * U 0 0 0)) (α * (v0 * U 0 0 1 + v1 * U 0 1 1))
        (α * (v0 * U 0 0 2 + v1 * U 0 1 2 + v2 * U 0 2 2)) =
      α * U 0 2 2 * tlxW W v0 v1 v2 := by
  have m1 := h.mu 1 0 (by decide); have m2 := h.mu 2 0 (by decide)
  have l1 := h.L0 1; have l2 := h.L0 2
  have u0 := h.U0 0 0; have u1 := h.U0 0 1
  have hd' : W 1 0 0 1 * W 2 0 0 0 - W 1 0 0 0 * W 2 0 0 1 ≠ 0 := by
    intro h0; apply hd; unfold dxW; linear_combination -h0
  have hdx' : dxW W' ≠ 0 := by rw [h.dx]; simp [m1, m2, l1, l2, u0, u1, hd]
  have hd'' : W' 1 0 0 1 * W' 2 0 0 0 - W' 1 0 0 0 * W' 2 0 0 1 ≠ 0 := by
    intro h0; apply hdx'; unfold dxW; linear_combination -h0
  unfold tlxW xiAW xiBW
  generalize hD' : W' 1 0 0 1 * W' 2 0 0 0 - W' 1 0 0 0 * W' 2 0 0 1 = D' at *
  generalize hD : W 1 0 0 1 * W 2 0 0 0 - W 1 0 0 0 * W 2 0 0 1 = D at *
  have hDD : D' = μ 1 0 * μ 2 0 * L 1 0 0 * L 2 0 0 * U 0 0 0 * U 0 1 1 * D := by
    rw [← hD', ← hD, h.e00 1 0 (by decide), h.e01 1 0 (by decide), h.e00 2 0 (by decide),
      h.e01 2 0 (by decide)]
    ring
  rw [hDD, h.e00 1 0 (by decide), h.e01 1 0 (by decide), h.e02 1 0 (by decide),
    h.e00 2 0 (by decide), h.e01 2 0 (by decide), h.e02 2 0 (by decide)]
  have u2 := h.U0 0 2
  field_simp
  rw [← hD]
  ring

theorem J_inv (h : Gauge L U μ W W') (hW : DefJ W) :
    DefJ W' ∧ JW1 W' = JW1 W ∧ JW2 W' = JW2 W ∧ JW3 W' = JW3 W ∧ JW4 W' = JW4 W ∧
      JW5 W' = JW5 W := by
  obtain ⟨hy0, hz0, hdx, hry, hrz, hxz, hxy, htz, hty, hyz, hzy, htx⟩ := hW
  have m10 := h.mu 1 0 (by decide); have m20 := h.mu 2 0 (by decide)
  have m12 := h.mu 1 2 (by decide); have m21 := h.mu 2 1 (by decide)
  have m02 := h.mu 0 2 (by decide); have m01 := h.mu 0 1 (by decide)
  have l00 := h.L0 0; have l10 := h.L0 1; have l20 := h.L0 2
  have l11 := h.L1 1; have l21 := h.L1 2
  have u00 := h.U0 0 0; have u01 := h.U0 0 1; have u02 := h.U0 0 2
  have u10 := h.U0 1 0; have u11 := h.U0 1 1; have u20 := h.U0 2 0; have u21 := h.U0 2 1
  -- the atoms
  have ry00 := RYW_self W hy0
  have rz00 := RZW_self W hz0
  have aRY01 : RYW W' 0 1 = μ 1 0 * L 1 1 1 * U 0 1 1 * RYW W 0 1 := by
    rw [h.RY1 0 (by decide) hy0, ry00]; ring
  have aRZ01 : RYW W' 0 1 = RYW W' 0 1 := rfl
  have aRZ01' : RZW W' 0 1 = μ 2 0 * L 2 1 1 * U 0 1 1 * RZW W 0 1 := by
    rw [h.RZ1 0 (by decide) hz0, rz00]; ring
  have aRY20 := h.RY0 2 (by decide) hy0
  have aRZ10 := h.RZ0 1 (by decide) hz0
  have aY20 := h.e00 1 2 (by decide)
  have aZ10 := h.e00 2 1 (by decide)
  have aY00 := h.e00 1 0 (by decide)
  have aZ00 := h.e00 2 0 (by decide)
  have aX20 := h.e00 0 2 (by decide)
  have aX10 := h.e00 0 1 (by decide)
  have adx := h.dx
  -- ζ̃ rows
  have tzRY : tlzW W' (RYW W' 2 0) (RYW W' 2 1) = μ 1 2 * L 1 1 1 * U 2 1 1 *
      tlzW W (RYW W 2 0) (RYW W 2 1) := by
    rw [h.RY0 2 (by decide) hy0, h.RY1 2 (by decide) hy0, h.tlz hxz]
  have tzY : tlzW W' (W' 1 2 0 0) (W' 1 2 0 1) = μ 1 2 * L 1 0 0 * U 2 1 1 *
      tlzW W (W 1 2 0 0) (W 1 2 0 1) := by
    rw [h.e00 1 2 (by decide), h.e01 1 2 (by decide)]
    rw [show μ 1 2 * L 1 0 0 * U 2 0 0 * W 1 2 0 0 = (μ 1 2 * L 1 0 0) * (W 1 2 0 0 * U 2 0 0) by ring,
      show μ 1 2 * L 1 0 0 * (W 1 2 0 0 * U 2 0 1 + W 1 2 0 1 * U 2 1 1) =
        (μ 1 2 * L 1 0 0) * (W 1 2 0 0 * U 2 0 1 + W 1 2 0 1 * U 2 1 1) by ring, h.tlz hxz]
  have tyRZ : tlyW W' (RZW W' 1 0) (RZW W' 1 1) = μ 2 1 * L 2 1 1 * U 1 1 1 *
      tlyW W (RZW W 1 0) (RZW W 1 1) := by
    rw [h.RZ0 1 (by decide) hz0, h.RZ1 1 (by decide) hz0, h.tly hxy]
  have tyZ : tlyW W' (W' 2 1 0 0) (W' 2 1 0 1) = μ 2 1 * L 2 0 0 * U 1 1 1 *
      tlyW W (W 2 1 0 0) (W 2 1 0 1) := by
    rw [h.e00 2 1 (by decide), h.e01 2 1 (by decide)]
    rw [show μ 2 1 * L 2 0 0 * U 1 0 0 * W 2 1 0 0 = (μ 2 1 * L 2 0 0) * (W 2 1 0 0 * U 1 0 0) by ring,
      show μ 2 1 * L 2 0 0 * (W 2 1 0 0 * U 1 0 1 + W 2 1 0 1 * U 1 1 1) =
        (μ 2 1 * L 2 0 0) * (W 2 1 0 0 * U 1 0 1 + W 2 1 0 1 * U 1 1 1) by ring, h.tly hxy]
  -- ξ̃ rows
  have txRY : tlxW W' (RYW W' 0 0) (RYW W' 0 1) (RYW W' 0 2) = μ 1 0 * L 1 1 1 * U 0 2 2 *
      tlxW W (RYW W 0 0) (RYW W 0 1) (RYW W 0 2) := by
    rw [h.RY0 0 (by decide) hy0, h.RY1 0 (by decide) hy0, h.RY2 0 (by decide) hy0, h.tlx hdx]
  have txRZ : tlxW W' (RZW W' 0 0) (RZW W' 0 1) (RZW W' 0 2) = μ 2 0 * L 2 1 1 * U 0 2 2 *
      tlxW W (RZW W 0 0) (RZW W 0 1) (RZW W 0 2) := by
    rw [h.RZ0 0 (by decide) hz0, h.RZ1 0 (by decide) hz0, h.RZ2 0 (by decide) hz0, h.tlx hdx]
  have u22 := h.U0 0 2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aY00]; simp [m10, l10, u00, hy0]
  · rw [aZ00]; simp [m20, l20, u00, hz0]
  · rw [adx]; simp [m10, m20, l10, l20, u00, u01, hdx]
  · rw [aRY20]; simp [m12, l11, u20, hry]
  · rw [aRZ10]; simp [m21, l21, u10, hrz]
  · rw [aX20]; simp [m02, l00, u20, hxz]
  · rw [aX10]; simp [m01, l00, u10, hxy]
  · rw [tzY]; simp [m12, l10, u21, htz]
  · rw [tyZ]; simp [m21, l20, u11, hty]
  · rw [aY20]; simp [m12, l10, u20, hyz]
  · rw [aZ10]; simp [m21, l20, u10, hzy]
  · rw [txRY]; simp [m10, l11, u22, htx]
  · unfold JW1; rw [aRY01, aZ00, aY20, aRY20, adx]; field_simp
  · unfold JW2; rw [aRZ01', aY00, aZ10, aRZ10, adx]; field_simp
  · unfold JW3; rw [tzRY, tzY, aY20, aRY20]; field_simp
  · unfold JW4; rw [tyRZ, tyZ, aZ10, aRZ10]; field_simp
  · unfold JW5; rw [txRZ, txRY, aY00, aZ10, aRY20, aZ00, aY20, aRZ10]; field_simp

end

end Z3NetPI.InvA

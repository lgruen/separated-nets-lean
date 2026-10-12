module
public import Z3Net.Net

@[expose] public section

/-!
# The net property of `𝒬_{k,p}` (Theorem `thm:two`, net part; `def:Q`, `lem:gauge`)

1. The frame `(T², I, T)` has all box minors `±1` (`scrambled_boxMinor` with `L = 1`); its graph
   form `Φ^F` (over `ℤ`, via the Mathlib inverse of the unimodular `(k,k,k)` box matrix) gives the
   generator matrices `graphGen k Φ^F c = F_c G⁻¹`, whose box matrices are again unimodular.
2. `T³ = 1` makes `Φ^F` circulant: `Φ^F_{c+1,d+1} = Φ^F_{c,d}`.
3. Gauge moves (`lem:gauge`): `Φ_{cd} ↦ μ_{cd} R Φ_{cd} U` (`c ≠ d`, `R`, `U` lower-triangular
   with unit diagonal, `μ = ±1`) and arbitrary diagonal blocks preserve injectivity of box
   matrices.  `𝒬_{k,p}` is such a gauge transform of `Φ^F` for odd `p`.
-/

namespace Z3Net.Proofs

open Matrix Finset

/-! ## Lower-triangular helpers -/

section Tri

variable {R : Type*} [CommRing R]

lemma lower_mul {a : ℕ} (A B : Matrix (Fin a) (Fin a) R) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) : ∀ i j, i < j → (A * B) i j = 0 := by
  intro i j h
  rw [mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge i l with hil | hli
  · rw [hA i l hil, zero_mul]
  · rw [hB l j (lt_of_le_of_lt hli h), mul_zero]

lemma diag_mul_of_lower {a : ℕ} (A B : Matrix (Fin a) (Fin a) R) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) (i : Fin a) : (A * B) i i = A i i * B i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hB l i h, mul_zero]
    · rw [hA i l h, zero_mul]
  · simp

/-- Lower-triangular `U`: `(U w)_i = 0` as soon as `w_l = 0` for all `l ≤ i`. -/
lemma lower_mulVec_eq_zero {a : ℕ} (U : Matrix (Fin a) (Fin a) R) (hU : ∀ i j, i < j → U i j = 0)
    (w : Fin a → R) (i : Fin a) (hw : ∀ l, l ≤ i → w l = 0) : (U *ᵥ w) i = 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases le_or_gt l i with h | h
  · rw [hw l h, mul_zero]
  · rw [hU i l h, zero_mul]

end Tri

/-! ## Graph form -/

section GraphForm

variable {R : Type*} [CommRing R]

lemma box_kkk_row (k : ℕ) (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) R) (c : Fin 3)
    (i : Fin (3 * k)) (hi : (i : ℕ) < k) :
    boxMatrix C (fun _ => k) ⟨(c : ℕ) * k + i, by have := c.isLt; nlinarith⟩ = C c i := by
  fin_cases c
  · unfold boxMatrix
    rw [if_pos (by simp; omega)]
    congr 1; ext; simp
  · unfold boxMatrix
    rw [if_neg (by simp), if_pos (by simp; omega)]
    congr 1; ext; simp
  · unfold boxMatrix
    rw [if_neg (by simp; omega), if_neg (by simp; omega)]
    congr 1; ext; simp; omega

/-- The graph form generators are `C_c B_kkk⁻¹` (when `B_kkk` is invertible). -/
lemma graphGen_graphBlock (k : ℕ) (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) R)
    (hG : IsUnit (boxMatrix C (fun _ => k)).det) (c : Fin 3) :
    graphGen k (graphBlock k C) c = C c * (boxMatrix C (fun _ => k))⁻¹ := by
  set G := boxMatrix C (fun _ => k)
  ext i j
  unfold graphGen
  by_cases hi : (i : ℕ) < k
  · rw [if_pos hi]
    have hrow := box_kkk_row k C c i hi
    have : (C c * G⁻¹) i j = (G * G⁻¹) ⟨(c : ℕ) * k + i, by have := c.isLt; nlinarith⟩ j := by
      simp only [mul_apply]
      rw [show G ⟨(c : ℕ) * k + i, _⟩ = C c i from hrow]
    rw [this, mul_nonsing_inv G hG, one_apply]
    by_cases h : (j : ℕ) = (c : ℕ) * k + i
    · rw [if_pos h, if_pos (Fin.ext h.symm)]
    · rw [if_neg h, if_neg (fun e => h (congrArg Fin.val e).symm)]
  · rw [if_neg hi]
    have hj := j.isLt
    have hjk : (j : ℕ) % k < k := Nat.mod_lt _ (by omega)
    have hdm : (j : ℕ) / k * k + (j : ℕ) % k = j := Nat.div_add_mod' _ _
    unfold ent
    rw [dif_pos ⟨by omega, hjk⟩]
    unfold graphBlock ent
    rw [dif_pos ⟨by simp only; omega, by simp only; omega⟩]
    exact congrArg₂ (fun a b => (C c * G⁻¹) a b) (Fin.ext (by simp only; omega))
      (Fin.ext (by simp only; omega))

end GraphForm

/-! ## The frame `(T², I, T)` over `ℤ` -/

section Frame

lemma tau_cube_mulVec (m : ℕ) (hm : 0 < m) (v : Fin m → ℤ) :
    tau m *ᵥ (tau m *ᵥ (tau m *ᵥ v)) = (-1 : ℤ) ^ (m - 1) • v := by
  have hmap : (tau m).map (Int.cast : ℤ → ℤ) = tau m := by ext; simp
  have h := tauL_cube (R := ℤ) (m - 1) (toPoly v)
    (by rw [Nat.sub_add_cancel hm]; exact toPoly_mem v)
  rw [← toPoly_tau_mulVec m hm, ← toPoly_tau_mulVec m hm, ← toPoly_tau_mulVec m hm, hmap] at h
  funext i
  have := congrArg (fun P => Polynomial.coeff P i) h
  simp only [Polynomial.coeff_smul, coeff_toPoly, dif_pos i.isLt, smul_eq_mul, Fin.eta] at this
  rw [Pi.smul_apply, smul_eq_mul]
  exact this

/-- `T³ = 1`. -/
lemma T_cube (k : ℕ) (hk : 1 ≤ k) : T k ^ 3 = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [one_mulVec, pow_succ, pow_two, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [T, smul_mulVec, mulVec_smul, smul_smul]
  rw [tau_cube_mulVec (3 * k) (by omega), smul_smul]
  have : (-1 : ℤ) ^ (k + 1) * (-1) ^ (k + 1) * (-1) ^ (k + 1) * (-1) ^ (3 * k - 1) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add]
    exact Even.neg_one_pow ⟨3 * k + 1, by omega⟩
  rw [this, one_smul]

lemma frameGen_mul_T (k : ℕ) (hk : 1 ≤ k) (c : Fin 3) :
    frameGen k c * T k = frameGen k (c + 1) := by
  fin_cases c
  · show T k ^ 2 * T k = 1
    rw [← pow_succ, T_cube k hk]
  · show 1 * T k = T k
    rw [one_mul]
  · show T k * T k = T k ^ 2
    rw [pow_two]

lemma frame_boxMinor (k : ℕ) (hk : 1 ≤ k) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    (boxMatrix (frameGen k) d).det = 1 ∨ (boxMatrix (frameGen k) d).det = -1 := by
  have h := scrambled_boxMinor k hk 1 (fun i j h => one_apply_ne (ne_of_lt h))
    (fun i => Or.inl (one_apply_eq i)) d hd
  have e : (![1 * T k ^ 2, 1, 1 * T k] : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ) =
      frameGen k := by
    simp only [one_mul]; rfl
  rwa [e] at h

lemma isUnit_of_pm_one {z : ℤ} (h : z = 1 ∨ z = -1) : IsUnit z := by
  rcases h with h | h <;> rw [h] <;> simp

/-- The `(k,k,k)` box matrix of the frame. -/
noncomputable abbrev Gk (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  boxMatrix (frameGen k) (fun _ => k)

lemma Gk_isUnit (k : ℕ) (hk : 1 ≤ k) : IsUnit (Gk k).det :=
  isUnit_of_pm_one (frame_boxMinor k hk (fun _ => k) (by ring))

/-- Cyclic shift of the index blocks: `r ↦ r + k (mod 3k)`. -/
def sig (k : ℕ) (r : Fin (3 * k)) : Fin (3 * k) :=
  ⟨if (r : ℕ) < 2 * k then r + k else r - 2 * k, by have := r.isLt; split_ifs <;> omega⟩

lemma sig_injective (k : ℕ) : Function.Injective (sig k) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [sig] at this
  ext
  have ha := a.isLt; have hb := b.isLt
  split_ifs at this <;> omega

lemma box_kkk_of_lt {R : Type*} [CommRing R] (k : ℕ)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) R) (r : Fin (3 * k)) (h : (r : ℕ) < k) :
    boxMatrix C (fun _ => k) r = C 0 r := by
  unfold boxMatrix; dsimp only; rw [if_pos h]

lemma box_kkk_of_mid {R : Type*} [CommRing R] (k : ℕ)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) R) (r : Fin (3 * k)) (h1 : k ≤ (r : ℕ))
    (h2 : (r : ℕ) < 2 * k) :
    boxMatrix C (fun _ => k) r = C 1 ⟨(r : ℕ) - k, by omega⟩ := by
  unfold boxMatrix; dsimp only; rw [if_neg (by omega), if_pos (by omega)]

lemma box_kkk_of_ge {R : Type*} [CommRing R] (k : ℕ)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) R) (r : Fin (3 * k)) (h : 2 * k ≤ (r : ℕ)) :
    boxMatrix C (fun _ => k) r = C 2 ⟨(r : ℕ) - 2 * k, by omega⟩ := by
  unfold boxMatrix; dsimp only; rw [if_neg (by omega), if_neg (by omega)]
  congr 1; ext; simp only; omega

lemma Gk_mul_T (k : ℕ) (hk : 1 ≤ k) : Gk k * T k = (Gk k).submatrix (sig k) id := by
  rw [Gk, ← boxMatrix_mul_right]
  simp only [frameGen_mul_T k hk]
  ext r j
  rw [submatrix_apply, id]
  have hr := r.isLt
  by_cases h1 : (r : ℕ) < k
  · have hs : sig k r = ⟨(r : ℕ) + k, by omega⟩ := Fin.ext (by simp [sig]; omega)
    rw [box_kkk_of_lt _ _ r h1, hs, box_kkk_of_mid _ _ _ (by simp) (by simp; omega)]
    show frameGen k 1 r j = _
    congr 2; ext; simp
  · by_cases h2 : (r : ℕ) < 2 * k
    · have hs : sig k r = ⟨(r : ℕ) + k, by omega⟩ := Fin.ext (by simp [sig]; omega)
      rw [box_kkk_of_mid _ _ r (by omega) h2, hs, box_kkk_of_ge _ _ _ (by simp; omega)]
      show frameGen k 2 _ j = _
      congr 2; dsimp only; omega
    · have hs : sig k r = ⟨(r : ℕ) - 2 * k, by omega⟩ := Fin.ext (by simp [sig]; omega)
      rw [box_kkk_of_ge _ _ r (by omega), hs, box_kkk_of_lt _ _ _ (by simp; omega)]
      rfl

/-- The frame graph-form generators `H_c = F_c G⁻¹` satisfy `H_{c+1} (σ r) = H_c r`. -/
lemma H_shift (k : ℕ) (hk : 1 ≤ k) (c : Fin 3) (i r0 : Fin (3 * k)) :
    (frameGen k (c + 1) * (Gk k)⁻¹) i (sig k r0) = (frameGen k c * (Gk k)⁻¹) i r0 := by
  have hG := Gk_isUnit k hk
  have hTG : T k * (Gk k)⁻¹ = (Gk k)⁻¹ * ((Gk k).submatrix (sig k) id * (Gk k)⁻¹) := by
    rw [← Gk_mul_T k hk, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hG,
      Matrix.one_mul]
  have hP : ∀ r j, ((Gk k).submatrix (sig k) id * (Gk k)⁻¹) r j = (1 : Matrix _ _ ℤ) (sig k r) j := by
    intro r j
    rw [← mul_nonsing_inv _ hG]
    simp [mul_apply]
  rw [← frameGen_mul_T k hk, Matrix.mul_assoc, hTG, ← Matrix.mul_assoc, mul_apply,
    Finset.sum_eq_single r0]
  · rw [hP, one_apply_eq, mul_one]
  · intro r _ hr
    rw [hP, one_apply_ne (fun e => hr (sig_injective k e)), mul_zero]
  · simp

/-- The frame graph form is circulant. -/
lemma frameBlock_shift (k : ℕ) (hk : 1 ≤ k) (c d : Fin 3) :
    graphBlock k (frameGen k) (c + 1) (d + 1) = graphBlock k (frameGen k) c d := by
  ext r l
  have hr := r.isLt; have hl := l.isLt
  have hd := d.isLt
  unfold graphBlock ent
  have hdk : (d : ℕ) * k + l < 3 * k := by nlinarith
  have hd1k : ((d + 1 : Fin 3) : ℕ) * k + l < 3 * k := by
    have := (d + 1 : Fin 3).isLt; nlinarith
  rw [dif_pos ⟨by omega, hd1k⟩, dif_pos ⟨by omega, hdk⟩]
  have hs : sig k ⟨(d : ℕ) * k + l, hdk⟩ = ⟨((d + 1 : Fin 3) : ℕ) * k + l, hd1k⟩ := by
    ext
    simp only [sig]
    fin_cases d <;> simp <;> split_ifs <;> omega
  rw [← hs]
  exact H_shift k hk c _ _

lemma frameB_eq (k : ℕ) (hk : 1 ≤ k) (c : Fin 3) :
    graphBlock k (frameGen k) c (c + 1) = frameB k := by
  unfold frameB
  fin_cases c
  · rfl
  · have := frameBlock_shift k hk 0 1
    simpa using this
  · have h1 := frameBlock_shift k hk 0 1
    have h2 := frameBlock_shift k hk 1 2
    simp at h1 h2
    rw [← h1, ← h2]
    rfl

lemma frameC_eq (k : ℕ) (hk : 1 ≤ k) (c : Fin 3) :
    graphBlock k (frameGen k) c (c + 2) = frameC k := by
  unfold frameC
  fin_cases c
  · rfl
  · have := frameBlock_shift k hk 0 2
    simpa using this
  · have h1 := frameBlock_shift k hk 0 2
    have h2 := frameBlock_shift k hk 1 0
    simp at h1 h2
    rw [← h1, ← h2]
    rfl

end Frame

/-! ## Gauge moves (`lem:gauge`) -/

section Gauge

variable {F : Type*} [Field F]

/-- Block `e` (levels `0..k-1`) of a vector indexed by `Fin (3k)` (index `l + k e`). -/
def blk {k : ℕ} (n : Fin (3 * k) → F) (e : Fin 3) : Fin k → F :=
  fun l => n (finProdFinEquiv (e, l))

lemma fp_val (k : ℕ) (e : Fin 3) (l : Fin k) :
    ((finProdFinEquiv (e, l) : Fin (3 * k)) : ℕ) = l + k * e := rfl

lemma graphGen_mulVec_cell (k : ℕ) (Φ : Fin 3 → Fin 3 → Matrix (Fin (2 * k)) (Fin k) F)
    (c : Fin 3) (n : Fin (3 * k) → F) (i : Fin (3 * k)) (hi : (i : ℕ) < k) :
    (graphGen k Φ c *ᵥ n) i = n (finProdFinEquiv (c, ⟨i, hi⟩)) := by
  simp only [mulVec, dotProduct, graphGen, if_pos hi]
  rw [Finset.sum_eq_single (finProdFinEquiv (c, ⟨i, hi⟩))]
  · rw [if_pos (by rw [fp_val]; show (i : ℕ) + k * c = c * k + i; ring)]; simp
  · intro j _ hj
    rw [if_neg, zero_mul]
    intro h
    apply hj
    ext
    rw [h, fp_val]; show (c : ℕ) * k + i = i + k * c; ring
  · simp

lemma graphGen_mulVec_off (k : ℕ) (hk : 0 < k) (Φ : Fin 3 → Fin 3 → Matrix (Fin (2 * k)) (Fin k) F)
    (c : Fin 3) (n : Fin (3 * k) → F) (i : Fin (3 * k)) (hi : k ≤ (i : ℕ)) :
    (graphGen k Φ c *ᵥ n) i = (∑ e, Φ c e *ᵥ blk n e) ⟨(i : ℕ) - k, by omega⟩ := by
  simp only [mulVec, dotProduct, graphGen, if_neg (not_lt.mpr hi)]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mulVec, dotProduct, blk]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  have hl := l.isLt
  have h1 : ((l : ℕ) + k * e) / k = e := by
    rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hl, zero_add]
  have h2 : ((l : ℕ) + k * e) % k = l := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have hil := i.isLt
  unfold ent
  rw [dif_pos ⟨by omega, Nat.mod_lt _ hk⟩]
  have he : (⟨((finProdFinEquiv (e, l) : Fin (3 * k)) : ℕ) / k, by
      rw [fp_val, h1]; exact e.isLt⟩ : Fin 3) = e := Fin.ext (by simp only [fp_val]; exact h1)
  congr 1
  all_goals first | exact he | rw [he] | (ext; simp only [fp_val]; exact h2)

/-- **Gauge moves (`lem:gauge`)**, kernel form: if `Φ_{ce} = μ_{ce} L Ψ_{ce} U` for `c ≠ e`
(`L`, `U` lower-triangular with unit diagonals) and `μ` factors as `λ_c s_e` on the relevant
(over, not-over) pairs, then trivial kernels of the boxes of `Ψ` give trivial kernels for `Φ`. -/
theorem gauge_transfer (k : ℕ) (hk : 0 < k) (Φ Ψ : Fin 3 → Fin 3 → Matrix (Fin (2 * k)) (Fin k) F)
    (Lr : Matrix (Fin (2 * k)) (Fin (2 * k)) F) (hLlow : ∀ i j, i < j → Lr i j = 0)
    (hLdiag : ∀ i, IsUnit (Lr i i))
    (U : Matrix (Fin k) (Fin k) F) (hUlow : ∀ i j, i < j → U i j = 0)
    (hUdiag : ∀ i, IsUnit (U i i))
    (μ : Fin 3 → Fin 3 → F) (hΦ : ∀ c e, c ≠ e → Φ c e = μ c e • (Lr * Ψ c e * U))
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k)
    (lam s : Fin 3 → F) (hlam : ∀ c, IsUnit (lam c)) (hs : ∀ e, IsUnit (s e))
    (hfac : ∀ c e, c ≠ e → k < d c → d e ≤ k → μ c e = lam c * s e)
    (hΨ : ∀ n', boxMatrix (graphGen k Ψ) d *ᵥ n' = 0 → n' = 0) :
    ∀ n, boxMatrix (graphGen k Φ) d *ᵥ n = 0 → n = 0 := by
  intro n hn
  rw [boxMatrix_mulVec_eq_zero_iff _ d hd] at hn
  have hdle : ∀ c, d c ≤ 3 * k := by intro c; fin_cases c <;> simp <;> omega
  have hcell : ∀ c (l : Fin k), (l : ℕ) < d c → blk n c l = 0 := by
    intro c l hl
    have := hn c ⟨l, by omega⟩ hl
    rw [graphGen_mulVec_cell k Φ c n _ l.isLt] at this
    exact this
  have hover : ∀ c, k < d c → blk n c = 0 :=
    fun c hc => funext fun l => hcell c l (by have := l.isLt; omega)
  have hoff : ∀ c (r : Fin (2 * k)), k + (r : ℕ) < d c → (∑ e, Φ c e *ᵥ blk n e) r = 0 := by
    intro c r hr
    have := hn c ⟨k + r, by have := hdle c; omega⟩ hr
    rw [graphGen_mulVec_off k hk Φ c n _ (by simp)] at this
    convert this using 2
    ext; simp
  set n' : Fin (3 * k) → F := fun j =>
    s (finProdFinEquiv.symm j).1 * (U *ᵥ blk n (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2
    with hn'def
  have hblk' : ∀ e, blk n' e = s e • (U *ᵥ blk n e) := by
    intro e; funext l; simp only [n', blk, Equiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul]
  have hn' : n' = 0 := by
    apply hΨ
    rw [boxMatrix_mulVec_eq_zero_iff _ d hd]
    intro c i hi
    by_cases hik : (i : ℕ) < k
    · rw [graphGen_mulVec_cell k Ψ c n' i hik]
      show blk n' c ⟨i, hik⟩ = 0
      rw [hblk', Pi.smul_apply, smul_eq_mul,
        lower_mulVec_eq_zero U hUlow _ _ (fun l hl => hcell c l (by
          have : (l : ℕ) ≤ i := hl
          omega)), mul_zero]
    · replace hik : k ≤ (i : ℕ) := not_lt.mp hik
      have hcov : k < d c := by omega
      rw [graphGen_mulVec_off k hk Ψ c n' i hik]
      have hsum : ∑ e, Φ c e *ᵥ blk n e = lam c • (Lr *ᵥ ∑ e, Ψ c e *ᵥ blk n' e) := by
        rw [mulVec_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        by_cases hce : c = e
        · subst hce
          rw [hblk', hover c hcov]
          simp
        · by_cases hde : k < d e
          · rw [hblk', hover e hde]
            simp
          · replace hde : d e ≤ k := not_lt.mp hde
            rw [hΦ c e hce, hfac c e hce hcov hde, hblk']
            rw [smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_smul, mulVec_smul,
              smul_smul, mul_comm (lam c) (s e)]
      have hker := lowerTri_kill Lr hLlow hLdiag (∑ e, Ψ c e *ᵥ blk n' e) (d c - k) (by
        intro r hr
        have := hoff c r (by omega)
        rw [hsum, Pi.smul_apply, smul_eq_mul] at this
        exact (hlam c).mul_right_eq_zero.mp this)
      exact hker ⟨(i : ℕ) - k, by omega⟩ (by simp only; omega)
  funext j
  obtain ⟨⟨e, l⟩, rfl⟩ := finProdFinEquiv.surjective j
  have h1 : U *ᵥ blk n e = 0 := by
    have := congrArg (fun x => blk x e) hn'
    simp only [hblk'] at this
    funext r
    have hr := congrFun this r
    simp only [Pi.smul_apply, smul_eq_mul, blk, Pi.zero_apply] at hr
    exact (hs e).mul_right_eq_zero.mp hr
  exact lowerTri_kill U hUlow hUdiag (blk n e) k (fun r _ => by rw [h1]; rfl) l l.isLt

/-- The sign pattern of `def:Q`: `+1` on the blocks `Φ_{c,c+1}`, `-1` on `Φ_{c,c+2}`. -/
def muQ (c e : Fin 3) : F := if e = c + 1 then 1 else -1

lemma muQ_isUnit (c e : Fin 3) : IsUnit (muQ (F := F) c e) := by
  unfold muQ; split_ifs
  · exact isUnit_one
  · exact isUnit_one.neg

lemma muQ_factor (k : ℕ) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    ∃ lam s : Fin 3 → F, (∀ c, IsUnit (lam c)) ∧ (∀ e, IsUnit (s e)) ∧
      ∀ c e, c ≠ e → k < d c → d e ≤ k → muQ c e = lam c * s e := by
  by_cases h01 : k < d 0 ∧ k < d 1
  · refine ⟨fun c => muQ c 2, 1, fun c => muQ_isUnit _ _, fun _ => isUnit_one, ?_⟩
    intro c e hce hc he
    have : e = 2 := by fin_cases e <;> simp_all <;> omega
    subst this; simp
  by_cases h02 : k < d 0 ∧ k < d 2
  · refine ⟨fun c => muQ c 1, 1, fun c => muQ_isUnit _ _, fun _ => isUnit_one, ?_⟩
    intro c e hce hc he
    have : e = 1 := by fin_cases e <;> simp_all <;> omega
    subst this; simp
  by_cases h12 : k < d 1 ∧ k < d 2
  · refine ⟨fun c => muQ c 0, 1, fun c => muQ_isUnit _ _, fun _ => isUnit_one, ?_⟩
    intro c e hce hc he
    have : e = 0 := by fin_cases e <;> simp_all <;> omega
    subst this; simp
  · let c0 : Fin 3 := if k < d 0 then 0 else if k < d 1 then 1 else 2
    refine ⟨1, fun e => muQ c0 e, fun _ => isUnit_one, fun e => muQ_isUnit _ _, ?_⟩
    intro c e hce hc he
    have : c = c0 := by
      simp only [c0]
      fin_cases c
      · have hc' : k < d 0 := hc
        rw [if_pos hc']; rfl
      · have hc' : k < d 1 := hc
        rw [if_neg (fun h => h01 ⟨h, hc'⟩), if_pos hc']; rfl
      · have hc' : k < d 2 := hc
        rw [if_neg (fun h => h02 ⟨h, hc'⟩), if_neg (fun h => h12 ⟨h, hc'⟩)]; rfl
    subst this; simp

end Gauge

/-! ## The two-digit nets `𝒬_{k,p}` -/

section Q

lemma Rmat_lower (k : ℕ) : ∀ i j : Fin (2 * k), i < j → Rmat k i j = 0 := by
  intro i j h
  have h' : i.val < j.val := h
  unfold Rmat
  rw [if_neg (ne_of_lt h), if_neg (by omega)]

lemma Rmat_diag (k : ℕ) (i : Fin (2 * k)) : Rmat k i i = 1 ∨ Rmat k i i = -1 := by
  left; unfold Rmat; rw [if_pos rfl]

lemma U0_lower (k : ℕ) : ∀ i j : Fin k, i < j → U0 k i j = 0 := by
  intro i j h; unfold U0; rw [if_neg (not_le.mpr h)]

lemma U0_diag (k : ℕ) (i : Fin k) : U0 k i i = 1 := by
  unfold U0; rw [if_pos le_rfl]; simp

lemma Vmat_lower (k : ℕ) : ∀ i j : Fin k, i < j → Vmat k i j = 0 := by
  intro i j h
  have h' : i.val < j.val := h
  unfold Vmat
  split_ifs <;> first | rfl | omega | (subst_vars; omega)

lemma Vmat_diag_dvd (k : ℕ) (i : Fin k) : Vmat k i i ∣ 4 := by
  unfold Vmat
  split_ifs <;> first | decide | simp_all

lemma Ustar_lower (k : ℕ) : ∀ i j : Fin k, i < j → Ustar k i j = 0 :=
  lower_mul _ _ (U0_lower k) (Vmat_lower k)

lemma Ustar_diag_dvd (k : ℕ) (i : Fin k) : Ustar k i i ∣ 4 := by
  unfold Ustar
  rw [diag_mul_of_lower _ _ (U0_lower k) (Vmat_lower k), U0_diag, one_mul]
  exact Vmat_diag_dvd k i

lemma isUnit_intCast_of_dvd_four (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (z : ℤ) (hz : z ∣ 4) :
    IsUnit (z : ZMod p) := by
  rw [isUnit_iff_ne_zero]
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h4 : (p : ℤ) ∣ ((2 ^ 2 : ℕ) : ℤ) := by
    have := dvd_trans h hz; norm_num at this ⊢; exact this
  have hp := (Fact.out : p.Prime)
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.mp h4)
  have := Nat.le_of_dvd (by norm_num) h2
  have := hp.two_le
  omega

variable {F : Type*} [Field F]

lemma map_mul_int {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℤ) (B : Matrix (Fin b) (Fin c) ℤ) :
    (A * B).map (Int.cast : ℤ → F) = A.map Int.cast * B.map Int.cast := by
  exact Matrix.map_mul (L := A) (M := B) (f := Int.castRingHom F)

lemma map_neg_int {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℤ) :
    (-A).map (Int.cast : ℤ → F) = -A.map Int.cast := by
  ext i j; simp

lemma graphGen_map_int (k : ℕ) (Φ : Fin 3 → Fin 3 → Matrix (Fin (2 * k)) (Fin k) ℤ) (c : Fin 3) :
    (graphGen k Φ c).map (Int.cast : ℤ → F) =
      graphGen k (fun c d => (Φ c d).map (Int.cast : ℤ → F)) c := by
  ext i j
  simp only [graphGen, map_apply, ent]
  split_ifs <;> simp

/-- The frame graph form has unimodular box matrices, so over any field its boxes are
injective. -/
lemma frameGraph_box_kernel (k : ℕ) (hk : 1 ≤ k) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k)
    (n : Fin (3 * k) → F)
    (hn : boxMatrix (graphGen k (fun c e => (graphBlock k (frameGen k) c e).map
      (Int.cast : ℤ → F))) d *ᵥ n = 0) : n = 0 := by
  have hG := Gk_isUnit k hk
  have hgg : (fun c => graphGen k (graphBlock k (frameGen k)) c * Gk k) = frameGen k := by
    funext c
    rw [graphGen_graphBlock k _ hG c, Matrix.mul_assoc, nonsing_inv_mul _ hG, Matrix.mul_one]
  have hbox : boxMatrix (graphGen k (graphBlock k (frameGen k))) d * Gk k =
      boxMatrix (frameGen k) d := by
    rw [← boxMatrix_mul_right, hgg]
  have hunit : IsUnit (boxMatrix (graphGen k (graphBlock k (frameGen k))) d).det := by
    have := isUnit_of_pm_one (frame_boxMinor k hk d hd)
    rw [← hbox, det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hmap : boxMatrix (graphGen k (fun c e => (graphBlock k (frameGen k) c e).map
      (Int.cast : ℤ → F))) d =
      (boxMatrix (graphGen k (graphBlock k (frameGen k))) d).map (Int.castRingHom F) := by
    rw [← boxMatrix_map]
    congr 1
    funext c
    exact (graphGen_map_int k _ c).symm
  have hunitF : IsUnit (boxMatrix (graphGen k (fun c e => (graphBlock k (frameGen k) c e).map
      (Int.cast : ℤ → F))) d).det := by
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hunit.map _
  apply mulVec_injective_of_isUnit_det _ hunitF
  rw [hn, mulVec_zero]

/-- `def:Q` is a gauge transform of the frame graph form. -/
lemma QPhi_gauge (k : ℕ) (hk : 1 ≤ k) (c e : Fin 3) (hce : c ≠ e) :
    (QPhiOf k (frameB k) (frameC k) c e).map (Int.cast : ℤ → F) =
      (muQ c e : F) • ((Rmat k).map Int.cast * (graphBlock k (frameGen k) c e).map Int.cast *
        (Ustar k).map Int.cast) := by
  unfold QPhiOf
  rw [if_neg (Ne.symm hce)]
  by_cases h1 : e = c + 1
  · rw [if_pos h1]
    simp only [muQ, if_pos h1, one_smul]
    rw [map_mul_int, map_mul_int, h1, frameB_eq k hk c]
    try rfl
  · have h2 : e = c + 2 := by
      fin_cases c <;> fin_cases e <;> simp_all <;> decide
    rw [if_neg h1]
    simp only [muQ, if_neg h1, neg_one_smul]
    rw [map_neg_int, map_mul_int, map_mul_int, h2, frameC_eq k hk c]
    try rfl

end Q

/-! ## Main statement -/

/-- **Theorem `thm:two`, net part** (all odd primes `p`, via `lem:gauge`). -/
theorem Q_net (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) :
    IsNet0 p (3 * k) (Qpoint p k) := by
  haveI := Fact.mk hp
  apply isNet0_of_box_injective
  intro d hd
  apply mulVec_injective_of_ker
  have hgen : (fun c => (QGen k c).map (Int.cast : ℤ → ZMod p)) =
      graphGen k (fun c e => (QPhiOf k (frameB k) (frameC k) c e).map (Int.cast : ℤ → ZMod p)) := by
    funext c
    exact graphGen_map_int k _ c
  rw [hgen]
  obtain ⟨lam, s, hlam, hs, hfac⟩ := muQ_factor (F := ZMod p) k d hd
  exact gauge_transfer k (by omega) _
    (fun c e => (graphBlock k (frameGen k) c e).map (Int.cast : ℤ → ZMod p))
    ((Rmat k).map Int.cast) (map_lower _ (Rmat_lower k)) (isUnit_map_diag _ (Rmat_diag k))
    ((Ustar k).map Int.cast) (map_lower _ (Ustar_lower k))
    (fun i => by rw [map_apply]; exact isUnit_intCast_of_dvd_four p hp2 _ (Ustar_diag_dvd k i))
    muQ (fun c e hce => QPhi_gauge k (by omega) c e hce) d hd lam s hlam hs hfac
    (fun n' hn' => frameGraph_box_kernel k (by omega) d hd n' hn')

end Z3Net.Proofs

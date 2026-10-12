module
public import Z3Net.NetPoly
public import Z3Net.KNDefs

@[expose] public section

/-!
# The Möbius frame in unequal-depth graph form, and the gauge moves (KN entry, net part)

Generic linear algebra for the net halves `B1_net`, `B2_net` (and reusable for `KN1_net`,
`KN2_net`):

* `T0 X` — every box matrix of `X` has trivial kernel (`t = 0` in kernel form);
  `T0.isNet0` turns it into `IsNet0` (via `Z3Net.Proofs.isNet0_of_box_injective`).
* moves preserving `T0`: right multiplication of all coordinates by a common invertible matrix
  (`T0_mul_right`, a change of index basis), and per-coordinate lower-triangular row operations
  with nonzero diagonal (`prefImp_updateRow`, `T0_of_prefImp`: the first `d` digits span the
  same space).
* graph form `gr X K c = X c * (boxMatrix X K)⁻¹`: its first `K c` rows are unit vectors
  (`gr_coarse`); `gr_row` describes the other rows.
* the frame `(τ², I, τ)` is `T0` for every `m` (`frame_T0`, from `Z3Net.Proofs.frame_kernel`), and
  `frameGF r p k` is its graph form with depths `depth r k`.
-/

namespace Z3NetKN.Frame

open Matrix Finset

section Generic

variable {𝕜 : Type*} [Field 𝕜] {m : ℕ}

/-- `t = 0` in kernel form: every box matrix has trivial kernel. -/
def T0 (X : Fin 3 → Matrix (Fin m) (Fin m) 𝕜) : Prop :=
  ∀ d : Fin 3 → ℕ, d 0 + d 1 + d 2 = m → ∀ v : Fin m → 𝕜,
    (∀ c (i : Fin m), (i : ℕ) < d c → (X c *ᵥ v) i = 0) → v = 0

lemma T0.injective {X : Fin 3 → Matrix (Fin m) (Fin m) 𝕜} (h : T0 X) (d : Fin 3 → ℕ)
    (hd : d 0 + d 1 + d 2 = m) : Function.Injective (Z3Net.boxMatrix X d).mulVec :=
  Z3Net.Proofs.mulVec_injective_of_ker _
    (fun v hv => h d hd v ((Z3Net.Proofs.boxMatrix_mulVec_eq_zero_iff X d hd v).1 hv))

/-- `A`'s prefix kernels are contained in `B`'s: if the first `d` digits of `A v` vanish, so do
those of `B v`. -/
def PrefImp (A B : Matrix (Fin m) (Fin m) 𝕜) : Prop :=
  ∀ (d : ℕ) (v : Fin m → 𝕜), (∀ i : Fin m, (i : ℕ) < d → (A *ᵥ v) i = 0) →
    ∀ i : Fin m, (i : ℕ) < d → (B *ᵥ v) i = 0

lemma PrefImp.refl (A : Matrix (Fin m) (Fin m) 𝕜) : PrefImp A A := fun _ _ h => h

lemma PrefImp.trans {A B C : Matrix (Fin m) (Fin m) 𝕜} (h1 : PrefImp A B) (h2 : PrefImp B C) :
    PrefImp A C :=
  fun d v h => h2 d v (h1 d v h)

lemma T0_of_prefImp {X Y : Fin 3 → Matrix (Fin m) (Fin m) 𝕜} (hX : T0 X)
    (h : ∀ c, PrefImp (Y c) (X c)) : T0 Y :=
  fun d hd v hv => hX d hd v (fun c => h c (d c) v (hv c))

/-- **Row move.** Replacing row `i0` by `β ᵥ* X` with `β` supported on `j ≤ i0` and `β i0 ≠ 0`
(a lower-triangular row operation) does not enlarge the prefix kernels. -/
lemma prefImp_updateRow (X : Matrix (Fin m) (Fin m) 𝕜) (i0 : Fin m) (β : Fin m → 𝕜)
    (hlow : ∀ j : Fin m, i0 < j → β j = 0) (hdiag : β i0 ≠ 0) :
    PrefImp (X.updateRow i0 (β ᵥ* X)) X := by
  intro d v hv i hi
  have hne : ∀ j : Fin m, j ≠ i0 → (j : ℕ) < d → (X *ᵥ v) j = 0 := by
    intro j hj hjd
    have := hv j hjd
    simpa [mulVec, updateRow_apply, hj] using this
  by_cases hii : i = i0
  · subst hii
    have h0 := hv i hi
    have hrw : (X.updateRow i (β ᵥ* X) *ᵥ v) i = β ⬝ᵥ (X *ᵥ v) := by
      rw [dotProduct_mulVec]
      simp only [mulVec, updateRow_self]
    rw [hrw, dotProduct, Finset.sum_eq_single i] at h0
    · exact (mul_eq_zero.mp h0).resolve_left hdiag
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [hne j hji (by have : (j : ℕ) < i := hlt; omega), mul_zero]
      · rw [hlow j hgt, zero_mul]
    · simp
  · exact hne i hii hi

/-- `vecMul` of a vector `β` vanishing at `i0` ignores row `i0`. -/
lemma vecMul_updateRow_of_zero (X : Matrix (Fin m) (Fin m) 𝕜) (i0 : Fin m) (w β : Fin m → 𝕜)
    (hβ : β i0 = 0) : β ᵥ* X.updateRow i0 w = β ᵥ* X := by
  ext col
  simp only [vecMul, dotProduct, updateRow_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j = i0
  · subst hj; simp [hβ]
  · simp [hj]

/-- Common change of index basis. -/
lemma T0_mul_right {X : Fin 3 → Matrix (Fin m) (Fin m) 𝕜} (hX : T0 X)
    (U : Matrix (Fin m) (Fin m) 𝕜) (hU : IsUnit U) : T0 (fun c => X c * U) := by
  intro d hd v hv
  have h1 : U *ᵥ v = 0 := hX d hd _ (fun c i hi => by simpa [mulVec_mulVec] using hv c i hi)
  exact (mulVec_injective_iff_isUnit.2 hU) (by rw [h1, mulVec_zero])

/-- Block offsets for depths `K` (the layout of `Z3Net.boxMatrix`). -/
def offK (K : Fin 3 → ℕ) (c : Fin 3) : ℕ :=
  if (c : ℕ) = 0 then 0 else if (c : ℕ) = 1 then K 0 else K 0 + K 1

lemma off_eq (r k : ℕ) : off r k = offK (depth r k) := rfl

lemma offK_lt (K : Fin 3 → ℕ) (hK : K 0 + K 1 + K 2 = m) (c : Fin 3) (j : ℕ) (hj : j < K c) :
    offK K c + j < m := by
  fin_cases c <;> simp [offK] at hj ⊢ <;> omega

/-- Row `offK K c + j` of the box matrix is row `j` of `X c`. -/
lemma boxMatrix_row (X : Fin 3 → Matrix (Fin m) (Fin m) 𝕜) (K : Fin 3 → ℕ)
    (hK : K 0 + K 1 + K 2 = m) (c : Fin 3) (j : Fin m) (hj : (j : ℕ) < K c) :
    Z3Net.boxMatrix X K ⟨offK K c + j, offK_lt K hK c j hj⟩ = X c j := by
  rcases c with ⟨_ | _ | _ | c, hc⟩
  · change (j : ℕ) < K 0 at hj
    simp [offK, Z3Net.boxMatrix, hj]
  · change (j : ℕ) < K 1 at hj
    simp only [offK]
    unfold Z3Net.boxMatrix
    simp only [Fin.isValue, zero_add, Nat.reduceAdd, one_ne_zero, ↓reduceIte]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1; ext; simp
  · change (j : ℕ) < K 2 at hj
    simp only [offK]
    unfold Z3Net.boxMatrix
    simp only [Fin.isValue, Nat.reduceAdd, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1; ext; simp; omega
  · omega

/-- Graph form with depths `K`. -/
noncomputable def gr (X : Fin 3 → Matrix (Fin m) (Fin m) 𝕜) (K : Fin 3 → ℕ) :
    Fin 3 → Matrix (Fin m) (Fin m) 𝕜 :=
  fun c => X c * (Z3Net.boxMatrix X K)⁻¹

lemma isUnit_box {X : Fin 3 → Matrix (Fin m) (Fin m) 𝕜} (hX : T0 X) (K : Fin 3 → ℕ)
    (hK : K 0 + K 1 + K 2 = m) : IsUnit (Z3Net.boxMatrix X K) :=
  mulVec_injective_iff_isUnit.1 (hX.injective K hK)

lemma T0_gr {X : Fin 3 → Matrix (Fin m) (Fin m) 𝕜} (hX : T0 X) (K : Fin 3 → ℕ)
    (hK : K 0 + K 1 + K 2 = m) : T0 (gr X K) :=
  T0_mul_right hX _ (isUnit_nonsing_inv_iff.2 (isUnit_box hX K hK))

lemma gr_row (X : Fin 3 → Matrix (Fin m) (Fin m) 𝕜) (K : Fin 3 → ℕ) (c : Fin 3) (i : Fin m) :
    gr X K c i = X c i ᵥ* (Z3Net.boxMatrix X K)⁻¹ := by
  ext j; rfl

/-- **Graph form (a).** The first `K c` rows of `gr X K c` are unit vectors. -/
lemma gr_coarse {X : Fin 3 → Matrix (Fin m) (Fin m) 𝕜} (hX : T0 X) (K : Fin 3 → ℕ)
    (hK : K 0 + K 1 + K 2 = m) (c : Fin 3) (j col : Fin m) (hj : (j : ℕ) < K c) :
    gr X K c j col = if (col : ℕ) = offK K c + j then 1 else 0 := by
  have hB := isUnit_box hX K hK
  have hr := boxMatrix_row X K hK c j hj
  have : gr X K c j col =
      (Z3Net.boxMatrix X K * (Z3Net.boxMatrix X K)⁻¹) ⟨offK K c + j, offK_lt K hK c j hj⟩ col := by
    rw [mul_apply, hr]; rfl
  rw [this, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hB), one_apply]
  by_cases h : (col : ℕ) = offK K c + j
  · rw [if_pos (Fin.ext h.symm), if_pos h]
  · rw [if_neg (fun h' => h (by rw [← h'])), if_neg h]

/-- Rows of a graph-form matrix combine like the index-basis vectors:
`(β ᵥ* X) col = β s · X s col + β (col - o)` on the block `[o, o + Kc)`, if `X`'s rows `j < Kc`
are the unit vectors at `o + j`, `s = Kc` and `β` vanishes beyond `Kc`. -/
lemma vecMul_graph (X : Matrix (Fin m) (Fin m) 𝕜) (o Kc : ℕ)
    (hX : ∀ j col : Fin m, (j : ℕ) < Kc → X j col = if (col : ℕ) = o + j then 1 else 0)
    (β : Fin m → 𝕜) (s : Fin m) (hs : (s : ℕ) = Kc) (hβ : ∀ j : Fin m, Kc < (j : ℕ) → β j = 0)
    (col : Fin m) :
    (β ᵥ* X) col = β s * X s col +
      (if h : o ≤ (col : ℕ) ∧ (col : ℕ) < o + Kc then β ⟨(col : ℕ) - o, by omega⟩ else 0) := by
  have hterm : ∀ j : Fin m, β j * X j col =
      (if j = s then β s * X s col else 0) +
        (if (j : ℕ) < Kc ∧ (col : ℕ) = o + j then β j else 0) := by
    intro j
    rcases lt_trichotomy (j : ℕ) Kc with h | h | h
    · have hjs : j ≠ s := fun e => by rw [e] at h; omega
      rw [if_neg hjs, hX j col h, zero_add]
      by_cases hc : (col : ℕ) = o + j
      · simp [hc, h]
      · simp [hc]
    · have hjs : j = s := Fin.ext (by omega)
      subst hjs
      rw [if_pos rfl, if_neg (by omega), add_zero]
    · have hjs : j ≠ s := fun e => by rw [e] at h; omega
      rw [hβ j h, if_neg hjs, if_neg (by omega)]
      simp
  simp only [vecMul, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  congr 1
  split_ifs with hb
  · rw [Finset.sum_eq_single ⟨(col : ℕ) - o, by omega⟩]
    · rw [if_pos ⟨by simp; omega, by simp; omega⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨_, h2⟩
      exact hj (Fin.ext (by simp; omega))
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hb ⟨by omega, by omega⟩

/-- A coarse (unit-vector) row reads off one index digit. -/
lemma mulVec_coarse (X : Matrix (Fin m) (Fin m) 𝕜) (o Kc : ℕ)
    (hX : ∀ j col : Fin m, (j : ℕ) < Kc → X j col = if (col : ℕ) = o + j then 1 else 0)
    (v : Fin m → 𝕜) (i : Fin m) (hi : (i : ℕ) < Kc) (hlt : o + i < m) :
    (X *ᵥ v) i = v ⟨o + i, hlt⟩ := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single ⟨o + i, hlt⟩]
  · rw [hX i _ hi, if_pos rfl, one_mul]
  · intro j _ hj
    rw [hX i _ hi, if_neg (fun h => hj (Fin.ext h)), zero_mul]
  · simp

/-- **Kernel test** in graph form: for a box `d` with `d c ≤ K c + 1`, a vector whose coarse
digits in the box vanish and which is killed by the first offset row of every coordinate with
`d c = K c + 1` is zero. -/
lemma kernel_test {G : Fin 3 → Matrix (Fin m) (Fin m) 𝕜} (hG : T0 G) (K : Fin 3 → ℕ)
    (hK : K 0 + K 1 + K 2 = m)
    (hGc : ∀ c (j col : Fin m), (j : ℕ) < K c → G c j col = if (col : ℕ) = offK K c + j then 1 else 0)
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = m) (hdK : ∀ c, d c ≤ K c + 1) (v : Fin m → 𝕜)
    (h1 : ∀ c (l : ℕ) (hl : l < K c), l < d c → v ⟨offK K c + l, offK_lt K hK c l hl⟩ = 0)
    (h2 : ∀ c, d c = K c + 1 → ∀ s : Fin m, (s : ℕ) = K c → (G c *ᵥ v) s = 0) : v = 0 := by
  apply hG d hd v
  intro c i hi
  by_cases hiK : (i : ℕ) < K c
  · rw [mulVec_coarse (G c) (offK K c) (K c) (hGc c) v i hiK (offK_lt K hK c i hiK)]
    exact h1 c i hiK hi
  · have := hdK c
    exact h2 c (by omega) i (by omega)

/-- **Unit pivot.** If the box `d` (with `d c ≤ K c + 1`) contains no coarse digit at column `n`
and `c0` is the only coordinate with `d c0 = K c0 + 1`, then the entry of `c0`'s first offset row
at column `n` is nonzero (it is a `1 × 1` box minor). -/
lemma pivot_single {G : Fin 3 → Matrix (Fin m) (Fin m) 𝕜} (hG : T0 G) (K : Fin 3 → ℕ)
    (hK : K 0 + K 1 + K 2 = m)
    (hGc : ∀ c (j col : Fin m), (j : ℕ) < K c → G c j col = if (col : ℕ) = offK K c + j then 1 else 0)
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = m) (hdK : ∀ c, d c ≤ K c + 1) (n : Fin m)
    (hn : ∀ c (l : ℕ), l < K c → l < d c → offK K c + l ≠ (n : ℕ))
    (c0 : Fin 3) (hc0 : ∀ c, d c = K c + 1 → c = c0) (s : Fin m) (hs : (s : ℕ) = K c0) :
    G c0 s n ≠ 0 := by
  intro h0
  have hv := kernel_test hG K hK hGc d hd hdK (Pi.single n 1)
    (by
      intro c l hl hld
      rw [Pi.single_apply, if_neg]
      intro heq
      exact hn c l hl hld (congrArg Fin.val heq))
    (by
      intro c hc s' hs'
      have := hc0 c hc
      subst this
      have hss : s' = s := Fin.ext (by rw [hs, hs'])
      rw [mulVec_single_one, Matrix.col_apply, hss, h0])
  have := congrFun hv n
  simp at this

/-- A box given by its three sides. -/
def box3 (a b c : ℕ) : Fin 3 → ℕ := fun e => if (e : ℕ) = 0 then a else if (e : ℕ) = 1 then b else c

lemma box3_sum (a b c : ℕ) : box3 a b c 0 + box3 a b c 1 + box3 a b c 2 = a + b + c := by
  simp [box3]

/-- Rows of `C * U` combine like the rows of `C`. -/
lemma row_mul_right (A U : Matrix (Fin m) (Fin m) 𝕜) (i : Fin m) : (A * U) i = A i ᵥ* U := by
  ext j; rfl

end Generic

/-! ## The frame `(τ², I, τ)` -/

/-- The integer frame `(τ², I, τ)` on `ℤ[t]_{<m}`. -/
def frameZ (m : ℕ) : Fin 3 → Matrix (Fin m) (Fin m) ℤ :=
  ![Z3Net.tau m * Z3Net.tau m, 1, Z3Net.tau m]

/-- The frame over a field. -/
def frameF (𝕜 : Type*) [Field 𝕜] (m : ℕ) : Fin 3 → Matrix (Fin m) (Fin m) 𝕜 :=
  fun c => (frameZ m c).map (Int.cast : ℤ → 𝕜)

theorem frame_T0 (𝕜 : Type*) [Field 𝕜] (m : ℕ) (hm : 0 < m) : T0 (frameF 𝕜 m) := by
  intro d hd v hv
  have hmap : ((Z3Net.tau m * Z3Net.tau m).map (Int.cast : ℤ → 𝕜)) =
      (Z3Net.tau m).map (Int.cast : ℤ → 𝕜) * (Z3Net.tau m).map (Int.cast : ℤ → 𝕜) :=
    Matrix.map_mul (f := Int.castRingHom 𝕜)
  have e0 : frameF 𝕜 m 0 =
      (Z3Net.tau m).map (Int.cast : ℤ → 𝕜) * (Z3Net.tau m).map (Int.cast : ℤ → 𝕜) := by
    rw [← hmap]; rfl
  have e1 : frameF 𝕜 m 1 = 1 := by
    ext a b
    simp [frameF, frameZ, Matrix.one_apply]
  apply Z3Net.Proofs.frame_kernel m hm v (d 0) (d 1) (d 2) hd
  · intro i hi
    have := hv 0 i hi
    rwa [e0, ← mulVec_mulVec] at this
  · intro i hi
    have := hv 1 i hi
    rwa [e1, one_mulVec] at this
  · intro i hi
    exact hv 2 i hi

/-- The frame's graph form with the unequal depths `depth r k` (`m = 3k + r`), over `𝔽_p`. -/
noncomputable def frameGF (r p k : ℕ) (c : Fin 3) :
    Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p) :=
  ((![Z3Net.tau (3 * k + r) * Z3Net.tau (3 * k + r), 1, Z3Net.tau (3 * k + r)] :
      Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) ℤ) c).map (Int.cast : ℤ → ZMod p) *
    (Z3Net.boxMatrix (fun c => ((![Z3Net.tau (3 * k + r) * Z3Net.tau (3 * k + r), 1,
      Z3Net.tau (3 * k + r)] : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) ℤ) c).map
        (Int.cast : ℤ → ZMod p)) (depth r k))⁻¹

lemma frameGF_eq (r p k : ℕ) [Fact p.Prime] : frameGF r p k = gr (frameF (ZMod p) (3 * k + r)) (depth r k) := rfl

lemma depth_sum (r k : ℕ) (hr : r ≤ 3) : depth r k 0 + depth r k 1 + depth r k 2 = 3 * k + r := by
  simp only [depth, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  interval_cases r <;> simp <;> omega

/-- The frame graph form is `t = 0` and in graph form (a), for every prime `p`. -/
theorem frameGF_T0 (r p k : ℕ) [Fact p.Prime] (hr : r ≤ 3) (hm : 0 < 3 * k + r) :
    T0 (frameGF r p k) :=
  T0_gr (frame_T0 (ZMod p) _ hm) _ (depth_sum r k hr)

theorem frameGF_coarse (r p k : ℕ) [Fact p.Prime] (hr : r ≤ 3) (hm : 0 < 3 * k + r)
    (c : Fin 3) (j col : Fin (3 * k + r)) (hj : (j : ℕ) < depth r k c) :
    frameGF r p k c j col = if (col : ℕ) = off r k c + j then 1 else 0 :=
  gr_coarse (frame_T0 (ZMod p) _ hm) _ (depth_sum r k hr) c j col hj

/-- `T0` gives the `(0,m,3)`-net property. -/
theorem T0.isNet0 {p m : ℕ} [NeZero p] {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p)}
    [Fact p.Prime] (h : T0 C) : IsNet0 p m (digPoint p m C) :=
  Z3Net.Proofs.isNet0_of_box_injective p m C (fun d hd => h.injective d hd)

end Z3NetKN.Frame

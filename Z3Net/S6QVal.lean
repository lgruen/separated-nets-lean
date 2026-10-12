/-
Proof module (stage 6, main entry): `prop:Qnet`, the explicit value of the box minors of `𝒬_k`,
the even-`q` negative, and `𝒬_{2,q}` in every base.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.NetQOdd
public import Z3Net.FBox
public import Z3Net.FSep

@[expose] public section

/-!
# `prop:Qnet`: the box minors of `𝒬_k` are `± ∏_{c : d_c < k} ∏_{j = d_c}^{k-1} Γ_jj`

The proof runs the reduced box matrix of `lem:box` (entry F, `Z3NetF.Proofs.box_minor`, `Dm_LU`)
over `ℤ`: on the (over, under) blocks, `𝒬_k` is `(λ_c R) Φ^F_ce (s_e U_*)` with signs `λ_c s_e`
(the block signs of `def:Q` factor on these blocks, `muZ_factor`), so the reduced matrix of `𝒬_k`
is `A D B` with `D` that of the frame, `det A = ±1` (`R` unitriangular) and
`det B = ± ∏ (U_*)_jj = ± ∏ Γ_jj` over the last `k - d_e` levels of the under coordinates `e`.
The frame graph form has box minors `±1`.
-/

namespace Z3Net.Proofs

open Matrix Finset

noncomputable section

namespace QVal

/-! ## Bridges to entry F's graph forms -/

lemma boxMatrix_bridge {R : Type*} [Zero R] {m : ℕ} (C : Fin 3 → Matrix (Fin m) (Fin m) R)
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = m) :
    Z3Net.boxMatrix C d = Z3NetF.boxMatrix C d := by
  ext r l
  have hr := r.isLt
  unfold Z3Net.boxMatrix Z3NetF.boxMatrix
  simp only [List.ofFn_succ, List.ofFn_zero, Z3NetF.boxLoc, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  split_ifs <;> first | rfl | omega | (simp_all; omega)

/-- Reindex the rows `Fin (2k)` of a main-entry graph form to entry F's `Fin (3k - k)`. -/
def castΦ {R : Type*} (k : ℕ) (Φ : Fin 3 → Fin 3 → Matrix (Fin (2 * k)) (Fin k) R) :
    (c d : Fin 3) → Matrix (Fin (3 * k - k)) (Fin k) R :=
  fun c d r l => Φ c d ⟨r, by have := r.isLt; omega⟩ l

lemma graphGen_bridge {R : Type*} [Zero R] [One R] (k : ℕ)
    (Φ : Fin 3 → Fin 3 → Matrix (Fin (2 * k)) (Fin k) R) :
    Z3Net.graphGen k Φ = Z3NetF.graphGenK (m := 3 * k) (fun _ => k) (castΦ k Φ) := by
  rw [Z3NetF.Proofs.graphGenK_const]
  funext c
  ext i j
  simp only [Z3Net.graphGen, Z3NetU.graphGen]
  by_cases hi : (i : ℕ) < k
  · simp only [if_pos hi, dif_pos hi]
  · simp only [if_neg hi, dif_neg hi]
    have hj := j.isLt
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at hj
      · exact h
    unfold Z3Net.ent castΦ
    rw [dif_pos ⟨by omega, Nat.mod_lt _ hk0⟩]

/-! ## Exact determinants of the factors -/

variable {s m : ℕ} (K d : Fin s → ℕ)

lemma det_Ablk_eq {R : Type*} [CommRing R] (hd : ∑ c, d c = m)
    (L : (c : Fin s) → Matrix (Fin (m - K c)) (Fin (m - K c)) R)
    (hL : ∀ c i j, i < j → L c i j = 0) :
    (Z3NetF.Proofs.Ablk K d hd L).det = ∏ x : Z3NetF.OverRows K d,
      L x.1.1 ⟨x.2, by have := x.2.isLt; have := Z3NetF.Proofs.le_of_sum d hd x.1.1; omega⟩
        ⟨x.2, by have := x.2.isLt; have := Z3NetF.Proofs.le_of_sum d hd x.1.1; omega⟩ := by
  letI : LinearOrder (Z3NetF.OverRows K d) :=
    LinearOrder.lift' _ (Z3NetF.Proofs.posR_inj K d hd)
  rw [det_of_isLowerTriangular]
  · refine Finset.prod_congr rfl fun x _ => ?_
    simp [Z3NetF.Proofs.Ablk]
  · intro x x' hxx'
    simp only [Z3NetF.Proofs.Ablk]
    split_ifs with h
    · obtain ⟨⟨c, hc⟩, r⟩ := x
      obtain ⟨⟨c', hc'⟩, r'⟩ := x'
      simp only at h
      subst h
      apply hL
      have : ((Z3NetF.Proofs.rowF K d hd (Sum.inr ⟨⟨c, hc⟩, r⟩) : Fin m) : ℕ) <
          ((Z3NetF.Proofs.rowF K d hd (Sum.inr ⟨⟨c, hc'⟩, r'⟩) : Fin m) : ℕ) := hxx'
      simp only [Z3NetF.Proofs.rowF] at this
      show (r : ℕ) < r'
      omega
    · rfl

lemma det_Bblk_eq {R : Type*} [CommRing R] (hK : ∑ c, K c = m)
    (U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) R)
    (hU : ∀ d i j, i < j → U d i j = 0) :
    (Z3NetF.Proofs.Bblk K d U).det = ∏ y : Z3NetF.UnderCols K d,
      U y.1.1 ⟨d y.1.1 + (y.2 : ℕ), by have := y.2.isLt; have := y.1.2; omega⟩
        ⟨d y.1.1 + (y.2 : ℕ), by have := y.2.isLt; have := y.1.2; omega⟩ := by
  letI : LinearOrder (Z3NetF.UnderCols K d) :=
    LinearOrder.lift' _ (Z3NetF.Proofs.posC_inj K d hK)
  rw [det_of_isLowerTriangular]
  · refine Finset.prod_congr rfl fun y _ => ?_
    simp [Z3NetF.Proofs.Bblk]
  · intro y' y hyy
    simp only [Z3NetF.Proofs.Bblk]
    split_ifs with h
    · obtain ⟨⟨e, he⟩, l⟩ := y
      obtain ⟨⟨e', he'⟩, l'⟩ := y'
      simp only at h
      subst h
      apply hU
      have : ((Z3NetF.Proofs.colF K d hK (Sum.inr ⟨⟨e', he'⟩, l'⟩) : Fin m) : ℕ) <
          ((Z3NetF.Proofs.colF K d hK (Sum.inr ⟨⟨e', he⟩, l⟩) : Fin m) : ℕ) := hyy
      simp only [Z3NetF.Proofs.colF] at this
      show d e' + (l' : ℕ) < d e' + l
      omega
    · rfl

lemma prod_pm_one {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ) (hf : ∀ i, f i = 1 ∨ f i = -1) :
    ∏ i ∈ S, f i = 1 ∨ ∏ i ∈ S, f i = -1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha]
    rcases hf a with h | h <;> rcases ih with h' | h' <;> rw [h, h'] <;> norm_num

/-! ## The block signs of `def:Q` over `ℤ` -/

/-- `+1` on the blocks `Φ_{c,c+1}`, `-1` on `Φ_{c,c+2}`. -/
def muZ (c e : Fin 3) : ℤ := if e = c + 1 then 1 else -1

lemma muZ_pm (c e : Fin 3) : muZ c e = 1 ∨ muZ c e = -1 := by
  unfold muZ; split_ifs <;> simp

lemma muZ_factor (k : ℕ) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    ∃ lam s : Fin 3 → ℤ, (∀ c, lam c = 1 ∨ lam c = -1) ∧ (∀ e, s e = 1 ∨ s e = -1) ∧
      ∀ c e, c ≠ e → k < d c → d e ≤ k → muZ c e = lam c * s e := by
  by_cases h01 : k < d 0 ∧ k < d 1
  · refine ⟨fun c => muZ c 2, 1, fun c => muZ_pm _ _, fun _ => Or.inl rfl, ?_⟩
    intro c e hce hc he
    have : e = 2 := by fin_cases e <;> simp_all <;> omega
    subst this; simp
  by_cases h02 : k < d 0 ∧ k < d 2
  · refine ⟨fun c => muZ c 1, 1, fun c => muZ_pm _ _, fun _ => Or.inl rfl, ?_⟩
    intro c e hce hc he
    have : e = 1 := by fin_cases e <;> simp_all <;> omega
    subst this; simp
  by_cases h12 : k < d 1 ∧ k < d 2
  · refine ⟨fun c => muZ c 0, 1, fun c => muZ_pm _ _, fun _ => Or.inl rfl, ?_⟩
    intro c e hce hc he
    have : e = 0 := by fin_cases e <;> simp_all <;> omega
    subst this; simp
  · let c0 : Fin 3 := if k < d 0 then 0 else if k < d 1 then 1 else 2
    refine ⟨1, fun e => muZ c0 e, fun _ => Or.inl rfl, fun e => muZ_pm _ _, ?_⟩
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

lemma QPhi_gaugeZ (k : ℕ) (hk : 1 ≤ k) (c e : Fin 3) (hce : c ≠ e) :
    QPhiOf k (frameB k) (frameC k) c e =
      muZ c e • (Rmat k * graphBlock k (frameGen k) c e * Ustar k) := by
  unfold QPhiOf
  rw [if_neg (Ne.symm hce)]
  by_cases h1 : e = c + 1
  · rw [if_pos h1]
    simp only [muZ, if_pos h1, one_smul]
    rw [h1, frameB_eq k hk c]
  · have h2 : e = c + 2 := by
      fin_cases c <;> fin_cases e <;> simp_all
    rw [if_neg h1]
    simp only [muZ, if_neg h1, neg_one_smul]
    rw [h2, frameC_eq k hk c]

/-! ## Products over the under columns -/

lemma prod_shift (k a : ℕ) (g : ℕ → ℤ) :
    ∏ l : Fin (k - a), g (a + l) = ∏ j : Fin k, (if a ≤ (j : ℕ) then g j else 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun l => g (a + l)),
    Fin.prod_univ_eq_prod_range (fun j => if a ≤ j then g j else 1), Finset.prod_ite,
    Finset.prod_const_one, mul_one, ← Finset.prod_Ico_eq_prod_range]
  congr 1
  ext j; simp [Finset.mem_Ico]; omega

lemma under_prod (k : ℕ) (d : Fin 3 → ℕ) (g : Fin 3 → ℕ → ℤ) :
    ∏ y : Z3NetF.UnderCols (fun _ => k) d, g y.1.1 (d y.1.1 + (y.2 : ℕ)) =
      ∏ c : Fin 3, ∏ j : Fin k, (if d c ≤ (j : ℕ) then g c j else 1) := by
  rw [Fintype.prod_sigma]
  simp only
  rw [← Finset.prod_subtype (univ.filter fun e : Fin 3 => d e < k) (by simp)
    (fun e => ∏ l : Fin (k - d e), g e (d e + l))]
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun c _ => ?_
  split_ifs with h
  · exact prod_shift k (d c) (g c)
  · symm
    exact Finset.prod_eq_one fun j _ => by rw [if_neg (by have := j.isLt; omega)]

/-! ## The value -/

/-! ## The value -/

lemma sum_cast {k : ℕ} (f : Fin (2 * k) → ℤ) :
    ∑ j : Fin (3 * k - k), f ⟨j, by have := j.isLt; omega⟩ = ∑ j : Fin (2 * k), f j := by
  have h : 3 * k - k = 2 * k := by omega
  exact Fin.sum_congr' f h

/-- `castR`: `R` with rows and columns indexed by `Fin (3k - k)`. -/
def castR (k : ℕ) : Matrix (Fin (3 * k - k)) (Fin (3 * k - k)) ℤ :=
  fun i j => Rmat k ⟨i, by have := i.isLt; omega⟩ ⟨j, by have := j.isLt; omega⟩

lemma castΦ_gauge (k : ℕ) (X : Matrix (Fin (2 * k)) (Fin k) ℤ) (t u : ℤ) :
    (Matrix.of fun (r : Fin (3 * k - k)) (l : Fin k) =>
        ((t * u) • (Rmat k * X * Ustar k)) ⟨r, by have := r.isLt; omega⟩ l) =
      (t • castR k) * (Matrix.of fun (r' : Fin (3 * k - k)) (l' : Fin k) =>
        X ⟨r', by have := r'.isLt; omega⟩ l') * (u • Ustar k) := by
  ext r l
  simp only [Matrix.smul_apply, mul_apply, smul_eq_mul, castR, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j1 _ => ?_
  refine Fintype.sum_equiv (finCongr (by omega : 3 * k - k = 2 * k)).symm _ _ (fun j => ?_)
  simp only [finCongr_symm, finCongr_apply, Fin.cast]
  ring

lemma frameGraph_det (k : ℕ) (hk : 1 ≤ k) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    (Z3Net.boxMatrix (graphGen k (graphBlock k (frameGen k))) d).det = 1 ∨
      (Z3Net.boxMatrix (graphGen k (graphBlock k (frameGen k))) d).det = -1 := by
  have hG := Gk_isUnit k hk
  have hgg : (fun c => graphGen k (graphBlock k (frameGen k)) c * Gk k) = frameGen k := by
    funext c
    rw [graphGen_graphBlock k _ hG c, Matrix.mul_assoc, nonsing_inv_mul _ hG]
    exact Matrix.mul_one _
  have hbox : Z3Net.boxMatrix (graphGen k (graphBlock k (frameGen k))) d * Gk k =
      Z3Net.boxMatrix (frameGen k) d := by
    rw [← boxMatrix_mul_right, hgg]
  have hunit : IsUnit (Z3Net.boxMatrix (graphGen k (graphBlock k (frameGen k))) d).det := by
    have := isUnit_of_pm_one (frame_boxMinor k hk d hd)
    rw [← hbox, det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  exact Int.isUnit_iff.mp hunit

theorem Q_boxMinor_value (k : ℕ) (hk : 2 ≤ k) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    (boxMatrix (QGen k) d).det =
        ∏ c : Fin 3, ∏ j : Fin k, (if d c ≤ (j : ℕ) then Vmat k j j else 1) ∨
      (boxMatrix (QGen k) d).det =
        -∏ c : Fin 3, ∏ j : Fin k, (if d c ≤ (j : ℕ) then Vmat k j j else 1) := by
  classical
  have hk1 : 1 ≤ k := by omega
  set K : Fin 3 → ℕ := fun _ => k with hKdef
  have hK : ∑ c, K c = 3 * k := by simp only [K, Fin.sum_univ_three]; ring
  have hdF : ∑ c, d c = 3 * k := by rw [Fin.sum_univ_three]; exact hd
  set QΦ := QPhiOf k (frameB k) (frameC k) with hQΦ
  set FΦ := graphBlock k (frameGen k) with hFΦ
  have hQ : Z3Net.boxMatrix (QGen k) d =
      Z3NetF.boxMatrix (Z3NetF.graphGenK (m := 3 * k) K (castΦ k QΦ)) d := by
    rw [boxMatrix_bridge _ d hd]; unfold QGen; rw [graphGen_bridge]
  have hF : Z3Net.boxMatrix (graphGen k FΦ) d =
      Z3NetF.boxMatrix (Z3NetF.graphGenK (m := 3 * k) K (castΦ k FΦ)) d := by
    rw [boxMatrix_bridge _ d hd, graphGen_bridge]
  have hFdet := frameGraph_det k hk1 d hd
  rw [hF] at hFdet
  obtain ⟨⟨σ⟩, H⟩ := Z3NetF.Proofs.box_minor (R := ℤ) K d hK hdF
  obtain ⟨ε, -, hε⟩ := H σ
  obtain ⟨lam, sg, hlam, hsg, hfac⟩ := muZ_factor k d hd
  set L : (c : Fin 3) → Matrix (Fin (3 * k - K c)) (Fin (3 * k - K c)) ℤ :=
    fun c => lam c • castR k with hLdef
  set U : (e : Fin 3) → Matrix (Fin (K e)) (Fin (K e)) ℤ := fun e => sg e • Ustar k with hUdef
  set Ψ : (c e : Fin 3) → Matrix (Fin (3 * k - K c)) (Fin (K e)) ℤ :=
    fun c e => L c * castΦ k FΦ c e * U e with hΨ
  have hL : ∀ c i j, i < j → L c i j = 0 := by
    intro c i j h
    simp only [hLdef, Matrix.smul_apply, castR, smul_eq_mul]
    rw [Rmat_lower k _ _ (show (⟨i, _⟩ : Fin (2 * k)) < ⟨j, _⟩ from h), mul_zero]
  have hU : ∀ e i j, i < j → U e i j = 0 := by
    intro e i j h
    simp only [hUdef, Matrix.smul_apply, smul_eq_mul]
    rw [Ustar_lower k i j h, mul_zero]
  have hblk : ∀ c e, c ≠ e → k < d c → d e ≤ k → castΦ k QΦ c e = Ψ c e := by
    intro c e hce hc he
    have e1 : castΦ k QΦ c e = Matrix.of fun (r : Fin (3 * k - k)) (l : Fin k) =>
        ((lam c * sg e) • (Rmat k * FΦ c e * Ustar k)) ⟨r, by have := r.isLt; omega⟩ l := by
      ext r l
      simp only [castΦ, Matrix.of_apply, hQΦ]
      rw [QPhi_gaugeZ k hk1 c e hce, hfac c e hce hc he]
    rw [e1, castΦ_gauge]
    rfl
  have hDm : Z3NetF.Proofs.Dm K d hdF (castΦ k QΦ) = Z3NetF.Proofs.Dm K d hdF Ψ := by
    ext x y
    obtain ⟨⟨c, hc⟩, r⟩ := x
    obtain ⟨⟨e, he⟩, l⟩ := y
    have hce : c ≠ e := by intro h'; subst h'; simp only [K] at hc he; omega
    simp only [Z3NetF.Proofs.Dm]
    rw [hblk c e hce (by simpa [K] using hc) (by simp only [K] at he; omega)]
  have hDmLU := Z3NetF.Proofs.Dm_LU K d hdF L U hL hU (castΦ k FΦ) Ψ (fun c e _ => rfl)
  have hsub : ∀ (A : Matrix (Z3NetF.OverRows K d) (Z3NetF.OverRows K d) ℤ)
      (D : Matrix (Z3NetF.OverRows K d) (Z3NetF.UnderCols K d) ℤ)
      (B : Matrix (Z3NetF.UnderCols K d) (Z3NetF.UnderCols K d) ℤ),
      (A * D * B).submatrix σ id = A.submatrix σ σ * D.submatrix σ id * B := by
    intro A D B
    ext x y
    simp only [submatrix_apply, mul_apply, id]
    refine Finset.sum_congr rfl fun y' _ => ?_
    congr 1
    exact (Equiv.sum_comp σ (fun x' => A (σ x) x' * D x' y')).symm
  have hval : (Z3Net.boxMatrix (QGen k) d).det =
      (Z3NetF.Proofs.Ablk K d hdF L).det * (Z3NetF.Proofs.Bblk K d U).det *
        (Z3NetF.boxMatrix (Z3NetF.graphGenK (m := 3 * k) K (castΦ k FΦ)) d).det := by
    rw [hQ, hε, hε, Z3NetF.Proofs.redBox_eq K d hdF, Z3NetF.Proofs.redBox_eq K d hdF, hDm, hDmLU,
      hsub, det_mul, det_mul, det_submatrix_equiv_self]
    ring
  -- the factors
  have hA : (Z3NetF.Proofs.Ablk K d hdF L).det = 1 ∨ (Z3NetF.Proofs.Ablk K d hdF L).det = -1 := by
    rw [det_Ablk_eq K d hdF L hL]
    apply prod_pm_one
    intro x
    simp only [hLdef]
    rw [Matrix.smul_apply]
    simp only [castR, Rmat, smul_eq_mul]
    rw [if_pos trivial, mul_one]
    exact hlam _
  have hdiag : ∀ j : Fin k, Ustar k j j = Vmat k j j := by
    intro j
    rw [Ustar, diag_mul_of_lower _ _ (U0_lower k) (Vmat_lower k), U0_diag, one_mul]
  have hB : (Z3NetF.Proofs.Bblk K d U).det =
      (∏ y : Z3NetF.UnderCols K d, sg y.1.1) *
        ∏ c : Fin 3, ∏ j : Fin k, (if d c ≤ (j : ℕ) then Vmat k j j else 1) := by
    rw [det_Bblk_eq K d hK U hU]
    simp only [hUdef, Matrix.smul_apply, smul_eq_mul, hdiag]
    rw [Finset.prod_mul_distrib]
    congr 1
    have := under_prod k d (fun _ j => if h : j < k then Vmat k ⟨j, h⟩ ⟨j, h⟩ else 1)
    simp only at this
    convert this using 2 with y c _ j _
    · rw [dif_pos (by have := y.2.isLt; have := y.1.2; simp only [K] at *; omega)]
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [dif_pos j.isLt]
  have hs : (∏ y : Z3NetF.UnderCols K d, sg y.1.1) = 1 ∨ (∏ y : Z3NetF.UnderCols K d, sg y.1.1) = -1 :=
    prod_pm_one _ _ (fun y => hsg _)
  rw [hval, hB]
  rcases hA with hA | hA <;> rcases hs with hs | hs <;> rcases hFdet with hf | hf <;>
    rw [hA, hs, hf] <;> [left; right; right; left; right; left; left; right] <;> ring

/-! ## Consequences: even `q`, and `k = 2` -/

lemma isNet0_iff_F (q m : ℕ) (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod q)) :
    Z3Net.IsNet0 q m (Z3Net.digPoint q m C) ↔ Z3NetF.IsNet0 3 q m (Z3NetF.digPoint q m C) := by
  constructor
  · intro h d hd a ha
    exact h d (by rw [Fin.sum_univ_three] at hd; exact hd) a ha
  · intro h d hd a ha
    exact h d (by rw [Fin.sum_univ_three]; exact hd) a ha

lemma Qbox_cast (q k : ℕ) (d : Fin 3 → ℕ) :
    (Z3Net.boxMatrix (fun c => (QGen k c).map (Int.cast : ℤ → ZMod q)) d).det =
      (((Z3Net.boxMatrix (QGen k) d).det : ℤ) : ZMod q) := by
  rw [show (fun c => (QGen k c).map (Int.cast : ℤ → ZMod q)) =
      (fun c => (QGen k c).map (Int.castRingHom (ZMod q))) from rfl, boxMatrix_map,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

lemma Vmat_diag (k : ℕ) (j : ℕ) (hj : j < k) :
    Vmat k ⟨j, hj⟩ ⟨j, hj⟩ =
      if j + 1 = k then -1 else if j + 3 = k then -2 else if j + 4 = k then 4 else 1 := by
  unfold Vmat
  simp only
  split_ifs <;> omega

lemma prod_last3 (k : ℕ) (hk : 3 ≤ k) :
    ∏ j : Fin k, (if k - 3 ≤ (j : ℕ) then Vmat k j j else 1) = 2 := by
  set g : ℕ → ℤ := fun j => if h : j < k then Vmat k ⟨j, h⟩ ⟨j, h⟩ else 1 with hg
  have e1 : ∏ j : Fin k, (if k - 3 ≤ (j : ℕ) then Vmat k j j else 1) =
      ∏ j : Fin k, (if k - 3 ≤ (j : ℕ) then g j else 1) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hg, dif_pos j.isLt]
  rw [e1, ← prod_shift k (k - 3) g, show k - (k - 3) = 3 by omega, Fin.prod_univ_three]
  simp only [hg, Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega), Vmat_diag, Vmat_diag, Vmat_diag]
  rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  norm_num

/-- **`prop:Qnet`, the even-`q` negative**: for even `q` and `k ≥ 3`, the box `(k+3, k-3, k)` has
minor `±2`, so `𝒬_{k,q}` is not a `(0,3k,3)`-net. -/
theorem Q_not_net_even (q k : ℕ) (hq : Even q) (hq2 : 2 ≤ q) (hk : 3 ≤ k) :
    ¬ IsNet0 q (3 * k) (Qpoint q k) := by
  intro hnet
  haveI : NeZero q := ⟨by omega⟩
  set d : Fin 3 → ℕ := ![k + 3, k - 3, k] with hdd
  have hd : d 0 + d 1 + d 2 = 3 * k := by simp [d]; omega
  have hF := (isNet0_iff_F q (3 * k) _).1 hnet
  have hu := (Z3NetF.Proofs.nie_zmod q _).1 hF d (by rw [Fin.sum_univ_three]; exact hd)
  rw [← boxMatrix_bridge _ d hd, Qbox_cast] at hu
  have hP : ∏ c : Fin 3, ∏ j : Fin k, (if d c ≤ (j : ℕ) then Vmat k j j else 1) = 2 := by
    rw [Fin.prod_univ_three]
    have h0 : ∏ j : Fin k, (if d 0 ≤ (j : ℕ) then Vmat k j j else 1) = 1 :=
      Finset.prod_eq_one fun j _ => by rw [if_neg (by have := j.isLt; simp [d] <;> omega)]
    have h2 : ∏ j : Fin k, (if d 2 ≤ (j : ℕ) then Vmat k j j else 1) = 1 :=
      Finset.prod_eq_one fun j _ => by rw [if_neg (by have := j.isLt; simp [d] <;> omega)]
    rw [h0, h2, show d 1 = k - 3 from rfl, prod_last3 k hk]
    norm_num
  have hodd : ¬ Nat.Coprime 2 q := by
    rw [Nat.coprime_two_left]; exact Nat.not_odd_iff_even.mpr hq
  have hu2 : IsUnit ((2 : ℕ) : ZMod q) := by
    rcases Q_boxMinor_value k (by omega) d hd with h | h <;> rw [h, hP] at hu
    · exact_mod_cast hu
    · have : IsUnit (-(((2 : ℕ) : ZMod q))) := by exact_mod_cast hu
      exact (IsUnit.neg_iff _).mp this
  exact hodd ((ZMod.isUnit_iff_coprime 2 q).mp hu2)

/-- **`𝒬_{2,q}` in every base** (the remark after `prop:Qnet`): `Γ = diag(1, -1)` for `k = 2`, so
every box minor is `±1` and `𝒬_{2,q}` is a `(0,6,3)`-net over `ℤ/qℤ` for every `q ≥ 2`. -/
theorem Q2_net (q : ℕ) (hq : 2 ≤ q) : IsNet0 q (3 * 2) (Qpoint q 2) := by
  have : NeZero q := ⟨by omega⟩
  apply (isNet0_iff_F q (3 * 2) _).2
  apply (Z3NetF.Proofs.nie_zmod q _).2
  intro d hd
  have hd' : d 0 + d 1 + d 2 = 3 * 2 := by rw [Fin.sum_univ_three] at hd; exact hd
  rw [← boxMatrix_bridge _ d hd', Qbox_cast]
  have hV : ∀ j : Fin 2, Vmat 2 j j = 1 ∨ Vmat 2 j j = -1 := by decide
  have hP := prod_pm_one (univ : Finset (Fin 3))
    (fun c => ∏ j : Fin 2, (if d c ≤ (j : ℕ) then Vmat 2 j j else 1))
    (fun c => prod_pm_one _ _ (fun j => by split_ifs <;> [exact hV j; exact Or.inl rfl]))
  rcases Q_boxMinor_value 2 le_rfl d hd' with h | h <;> rw [h] <;>
    rcases hP with hP | hP <;> rw [hP] <;> simp

end QVal

end

end Z3Net.Proofs

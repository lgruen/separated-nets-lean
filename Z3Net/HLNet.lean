module
public import Mathlib
public import Z3Net.HLDefs
public import Z3Net.HLFrame
public import Z3Net.HLQr
public import Z3Net.SUThm1

@[expose] public section

/-!
# Entry HL, part 3: the net property for every `k` (`HL_net`)

The net is the split frame read through lower-triangular scrambles: with the coefficients
`m_d = U'^(k)_d n_d` of the cell vector `n` in the basis `E_{d,j}`, the polynomial
`V = ∑ m_{d,j} E_{d,j}` has cells `U0_c m_c` (`U0_c` lower triangular with unit diagonal
`∏_{d' ≠ c} (v_c - v_{d'})^k`) and the offset digit `k + r` of coordinate `c` is
`(own terms in n_c) + s_{c,r} · (digit k + r of reading c of V)` with a unit `s_{c,r}`.
Vanishing first digits of the net force vanishing first split-frame digits of `V`; the `2s`
points have unit differences, so `V` is divisible by a monic polynomial of degree `sk` (Lemma T′,
kernel form) and `V = 0`, whence `n = 0`.
-/

namespace Z3NetHL.Proofs

open Polynomial Finset Matrix

noncomputable section

/-! ## Bridges -/

lemma graphGen_eq {R : Type*} [Zero R] [One R] (s k : ℕ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) R) :
    Z3NetHL.graphGen s k Φ = Z3NetU.graphGen s k Φ := rfl

lemma isNet0_iff (s q m : ℕ) (X : (Fin m → ZMod q) → Fin s → ℕ) :
    Z3NetHL.IsNet0 s q m X ↔ Z3NetU.IsNet0 s q m X := Iff.rfl

lemma digPoint_eq {s : ℕ} (q m : ℕ) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) :
    Z3NetHL.digPoint q m C = Z3NetU.digPoint q m C := rfl

/-! ## Readings over a commutative ring -/

section reading

variable {R : Type*} [CommRing R]

lemma split_reading_R {s : ℕ} (m k : ℕ) (u v : Fin s → ℤ) (c : Fin s) (V : Fin m → R) (i : Fin m) :
    ((splitGen m k u v c).map (Int.cast : ℤ → R) *ᵥ V) i =
      if (i : ℕ) < k then (taylor ((v c : ℤ) : R) (Z3NetU.Proofs.pv V)).coeff i
      else (taylor ((u c : ℤ) : R) (Z3NetU.Proofs.pv V)).coeff ((i : ℕ) - k) := by
  simp only [mulVec, dotProduct, map_apply, splitGen]
  rw [Z3NetU.Proofs.pv, map_sum, finset_sum_coeff, map_sum, finset_sum_coeff]
  split_ifs with h
  · refine sum_congr rfl fun l _ => ?_
    rw [taylor_monomial, coeff_C_mul, coeff_X_add_C_pow]
    push_cast; ring
  · refine sum_congr rfl fun l _ => ?_
    rw [taylor_monomial, coeff_C_mul, coeff_X_add_C_pow]
    push_cast; ring

end reading

/-! ## The basis `E_{d,j}` over `ℤ/qℤ` -/

section basis

variable {s q k : ℕ} (u v : Fin s → ℤ)

/-- `E_{d,j}` over `ℤ/qℤ`. -/
def EpolyZ (k : ℕ) (d : Fin s) (j : ℕ) : (ZMod q)[X] :=
  (∏ d' ∈ univ.erase d, (X - C ((v d' : ℤ) : ZMod q)) ^ k) * (X - C ((v d : ℤ) : ZMod q)) ^ j

lemma EpolyZ_map (k : ℕ) (d : Fin s) (j : ℕ) :
    (Epoly k v d j).map (Int.castRingHom (ZMod q)) = EpolyZ (q := q) v k d j := by
  simp [Epoly, EpolyZ, Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_sub]

lemma natDegree_Epoly_le (k : ℕ) (d : Fin s) (j : ℕ) :
    (Epoly k v d j).natDegree ≤ (s - 1) * k + j := by
  have hm : (Epoly k v d j).Monic := by
    unfold Epoly
    exact (monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _).mul ((monic_X_sub_C _).pow _)
  unfold Epoly
  rw [(monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow _).natDegree_mul
    ((monic_X_sub_C _).pow _), natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_sub_C _).pow _)]
  simp only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one, sum_const, card_erase_of_mem
    (mem_univ d), card_univ, Fintype.card_fin, smul_eq_mul]
  exact le_refl _

/-- Coefficient vector of `E_{d,j}` over `ℤ/qℤ`. -/
def EvecZ (k : ℕ) (d : Fin s) (j : ℕ) : Fin (s * k) → ZMod q :=
  fun i => (((Epoly k v d j).coeff i : ℤ) : ZMod q)

lemma pv_EvecZ (hs : 1 ≤ s) (k : ℕ) (d : Fin s) (j : ℕ) (hj : j < k) :
    Z3NetU.Proofs.pv (EvecZ (q := q) v k d j) = EpolyZ (q := q) v k d j := by
  rw [← EpolyZ_map]
  ext i
  rw [Z3NetU.Proofs.coeff_pv, coeff_map]
  split_ifs with h
  · simp [EvecZ]
  · have hdeg := natDegree_Epoly_le v k d j
    have : (s - 1) * k + j < s * k := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; nlinarith
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp

/-- Readings of a coefficient vector over `ℤ/qℤ` (split frame, coordinate `c`). -/
def Frs (k : ℕ) (c : Fin s) (V : Fin (s * k) → ZMod q) : Fin (s * k) → ZMod q :=
  (splitGen (s * k) k u v c).map (Int.cast : ℤ → ZMod q) *ᵥ V

lemma k_le_sk' (k : ℕ) (c : Fin s) : k ≤ s * k := by
  have := c.isLt
  exact Nat.le_mul_of_pos_left k (by omega)

lemma Frs_cell (hs : 1 ≤ s) (k : ℕ) (c d : Fin s) (j : ℕ) (hj : j < k) (i : ℕ) (hi : i < k) :
    Frs (q := q) u v k c (EvecZ v k d j) ⟨i, lt_of_lt_of_le hi (k_le_sk' k c)⟩ =
      (taylor ((v c : ℤ) : ZMod q) (EpolyZ (q := q) v k d j)).coeff i := by
  rw [Frs, split_reading_R, pv_EvecZ v hs k d j hj, if_pos hi]

lemma Frs_offset (hs : 1 ≤ s) (k : ℕ) (c d : Fin s) (j : ℕ) (hj : j < k) (i : Fin (s * k))
    (hi : k ≤ (i : ℕ)) :
    Frs (q := q) u v k c (EvecZ v k d j) i =
      (taylor ((u c : ℤ) : ZMod q) (EpolyZ (q := q) v k d j)).coeff ((i : ℕ) - k) := by
  rw [Frs, split_reading_R, pv_EvecZ v hs k d j hj, if_neg (by omega)]

lemma EpolyZ_fac (k : ℕ) (c d : Fin s) (hcd : c ≠ d) (j : ℕ) :
    EpolyZ (q := q) v k d j = (X - C ((v c : ℤ) : ZMod q)) ^ k *
      ((∏ d' ∈ (univ.erase d).erase c, (X - C ((v d' : ℤ) : ZMod q)) ^ k) *
        (X - C ((v d : ℤ) : ZMod q)) ^ j) := by
  have hmem : c ∈ univ.erase d := mem_erase.mpr ⟨hcd, mem_univ c⟩
  rw [EpolyZ, ← Finset.mul_prod_erase _ _ hmem, mul_assoc]

/-- Cells of `E_{d,j}` vanish at `c ≠ d`. -/
lemma Frs_cell_ne (hs : 1 ≤ s) (k : ℕ) (c d : Fin s) (hcd : c ≠ d) (j : ℕ) (hj : j < k) (i : ℕ)
    (hi : i < k) : Frs (q := q) u v k c (EvecZ v k d j) ⟨i, lt_of_lt_of_le hi (k_le_sk' k c)⟩ = 0 := by
  rw [Frs_cell u v hs k c d j hj i hi, EpolyZ_fac v k c d hcd j,
    Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, if_neg (by omega)]

/-- `U0_c`: the cell of `E_{c,j}` at `c` (column `j`). -/
def U0 (k : ℕ) (c : Fin s) : Matrix (Fin k) (Fin k) (ZMod q) :=
  fun i j => Frs (q := q) u v k c (EvecZ v k c j) ⟨i, lt_of_lt_of_le i.isLt (k_le_sk' k c)⟩

lemma EpolyZ_self (k : ℕ) (c : Fin s) (j : ℕ) :
    EpolyZ (q := q) v k c j = (X - C ((v c : ℤ) : ZMod q)) ^ j *
      ∏ d' ∈ univ.erase c, (X - C ((v d' : ℤ) : ZMod q)) ^ k := by
  rw [EpolyZ, mul_comm]

lemma U0_lower (hs : 1 ≤ s) (k : ℕ) (c : Fin s) (i j : Fin k) (h : i < j) : U0 (q := q) u v k c i j = 0 := by
  have hij : (i : ℕ) < j := h
  unfold U0
  rw [Frs_cell u v hs k c c j j.isLt i i.isLt, EpolyZ_self, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul,
    if_neg (by omega)]

lemma U0_diag (hs : 1 ≤ s) (k : ℕ) (c : Fin s)
    (hv : ∀ d', d' ≠ c → IsUnit (((v c - v d' : ℤ)) : ZMod q)) (i : Fin k) :
    IsUnit (U0 (q := q) u v k c i i) := by
  unfold U0
  rw [Frs_cell u v hs k c c i i.isLt i i.isLt, EpolyZ_self, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul,
    if_pos le_rfl, Nat.sub_self, taylor_coeff_zero]
  simp only [eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  rw [IsUnit.prod_iff]
  intro d' hd'
  have := hv d' (ne_of_mem_erase hd')
  push_cast at this
  exact this.pow _

/-- Offset digits of `E_{d,j}` in reading `c` are `Ψ_cd`. -/
lemma Frs_E_off (k : ℕ) (c d : Fin s) (j : Fin k) (r : Fin (s * k - k)) :
    Frs (q := q) u v k c (EvecZ v k d j) ⟨k + r, Z3NetU.Proofs.sk_sub_add r⟩ =
      ((Psi k u v c d r j : ℤ) : ZMod q) := by
  simp only [Frs, Psi, EvecZ]
  exact (RingHom.map_mulVec (Int.castRingHom (ZMod q)) _ _ _).symm

end basis

/-! ## The gauge -/

section gauge

variable {s q : ℕ} (u v : Fin s → ℤ) (gco : Fin s → ℕ → ℕ → ℚ)

lemma UxZ_upper (d : Fin s) (n' n : ℕ) (hlt : n < n') : UxZ q u v gco d n' n = 0 := by
  unfold UxZ
  split_ifs <;> first | rfl | omega

lemma UkZ_lower (k : ℕ) (d : Fin s) (i j : Fin k) (hij : i < j) : UkZ q u v gco k d i j = 0 := by
  have : (i : ℕ) < j := hij
  unfold UkZ
  exact UxZ_upper u v gco d _ _ (by have := j.isLt; omega)

lemma UkZ_diag (k : ℕ) (d : Fin s) (hlead : ∀ n < s - 1, IsUnit (qr q (gco d n n))) (i : Fin k) :
    IsUnit (UkZ q u v gco k d i i) := by
  unfold UkZ UxZ
  split_ifs with h1 h2
  · exact hlead _ h1
  · omega
  · exact isUnit_one
  · omega

end gauge

/-! ## The kernel argument -/

section kernel

variable {s q : ℕ} (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
  (dg : Fin s → ℕ → ℚ)

open Z3NetU.Proofs (ix ix_surj sk_sub_add graphGen_cell graphGen_off)

/-- The cell `n_c`. -/
def nb (k : ℕ) (n : Fin (s * k) → ZMod q) (c : Fin s) : Fin k → ZMod q := fun l => n (ix k c l)

/-- Coefficients `m_c = U'^(k)_c n_c` in the basis `E_{c,j}`. -/
def mco (k : ℕ) (n : Fin (s * k) → ZMod q) (c : Fin s) : Fin k → ZMod q :=
  UkZ q u v gco k c *ᵥ nb k n c

/-- `V = ∑_{d,j} m_{d,j} E_{d,j}`. -/
def Vvec (k : ℕ) (n : Fin (s * k) → ZMod q) : Fin (s * k) → ZMod q :=
  ∑ d : Fin s, ∑ j : Fin k, mco u v gco k n d j • EvecZ v k d j

/-- Row scaling of the off-diagonal blocks. -/
def sfac (k : ℕ) (c : Fin s) (r : ℕ) : ZMod q :=
  if r = 0 then qr q (lam c) * PinvZ q u v c ^ k else 1

lemma Frs_Vvec (k : ℕ) (n : Fin (s * k) → ZMod q) (c : Fin s) (i : Fin (s * k)) :
    Frs u v k c (Vvec u v gco k n) i =
      ∑ d, ∑ j : Fin k, mco u v gco k n d j * Frs u v k c (EvecZ v k d j) i := by
  simp only [Frs, Vvec, mulVec_sum, mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma Frs_Vvec_cell (hs : 1 ≤ s) (k : ℕ) (n : Fin (s * k) → ZMod q) (c : Fin s) (i : ℕ) (hi : i < k) :
    Frs u v k c (Vvec u v gco k n) ⟨i, lt_of_lt_of_le hi (k_le_sk' k c)⟩ =
      (U0 u v k c *ᵥ mco u v gco k n c) ⟨i, hi⟩ := by
  rw [Frs_Vvec, Finset.sum_eq_single c]
  · simp only [mulVec, dotProduct, U0]; refine sum_congr rfl fun j _ => by ring
  · intro d _ hdc
    apply sum_eq_zero; intro j _
    rw [Frs_cell_ne u v hs k c d (Ne.symm hdc) j j.isLt i hi, mul_zero]
  · simp

lemma Frs_Vvec_off (k : ℕ) (n : Fin (s * k) → ZMod q) (c : Fin s) (r : Fin (s * k - k)) :
    Frs u v k c (Vvec u v gco k n) ⟨k + r, sk_sub_add r⟩ =
      ∑ d, ∑ j : Fin k, mco u v gco k n d j * ((Psi k u v c d r j : ℤ) : ZMod q) := by
  rw [Frs_Vvec]; simp only [Frs_E_off]

lemma digit_off (k : ℕ) (n : Fin (s * k) → ZMod q) (c : Fin s) (r : Fin (s * k - k)) :
    (Z3NetU.graphGen s k (HLPhi s q k u v lam gco dg) c *ᵥ n) ⟨k + r, sk_sub_add r⟩ =
      ∑ l, HLPhi s q k u v lam gco dg c c r l * nb k n c l + sfac u v lam k c r *
        (Frs u v k c (Vvec u v gco k n) ⟨k + r, sk_sub_add r⟩ -
          ∑ j, mco u v gco k n c j * ((Psi k u v c c r j : ℤ) : ZMod q)) := by
  rw [graphGen_off, Frs_Vvec_off]
  rw [← Finset.add_sum_erase _ _ (mem_univ c), ← Finset.add_sum_erase _ _ (mem_univ c)]
  rw [add_sub_cancel_left, Finset.mul_sum]
  simp only [nb]
  congr 1
  refine sum_congr rfl fun d hd => ?_
  have hdc : c ≠ d := Ne.symm (Finset.ne_of_mem_erase hd)
  simp only [HLPhi, if_neg hdc, sfac, mco, mulVec, dotProduct, nb]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun l _ => by ring

/-- **Lemma T′, kernel form**: over `ℤ/qℤ`, if the `2s` points have unit differences, a
polynomial of degree `< m` whose first `min(d_c, k)` Taylor coefficients at `v_c` and first
`d_c - k` Taylor coefficients at `u_c` vanish (`∑ d = m`) is zero. -/
lemma lemmaT' (hq : 2 ≤ q) (k : ℕ)
    (hpts : ∀ c e c' e', (c, e) ≠ (c', e') →
      IsUnit (((splitPt u v c e - splitPt u v c' e' : ℤ)) : ZMod q))
    (m : ℕ) (V : (ZMod q)[X]) (hV : V.degree < m) (d : Fin s → ℕ) (hd : ∑ c, d c = m)
    (hvz : ∀ c : Fin s, ∀ i < min (d c) k, (taylor ((v c : ℤ) : ZMod q) V).coeff i = 0)
    (huz : ∀ c : Fin s, ∀ i < d c - k, (taylor ((u c : ℤ) : ZMod q) V).coeff i = 0) : V = 0 := by
  have : Fact (1 < q) := ⟨by omega⟩
  set S : Finset (Fin s × Fin 2) := univ
  let pt : Fin s × Fin 2 → ZMod q := fun p => ((splitPt u v p.1 p.2 : ℤ) : ZMod q)
  let mu : Fin s × Fin 2 → ℕ := fun p => splitMult k d p.1 p.2
  have hdvd : ∏ p ∈ S, (X - C (pt p)) ^ mu p ∣ V := by
    apply Finset.prod_dvd_of_coprime
    · intro p _ p' _ hne
      apply IsCoprime.pow
      apply isCoprime_X_sub_C_of_isUnit_sub
      have := hpts p.1 p.2 p'.1 p'.2 (by simpa using hne)
      simp only [pt]; push_cast at this ⊢; exact this
    · intro p _
      obtain ⟨c, e⟩ := p
      apply Z3NetU.Proofs.dvd_of_taylor
      intro i hi
      fin_cases e
      · simp only [pt, mu, splitPt, splitMult, Fin.isValue, Fin.val_zero, if_true] at hi ⊢
        exact hvz c i hi
      · simp only [pt, mu, splitPt, splitMult, Fin.isValue, Fin.val_one, one_ne_zero, if_false] at hi ⊢
        exact huz c i hi
  have hmon : (∏ p ∈ S, (X - C (pt p)) ^ mu p).Monic :=
    monic_prod_of_monic _ _ fun p _ => (monic_X_sub_C _).pow _
  have hdeg : (∏ p ∈ S, (X - C (pt p)) ^ mu p).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ (fun p _ => (monic_X_sub_C _).pow _)]
    simp only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [← hd, Fintype.sum_prod_type]
    refine sum_congr rfl fun c _ => ?_
    rw [Fin.sum_univ_two]
    simp only [mu, splitMult, Fin.isValue, Fin.val_zero, if_true, Fin.val_one, one_ne_zero, if_false]
    omega
  by_contra hne
  apply hmon.not_dvd_of_degree_lt hne _ hdvd
  rw [degree_eq_natDegree hmon.ne_zero, hdeg]
  exact hV

lemma isUnit_zinv {a : ZMod q} (ha : IsUnit a) : IsUnit a⁻¹ :=
  isUnit_iff_exists.mpr ⟨a, ZMod.inv_mul_of_unit _ ha, ZMod.mul_inv_of_unit _ ha⟩

lemma nb_eq_zero_imp (k : ℕ) (n : Fin (s * k) → ZMod q) (h0 : ∀ c, nb k n c = 0) : n = 0 := by
  funext j
  obtain ⟨d, l, rfl⟩ := ix_surj k j
  exact congrFun (h0 d) l

/-- **`t = 0` kernel argument.** -/
theorem box_kernel (hs : 1 ≤ s) (hq : 2 ≤ q) (k : ℕ)
    (hpts : ∀ c e c' e', (c, e) ≠ (c', e') →
      IsUnit (((splitPt u v c e - splitPt u v c' e' : ℤ)) : ZMod q))
    (hlam : ∀ c, IsUnit (qr q (lam c))) (hlead : ∀ d, ∀ n < s - 1, IsUnit (qr q (gco d n n)))
    (d : Fin s → ℕ) (hd : ∑ c, d c = s * k) (n : Fin (s * k) → ZMod q)
    (hn : ∀ c (i : Fin (s * k)), (i : ℕ) < d c →
      (Z3NetU.graphGen s k (HLPhi s q k u v lam gco dg) c *ᵥ n) i = 0) :
    n = 0 := by
  have hvv : ∀ c d', d' ≠ c → IsUnit (((v c - v d' : ℤ)) : ZMod q) := by
    intro c d' h
    have := hpts c 0 d' 0 (by intro h'; exact h (by simp at h'; exact h'.symm))
    simpa [splitPt] using this
  have hP : ∀ c, IsUnit (PinvZ q u v c) := by
    intro c
    apply isUnit_zinv
    rw [IsUnit.prod_iff]
    intro d' _
    have := hpts c 1 d' 0 (by simp)
    simpa [splitPt] using this
  have hsf : ∀ c r, IsUnit (sfac (q := q) u v lam k c r) := by
    intro c r
    unfold sfac
    split_ifs
    · exact (hlam c).mul ((hP c).pow _)
    · exact isUnit_one
  have hnb : ∀ c (i : Fin k), (i : ℕ) < d c → nb k n c i = 0 := by
    intro c i hi
    have := hn c ⟨i, lt_of_lt_of_le i.isLt (k_le_sk' k c)⟩ hi
    rwa [graphGen_cell k _ c n i i.isLt] at this
  have hmco : ∀ c (i : Fin k), (i : ℕ) < d c → mco u v gco k n c i = 0 :=
    fun c => Z3NetU.Proofs.lower_mulVec_prefix _ (UkZ_lower u v gco k c) _ _ (hnb c)
  have hF : ∀ c (i : Fin (s * k)), (i : ℕ) < d c → Frs u v k c (Vvec u v gco k n) i = 0 := by
    intro c i hi
    by_cases hik : (i : ℕ) < k
    · have e := Frs_Vvec_cell u v gco hs k n c i hik
      rw [show (⟨(i : ℕ), lt_of_lt_of_le hik (k_le_sk' k c)⟩ : Fin (s * k)) = i from rfl] at e
      rw [e]
      exact Z3NetU.Proofs.lower_mulVec_prefix _ (U0_lower u v hs k c) _ _ (hmco c) ⟨i, hik⟩ hi
    · have hz : nb k n c = 0 := funext fun l => hnb c l (by have := l.isLt; omega)
      have hm : mco u v gco k n c = 0 := by simp [mco, hz]
      have hd' := hn c i hi
      have hi' : i = ⟨k + ((⟨(i : ℕ) - k, by omega⟩ : Fin (s * k - k)) : ℕ),
          sk_sub_add ⟨(i : ℕ) - k, by omega⟩⟩ := by
        ext; simp; omega
      rw [hi', digit_off] at hd'
      simp only [hz, hm, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero,
        zero_add] at hd'
      rw [hi']
      exact (hsf c _).mul_right_eq_zero.mp hd'
  have hV : Z3NetU.Proofs.pv (Vvec u v gco k n) = 0 := by
    refine lemmaT' u v hq k hpts (s * k) _ (Z3NetU.Proofs.degree_pv_lt _) d hd ?_ ?_
    · intro c i hi
      have hik : i < k := lt_of_lt_of_le hi (min_le_right _ _)
      have hid : i < d c := lt_of_lt_of_le hi (min_le_left _ _)
      have := hF c ⟨i, lt_of_lt_of_le hik (k_le_sk' k c)⟩ hid
      rw [Frs, split_reading_R, if_pos hik] at this
      exact this
    · intro c i hi
      have hdc : d c ≤ s * k := by
        rw [← hd]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)
      have := hF c ⟨k + i, by omega⟩ (by simp; omega)
      rw [Frs, split_reading_R, if_neg (by simp)] at this
      simpa using this
  have hV0 := Z3NetU.Proofs.pv_eq_zero hV
  apply nb_eq_zero_imp k n
  intro c
  have hm : mco u v gco k n c = 0 := by
    funext i
    refine Z3Net.Proofs.lowerTri_kill (U0 u v k c) (U0_lower u v hs k c)
      (U0_diag u v hs k c (hvv c)) _ k ?_ i i.isLt
    intro r hr
    rw [← Frs_Vvec_cell u v gco hs k n c r hr, hV0]
    simp [Frs]
  funext i
  refine Z3Net.Proofs.lowerTri_kill (UkZ q u v gco k c) (UkZ_lower u v gco k c)
    (UkZ_diag u v gco k c (hlead c)) _ k ?_ i i.isLt
  intro r _
  exact congrFun hm r

lemma adm_units {s q : ℕ} {u v : Fin s → ℤ} {lam : Fin s → ℚ} {gco : Fin s → ℕ → ℕ → ℚ}
    (hq : HLAdm s q u v lam gco) :
    (∀ c e c' e', (c, e) ≠ (c', e') → IsUnit (((splitPt u v c e - splitPt u v c' e' : ℤ)) : ZMod q)) ∧
    (∀ c, IsUnit (qr q (lam c))) ∧ (∀ d, ∀ n < s - 1, IsUnit (qr q (gco d n n))) := by
  obtain ⟨_, hpts, hlam, hlead⟩ := hq
  refine ⟨fun c e c' e' h => isUnit_int_of_gcd (hpts c e c' e' h), fun c => ?_, fun d n hn => ?_⟩
  · exact isUnit_qr (isUnit_nat_of_coprime (hlam c).2) (isUnit_int_of_gcd (hlam c).1)
  · exact isUnit_qr (isUnit_nat_of_coprime (hlead d n hn).2) (isUnit_int_of_gcd (hlead d n hn).1)

theorem HL_net (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (hs : 2 ≤ s) (hq : HLAdm s q u v lam gco) (hk : 1 ≤ k) :
    Z3NetHL.IsNet0 s q (s * k) (HLpoint s q k u v lam gco dg) := by
  have hq2 : 2 ≤ q := hq.1
  obtain ⟨hpts, hlam, hlead⟩ := adm_units hq
  haveI : NeZero q := ⟨by omega⟩
  rw [isNet0_iff]
  exact Z3NetU.Proofs.isNet0_of_kernel s q (s * k) _
    (fun d hd n hn => box_kernel u v lam gco dg (by omega) hq2 k hpts hlam hlead d hd n hn)

end kernel


end

end Z3NetHL.Proofs

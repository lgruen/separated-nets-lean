module
public import Mathlib
public import Z3Net.SUDefs
public import Z3Net.SUPoly
public import Z3Net.SUGraph
public import Z3Net.NetBasic

@[expose] public section

/-!
# Entry U, part 3: units and `t = 0` (Theorem U(1))

* `IvOK iv n`: `iv i` is an inverse of `i` for `1 ≤ i ≤ n` (`n = s - 2`). Then `ivz`, `Q_c^(-k)`,
  `1/n!`, `L_s` and the row scalings are units.
* The net is the frame read through lower-triangular scrambles: with the coefficients
  `m_d = U'^(k)_d n_d` of the cell vector `n` in the basis `E_{d,j}`, `V = ∑ m_{d,j} E_{d,j}` has
  cells `U0_c m_c` (`U0_c` lower triangular with unit diagonal) and the final offset digit `k + r`
  of coordinate `c` is `(own terms in n_c) + s_{c,r} · (digit k + r of reading c of V)` with a unit
  `s_{c,r}`. Hence vanishing first digits of the net force vanishing first digits of every reading
  of `V`, Lemma T_s gives `V = 0`, and `n = 0` (`box_kernel`).
-/

namespace Z3NetU.Proofs

open Polynomial Finset Matrix Z3NetU

noncomputable section

variable {R : Type*} [CommRing R]

/-! ## Lower-triangular matrices (copied from the 4D entry) -/

lemma lower_mulVec_prefix {a : ℕ} (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i j : Fin a, i < j → M i j = 0) (w : Fin a → R) (e : ℕ)
    (hw : ∀ i : Fin a, (i : ℕ) < e → w i = 0) :
    ∀ i : Fin a, (i : ℕ) < e → (M *ᵥ w) i = 0 := by
  intro i hi
  simp only [mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  rcases lt_or_ge i j with h | h
  · rw [hM i j h, zero_mul]
  · have : (j : ℕ) ≤ i := h
    rw [hw j (by omega), mul_zero]

/-! ## Units -/

/-- `iv i` is an inverse of `i` for `1 ≤ i ≤ n`. -/
def IvOK (iv : ℕ → R) (n : ℕ) : Prop := ∀ i : ℕ, 1 ≤ i → i ≤ n → (i : R) * iv i = 1

variable {iv : ℕ → R} {n : ℕ}

lemma ivz_mul (h : IvOK iv n) (z : ℤ) (hz : z ≠ 0) (hzn : |z| ≤ n) : (z : R) * ivz iv z = 1 := by
  unfold ivz
  split_ifs with h0
  · have e : (z : R) = ((z.toNat : ℕ) : R) := by
      rw [show (z : R) = ((z.toNat : ℤ) : R) by rw [Int.toNat_of_nonneg h0]]; push_cast; rfl
    rw [e]
    exact h _ (by omega) (by rw [abs_of_nonneg h0] at hzn; omega)
  · have e : (z : R) = -(((-z).toNat : ℕ) : R) := by
      rw [show (z : R) = -(((-z).toNat : ℤ) : R) by rw [Int.toNat_of_nonneg (by omega)]; simp]; push_cast; rfl
    rw [e, neg_mul_neg]
    exact h _ (by omega) (by rw [abs_of_neg (by omega)] at hzn; omega)

lemma ivz_unit (h : IvOK iv n) (z : ℤ) (hz : z ≠ 0) (hzn : |z| ≤ n) : IsUnit (ivz iv z) :=
  IsUnit.of_mul_eq_one_right _ (ivz_mul h z hz hzn)

lemma intCast_unit (h : IvOK iv n) (z : ℤ) (hz : z ≠ 0) (hzn : |z| ≤ n) : IsUnit (z : R) :=
  IsUnit.of_mul_eq_one _ (ivz_mul h z hz hzn)

lemma natCast_unit (h : IvOK iv n) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ n) : IsUnit (i : R) :=
  IsUnit.of_mul_eq_one _ (h i h1 h2)

lemma iv_unit (h : IvOK iv n) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ n) : IsUnit (iv i) :=
  IsUnit.of_mul_eq_one_right _ (h i h1 h2)

/-- Differences of finite places are small nonzero integers. -/
lemma diff_small {s : ℕ} (c b : Fin s) (hc : (c : ℕ) ≠ 0) (hb : (b : ℕ) ≠ 0) (hcb : c ≠ b) :
    ((c : ℤ) - b) ≠ 0 ∧ |(c : ℤ) - b| ≤ (s - 2 : ℕ) := by
  have h1 := c.isLt; have h2 := b.isLt
  have hne : (c : ℕ) ≠ b := fun h => hcb (Fin.ext h)
  constructor
  · omega
  · rw [abs_le]; constructor <;> push_cast [show 2 ≤ s by omega] <;> omega

lemma invFact_unit (h : IvOK iv n) (j : ℕ) (hj : j ≤ n) : IsUnit (invFact iv j) := by
  unfold invFact
  rw [IsUnit.prod_iff]
  intro i hi
  rw [mem_range] at hi
  exact iv_unit h _ (by omega) (by omega)

lemma Lcst_unit {s : ℕ} (h : IvOK iv (s - 2)) : IsUnit ((Lcst s : ℤ) : R) := by
  unfold Lcst
  push_cast
  apply IsUnit.pow
  have hd : (Finset.Icc 1 (s - 2)).lcm id ∣ ∏ i ∈ Finset.Icc 1 (s - 2), id i :=
    Finset.lcm_dvd_prod _ _
  have hd' : (((Finset.Icc 1 (s - 2)).lcm id : ℕ) : R) ∣ ((∏ i ∈ Finset.Icc 1 (s - 2), id i : ℕ) : R) :=
    Nat.cast_dvd_cast hd
  refine isUnit_of_dvd_unit hd' ?_
  push_cast
  rw [IsUnit.prod_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact natCast_unit h i hi.1 hi.2

lemma lamRes_unit {s : ℕ} (h : IvOK iv (s - 2)) (c : Fin s) : IsUnit ((lamRes c : ℤ) : R) := by
  unfold lamRes
  split_ifs
  · simp
  · exact Lcst_unit h

lemma Qinv_unit {s : ℕ} (h : IvOK iv (s - 2)) (k : ℕ) (c : Fin s) : IsUnit (Qinv iv k c) := by
  unfold Qinv
  split_ifs with hc
  · exact isUnit_one
  · apply IsUnit.pow
    rw [IsUnit.prod_iff]
    intro b hb
    rw [mem_filter] at hb
    obtain ⟨h1, h2⟩ := diff_small c b hc hb.2.1 (Ne.symm hb.2.2)
    exact ivz_unit h _ h1 h2

/-! ## The cell matrix `U0` -/

lemma k_le_sk {s : ℕ} (k : ℕ) (c : Fin s) : k ≤ s * k := by
  have := c.isLt
  exact Nat.le_mul_of_pos_left k (by omega)

/-- Readings of a coefficient vector over `R`. -/
def Fr {s : ℕ} (k : ℕ) (c : Fin s) (V : Fin (s * k) → R) : Fin (s * k) → R :=
  (frameGen (s * k) c).map (Int.cast : ℤ → R) *ᵥ V

/-- `U0_c`: the cell of `E_{c,j}` at `c` (column `j`), i.e. `Q_c^k Toep(g_c)`. -/
def U0 (R : Type*) [CommRing R] {s : ℕ} (k : ℕ) (c : Fin s) : Matrix (Fin k) (Fin k) R :=
  fun i j => Fr k c (EvecR k c j) ⟨i, lt_of_lt_of_le i.isLt (k_le_sk k c)⟩

lemma Fr_E_fin {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (c d : Fin s) (j : ℕ) (hj : j < k) (hc : (c : ℕ) ≠ 0)
    (i : Fin (s * k)) :
    Fr k c (EvecR (R := R) k d j) i = (taylor ((place c : ℤ) : R) (EPoly R k d j)).coeff i := by
  rw [Fr, frame_fin _ c hc, pv_EvecR hs k d j hj]

lemma Fr_E_inf {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (c d : Fin s) (j : ℕ) (hj : j < k) (hc : (c : ℕ) = 0)
    (i : Fin (s * k)) :
    Fr k c (EvecR (R := R) k d j) i = (EPoly R k d j).coeff (s * k - 1 - i) := by
  rw [Fr, frame_inf _ c hc, pv_EvecR hs k d j hj]

lemma Eexp_self {s : ℕ} (k : ℕ) (c : Fin s) (j : ℕ) (hc : (c : ℕ) ≠ 0) : Eexp k c c j = j := by
  simp [Eexp, hc]

lemma Eexp_ne {s : ℕ} (k : ℕ) (c d : Fin s) (j : ℕ) (hc : (c : ℕ) ≠ 0) (hcd : c ≠ d) :
    Eexp k d c j = k := by
  simp [Eexp, hc, hcd]

lemma sk_eq {s : ℕ} (hs : 2 ≤ s) (k : ℕ) : (s - 1) * k + k = s * k := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

lemma U0_lower {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (c : Fin s) (i j : Fin k) (h : i < j) :
    U0 R k c i j = 0 := by
  have hij : (i : ℕ) < j := h
  unfold U0
  by_cases hc : (c : ℕ) = 0
  · rw [Fr_E_inf hs k c c j j.isLt hc]
    apply coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt (natDegree_EPoly_le k c j) ?_
    rw [Esum_inf hs k c hc j]
    have := sk_eq hs k; have := j.isLt
    simp only; omega
  · rw [Fr_E_fin hs k c c j j.isLt hc, taylor_EPoly_fin k c c j hc, Eexp_self k c j hc,
      if_neg (by simp; omega)]

lemma U0_diag {s : ℕ} (hs : 3 ≤ s) (h : IvOK iv (s - 2)) (k : ℕ) (c : Fin s) (i : Fin k) :
    IsUnit (U0 R k c i i) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact isUnit_of_subsingleton _
  unfold U0
  by_cases hc : (c : ℕ) = 0
  · rw [Fr_E_inf (by omega) k c c i i.isLt hc]
    have e : s * k - 1 - (i : ℕ) = (EPoly R k c i).natDegree := by
      rw [natDegree_EPoly, Esum_inf (by omega) k c hc i]
      have := sk_eq (show 2 ≤ s by omega) k; have := i.isLt
      omega
    simp only
    rw [e, (EPoly_monic k c i).coeff_natDegree]
    exact isUnit_one
  · rw [Fr_E_fin (by omega) k c c i i.isLt hc, taylor_EPoly_fin k c c i hc, Eexp_self k c i hc,
      if_pos le_rfl, Nat.sub_self, taylor_coeff_zero, Rest_eval]
    rw [IsUnit.prod_iff]
    intro b hb
    rw [mem_erase] at hb
    by_cases hb0 : (b : ℕ) = 0
    · have : Eexp k c b i = 0 := by simp [Eexp, hb0, hc]
      rw [this, pow_zero]; exact isUnit_one
    · rw [Eexp_fin k c b i hb0, if_neg hb.1, Eroot_fin b hb0]
      apply IsUnit.pow
      obtain ⟨h1, h2⟩ := diff_small c b hc hb0 (Ne.symm hb.1)
      have := intCast_unit h _ h1 h2
      simpa [place] using this

/-- Cells of `E_{d,j}` vanish at `c ≠ d`. -/
lemma Fr_E_cell_ne {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (c d : Fin s) (hcd : c ≠ d) (j : ℕ) (hj : j < k)
    (i : ℕ) (hi : i < k) :
    Fr k c (EvecR (R := R) k d j) ⟨i, lt_of_lt_of_le hi (k_le_sk k c)⟩ = 0 := by
  by_cases hc : (c : ℕ) = 0
  · rw [Fr_E_inf hs k c d j hj hc]
    apply coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt (natDegree_EPoly_le k d j) ?_
    have hd : (d : ℕ) ≠ 0 := fun h => hcd (Fin.ext (by rw [hc, h]))
    rw [Esum_fin hs k d hd j]
    have := sk_eq hs k
    have e2 : (s - 2) * k + k = (s - 1) * k := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
      simp only [Nat.add_sub_cancel, show t + 2 - 1 = t + 1 by omega]; ring
    simp only; omega
  · rw [Fr_E_fin hs k c d j hj hc, taylor_EPoly_fin k c d j hc, Eexp_ne k c d j hc hcd,
      if_neg (by simp; omega)]

/-- Offset digits of `E_{d,j}` in reading `c` are `Ψ_cd`. -/
lemma Fr_E_off {s : ℕ} (k : ℕ) (c d : Fin s) (j : Fin k) (r : Fin (s * k - k)) :
    Fr k c (EvecR (R := R) k d j) ⟨k + r, sk_sub_add r⟩ = (Psi k c d r j : R) := by
  simp only [Fr, Psi]
  exact (RingHom.map_mulVec (Int.castRingHom R) _ _ _).symm

/-! ## The gauge `U'^(k)` -/

lemma stir_eq_zero : ∀ (n i : ℕ), n < i → stir n i = 0
  | 0, i, h => by simp [stir]; omega
  | n + 1, i, h => by
    simp only [stir]
    rw [if_neg (by omega), stir_eq_zero n (i - 1) (by omega), stir_eq_zero n i (by omega)]
    simp

lemma stir_self : ∀ n : ℕ, stir n n = 1
  | 0 => by simp [stir]
  | n + 1 => by
    simp only [stir]
    rw [if_neg (by omega), Nat.add_sub_cancel, stir_self n, stir_eq_zero n (n + 1) (by omega)]
    simp

lemma Ures_upper {s : ℕ} (d : Fin s) (n' n : ℕ) (hlt : n < n') : Ures iv d n' n = 0 := by
  unfold Ures
  split_ifs with h1 h2
  · rw [stir_eq_zero n n' hlt]; simp
  · omega
  · rfl

lemma Ux_upper {s : ℕ} (d : Fin s) (n' n : ℕ) (hlt : n < n') : Ux iv d n' n = 0 := by
  unfold Ux
  split_ifs with h1 h2 h3 h4
  · exact Ures_upper d n' n hlt
  · rfl
  · omega
  · omega
  · rfl

lemma Ux_diag {s : ℕ} (h : IvOK iv (s - 2)) (d : Fin s) (n : ℕ) : IsUnit (Ux iv d n n) := by
  unfold Ux
  by_cases h1 : n < s - 1
  · rw [if_pos h1, if_pos h1]; unfold Ures
    by_cases hd : (d : ℕ) = 0
    · rw [if_pos hd, stir_self]; simpa using invFact_unit h n (by omega)
    · rw [if_neg hd, if_pos rfl]; exact isUnit_one
  · rw [if_neg h1, if_pos rfl]; exact isUnit_one

lemma Uk_lower {s : ℕ} (k : ℕ) (d : Fin s) (i j : Fin k) (hij : i < j) : Uk iv k d i j = 0 := by
  have : (i : ℕ) < j := hij
  unfold Uk
  exact Ux_upper d _ _ (by have := j.isLt; omega)

lemma Uk_diag {s : ℕ} (h : IvOK iv (s - 2)) (k : ℕ) (d : Fin s) (i : Fin k) :
    IsUnit (Uk iv k d i i) :=
  Ux_diag h d _

/-! ## The kernel argument -/

section kernel

variable (iv)

/-- The cell `n_c` (levels `0..k-1`). -/
def nb {s : ℕ} (k : ℕ) (n : Fin (s * k) → R) (c : Fin s) : Fin k → R := fun l => n (ix k c l)

/-- Coefficients `m_c = U'^(k)_c n_c` of the index in the basis `E_{c,j}`. -/
def mco {s : ℕ} (k : ℕ) (n : Fin (s * k) → R) (c : Fin s) : Fin k → R := Uk iv k c *ᵥ nb k n c

/-- `V = ∑_{d,j} m_{d,j} E_{d,j}` (coefficient vector). -/
def Vvec {s : ℕ} (k : ℕ) (n : Fin (s * k) → R) : Fin (s * k) → R :=
  ∑ d : Fin s, ∑ j : Fin k, mco iv k n d j • EvecR k d j

/-- Row scaling of the off-diagonal blocks: `λ'_c Q_c^(-k)` on row `0`, `1` below. -/
def sfac {s : ℕ} (k : ℕ) (c : Fin s) (r : ℕ) : R := if r = 0 then (lamRes c : R) * Qinv iv k c else 1

lemma Fr_Vvec {s : ℕ} (k : ℕ) (n : Fin (s * k) → R) (c : Fin s) (i : Fin (s * k)) :
    Fr k c (Vvec iv k n) i = ∑ d, ∑ j : Fin k, mco iv k n d j * Fr k c (EvecR k d j) i := by
  simp only [Fr, Vvec, mulVec_sum, mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma Fr_Vvec_cell {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (n : Fin (s * k) → R) (c : Fin s) (i : ℕ) (hi : i < k) :
    Fr k c (Vvec iv k n) ⟨i, lt_of_lt_of_le hi (k_le_sk k c)⟩ = (U0 R k c *ᵥ mco iv k n c) ⟨i, hi⟩ := by
  rw [Fr_Vvec, Finset.sum_eq_single c]
  · simp only [mulVec, dotProduct, U0]; refine sum_congr rfl fun j _ => by ring
  · intro d _ hdc
    apply sum_eq_zero; intro j _
    rw [Fr_E_cell_ne hs k c d (Ne.symm hdc) j j.isLt i hi, mul_zero]
  · simp

lemma Fr_Vvec_off {s : ℕ} (k : ℕ) (n : Fin (s * k) → R) (c : Fin s) (r : Fin (s * k - k)) :
    Fr k c (Vvec iv k n) ⟨k + r, sk_sub_add r⟩ =
      ∑ d, ∑ j : Fin k, mco iv k n d j * (Psi k c d r j : R) := by
  rw [Fr_Vvec]; simp only [Fr_E_off]

lemma digit_off {s : ℕ} (k : ℕ) (n : Fin (s * k) → R) (c : Fin s) (r : Fin (s * k - k)) :
    (graphGen s k (UPhi R iv k) c *ᵥ n) ⟨k + r, sk_sub_add r⟩ =
      ∑ l, UPhi R iv k c c r l * nb k n c l + sfac iv k c r *
        (Fr k c (Vvec iv k n) ⟨k + r, sk_sub_add r⟩ - ∑ j, mco iv k n c j * (Psi k c c r j : R)) := by
  rw [graphGen_off, Fr_Vvec_off]
  rw [← Finset.add_sum_erase _ _ (mem_univ c), ← Finset.add_sum_erase _ _ (mem_univ c)]
  rw [add_sub_cancel_left, Finset.mul_sum]
  simp only [nb]
  congr 1
  refine sum_congr rfl fun d hd => ?_
  have hdc : c ≠ d := Ne.symm (Finset.ne_of_mem_erase hd)
  simp only [UPhi, if_neg hdc, sfac, mco, mulVec, dotProduct, nb]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun l _ => by ring

lemma sfac_unit {s : ℕ} (h : IvOK iv (s - 2)) (k : ℕ) (c : Fin s) (r : ℕ) :
    IsUnit (sfac iv k c r) := by
  unfold sfac
  split_ifs
  · exact (lamRes_unit h c).mul (Qinv_unit h k c)
  · exact isUnit_one

lemma nb_eq_zero_imp {s : ℕ} (k : ℕ) (n : Fin (s * k) → R) (h0 : ∀ c, nb k n c = 0) : n = 0 := by
  funext j
  obtain ⟨d, l, rfl⟩ := ix_surj k j
  exact congrFun (h0 d) l

/-- **`t = 0` kernel argument.** If the first `d c` digits of every coordinate of the index `n`
vanish (`∑ d = s k`), then `n = 0`. -/
theorem box_kernel {s : ℕ} (hs : 3 ≤ s) (h : IvOK iv (s - 2)) (k : ℕ) (d : Fin s → ℕ)
    (hd : ∑ c, d c = s * k) (n : Fin (s * k) → R)
    (hn : ∀ c (i : Fin (s * k)), (i : ℕ) < d c → (graphGen s k (UPhi R iv k) c *ᵥ n) i = 0) :
    n = 0 := by
  have hs2 : 2 ≤ s := by omega
  have hs0 : 0 < s := by omega
  have hnb : ∀ c (i : Fin k), (i : ℕ) < d c → nb k n c i = 0 := by
    intro c i hi
    have := hn c ⟨i, lt_of_lt_of_le i.isLt (k_le_sk k c)⟩ hi
    rwa [graphGen_cell k _ c n i i.isLt] at this
  have hmco : ∀ c (i : Fin k), (i : ℕ) < d c → mco iv k n c i = 0 :=
    fun c => lower_mulVec_prefix _ (Uk_lower k c) _ _ (hnb c)
  have hF : ∀ c (i : Fin (s * k)), (i : ℕ) < d c → Fr k c (Vvec iv k n) i = 0 := by
    intro c i hi
    by_cases hik : (i : ℕ) < k
    · have e := Fr_Vvec_cell iv hs2 k n c i hik
      rw [show (⟨(i : ℕ), lt_of_lt_of_le hik (k_le_sk k c)⟩ : Fin (s * k)) = i from rfl] at e
      rw [e]
      exact lower_mulVec_prefix _ (U0_lower hs2 k c) _ _ (hmco c) ⟨i, hik⟩ hi
    · have hz : nb k n c = 0 := funext fun l => hnb c l (by have := l.isLt; omega)
      have hm : mco iv k n c = 0 := by simp [mco, hz]
      have hd' := hn c i hi
      have hi' : i = ⟨k + ((⟨(i : ℕ) - k, by omega⟩ : Fin (s * k - k)) : ℕ),
          sk_sub_add ⟨(i : ℕ) - k, by omega⟩⟩ := by
        ext; simp; omega
      rw [hi', digit_off] at hd'
      simp only [hz, hm, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero,
        zero_add] at hd'
      rw [hi']
      exact (sfac_unit iv h k c _).mul_right_eq_zero.mp hd'
  have hV : pv (Vvec iv k n) = 0 := by
    refine lemmaT hs0 (fun c => ((place c : ℤ) : R)) ?_ (s * k) _ (degree_pv_lt _) d hd ?_ ?_
    · intro c c' hc hc' hne
      obtain ⟨h1, h2⟩ := diff_small c c' hc hc' hne
      have := intCast_unit h _ h1 h2
      simpa [place] using this
    · intro c hc i hi
      have hi4 : i < s * k := by
        have : d c ≤ s * k := by
          rw [← hd]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)
        omega
      have := frame_fin (s * k) c hc (Vvec iv k n) ⟨i, hi4⟩
      rw [← this]
      exact hF c ⟨i, hi4⟩ hi
    · intro i hi
      have hi4 : i < s * k := by
        have : d (c0 hs0) ≤ s * k := by
          rw [← hd]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
        omega
      have := frame_inf (s * k) (c0 hs0) rfl (Vvec iv k n) ⟨i, hi4⟩
      rw [← this]
      exact hF (c0 hs0) ⟨i, hi4⟩ hi
  have hV0 := pv_eq_zero hV
  apply nb_eq_zero_imp k n
  intro c
  have hm : mco iv k n c = 0 := by
    funext i
    refine Z3Net.Proofs.lowerTri_kill (U0 R k c) (U0_lower hs2 k c) (U0_diag hs h k c) _ k ?_ i i.isLt
    intro r hr
    rw [← Fr_Vvec_cell iv hs2 k n c r hr, hV0]
    simp [Fr]
  funext i
  refine Z3Net.Proofs.lowerTri_kill (Uk iv k c) (Uk_lower k c) (Uk_diag h k c) _ k ?_ i i.isLt
  intro r _
  exact congrFun hm r

end kernel

end

end Z3NetU.Proofs

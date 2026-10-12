module
public import Mathlib
public import Z3Net.D4Defs
public import Z3Net.D4Poly
public import Z3Net.D4Graph
public import Z3Net.NetBasic

@[expose] public section

/-!
# 4D entry, part 3: `t = 0` (Theorem 4D(1))

The net is the frame read through lower-triangular scrambles: with the coefficients
`m_d = U'^(k)_d n_d` of the cell vector `n` in the basis `E_{d,j}`, `V = ∑ m_{d,j} E_{d,j}` has
cells `U0_c m_c` (`U0_c` lower triangular with diagonal `Q_c^k`) and the final offset digit `k + r`
of coordinate `c` is `(own terms in n_c) + s_{c,r} · (digit k + r of reading c of V)` with a unit
`s_{c,r}`. Hence vanishing first digits of the net force vanishing first digits of every reading
of `V`, Lemma T gives `V = 0`, and `n = 0` (`box_kernel`).
-/

namespace Z3NetD4.Proofs

open Polynomial Finset Matrix Z3NetD4

noncomputable section

variable {R : Type*} [CommRing R]

/-! ## Lower-triangular matrices -/

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

/-! ## The cell matrix `U0` -/

/-- Readings of a coefficient vector over `R`. -/
def Fr (k : ℕ) (c : Fin 4) (V : Fin (4 * k) → R) : Fin (4 * k) → R :=
  (frameGen (4 * k) c).map (Int.cast : ℤ → R) *ᵥ V

/-- `U0_c`: the cell of `E_{c,j}` at `c` (column `j`), i.e. `Q_c^k Toep(g_c)`. -/
def U0 (R : Type*) [CommRing R] (k : ℕ) (c : Fin 4) : Matrix (Fin k) (Fin k) R :=
  fun i j => Fr k c (EvecR k c j) ⟨i, by omega⟩

lemma exSum_two (k j : ℕ) (hj : j < k) : exT k 2 j + exP k 2 j + exM k 2 j = 4 * k - 1 - j := by
  simp [exT, exP, exM]; omega

lemma exSum_ne_two (k : ℕ) (d : Fin 4) (j : ℕ) (hd : d ≠ 2) :
    exT k d j + exP k d j + exM k d j = 2 * k + j := by
  fin_cases d <;> simp_all [exT, exP, exM] <;> omega

lemma Fr_E_fin (k : ℕ) (c d : Fin 4) (j : ℕ) (hj : j < k) (hc : c ≠ 2) (i : Fin (4 * k)) :
    Fr k c (EvecR (R := R) k d j) i = (taylor ((place c : ℤ) : R) (EPoly R k d j)).coeff i := by
  rw [Fr, frame_fin _ c hc, pv_EvecR k d j hj]

lemma Fr_E_inf (k : ℕ) (d : Fin 4) (j : ℕ) (hj : j < k) (i : Fin (4 * k)) :
    Fr k 2 (EvecR (R := R) k d j) i = (EPoly R k d j).coeff (4 * k - 1 - i) := by
  rw [Fr, frame_inf, pv_EvecR k d j hj]

lemma U0_lower (k : ℕ) (c : Fin 4) (i j : Fin k) (h : i < j) : U0 R k c i j = 0 := by
  have hij : (i : ℕ) < j := h
  unfold U0
  by_cases hc : c = 2
  · subst hc
    rw [Fr_E_inf k 2 j j.isLt]
    apply coeff_EPoly_gt
    rw [exSum_two k j j.isLt]; simp; omega
  · rw [Fr_E_fin k c c j j.isLt hc, taylor_E_self k c j hc, if_neg (by simp; omega)]

lemma U0_diag (h2 : IsUnit (2 : R)) (k : ℕ) (c : Fin 4) (i : Fin k) : IsUnit (U0 R k c i i) := by
  unfold U0
  by_cases hc : c = 2
  · subst hc
    rw [Fr_E_inf k 2 i i.isLt]
    simp only
    rw [← exSum_two k i i.isLt, coeff_EPoly_top]
    exact isUnit_one
  · rw [Fr_E_fin k c c i i.isLt hc, taylor_E_self k c i hc, if_pos le_rfl, Nat.sub_self,
      taylor_coeff_zero, Hself_eval k c hc]
    unfold Qpow
    split_ifs
    · exact ((isUnit_one (M := R)).neg).pow k
    · exact h2.pow k

/-- Cells of `E_{d,j}` vanish at `c ≠ d`. -/
lemma Fr_E_cell_ne (k : ℕ) (c d : Fin 4) (hcd : c ≠ d) (j : ℕ) (hj : j < k) (i : ℕ) (hi : i < k) :
    Fr k c (EvecR (R := R) k d j) ⟨i, by omega⟩ = 0 := by
  by_cases hc : c = 2
  · subst hc
    rw [Fr_E_inf k d j hj]
    apply coeff_EPoly_gt
    rw [exSum_ne_two k d j (Ne.symm hcd)]; simp; omega
  · rw [Fr_E_fin k c d j hj hc, taylor_E_ne k c d j hc hcd hj, if_neg (by simp; omega)]

/-- Offset digits of `E_{d,j}` in reading `c` are `Ψ_cd`. -/
lemma Fr_E_off (k : ℕ) (c d : Fin 4) (j : Fin k) (r : Fin (3 * k)) :
    Fr k c (EvecR (R := R) k d j) ⟨k + r, by omega⟩ = (Psi k c d r j : R) := by
  simp only [Fr, Psi]
  exact (RingHom.map_mulVec (Int.castRingHom R) _ _ _).symm

/-! ## The gauge `U'^(k)` -/

lemma Ures_upper (h : R) (d : Fin 4) (a b : Fin 3) (hab : b < a) : Ures h d a b = 0 := by
  fin_cases d <;> fin_cases a <;> fin_cases b <;> simp_all [Ures] <;> contradiction

lemma Ux_upper (h : R) (d : Fin 4) (n' n : ℕ) (hlt : n < n') : Ux h d n' n = 0 := by
  unfold Ux
  split_ifs with h1 h2 h3 h4 h5
  · exact Ures_upper h d _ _ (by simp [Fin.lt_def]; omega)
  · omega
  · omega
  · omega
  · rfl
  · rfl

lemma Ux_diag (h : R) (hh : 2 * h = 1) (d : Fin 4) (n : ℕ) : IsUnit (Ux h d n n) := by
  have h2 : IsUnit (2 : R) := IsUnit.of_mul_eq_one _ hh
  have hu : IsUnit h := IsUnit.of_mul_eq_one_right _ hh
  unfold Ux
  by_cases h1 : n < 3 ∧ n < 3
  · rw [dif_pos h1]
    obtain ⟨hn, -⟩ := h1
    have h4 : IsUnit (4 : R) := by rw [show (4 : R) = 2 ^ 2 by norm_num]; exact h2.pow 2
    fin_cases d <;> interval_cases n <;> simp [Ures] <;> first | exact isUnit_one | exact isUnit_one.neg | exact h2 | exact h2.neg | exact hu.neg | exact (hu.pow 2).neg | exact h4 | exact hu | exact hu.pow 2
  · rw [dif_neg h1, if_pos (by omega), if_pos rfl]
    exact isUnit_one

lemma Uk_lower (h : R) (k : ℕ) (d : Fin 4) (i j : Fin k) (hij : i < j) : Uk h k d i j = 0 := by
  have : (i : ℕ) < j := hij
  unfold Uk
  exact Ux_upper h d _ _ (by have := j.isLt; omega)

lemma Uk_diag (h : R) (hh : 2 * h = 1) (k : ℕ) (d : Fin 4) (i : Fin k) : IsUnit (Uk h k d i i) :=
  Ux_diag h hh d _

/-! ## The kernel argument -/

section kernel

variable (h : R)

/-- The cell `n_c` (levels `0..k-1`). -/
def nb (k : ℕ) (n : Fin (4 * k) → R) (c : Fin 4) : Fin k → R := fun l => n (ix k c l)

/-- Coefficients `m_c = U'^(k)_c n_c` of the index in the basis `E_{c,j}`. -/
def mco (k : ℕ) (n : Fin (4 * k) → R) (c : Fin 4) : Fin k → R := Uk h k c *ᵥ nb k n c

/-- `V = ∑_{d,j} m_{d,j} E_{d,j}` (coefficient vector). -/
def Vvec (k : ℕ) (n : Fin (4 * k) → R) : Fin (4 * k) → R :=
  ∑ d : Fin 4, ∑ j : Fin k, mco h k n d j • EvecR k d j

/-- Row scaling of the off-diagonal blocks: `λ'_c Q_c^(-k)` on row `0`, `1` below. -/
def sfac (k : ℕ) (c : Fin 4) (r : ℕ) : R := if r = 0 then (lamRes c : R) * Qinv h k c else 1

lemma Fr_Vvec (k : ℕ) (n : Fin (4 * k) → R) (c : Fin 4) (i : Fin (4 * k)) :
    Fr k c (Vvec h k n) i = ∑ d, ∑ j : Fin k, mco h k n d j * Fr k c (EvecR k d j) i := by
  simp only [Fr, Vvec, mulVec_sum, mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma Fr_Vvec_cell (k : ℕ) (n : Fin (4 * k) → R) (c : Fin 4) (i : ℕ) (hi : i < k) :
    Fr k c (Vvec h k n) ⟨i, by omega⟩ = (U0 R k c *ᵥ mco h k n c) ⟨i, hi⟩ := by
  rw [Fr_Vvec, Finset.sum_eq_single c]
  · simp only [mulVec, dotProduct, U0]; refine sum_congr rfl fun j _ => by ring
  · intro d _ hdc
    apply sum_eq_zero; intro j _
    rw [Fr_E_cell_ne k c d (Ne.symm hdc) j j.isLt i hi, mul_zero]
  · simp

lemma Fr_Vvec_off (k : ℕ) (n : Fin (4 * k) → R) (c : Fin 4) (r : Fin (3 * k)) :
    Fr k c (Vvec h k n) ⟨k + r, by omega⟩ = ∑ d, ∑ j : Fin k, mco h k n d j * (Psi k c d r j : R) := by
  rw [Fr_Vvec]; simp only [Fr_E_off]

lemma digit_off (k : ℕ) (n : Fin (4 * k) → R) (c : Fin 4) (r : Fin (3 * k)) :
    (graphGen k (D4Phi R h k) c *ᵥ n) ⟨k + r, by omega⟩ =
      ∑ l, D4Phi R h k c c r l * nb k n c l + sfac h k c r *
        (Fr k c (Vvec h k n) ⟨k + r, by omega⟩ - ∑ j, mco h k n c j * (Psi k c c r j : R)) := by
  rw [graphGen_off, Fr_Vvec_off]
  rw [← Finset.add_sum_erase _ _ (mem_univ c), ← Finset.add_sum_erase _ _ (mem_univ c)]
  rw [add_sub_cancel_left, Finset.mul_sum]
  simp only [nb]
  congr 1
  refine sum_congr rfl fun d hd => ?_
  have hdc : c ≠ d := Ne.symm (Finset.ne_of_mem_erase hd)
  simp only [D4Phi, if_neg hdc, sfac, mco, mulVec, dotProduct, nb]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun l _ => by ring

lemma sfac_unit (hh : 2 * h = 1) (k : ℕ) (c : Fin 4) (r : ℕ) : IsUnit (sfac h k c r) := by
  have h2 : IsUnit (2 : R) := IsUnit.of_mul_eq_one _ hh
  have hu : IsUnit h := IsUnit.of_mul_eq_one_right _ hh
  unfold sfac
  split_ifs
  · refine IsUnit.mul ?_ ?_
    · fin_cases c <;> simp [lamRes] <;> first | exact isUnit_one | exact h2
    · fin_cases c <;> simp [Qinv] <;> first | exact isUnit_one | exact hu.pow k | exact h2.pow k | exact ((isUnit_one (M := R)).neg).pow k
  · exact isUnit_one

lemma nb_eq_zero_imp (k : ℕ) (hk : 1 ≤ k) (n : Fin (4 * k) → R) (h0 : ∀ c, nb k n c = 0) : n = 0 := by
  funext j
  have hj := j.isLt
  have hc : (j : ℕ) / k < 4 := Nat.div_lt_of_lt_mul (by omega)
  have := congrFun (h0 ⟨(j : ℕ) / k, hc⟩) ⟨(j : ℕ) % k, Nat.mod_lt _ (by omega)⟩
  simp only [nb, Pi.zero_apply] at this
  rw [show j = ix k ⟨(j : ℕ) / k, hc⟩ ⟨(j : ℕ) % k, Nat.mod_lt _ (by omega)⟩ by
    ext; simp [ix]; exact (Nat.div_add_mod' (j : ℕ) k).symm]
  exact this

/-- **`t = 0` kernel argument.** If the first `d c` digits of every coordinate of the index `n`
vanish (`∑ d = 4k`), then `n = 0`. -/
theorem box_kernel (hh : 2 * h = 1) (k : ℕ) (hk : 1 ≤ k) (d : Fin 4 → ℕ)
    (hd : d 0 + d 1 + d 2 + d 3 = 4 * k) (n : Fin (4 * k) → R)
    (hn : ∀ c (i : Fin (4 * k)), (i : ℕ) < d c → (graphGen k (D4Phi R h k) c *ᵥ n) i = 0) :
    n = 0 := by
  have h2 : IsUnit (2 : R) := IsUnit.of_mul_eq_one _ hh
  have hnb : ∀ c (i : Fin k), (i : ℕ) < d c → nb k n c i = 0 := by
    intro c i hi
    have := hn c ⟨i, by omega⟩ hi
    rwa [graphGen_cell k _ c n i i.isLt] at this
  have hmco : ∀ c (i : Fin k), (i : ℕ) < d c → mco h k n c i = 0 :=
    fun c => lower_mulVec_prefix _ (Uk_lower h k c) _ _ (hnb c)
  have hF : ∀ c (i : Fin (4 * k)), (i : ℕ) < d c → Fr k c (Vvec h k n) i = 0 := by
    intro c i hi
    by_cases hik : (i : ℕ) < k
    · have e := Fr_Vvec_cell h k n c i hik
      rw [show (⟨(i : ℕ), by omega⟩ : Fin (4 * k)) = i from rfl] at e
      rw [e]
      exact lower_mulVec_prefix _ (U0_lower k c) _ _ (hmco c) ⟨i, hik⟩ hi
    · have hz : nb k n c = 0 := funext fun l => hnb c l (by have := l.isLt; omega)
      have hm : mco h k n c = 0 := by simp [mco, hz]
      have hd' := hn c i hi
      have hi' : i = ⟨k + ((⟨(i : ℕ) - k, by omega⟩ : Fin (3 * k)) : ℕ), by simp; omega⟩ := by
        ext; simp; omega
      rw [hi', digit_off] at hd'
      simp only [hz, hm, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero,
        zero_add] at hd'
      rw [hi']
      exact (sfac_unit h hh k c _).mul_right_eq_zero.mp hd'
  have hV : pv (Vvec h k n) = 0 := by
    have hfin : ∀ (c : Fin 4), c ≠ 2 → ∀ i < d c,
        (taylor ((place c : ℤ) : R) (pv (Vvec h k n))).coeff i = 0 := by
      intro c hc i hi
      have hi4 : i < 4 * k := by fin_cases c <;> simp at hi ⊢ <;> omega
      have := frame_fin (4 * k) c hc (Vvec h k n) ⟨i, hi4⟩
      rw [← this]
      exact hF c ⟨i, hi4⟩ hi
    refine lemmaT h2 (4 * k) _ (degree_pv_lt _) d hd (hfin 0 (by decide)) (hfin 1 (by decide))
      (hfin 3 (by decide)) ?_
    intro i hi
    have hi4 : i < 4 * k := by omega
    have := frame_inf (4 * k) (Vvec h k n) ⟨i, hi4⟩
    rw [← this]
    exact hF 2 ⟨i, hi4⟩ hi
  have hV0 := pv_eq_zero hV
  apply nb_eq_zero_imp k hk n
  intro c
  have hm : mco h k n c = 0 := by
    funext i
    refine Z3Net.Proofs.lowerTri_kill (U0 R k c) (U0_lower k c) (U0_diag h2 k c) _ k ?_ i i.isLt
    intro r hr
    rw [← Fr_Vvec_cell h k n c r hr, hV0]
    simp [Fr]
  funext i
  refine Z3Net.Proofs.lowerTri_kill (Uk h k c) (Uk_lower h k c) (Uk_diag h hh k c) _ k ?_ i i.isLt
  intro r _
  exact congrFun hm r

end kernel

end

end Z3NetD4.Proofs

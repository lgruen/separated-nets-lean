module
public import Mathlib
public import Z3Net.D4Defs

@[expose] public section

/-!
# 4D entry, part 1: the frame as polynomial readings, the basis `E_{d,j}`, Lemma T

* `pv v` is the polynomial with coefficient vector `v`; reading `c` of the frame is the Taylor
  expansion at the finite place `a_c` (`frame_fin`) resp. the reversed coefficient list at `∞`
  (`frame_inf`).
* `EPoly k d j = t^(exT) (t+1)^(exP) (t-1)^(exM)` is the basis polynomial `E_{d,j}`;
  `pv (Evec k d j) = EPoly k d j` (`pv_EvecR`).
* Cells of `E_{d,j}`: they vanish at every `c ≠ d` (`cell_E_ne`), and at `d` they form a
  lower-triangular matrix with diagonal `Q_d^k` (`cell_E_self_lt`, `cell_E_self_diag`).
* **Lemma T** (`lemmaT`, every commutative ring in which `2` is a unit): a polynomial of degree
  `< m` whose first `d_c` digits vanish in every reading, `∑ d_c = m`, is zero.
-/

namespace Z3NetD4.Proofs

open Polynomial Finset Matrix Z3NetD4

noncomputable section

variable {R : Type*} [CommRing R]

/-! ## Polynomials from coefficient vectors -/

/-- The polynomial `∑_i v_i t^i` with coefficient vector `v`. -/
def pv {m : ℕ} (v : Fin m → R) : R[X] := ∑ i : Fin m, monomial (i : ℕ) (v i)

lemma coeff_pv {m : ℕ} (v : Fin m → R) (n : ℕ) :
    (pv v).coeff n = if h : n < m then v ⟨n, h⟩ else 0 := by
  simp only [pv, finset_sum_coeff, coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h'; apply hb; ext; exact h'
    · simp
  · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; intro h'; apply h; rw [← h']; exact b.isLt

lemma coeff_pv_fin {m : ℕ} (v : Fin m → R) (i : Fin m) : (pv v).coeff i = v i := by
  rw [coeff_pv, dif_pos i.isLt]

lemma degree_pv_lt {m : ℕ} (v : Fin m → R) : (pv v).degree < m := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_pv, dif_neg (by omega)]

lemma pv_eq_zero {m : ℕ} {v : Fin m → R} (h : pv v = 0) : v = 0 := by
  funext i
  rw [← coeff_pv_fin v i, h, coeff_zero]; rfl

/-! ## Readings of the frame -/

lemma frame_fin (m : ℕ) (c : Fin 4) (hc : c ≠ 2) (v : Fin m → R) (i : Fin m) :
    ((frameGen m c).map (Int.cast : ℤ → R) *ᵥ v) i = (taylor (place c : R) (pv v)).coeff i := by
  simp only [mulVec, dotProduct, map_apply, frameGen, if_neg hc]
  rw [pv, map_sum, finset_sum_coeff]
  refine sum_congr rfl fun l _ => ?_
  rw [taylor_monomial, coeff_C_mul, coeff_X_add_C_pow]
  push_cast
  ring

lemma frameGen_two (m : ℕ) (i l : Fin m) :
    frameGen m 2 i l = if (l : ℕ) + (i : ℕ) + 1 = m then 1 else 0 := by
  simp [frameGen]

lemma frame_inf (m : ℕ) (v : Fin m → R) (i : Fin m) :
    ((frameGen m 2).map (Int.cast : ℤ → R) *ᵥ v) i = (pv v).coeff (m - 1 - i) := by
  have hi := i.isLt
  simp only [mulVec, dotProduct, map_apply, frameGen_two]
  rw [coeff_pv, dif_pos (by omega)]
  rw [Finset.sum_eq_single ⟨m - 1 - i, by omega⟩]
  · simp [show m - 1 - (i : ℕ) + i + 1 = m by omega]
  · intro b _ hb
    rw [if_neg]
    · simp
    · intro h; apply hb; ext; simp; omega
  · simp

/-! ## The basis polynomials -/

/-- `E_{d,j} = t^(exT) (t+1)^(exP) (t-1)^(exM)` over `R`. -/
def EPoly (R : Type*) [CommRing R] (k : ℕ) (d : Fin 4) (j : ℕ) : R[X] :=
  X ^ exT k d j * (X + 1) ^ exP k d j * (X - 1) ^ exM k d j

lemma EPoly_map (k : ℕ) (d : Fin 4) (j : ℕ) :
    (EPoly ℤ k d j).map (Int.castRingHom R) = EPoly R k d j := by
  simp [EPoly, Polynomial.map_mul, Polynomial.map_pow]

lemma linPow_coeff (a : ℤ) (e i : ℕ) : linPow a e i = ((X - C a) ^ e).coeff i := by
  rw [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow, linPow]; ring

lemma conv_coeff (P Q : ℤ[X]) (n : ℕ) : conv (fun i => P.coeff i) (fun i => Q.coeff i) n =
    (P * Q).coeff n := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, conv]

lemma Evec_coeff (k : ℕ) (d : Fin 4) (j : ℕ) (i : Fin (4 * k)) :
    Evec k d j i = (EPoly ℤ k d j).coeff i := by
  have e1 : (fun i => linPow 0 (exT k d j) i) = fun i => ((X - C 0 : ℤ[X]) ^ exT k d j).coeff i := by
    funext i; exact linPow_coeff _ _ _
  have e2 : (fun i => linPow (-1) (exP k d j) i) =
      fun i => ((X - C (-1) : ℤ[X]) ^ exP k d j).coeff i := by
    funext i; exact linPow_coeff _ _ _
  have e3 : (fun i => linPow 1 (exM k d j) i) = fun i => ((X - C 1 : ℤ[X]) ^ exM k d j).coeff i := by
    funext i; exact linPow_coeff _ _ _
  have e12 : conv (fun i => linPow 0 (exT k d j) i) (fun i => linPow (-1) (exP k d j) i) =
      fun i => ((X - C 0 : ℤ[X]) ^ exT k d j * (X - C (-1)) ^ exP k d j).coeff i := by
    rw [e1, e2]; funext n; exact conv_coeff _ _ n
  simp only [Evec]
  rw [show (linPow 0 (exT k d j)) = fun i => linPow 0 (exT k d j) i from rfl,
    show (linPow (-1) (exP k d j)) = fun i => linPow (-1) (exP k d j) i from rfl, e12,
    show (linPow 1 (exM k d j)) = fun i => linPow 1 (exM k d j) i from rfl, e3, conv_coeff]
  simp [EPoly, sub_eq_add_neg]

lemma natDegree_EPoly_le (k : ℕ) (d : Fin 4) (j : ℕ) :
    (EPoly R k d j).natDegree ≤ exT k d j + exP k d j + exM k d j := by
  have hX : (X : R[X]).natDegree ≤ 1 := natDegree_X_le
  have hP : (X + 1 : R[X]).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
  have hM : (X - 1 : R[X]).natDegree ≤ 1 := by rw [← C_1]; exact natDegree_X_sub_C_le 1
  unfold EPoly
  calc _ ≤ exT k d j * 1 + exP k d j * 1 + exM k d j * 1 :=
        natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans (add_le_add
          (natDegree_pow_le_of_le _ hX) (natDegree_pow_le_of_le _ hP))) (natDegree_pow_le_of_le _ hM))
    _ = _ := by ring

lemma exSum_lt (k : ℕ) (d : Fin 4) (j : ℕ) (hj : j < k) :
    exT k d j + exP k d j + exM k d j < 4 * k := by
  unfold exT exP exM
  fin_cases d <;> simp <;> omega

/-- The coefficient vector of `E_{d,j}` (cast to `R`). -/
def EvecR (k : ℕ) (d : Fin 4) (j : ℕ) : Fin (4 * k) → R := fun i => ((Evec k d j i : ℤ) : R)

lemma pv_EvecR (k : ℕ) (d : Fin 4) (j : ℕ) (hj : j < k) : pv (EvecR (R := R) k d j) = EPoly R k d j := by
  ext n
  rw [coeff_pv]
  split_ifs with hn
  · simp only [EvecR, Evec_coeff, ← EPoly_map (R := R), coeff_map, eq_intCast]
  · symm
    apply coeff_eq_zero_of_natDegree_lt
    have := natDegree_EPoly_le (R := R) k d j
    have := exSum_lt k d j hj
    omega

/-! ## Taylor expansions of the basis polynomials -/

lemma taylor_X_sub_C_pow_mul (r : R) (e : ℕ) (G : R[X]) :
    taylor r ((X - C r) ^ e * G) = X ^ e * taylor r G := by
  rw [taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]

lemma coeff_taylor_X_sub_C_pow_mul (r : R) (e : ℕ) (G : R[X]) (i : ℕ) :
    (taylor r ((X - C r) ^ e * G)).coeff i = if e ≤ i then (taylor r G).coeff (i - e) else 0 := by
  rw [taylor_X_sub_C_pow_mul, coeff_X_pow_mul']

lemma pow_split {a e : ℕ} (h : e ≤ a) (p : R[X]) : p ^ a = p ^ e * p ^ (a - e) := by
  rw [← pow_add, Nat.add_sub_cancel' h]

/-- The cofactor of `(t - a_c)^k` in `E_{d,j}` (`c` finite, `c ≠ d`). -/
def Gfac (R : Type*) [CommRing R] (k : ℕ) (c d : Fin 4) (j : ℕ) : R[X] :=
  X ^ (exT k d j - (if c = 0 then k else 0)) * (X + 1) ^ (exP k d j - (if c = 1 then k else 0)) *
    (X - 1) ^ (exM k d j - (if c = 3 then k else 0))

lemma EPoly_fac (k : ℕ) (c d : Fin 4) (j : ℕ) (hc : c ≠ 2) (hcd : c ≠ d) (hj : j < k) :
    EPoly R k d j = (X - C ((place c : ℤ) : R)) ^ k * Gfac R k c d j := by
  fin_cases c
  · have h : k ≤ exT k d j := by unfold exT; split_ifs <;> simp_all <;> omega
    simp only [EPoly, Gfac, Fin.zero_eta, Fin.isValue, if_true, show ¬((0 : Fin 4) = 1) by decide,
      show ¬((0 : Fin 4) = 3) by decide, if_false, Nat.sub_zero]
    rw [pow_split h X]; simp [place]; ring
  · have h : k ≤ exP k d j := by unfold exP; split_ifs <;> simp_all
    simp only [EPoly, Gfac, Fin.mk_one, Fin.isValue, if_true, show ¬((1 : Fin 4) = 0) by decide,
      show ¬((1 : Fin 4) = 3) by decide, if_false, Nat.sub_zero]
    rw [pow_split h (X + 1)]; simp [place]; ring
  · exact absurd rfl hc
  · have h : k ≤ exM k d j := by unfold exM; split_ifs <;> simp_all
    have e3 : ((3 : Fin 4) = 0) = False := by decide
    have e3' : ((3 : Fin 4) = 1) = False := by decide
    simp only [EPoly, Gfac]
    rw [show (⟨3, by omega⟩ : Fin 4) = 3 from rfl, if_neg (by decide), if_neg (by decide), if_pos rfl,
      Nat.sub_zero, Nat.sub_zero, pow_split h (X - 1)]
    simp [place]; ring

/-- Cells of `E_{d,j}` vanish at every finite `c ≠ d`; offset digits are those of the cofactor. -/
lemma taylor_E_ne (k : ℕ) (c d : Fin 4) (j : ℕ) (hc : c ≠ 2) (hcd : c ≠ d) (hj : j < k) (i : ℕ) :
    (taylor ((place c : ℤ) : R) (EPoly R k d j)).coeff i =
      if k ≤ i then (taylor ((place c : ℤ) : R) (Gfac R k c d j)).coeff (i - k) else 0 := by
  rw [EPoly_fac k c d j hc hcd hj, coeff_taylor_X_sub_C_pow_mul]

lemma coeff_EPoly_top (k : ℕ) (d : Fin 4) (j : ℕ) :
    (EPoly R k d j).coeff (exT k d j + exP k d j + exM k d j) = 1 := by
  have hX : (X : R[X]).natDegree ≤ 1 := natDegree_X_le
  have hP : (X + 1 : R[X]).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
  have hM : (X - 1 : R[X]).natDegree ≤ 1 := by rw [← C_1]; exact natDegree_X_sub_C_le 1
  unfold EPoly
  rw [coeff_mul_add_eq_of_natDegree_le (df := exT k d j + exP k d j) (dg := exM k d j)
    (natDegree_mul_le.trans (add_le_add ((natDegree_pow_le_of_le _ hX).trans (by simp))
      ((natDegree_pow_le_of_le _ hP).trans (by simp))))
    ((natDegree_pow_le_of_le _ hM).trans (by simp)),
    coeff_mul_add_eq_of_natDegree_le ((natDegree_pow_le_of_le _ hX).trans (by simp))
      ((natDegree_pow_le_of_le _ hP).trans (by simp))]
  rw [show (X - 1 : R[X]) = X + C (-1) by simp [sub_eq_add_neg], show (X + 1 : R[X]) = X + C 1 by simp,
    coeff_X_pow_self, coeff_X_add_C_pow, coeff_X_add_C_pow]
  simp

lemma coeff_EPoly_gt (k : ℕ) (d : Fin 4) (j n : ℕ) (hn : exT k d j + exP k d j + exM k d j < n) :
    (EPoly R k d j).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_EPoly_le k d j).trans_lt hn)

/-- The cofactor of `(t - a_d)^j` in `E_{d,j}` for finite `d`. -/
def Hself (R : Type*) [CommRing R] (k : ℕ) (d : Fin 4) : R[X] :=
  (if d = 0 then 1 else X ^ k) * (if d = 1 then 1 else (X + 1) ^ k) * (if d = 3 then 1 else (X - 1) ^ k)

lemma EPoly_self (k : ℕ) (d : Fin 4) (j : ℕ) (hd : d ≠ 2) :
    EPoly R k d j = (X - C ((place d : ℤ) : R)) ^ j * Hself R k d := by
  fin_cases d
  · simp [EPoly, Hself, exT, exP, exM, place]; ring
  · simp [EPoly, Hself, exT, exP, exM, place]; ring
  · exact absurd rfl hd
  · simp [EPoly, Hself, exT, exP, exM, place]; ring

/-- `Q_d^k = H_d(a_d)` (`(-1)^k`, `2^k`, `2^k` for `d = 0, -1, 1`). -/
def Qpow (R : Type*) [CommRing R] (k : ℕ) (d : Fin 4) : R :=
  if d = 0 then (-1) ^ k else if d = 2 then 1 else 2 ^ k

lemma Hself_eval (k : ℕ) (d : Fin 4) (hd : d ≠ 2) :
    (Hself R k d).eval ((place d : ℤ) : R) = Qpow R k d := by
  fin_cases d
  · simp [Hself, Qpow, place]
  · simp [Hself, Qpow, place, ← mul_pow]; norm_num
  · exact absurd rfl hd
  · simp [Hself, Qpow, place]; norm_num

lemma taylor_E_self (k : ℕ) (d : Fin 4) (j : ℕ) (hd : d ≠ 2) (i : ℕ) :
    (taylor ((place d : ℤ) : R) (EPoly R k d j)).coeff i =
      if j ≤ i then (taylor ((place d : ℤ) : R) (Hself R k d)).coeff (i - j) else 0 := by
  rw [EPoly_self k d j hd, coeff_taylor_X_sub_C_pow_mul]

/-! ## Lemma T -/

lemma dvd_of_taylor (r : R) (e : ℕ) (V : R[X]) (h : ∀ i < e, (taylor r V).coeff i = 0) :
    (X - C r) ^ e ∣ V := by
  obtain ⟨G, hG⟩ := X_pow_dvd_iff.mpr h
  refine ⟨taylor (-r) G, ?_⟩
  have h1 : V = taylor (-r) (taylor r V) := by rw [taylor_taylor, neg_add_cancel, taylor_zero]
  rw [h1, hG, taylor_mul, taylor_pow, taylor_X, C_neg, ← sub_eq_add_neg]

/-- **Lemma T** (frame `t = 0`): over a commutative ring in which `2` is a unit, a polynomial of
degree `< m` whose first `d 0`, `d 1`, `d 3` Taylor coefficients at `0, -1, 1` and whose top
`d 2` coefficients vanish, with `∑ d = m`, is zero. -/
theorem lemmaT (h2 : IsUnit (2 : R)) (m : ℕ) (V : R[X]) (hV : V.degree < m) (d : Fin 4 → ℕ)
    (hd : d 0 + d 1 + d 2 + d 3 = m)
    (h0 : ∀ i < d 0, (taylor ((0 : ℤ) : R) V).coeff i = 0)
    (h1 : ∀ i < d 1, (taylor ((-1 : ℤ) : R) V).coeff i = 0)
    (h3 : ∀ i < d 3, (taylor ((1 : ℤ) : R) V).coeff i = 0)
    (hinf : ∀ i < d 2, V.coeff (m - 1 - i) = 0) : V = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have d0 := dvd_of_taylor _ _ V h0
  have d1 := dvd_of_taylor _ _ V h1
  have d3 := dvd_of_taylor _ _ V h3
  have c01 : IsCoprime (X - C ((0 : ℤ) : R)) (X - C ((-1 : ℤ) : R)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by simp)
  have c03 : IsCoprime (X - C ((0 : ℤ) : R)) (X - C ((1 : ℤ) : R)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by simp)
  have c13 : IsCoprime (X - C ((-1 : ℤ) : R)) (X - C ((1 : ℤ) : R)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by push_cast; rw [show (-1 - 1 : R) = -2 by ring]; exact h2.neg)
  have hP : (X - C ((0 : ℤ) : R)) ^ d 0 * (X - C ((-1 : ℤ) : R)) ^ d 1 *
      (X - C ((1 : ℤ) : R)) ^ d 3 ∣ V :=
    IsCoprime.mul_dvd (IsCoprime.mul_left (c03.pow) (c13.pow)) ((c01.pow).mul_dvd d0 d1) d3
  have hmon : ((X - C ((0 : ℤ) : R)) ^ d 0 * (X - C ((-1 : ℤ) : R)) ^ d 1 *
      (X - C ((1 : ℤ) : R)) ^ d 3).Monic :=
    (((monic_X_sub_C _).pow _).mul ((monic_X_sub_C _).pow _)).mul ((monic_X_sub_C _).pow _)
  have e : ∀ (a : R) (n : ℕ), ((X - C a) ^ n).natDegree = n := fun a n => by
    rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hdeg : ((X - C ((0 : ℤ) : R)) ^ d 0 * (X - C ((-1 : ℤ) : R)) ^ d 1 *
      (X - C ((1 : ℤ) : R)) ^ d 3).natDegree = d 0 + d 1 + d 3 := by
    rw [(((monic_X_sub_C _).pow _).mul ((monic_X_sub_C _).pow _)).natDegree_mul
      ((monic_X_sub_C _).pow _), ((monic_X_sub_C _).pow _).natDegree_mul ((monic_X_sub_C _).pow _),
      e, e, e]
  by_contra hne
  apply hmon.not_dvd_of_degree_lt hne _ hP
  rw [degree_eq_natDegree hmon.ne_zero, hdeg]
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  by_cases hnm : m ≤ n
  · exact (degree_lt_iff_coeff_zero V m).mp hV n hnm
  · have := hinf (m - 1 - n) (by omega)
    rwa [show m - 1 - (m - 1 - n) = n by omega] at this

end

end Z3NetD4.Proofs

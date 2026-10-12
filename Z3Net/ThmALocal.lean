/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmABabai

@[expose] public section

/-!
# Theorem A, part 5: the local bounds `h_{d,j} ≤ H_s` and the bound on `a*_s`

V14 stage S5. The part "The bound on `a*_s`" of the proof of `thm:A` (`sec:Ustar`), after the
reduction `aStar_le_core` (stage S4):

* the monic Chebyshev polynomials `2^{1-j} T_j` of `[-1, 1]` (`chebM`) and of `[0, n]` (`chebI`);
* a finite column `d`: at `∞` the Chebyshev polynomial gives `A_{j,∞} ≤ √(s-1)`
  (`Ainf_fin_le`); at a prime `p` the root-placing polynomial (`rootPoly`: roots at the nodes of
  the rows `c` with the largest `v_p(c - d)`) gives `max_c |w_c g(y_c)|_p ≤ |D|_p⁻¹` with
  `D = ∏_{c finite, c ≠ d} (c - d)`, `|D| = d!(n-d)!` in the place values (`prodAp_fin_le`);
* the column `∞`: Chebyshev on `[0, n]` at `∞` (`Ainf_inf_le`), the falling factorial at `p`
  (`prodAp_inf_le`), and `(n/4)^j/j! ≤ e^{n/4} ≤ n!`;
* `h_{d,j} ≤ H_s = 2√(s-1)(s-2)!` for `s ≥ 4` (`hS_le_Hs`), hence
  `a*_s ≤ 2(s-1)^{3/2}(3/2)^{s-2}(s-2)!` (`aStar_bound_core`), and the asymptotic form
  `|log(2(s-1)^{3/2}(3/2)^{s-2}(s-2)!) - s log s| ≤ 3s` (`aStar_bound_log_core`).
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The monic Chebyshev polynomials -/

/-- The monic Chebyshev polynomial `2^{1-j} T_j` of `[-1, 1]` (`T_0 = 1`). -/
def chebM (j : ℕ) : ℝ[X] := C ((2 : ℝ) ^ (j - 1))⁻¹ * Chebyshev.T ℝ (j : ℤ)

lemma chebM_monic (j : ℕ) : (chebM j).Monic := by
  unfold Monic chebM
  rw [leadingCoeff_mul, leadingCoeff_C, Chebyshev.leadingCoeff_T, Int.natAbs_natCast]
  exact inv_mul_cancel₀ (by positivity)

lemma chebM_natDegree (j : ℕ) : (chebM j).natDegree = j := by
  unfold chebM
  rw [natDegree_C_mul (by positivity), Chebyshev.natDegree_T, Int.natAbs_natCast]

lemma chebM_abs_le (j : ℕ) (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    |(chebM j).eval x| ≤ ((2 : ℝ) ^ (j - 1))⁻¹ := by
  unfold chebM
  rw [eval_mul, eval_C, abs_mul, abs_of_pos (by positivity)]
  have h : |(Chebyshev.T ℝ (j : ℤ)).eval x| ≤ 1 := by
    rw [← Real.cos_arccos hx.1 hx.2, Chebyshev.T_real_cos]
    exact Real.abs_cos_le_one _
  calc ((2 : ℝ) ^ (j - 1))⁻¹ * |(Chebyshev.T ℝ (j : ℤ)).eval x|
      ≤ ((2 : ℝ) ^ (j - 1))⁻¹ * 1 := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := mul_one _

lemma chebM_abs_le_one (j : ℕ) (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : |(chebM j).eval x| ≤ 1 :=
  (chebM_abs_le j x hx).trans (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))

/-- The monic Chebyshev polynomial of `[0, n]`: `(n/2)^j · 2^{1-j} T_j(2x/n - 1)`. -/
def chebI (n : ℝ) (j : ℕ) : ℝ[X] := C ((n / 2) ^ j) * (chebM j).comp (C (2 / n) * (X - C (n / 2)))

lemma chebI_monic (n : ℝ) (hn : n ≠ 0) (j : ℕ) : (chebI n j).Monic ∧ (chebI n j).natDegree = j := by
  have hQ : (C (2 / n) * (X - C (n / 2))).natDegree = 1 := by
    rw [natDegree_C_mul (by positivity), natDegree_X_sub_C]
  have hQl : (C (2 / n) * (X - C (n / 2))).leadingCoeff = 2 / n := by
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_sub_C, mul_one]
  have hn2 : (n / 2) ^ j ≠ 0 := pow_ne_zero _ (by positivity)
  refine ⟨?_, ?_⟩
  · unfold Monic chebI
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by rw [hQ]; norm_num), hQl,
      chebM_monic j, chebM_natDegree, one_mul, ← mul_pow]
    rw [show n / 2 * (2 / n) = 1 by field_simp, one_pow]
  · unfold chebI
    rw [natDegree_C_mul hn2, natDegree_comp, hQ, chebM_natDegree, mul_one]

lemma chebI_abs_le (n : ℝ) (hn : 0 < n) (j : ℕ) (y : ℝ) (hy : 0 ≤ y ∧ y ≤ n) :
    |(chebI n j).eval y| ≤ 2 * (n / 4) ^ j := by
  unfold chebI
  rw [eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_sub, eval_X, eval_C, abs_mul,
    abs_of_pos (by positivity)]
  have hx : -1 ≤ 2 / n * (y - n / 2) ∧ 2 / n * (y - n / 2) ≤ 1 := by
    constructor
    · rw [show 2 / n * (y - n / 2) = 2 * y / n - 1 by field_simp]
      have : 0 ≤ 2 * y / n := div_nonneg (by linarith [hy.1]) hn.le
      linarith
    · rw [show 2 / n * (y - n / 2) = 2 * y / n - 1 by field_simp]
      have : 2 * y / n ≤ 2 := by rw [div_le_iff₀ hn]; linarith
      linarith
  have h1 := chebM_abs_le j _ hx
  have h2 : ((2 : ℝ) ^ (j - 1))⁻¹ ≤ 2 * ((2 : ℝ) ^ j)⁻¹ := by
    have h3 : (2 : ℝ) ^ j ≤ 2 * 2 ^ (j - 1) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · norm_num
      · rw [← pow_succ', Nat.sub_add_cancel hj]
    have h4 : ((2 : ℝ) ^ (j - 1))⁻¹ = 2 * (2 * (2 : ℝ) ^ (j - 1))⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num), one_mul]
    rw [h4]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h3) (by norm_num)
  have h5 : (n / 4) ^ j = (n / 2) ^ j * ((2 : ℝ) ^ j)⁻¹ := by
    rw [← inv_pow, ← mul_pow]; congr 1; ring
  calc (n / 2) ^ j * |(chebM j).eval (2 / n * (y - n / 2))|
      ≤ (n / 2) ^ j * (2 * ((2 : ℝ) ^ j)⁻¹) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = 2 * (n / 4) ^ j := by rw [h5]; ring

/-! ## Weights and nodes of the places `∞, 0, …, s-2` -/

variable {s : ℕ} [NeZero s]

lemma wQ_eq (c d : Fin s) :
    wQ c d = if c = 0 ∨ d = 0 then 1 else (((c : ℕ) : ℚ) - ((d : ℕ) : ℚ))⁻¹ := by
  unfold wQ wN
  split_ifs with h
  · rfl
  · simp [placeA, Ring.inverse_eq_inv']

lemma yQ_eq (c d : Fin s) :
    yQ c d = if c = 0 then 0 else if d = 0 then ((c : ℕ) : ℚ) - 1
      else (((c : ℕ) : ℚ) - ((d : ℕ) : ℚ))⁻¹ := by
  unfold yQ yN
  split_ifs with h1 h2
  · rfl
  · simp [placeA]
  · simp [placeA, Ring.inverse_eq_inv']

/-- The Euclidean norm of the vector of a real polynomial is at most `√(s-1)` times a bound on its
entries `c ≠ d`. -/
lemma norm_polyVecR_le (d : Fin s) (g : Polynomial ℝ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ c, c ≠ d → |(wQ c d : ℝ) * g.eval (yQ c d : ℝ)| ≤ B) :
    ‖polyVecR d g‖ ≤ Real.sqrt ((s : ℝ) - 1) * B := by
  rw [EuclideanSpace.norm_eq]
  have hle : ∑ c, ‖polyVecR d g c‖ ^ 2 ≤ ((s : ℝ) - 1) * B ^ 2 := by
    calc ∑ c, ‖polyVecR d g c‖ ^ 2 ≤ ∑ c, (if c = d then 0 else B ^ 2) := by
          refine sum_le_sum fun c _ => ?_
          rw [polyVecR_apply, Real.norm_eq_abs, sq_abs]
          split_ifs with hc
          · simp
          · rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h c hc) 2
      _ = ((s : ℝ) - 1) * B ^ 2 := by
          rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, card_rows]
          rw [Nat.cast_sub (by have := NeZero.pos s; omega)]; push_cast; ring
  calc Real.sqrt (∑ c, ‖polyVecR d g c‖ ^ 2) ≤ Real.sqrt (((s : ℝ) - 1) * B ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt ((s : ℝ) - 1) * B := by
        rw [Real.sqrt_mul' _ (sq_nonneg B), Real.sqrt_sq hB]

/-- `A_{j,∞}` is at most the size of the vector of any monic real polynomial of degree `j`. -/
lemma Ainf_le (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (g : Polynomial ℝ) (hg : g.Monic)
    (hgd : g.natDegree = j) : Ainf d j ≤ ‖polyVecR d g‖ := by
  have hB := flag_Ecol hs d j hj
  rw [Ainf_eq hs d (Ecol d) j hj hB]
  exact (Ainf_isLeast hs d (Ecol d) j hj hB).2 ⟨g, hg, hgd, rfl⟩

/-- `A_{j,p}` is at most the `p`-adic size of the vector of any monic rational polynomial of degree
`j`. -/
lemma Ap_le (hs : 3 ≤ s) (p : ℕ) [Fact p.Prime] (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (g : Polynomial ℚ) (hg : g.Monic) (hgd : g.natDegree = j) :
    Ap p d j ≤ ⨆ c, ((padicNorm p (polyVecQ d g c) : ℚ) : ℝ) := by
  rw [Ap_eq hs p d j hj]
  exact (Ap_isLeast hs p d j hj).2 ⟨g, hg, hgd, rfl⟩

lemma Ap_nonneg (hs : 3 ≤ s) (p : ℕ) [Fact p.Prime] (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    0 ≤ Ap p d j := by
  rw [Ap_eq hs p d j hj]; positivity

/-! ## The place `∞` -/

/-- A finite column: all nodes lie in `[-1, 1]` and all weights in `[-1, 1]`. -/
lemma node_fin (d : Fin s) (hd : d ≠ 0) (c : Fin s) (hc : c ≠ d) :
    |(wQ c d : ℝ)| ≤ 1 ∧ -1 ≤ (yQ c d : ℝ) ∧ (yQ c d : ℝ) ≤ 1 := by
  rw [wQ_eq, yQ_eq]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hne : ((c : ℕ) : ℝ) - ((d : ℕ) : ℝ) ≠ 0 := by
      intro h; apply hc; apply Fin.ext; exact_mod_cast sub_eq_zero.mp h
    have h1 : 1 ≤ |((c : ℕ) : ℝ) - ((d : ℕ) : ℝ)| := by
      have : (1 : ℤ) ≤ |((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)| := by
        have : ((c : ℕ) : ℤ) ≠ ((d : ℕ) : ℤ) := fun h => hc (Fin.ext (by exact_mod_cast h))
        have := Int.one_le_abs (sub_ne_zero.mpr this); exact this
      exact_mod_cast this
    have h2 : |(((c : ℕ) : ℝ) - ((d : ℕ) : ℝ))⁻¹| ≤ 1 := by
      rw [abs_inv]; exact inv_le_one_of_one_le₀ h1
    simp only [hc0, hd, or_self, ite_false]
    push_cast
    exact ⟨h2, (abs_le.mp h2).1, (abs_le.mp h2).2⟩

/-- `thm:A`, proof, finite column, the place `∞`: the monic Chebyshev polynomial `2^{1-j} T_j`
gives `A_{j,∞} ≤ √(s-1)`. -/
theorem Ainf_fin_le (hs : 3 ≤ s) (d : Fin s) (hd : d ≠ 0) (j : ℕ) (hj : j ≤ s - 2) :
    Ainf d j ≤ Real.sqrt ((s : ℝ) - 1) := by
  refine (Ainf_le hs d j hj (chebM j) (chebM_monic j) (chebM_natDegree j)).trans ?_
  have := norm_polyVecR_le d (chebM j) 1 zero_le_one fun c hc => by
    obtain ⟨hw, hy1, hy2⟩ := node_fin d hd c hc
    rw [abs_mul]
    calc |(wQ c d : ℝ)| * |(chebM j).eval (yQ c d : ℝ)| ≤ 1 * 1 :=
          mul_le_mul hw (chebM_abs_le_one j _ ⟨hy1, hy2⟩) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rwa [mul_one] at this

/-- `thm:A`, proof, the column `∞`, the place `∞`: the monic Chebyshev polynomial of `[0, n]`
(`n = s - 2`) gives `A_{j,∞} ≤ 2√(s-1)(n/4)^j`. -/
theorem Ainf_inf_le (hs : 3 ≤ s) (j : ℕ) (hj : j ≤ s - 2) :
    Ainf (0 : Fin s) j ≤ 2 * Real.sqrt ((s : ℝ) - 1) * (((s : ℝ) - 2) / 4) ^ j := by
  have hn : (0 : ℝ) < (s : ℝ) - 2 := by
    have : (3 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  obtain ⟨hm, hdeg⟩ := chebI_monic ((s : ℝ) - 2) hn.ne' j
  refine (Ainf_le hs 0 j hj _ hm hdeg).trans ?_
  have := norm_polyVecR_le (0 : Fin s) (chebI ((s : ℝ) - 2) j) (2 * (((s : ℝ) - 2) / 4) ^ j)
    (by positivity) fun c hc => by
      rw [wQ_eq, yQ_eq, if_pos (Or.inr rfl), if_neg hc, if_pos rfl]
      push_cast
      rw [one_mul]
      apply chebI_abs_le _ hn
      have h1 : 1 ≤ (c : ℕ) := Nat.one_le_iff_ne_zero.2 fun h => hc (Fin.ext h)
      have h2 : (c : ℕ) ≤ s - 1 := by have := c.isLt; omega
      constructor
      · have : (1 : ℝ) ≤ ((c : ℕ) : ℝ) := by exact_mod_cast h1
        linarith
      · have : ((c : ℕ) : ℝ) ≤ (s : ℝ) - 1 := by
          have := Nat.cast_le (α := ℝ) |>.mpr h2
          rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
        linarith
  linarith [this]

/-! ## The places `p ∈ S`: generalities -/

/-- `|·|_p` as a multiplicative map. -/
def pN (p : ℕ) [Fact p.Prime] : ℚ →*₀ ℚ where
  toFun := padicNorm p
  map_zero' := padicNorm.zero
  map_one' := padicNorm.one
  map_mul' := padicNorm.mul

lemma pN_apply (p : ℕ) [Fact p.Prime] (x : ℚ) : pN p x = padicNorm p x := rfl

lemma pN_nonneg (p : ℕ) [Fact p.Prime] (x : ℚ) : 0 ≤ pN p x := padicNorm.nonneg x

lemma pN_neg (p : ℕ) [Fact p.Prime] (x : ℚ) : pN p (-x) = pN p x := padicNorm.neg x

/-- `∏_{p ∈ S} |m|_p⁻¹ = m` for a positive integer all of whose prime factors lie in `S` (the product
formula). -/
lemma prod_padicNorm_inv (m : ℕ) (hm : m ≠ 0) (hp : ∀ p, p.Prime → p ∣ m → p ≤ s - 2) :
    ∏ p ∈ primesS s, (((padicNorm p (m : ℚ))⁻¹ : ℚ) : ℝ) = m := by
  have h := prod_primesS (s := s) m hm hp
  have h' : (∏ p ∈ primesS s, ((p ^ padicValNat p m : ℕ) : ℝ)) = (m : ℝ) := by exact_mod_cast h
  rw [← h']
  refine prod_congr rfl fun p hpS => ?_
  simp only [primesS, mem_filter] at hpS
  have : Fact p.Prime := ⟨hpS.2⟩
  rw [padicNorm_inv_eq p _ (by exact_mod_cast hm), padicValRat.of_nat, zpow_natCast]
  push_cast; rfl

/-- Among the elements of `T` with `f < 1`, at most `j` with the least values of `f`: either all
of them, or `j` of them, none of whose values exceeds that of an element left out. -/
lemma exists_top {α : Type*} [DecidableEq α] (T : Finset α) (f : α → ℚ) (j : ℕ) :
    ∃ R ⊆ T, R.card ≤ j ∧ ∀ c ∈ T, c ∉ R → f c < 1 → R.card = j ∧ ∀ r ∈ R, f r ≤ f c := by
  set T1 := T.filter (fun c => f c < 1) with hT1
  by_cases hT : T1.card ≤ j
  · exact ⟨T1, filter_subset _ _, hT, fun c hc hcR hfc => absurd (mem_filter.2 ⟨hc, hfc⟩) hcR⟩
  · push Not at hT
    have hne : (T1.powersetCard j).Nonempty := powersetCard_nonempty.2 hT.le
    obtain ⟨R, hR, hmin⟩ := exists_min_image _ (fun R => ∑ r ∈ R, f r) hne
    rw [mem_powersetCard] at hR
    refine ⟨R, hR.1.trans (filter_subset _ _), hR.2.le, fun c hc hcR hfc => ⟨hR.2, fun r hr => ?_⟩⟩
    by_contra hlt
    push Not at hlt
    have hcE : c ∉ R.erase r := fun h => hcR (mem_of_mem_erase h)
    have hmem : insert c (R.erase r) ∈ T1.powersetCard j := by
      rw [mem_powersetCard]
      refine ⟨insert_subset (mem_filter.2 ⟨hc, hfc⟩) ((erase_subset _ _).trans hR.1), ?_⟩
      rw [card_insert_of_notMem hcE, card_erase_of_mem hr]
      have := card_pos.2 ⟨r, hr⟩
      omega
    have h1 := hmin _ hmem
    rw [sum_insert hcE] at h1
    have h2 := add_sum_erase R f hr
    linarith

/-! ## A finite column at a prime `p`: the root-placing polynomial -/

/-- The finite rows `c ≠ d` (coordinates `c ≠ 0`). -/
def rowsF (d : Fin s) : Finset (Fin s) := univ.filter fun c => c ≠ 0 ∧ c ≠ d

/-- `u_c = c - d` (the difference of the place values `c - 1` and `d - 1`). -/
def uF (d c : Fin s) : ℚ := ((c : ℕ) : ℚ) - ((d : ℕ) : ℚ)

/-- `D = ∏_{c finite, c ≠ d} (c - d)`. -/
def DF (d : Fin s) : ℚ := ∏ c ∈ rowsF d, uF d c

lemma uF_ne (d c : Fin s) (hc : c ≠ d) : uF d c ≠ 0 := by
  unfold uF; intro h; apply hc; apply Fin.ext; exact_mod_cast sub_eq_zero.mp h

lemma uF_int (d c : Fin s) : uF d c = ((((c : ℕ) : ℤ) - ((d : ℕ) : ℤ) : ℤ) : ℚ) := by
  unfold uF; push_cast; ring

lemma pN_uF_le (p : ℕ) [Fact p.Prime] (d c : Fin s) : pN p (uF d c) ≤ 1 := by
  rw [pN_apply, uF_int]; exact padicNorm.of_int _

lemma pN_uF_pos (p : ℕ) [Fact p.Prime] (d c : Fin s) (hc : c ≠ d) : 0 < pN p (uF d c) :=
  padicNorm_pos p (uF_ne d c hc)

lemma wQ_fin (d : Fin s) (hd : d ≠ 0) (c : Fin s) (hc : c ∈ rowsF d) : wQ c d = (uF d c)⁻¹ := by
  simp only [rowsF, mem_filter, mem_univ, true_and] at hc
  rw [wQ_eq, if_neg (by tauto)]; rfl

lemma yQ_fin (d : Fin s) (hd : d ≠ 0) (c : Fin s) (hc : c ∈ rowsF d) : yQ c d = (uF d c)⁻¹ := by
  simp only [rowsF, mem_filter, mem_univ, true_and] at hc
  rw [yQ_eq, if_neg hc.1, if_neg hd]; rfl

/-- The root-placing polynomial `∏_{r ∈ R} (X - y_r) · X^{j - |R|}`. -/
def rootPoly (d : Fin s) (R : Finset (Fin s)) (j : ℕ) : ℚ[X] :=
  (∏ r ∈ R, (X - C (yQ r d))) * X ^ (j - R.card)

lemma rootPoly_monic (d : Fin s) (R : Finset (Fin s)) (j : ℕ) (hR : R.card ≤ j) :
    (rootPoly d R j).Monic ∧ (rootPoly d R j).natDegree = j := by
  have h1 : (∏ r ∈ R, (X - C (yQ r d))).Monic := monic_prod_of_monic _ _ fun r _ => monic_X_sub_C _
  have h2 : ((X : ℚ[X]) ^ (j - R.card)).Monic := monic_X_pow _
  refine ⟨h1.mul h2, ?_⟩
  unfold rootPoly
  rw [h1.natDegree_mul h2, natDegree_prod_of_monic _ _ fun r _ => monic_X_sub_C _, natDegree_X_pow]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
  omega

lemma rootPoly_eval (d : Fin s) (R : Finset (Fin s)) (j : ℕ) (x : ℚ) :
    (rootPoly d R j).eval x = (∏ r ∈ R, (x - yQ r d)) * x ^ (j - R.card) := by
  simp [rootPoly, eval_prod]

/-- The entries of the vector of the root-placing polynomial: `|w_c g_p(y_c)|_p ≤ |D|_p⁻¹` for every
row, if `R` holds at most `j` finite rows and, when a finite row `c ∉ R` has `p ∣ c - d`, `R` holds
`j` rows `r` with `v_p(r - d) ≥ v_p(c - d)`. -/
lemma rootPoly_entry (p : ℕ) [Fact p.Prime] (d : Fin s) (hd : d ≠ 0) (R : Finset (Fin s))
    (j : ℕ) (hRs : R ⊆ rowsF d) (hRj : R.card ≤ j)
    (hR : ∀ c ∈ rowsF d, c ∉ R → pN p (uF d c) < 1 →
      R.card = j ∧ ∀ r ∈ R, pN p (uF d r) ≤ pN p (uF d c)) (c : Fin s) :
    pN p (polyVecQ d (rootPoly d R j) c) ≤ (pN p (DF d))⁻¹ := by
  have hrow : ∀ r ∈ rowsF d, r ≠ d := fun r hr => by
    simp only [rowsF, mem_filter] at hr; exact hr.2.2
  have hpos : ∀ r ∈ rowsF d, 0 < pN p (uF d r) := fun r hr => pN_uF_pos p d r (hrow r hr)
  -- `|D|_p = ∏_{R} |u_r|_p · ∏_{rest} |u|_p`
  have hD : pN p (DF d) = (∏ r ∈ R, pN p (uF d r)) * ∏ r ∈ rowsF d \ R, pN p (uF d r) := by
    rw [DF, map_prod, mul_comm, prod_sdiff hRs]
  have hrest : ∀ T ⊆ rowsF d, 0 < ∏ r ∈ T, pN p (uF d r) ∧ ∏ r ∈ T, pN p (uF d r) ≤ 1 :=
    fun T hT => ⟨prod_pos fun r hr => hpos r (hT hr),
      prod_le_one₀ (fun r hr => (hpos r (hT hr)).le) fun r _ => pN_uF_le p d r⟩
  have hRpos := (hrest R hRs).1
  have hRest := hrest (rowsF d \ R) sdiff_subset
  by_cases hcd : c = d
  · simp only [polyVecQ, if_pos hcd, map_zero]; exact inv_nonneg.2 (pN_nonneg p _)
  simp only [polyVecQ, if_neg hcd]
  rw [rootPoly_eval]
  by_cases hc0 : c = 0
  · -- the row `∞`: `w = 1`, `y = 0`
    subst hc0
    rw [wQ_eq, yQ_eq, if_pos (Or.inl rfl), if_pos rfl, one_mul, map_mul, map_prod, map_pow]
    have h1 : ∏ r ∈ R, pN p (0 - yQ r d) = (∏ r ∈ R, pN p (uF d r))⁻¹ := by
      rw [← prod_inv_distrib]
      refine prod_congr rfl fun r hr => ?_
      rw [zero_sub, pN_neg, yQ_fin d hd r (hRs hr), map_inv₀]
    have h2 : pN p 0 ^ (j - R.card) ≤ 1 := by
      rw [map_zero]; rcases Nat.eq_zero_or_pos (j - R.card) with h | h
      · rw [h, pow_zero]
      · rw [zero_pow h.ne']; exact zero_le_one
    rw [h1, hD, mul_inv]
    calc (∏ r ∈ R, pN p (uF d r))⁻¹ * pN p 0 ^ (j - R.card)
        ≤ (∏ r ∈ R, pN p (uF d r))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hRpos.le)
      _ ≤ (∏ r ∈ R, pN p (uF d r))⁻¹ * (∏ r ∈ rowsF d \ R, pN p (uF d r))⁻¹ :=
          mul_le_mul_of_nonneg_left (one_le_inv₀ hRest.1 |>.2 hRest.2) (inv_nonneg.2 hRpos.le)
  have hcR : c ∈ rowsF d := by simp [rowsF, hc0, hcd]
  by_cases hcin : c ∈ R
  · rw [prod_eq_zero hcin (sub_self _), zero_mul, mul_zero, map_zero]
    exact inv_nonneg.2 (pN_nonneg p _)
  -- a finite row `c ∉ R`
  rw [wQ_fin d hd c hcR, yQ_fin d hd c hcR]
  set a := pN p (uF d c) with ha
  have ha0 : 0 < a := hpos c hcR
  have ha1 : a ≤ 1 := pN_uF_le p d c
  have hsub : ∀ r ∈ R, (uF d c)⁻¹ - yQ r d = (uF d r - uF d c) / (uF d c * uF d r) := by
    intro r hr
    rw [yQ_fin d hd r (hRs hr)]
    field_simp [uF_ne d c hcd, uF_ne d r (hrow r (hRs hr))]
  have hval : pN p ((uF d c)⁻¹ * ((∏ r ∈ R, ((uF d c)⁻¹ - yQ r d)) * (uF d c)⁻¹ ^ (j - R.card))) =
      (∏ r ∈ R, pN p (uF d r - uF d c)) / a ^ j * (a * ∏ r ∈ R, pN p (uF d r))⁻¹ := by
    rw [prod_congr rfl hsub, map_mul, map_mul, map_prod, map_pow, map_inv₀]
    simp only [map_div₀, map_mul]
    rw [prod_div_distrib, prod_mul_distrib, prod_const, ← ha]
    have hpow : a ^ R.card * a ^ (j - R.card) = a ^ j := by rw [← pow_add]; congr 1; omega
    rw [← hpow]
    field_simp
    rw [mul_assoc, ← mul_pow, one_div_mul_cancel ha0.ne', one_pow, mul_one]
  rw [hval]
  -- `∏_{r ∈ R} |u_r - u_c|_p ≤ a^j`
  have hnum : ∏ r ∈ R, pN p (uF d r - uF d c) ≤ a ^ j := by
    by_cases ha1' : a < 1
    · obtain ⟨hcard, hle⟩ := hR c hcR hcin ha1'
      rw [← hcard, ← prod_const]
      refine prod_le_prod₀ (fun r _ => pN_nonneg p _) fun r hr => ?_
      rw [pN_apply]
      refine padicNorm.sub.trans (max_le ?_ le_rfl)
      exact hle r hr
    · have : a = 1 := le_antisymm ha1 (not_lt.mp ha1')
      rw [this, one_pow]
      refine prod_le_one₀ (fun r _ => pN_nonneg p _) fun r _ => ?_
      rw [pN_apply, uF_int, uF_int, ← Int.cast_sub]; exact padicNorm.of_int _
  -- `|D|_p ≤ a ∏_{R} |u_r|_p`
  have hDle : pN p (DF d) ≤ a * ∏ r ∈ R, pN p (uF d r) := by
    rw [hD, mul_comm a]
    refine mul_le_mul_of_nonneg_left ?_ hRpos.le
    rw [← mul_prod_erase _ _ (mem_sdiff.2 ⟨hcR, hcin⟩)]
    have := (hrest ((rowsF d \ R).erase c) ((erase_subset c (rowsF d \ R)).trans sdiff_subset)).2
    calc pN p (uF d c) * ∏ x ∈ (rowsF d \ R).erase c, pN p (uF d x) ≤ a * 1 :=
          mul_le_mul_of_nonneg_left this ha0.le
      _ = a := mul_one a
  have hDpos : 0 < pN p (DF d) := by rw [hD]; exact mul_pos hRpos hRest.1
  calc (∏ r ∈ R, pN p (uF d r - uF d c)) / a ^ j * (a * ∏ r ∈ R, pN p (uF d r))⁻¹
      ≤ 1 * (a * ∏ r ∈ R, pN p (uF d r))⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (mul_pos ha0 hRpos).le)
        rw [div_le_one (pow_pos ha0 _)]; exact hnum
    _ ≤ (pN p (DF d))⁻¹ := by rw [one_mul]; exact inv_anti₀ hDpos hDle

/-! ## `|D| = d!(n-d)!` -/

lemma prod_rows_nat (d : ℕ) (hd : 1 ≤ d) : ∀ m, d < m →
    ∏ i ∈ (range m).filter (fun i => i ≠ 0 ∧ i ≠ d), Int.natAbs ((i : ℤ) - d) =
      (d - 1).factorial * (m - 1 - d).factorial := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have hset : (range (d + 1)).filter (fun i => i ≠ 0 ∧ i ≠ d) = Ico 1 d := by
      ext i; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hset, show d + 1 - 1 - d = 0 by omega, Nat.factorial_zero, mul_one]
    have h1 : ∏ i ∈ Ico 1 d, Int.natAbs ((i : ℤ) - d) = ∏ i ∈ Ico 1 d, i := by
      refine prod_nbij' (fun i => d - i) (fun i => d - i) (fun i hi => ?_) (fun i hi => ?_)
        (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
      all_goals simp only [mem_Ico] at hi ⊢
      all_goals omega
    rw [h1, show Ico 1 d = Ico 1 (d - 1 + 1) by congr 1; omega, prod_Ico_id_eq_factorial]
  | succ m hm ih =>
    have hset : (range (m + 1)).filter (fun i => i ≠ 0 ∧ i ≠ d) =
        insert m ((range m).filter (fun i => i ≠ 0 ∧ i ≠ d)) := by
      rw [range_add_one, filter_insert, if_pos (by omega)]
    rw [hset, prod_insert (by simp), ih]
    have h2 : Int.natAbs ((m : ℤ) - d) = m - d := by omega
    rw [h2, show m + 1 - 1 - d = (m - 1 - d) + 1 by omega, Nat.factorial_succ,
      show m - 1 - d + 1 = m - d by omega]
    ring

/-- `|D|` as a natural number. -/
def Dnat (d : Fin s) : ℕ := ∏ c ∈ rowsF d, Int.natAbs (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))

lemma Dnat_eq (d : Fin s) (hd : d ≠ 0) :
    Dnat d = ((d : ℕ) - 1).factorial * (s - 1 - (d : ℕ)).factorial := by
  have hd1 : 1 ≤ (d : ℕ) := Nat.one_le_iff_ne_zero.2 fun h => hd (Fin.ext h)
  rw [← prod_rows_nat (d : ℕ) hd1 s d.isLt]
  unfold Dnat
  have himg : (rowsF d).image (fun c : Fin s => (c : ℕ)) =
      (range s).filter (fun i => i ≠ 0 ∧ i ≠ (d : ℕ)) := by
    ext i
    simp only [rowsF, mem_image, mem_filter, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      exact ⟨c.isLt, fun h => h1 (Fin.ext h), fun h => h2 (Fin.ext h)⟩
    · rintro ⟨hi, h1, h2⟩
      exact ⟨⟨i, hi⟩, ⟨fun h => h1 (by simpa using congrArg Fin.val h),
        fun h => h2 (by simpa using congrArg Fin.val h)⟩, rfl⟩
  rw [← himg, prod_image (fun x _ y _ h => Fin.ext h)]

lemma Dnat_dvd (d : Fin s) (hd : d ≠ 0) : Dnat d ∣ (s - 2).factorial := by
  rw [Dnat_eq d hd]
  have h := Nat.factorial_mul_factorial_dvd_factorial_add ((d : ℕ) - 1) (s - 1 - (d : ℕ))
  have hd1 : 1 ≤ (d : ℕ) := Nat.one_le_iff_ne_zero.2 fun h => hd (Fin.ext h)
  rwa [show (d : ℕ) - 1 + (s - 1 - (d : ℕ)) = s - 2 by have := d.isLt; omega] at h

lemma Dnat_ne (d : Fin s) (hd : d ≠ 0) : Dnat d ≠ 0 := by
  rw [Dnat_eq d hd]; positivity

lemma pN_DF (p : ℕ) [Fact p.Prime] (d : Fin s) : pN p (DF d) = padicNorm p (Dnat d : ℚ) := by
  rw [DF, Dnat, map_prod, Nat.cast_prod, ← pN_apply, map_prod]
  refine prod_congr rfl fun c _ => ?_
  rw [uF_int]
  set z : ℤ := ((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)
  have h : ((Int.natAbs z : ℕ) : ℚ) = |(z : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h]
  rcases abs_choice (z : ℚ) with h' | h' <;> rw [h']
  exact (pN_neg p _).symm

/-! ## The local bounds -/

lemma iSup_nonneg_pN (p : ℕ) [Fact p.Prime] (f : Fin s → ℚ) :
    0 ≤ ⨆ c, ((padicNorm p (f c) : ℚ) : ℝ) :=
  (by exact_mod_cast padicNorm.nonneg (f 0) : (0 : ℝ) ≤ ((padicNorm p (f 0) : ℚ) : ℝ)).trans
    (le_iSup_val (fun c => padicNorm p (f c)) 0)

/-- A finite column `d` at a prime `p`: `A_{j,p} ≤ |D|_p⁻¹`. -/
lemma Ap_fin_le (hs : 3 ≤ s) (p : ℕ) [Fact p.Prime] (d : Fin s) (hd : d ≠ 0) (j : ℕ)
    (hj : j ≤ s - 2) : Ap p d j ≤ (((padicNorm p (Dnat d : ℚ))⁻¹ : ℚ) : ℝ) := by
  obtain ⟨R, hRs, hRj, hR⟩ := exists_top (rowsF d) (fun c => pN p (uF d c)) j
  obtain ⟨hm, hdeg⟩ := rootPoly_monic d R j hRj
  refine (Ap_le hs p d j hj _ hm hdeg).trans (iSup_le_bound _ _ fun c => ?_)
  have := rootPoly_entry p d hd R j hRs hRj hR c
  rwa [pN_DF, pN_apply] at this

/-- **`thm:A`, proof, finite column, the places `p ∈ S`**: the root-placing polynomials give
`∏_{p ∈ S} A_{j,p} ≤ d!(n-d)!` (in the place value `d - 1` of the coordinate `d`: `(d-1)!(s-1-d)!`). -/
theorem prodAp_fin_le (hs : 3 ≤ s) (d : Fin s) (hd : d ≠ 0) (j : ℕ) (hj : j ≤ s - 2) :
    ∏ p ∈ primesS s, Ap p d j ≤ (((d : ℕ) - 1).factorial * (s - 1 - (d : ℕ)).factorial : ℕ) := by
  rw [← Dnat_eq d hd, ← prod_padicNorm_inv (s := s) (Dnat d) (Dnat_ne d hd) fun p hp hpd =>
    (hp.dvd_factorial).1 (hpd.trans (Dnat_dvd d hd))]
  refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
  · simp only [primesS, mem_filter] at hp
    have : Fact p.Prime := ⟨hp.2⟩
    exact Ap_nonneg hs p d j hj
  · simp only [primesS, mem_filter] at hp
    have : Fact p.Prime := ⟨hp.2⟩
    exact Ap_fin_le hs p d hd j hj

/-- The column `∞` at a prime `p`: the falling factorial `X(X-1)⋯(X-j+1)` takes the values
`j! binom(c, j)` at the nodes, so `A_{j,p} ≤ |j!|_p`. -/
lemma Ap_inf_le (hs : 3 ≤ s) (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : j ≤ s - 2) :
    Ap p (0 : Fin s) j ≤ ((padicNorm p (j.factorial : ℚ) : ℚ) : ℝ) := by
  refine (Ap_le hs p 0 j hj (descPochhammer ℚ j) (monic_descPochhammer ℚ j)
    (descPochhammer_natDegree ℚ j)).trans (iSup_le_bound _ _ fun c => ?_)
  unfold polyVecQ
  split_ifs with hc
  · rw [padicNorm.zero]; exact padicNorm.nonneg _
  rw [wQ_eq, yQ_eq, if_pos (Or.inr rfl), if_neg hc, if_pos rfl, one_mul]
  have h1 : (1 : ℕ) ≤ (c : ℕ) := Nat.one_le_iff_ne_zero.2 fun h => hc (Fin.ext h)
  have h2 : ((c : ℕ) : ℚ) - 1 = (((c : ℕ) - 1 : ℕ) : ℚ) := by push_cast [h1]; ring
  rw [h2, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, padicNorm.mul]
  exact mul_le_of_le_one_right (padicNorm.nonneg _) (padicNorm.of_nat _)

/-- **`thm:A`, proof, the column `∞`, the places `p ∈ S`**: `∏_{p ∈ S} A_{j,p} ≤ 1/j!`. -/
theorem prodAp_inf_le (hs : 3 ≤ s) (j : ℕ) (hj : j ≤ s - 2) :
    ∏ p ∈ primesS s, Ap p (0 : Fin s) j ≤ ((j.factorial : ℕ) : ℝ)⁻¹ := by
  have hP := prod_padicNorm_inv (s := s) j.factorial (Nat.factorial_ne_zero j) fun p hp hpd =>
    ((hp.dvd_factorial).1 hpd).trans hj
  rw [← hP, ← prod_inv_distrib]
  refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
  · simp only [primesS, mem_filter] at hp
    have : Fact p.Prime := ⟨hp.2⟩
    exact Ap_nonneg hs p 0 j hj
  · simp only [primesS, mem_filter] at hp
    have : Fact p.Prime := ⟨hp.2⟩
    refine (Ap_inf_le hs p j hj).trans (le_of_eq ?_)
    push_cast; rw [inv_inv]

lemma Ainf_nonneg (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) : 0 ≤ Ainf d j := by
  have hB := flag_Ecol hs d j hj
  rw [Ainf_eq hs d (Ecol d) j hj hB]
  exact div_nonneg (norm_nonneg _) (gam_pos hs d j hj).le

lemma prodAp_nonneg (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    0 ≤ ∏ p ∈ primesS s, Ap p d j :=
  prod_nonneg fun p hp => by
    simp only [primesS, mem_filter] at hp
    have : Fact p.Prime := ⟨hp.2⟩
    exact Ap_nonneg hs p d j hj

/-- `h_{d,j} ≤ √(s-1) d!(n-d)!` for a finite column `d` (place value `d - 1`). -/
theorem hS_fin_le (hs : 3 ≤ s) (d : Fin s) (hd : d ≠ 0) (j : ℕ) (hj : j ≤ s - 2) :
    hS d j ≤ Real.sqrt ((s : ℝ) - 1) *
      ((((d : ℕ) - 1).factorial * (s - 1 - (d : ℕ)).factorial : ℕ) : ℝ) :=
  mul_le_mul (Ainf_fin_le hs d hd j hj) (prodAp_fin_le hs d hd j hj) (prodAp_nonneg hs d j hj)
    (Real.sqrt_nonneg _)

/-- `h_{∞,j} ≤ 2√(s-1)(n/4)^j/j!`. -/
theorem hS_inf_le (hs : 3 ≤ s) (j : ℕ) (hj : j ≤ s - 2) :
    hS (0 : Fin s) j ≤ 2 * Real.sqrt ((s : ℝ) - 1) * (((s : ℝ) - 2) / 4) ^ j /
      ((j.factorial : ℕ) : ℝ) := by
  rw [div_eq_mul_inv]
  exact mul_le_mul (Ainf_inf_le hs j hj) (prodAp_inf_le hs j hj) (prodAp_nonneg hs 0 j hj)
    (by have : (3 : ℝ) ≤ s := by exact_mod_cast hs
        have : 0 ≤ (s : ℝ) - 2 := by linarith
        positivity)

/-- `e^{n/4} ≤ n!` for `n ≥ 2`. -/
lemma exp_quarter_le_factorial (n : ℕ) (hn : 2 ≤ n) : Real.exp ((n : ℝ) / 4) ≤ (n.factorial : ℝ) := by
  have h2 : ∀ m : ℕ, 2 ^ m ≤ (m + 1).factorial := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Nat.factorial_succ]
      calc 2 ^ m * 2 ≤ (m + 1).factorial * 2 := Nat.mul_le_mul_right 2 ih
        _ ≤ (m + 1).factorial * (m + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (m + 1 + 1) * (m + 1).factorial := mul_comm _ _
  have h3 : (2 : ℝ) ^ (n - 1) ≤ (n.factorial : ℝ) := by
    have := h2 (n - 1); rw [Nat.sub_add_cancel (by omega)] at this; exact_mod_cast this
  refine le_trans ?_ h3
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have hl := Real.log_two_gt_d9
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  nlinarith

/-- **`thm:A`, proof, the local bounds**: `h_{d,j} ≤ H_s = 2√(s-1)(s-2)!` for every column `d` and level
`j ≤ s - 2`, `s ≥ 4`. -/
theorem hS_le_Hs (hs : 4 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    hS d j ≤ 2 * Real.sqrt ((s : ℝ) - 1) * ((s - 2).factorial : ℝ) := by
  have hs3 : 3 ≤ s := by omega
  have hsq := Real.sqrt_nonneg ((s : ℝ) - 1)
  by_cases hd : d = 0
  · subst hd
    refine (hS_inf_le hs3 j hj).trans ?_
    have hn : (s : ℝ) - 2 = ((s - 2 : ℕ) : ℝ) := by push_cast [show 2 ≤ s by omega]; ring
    rw [hn, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := Real.pow_div_factorial_le_exp (x := ((s - 2 : ℕ) : ℝ) / 4) (by positivity) j
    exact h1.trans (exp_quarter_le_factorial (s - 2) (by omega))
  · refine (hS_fin_le hs3 d hd j hj).trans ?_
    have hdv := Nat.le_of_dvd (Nat.factorial_pos _) ((Dnat_eq d hd) ▸ Dnat_dvd d hd)
    have : (((((d : ℕ) - 1).factorial * (s - 1 - (d : ℕ)).factorial : ℕ) : ℝ)) ≤
        ((s - 2).factorial : ℝ) := by exact_mod_cast hdv
    calc Real.sqrt ((s : ℝ) - 1) * ((((d : ℕ) - 1).factorial * (s - 1 - (d : ℕ)).factorial : ℕ) : ℝ)
        ≤ Real.sqrt ((s : ℝ) - 1) * ((s - 2).factorial : ℝ) := mul_le_mul_of_nonneg_left this hsq
      _ ≤ 2 * Real.sqrt ((s : ℝ) - 1) * ((s - 2).factorial : ℝ) := by
          have : 0 ≤ Real.sqrt ((s : ℝ) - 1) * ((s - 2).factorial : ℝ) := by positivity
          linarith

/-! ## The bound on `a*_s` and its asymptotic form -/

/-- `(s-1)^{3/2} = (s-1)√(s-1)`. -/
lemma rpow_three_halves (x : ℝ) (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rcases hx.eq_or_lt with h | h
  · subst h; rw [Real.zero_rpow (by norm_num)]; simp
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- **`thm:A`, the bound on `a*_s`** (`s ≥ 4`): every entry `|E_{d,j}[c]|` of `U*_s` is at most
`(3/2)^{s-2} H_s` and `a*_s ≤ 2(s-1)^{3/2}(3/2)^{s-2}(s-2)!`. -/
theorem aStar_bound_core (hs : 4 ≤ s) :
    (∀ d c : Fin s, ∀ j ≤ s - 2,
        |(Ecol d j c : ℝ)| ≤ (3 / 2) ^ (s - 2) * (2 * Real.sqrt ((s : ℝ) - 1) * ((s - 2).factorial : ℝ))) ∧
      (aStar s : ℝ) ≤ 2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ) := by
  obtain ⟨h1, h2⟩ := aStar_le_core (by omega : 3 ≤ s) _ fun d j hj => hS_le_Hs hs d j hj
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [rpow_three_halves _ (by have : (4 : ℝ) ≤ s := by exact_mod_cast hs
                              linarith)]
  ring

/-- **`thm:A`, the asymptotic form** `2(s-1)^{3/2}(3/2)^{s-2}(s-2)! = e^{s log s + O(s)}`, with an
explicit constant: `|log(2(s-1)^{3/2}(3/2)^{s-2}(s-2)!) - s log s| ≤ 3s` for every `s ≥ 4`. -/
theorem aStar_bound_log_core (s : ℕ) (hs : 4 ≤ s) :
    |Real.log (2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ)) -
      s * Real.log s| ≤ 3 * s := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 2 := ⟨s - 2, by omega⟩
  have hn : 2 ≤ n := by omega
  rw [show n + 2 - 2 = n by omega]
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  rw [show (n : ℝ) + 2 - 1 = n + 1 by ring]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hn1 : (0 : ℝ) < n + 1 := by linarith
  rw [Real.log_mul (by positivity) hf.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_rpow hn1, Real.log_pow]
  -- the factorial: `n log n - n ≤ log n! ≤ n log n`
  have hfu : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log hf (by exact_mod_cast Nat.factorial_le_pow n)
  have hfl : n * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (by positivity) n
    have hpos : (0 : ℝ) < (n : ℝ) ^ n / n.factorial := by positivity
    have := Real.log_le_log hpos h
    rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at this
    linarith
  -- elementary logarithms
  have hl2 : 0 < Real.log 2 ∧ Real.log 2 ≤ 1 := ⟨Real.log_pos (by norm_num),
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)⟩
  have hl32 : 0 < Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ 1 / 2 := ⟨Real.log_pos (by norm_num),
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)⟩
  have hln1 : 0 ≤ Real.log (n + 1) ∧ Real.log (n + 1) ≤ n :=
    ⟨Real.log_nonneg (by linarith), (Real.log_le_sub_one_of_pos hn1).trans (by linarith)⟩
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hmono : Real.log n ≤ Real.log (n + 2) := Real.log_le_log (by linarith) (by linarith)
  have hln2 : Real.log (n + 2) ≤ n + 1 := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hdiff : Real.log (n + 2) - Real.log n ≤ 2 / n := by
    rw [← Real.log_div (by linarith) (by linarith)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp; ring
  have hnd : (n : ℝ) * (2 / n) = 2 := by field_simp
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdiff (by linarith : (0 : ℝ) ≤ n)]
  · nlinarith [mul_le_mul_of_nonneg_left hmono (by linarith : (0 : ℝ) ≤ n)]

end

end Z3NetA.Proofs

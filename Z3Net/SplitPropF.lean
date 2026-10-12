module
public import Z3Net.SplitGs
public import Z3Net.FPropF

@[expose] public section

/-!
# Entry Split, part 4: `prop:Gsplit` (`prop:F` on the split frame, both directions)

* `Gsplit_reach_iff`: for `k ≥ s-1`, the off-diagonal design is reachable from the split frame by
  lower-triangular unit-diagonal column gauges with row scalars `λ'_c P_c^(-k)` iff the residual
  problem is solvable (`⇐` is `Gsplit_row0`; `⇒` factors `U_d = Toep(Π_d(v_d + x)) V_d`).
* `Gsplit_poly_iff`: the residual problem is solvable iff the partial sums are
  `λ'_c g(y_cd)/(u_c - v_d)` with `g` of degree `j` and unit leading coefficient.
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s : ℕ}

/-! ## Polynomial form -/

theorem Gsplit_poly_iff [Nontrivial R] (u v : Fin s → R)
    (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (hlam : ∀ c, IsUnit (lam c)) :
    (∃ Ur : Fin s → ℕ → ℕ → R, Z3NetF.ResidualS u v F lam Ur) ↔
      ∀ d : Fin s, ∀ j, j < s - 1 → ∃ g : Polynomial R, g.natDegree = j ∧
        IsUnit g.leadingCoeff ∧ ∀ c, c ≠ d →
          Z3NetF.Msum F j c d = lam c * g.eval (Z3NetF.ySplit u v c d) * Ring.inverse (u c - v d) := by
  have hform : ∀ c d (g : R[X]), lam c * g.eval (Z3NetF.ySplit u v c d) * Ring.inverse (u c - v d) =
      lam c * Z3NetF.ySplit u v c d * g.eval (Z3NetF.ySplit u v c d) := by
    intro c d g; unfold Z3NetF.ySplit; ring
  constructor
  · rintro ⟨Ur, hres⟩ d j hj
    let g : R[X] := ∑ n ∈ range (j + 1), ∑ n' ∈ range (n + 1), C (Ur d n' n) * X ^ n'
    have hcoeff : ∀ t, g.coeff t = ∑ n ∈ range (j + 1), if t ≤ n then Ur d t n else 0 := by
      intro t
      simp only [g, finset_sum_coeff, coeff_C_mul_X_pow]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_ite_eq (range (n + 1)) t]
      simp only [mem_range, Nat.lt_succ_iff]
    have hcj : g.coeff j = Ur d j j := by
      rw [hcoeff, Finset.sum_eq_single j]
      · rw [if_pos le_rfl]
      · intro n hn hnj
        have := mem_range.mp hn
        rw [if_neg (by omega)]
      · intro h; exact absurd (mem_range.mpr (by omega)) h
    have hdeg_le : g.natDegree ≤ j := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro t ht
      rw [hcoeff]
      refine Finset.sum_eq_zero fun n hn => ?_
      have := mem_range.mp hn
      rw [if_neg (by have hjt : j < t := (by exact_mod_cast ht); omega)]
    have hu : IsUnit (g.coeff j) := hcj ▸ hres.2.2.1 d j hj
    have hdeg : g.natDegree = j :=
      le_antisymm hdeg_le (le_natDegree_of_ne_zero hu.ne_zero)
    refine ⟨g, hdeg, by rw [leadingCoeff, hdeg]; exact hu, fun c hc => ?_⟩
    rw [hform]
    simp only [Z3NetF.Msum, g, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hres.2.2.2 c d hc n (by have := mem_range.mp hn; omega), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    ring
  · intro H
    choose! G hGdeg hGu hGval0 using H
    have hGval : ∀ d j, j < s - 1 → ∀ c, c ≠ d →
        Z3NetF.Msum F j c d = lam c * Z3NetF.ySplit u v c d * (G d j).eval (Z3NetF.ySplit u v c d) := by
      intro d j hj c hc; rw [hGval0 d j hj c hc, hform]
    refine ⟨fun d n' n => if n = 0 then (G d 0).coeff n' else (G d n - G d (n - 1)).coeff n',
      hlam, ?_, ?_, ?_⟩
    · intro d n' n hnn' hn's
      have hn : n < s - 1 := by omega
      simp only
      split_ifs with h0
      · subst h0
        apply coeff_eq_zero_of_natDegree_lt
        rw [hGdeg d 0 hn]; omega
      · rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by rw [hGdeg d n hn]; omega),
          coeff_eq_zero_of_natDegree_lt (by rw [hGdeg d (n - 1) (by omega)]; omega), sub_zero]
    · intro d n hn
      simp only
      split_ifs with h0
      · subst h0
        have := hGu d 0 hn
        rwa [leadingCoeff, hGdeg d 0 hn] at this
      · rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (p := G d (n - 1))
          (by rw [hGdeg d (n - 1) (by omega)]; omega), sub_zero]
        have := hGu d n hn
        rwa [leadingCoeff, hGdeg d n hn] at this
    · intro c d hcd n hn
      have hval : F n c d = lam c * Z3NetF.ySplit u v c d *
          (if n = 0 then G d 0 else G d n - G d (n - 1)).eval (Z3NetF.ySplit u v c d) := by
        split_ifs with h0
        · subst h0
          rw [← hGval d 0 hn c hcd]; simp [Z3NetF.Msum]
        · have e1 := hGval d n hn c hcd
          have e2 := hGval d (n - 1) (by omega) c hcd
          have e3 : Z3NetF.Msum F n c d = Z3NetF.Msum F (n - 1) c d + F n c d := by
            simp only [Z3NetF.Msum]
            rw [show n + 1 = (n - 1 + 1) + 1 by omega, Finset.sum_range_succ,
              show n - 1 + 1 = n by omega]
          rw [eval_sub, mul_sub, ← e1, ← e2, e3]; ring
      rw [hval]
      have hdeg : (if n = 0 then G d 0 else G d n - G d (n - 1)).natDegree < n + 1 := by
        split_ifs with h0
        · subst h0; rw [hGdeg d 0 hn]; omega
        · refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
          rw [hGdeg d n hn, hGdeg d (n - 1) (by omega)]; omega
      rw [eval_eq_sum_range' hdeg, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n' _ => ?_
      by_cases h0 : n = 0
      · simp only [h0, if_true]; ring
      · simp only [h0, if_false]; ring

/-! ## Reachability -/

theorem Gsplit_reach_iff (hs : 2 ≤ s) (k : ℕ) (hk : s - 1 ≤ k)
    (u v : Fin s → R) (huv : Z3NetF.SplitOK u v) (F : ℕ → Fin s → Fin s → R)
    (lam : Fin s → R) (hlam : ∀ c, IsUnit (lam c)) :
    (∃ U : Fin s → Matrix (Fin k) (Fin k) R, (∀ d i j, i < j → U d i j = 0) ∧
      (∀ d i, IsUnit (U d i i)) ∧ ∀ c d, c ≠ d → ∀ (r : Fin (s * k - k)), (r : ℕ) = 0 →
        ∀ j : Fin k, (Z3NetF.LmatS k u v lam c * Z3NetF.splitGraph R k u v c d * U d) r j =
          if k - 1 - (j : ℕ) < s - 1 then F (k - 1 - (j : ℕ)) c d else 0) ↔
    ∃ Ur : Fin s → ℕ → ℕ → R, Z3NetF.ResidualS u v F lam Ur := by
  classical
  constructor
  · rintro ⟨U, hUl, hUu, hrow⟩
    have hTdet : ∀ d, IsUnit (Z3NetF.toep k (Z3NetF.piSplit k v d)).det := by
      intro d
      rw [det_of_isLowerTriangular _ (fun i j hij => toep_lower k _ i j hij)]
      rw [IsUnit.prod_univ_iff]; intro i
      simp only [Z3NetF.toep, le_refl, if_true, Nat.sub_self]
      exact piSplit_unit k u v huv d
    set V : Fin s → Matrix (Fin k) (Fin k) R :=
      fun d => (Z3NetF.toep k (Z3NetF.piSplit k v d))⁻¹ * U d with hV
    have hTinv_lower : ∀ d, ∀ i j : Fin k, i < j →
        (Z3NetF.toep k (Z3NetF.piSplit k v d))⁻¹ i j = 0 := by
      intro d i j hij
      letI := invertibleOfIsUnitDet _ (hTdet d)
      have hbt : (Z3NetF.toep k (Z3NetF.piSplit k v d)).BlockTriangular OrderDual.toDual :=
        fun i j hij => toep_lower k _ i j hij
      exact blockTriangular_inv_of_blockTriangular hbt hij
    have hVl : ∀ d i j, i < j → V d i j = 0 := fun d =>
      lower_mul _ _ (hTinv_lower d) (hUl d)
    have hVu : ∀ d i, IsUnit (V d i i) := by
      intro d i
      show IsUnit (((Z3NetF.toep k (Z3NetF.piSplit k v d))⁻¹ * U d) i i)
      rw [diag_mul _ _ (hTinv_lower d) (hUl d)]
      refine IsUnit.mul ?_ (hUu d i)
      have h1 : ((Z3NetF.toep k (Z3NetF.piSplit k v d))⁻¹ *
          Z3NetF.toep k (Z3NetF.piSplit k v d)) i i = 1 := by
        rw [nonsing_inv_mul _ (hTdet d), one_apply_eq]
      rw [diag_mul _ _ (hTinv_lower d) (fun i j hij => toep_lower k _ i j hij)] at h1
      exact IsUnit.of_mul_eq_one _ h1
    have hUV : ∀ d, U d = Z3NetF.toep k (Z3NetF.piSplit k v d) * V d := by
      intro d; rw [hV, ← Matrix.mul_assoc, mul_nonsing_inv _ (hTdet d), Matrix.one_mul]
    refine ⟨fun d n' n => if h : n' < k ∧ n < k then V d ⟨k - 1 - n', by omega⟩ ⟨k - 1 - n, by omega⟩
      else 0, hlam, ?_, ?_, ?_⟩
    · intro d n' n hnn' hn's
      simp only
      rw [dif_pos ⟨by omega, by omega⟩]
      exact hVl d _ _ (by show k - 1 - n' < k - 1 - n; omega)
    · intro d n hn
      simp only
      rw [dif_pos ⟨by omega, by omega⟩]
      exact hVu d _
    · intro c d hcd n hn
      have hr0 : (0 : ℕ) < s * k - k := by
        have : 1 ≤ k := by omega
        have : 2 * k ≤ s * k := Nat.mul_le_mul_right k hs
        omega
      have h := hrow c d hcd ⟨0, hr0⟩ rfl ⟨k - 1 - n, by omega⟩
      simp only [show k - 1 - (k - 1 - n) = n by omega, if_pos hn] at h
      rw [← h, hUV d, ← Matrix.mul_assoc, mul_apply]
      simp only [srow0_LPT k u v lam huv c d hcd ⟨0, hr0⟩ rfl]
      set y := Z3NetF.ySplit u v c d
      have hA : ∑ l : Fin k, lam c * (y * y ^ (k - 1 - (l : ℕ))) * V d l ⟨k - 1 - n, by omega⟩ =
          ∑ l ∈ range k, (if h : l < k then lam c * (y * y ^ (k - 1 - l)) *
            V d ⟨l, h⟩ ⟨k - 1 - n, by omega⟩ else 0) := by
        rw [← Fin.sum_univ_eq_sum_range (fun l => if h : l < k then lam c * (y * y ^ (k - 1 - l)) *
          V d ⟨l, h⟩ ⟨k - 1 - n, by omega⟩ else 0) k]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [dif_pos l.isLt]
      rw [hA, ← Finset.sum_range_reflect, Finset.mul_sum]
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by omega))
      · intro n' hn'
        simp only [mem_sdiff, mem_range] at hn'
        rw [dif_pos (by omega)]
        have := hVl d ⟨k - 1 - n', by omega⟩ ⟨k - 1 - n, by omega⟩
          (by show k - 1 - n' < k - 1 - n; omega)
        rw [this, mul_zero]
      · intro n' hn'
        simp only [mem_range] at hn'
        have c1 : n' < k ∧ n < k := ⟨by omega, by omega⟩
        have c2 : k - 1 - n' < k := by omega
        rw [dif_pos c1, dif_pos c2]
        have e : k - 1 - (k - 1 - n') = n' := by omega
        simp only [e]
        ring
  · rintro ⟨Ur, hres⟩
    have hb := fun d n => Gsplit_beta hs u v huv F lam Ur hres d n
    choose b hb1 _ using hb
    let β : Fin s → ℕ → ℕ → R := fun d n i => if h : i < s - 1 then b d n ⟨i, h⟩ else 0
    have hβ : Z3NetF.BetaRelS u v F lam β := by
      intro d n _ c hc
      rw [hb1 d n c hc, ← Fin.sum_univ_eq_sum_range (fun i => β d n i * F i c d) (s - 1)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [β, dif_pos i.isLt]
    obtain ⟨-, -, hU, hUu⟩ := Gsplit_gauge k u v huv F lam Ur β hres
    exact ⟨Z3NetF.UgaugeS k v Ur β, hU, hUu, fun c d hcd r hr j =>
      Gsplit_row0 k u v huv F lam Ur β hres hβ c d hcd r hr j⟩

end

end Z3NetF.Proofs

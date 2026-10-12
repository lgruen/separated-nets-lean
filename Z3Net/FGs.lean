module
public import Z3Net.FRs

@[expose] public section

/-!
# Entry F, part 9: `prop:Gs` (the all-`k` gauge)
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (inf : Fin s) (x : Fin s → R)
  (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R)

/-! ## The gauge is lower triangular with unit diagonal -/

lemma lower_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) : ∀ i j, i < j → (A * B) i j = 0 := by
  intro i j hij
  rw [mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : i < l
  · rw [hA i l h, zero_mul]
  · rw [hB l j (lt_of_le_of_lt (not_lt.mp h) hij), mul_zero]

lemma diag_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hB l i h, mul_zero]
    · rw [hA i l h, zero_mul]
  · simp

lemma toep_lower (u : R[X]) : ∀ i j : Fin k, i < j → Z3NetF.toep k u i j = 0 := by
  intro i j hij
  simp only [Z3NetF.toep]
  rw [if_neg (not_le.mpr hij)]

lemma Uxm_lower (hres : Z3NetF.Residual inf x F lam Ur) (d : Fin s) :
    ∀ i j : Fin k, i < j → Z3NetF.Ux Ur β d (k - 1 - (i : ℕ)) (k - 1 - (j : ℕ)) = 0 := by
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  have hjk := j.isLt
  simp only [Z3NetF.Ux]
  split_ifs with h1 h2 h3 h4
  · exact hres.2.1 d _ _ (by omega) h2
  · rfl
  · omega
  · omega
  · rfl

lemma Uxm_diag (hres : Z3NetF.Residual inf x F lam Ur) (d : Fin s) (i : Fin k) :
    IsUnit (Z3NetF.Ux Ur β d (k - 1 - (i : ℕ)) (k - 1 - (i : ℕ))) := by
  simp only [Z3NetF.Ux]
  by_cases h1 : k - 1 - (i : ℕ) < s - 1
  · rw [if_pos h1, if_pos h1]; exact hres.2.2.1 d _ h1
  · rw [if_neg h1]; simp

theorem Gs_gauge_core (hx : Z3NetF.PlacesOK inf x) (hres : Z3NetF.Residual inf x F lam Ur) :
    (∀ c i j, i < j → Z3NetF.Lmat k inf x lam c i j = 0) ∧
      (∀ c i, IsUnit (Z3NetF.Lmat k inf x lam c i i)) ∧
      (∀ d i j, i < j → Z3NetF.Ugauge k inf x Ur β d i j = 0) ∧
      (∀ d i, IsUnit (Z3NetF.Ugauge k inf x Ur β d i i)) := by
  refine ⟨fun c i j hij => ?_, fun c i => ?_, fun d i j hij => ?_, fun d i => ?_⟩
  · simp only [Z3NetF.Lmat, Z3NetF.Lgauge]
    rw [diagonal_apply_ne _ (ne_of_lt hij)]
  · simp only [Z3NetF.Lmat, Z3NetF.Lgauge, diagonal_apply_eq]
    split_ifs
    · exact (hres.1 c).mul ((Qf_unit inf x hx c).pow k).ringInverse
    · exact isUnit_one
  · exact lower_mul _ _ (toep_lower k _) (fun i j h => by
      simp only [of_apply]; exact Uxm_lower k inf x F lam Ur β hres d i j h) i j hij
  · rw [Z3NetF.Ugauge, diag_mul _ _ (toep_lower k _) (fun i j h => by
      simp only [of_apply]; exact Uxm_lower k inf x F lam Ur β hres d i j h)]
    refine IsUnit.mul ?_ ?_
    · simp only [Z3NetF.toep, le_refl, if_true, Nat.sub_self]
      exact uN_unit k inf x hx d
    · simp only [of_apply]; exact Uxm_diag k inf x F lam Ur β hres d i

/-! ## Row `0` of the gauged block -/

lemma row0_LPT (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) (hcd : c ≠ d) (r : Fin (s * k - k))
    (hr : (r : ℕ) = 0) (l : Fin k) :
    (Z3NetF.Lmat k inf x lam c * Z3NetF.frameGraph R k inf x c d *
        Z3NetF.toep k (Z3NetF.uN k inf x d)) r l =
      lam c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ (k - 1 - (l : ℕ))) := by
  have h := Ns_row0_core k inf x hx c d hcd r hr l
  rw [Matrix.mul_assoc, Z3NetF.Lgauge, diagonal_mul, if_pos hr] at h
  rw [Matrix.mul_assoc, Z3NetF.Lmat, Z3NetF.Lgauge, diagonal_mul, if_pos hr, mul_assoc, h]

/-- The sum `∑_{n' < k} λ' w y^(n') Ux[n', n]` is the design (`n < s-1`) or `0`. -/
lemma sum_Ux (hres : Z3NetF.Residual inf x F lam Ur) (hβ : Z3NetF.BetaRel inf x F lam β)
    (c d : Fin s) (hcd : c ≠ d) (n : ℕ) (hn : n < k) :
    ∑ n' ∈ range k, lam c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ n') * Z3NetF.Ux Ur β d n' n =
      if n < s - 1 then F n c d else 0 := by
  set g : ℕ → R := fun n' => lam c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ n') with hg
  -- `∑_{n' ≤ i} g n' Ur n' i = F i` for `i < s-1`
  have hF0 : ∀ i, i < s - 1 → ∑ n' ∈ range (i + 1), g n' * Ur d n' i = F i c d := by
    intro i hi
    rw [hres.2.2.2 c d hcd i hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    simp only [hg]; ring
  -- the same sum over `n' < N` for any `N ≥ i + 1`, `N ≤ s - 1` resp. `k`
  have hFN : ∀ i N, i < s - 1 → i + 1 ≤ N →
      ∑ n' ∈ range N, g n' * (if n' < s - 1 then Ur d n' i else 0) = F i c d := by
    intro i N hi hN
    rw [← hF0 i hi]
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr hN)
    · intro n' hn'
      simp only [mem_sdiff, mem_range] at hn'
      split_ifs with h
      · rw [hres.2.1 d n' i (by omega) h, mul_zero]
      · rw [mul_zero]
    · intro n' hn'
      simp only [mem_range] at hn'
      rw [if_pos (by omega)]
  by_cases hns : n < s - 1
  · rw [if_pos hns, ← hFN n k hns (by omega)]
    refine Finset.sum_congr rfl fun n' _ => ?_
    simp only [Z3NetF.Ux, if_pos hns, hg]
  · rw [if_neg hns]
    have hsk : s - 1 ≤ k := by omega
    have hsplit : ∀ n', Z3NetF.Ux Ur β d n' n = (if n' = n then 1 else 0) +
        (if n' < s - 1 then -∑ i ∈ range (s - 1), β d n i * Ur d n' i else 0) := by
      intro n'
      simp only [Z3NetF.Ux, if_neg hns]
      by_cases h1 : n' = n
      · rw [if_pos h1, if_pos h1, if_neg (by omega), add_zero]
      · rw [if_neg h1, if_neg h1, zero_add]
    simp only [hsplit, mul_add, Finset.sum_add_distrib]
    have e1 : ∑ n' ∈ range k, g n' * (if n' = n then 1 else 0) = g n := by
      rw [Finset.sum_eq_single n]
      · rw [if_pos rfl, mul_one]
      · intro b _ hb; rw [if_neg hb, mul_zero]
      · intro h; exact absurd (mem_range.mpr hn) h
    have e2 : ∑ n' ∈ range k, g n' * (if n' < s - 1 then -∑ i ∈ range (s - 1), β d n i * Ur d n' i else 0) =
        -∑ i ∈ range (s - 1), β d n i * F i c d := by
      have : ∀ n', g n' * (if n' < s - 1 then -∑ i ∈ range (s - 1), β d n i * Ur d n' i else 0) =
          -∑ i ∈ range (s - 1), β d n i * (g n' * (if n' < s - 1 then Ur d n' i else 0)) := by
        intro n'
        split_ifs
        · rw [mul_neg, Finset.mul_sum]; congr 1
          refine Finset.sum_congr rfl fun i _ => by ring
        · simp
      simp only [this, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.mul_sum, hFN i k (mem_range.mp hi) (by have := mem_range.mp hi; omega)]
    rw [e1, e2, ← hβ d n (by omega) c hcd]
    simp only [hg]; ring

theorem Gs_row0_core (hx : Z3NetF.PlacesOK inf x) (hres : Z3NetF.Residual inf x F lam Ur)
    (hβ : Z3NetF.BetaRel inf x F lam β) (c d : Fin s) (hcd : c ≠ d) (r : Fin (s * k - k))
    (hr : (r : ℕ) = 0) (j : Fin k) :
    (Z3NetF.Lmat k inf x lam c * Z3NetF.frameGraph R k inf x c d * Z3NetF.Ugauge k inf x Ur β d) r j =
      if k - 1 - (j : ℕ) < s - 1 then F (k - 1 - (j : ℕ)) c d else 0 := by
  rw [Z3NetF.Ugauge, ← Matrix.mul_assoc, mul_apply]
  simp only [row0_LPT k inf x lam hx c d hcd r hr, of_apply]
  rw [← sum_Ux k inf x F lam Ur β hres hβ c d hcd (k - 1 - j) (by omega)]
  rw [Fin.sum_univ_eq_sum_range (fun l => lam c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ (k - 1 - l)) *
    Z3NetF.Ux Ur β d (k - 1 - l) (k - 1 - (j : ℕ))) k]
  exact Finset.sum_range_reflect (fun n' => lam c * (Z3NetF.wN inf x c d * Z3NetF.yN inf x c d ^ n') *
    Z3NetF.Ux Ur β d n' (k - 1 - (j : ℕ))) k

end

end Z3NetF.Proofs

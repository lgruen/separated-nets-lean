module
public import Mathlib
public import Z3Net.SUDefN

@[expose] public section

/-!
# Entry U, part 13: uniqueness of `γ_n` (Proposition G_s)

The difference of two solutions is a polynomial of degree `< s - 1` vanishing at the `s - 1`
distinct nodes `y_cd` (`c ≠ d`), hence zero.
-/

namespace Z3NetU.Proofs

open Polynomial Finset Matrix Z3NetU

noncomputable section

variable {s : ℕ}

local notation "ivQ" => (fun i : ℕ => ((i : ℕ) : ℚ)⁻¹)

lemma yN_rat (c d : Fin s) : yN ivQ c d =
    if (c : ℕ) = 0 then 0 else if (d : ℕ) = 0 then ((c : ℚ) - 1) else (((c : ℚ) - d))⁻¹ := by
  unfold yN
  split_ifs
  · rfl
  · simp [place]
  · rw [ivz_rat]; push_cast; rfl

lemma wN_ne_zero (c d : Fin s) (hcd : c ≠ d) : wN ivQ c d ≠ 0 := by
  unfold wN
  split_ifs with h
  · exact one_ne_zero
  · push_neg at h
    rw [ivz_rat]
    have : (c : ℕ) ≠ d := fun h' => hcd (Fin.ext h')
    have : ((c : ℤ) - d : ℤ) ≠ 0 := by omega
    exact inv_ne_zero (by exact_mod_cast this)

lemma yN_inj (d : Fin s) (c c' : Fin s) (hc : c ≠ d) (hc' : c' ≠ d)
    (h : yN ivQ c d = yN ivQ c' d) : c = c' := by
  rw [yN_rat, yN_rat] at h
  have hcv : (c : ℕ) ≠ d := fun h' => hc (Fin.ext h')
  have hcv' : (c' : ℕ) ≠ d := fun h' => hc' (Fin.ext h')
  apply Fin.ext
  by_cases h0 : (c : ℕ) = 0 <;> by_cases h0' : (c' : ℕ) = 0
  · omega
  · rw [if_pos h0, if_neg h0'] at h
    have hd : (d : ℕ) ≠ 0 := fun h' => hcv (by rw [h0, h'])
    rw [if_neg hd] at h
    have : ((c' : ℚ) - d) ≠ 0 := by
      have : ((c' : ℕ) : ℚ) ≠ (d : ℕ) := by exact_mod_cast hcv'
      intro h''; apply this; linarith
    exact absurd h.symm (inv_ne_zero this)
  · rw [if_neg h0, if_pos h0'] at h
    have hd : (d : ℕ) ≠ 0 := fun h' => hcv' (by rw [h0', h'])
    rw [if_neg hd] at h
    have : ((c : ℚ) - d) ≠ 0 := by
      have : ((c : ℕ) : ℚ) ≠ (d : ℕ) := by exact_mod_cast hcv
      intro h''; apply this; linarith
    exact absurd h (inv_ne_zero this)
  · rw [if_neg h0, if_neg h0'] at h
    by_cases hd : (d : ℕ) = 0
    · rw [if_pos hd, if_pos hd] at h
      have : ((c : ℕ) : ℚ) = (c' : ℕ) := by linarith
      exact_mod_cast this
    · rw [if_neg hd, if_neg hd, _root_.inv_inj] at h
      have : ((c : ℕ) : ℚ) = (c' : ℕ) := by linarith
      exact_mod_cast this

/-- **Proposition G_s, uniqueness.** -/
theorem U_gam_unique (s : ℕ) (hs : 3 ≤ s) (d : Fin s) (n : ℕ) (g : ℕ → ℚ)
    (hg : ∀ c : Fin s, c ≠ d → ∑ i ∈ range (s - 1), g i *
      (wN (fun i => ((i : ℕ) : ℚ)⁻¹) c d * yN (fun i => ((i : ℕ) : ℚ)⁻¹) c d ^ i) =
        wN (fun i => ((i : ℕ) : ℚ)⁻¹) c d * yN (fun i => ((i : ℕ) : ℚ)⁻¹) c d ^ n) :
    ∀ i < s - 1, g i = gam (fun i => ((i : ℕ) : ℚ)⁻¹) d n i := by
  set P : ℚ[X] := ∑ i ∈ range (s - 1), C (g i - gam ivQ d n i) * X ^ i with hP
  have hroot : ∀ c : {c : Fin s // c ≠ d}, P.eval (yN ivQ c.1 d) = 0 := by
    rintro ⟨c, hc⟩
    have h1 := hg c hc
    have h2 := propG (iv := ivQ) hs c d hc n
    have hsum : wN ivQ c d * ∑ i ∈ range (s - 1), (g i - gam ivQ d n i) * yN ivQ c d ^ i = 0 := by
      rw [Finset.mul_sum]
      have : ∑ i ∈ range (s - 1), wN ivQ c d * ((g i - gam ivQ d n i) * yN ivQ c d ^ i) =
          ∑ i ∈ range (s - 1), g i * (wN ivQ c d * yN ivQ c d ^ i) -
            ∑ i ∈ range (s - 1), gam ivQ d n i * (wN ivQ c d * yN ivQ c d ^ i) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, h1, ← h2, sub_self]
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h (wN_ne_zero c d hc)
    · rw [hP, eval_finset_sum]
      simpa [eval_mul, eval_C, eval_pow, eval_X] using h
  have hdeg : P.natDegree < Fintype.card {c : Fin s // c ≠ d} := by
    have hcard : Fintype.card {c : Fin s // c ≠ d} = s - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
    rw [hcard]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := s - 2) fun i hi => ?_) (by omega)
    rw [mem_range] at hi
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have hP0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun c : {c : Fin s // c ≠ d} => yN ivQ c.1 d)
    (fun a b h => Subtype.ext (yN_inj d a.1 b.1 a.2 b.2 h)) hroot hdeg
  intro i hi
  have hc := congrArg (fun p => Polynomial.coeff p i) hP0
  simp only [hP, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg (Ne.symm hb)]) (by simp; omega),
    if_pos rfl] at hc
  linarith

end

end Z3NetU.Proofs

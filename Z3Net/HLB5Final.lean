module
public import Mathlib
public import Z3Net.HLB5Sound
public import Z3Net.HLB5Check

@[expose] public section

/-!
# Entry HL, part 13: the `s = 5` headline `δ N^(1/5) ≥ 1.02652 > 1.0265`, every prime `q ≥ 1511`,
every `k ≥ 1`

`HL_relax` (with `B5_design`, admissibility for `q ∉ {2,3,5,7,97,101}`) gives either the far case
`D² ≥ 4 q^(8k)` or a configuration `(E, J, Δ)` with `J_d ≤ 3`; `cert_sound` (certificate
`check_all`) bounds the latter.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

lemma notbad_of_ge (q : ℕ) (hq : 1511 ≤ q) : q ∉ ({2, 3, 5, 7, 97, 101} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]; omega

theorem B5_sep (q k : ℕ) (hq : q.Prime) (hq1511 : 1511 ≤ q) (hk : 1 ≤ k)
    (x y : Fin (5 * k) → ZMod q) (hxy : x ≠ y) :
    (102652 : ℤ) ^ 2 * (q : ℤ) ^ (2 * (5 * k - k)) ≤
      100000 ^ 2 * (torusDist2 (q ^ (5 * k)) (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 x)
        (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 y) : ℤ) := by
  have hbad := notbad_of_ge q hq1511
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hqodd' : Odd (q : ℤ) := by obtain ⟨t, ht⟩ := hqodd; exact ⟨t, by rw [ht]; push_cast; ring⟩
  have hM : (q : ℤ) ^ (2 * (5 * k - k)) = (q : ℤ) ^ (2 * (5 * k - k - 1)) * (q : ℤ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rcases HL_relax 5 q k uB5 vB5 lamB5 gcoB5 dgB5 F2B5 (by norm_num) (adm_B5 q hq hbad)
      (den_B5 q hq hbad) (by omega) B5_design hk x y hxy with hfar | ⟨E, J, Δ, hE, hne, hJ, hdvd, hΔ, hbd⟩
  · have h0 : (0 : ℤ) ≤ (q : ℤ) ^ (2 * (5 * k - k)) := by positivity
    nlinarith
  · have hJ3 : ∀ c, J c ≤ 3 := fun c => by have := hJ c; omega
    have hc := cert_sound check_all (q : ℤ) (by exact_mod_cast hq1511) hqodd' E J Δ hE hne hJ3 hdvd hΔ
    have hP : (0 : ℤ) ≤ (q : ℤ) ^ (2 * (5 * k - k - 1)) := by positivity
    rw [hM]
    calc (102652 : ℤ) ^ 2 * ((q : ℤ) ^ (2 * (5 * k - k - 1)) * (q : ℤ) ^ 2)
        = (q : ℤ) ^ (2 * (5 * k - k - 1)) * (102652 ^ 2 * (q : ℤ) ^ 2) := by ring
      _ ≤ (q : ℤ) ^ (2 * (5 * k - k - 1)) * (100000 ^ 2 * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2) :=
          mul_le_mul_of_nonneg_left hc hP
      _ = 100000 ^ 2 * ((q : ℤ) ^ (2 * (5 * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbd (by norm_num)

theorem B5_sep_real (q k : ℕ) (hq : q.Prime) (hq1511 : 1511 ≤ q) (hk : 1 ≤ k)
    (x y : Fin (5 * k) → ZMod q) (hxy : x ≠ y) :
    1.0265 * ((q : ℝ) ^ (5 * k)) ^ (-(1 / (5 : ℝ)))
      < Real.sqrt (∑ c, ((cres (q ^ (5 * k))
          ((HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 x c : ℤ) -
            (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 y c : ℤ)) : ℝ) / (q : ℝ) ^ (5 * k)) ^ 2) := by
  have hZ := B5_sep q k hq hq1511 hk x y hxy
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set S : ℝ := ∑ c, ((cres (q ^ (5 * k))
      ((HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 x c : ℤ) -
        (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 y c : ℤ)) : ℝ)) ^ 2 with hS
  have hR : (102652 : ℝ) ^ 2 * (q : ℝ) ^ (2 * (5 * k - k)) ≤ 100000 ^ 2 * S := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this
    rw [torusDist2] at this
    push_cast at this
    rw [hS]
    convert this using 1 <;> norm_num
  have hsum : ∑ c, ((cres (q ^ (5 * k))
      ((HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 x c : ℤ) -
        (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 y c : ℤ)) : ℝ) / (q : ℝ) ^ (5 * k)) ^ 2 =
      S / ((q : ℝ) ^ (5 * k)) ^ 2 := by
    rw [hS, Finset.sum_div]; refine Finset.sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum]
  have hrp : ((q : ℝ) ^ (5 * k)) ^ (-(1 / (5 : ℝ))) = 1 / (q : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, show ((5 * k : ℕ) : ℝ) * (-(1 / (5 : ℝ))) =
      -(k : ℝ) by push_cast; ring, Real.rpow_neg hq0.le, Real.rpow_natCast, one_div]
  rw [hrp]
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hlt : 1.0265 * (1 / (q : ℝ) ^ k) < 1.02652 * (1 / (q : ℝ) ^ k) := by
    apply mul_lt_mul_of_pos_right (by norm_num) (by positivity)
  refine lt_of_lt_of_le hlt (Real.le_sqrt_of_sq_le ?_)
  have eN : ((q : ℝ) ^ (5 * k)) = (q : ℝ) ^ (5 * k - k) * (q : ℝ) ^ k := by
    rw [← pow_add]; congr 1; omega
  have eP : (q : ℝ) ^ (2 * (5 * k - k)) = ((q : ℝ) ^ (5 * k - k)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [eP] at hR
  rw [eN, le_div_iff₀ (by positivity)]
  have : (1.02652 * (1 / (q : ℝ) ^ k)) ^ 2 * ((q : ℝ) ^ (5 * k - k) * (q : ℝ) ^ k) ^ 2 =
      (1.02652 : ℝ) ^ 2 * ((q : ℝ) ^ (5 * k - k)) ^ 2 := by
    field_simp
  rw [this]
  nlinarith

end

end Z3NetHL.Proofs

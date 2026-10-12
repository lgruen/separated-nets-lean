module
public import Mathlib
public import Z3Net.S1Sep
public import Z3Net.S1Net3

@[expose] public section

/-!
# Entry S1, part 6: real forms, constants, headline (`S1_sep_real`, `S1_const`, `S1_main`)
-/

namespace Z3NetS1.Proofs

open Finset

/-- **Theorem S1, separation (real form).** -/
theorem S1_sep_real (s p k ρ : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k ρ C) (v w : Fin (s * k + (s - 1)) → ZMod p) (hvw : v ≠ w) :
    ((ρ : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 1)))
          ((digPoint p (s * k + (s - 1)) C v c : ℤ) - (digPoint p (s * k + (s - 1)) C w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (s * k + (s - 1))) ^ 2) := by
  have hZ := S1_sep s p k ρ hs hp hρ hρp C hC v w hvw
  unfold torusDist2 at hZ
  set S : ℝ := ∑ c, ((cres (p ^ (s * k + (s - 1))) ((digPoint p (s * k + (s - 1)) C v c : ℤ) - (digPoint p (s * k + (s - 1)) C w c : ℤ)) : ℝ)) ^ 2
    with hS
  have hR : ((ρ - 1 : ℕ) : ℝ) ^ 2 * (p : ℝ) ^ (2 * ((s - 1) * (k + 1) - 1)) ≤ S := by
    have := (Nat.cast_le (α := ℝ)).mpr hZ
    push_cast at this
    rw [hS]; exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs0 : (s : ℝ) ≠ 0 := by
    have h0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    exact h0.ne'
  have hm1 : (s * k + (s - 1)) + 1 = s * (k + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have hrp : (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ))) = 1 / (p : ℝ) ^ (k + 1) := by
    rw [← Real.mul_rpow hp0.le (by positivity), ← pow_succ', hm1, ← Real.rpow_natCast,
      ← Real.rpow_mul hp0.le, show ((s * (k + 1) : ℕ) : ℝ) * (-(1 / (s : ℝ))) = -((k + 1 : ℕ) : ℝ) by
        push_cast; field_simp, Real.rpow_neg hp0.le, Real.rpow_natCast, one_div]
  have hsum : ∑ c, ((cres (p ^ (s * k + (s - 1))) ((digPoint p (s * k + (s - 1)) C v c : ℤ) - (digPoint p (s * k + (s - 1)) C w c : ℤ)) : ℝ)
      / (p : ℝ) ^ (s * k + (s - 1))) ^ 2 = S / ((p : ℝ) ^ (s * k + (s - 1))) ^ 2 := by
    rw [hS, Finset.sum_div]; refine Finset.sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum, mul_assoc, hrp]
  apply Real.le_sqrt_of_sq_le
  have hρ1 : ((ρ - 1 : ℕ) : ℝ) = (ρ : ℝ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ ρ)]; ring
  rw [← hρ1]
  have hpk : (0 : ℝ) < (p : ℝ) ^ (k + 1) := by positivity
  rw [mul_one_div, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmk : (s * k + (s - 1)) = ((s - 1) * (k + 1) - 1) + (k + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have e1 : (t + 1) * k = t * k + k := by ring
    have e2 : t * (k + 1) = t * k + t := by ring
    have : 1 ≤ t * (k + 1) := by nlinarith
    omega
  have e1 : ((p : ℝ) ^ (s * k + (s - 1))) ^ 2 = (p : ℝ) ^ (2 * ((s - 1) * (k + 1) - 1)) * ((p : ℝ) ^ (k + 1)) ^ 2 := by
    rw [hmk, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  rw [e1]
  have hk2 : (0 : ℝ) ≤ ((p : ℝ) ^ (k + 1)) ^ 2 := by positivity
  calc ((ρ - 1 : ℕ) : ℝ) ^ 2 * ((p : ℝ) ^ (2 * ((s - 1) * (k + 1) - 1)) * ((p : ℝ) ^ (k + 1)) ^ 2)
      = (((ρ - 1 : ℕ) : ℝ) ^ 2 * (p : ℝ) ^ (2 * ((s - 1) * (k + 1) - 1))) * ((p : ℝ) ^ (k + 1)) ^ 2 := by
        ring
    _ ≤ S * ((p : ℝ) ^ (k + 1)) ^ 2 := mul_le_mul_of_nonneg_right hR hk2

/-! ## Constants -/

theorem S1_const (s p : ℕ) (hs : 2 ≤ s) (hp : p.Prime) (hps : 2 ^ s < p) :
    2 ≤ rhoS s p ∧ rhoS s p ^ s < p ∧ p < (rhoS s p + 1) ^ s ∧
      ((rhoS s p : ℝ) - 1) / ((rhoS s p : ℝ) + 1) < ((rhoS s p : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) ∧
      (1 : ℝ) / 3 ≤ ((rhoS s p : ℝ) - 1) / ((rhoS s p : ℝ) + 1) ∧
      (3 ^ s < p → (1 : ℝ) / 2 ≤ ((rhoS s p : ℝ) - 1) / ((rhoS s p : ℝ) + 1)) := by
  set ρ := rhoS s p with hρdef
  have h2p : 2 ≤ p := by
    have : 2 ≤ 2 ^ s := Nat.le_self_pow (by omega) 2
    omega
  have hρ2 : 2 ≤ ρ := Nat.le_findGreatest h2p hps
  have hρs : ρ ^ s < p := Nat.findGreatest_spec (P := fun ρ => ρ ^ s < p) h2p hps
  have hρlt : ρ < p := lt_of_le_of_lt (Nat.le_self_pow (by omega) ρ) hρs
  have hge : p ≤ (ρ + 1) ^ s := by
    have := Nat.findGreatest_is_greatest (P := fun ρ => ρ ^ s < p) (Nat.lt_succ_self ρ) hρlt
    simpa using this
  have hne : p ≠ (ρ + 1) ^ s := by
    intro h
    have hd : ρ + 1 ∣ p := by rw [h]; exact dvd_pow_self _ (by omega)
    rcases (Nat.dvd_prime hp).mp hd with h1 | h1
    · omega
    · rw [← h1] at h
      have : (ρ + 1) ^ 1 < (ρ + 1) ^ s := Nat.pow_lt_pow_right (by omega) (by omega)
      rw [pow_one] at this; omega
  have hlt : p < (ρ + 1) ^ s := lt_of_le_of_ne hge hne
  refine ⟨hρ2, hρs, hlt, ?_, ?_, ?_⟩
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    have hroot : (p : ℝ) ^ (1 / (s : ℝ)) < (ρ : ℝ) + 1 := by
      have h1 : (p : ℝ) < ((ρ : ℝ) + 1) ^ s := by exact_mod_cast hlt
      have h2 := Real.rpow_lt_rpow hp0.le h1 (by positivity : (0 : ℝ) < 1 / (s : ℝ))
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((s : ℕ) : ℝ) * (1 / (s : ℝ)) = 1 by field_simp, Real.rpow_one] at h2
    have hpos : (0 : ℝ) < (p : ℝ) ^ (1 / (s : ℝ)) := by positivity
    rw [Real.rpow_neg hp0.le, ← div_eq_mul_inv]
    have hρ1 : (0 : ℝ) < (ρ : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ2
      linarith
    exact div_lt_div_of_pos_left hρ1 hpos hroot
  · have : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ2
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  · intro h3
    have h3p : 3 ≤ p := by
      have : 3 ≤ 3 ^ s := Nat.le_self_pow (by omega) 3
      omega
    have hρ3 : 3 ≤ ρ := Nat.le_findGreatest h3p h3
    have : (3 : ℝ) ≤ ρ := by exact_mod_cast hρ3
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith

/-- **Theorem S1 (headline).** -/
theorem S1_main (s p k : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hps : 2 ^ s < p) :
    ∃ C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p),
      IsS1skel s p k (rhoS s p) C ∧ IsNet0 s p (s * k + (s - 1)) (digPoint p (s * k + (s - 1)) C) ∧
      ∀ v w : Fin (s * k + (s - 1)) → ZMod p, v ≠ w →
        (1 : ℝ) / 3 * ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ)))
          < Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 1)))
              ((digPoint p (s * k + (s - 1)) C v c : ℤ) - (digPoint p (s * k + (s - 1)) C w c : ℤ)) : ℝ)
              / (p : ℝ) ^ (s * k + (s - 1))) ^ 2) := by
  obtain ⟨hρ2, hρs, -, hc, h3, -⟩ := S1_const s p (by omega) hp hps
  obtain ⟨C, hC, hnet⟩ := S1_net s p k (rhoS s p) hs hp hρ2 hρs
  refine ⟨C, hC, hnet, fun v w hvw => ?_⟩
  have hsep := S1_sep_real s p k (rhoS s p) hs hp hρ2 hρs C hC v w hvw
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : (0 : ℝ) < ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ))) := by positivity
  refine lt_of_lt_of_le ?_ hsep
  exact mul_lt_mul_of_pos_right (lt_of_le_of_lt h3 hc) hN

end Z3NetS1.Proofs

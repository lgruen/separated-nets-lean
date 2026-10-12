/-
Development module (Solution side) for `cor:dim4` (entry S2). Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkD4Cover
public import Z3Net.D4Main
public import Z3Net.S1Main

@[expose] public section

/-!
# `cor:dim4`, the residues `m ≢ 1 (mod 4)`, from the `thm:S2`(1) hypotheses

`dim4_of` proves the statement of `cor:dim4` (Challenge `dim4`) for a prime `23 ≤ p ≤ 83` from the
two `s = 4` parts of `thm:S2`(1) (net and real-form separation, as hypotheses for this `p`):

* `m ≡ 0`, `m ≥ 8`: the net of `thm:4D` (`Z3NetD4.D4_net`, `D4_sep_real`, `D4_covering`),
  separation constant `c₄(p) ≥ 1/√31`, covering `h N^(1/4) ≤ 2`;
* `m ≡ 3`, `m ≥ 3`: `thm:S1` at `s = 4` with `ρ = ρ₄(p) ∈ {2, 3}` (`Z3NetS1.S1_net`,
  `S1_sep_real`, `S1_cover`), constant `(ρ - 1) p^(-1/4) ≥ 83^(-1/4) > 1/4 > 1/√31`, covering
  `h N^(1/4) < 2 (μ + 1) p^(-1/4)`;
* `m ≡ 2`, `m ≥ 6`: `thm:S2`(1), constant `(ρ - 4) p^(-1/2)` with `ρ = rhoT p`, which is
  `≥ 1/√31` iff `p ≤ 31 (ρ - 4)²` (checked by `decide` for `23 ≤ p ≤ 83`, `p ≠ 32`; equality at
  `p = 31`, `ρ = 5`), covering `h N^(1/4) ≤ 2 √p` (elementary box, `SkD4.cover_4k2`).

The covering constant is `C_p = max(2 √p, 2 (μ + 1) p^(-1/4))`, `μ = ⌈p/ρ₄(p)³⌉`.
-/

namespace Z3NetF.Proofs

namespace SkD4

open Finset

/-! ## Bridges between the namespace copies -/

theorem isNet0_of_D4 {q m : ℕ} {X : (Fin m → ZMod q) → Fin 4 → ℕ} (h : Z3NetD4.IsNet0 q m X) :
    IsNet0 4 q m X := by
  intro d hd a ha
  exact h d (by simpa [Fin.sum_univ_four] using hd) a ha

theorem isNet0_of_S1 {s q m : ℕ} {X : (Fin m → ZMod q) → Fin s → ℕ}
    (h : Z3NetS1.IsNet0 s q m X) : IsNet0 s q m X := h

/-! ## The constants -/

/-- `rhoT p ≥ 5` and `p ≤ 31 (rhoT p - 4)²` for `23 ≤ p ≤ 83`, `p ≠ 32` (finite check). -/
theorem rhoT_tab : ∀ p < 84, 23 ≤ p → p ≠ 32 → 5 ≤ rhoT p ∧ p ≤ 31 * (rhoT p - 4) ^ 2 := by
  decide

theorem one_div_sqrt31_le_quarter : 1 / Real.sqrt 31 ≤ 1 / 4 := by
  have : (4 : ℝ) ≤ Real.sqrt 31 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  exact one_div_le_one_div_of_le (by norm_num) this

/-- `thm:4D`: `c₄(p) ≥ 1/√31` for `p ≥ 23`. -/
theorem c4_ge (p : ℕ) (h23 : 23 ≤ p) : 1 / Real.sqrt 31 ≤ Z3NetD4.c4 p := by
  have hK : Z3NetD4.K4 p = ((p : ℤ) - 5) ^ 2 + 4 := by
    unfold Z3NetD4.K4; simp [show p ≠ 5 by omega, show p ≠ 7 by omega]
  have hp : (23 : ℝ) ≤ p := by exact_mod_cast h23
  unfold Z3NetD4.c4
  rw [hK]; push_cast
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by norm_num)) (by linarith), one_mul,
    ← Real.sqrt_mul (by positivity)]
  rw [Real.le_sqrt (by linarith) (by positivity)]
  nlinarith

/-- `thm:S1` at `s = 4`: `(ρ - 1) p^(-1/4) ≥ 1/√31` for `ρ ≥ 2`, `p ≤ 256`. -/
theorem S1const_ge (p ρ : ℕ) (hp1 : 1 ≤ p) (hp : p ≤ 256) (hρ : 2 ≤ ρ) :
    1 / Real.sqrt 31 ≤ ((ρ : ℝ) - 1) * (p : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have hρ' : (1 : ℝ) ≤ (ρ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
    linarith
  have h4 : (p : ℝ) ^ (1 / 4 : ℝ) ≤ 4 := by
    have h256 : (p : ℝ) ≤ (4 : ℝ) ^ (4 : ℝ) := by
      norm_num; exact_mod_cast hp
    calc (p : ℝ) ^ (1 / 4 : ℝ) ≤ ((4 : ℝ) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hp0.le h256 (by norm_num)
      _ = 4 := by rw [← Real.rpow_mul (by norm_num)]; norm_num
  have hq : (1 / 4 : ℝ) ≤ (p : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg hp0.le]
    calc (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := inv_anti₀ (Real.rpow_pos_of_pos hp0 _) h4
  calc 1 / Real.sqrt 31 ≤ 1 / 4 := one_div_sqrt31_le_quarter
    _ ≤ (p : ℝ) ^ (-(1 / 4 : ℝ)) := hq
    _ = 1 * (p : ℝ) ^ (-(1 / 4 : ℝ)) := (one_mul _).symm
    _ ≤ ((ρ : ℝ) - 1) * (p : ℝ) ^ (-(1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right hρ' (Real.rpow_nonneg hp0.le _)

/-- `thm:S2`(1): `(rhoT p - 4) p^(-1/2) ≥ 1/√31` for primes `23 ≤ p ≤ 83` (equality at `p = 31`). -/
theorem S2const_ge (p : ℕ) (hpp : p.Prime) (h23 : 23 ≤ p) (h83 : p ≤ 83) :
    1 / Real.sqrt 31 ≤ ((rhoT p : ℝ) - 4) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have h32 : p ≠ 32 := by rintro rfl; norm_num at hpp
  obtain ⟨h5, hle⟩ := rhoT_tab p (by omega) h23 h32
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set a : ℝ := (rhoT p : ℝ) - 4 with ha
  have ha1 : (1 : ℝ) ≤ a := by
    have : (5 : ℝ) ≤ rhoT p := by exact_mod_cast h5
    linarith
  have hle' : (p : ℝ) ≤ 31 * a ^ 2 := by
    have : ((rhoT p - 4 : ℕ) : ℝ) = a := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← this]; exact_mod_cast hle
  rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv,
    div_le_div_iff₀ (Real.sqrt_pos.2 (by norm_num)) (Real.sqrt_pos.2 hp0), one_mul]
  calc Real.sqrt p ≤ Real.sqrt (a ^ 2 * 31) := Real.sqrt_le_sqrt (by linarith)
    _ = a * Real.sqrt 31 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]

/-! ## `cor:dim4` from the `thm:S2`(1) hypotheses -/

/-- **`cor:dim4`** (residues `m ≢ 1 (mod 4)`) for one prime `23 ≤ p ≤ 83`, from the net and
separation parts of `thm:S2`(1) at this `p` (`S2_net4`, `S2_sep4_real`). -/
theorem dim4_of (p : ℕ) [Fact p.Prime] (h23 : 23 ≤ p) (h83 : p ≤ 83)
    (h_net4 : ∀ k : ℕ, 1 ≤ k →
      ∃ C : Fin 4 → Matrix (Fin (4 * k + 2)) (Fin (4 * k + 2)) (ZMod p),
        IsS2skel 4 p k {1} C ∧ IsNet0 4 p (4 * k + 2) (digPoint p (4 * k + 2) C))
    (h_sep4 : ∀ k : ℕ, 1 ≤ k →
      ∀ C : Fin 4 → Matrix (Fin (4 * k + 2)) (Fin (4 * k + 2)) (ZMod p), IsS2skel 4 p k {1} C →
      ∀ v w : Fin (4 * k + 2) → ZMod p, v ≠ w →
        ((rhoT p : ℝ) - 4) * (p : ℝ) ^ (-(1 / 2 : ℝ)) * ((p : ℝ) ^ (4 * k + 2)) ^ (-(1 / 4 : ℝ))
          ≤ Real.sqrt (∑ c, ((cres (p ^ (4 * k + 2))
              ((digPoint p (4 * k + 2) C v c : ℤ) - (digPoint p (4 * k + 2) C w c : ℤ)) : ℝ)
              / (p : ℝ) ^ (4 * k + 2)) ^ 2)) :
    ∃ Cp : ℝ, ∀ m : ℕ, 3 ≤ m → m ≠ 4 → m % 4 ≠ 1 →
      ∃ C : Fin 4 → Matrix (Fin m) (Fin m) (ZMod p), IsNet0 4 p m (digPoint p m C) ∧
        (∀ v w : Fin m → ZMod p, v ≠ w →
          1 / Real.sqrt 31 * ((p : ℝ) ^ m) ^ (-(1 / 4 : ℝ)) ≤
            Real.sqrt (∑ c, ((cres (p ^ m) ((digPoint p m C v c : ℤ) - (digPoint p m C w c : ℤ)) : ℝ)
              / (p : ℝ) ^ m) ^ 2)) ∧
        ∀ y : Fin 4 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin m → ZMod p,
          Real.sqrt (∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
            Cp * ((p : ℝ) ^ m) ^ (-(1 / 4 : ℝ)) := by
  have hpp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  have hsq1 : (1 : ℝ) ≤ Real.sqrt p := by rw [Real.le_sqrt (by norm_num) hp0.le]; simpa using hp1
  obtain ⟨hρ2, hρp, -, -, -, -⟩ := Z3NetS1.S1_const 4 p (by norm_num) hpp (by norm_num; omega)
  set ρ := Z3NetS1.rhoS 4 p with hρ
  set μ := Z3NetS1.muS 4 p ρ with hμ
  refine ⟨max (2 * Real.sqrt p) (2 * ((μ : ℝ) + 1) * (p : ℝ) ^ (-(1 / 4 : ℝ))), ?_⟩
  intro m hm3 hm4 hm1
  have hcase : m % 4 = 0 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases hcase with h0 | h2 | h3
  · -- `m ≡ 0`: `thm:4D`
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k := ⟨m / 4, by omega⟩
    have hk : 2 ≤ k := by omega
    have hodd : Odd p := hpp.odd_of_ne_two (by omega)
    refine ⟨Z3NetD4.D4Gen p k, isNet0_of_D4 (Z3NetD4.D4_net p k hodd hk), ?_, ?_⟩
    · intro v w hvw
      have h := Z3NetD4.D4_sep_real p k hodd (by omega) hk v w hvw
      exact le_trans (mul_le_mul_of_nonneg_right (c4_ge p h23) (by positivity)) h
    · intro y hy
      obtain ⟨v, hv⟩ := Z3NetD4.D4_covering p k (by omega) hk y (fun c => ⟨(hy c).1, (hy c).2.le⟩)
      refine ⟨v, ?_⟩
      rw [quarter_4k _ hp0]
      have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hp0 _
      calc Real.sqrt _ ≤ Real.sqrt (4 / ((p : ℝ) ^ k) ^ 2) := Real.sqrt_le_sqrt hv
        _ = 2 * ((p : ℝ) ^ k)⁻¹ := by
            rw [show (4 : ℝ) / ((p : ℝ) ^ k) ^ 2 = (2 * ((p : ℝ) ^ k)⁻¹) ^ 2 by field_simp; norm_num,
              Real.sqrt_sq (by positivity)]
        _ ≤ _ := mul_le_mul_of_nonneg_right
            ((by linarith : (2 : ℝ) ≤ 2 * Real.sqrt p).trans (le_max_left _ _)) (by positivity)
  · -- `m ≡ 2`: `thm:S2`(1)
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 2 := ⟨m / 4, by omega⟩
    have hk : 1 ≤ k := by omega
    obtain ⟨C, hC, hnet⟩ := h_net4 k hk
    refine ⟨C, hnet, ?_, ?_⟩
    · intro v w hvw
      exact le_trans (mul_le_mul_of_nonneg_right (S2const_ge p hpp h23 h83) (by positivity))
        (h_sep4 k hk C hC v w hvw)
    · intro y hy
      obtain ⟨v, hv⟩ := cover_4k2 hpp.one_lt.le (digPoint p (4 * k + 2) C) hnet y hy
      exact ⟨v, hv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  · -- `m ≡ 3`: `thm:S1` at `s = 4`
    obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + (4 - 1) := ⟨m / 4, by omega⟩
    obtain ⟨C, hC, hnet⟩ := Z3NetS1.S1_net 4 p k ρ (by norm_num) hpp hρ2 hρp
    refine ⟨C, isNet0_of_S1 hnet, ?_, ?_⟩
    · intro v w hvw
      have h := Z3NetS1.S1_sep_real 4 p k ρ (by norm_num) hpp hρ2 hρp C hC v w hvw
      simp only [Nat.cast_ofNat] at h
      exact le_trans (mul_le_mul_of_nonneg_right (S1const_ge p ρ hpp.one_lt.le (by omega) hρ2)
        (by positivity)) h
    · intro y hy
      obtain ⟨v, hv⟩ := Z3NetS1.S1_cover 4 p k (by norm_num) hpp (by norm_num; omega) C hC y hy
      refine ⟨v, ?_⟩
      simp only [Nat.cast_ofNat] at hv
      rw [show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hv
      exact hv.le.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end SkD4

end Z3NetF.Proofs

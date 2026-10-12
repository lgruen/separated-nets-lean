/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.S1Shift
public import Z3Net.D3Allm

@[expose] public section

/-!
# V14 stage S10′: `thm:allm` and `rem:B2` under digital shifts (`prop:shift`)

The proof of `thm:allm` (`B1_sep`) uses the fine positions only through the residues of their last
two digits (the carry analysis `carry`, the skeleton relations) and the fact that equal fine positions
give equal indices. With the shifted fine positions `Pf k 1 (C_c v + τ_c)` the transfer lemmas of
`Z3Net/S1Shift.lean` (`PfSh_mod`, `PfSh_div`, `PfSh_inj`) give exactly the same residues and the same
injectivity, and Lemma T (`prefix_bound`) applies with the identity matrix (`shift_coord`); so the
bound holds verbatim for every digitally shifted net (`B1_sep_shift_core`, `B1_sep_shift_real_core`).
`rem:B2` is `thm:S1` at `s = 3` (`B2_skel_iff`), so its shifted form follows from
`Z3NetS1.Proofs.S1_sep_shift_core` (`B2_rem_sep_shift_core`, `B2_rem_sep_shift_real_core`).
-/

namespace Z3NetKN.Proofs

open Finset Matrix Z3NetKN.Relax Z3NetKN.Geom

/-- **`prop:shift`, `thm:allm`, integer form**: the bound of `B1_sep` holds for every digitally
shifted net with skeleton rows `skB1 ρ`. -/
theorem B1_sep_shift_core (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 2 ≤ ρ)
    (hρp : ρ ^ 2 * (ρ + 1) ≤ p)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p))
    (hC : IsKNskel 1 p k (skB1 ρ) C) (τ : Fin 3 → Fin (3 * k + 1) → ZMod p) (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    (ρ ^ 2 - 4) ^ 2 * p ^ (4 * k) ≤
      torusDist2 (p ^ (3 * k + 1)) (Z3NetF.digPointShift p (3 * k + 1) C τ v)
        (Z3NetF.digPointShift p (3 * k + 1) C τ w) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hr : (1 = 1 ∨ 1 = 2) := Or.inl rfl
  have hp2 := hp.two_le
  set a : Fin 3 → ℤ := fun c => cen (p ^ (k + 1)) ((Pf k (1 : Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (C c *ᵥ v + τ c) : ℤ) -
    Pf k (1 : Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (C c *ᵥ w + τ c)) with ha
  have hρ' : (2 : ℤ) ≤ ρ := by exact_mod_cast hρ
  have hρp' : (ρ : ℤ) ^ 2 * (ρ + 1) ≤ p := by exact_mod_cast hρp
  have hρ2p : (ρ : ℤ) ^ 2 + 2 ≤ p := by nlinarith
  have key : ∃ c, (ρ : ℤ) ^ 2 - 3 ≤ |a c| := by
    by_contra hcon
    push_neg at hcon
    have hsmall : ∀ c, |a c| < p := fun c => by have := hcon c; omega
    have hcar : ∀ c : Fin 3, ∃ ch, ch < min (k + 1) 2 ∧ (a c = 0 → ch = 0) ∧ ∀ i < min (k + 1) 2,
        ((Pf k (1 : Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (C c *ᵥ v + τ c) / p ^ i % p : ℕ) : ZMod p) -
          ((Pf k (1 : Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (C c *ᵥ w + τ c) / p ^ i % p : ℕ) : ZMod p) =
          ((pat (a c) ch i : ℤ) : ZMod p) := by
      intro c
      obtain ⟨z, hz⟩ := cen_spec (p ^ (k + 1)) ((Pf k (1 : Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (C c *ᵥ v + τ c) : ℤ) -
        Pf k (1 : Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (C c *ᵥ w + τ c))
      exact carry p (k + 1) 2 (by omega) (by omega) (by norm_num) (by norm_num) _ _
        (Pf_lt _ _) (Pf_lt _ _) (a c) z (hsmall c) hz
    choose ch hch1 hch0 hchD using hcar
    set ξ : Fin 3 → ℤ := fun c => pat (a c) (ch c) 1 with hξ
    have d0 : ∀ c, ((a c : ℤ) : ZMod p) =
        ((Pf k (C c) v % p : ℕ) : ZMod p) - ((Pf k (C c) w % p : ℕ) : ZMod p) :=
      fun c => (cen_cast_mod (k + 1) _ _ (by omega)).trans (PfSh_mod (C c) (τ c) v w)
    have d1 : ∀ c, ((ξ c : ℤ) : ZMod p) = vz v (off 1 k c + (k - 1)) - vz w (off 1 k c + (k - 1)) := by
      intro c
      have := hchD c 1 (by omega)
      rw [pow_one, PfSh_div hk (C c) (τ c) v w, Pf_div hr hC hk v c, Pf_div hr hC hk w c] at this
      exact this.symm
    have hY : ((a 1 : ℤ) : ZMod p) = (ρ : ZMod p) * ((a 0 : ℤ) : ZMod p) + ((ξ 2 : ℤ) : ZMod p) := by
      rw [d0 1, d0 0, d1 2, Pf_mod_skel hr hC v 1 (by simp), Pf_mod_skel hr hC w 1 (by simp),
        Pf_mod_full hr hC v 0 (by simp), Pf_mod_full hr hC w 0 (by simp),
        skel_diff hr hC v w 1 (by simp), Fin.sum_univ_three]
      have h0 : skB1 ρ 1 0 = ![(ρ : ℤ), 0, 0, 0] := rfl
      have h1 : skB1 ρ 1 1 = 0 := rfl
      have h2 : skB1 ρ 1 2 = ![(1 : ℤ), 0, 0, 0] := rfl
      rw [h0, h1, h2, win_sum_single _ _ _ (by simp [win]) (by simp [depth]), win_sum_zero,
        win_sum_single _ _ _ (by simp [win]) (by simp [depth]; omega)]
      have e0 : depth 1 k 0 - 1 = k := by simp [depth]
      have e2 : depth 1 k 2 - 1 = k - 1 := by simp [depth]
      rw [e0, e2]
      push_cast; ring
    have hZ : ((a 2 : ℤ) : ZMod p) = (ρ : ZMod p) ^ 2 * ((a 0 : ℤ) : ZMod p) + ((ξ 0 : ℤ) : ZMod p) +
        ((ξ 1 : ℤ) : ZMod p) - ((ξ 2 : ℤ) : ZMod p) := by
      rw [d0 2, d0 0, d1 0, d1 1, d1 2, Pf_mod_skel hr hC v 2 (by simp), Pf_mod_skel hr hC w 2 (by simp),
        Pf_mod_full hr hC v 0 (by simp), Pf_mod_full hr hC w 0 (by simp),
        skel_diff hr hC v w 2 (by simp), Fin.sum_univ_three]
      have h0 : skB1 ρ 2 0 = ![(ρ : ℤ) ^ 2, 1, 0, 0] := rfl
      have h1 : skB1 ρ 2 1 = ![(1 : ℤ), 0, 0, 0] := rfl
      have h2 : skB1 ρ 2 2 = ![(-1 : ℤ), 0, 0, 0] := rfl
      rw [h0, h1, h2, win_sum_two _ _ _ _ (by simp [win]) (by simp [depth]; omega),
        win_sum_single _ _ _ (by simp [win]) (by simp [depth]; omega),
        win_sum_single _ _ _ (by simp [win]) (by simp [depth]; omega)]
      have e0 : depth 1 k 0 - 1 = k := by simp [depth]
      have e0' : depth 1 k 0 - 2 = k - 1 := by simp [depth]
      have e1 : depth 1 k 1 - 1 = k - 1 := by simp [depth]
      have e2 : depth 1 k 2 - 1 = k - 1 := by simp [depth]
      rw [e0, e0', e1, e2]
      push_cast; ring
    have hdiv1 : (p : ℤ) ∣ (a 1 - ξ 2) - ρ * a 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hY]; ring
    have hdiv2 : (p : ℤ) ∣ (a 2 - ξ 0 - ξ 1 + ξ 2) - ρ ^ 2 * a 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hZ]; ring
    have hspec := fun c => pat1_spec (a c) (ch c) (hch0 c)
    have hξb : ∀ c, |ξ c| ≤ 1 := by
      intro c
      rcases hspec c with h | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [hξ, h] <;> norm_num
    have hab : ∀ c, |a c| ≤ (ρ : ℤ) ^ 2 - 4 := fun c => by have := hcon c; omega
    have hu0 : a 0 = 0 ∧ a 1 - ξ 2 = 0 ∧ a 2 - ξ 0 - ξ 1 + ξ 2 = 0 := by
      by_contra hne
      have := latL1 p ρ (by omega) hρp (a 0) (a 1 - ξ 2) (a 2 - ξ 0 - ξ 1 + ξ 2) ((ρ : ℤ) ^ 2 - 1)
        hdiv1 hdiv2
        (by have := hab 0; omega)
        (by have := hab 1; have := hξb 2
            have := abs_sub (a 1) (ξ 2); linarith)
        (by have := hab 2; have := hξb 0; have := hξb 1; have := hξb 2
            have t1 := abs_add_le (a 2 - ξ 0 - ξ 1) (ξ 2)
            have t2 := abs_sub (a 2 - ξ 0) (ξ 1)
            have t3 := abs_sub (a 2) (ξ 0)
            linarith) hne
      linarith
    obtain ⟨u0, u1, u2⟩ := hu0
    have ξ0 : ξ 0 = 0 := by simp only [hξ, pat]; rw [hch0 0 u0]; simp
    rw [ξ0] at u2
    have hall : a 1 = 0 ∧ a 2 = 0 := by
      rcases hspec 2 with h | ⟨h, hpos⟩ | ⟨h, hneg⟩
      · have h' : ξ 2 = 0 := h
        have a1 : a 1 = 0 := by linarith
        have ξ1 : ξ 1 = 0 := by simp only [hξ, pat]; rw [hch0 1 a1]; simp
        exact ⟨a1, by linarith⟩
      · exfalso
        have h' : ξ 2 = 1 := h
        rcases hspec 1 with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · have : ξ 1 = 0 := h1; linarith
        · have : ξ 1 = 1 := h1; linarith
        · have : ξ 1 = -1 := h1; linarith
      · exfalso
        have h' : ξ 2 = -1 := h
        rcases hspec 1 with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · have : ξ 1 = 0 := h1; linarith
        · have : ξ 1 = 1 := h1; linarith
        · have : ξ 1 = -1 := h1; linarith
    apply hvw
    refine eq_of_Pf_eq hr hC v w fun c =>
      PfSh_inj (C c) (τ c) v w (eq_of_cen_zero _ _ _ (Pf_lt _ _) (Pf_lt _ _) ?_)
    fin_cases c
    exacts [u0, hall.1, hall.2]
  obtain ⟨c, hc⟩ := key
  have hb : |a c| * ((p ^ (3 * k + 1 - (k + 1)) : ℕ) : ℤ) - (((p ^ (3 * k + 1 - (k + 1)) : ℕ) : ℤ) - 1) ≤
      (cres (p ^ (3 * k + 1)) ((Z3NetF.digPointShift p (3 * k + 1) C τ v c : ℤ) -
        Z3NetF.digPointShift p (3 * k + 1) C τ w c) : ℤ) := by
    rw [shift_coord, shift_coord]
    exact prefix_bound (1 : Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (C c *ᵥ v + τ c) (C c *ᵥ w + τ c) (k + 1) (by omega)
  set f := p ^ (3 * k + 1 - (k + 1)) with hf
  set cr := cres (p ^ (3 * k + 1)) ((Z3NetF.digPointShift p (3 * k + 1) C τ v c : ℤ) -
    Z3NetF.digPointShift p (3 * k + 1) C τ w c)
  have h4 : 4 ≤ ρ ^ 2 := by nlinarith
  have h1 : (((ρ ^ 2 - 4) * f : ℕ) : ℤ) ≤ cr := by
    push_cast [Nat.cast_sub h4]
    have hf0 : (0 : ℤ) ≤ f := by positivity
    have := mul_le_mul_of_nonneg_right hc hf0
    linarith
  have h1' : (ρ ^ 2 - 4) * f ≤ cr := by exact_mod_cast h1
  calc (ρ ^ 2 - 4) ^ 2 * p ^ (4 * k) = ((ρ ^ 2 - 4) * f) ^ 2 := by
        rw [hf, mul_pow, ← pow_mul]; congr 2; omega
    _ ≤ cr ^ 2 := Nat.pow_le_pow_left h1' 2
    _ ≤ _ := cres_le_torus _ (Z3NetF.digPointShift p (3 * k + 1) C τ v)
        (Z3NetF.digPointShift p (3 * k + 1) C τ w) c


open Filter Topology D3

/-- **`prop:shift`, `thm:allm`, real form**: `δ ≥ (ρ² - 4) p^(-2/3) N^(-1/3)` for every digitally
shifted net with skeleton rows `skB1 ρ`. -/
theorem B1_sep_shift_real_core (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 2 ≤ ρ)
    (hρp : ρ ^ 2 * (ρ + 1) ≤ p)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p))
    (hC : IsKNskel 1 p k (skB1 ρ) C) (τ : Fin 3 → Fin (3 * k + 1) → ZMod p) (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    ((ρ : ℝ) ^ 2 - 4) * (p : ℝ) ^ (-(2 / (3 : ℝ))) * ((p : ℝ) ^ (3 * k + 1)) ^ (-(1 / (3 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k + 1))
          ((Z3NetF.digPointShift p (3 * k + 1) C τ v c : ℤ) - (Z3NetF.digPointShift p (3 * k + 1) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k + 1)) ^ 2) := by
  have hZ := B1_sep_shift_core p k ρ hp hk hρ hρp C hC τ v w hvw
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN : 0 < p ^ (3 * k + 1) := pow_pos hp.pos _
  have hs := sqrt_cres_sum (p ^ (3 * k + 1)) hN (Z3NetF.digPointShift p (3 * k + 1) C τ v)
    (Z3NetF.digPointShift p (3 * k + 1) C τ w)
  push_cast at hs
  rw [hs, mul_assoc, rpow_mix _ hp0,
    show -(2 / (3 : ℝ) + ((3 * k + 1 : ℕ) : ℝ) / 3) = -((k + 1 : ℕ) : ℝ) by push_cast; ring,
    rpow_neg_nat _ hp0, le_div_iff₀ (by positivity)]
  have h4 : (4 : ℝ) ≤ (ρ : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
    nlinarith
  have hcast : (((ρ ^ 2 - 4 : ℕ) : ℝ)) = (ρ : ℝ) ^ 2 - 4 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  have hZr : ((ρ : ℝ) ^ 2 - 4) ^ 2 * (p : ℝ) ^ (4 * k) ≤
      (torusDist2 (p ^ (3 * k + 1)) (Z3NetF.digPointShift p (3 * k + 1) C τ v) (Z3NetF.digPointShift p (3 * k + 1) C τ w) : ℝ) := by
    rw [← hcast]; exact_mod_cast hZ
  have hle : ((ρ : ℝ) ^ 2 - 4) * (p : ℝ) ^ (2 * k) ≤
      Real.sqrt (torusDist2 (p ^ (3 * k + 1)) (Z3NetF.digPointShift p (3 * k + 1) C τ v)
        (Z3NetF.digPointShift p (3 * k + 1) C τ w) : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    calc (((ρ : ℝ) ^ 2 - 4) * (p : ℝ) ^ (2 * k)) ^ 2
        = ((ρ : ℝ) ^ 2 - 4) ^ 2 * (p : ℝ) ^ (4 * k) := by ring
      _ ≤ _ := hZr
  calc ((ρ : ℝ) ^ 2 - 4) * ((p : ℝ) ^ (k + 1))⁻¹ * (p : ℝ) ^ (3 * k + 1)
      = ((ρ : ℝ) ^ 2 - 4) * (p : ℝ) ^ (2 * k) := by
        field_simp; ring
    _ ≤ _ := hle

/-- **`prop:shift`, `rem:B2` (`thm:S1` at `s = 3`), integer form**, for every digitally shifted net. -/
theorem B2_rem_sep_shift_core (p k ρ : ℕ) (hp : p.Prime) (hρ : 1 ≤ ρ) (hρp : ρ ^ 3 < p)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p))
    (hC : IsKNskel 2 p k (skB2 ρ) C) (τ : Fin 3 → Fin (3 * k + 2) → ZMod p) (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    (ρ - 1) ^ 2 * p ^ (4 * k + 2) ≤
      torusDist2 (p ^ (3 * k + 2)) (Z3NetF.digPointShift p (3 * k + 2) C τ v) (Z3NetF.digPointShift p (3 * k + 2) C τ w) := by
  rcases Nat.lt_or_ge ρ 2 with h | h
  · rw [show ρ - 1 = 0 by omega]; simp
  · have hS : Z3NetS1.IsS1skel 3 p k ρ C := (B2_skel_iff p k ρ C).2 hC
    have := Z3NetS1.Proofs.S1_sep_shift_core 3 p k ρ (le_refl 3) hp h hρp C hS τ v w hvw
    rw [show 2 * ((3 - 1) * (k + 1) - 1) = 4 * k + 2 by omega] at this
    exact this

/-- **`prop:shift`, `rem:B2` (`thm:S1` at `s = 3`), real form**, for every digitally shifted net. -/
theorem B2_rem_sep_shift_real_core (p k ρ : ℕ) (hp : p.Prime) (hρ : 1 ≤ ρ) (hρp : ρ ^ 3 < p)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p))
    (hC : IsKNskel 2 p k (skB2 ρ) C) (τ : Fin 3 → Fin (3 * k + 2) → ZMod p) (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    ((ρ : ℝ) - 1) * (p : ℝ) ^ (-(1 / (3 : ℝ))) * ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k + 2))
          ((Z3NetF.digPointShift p (3 * k + 2) C τ v c : ℤ) - (Z3NetF.digPointShift p (3 * k + 2) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k + 2)) ^ 2) := by
  rcases Nat.lt_or_ge ρ 2 with h | h
  · rw [show ρ = 1 by omega]; simp only [Nat.cast_one, sub_self, zero_mul]
    exact Real.sqrt_nonneg _
  · have hS : Z3NetS1.IsS1skel 3 p k ρ C := (B2_skel_iff p k ρ C).2 hC
    have := Z3NetS1.Proofs.S1_sep_shift_real_core 3 p k ρ (le_refl 3) hp h hρp C hS τ v w hvw
    simp only [Nat.cast_ofNat] at this
    exact this

end Z3NetKN.Proofs

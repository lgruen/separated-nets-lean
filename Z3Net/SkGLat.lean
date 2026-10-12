module
public import Mathlib
public import Z3Net.SkelDefs

@[expose] public section

/-!
# Entry Skel, `lem:skellat` (L1), (T): short vectors of the skeleton lattices

* `skellat_L1`: for `A = (ρ, ρ², …, ρ^ℓ)ᵀ` and `ρ^ℓ (ρ + 1) ≤ p`, every nonzero lattice vector has
  maximum norm at least `ρ^ℓ` (comparison of `z_{i+1}` with `ρ z_i`);
* `skellat_L1_attained`: the vector `(1, ρ, …, ρ^ℓ)`;
* `skellat_T`: for `A = [[ρ, 1], [1, ρ]]` and `ρ² - 4 < p`, the minimum is at least `ρ - 1`.
-/

namespace Z3NetF.Proofs

open Finset

namespace SkG

/-- A multiple of `p` of absolute value `< p` vanishes. -/
lemma eq_of_dvd_of_abs_lt {p a b : ℤ} (h : p ∣ a - b) (hab : |a - b| < p) : a = b :=
  sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd h hab)

end SkG

theorem skellat_L1 (ℓ p ρ : ℕ) (hρ : 2 ≤ ρ) (hp : ρ ^ ℓ * (ρ + 1) ≤ p) (x : ℤ) (z : Fin ℓ → ℤ)
    (hz : ∀ i : Fin ℓ, (p : ℤ) ∣ z i - (ρ : ℤ) ^ ((i : ℕ) + 1) * x) (hne : ¬(x = 0 ∧ z = 0)) :
    (ρ : ℤ) ^ ℓ ≤ |x| ∨ ∃ i, (ρ : ℤ) ^ ℓ ≤ |z i| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hzb⟩ := hcon
  have hρz : (2 : ℤ) ≤ ρ := by exact_mod_cast hρ
  have hpz : (ρ : ℤ) ^ ℓ * (ρ + 1) ≤ p := by exact_mod_cast hp
  set R : ℤ := (ρ : ℤ) ^ ℓ with hR
  have hx' : |x| ≤ R - 1 := by omega
  have hz' : ∀ i, |z i| ≤ R - 1 := fun i => by have := hzb i; omega
  -- exactness of the relations
  have key : ∀ a b : ℤ, |a| ≤ R - 1 → |b| ≤ R - 1 → (p : ℤ) ∣ a - ρ * b → a = ρ * b := by
    intro a b ha hb hd
    apply SkG.eq_of_dvd_of_abs_lt hd
    have h1 : |a - ρ * b| ≤ |a| + ρ * |b| := by
      calc |a - ρ * b| ≤ |a| + |ρ * b| := abs_sub _ _
        _ = |a| + ρ * |b| := by rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ ρ)]
    have h2 : ρ * |b| ≤ ρ * (R - 1) := mul_le_mul_of_nonneg_left hb (by omega)
    nlinarith
  have hzi : ∀ i : Fin ℓ, z i = (ρ : ℤ) ^ ((i : ℕ) + 1) * x := by
    intro i
    obtain ⟨i, hi⟩ := i
    induction i with
    | zero =>
      have := key (z ⟨0, hi⟩) x (hz' _) hx' (by simpa using hz ⟨0, hi⟩)
      simpa using this
    | succ n ih =>
      have ih' := ih (by omega)
      have hd : (p : ℤ) ∣ z ⟨n + 1, hi⟩ - ρ * z ⟨n, by omega⟩ := by
        have h1 := hz ⟨n + 1, hi⟩
        simp only at h1
        rw [ih']
        have : (ρ : ℤ) * ((ρ : ℤ) ^ (n + 1) * x) = (ρ : ℤ) ^ (n + 1 + 1) * x := by ring
        rw [this]; exact h1
      rw [key _ _ (hz' _) (hz' _) hd, ih']
      simp only
      ring
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    apply hne
    refine ⟨?_, funext fun i => i.elim0⟩
    simp only [hR, pow_zero, sub_self] at hx'
    exact abs_nonpos_iff.mp hx'
  · have hx0 : x ≠ 0 := by
      intro hx0
      apply hne
      refine ⟨hx0, funext fun i => ?_⟩
      rw [hzi i, hx0]; simp
    have hl := hzi ⟨ℓ - 1, by omega⟩
    have hb := hz' ⟨ℓ - 1, by omega⟩
    rw [hl] at hb
    simp only at hb
    rw [Nat.sub_add_cancel hpos, abs_mul, abs_of_nonneg (by positivity)] at hb
    have : 1 ≤ |x| := Int.one_le_abs hx0
    nlinarith [show (0 : ℤ) < R by positivity]

theorem skellat_L1_attained (ℓ p ρ : ℕ) (hρ : 1 ≤ ρ) :
    ∃ x : ℤ, ∃ z : Fin ℓ → ℤ, (∀ i : Fin ℓ, (p : ℤ) ∣ z i - (ρ : ℤ) ^ ((i : ℕ) + 1) * x) ∧
      ¬(x = 0 ∧ z = 0) ∧ |x| ≤ (ρ : ℤ) ^ ℓ ∧ ∀ i, |z i| ≤ (ρ : ℤ) ^ ℓ := by
  refine ⟨1, fun i => (ρ : ℤ) ^ ((i : ℕ) + 1), fun i => by simp, by simp, ?_, fun i => ?_⟩
  · simp only [abs_one]
    exact one_le_pow₀ (by exact_mod_cast hρ)
  · rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_right₀ (by exact_mod_cast hρ) (by omega)

theorem skellat_T (p ρ : ℕ) (hρ : 2 ≤ ρ) (hp : ρ ^ 2 < p + 4) (x z : Fin 2 → ℤ)
    (h1 : (p : ℤ) ∣ z 0 - ((ρ : ℤ) * x 0 + x 1)) (h2 : (p : ℤ) ∣ z 1 - (x 0 + (ρ : ℤ) * x 1))
    (hne : ¬(x = 0 ∧ z = 0)) :
    (ρ : ℤ) - 1 ≤ |x 0| ∨ (ρ : ℤ) - 1 ≤ |x 1| ∨ (ρ : ℤ) - 1 ≤ |z 0| ∨ (ρ : ℤ) - 1 ≤ |z 1| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a0, a1, b0, b1⟩ := hcon
  have hρz : (2 : ℤ) ≤ ρ := by exact_mod_cast hρ
  have hpz : (ρ : ℤ) ^ 2 < p + 4 := by exact_mod_cast hp
  have bnd : ∀ u v w : ℤ, |u| ≤ ρ - 2 → |v| ≤ ρ - 2 → |w| ≤ ρ - 2 → |u - (ρ * v + w)| < p := by
    intro u v w hu hv hw
    have e1 : |u - (ρ * v + w)| ≤ |u| + ρ * |v| + |w| := by
      calc |u - (ρ * v + w)| ≤ |u| + |ρ * v + w| := abs_sub _ _
        _ ≤ |u| + (|ρ * v| + |w|) := by gcongr; exact abs_add_le _ _
        _ = |u| + ρ * |v| + |w| := by
          rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ ρ)]; ring
    have : ρ * |v| ≤ ρ * (ρ - 2) := mul_le_mul_of_nonneg_left hv (by omega)
    nlinarith
  have e0 := SkG.eq_of_dvd_of_abs_lt h1 (bnd _ _ _ (by omega) (by omega) (by omega))
  have e1' : z 1 = ρ * x 1 + x 0 := by
    have := SkG.eq_of_dvd_of_abs_lt (a := z 1) (b := ρ * x 1 + x 0)
      (by rw [add_comm]; exact h2) (bnd _ _ _ (by omega) (by omega) (by omega))
    exact this
  -- `x ≠ 0`
  have hx : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · fin_cases i <;> simp [h.1, h.2]
    · fin_cases i
      · simp [e0, h.1, h.2]
      · simp [e1', h.1, h.2]
  have key : ∀ u v w : ℤ, w = ρ * u + v → |v| ≤ |u| → u ≠ 0 → ρ - 1 ≤ |w| := by
    intro u v w hw hvu hu
    have : |ρ * u| ≤ |w| + |v| := by
      have : ρ * u = w - v := by rw [hw]; ring
      rw [this]; exact abs_sub _ _
    rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ ρ)] at this
    have hu1 : 1 ≤ |u| := Int.one_le_abs hu
    nlinarith
  rcases le_total |x 1| |x 0| with h | h
  · have hx0 : x 0 ≠ 0 := by
      rcases hx with hx | hx
      · exact hx
      · intro h0; rw [h0, abs_zero] at h; exact hx (abs_nonpos_iff.mp h)
    have := key _ _ _ e0 h hx0
    omega
  · have hx1 : x 1 ≠ 0 := by
      rcases hx with hx | hx
      · intro h0; rw [h0, abs_zero] at h; exact hx (abs_nonpos_iff.mp h)
      · exact hx
    have := key _ _ _ e1' h hx1
    omega

end Z3NetF.Proofs

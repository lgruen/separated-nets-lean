/-
Proof module (V14 stage S16′): `cor:dgs`(4), the parenthetical choice `ρ = ⌊p^{1/s}⌋`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.DGS

@[expose] public section

/-!
# `cor:dgs`(4): `ρ = ⌊p^{1/s}⌋` satisfies `(ρ − 1)² ≥ s` when `p > (⌈√s⌉ + 1)^s`

* `floor_root_bounds`: `ρ = ⌊p^{1/s}⌋` has `ρ^s ≤ p < (ρ + 1)^s`.
* `dgs_S1_floor_core`: for `s ≥ 3`, a prime `p > (⌈√s⌉ + 1)^s` and `ρ = ⌊p^{1/s}⌋`: `ρ ≥ ⌈√s⌉ + 1 ≥ 2`, `ρ^s < p`
  (`p` is prime and `s ≥ 2`), `(ρ − 1)² ≥ s`, and hence (`dgs_S1`) the nets `𝒮¹_{k,p,ρ}` are `(k+1)`-separated and
  toroidally `(k+1)`-separated for every digital shift.
-/

namespace Z3NetDGS.Proofs

open Finset Matrix

/-- `ρ = ⌊p^{1/s}⌋` has `ρ^s ≤ p < (ρ + 1)^s` (`s ≥ 1`). -/
lemma floor_root_bounds (s p : ℕ) (hs : 1 ≤ s) :
    ⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊ ^ s ≤ p ∧ p < (⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊ + 1) ^ s := by
  set x : ℝ := (p : ℝ) ^ ((1 : ℝ) / s) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxs : x ^ s = p := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    have : (1 : ℝ) / s * s = 1 := by
      have : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
      field_simp
    rw [this, Real.rpow_one]
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  constructor
  · have : ((⌊x⌋₊ ^ s : ℕ) : ℝ) ≤ p := by
      push_cast; rw [← hxs]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) h1 s
    exact_mod_cast this
  · have : (p : ℝ) < ((⌊x⌋₊ + 1) ^ s : ℕ) := by
      push_cast; rw [← hxs]; exact pow_lt_pow_left₀ h2 hx0 (by omega)
    exact_mod_cast this

/-- `s ≤ ⌈√s⌉²`. -/
lemma le_ceil_sqrt_sq (s : ℕ) : s ≤ ⌈Real.sqrt s⌉₊ ^ 2 := by
  have h := Nat.le_ceil (Real.sqrt s)
  have : (s : ℝ) ≤ ((⌈Real.sqrt s⌉₊ ^ 2 : ℕ) : ℝ) := by
    push_cast
    calc (s : ℝ) = Real.sqrt s ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  exact_mod_cast this

/-- **`cor:dgs`(4)**, the parenthetical: `ρ = ⌊p^{1/s}⌋` with `p > (⌈√s⌉ + 1)^s` prime. -/
theorem dgs_S1_floor_core (s p k ρ : ℕ) [NeZero p] (hs : 3 ≤ s) (hp : p.Prime)
    (hρ : ρ = ⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊) (hps : (⌈Real.sqrt s⌉₊ + 1) ^ s < p)
    (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p) :
    ⌈Real.sqrt s⌉₊ + 1 ≤ ρ ∧ 2 ≤ ρ ∧ ρ ^ s < p ∧ s ≤ (ρ - 1) ^ 2 ∧
      IsKSep p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) ∧
      IsKSepTor p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) := by
  obtain ⟨hle, hlt⟩ := floor_root_bounds s p (by omega)
  rw [← hρ] at hle hlt
  set c := ⌈Real.sqrt s⌉₊ with hc
  have hcρ : c + 1 ≤ ρ := by
    by_contra h
    push Not at h
    have : (ρ + 1) ^ s ≤ (c + 1) ^ s := Nat.pow_le_pow_left (by omega) s
    omega
  have hc1 : 1 ≤ c := by
    rw [hc, Nat.one_le_ceil_iff]
    exact Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < s by omega))
  have hρ2 : 2 ≤ ρ := by omega
  have hρp : ρ ^ s < p := by
    refine lt_of_le_of_ne hle fun h => ?_
    have := (Nat.Prime.pow_eq_iff hp).mp h
    omega
  have hsq : s ≤ (ρ - 1) ^ 2 :=
    (le_ceil_sqrt_sq s).trans (Nat.pow_le_pow_left (by omega) 2)
  exact ⟨hcρ, hρ2, hρp, hsq, (dgs_S1 s p k ρ hs hp hρ2 hρp τ).2.1 hsq⟩

end Z3NetDGS.Proofs

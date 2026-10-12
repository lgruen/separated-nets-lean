/-
Development module (Solution side) for `cor:dim4` (entry S2). Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.S2Defs

@[expose] public section

/-!
# `cor:dim4`, covering by an elementary box (`t = 0`)

For a `(0,m,s)`-net (`Z3NetF.IsNet0`) and any depths `d` with `∑ d = m`, every `y ∈ [0,1)^s` lies
in an elementary box with depths `d`, and the unique net point of that box is within `p^(-d_c)` of
`y` in every coordinate. For `s = 4`, `m = 4k + 2` and depths `(k+1, k+1, k, k)` this gives the
Euclidean covering bound `h N^(1/4) ≤ 2 √p` used for the residue `m ≡ 2` of `cor:dim4`.
-/

namespace Z3NetF.Proofs

namespace SkD4

open Finset

/-- One net point per elementary box: within `p^(-d_c)` of `y` in every coordinate. -/
theorem box_cover {s p m : ℕ} (hp : 1 ≤ p) (X : (Fin m → ZMod p) → Fin s → ℕ)
    (hX : IsNet0 s p m X) (d : Fin s → ℕ) (hd : ∑ c, d c = m) (y : Fin s → ℝ)
    (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v : Fin m → ZMod p, ∀ c, |y c - (X v c : ℝ) / (p : ℝ) ^ m| < ((p : ℝ) ^ d c)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set a : Fin s → ℕ := fun c => ⌊y c * (p : ℝ) ^ d c⌋₊ with ha
  have hdle : ∀ c, d c ≤ m := fun c => by
    rw [← hd]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have ha_lt : ∀ c, a c < p ^ d c := by
    intro c
    have hpd : (0 : ℝ) < (p : ℝ) ^ d c := pow_pos hp0 _
    have : y c * (p : ℝ) ^ d c < ((p ^ d c : ℕ) : ℝ) := by
      push_cast; nlinarith [(hy c).2]
    exact (Nat.floor_lt (by nlinarith [(hy c).1])).2 this
  obtain ⟨v, hv, -⟩ := hX d hd a ha_lt
  refine ⟨v, fun c => ?_⟩
  have hvc := hv c
  set e := m - d c with he
  have hpe : 0 < p ^ e := pow_pos hp _
  -- integer bounds
  have h1 : a c * p ^ e ≤ X v c := by rw [← hvc]; exact Nat.div_mul_le_self _ _
  have h2 : X v c < (a c + 1) * p ^ e := by
    rw [← hvc]
    have := Nat.div_add_mod (X v c) (p ^ e)
    have := Nat.mod_lt (X v c) hpe
    nlinarith
  have hm : (p : ℝ) ^ m = (p : ℝ) ^ e * (p : ℝ) ^ d c := by
    have := hdle c; rw [← pow_add]; congr 1; omega
  have hE : (0 : ℝ) < (p : ℝ) ^ e := pow_pos hp0 _
  have hP : (0 : ℝ) < (p : ℝ) ^ d c := pow_pos hp0 _
  have r1 : (a c : ℝ) * (p : ℝ) ^ e ≤ (X v c : ℝ) := by exact_mod_cast h1
  have r2 : (X v c : ℝ) < ((a c : ℝ) + 1) * (p : ℝ) ^ e := by exact_mod_cast h2
  have f1 : (a c : ℝ) ≤ y c * (p : ℝ) ^ d c := Nat.floor_le (by nlinarith [(hy c).1])
  have f2 : y c * (p : ℝ) ^ d c < (a c : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [hm, abs_sub_lt_iff]
  have key : (X v c : ℝ) / ((p : ℝ) ^ e * (p : ℝ) ^ d c) * (p : ℝ) ^ d c =
      (X v c : ℝ) / (p : ℝ) ^ e := by field_simp
  have q1 : (a c : ℝ) ≤ (X v c : ℝ) / (p : ℝ) ^ e := by rw [le_div_iff₀ hE]; exact r1
  have q2 : (X v c : ℝ) / (p : ℝ) ^ e < (a c : ℝ) + 1 := by rw [div_lt_iff₀ hE]; exact r2
  have hinv : ((p : ℝ) ^ d c)⁻¹ * (p : ℝ) ^ d c = 1 := inv_mul_cancel₀ hP.ne'
  constructor
  · rw [← mul_lt_mul_iff_left₀ hP, sub_mul, key, hinv]; linarith
  · rw [← mul_lt_mul_iff_left₀ hP, sub_mul, key, hinv]; linarith

/-! ## Real powers `N^(-1/4)` -/

theorem rpow_quarter (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (x ^ n) ^ (-(1 / 4 : ℝ)) = x ^ (-((n : ℝ) / 4)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; ring_nf

/-- `(x^(4k))^(-1/4) = x^(-k)`. -/
theorem quarter_4k (x : ℝ) (hx : 0 < x) (k : ℕ) :
    (x ^ (4 * k)) ^ (-(1 / 4 : ℝ)) = (x ^ k)⁻¹ := by
  rw [rpow_quarter x hx, ← Real.rpow_natCast x k, ← Real.rpow_neg hx.le]; push_cast; ring_nf

/-- `√x (x^(4k+2))^(-1/4) = x^(-k)`. -/
theorem quarter_4k2 (x : ℝ) (hx : 0 < x) (k : ℕ) :
    Real.sqrt x * (x ^ (4 * k + 2)) ^ (-(1 / 4 : ℝ)) = (x ^ k)⁻¹ := by
  rw [rpow_quarter x hx, Real.sqrt_eq_rpow, ← Real.rpow_add hx, ← Real.rpow_natCast x k,
    ← Real.rpow_neg hx.le]
  push_cast; ring_nf

/-- **Covering for `s = 4`, `m = 4k + 2`** (`cor:dim4`, residue `2`): the elementary box with depths
`(k+1, k+1, k, k)` around `y` gives a net point within `2 p^(-k) = 2 √p N^(-1/4)` (Euclidean). -/
theorem cover_4k2 {p k : ℕ} (hp : 1 ≤ p) (X : (Fin (4 * k + 2) → ZMod p) → Fin 4 → ℕ)
    (hX : IsNet0 4 p (4 * k + 2) X) (y : Fin 4 → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v : Fin (4 * k + 2) → ZMod p,
      Real.sqrt (∑ c, (y c - (X v c : ℝ) / (p : ℝ) ^ (4 * k + 2)) ^ 2) ≤
        2 * Real.sqrt p * (((p : ℝ) ^ (4 * k + 2)) ^ (-(1 / 4 : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨v, hv⟩ := box_cover hp X hX ![k + 1, k + 1, k, k]
    (by simp [Fin.sum_univ_four]; ring) y hy
  refine ⟨v, ?_⟩
  rw [mul_assoc, quarter_4k2 _ hp0]
  set t : ℝ := ((p : ℝ) ^ k)⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  have hc : ∀ c, (y c - (X v c : ℝ) / (p : ℝ) ^ (4 * k + 2)) ^ 2 ≤ t ^ 2 := by
    intro c
    have h1 := hv c
    have h2 : ((p : ℝ) ^ (![k + 1, k + 1, k, k] c))⁻¹ ≤ t := by
      rw [ht]
      apply inv_anti₀ (pow_pos hp0 _)
      apply pow_le_pow_right₀ hp1
      fin_cases c <;> simp
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.le.trans h2) 2
  have hsum : ∑ c, (y c - (X v c : ℝ) / (p : ℝ) ^ (4 * k + 2)) ^ 2 ≤ (2 * t) ^ 2 := by
    calc _ ≤ ∑ _c : Fin 4, t ^ 2 := Finset.sum_le_sum (fun c _ => hc c)
      _ = (2 * t) ^ 2 := by simp; ring
  calc _ ≤ Real.sqrt ((2 * t) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 2 * t := Real.sqrt_sq (by positivity)

end SkD4

end Z3NetF.Proofs

module
public import Mathlib
public import Z3Net.SkSepGraph

@[expose] public section

/-!
# Covering radius of a `(0, m, s)`-net with `m = s k + r` (helper for `cor:dim4`, `cor:allm`)

The elementary box with depth `k + 1` on the coordinates `c < r` and `k` on the others contains
the point `y` and a net point, so every `y ∈ [0,1)^s` has a net point at Euclidean distance
`< √(r p^(-2(k+1)) + (s - r) p^(-2k))`.
-/

namespace Z3NetF.Proofs

open Finset

namespace SkSep

lemma sum_depthN (r k : ℕ) : ∀ n, ∑ c ∈ range n, depthN r k c = skOff r k n
  | 0 => by simp [skOff]
  | n + 1 => by rw [sum_range_succ, sum_depthN r k n, skOff_succ]

lemma sum_ite_lt (r n : ℕ) (hr : r ≤ n) (A B : ℝ) :
    ∑ c ∈ range n, (if c < r then A else B) = (r : ℝ) * A + ((n - r : ℕ) : ℝ) * B := by
  rw [show n = r + (n - r) by omega, sum_range_add, show r + (n - r) - r = n - r by omega]
  rw [sum_congr rfl fun c hc => if_pos (mem_range.mp hc),
    sum_congr rfl fun j _ => if_neg (show ¬(r + j < r) by omega)]
  simp

end SkSep

open SkSep

/-- **Covering radius** of any digital `(0, m, s)`-net over `ℤ/pℤ` with `m = s k + r`, `r ≤ s`:
every `y ∈ [0,1)^s` has a point at Euclidean distance `< √(r p^(-2(k+1)) + (s - r) p^(-2k))`. -/
theorem skel_cover (s p m k r : ℕ) (hs : 1 ≤ s) (hp : 2 ≤ p) (hr : r ≤ s) (hm : m = s * k + r)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (hnet : IsNet0 s p m (digPoint p m C))
    (y : Fin s → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v : Fin m → ZMod p,
      Real.sqrt (∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2) <
        Real.sqrt ((r : ℝ) / (p : ℝ) ^ (2 * (k + 1)) + ((s - r : ℕ) : ℝ) / (p : ℝ) ^ (2 * k)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set d : Fin s → ℕ := fun c => skDepth r k c with hd
  have hdsum : ∑ c, d c = m := by
    rw [hm, ← skOff_top s r k hr, ← sum_depthN r k s]
    exact Fin.sum_univ_eq_sum_range (fun c => depthN r k c) s
  have hdm : ∀ c, d c ≤ m := fun c => by
    rw [← hdsum]; exact Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (mem_univ c)
  set a : Fin s → ℕ := fun c => ⌊y c * (p : ℝ) ^ d c⌋₊ with ha
  have hya : ∀ c, (a c : ℝ) ≤ y c * (p : ℝ) ^ d c ∧ y c * (p : ℝ) ^ d c < a c + 1 := fun c =>
    ⟨Nat.floor_le (by have := (hy c).1; positivity), Nat.lt_floor_add_one _⟩
  have halt : ∀ c, a c < p ^ d c := by
    intro c
    rw [ha]; simp only
    rw [Nat.floor_lt (by have := (hy c).1; positivity)]
    push_cast
    have hD : (0 : ℝ) < (p : ℝ) ^ d c := by positivity
    have := (hy c).2
    nlinarith
  obtain ⟨v, hv, -⟩ := hnet d hdsum a halt
  refine ⟨v, Real.sqrt_lt_sqrt (by positivity) ?_⟩
  have hterm : ∀ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2 <
      (if (c : ℕ) < r then 1 / (p : ℝ) ^ (2 * (k + 1)) else 1 / (p : ℝ) ^ (2 * k)) := by
    intro c
    set X := digPoint p m C v c
    set q := p ^ (m - d c) with hq
    have hq0 : 0 < q := by positivity
    have hXa : X / q = a c := hv c
    have h1 : a c * q ≤ X := by rw [← hXa]; exact Nat.div_mul_le_self X q
    have h2 : X < (a c + 1) * q := by
      rw [← hXa]
      have := Nat.div_add_mod X q
      have := Nat.mod_lt X hq0
      nlinarith
    have hD : (0 : ℝ) < (p : ℝ) ^ d c := by positivity
    have hQ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
    have hP : (p : ℝ) ^ m = (p : ℝ) ^ d c * (q : ℝ) := by
      rw [hq]; push_cast; rw [← pow_add]; congr 1; have := hdm c; omega
    have r1 : (a c : ℝ) * q ≤ X := by exact_mod_cast h1
    have r2 : (X : ℝ) < ((a c : ℝ) + 1) * q := by exact_mod_cast h2
    have hxl : (a c : ℝ) / (p : ℝ) ^ d c ≤ (X : ℝ) / (p : ℝ) ^ m := by
      rw [hP, div_le_div_iff₀ hD (by positivity)]; nlinarith
    have hxu : (X : ℝ) / (p : ℝ) ^ m < ((a c : ℝ) + 1) / (p : ℝ) ^ d c := by
      rw [hP, div_lt_div_iff₀ (by positivity) hD]; nlinarith
    have hyl : (a c : ℝ) / (p : ℝ) ^ d c ≤ y c := by
      rw [div_le_iff₀ hD]; exact (hya c).1
    have hyu : y c < ((a c : ℝ) + 1) / (p : ℝ) ^ d c := by
      rw [lt_div_iff₀ hD]; exact (hya c).2
    have hdiff : |y c - (X : ℝ) / (p : ℝ) ^ m| < 1 / (p : ℝ) ^ d c := by
      have e : ((a c : ℝ) + 1) / (p : ℝ) ^ d c = (a c : ℝ) / (p : ℝ) ^ d c + 1 / (p : ℝ) ^ d c := by
        rw [add_div]
      rw [e] at hxu hyu
      rw [abs_lt]; constructor <;> linarith
    have hsq : (y c - (X : ℝ) / (p : ℝ) ^ m) ^ 2 < (1 / (p : ℝ) ^ d c) ^ 2 := by
      have := sq_lt_sq' (abs_lt.mp hdiff).1 (abs_lt.mp hdiff).2
      exact this
    have e2 : (1 / (p : ℝ) ^ d c) ^ 2 =
        (if (c : ℕ) < r then 1 / (p : ℝ) ^ (2 * (k + 1)) else 1 / (p : ℝ) ^ (2 * k)) := by
      rw [hd]; simp only [skDepth]
      split_ifs <;> rw [div_pow, one_pow, ← pow_mul, Nat.mul_comm]
    rw [← e2]; exact hsq
  have hne : (univ : Finset (Fin s)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  calc ∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2
      < ∑ c : Fin s, (if (c : ℕ) < r then 1 / (p : ℝ) ^ (2 * (k + 1)) else 1 / (p : ℝ) ^ (2 * k)) :=
        Finset.sum_lt_sum_of_nonempty hne fun c _ => hterm c
    _ = _ := by
        rw [Fin.sum_univ_eq_sum_range
          (fun c => if c < r then 1 / (p : ℝ) ^ (2 * (k + 1)) else 1 / (p : ℝ) ^ (2 * k)) s,
          sum_ite_lt r s hr]
        ring

end Z3NetF.Proofs

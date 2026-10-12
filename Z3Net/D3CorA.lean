/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(`paper/core.tex`), `cor:allm`. Entry Dim3
(`ChallengeDim3.lean`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.D3Allm
public import Z3Net.D3B1
public import Z3Net.Main
public import Z3Net.ColMain

@[expose] public section

/-!
# Entry Dim3, part 6: tools for `cor:allm`

* `cover_box` — covering from the `(0,m,3)`-net property: every `y ∈ [0,1)³` lies in the
  elementary box of depths `d` of some net point, so `|y_c - X_c/N| < p^(-d_c)`.
* `cres_sq` — `cres N u` is `|-u + N t|` for some integer `t`.
* the `m = 3` family (V14 stage S9′: the column net `𝒞_p` of `thm:col`, which replaces the former
  `thm:E1`): `col_isNet0`, `col_sep_dim3`, `col_cover_dim3` (bridge from the `Z3NetC` statements to
  the KN-style `digPoint`, `IsNet0`, `cres`, which agree with `Z3NetF`'s by definition).
-/

namespace Z3NetKN.Proofs.D3

open Matrix Finset Filter Topology

/-! ## Real helpers -/

lemma rpow_third_nat (p : ℝ) (hp : 0 < p) (n : ℕ) :
    ((p ^ n) ^ (-(1 / (3 : ℝ)))) = p ^ (-((n : ℝ) / 3)) := by
  rw [← Real.rpow_natCast p n, ← Real.rpow_mul hp.le]; congr 1; ring

lemma mul_rpow_neg_third_lt (a b x : ℝ) (hx : 0 < x) (hb : 0 < b) (h : a ^ 3 < b ^ 3 * x) :
    a * x ^ (-(1 / (3 : ℝ))) < b := by
  have ht : 0 < x ^ (1 / (3 : ℝ)) := by positivity
  rw [Real.rpow_neg hx.le, ← div_eq_mul_inv, div_lt_iff₀ ht]
  apply lt_of_pow_lt_pow_left₀ 3 (by positivity)
  rw [mul_pow, rpow_third_cube x hx.le]; exact h

lemma sqrt_sum_div (N : ℝ) (hN : 0 < N) (f : Fin 3 → ℝ) :
    Real.sqrt (∑ c, (f c / N) ^ 2) = Real.sqrt (∑ c, (f c) ^ 2) / N := by
  have e : (∑ c, (f c / N) ^ 2) = (∑ c, (f c) ^ 2) / N ^ 2 := by
    rw [Finset.sum_div]; congr 1; ext c; rw [div_pow]
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hN.le]

/-! ## Covering from the net property -/

lemma cover_box (p m : ℕ) (hp : 0 < p) (X : (Fin m → ZMod p) → Fin 3 → ℕ)
    (hX : IsNet0 p m X) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = m) (y : Fin 3 → ℝ)
    (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v, ∀ c, |y c - (X v c : ℝ) / (p : ℝ) ^ m| < ((p : ℝ) ^ d c)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hdm : ∀ c, d c ≤ m := by intro c; fin_cases c <;> simp <;> omega
  let a : Fin 3 → ℕ := fun c => ⌊y c * (p : ℝ) ^ d c⌋₊
  have ha : ∀ c, a c < p ^ d c := by
    intro c
    have h1 : y c * (p : ℝ) ^ d c < (p : ℝ) ^ d c := by
      have := (hy c).2
      have hpd : (0 : ℝ) < (p : ℝ) ^ d c := by positivity
      nlinarith
    have h0 : 0 ≤ y c * (p : ℝ) ^ d c := mul_nonneg (hy c).1 (by positivity)
    show ⌊y c * (p : ℝ) ^ d c⌋₊ < p ^ d c
    rw [Nat.floor_lt h0]; exact_mod_cast h1
  obtain ⟨v, hv, -⟩ := hX d hd a ha
  refine ⟨v, fun c => ?_⟩
  have hvc := hv c
  have hq : 0 < p ^ (m - d c) := pow_pos hp _
  -- `a p^(m-d) ≤ X < (a+1) p^(m-d)`
  have hlo : a c * p ^ (m - d c) ≤ X v c := by
    rw [← hvc]; exact Nat.div_mul_le_self _ _
  have hhi : X v c < (a c + 1) * p ^ (m - d c) := by
    have h1 := Nat.div_add_mod (X v c) (p ^ (m - d c))
    have h2 := Nat.mod_lt (X v c) hq
    rw [hvc] at h1
    nlinarith
  have hpm : (p : ℝ) ^ m = (p : ℝ) ^ d c * (p : ℝ) ^ (m - d c) := by
    rw [← pow_add, Nat.add_sub_cancel' (hdm c)]
  have hpd : (0 : ℝ) < (p : ℝ) ^ d c := by positivity
  have hpq : (0 : ℝ) < (p : ℝ) ^ (m - d c) := by positivity
  have hloR : (a c : ℝ) / (p : ℝ) ^ d c ≤ (X v c : ℝ) / (p : ℝ) ^ m := by
    rw [hpm, div_le_div_iff₀ hpd (by positivity)]
    have : ((a c * p ^ (m - d c) : ℕ) : ℝ) ≤ (X v c : ℝ) := by exact_mod_cast hlo
    push_cast at this; nlinarith
  have hhiR : (X v c : ℝ) / (p : ℝ) ^ m < ((a c : ℝ) + 1) / (p : ℝ) ^ d c := by
    rw [hpm, div_lt_div_iff₀ (by positivity) hpd]
    have : (X v c : ℝ) < (((a c + 1) * p ^ (m - d c) : ℕ) : ℝ) := by exact_mod_cast hhi
    push_cast at this; nlinarith
  have hyl : (a c : ℝ) ≤ y c * (p : ℝ) ^ d c := Nat.floor_le (by have := (hy c).1; positivity)
  have hyh : y c * (p : ℝ) ^ d c < (a c : ℝ) + 1 := Nat.lt_floor_add_one _
  have hyl' : (a c : ℝ) / (p : ℝ) ^ d c ≤ y c := by rw [div_le_iff₀ hpd]; linarith
  have hyh' : y c < ((a c : ℝ) + 1) / (p : ℝ) ^ d c := by rw [lt_div_iff₀ hpd]; linarith
  have hw : ((a c : ℝ) + 1) / (p : ℝ) ^ d c - (a c : ℝ) / (p : ℝ) ^ d c = ((p : ℝ) ^ d c)⁻¹ := by
    field_simp; ring
  rw [abs_lt]; constructor <;> linarith

/-- The Euclidean form of `cover_box`. -/
lemma cover_box_dist (p m : ℕ) (hp : 0 < p) (X : (Fin m → ZMod p) → Fin 3 → ℕ)
    (hX : IsNet0 p m X) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = m) (y : Fin 3 → ℝ)
    (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v, Real.sqrt (∑ c, (y c - (X v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
      Real.sqrt (∑ c, (((p : ℝ) ^ d c)⁻¹) ^ 2) := by
  obtain ⟨v, hv⟩ := cover_box p m hp X hX d hd y hy
  refine ⟨v, Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => ?_)⟩
  have := hv c
  have h0 : 0 ≤ ((p : ℝ) ^ d c)⁻¹ := by positivity
  rw [← sq_abs (y c - _)]
  exact pow_le_pow_left₀ (abs_nonneg _) this.le 2

/-! ## `cres` as a translate -/

lemma cres_sq (N : ℕ) (hN : 0 < N) (u : ℤ) :
    ∃ t : ℤ, ((cres N u : ℕ) : ℤ) ^ 2 = (-u + N * t) ^ 2 := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ hN'.ne'
  have hrN : u % (N : ℤ) < N := Int.emod_lt_of_pos _ hN'
  have hdef : u % (N : ℤ) = u - N * (u / N) := Int.emod_def u N
  have htn : (((u % (N : ℤ)).toNat : ℕ) : ℤ) = u % (N : ℤ) := Int.toNat_of_nonneg hr0
  unfold cres
  rcases le_total (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) with h | h
  · rw [min_eq_left h, htn]
    exact ⟨u / N, by rw [hdef]; ring⟩
  · rw [min_eq_right h]
    have hle : (u % (N : ℤ)).toNat ≤ N := by omega
    refine ⟨u / N + 1, ?_⟩
    push_cast [hle]
    rw [htn, hdef]; ring

/-! ## The `m = 3` family (`thm:col`, the column net `𝒞_p`) -/

lemma coprime6_of_prime (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : Nat.Coprime p 6 := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
  have := Nat.le_of_dvd (by norm_num) h
  rcases (show p = 5 ∨ p = 6 by omega) with rfl | rfl <;> norm_num at *

lemma col_isNet0 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    IsNet0 p 3 (digPoint p 3 (Z3NetC.colGen p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h := (Z3NetC.col_net (coprime6_of_prime p hp hp5) hp5).1
  intro d hd a ha
  exact h d (by rw [Fin.sum_univ_three]; exact hd) a ha

lemma col_sep_dim3 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (v w : Fin 3 → ZMod p) (hvw : v ≠ w) :
    Z3NetC.cCol p * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
      Real.sqrt (∑ c, ((cres (p ^ 3) ((digPoint p 3 (Z3NetC.colGen p) v c : ℤ) -
        (digPoint p 3 (Z3NetC.colGen p) w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  exact (Z3NetC.col_sep_real (coprime6_of_prime p hp hp5) hp5).1 v w hvw

lemma digPoint_eqF (q m : ℕ) (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod q)) :
    digPoint q m C = Z3NetF.digPoint q m C := rfl

lemma col_cover_dim3 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (y : Fin 3 → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v : Fin 3 → ZMod p, Real.sqrt (∑ c, (y c - (digPoint p 3 (Z3NetC.colGen p) v c : ℝ) /
      (p : ℝ) ^ 3) ^ 2) ≤ Real.sqrt 3 * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [digPoint_eqF]
  exact Z3NetC.col_covering (coprime6_of_prime p hp hp5) y hy

end Z3NetKN.Proofs.D3

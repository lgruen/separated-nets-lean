/-
Proof module (stage 6, main entry): `rem:lattice3`, the lattice reading of `𝒫_{k,q}`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.Defs

@[expose] public section

/-!
# `rem:lattice3`

`M = -I + [u×]` with `u = (1,1,1)`; `I + M/q = R_θ ((1-1/q) P + r (I - P))` with `P` the projection
on `u`, `R_θ` the rotation by `θ = arctan(√3/(q-1))` about `u` and `r = ((1-1/q)² + 3/q²)^(1/2)`;
`det (I + M/q) = (1-1/q)((1-1/q)² + 3/q²) < 1`; `|(I+M/q)v|² = (1-1/q)²|v|² + (3/q²)|v_⊥|²`, whose
minimum over `ℤ³ \ 0` is `1 - 2/q + 3/q²` (attained at the unit vectors) for `q ≥ 3`; and
`c(q) < λ₁(Λ_q)`.
-/

namespace Z3Net.Proofs

open Matrix

lemma Mcell_real : Mcell.map (Int.cast : ℤ → ℝ) = !![-1, -1, 1; 1, -1, -1; -1, 1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mcell]

theorem lat3_cross (v : Fin 3 → ℝ) :
    Mcell.map (Int.cast : ℤ → ℝ) *ᵥ v = -v + crossProduct ![1, 1, 1] v := by
  rw [Mcell_real]
  ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, crossProduct] <;> ring

lemma projU_eq : projU = !![1/3, 1/3, 1/3; 1/3, 1/3, 1/3; 1/3, 1/3, 1/3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [projU]

lemma rotU_eq (θ : ℝ) : rotU θ =
    let c := Real.cos θ
    let t := Real.sin θ / Real.sqrt 3
    !![1/3 + c * (2/3), 1/3 - c/3 - t, 1/3 - c/3 + t;
       1/3 - c/3 + t, 1/3 + c * (2/3), 1/3 - c/3 - t;
       1/3 - c/3 - t, 1/3 - c/3 + t, 1/3 + c * (2/3)] := by
  unfold rotU
  rw [projU_eq, Mcell_real]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> simp

theorem lat3_rot (θ : ℝ) :
    rotU θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ∧ rotU θ *ᵥ ![1, 1, 1] = ![1, 1, 1] ∧
      ∀ w : Fin 3 → ℝ, w ⬝ᵥ ![1, 1, 1] = 0 →
        (rotU θ *ᵥ w) ⬝ᵥ w = Real.cos θ * (w ⬝ᵥ w) := by
  have hcs := Real.cos_sq_add_sin_sq θ
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  set c := Real.cos θ
  set sn := Real.sin θ
  have ht : (sn / Real.sqrt 3) ^ 2 = sn ^ 2 / 3 := by rw [div_pow, h3]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff, rotU_eq]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [mul_apply, Fin.sum_univ_three, one_apply] <;> nlinarith [ht]
    · rw [det_fin_three]
      simp
      nlinarith [ht]
  · rw [rotU_eq]
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  · intro w hw
    rw [rotU_eq]
    simp only [dotProduct, mulVec, Fin.sum_univ_three] at hw ⊢
    simp at hw ⊢
    have h2 : w 2 = -(w 0) - w 1 := by linarith
    rw [h2]
    ring

theorem lat3_decomp (q : ℕ) (hq : 2 ≤ q) :
    latMat q = rotU (Real.arctan (Real.sqrt 3 / ((q : ℝ) - 1))) *
      ((1 - 1 / (q : ℝ)) • projU + Real.sqrt ((1 - 1 / (q : ℝ)) ^ 2 + 3 / (q : ℝ) ^ 2) • (1 - projU)) := by
  have hq0 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set t := Real.sqrt 3 / ((q : ℝ) - 1) with ht
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : 0 < Real.sqrt 3 := by positivity
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  set r := Real.sqrt ((1 - 1 / (q : ℝ)) ^ 2 + 3 / (q : ℝ) ^ 2) with hr
  have hs1 : 0 < Real.sqrt (1 + t ^ 2) := by positivity
  -- `r = (1 - 1/q) √(1 + t²)`
  have hr' : r = (1 - 1 / (q : ℝ)) * Real.sqrt (1 + t ^ 2) := by
    have hpos : 0 ≤ 1 - 1 / (q : ℝ) := by
      have : 1 / (q : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq0
      linarith
    rw [hr, show (1 - 1 / (q : ℝ)) ^ 2 + 3 / (q : ℝ) ^ 2 =
        ((1 - 1 / (q : ℝ)) * Real.sqrt (1 + t ^ 2)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by positivity), ht, div_pow, h3]
      field_simp]
    exact Real.sqrt_sq (by positivity)
  have hc : r * Real.cos (Real.arctan t) = 1 - 1 / (q : ℝ) := by
    rw [Real.cos_arctan, hr']; field_simp
  have hs : r * (Real.sin (Real.arctan t) / Real.sqrt 3) = 1 / (q : ℝ) := by
    rw [Real.sin_arctan, hr', ht]; field_simp
  rw [rotU_eq, projU_eq]
  unfold latMat
  rw [Mcell_real]
  set c := Real.cos (Real.arctan t)
  set u := Real.sin (Real.arctan t) / Real.sqrt 3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply]
  · linear_combination (-(2 : ℝ) / 3) * hc
  · linear_combination (1 / 3 : ℝ) * hc + hs
  · linear_combination (1 / 3 : ℝ) * hc - hs
  · linear_combination (1 / 3 : ℝ) * hc - hs
  · linear_combination (-(2 : ℝ) / 3) * hc
  · linear_combination (1 / 3 : ℝ) * hc + hs
  · linear_combination (1 / 3 : ℝ) * hc + hs
  · linear_combination (1 / 3 : ℝ) * hc - hs
  · linear_combination (-(2 : ℝ) / 3) * hc

lemma latMat_eq (q : ℕ) : latMat q =
    let x := 1 / (q : ℝ)
    !![1 - x, -x, x; x, 1 - x, -x; -x, x, 1 - x] := by
  unfold latMat
  rw [Mcell_real]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem lat3_det (q : ℕ) (hq : 1 ≤ q) :
    (latMat q).det = (1 - 1 / (q : ℝ)) * ((1 - 1 / (q : ℝ)) ^ 2 + 3 / (q : ℝ) ^ 2) ∧
      (latMat q).det < 1 := by
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : (latMat q).det = (1 - 1 / (q : ℝ)) * ((1 - 1 / (q : ℝ)) ^ 2 + 3 / (q : ℝ) ^ 2) := by
    rw [latMat_eq, det_fin_three]
    simp [vecHead, vecTail]
    ring
  refine ⟨hd, ?_⟩
  rw [hd]
  set x := 1 / (q : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by linarith)]; exact hq0
  have h3 : 3 / (q : ℝ) ^ 2 = 3 * x ^ 2 := by rw [hx, div_pow, one_pow]; ring
  rw [h3]
  nlinarith [mul_pos hx0 hx0, mul_pos (mul_pos hx0 hx0) hx0]

theorem lat3_norm (q : ℕ) (v : Fin 3 → ℝ) :
    (latMat q *ᵥ v) ⬝ᵥ (latMat q *ᵥ v) =
      (1 - 1 / (q : ℝ)) ^ 2 * (v ⬝ᵥ v) + 3 / (q : ℝ) ^ 2 * (v ⬝ᵥ v - (∑ i, v i) ^ 2 / 3) := by
  rw [latMat_eq]
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem lat3_min (q : ℕ) (hq : 3 ≤ q) (v : Fin 3 → ℤ) (hv : v ≠ 0) :
    1 - 2 / (q : ℝ) + 3 / (q : ℝ) ^ 2 ≤
      (latMat q *ᵥ (fun i => (v i : ℝ))) ⬝ᵥ (latMat q *ᵥ (fun i => (v i : ℝ))) := by
  rw [lat3_norm]
  have hq0 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  set x := 1 / (q : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 3 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hq0
  have e2 : 2 / (q : ℝ) = 2 * x := by rw [hx]; ring
  have e3 : 3 / (q : ℝ) ^ 2 = 3 * x ^ 2 := by rw [hx, div_pow, one_pow]; ring
  rw [e2, e3]
  set a := v 0; set b := v 1; set c := v 2
  have hsum : ∑ i, ((v i : ℤ) : ℝ) = (a : ℝ) + b + c := by simp [Fin.sum_univ_three, a, b, c]
  have hdot : (fun i => ((v i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((v i : ℤ) : ℝ)) =
      (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 := by
    simp [dotProduct, Fin.sum_univ_three, a, b, c]; ring
  rw [hsum, hdot]
  have hn : 1 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
    by_contra h
    push Not at h
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    apply hv
    funext i; fin_cases i <;> simp <;> assumption
  -- `3|v|² - (Σ v)² = (a-b)² + (b-c)² + (a-c)² ≥ 0`
  by_cases h1 : a ^ 2 + b ^ 2 + c ^ 2 = 1
  · have hS : (a + b + c) ^ 2 = 1 := by
      have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg b, sq_nonneg c]
      have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg a, sq_nonneg c]
      have hc : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
      obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb; obtain ⟨hc1, hc2⟩ := hc
      interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all
    have h1' : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 = 1 := by exact_mod_cast h1
    have hS' : ((a : ℝ) + b + c) ^ 2 = 1 := by exact_mod_cast hS
    rw [h1', hS']
    nlinarith
  · have h2 : 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by omega
    have h2' : (2 : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 := by exact_mod_cast h2
    have hcs : 0 ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (c : ℝ) ^ 2 - ((a : ℝ) + b + c) ^ 2 / 3 := by
      nlinarith [sq_nonneg ((a : ℝ) - b), sq_nonneg ((b : ℝ) - c), sq_nonneg ((a : ℝ) - c)]
    have hx2 : 0 ≤ 3 * x ^ 2 := by positivity
    nlinarith [mul_nonneg hx2 hcs]

theorem lat3_min_attained (q : ℕ) :
    latMat q *ᵥ ![1, 0, 0] = ![1 - 1 / (q : ℝ), 1 / (q : ℝ), -(1 / (q : ℝ))] ∧
      (latMat q *ᵥ ![1, 0, 0]) ⬝ᵥ (latMat q *ᵥ ![1, 0, 0]) = 1 - 2 / (q : ℝ) + 3 / (q : ℝ) ^ 2 := by
  have e : latMat q *ᵥ ![1, 0, 0] = ![1 - 1 / (q : ℝ), 1 / (q : ℝ), -(1 / (q : ℝ))] := by
    rw [latMat_eq]
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨e, ?_⟩
  rw [e]
  simp [dotProduct, Fin.sum_univ_three]
  ring

theorem lat3_cP (q : ℕ) (hq : 1 ≤ q) : cP q < Real.sqrt (1 - 2 / (q : ℝ) + 3 / (q : ℝ) ^ 2) := by
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  unfold cP
  apply Real.sqrt_lt_sqrt (le_min (sq_nonneg _) (le_min (by positivity) (by positivity)))
  refine lt_of_le_of_lt (min_le_left _ _) ?_
  have hx0 : 0 < 1 / (q : ℝ) := by positivity
  have e2 : 2 / (q : ℝ) = 2 * (1 / (q : ℝ)) := by ring
  have e3 : 3 / (q : ℝ) ^ 2 = 3 * (1 / (q : ℝ)) ^ 2 := by rw [div_pow, one_pow]; ring
  rw [e2, e3]
  nlinarith [mul_pos hx0 hx0]

end Z3Net.Proofs

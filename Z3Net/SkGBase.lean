module
public import Mathlib
public import Z3Net.S2Defs

@[expose] public section

/-!
# Entry S2: basic facts on the Gaussian matrix `A(B)` and on `B(p)` (`def:G2rule`)

* `gcol r c d`: column `d` of `gaussA r c` as a Gaussian integer (`Ω_{d+1}`, resp. `i Ω_{r-1}`);
* `norm_gaussOmega`: `N(Ω_l) = ∏_{j<l} (c_j² + 1)`;
* `normA_ge`: `|Re Ω_{r-1}| + |Im Ω_{r-1}| ≤ max_j ‖A_j(B)‖₁` (the last two columns);
* `normA_sq_le`: `(max_j ‖A_j(B)‖₁)² ≤ r² N(Ω_{r-1})`;
* bounds on `c_j = cG B j` and on `N(Ω_{r-1})`: `2 B^r ≤ N(Ω_{r-1}) ≤ 10 · 5^(r-2) B^r`;
* `Bp_spec`, `le_Bp`, `Bp_lt`, `Bp_max` and **`Bp_mono`** (`def:G2rule`).
-/

namespace Z3NetF.Proofs

open Finset

namespace SkG

/-- Column `d` of `gaussA r c` as a Gaussian integer. -/
def gcol (r : ℕ) (c : ℕ → ℤ) (d : ℕ) : GaussianInt :=
  if d + 1 < r then gaussOmega c (d + 1) else (⟨0, 1⟩ : GaussianInt) * gaussOmega c (r - 1)

lemma gaussA_zero (r : ℕ) (c : ℕ → ℤ) (d : ℕ) : gaussA r c 0 d = (gcol r c d).re := by
  simp [gaussA, gcol]

lemma gaussA_one (r : ℕ) (c : ℕ → ℤ) (d : ℕ) : gaussA r c 1 d = (gcol r c d).im := by
  simp [gaussA, gcol]

lemma gaussOmega_succ (c : ℕ → ℤ) (l : ℕ) :
    gaussOmega c (l + 1) = gaussOmega c l * ⟨c l, 1⟩ := by
  simp [gaussOmega, prod_range_succ]

lemma norm_mk (a : ℤ) : (⟨a, 1⟩ : GaussianInt).norm = a ^ 2 + 1 := by
  simp [Zsqrtd.norm_def]; ring

lemma norm_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  simp [Zsqrtd.norm_def]; ring

lemma norm_prod (S : Finset ℕ) (f : ℕ → GaussianInt) :
    (∏ j ∈ S, f j).norm = ∏ j ∈ S, (f j).norm :=
  map_prod (Zsqrtd.normMonoidHom (d := -1)) f S

lemma norm_gaussOmega (c : ℕ → ℤ) (l : ℕ) :
    (gaussOmega c l).norm = ∏ j ∈ range l, (c j ^ 2 + 1) := by
  rw [gaussOmega, norm_prod]; simp only [norm_mk]

lemma re_sq_le_norm (z : GaussianInt) : z.re ^ 2 ≤ z.norm := by
  rw [norm_eq]; nlinarith [sq_nonneg z.im]

lemma im_sq_le_norm (z : GaussianInt) : z.im ^ 2 ≤ z.norm := by
  rw [norm_eq]; nlinarith [sq_nonneg z.re]

lemma norm_le_abs_sq (z : GaussianInt) : z.norm ≤ (|z.re| + |z.im|) ^ 2 := by
  rw [norm_eq]
  have h1 := sq_abs z.re
  have h2 := sq_abs z.im
  nlinarith [abs_nonneg z.re, abs_nonneg z.im]

lemma normA_nonneg (s B : ℕ) : 0 ≤ normA s B :=
  le_max_of_le_left (sum_nonneg fun _ _ => abs_nonneg _)

lemma AG_zero (s B d : ℕ) : AG s B 0 d = (gcol (s - 2) (cG B) d).re := gaussA_zero _ _ _
lemma AG_one (s B d : ℕ) : AG s B 1 d = (gcol (s - 2) (cG B) d).im := gaussA_one _ _ _

/-- `|Re Ω_{r-1}| + |Im Ω_{r-1}| ≤ ‖A_j‖₁` for both rows. -/
lemma rows_ge (s B : ℕ) (hs : 4 ≤ s) (i : Fin 2) :
    |(gaussOmega (cG B) (s - 3)).re| + |(gaussOmega (cG B) (s - 3)).im| ≤
      ∑ d ∈ range (s - 2), |AG s B i d| := by
  have hsub : ({s - 4, s - 3} : Finset ℕ) ⊆ range (s - 2) := by
    intro x hx; simp at hx; simp; omega
  have hne : s - 4 ≠ s - 3 := by omega
  have h := sum_le_sum_of_subset_of_nonneg hsub (f := fun d => |AG s B i d|)
    (fun _ _ _ => abs_nonneg _)
  rw [sum_pair hne] at h
  refine le_trans (le_of_eq ?_) h
  have e1 : gcol (s - 2) (cG B) (s - 4) = gaussOmega (cG B) (s - 3) := by
    unfold gcol; split_ifs with h
    · congr 1; omega
    · omega
  have e2 : gcol (s - 2) (cG B) (s - 3) = (⟨0, 1⟩ : GaussianInt) * gaussOmega (cG B) (s - 3) := by
    unfold gcol; split_ifs with h
    · omega
    · congr 2
  fin_cases i
  · simp only [Fin.zero_eta, AG_zero, e1, e2, Zsqrtd.re_mul]; simp
  · simp only [Fin.mk_one, AG_one, e1, e2, Zsqrtd.im_mul]; simp; ring

lemma normA_ge (s B : ℕ) (hs : 4 ≤ s) :
    |(gaussOmega (cG B) (s - 3)).re| + |(gaussOmega (cG B) (s - 3)).im| ≤ normA s B :=
  le_max_of_le_left (rows_ge s B hs 0)

lemma norm_gaussOmega_mono (c : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    (gaussOmega c a).norm ≤ (gaussOmega c b).norm := by
  rw [norm_gaussOmega, norm_gaussOmega, ← prod_range_mul_prod_Ico _ hab]
  have h1 : 0 ≤ ∏ j ∈ range a, (c j ^ 2 + 1) := prod_nonneg fun _ _ => by positivity
  have h2 : 1 ≤ ∏ j ∈ Ico a b, (c j ^ 2 + 1) :=
    one_le_prod₀ fun j _ => by nlinarith [sq_nonneg (c j)]
  nlinarith

lemma norm_gcol_le (r : ℕ) (c : ℕ → ℤ) (d : ℕ) :
    (gcol r c d).norm ≤ (gaussOmega c (r - 1)).norm := by
  unfold gcol
  split_ifs with h
  · exact norm_gaussOmega_mono c (by omega)
  · rw [Zsqrtd.norm_mul]; simp [Zsqrtd.norm_def]

lemma row_sq_le (r : ℕ) (f : ℕ → ℤ) (n : ℤ) (h : ∀ d, f d ^ 2 ≤ n) :
    (∑ d ∈ range r, |f d|) ^ 2 ≤ (r : ℤ) ^ 2 * n := by
  have := sq_sum_le_card_mul_sum_sq (s := range r) (f := fun d => |f d|)
  simp only [card_range, sq_abs] at this
  have h2 : ∑ d ∈ range r, f d ^ 2 ≤ ∑ _d ∈ range r, n := sum_le_sum fun d _ => h d
  simp only [sum_const, card_range, nsmul_eq_mul] at h2
  have hr : (0 : ℤ) ≤ r := by positivity
  nlinarith

/-- `(max_j ‖A_j(B)‖₁)² ≤ r² N(Ω_{r-1})`. -/
lemma normA_sq_le (s B : ℕ) :
    normA s B ^ 2 ≤ ((s - 2 : ℕ) : ℤ) ^ 2 * (gaussOmega (cG B) (s - 3)).norm := by
  have key : ∀ i : Fin 2, (∑ d ∈ range (s - 2), |AG s B i d|) ^ 2 ≤
      ((s - 2 : ℕ) : ℤ) ^ 2 * (gaussOmega (cG B) (s - 3)).norm := by
    intro i
    apply row_sq_le
    intro d
    have hn := norm_gcol_le (s - 2) (cG B) d
    rw [show s - 2 - 1 = s - 3 by omega] at hn
    fin_cases i
    · simp only [Fin.zero_eta, AG_zero]; exact (re_sq_le_norm _).trans hn
    · simp only [Fin.mk_one, AG_one]; exact (im_sq_le_norm _).trans hn
  unfold normA
  rcases le_total (∑ d ∈ range (s - 2), |AG s B 0 d|) (∑ d ∈ range (s - 2), |AG s B 1 d|) with h | h
  · rw [max_eq_right h]; exact key 1
  · rw [max_eq_left h]; exact key 0

/-! ### The parameters `c_j` -/

lemma cG_zero (B : ℕ) : cG B 0 = ((Nat.sqrt (2 * B ^ 2) + 1 : ℕ) : ℤ) := by simp [cG]
lemma cG_pos' (B j : ℕ) (hj : j ≠ 0) : cG B j = ((Nat.sqrt B + 1 : ℕ) : ℤ) := by simp [cG, hj]

lemma cG_pos (B j : ℕ) : 0 < cG B j := by unfold cG; split_ifs <;> positivity

/-- `c_0² > 2 B²`. -/
lemma cG0_sq_gt (B : ℕ) : 2 * (B : ℤ) ^ 2 < cG B 0 ^ 2 := by
  rw [cG_zero]
  have := Nat.lt_succ_sqrt' (2 * B ^ 2)
  exact_mod_cast this

/-- `c_0 ≤ 2 B + 1`. -/
lemma cG0_le (B : ℕ) : cG B 0 ≤ 2 * B + 1 := by
  rw [cG_zero]
  have : Nat.sqrt (2 * B ^ 2) ≤ 2 * B := by
    have := Nat.sqrt_lt'.mpr (show 2 * B ^ 2 < (2 * B + 1) ^ 2 by ring_nf; nlinarith [Nat.zero_le B])
    omega
  push_cast; omega

/-- `c_j² > B` for `j ≥ 1`. -/
lemma cGj_sq_gt (B j : ℕ) (hj : j ≠ 0) : (B : ℤ) < cG B j ^ 2 := by
  rw [cG_pos' B j hj]
  have := Nat.lt_succ_sqrt' B
  exact_mod_cast this

/-- `c_j ≤ B + 1` and `c_j ≥ 2` for `j ≥ 1`, `B ≥ 1`. -/
lemma cGj_le (B j : ℕ) (hj : j ≠ 0) : cG B j ≤ B + 1 := by
  rw [cG_pos' B j hj]; have := Nat.sqrt_le_self B; push_cast; omega

lemma cGj_ge (B j : ℕ) (hj : j ≠ 0) (hB : 1 ≤ B) : 2 ≤ cG B j := by
  rw [cG_pos' B j hj]
  have : 1 ≤ Nat.sqrt B := Nat.le_sqrt.mpr (by omega)
  push_cast; omega

/-- `c_j ≤ c_0`. -/
lemma cGj_le_cG0 (B j : ℕ) : cG B j ≤ cG B 0 := by
  by_cases hj : j = 0
  · subst hj; rfl
  · rw [cG_pos' B j hj, cG_zero]
    have : Nat.sqrt B ≤ Nat.sqrt (2 * B ^ 2) := Nat.sqrt_le_sqrt (by nlinarith)
    exact_mod_cast Nat.succ_le_succ this

/-- `c_j² + 1 ≤ 5 B` for `j ≥ 1` (`B ≥ 1`). -/
lemma cGj_sq_le (B j : ℕ) (hj : j ≠ 0) (hB : 1 ≤ B) : cG B j ^ 2 + 1 ≤ 5 * B := by
  rw [cG_pos' B j hj]
  have h1 := Nat.sqrt_le' B
  have h2 := Nat.sqrt_le_self B
  have : (Nat.sqrt B + 1) ^ 2 + 1 ≤ 5 * B := by nlinarith
  exact_mod_cast this

/-- `N(Ω_{l+1}) = (c_0² + 1) ∏_{1 ≤ j ≤ l} (c_j² + 1)`, with all `c_j = c_1` for `j ≥ 1`. -/
lemma norm_gaussOmega_cG (B l : ℕ) :
    (gaussOmega (cG B) (l + 1)).norm = (cG B 0 ^ 2 + 1) * (cG B 1 ^ 2 + 1) ^ l := by
  rw [norm_gaussOmega, prod_range_succ']
  have : ∀ j ∈ range l, cG B (j + 1) ^ 2 + 1 = cG B 1 ^ 2 + 1 := by
    intro j _; rw [cG_pos' B (j + 1) (by omega), cG_pos' B 1 (by omega)]
  rw [prod_congr rfl this, prod_const, card_range]; ring

/-- `N(Ω_{r-1}) ≥ 2 B^r` (`r = l + 2`). -/
lemma norm_gaussOmega_ge (B l : ℕ) :
    2 * (B : ℤ) ^ (l + 2) ≤ (gaussOmega (cG B) (l + 1)).norm := by
  rw [norm_gaussOmega_cG]
  have h0 := cG0_sq_gt B
  have h1 : (B : ℤ) ≤ cG B 1 ^ 2 + 1 := by have := cGj_sq_gt B 1 (by omega); omega
  have h2 : (B : ℤ) ^ l ≤ (cG B 1 ^ 2 + 1) ^ l := pow_le_pow_left₀ (by positivity) h1 l
  have h3 : 2 * (B : ℤ) ^ 2 ≤ cG B 0 ^ 2 + 1 := by omega
  calc 2 * (B : ℤ) ^ (l + 2) = (2 * (B : ℤ) ^ 2) * (B : ℤ) ^ l := by ring
    _ ≤ (cG B 0 ^ 2 + 1) * (cG B 1 ^ 2 + 1) ^ l :=
      mul_le_mul h3 h2 (by positivity) (by positivity)

/-- `N(Ω_{r-1}) ≤ 10 · 5^(r-2) · B^r` (`r = l + 2`, `B ≥ 1`). -/
lemma norm_gaussOmega_le (B l : ℕ) (hB : 1 ≤ B) :
    (gaussOmega (cG B) (l + 1)).norm ≤ 10 * 5 ^ l * (B : ℤ) ^ (l + 2) := by
  rw [norm_gaussOmega_cG]
  have h0 := cG0_le B
  have h0' := cG_pos B 0
  have hB' : (1 : ℤ) ≤ B := by exact_mod_cast hB
  have h3 : cG B 0 ^ 2 + 1 ≤ 10 * (B : ℤ) ^ 2 := by nlinarith
  have h1 : cG B 1 ^ 2 + 1 ≤ 5 * (B : ℤ) := by exact_mod_cast cGj_sq_le B 1 (by omega) hB
  have h2 : (cG B 1 ^ 2 + 1) ^ l ≤ (5 * (B : ℤ)) ^ l :=
    pow_le_pow_left₀ (by positivity) h1 l
  calc (cG B 0 ^ 2 + 1) * (cG B 1 ^ 2 + 1) ^ l ≤ (10 * (B : ℤ) ^ 2) * (5 * (B : ℤ)) ^ l :=
        mul_le_mul h3 h2 (by positivity) (by positivity)
    _ = 10 * 5 ^ l * (B : ℤ) ^ (l + 2) := by ring

/-! ### `B(p)` -/

lemma Bp_le (s p : ℕ) : Bp s p ≤ p := Nat.findGreatest_le p

lemma Bp_spec (s p : ℕ) (h : 1 ≤ Bp s p) :
    ((Bp s p : ℕ) : ℤ) * (1 + normA s (Bp s p)) < p :=
  (Nat.findGreatest_of_ne_zero (P := fun B => 1 ≤ B ∧ (B : ℤ) * (1 + normA s B) < p) rfl
    (Nat.one_le_iff_ne_zero.mp h)).2

lemma le_Bp (s p B : ℕ) (hB : 1 ≤ B) (h : (B : ℤ) * (1 + normA s B) < p) : B ≤ Bp s p := by
  have hBp : B ≤ p := by
    have := normA_nonneg s B
    have : (B : ℤ) ≤ B * (1 + normA s B) := by nlinarith
    omega
  exact Nat.le_findGreatest hBp ⟨hB, h⟩

lemma Bp_max (s p B : ℕ) (hB : Bp s p < B) (hBp : B ≤ p) :
    p ≤ (B : ℤ) * (1 + normA s B) := by
  have := Nat.findGreatest_is_greatest (P := fun B => 1 ≤ B ∧ (B : ℤ) * (1 + normA s B) < p) hB hBp
  simp only [not_and, not_lt] at this
  exact this (by omega)

lemma Bp_lt (s p : ℕ) (hp : 1 ≤ p) : Bp s p < p := by
  rcases Nat.eq_zero_or_pos (Bp s p) with h | h
  · omega
  · have := Bp_spec s p h
    have := normA_nonneg s (Bp s p)
    have : ((Bp s p : ℕ) : ℤ) ≤ (Bp s p) * (1 + normA s (Bp s p)) := by nlinarith
    omega

end SkG

theorem Bp_mono (s p p' : ℕ) (h : p ≤ p') : Bp s p ≤ Bp s p' := by
  rcases Nat.eq_zero_or_pos (Bp s p) with h0 | h0
  · omega
  · exact SkG.le_Bp s p' _ h0 (lt_of_lt_of_le (SkG.Bp_spec s p h0) (by exact_mod_cast h))

end Z3NetF.Proofs

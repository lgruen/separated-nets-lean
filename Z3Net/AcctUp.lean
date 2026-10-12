/-
`rem:accounting` (first-order accounting), the upper bound for `K_eff`: the lower bound for `δN^{1/5}` by `lem:R2`
and (Λ), of the manuscript *Low-discrepancy quasi-uniform digital nets in every dimension*
(`paper/core.tex`). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.AcctDefs
public import Z3Net.R2Sep
public import Z3Net.HalfSep
public import Z3Net.TDEnum

@[expose] public section

/-!
# V14 stage S13′: `rem:accounting`, the lower bound for `δN^{1/5}` (`limsup K_eff ≤ dj`)

* `sepN` is a minimum over the pairs (`sepN_le`, `le_sepN`, `sepN_attained`).
* The options of `lem:R2` on a binding step (`bind_opt`, the case analysis of the printed proof): every option of
  coordinate `c` has absolute value at least `p² − p (2dr_c(E) + 2[c harmful]) − 2|v_c|` (doubled), where for
  `E_c = 0` the longer first-digit option with a harmful wrap is not shorter because `|2β_c| ≥ 1`.
* On the other steps every option is at least `p² · 2ℓ_c(E) − p(|2β_c| + 2)` (`gen_opt_odd`, `gen_opt_even`).
* Summed: `∑_c (2b_c)² ≥ 5p⁴ − 2p³ · 2dj − C p²` on every step for `p ≥ P` (`sum_bR2_ge`), with (Λ) on the
  non-binding steps; then `LB₂(p) ≥ (√5/2)(1 − 2dj/(5p)) − C'/p²` (`LB2R_ge`) and `lem:R2` (`R2_sep_core`).
-/

namespace Z3NetHL.Proofs.Acct

open Finset Matrix Z3NetHL Z3NetHL.Proofs

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

/-! ## `sepN` is a minimum -/

/-- The value of a pair in `sepN`. -/
def pairVal (p : ℕ) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) (x y : Fin (5 * 1) → ZMod p) : ℝ :=
  (p : ℝ) * Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℝ) / (p : ℝ) ^ (5 * 1)) ^ 2)

lemma pairVal_nonneg (p : ℕ) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) (x y : Fin (5 * 1) → ZMod p) :
    0 ≤ pairVal p X x y := by
  unfold pairVal; positivity

lemma sepN_eq (p : ℕ) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) :
    sepN p X = ⨅ xy : {xy : (Fin (5 * 1) → ZMod p) × (Fin (5 * 1) → ZMod p) // xy.1 ≠ xy.2},
      pairVal p X xy.1.1 xy.1.2 := rfl

lemma sepN_le (p : ℕ) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) (x y : Fin (5 * 1) → ZMod p) (hxy : x ≠ y) :
    sepN p X ≤ pairVal p X x y := by
  rw [sepN_eq]
  exact ciInf_le (f := fun xy : {xy : (Fin (5 * 1) → ZMod p) × (Fin (5 * 1) → ZMod p) // xy.1 ≠ xy.2} =>
    pairVal p X xy.1.1 xy.1.2) ⟨0, fun _ ⟨_, h⟩ => h ▸ pairVal_nonneg _ _ _ _⟩ ⟨(x, y), hxy⟩

lemma pairs_nonempty (p : ℕ) (hp : 2 ≤ p) :
    Nonempty {xy : (Fin (5 * 1) → ZMod p) × (Fin (5 * 1) → ZMod p) // xy.1 ≠ xy.2} := by
  have : Fact (1 < p) := ⟨by omega⟩
  refine ⟨⟨(0, fun _ => 1), fun h => ?_⟩⟩
  have := congrFun h 0
  simp at this

lemma le_sepN (p : ℕ) (hp : 2 ≤ p) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) (L : ℝ)
    (h : ∀ x y : Fin (5 * 1) → ZMod p, x ≠ y → L ≤ pairVal p X x y) : L ≤ sepN p X := by
  have := pairs_nonempty p hp
  rw [sepN_eq]
  exact le_ciInf fun xy => h _ _ xy.2

lemma sepN_attained (p : ℕ) (hp : 2 ≤ p) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) :
    ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧ sepN p X = pairVal p X x y := by
  have := pairs_nonempty p hp
  have : NeZero p := ⟨by omega⟩
  obtain ⟨xy, hxy⟩ := Finite.exists_min (fun xy : {xy : (Fin (5 * 1) → ZMod p) × (Fin (5 * 1) → ZMod p) //
    xy.1 ≠ xy.2} => pairVal p X xy.1.1 xy.1.2)
  refine ⟨xy.1.1, xy.1.2, xy.2, le_antisymm (sepN_le p X _ _ xy.2) ?_⟩
  exact le_sepN p hp X _ fun x y h => hxy ⟨(x, y), h⟩

/-- `N^{-1/5} = 1/p` turns the separation statements of S11′ into bounds for `pairVal`. -/
lemma pairVal_eq (p : ℕ) (hp : 1 ≤ p) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) (x y : Fin (5 * 1) → ZMod p)
    (L : ℝ) (h : L * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) ≤
      Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℝ) / (p : ℝ) ^ (5 * 1)) ^ 2)) :
    L ≤ pairVal p X x y := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have e := Npow_eq 5 p 1 (by norm_num) hp
  rw [show ((5 : ℕ) : ℝ) = (5 : ℝ) by norm_num] at e
  rw [e, pow_one, mul_one_div] at h
  unfold pairVal
  rw [div_le_iff₀ hp0] at h
  linarith

/-! ## The options on a binding step -/

set_option maxHeartbeats 1000000 in
lemma bind_opt_0 (p e B v t2 u : ℤ) (hp : 0 < p) (he : e = -1 ∨ e = 0 ∨ e = 1)
    (hBp : |B| + 2 ≤ p) (hvp : -p < v ∧ v < p) (ht : t2 = B + p ∨ t2 = B - p)
    (hu : u = v ∨ u = v - p * Int.sign v) (hb : B < 0) (hv : v < 0) :
    p ^ 2 - p * ((if e = 0 then |B| else -(e * B)) +
      2 * (if v ≠ 0 ∧ Int.sign v = (if e = 0 then -Int.sign B else e) then 1 else 0)) - 2 * |v|
      ≤ |2 * p ^ 2 * e + p * t2 + 2 * u| := by
  have hsB : Int.sign B = -1 := Int.sign_eq_neg_one_of_neg hb
  have hsv : Int.sign v = -1 := Int.sign_eq_neg_one_of_neg hv
  rw [abs_of_neg hv]
  rw [le_abs, abs_of_neg hb] at *
  rcases he with rfl | rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp only [hsB, hsv, Int.sign_zero, mul_zero, sub_zero, abs_zero] <;> split_ifs <;>
    first
    | (left; nlinarith)
    | (right; nlinarith)
    | (exfalso; simp_all)

set_option maxHeartbeats 1000000 in
lemma bind_opt_1 (p e B v t2 u : ℤ) (hp : 0 < p) (he : e = -1 ∨ e = 0 ∨ e = 1)
    (hBp : |B| + 2 ≤ p) (hvp : -p < v ∧ v < p) (ht : t2 = B + p ∨ t2 = B - p)
    (hu : u = v ∨ u = v - p * Int.sign v) (hb : B < 0) (hv : v = 0) :
    p ^ 2 - p * ((if e = 0 then |B| else -(e * B)) +
      2 * (if v ≠ 0 ∧ Int.sign v = (if e = 0 then -Int.sign B else e) then 1 else 0)) - 2 * |v|
      ≤ |2 * p ^ 2 * e + p * t2 + 2 * u| := by
  have hsB : Int.sign B = -1 := Int.sign_eq_neg_one_of_neg hb
  subst hv
  rw [le_abs, abs_of_neg hb] at *
  rcases he with rfl | rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp only [hsB, Int.sign_zero, mul_zero, sub_zero, abs_zero] <;> split_ifs <;>
    first
    | (left; nlinarith)
    | (right; nlinarith)
    | (exfalso; simp_all)

set_option maxHeartbeats 1000000 in
lemma bind_opt_2 (p e B v t2 u : ℤ) (hp : 0 < p) (he : e = -1 ∨ e = 0 ∨ e = 1)
    (hBp : |B| + 2 ≤ p) (hvp : -p < v ∧ v < p) (ht : t2 = B + p ∨ t2 = B - p)
    (hu : u = v ∨ u = v - p * Int.sign v) (hb : B < 0) (hv : 0 < v) :
    p ^ 2 - p * ((if e = 0 then |B| else -(e * B)) +
      2 * (if v ≠ 0 ∧ Int.sign v = (if e = 0 then -Int.sign B else e) then 1 else 0)) - 2 * |v|
      ≤ |2 * p ^ 2 * e + p * t2 + 2 * u| := by
  have hsB : Int.sign B = -1 := Int.sign_eq_neg_one_of_neg hb
  have hsv : Int.sign v = 1 := Int.sign_eq_one_of_pos hv
  rw [abs_of_pos hv]
  rw [le_abs, abs_of_neg hb] at *
  rcases he with rfl | rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp only [hsB, hsv, Int.sign_zero, mul_zero, sub_zero, abs_zero] <;> split_ifs <;>
    first
    | (left; nlinarith)
    | (right; nlinarith)
    | (exfalso; simp_all)

set_option maxHeartbeats 1000000 in
lemma bind_opt_3 (p e B v t2 u : ℤ) (hp : 0 < p) (he : e = -1 ∨ e = 0 ∨ e = 1)
    (hBp : |B| + 2 ≤ p) (hvp : -p < v ∧ v < p) (ht : t2 = B + p ∨ t2 = B - p)
    (hu : u = v ∨ u = v - p * Int.sign v) (hb : 0 < B) (hv : v < 0) :
    p ^ 2 - p * ((if e = 0 then |B| else -(e * B)) +
      2 * (if v ≠ 0 ∧ Int.sign v = (if e = 0 then -Int.sign B else e) then 1 else 0)) - 2 * |v|
      ≤ |2 * p ^ 2 * e + p * t2 + 2 * u| := by
  have hsB : Int.sign B = 1 := Int.sign_eq_one_of_pos hb
  have hsv : Int.sign v = -1 := Int.sign_eq_neg_one_of_neg hv
  rw [abs_of_neg hv]
  rw [le_abs, abs_of_pos hb] at *
  rcases he with rfl | rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp only [hsB, hsv, Int.sign_zero, mul_zero, sub_zero, abs_zero] <;> split_ifs <;>
    first
    | (left; nlinarith)
    | (right; nlinarith)
    | (exfalso; simp_all)

set_option maxHeartbeats 1000000 in
lemma bind_opt_4 (p e B v t2 u : ℤ) (hp : 0 < p) (he : e = -1 ∨ e = 0 ∨ e = 1)
    (hBp : |B| + 2 ≤ p) (hvp : -p < v ∧ v < p) (ht : t2 = B + p ∨ t2 = B - p)
    (hu : u = v ∨ u = v - p * Int.sign v) (hb : 0 < B) (hv : v = 0) :
    p ^ 2 - p * ((if e = 0 then |B| else -(e * B)) +
      2 * (if v ≠ 0 ∧ Int.sign v = (if e = 0 then -Int.sign B else e) then 1 else 0)) - 2 * |v|
      ≤ |2 * p ^ 2 * e + p * t2 + 2 * u| := by
  have hsB : Int.sign B = 1 := Int.sign_eq_one_of_pos hb
  subst hv
  rw [le_abs, abs_of_pos hb] at *
  rcases he with rfl | rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp only [hsB, Int.sign_zero, mul_zero, sub_zero, abs_zero] <;> split_ifs <;>
    first
    | (left; nlinarith)
    | (right; nlinarith)
    | (exfalso; simp_all)

set_option maxHeartbeats 1000000 in
lemma bind_opt_5 (p e B v t2 u : ℤ) (hp : 0 < p) (he : e = -1 ∨ e = 0 ∨ e = 1)
    (hBp : |B| + 2 ≤ p) (hvp : -p < v ∧ v < p) (ht : t2 = B + p ∨ t2 = B - p)
    (hu : u = v ∨ u = v - p * Int.sign v) (hb : 0 < B) (hv : 0 < v) :
    p ^ 2 - p * ((if e = 0 then |B| else -(e * B)) +
      2 * (if v ≠ 0 ∧ Int.sign v = (if e = 0 then -Int.sign B else e) then 1 else 0)) - 2 * |v|
      ≤ |2 * p ^ 2 * e + p * t2 + 2 * u| := by
  have hsB : Int.sign B = 1 := Int.sign_eq_one_of_pos hb
  have hsv : Int.sign v = 1 := Int.sign_eq_one_of_pos hv
  rw [abs_of_pos hv]
  rw [le_abs, abs_of_pos hb] at *
  rcases he with rfl | rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp only [hsB, hsv, Int.sign_zero, mul_zero, sub_zero, abs_zero] <;> split_ifs <;>
    first
    | (left; nlinarith)
    | (right; nlinarith)
    | (exfalso; simp_all)

/-- **The options on a binding step** (the case analysis of the proof of `rem:accounting`): for `E_c ∈ {-1, 0, 1}`,
odd `B = 2β_c`, `p ≥ |B| + 2`, `|v| < p`, every first-digit option `2t ∈ {B + p, B − p}` and second-digit option
`u ∈ {v, v − p sgn v}` has `|2p²E_c + p·2t + 2u| ≥ p² − p (2dr_c(E) + 2[c harmful]) − 2|v|`. -/
lemma bind_opt (p e B v t2 u : ℤ) (hp : 0 < p) (he : e = -1 ∨ e = 0 ∨ e = 1) (hB : Odd B)
    (hBp : |B| + 2 ≤ p) (hvp : |v| < p) (ht : t2 = B + p ∨ t2 = B - p)
    (hu : u = v ∨ u = v - p * Int.sign v) :
    p ^ 2 - p * ((if e = 0 then |B| else -(e * B)) +
      2 * (if v ≠ 0 ∧ Int.sign v = (if e = 0 then -Int.sign B else e) then 1 else 0)) - 2 * |v|
      ≤ |2 * p ^ 2 * e + p * t2 + 2 * u| := by
  have hB0 : B ≠ 0 := by rintro rfl; exact absurd hB (by decide)
  rw [abs_lt] at hvp
  rcases lt_or_gt_of_ne hB0 with hb | hb <;> rcases lt_trichotomy v 0 with hv | hv | hv
  exacts [bind_opt_0 p e B v t2 u hp he hBp hvp ht hu hb hv, bind_opt_1 p e B v t2 u hp he hBp hvp ht hu hb hv,
    bind_opt_2 p e B v t2 u hp he hBp hvp ht hu hb hv, bind_opt_3 p e B v t2 u hp he hBp hvp ht hu hb hv,
    bind_opt_4 p e B v t2 u hp he hBp hvp ht hu hb hv, bind_opt_5 p e B v t2 u hp he hBp hvp ht hu hb hv]

/-! ## The options on any step -/

lemma abs_u_le (p v u : ℤ) (hvp : |v| < p) (hu : u = v ∨ u = v - p * Int.sign v) : |u| ≤ p := by
  rcases hu with h | h <;> subst u
  · exact hvp.le
  · rw [abs_lt] at hvp
    rcases lt_trichotomy v 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h, abs_le]; constructor <;> linarith
    · subst h; simp; linarith
    · rw [Int.sign_eq_one_of_pos h, abs_le]; constructor <;> linarith

lemma gen_opt_core (p g B u : ℤ) (hp : 0 < p) (hu : |u| ≤ p) :
    p ^ 2 * |g| - p * (|B| + 2) ≤ |p ^ 2 * g + p * B + 2 * u| := by
  have h1 : |p ^ 2 * g| ≤ |p ^ 2 * g + p * B + 2 * u| + |p * B| + |2 * u| := by
    have := abs_sub_le (p ^ 2 * g) (p ^ 2 * g + p * B + 2 * u) 0
    have h2 := abs_add_le (p * B) (2 * u)
    rw [show p ^ 2 * g - (p ^ 2 * g + p * B + 2 * u) = -(p * B + 2 * u) by ring, abs_neg,
      sub_zero, show p ^ 2 * g + p * B + 2 * u - 0 = p ^ 2 * g + p * B + 2 * u by ring] at this
    linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < p ^ 2), abs_mul, abs_of_pos hp, abs_mul,
    abs_two] at h1
  nlinarith

/-- Every option of `lem:R2` on a step with `σ_E` odd: `|2p²E_c + p·2t + 2u| ≥ p² min(|2E_c+1|, |2E_c−1|) − p(|B|+2)`. -/
lemma gen_opt_odd (p e B v t2 u : ℤ) (hp : 0 < p) (hvp : |v| < p) (ht : t2 = B + p ∨ t2 = B - p)
    (hu : u = v ∨ u = v - p * Int.sign v) :
    p ^ 2 * min |2 * e + 1| |2 * e - 1| - p * (|B| + 2) ≤ |2 * p ^ 2 * e + p * t2 + 2 * u| := by
  have hu' := abs_u_le p v u hvp hu
  rcases ht with h | h <;> subst t2
  · have := gen_opt_core p (2 * e + 1) B u hp hu'
    have hm := min_le_left |2 * e + 1| |2 * e - 1|
    rw [show 2 * p ^ 2 * e + p * (B + p) + 2 * u = p ^ 2 * (2 * e + 1) + p * B + 2 * u by ring]
    nlinarith
  · have := gen_opt_core p (2 * e - 1) B u hp hu'
    have hm := min_le_right |2 * e + 1| |2 * e - 1|
    rw [show 2 * p ^ 2 * e + p * (B - p) + 2 * u = p ^ 2 * (2 * e - 1) + p * B + 2 * u by ring]
    nlinarith

/-- Every option on a step with `σ_E` even: `≥ p² min(|2E_c|, |2E_c − 2 sgn B|) − p(|B|+2)`. -/
lemma gen_opt_even (p e B v t2 u : ℤ) (hp : 0 < p) (hvp : |v| < p)
    (ht : t2 = B ∨ t2 = B - 2 * p * Int.sign B) (hu : u = v ∨ u = v - p * Int.sign v) :
    p ^ 2 * min |2 * e| |2 * e - 2 * Int.sign B| - p * (|B| + 2) ≤ |2 * p ^ 2 * e + p * t2 + 2 * u| := by
  have hu' := abs_u_le p v u hvp hu
  rcases ht with h | h <;> subst t2
  · have := gen_opt_core p (2 * e) B u hp hu'
    have hm := min_le_left |2 * e| |2 * e - 2 * Int.sign B|
    rw [show 2 * p ^ 2 * e + p * B + 2 * u = p ^ 2 * (2 * e) + p * B + 2 * u by ring]
    nlinarith
  · have := gen_opt_core p (2 * e - 2 * Int.sign B) B u hp hu'
    have hm := min_le_right |2 * e| |2 * e - 2 * Int.sign B|
    rw [show 2 * p ^ 2 * e + p * (B - 2 * p * Int.sign B) + 2 * u =
      p ^ 2 * (2 * e - 2 * Int.sign B) + p * B + 2 * u by ring]
    nlinarith

/-! ## The per-coordinate bounds for `2b_c` -/

lemma bR2_ge_odd (q : ℕ) (F2 D1 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) (hs : (∑ d, E d) % 2 = 1)
    (L : ℤ) (h : ∀ t2 u : ℤ, (t2 = dotR F2 E c + q ∨ t2 = dotR F2 E c - q) →
      (u = dotR D1 E c ∨ u = dotR D1 E c - q * Int.sign (dotR D1 E c)) →
      L ≤ |2 * (q : ℤ) ^ 2 * E c + q * t2 + 2 * u|) :
    L - 2 ≤ bR2 q F2 D1 E c := by
  unfold bR2 oR2
  simp only [hs, ↓reduceIte]
  refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;> refine le_max_of_le_right ?_ <;>
    linarith [h _ _ (Or.inl rfl) (Or.inl rfl), h _ _ (Or.inl rfl) (Or.inr rfl),
      h _ _ (Or.inr rfl) (Or.inl rfl), h _ _ (Or.inr rfl) (Or.inr rfl)]

lemma bR2_ge_even (q : ℕ) (F2 D1 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) (hs : ¬ (∑ d, E d) % 2 = 1)
    (L : ℤ) (h : ∀ t2 u : ℤ, (t2 = dotR F2 E c ∨ t2 = dotR F2 E c - 2 * q * Int.sign (dotR F2 E c)) →
      (u = dotR D1 E c ∨ u = dotR D1 E c - q * Int.sign (dotR D1 E c)) →
      L ≤ |2 * (q : ℤ) ^ 2 * E c + q * t2 + 2 * u|) :
    L - 2 ≤ bR2 q F2 D1 E c := by
  unfold bR2 oR2
  simp only [hs, ↓reduceIte]
  refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;> refine le_max_of_le_right ?_ <;>
    linarith [h _ _ (Or.inl rfl) (Or.inl rfl), h _ _ (Or.inl rfl) (Or.inr rfl),
      h _ _ (Or.inr rfl) (Or.inl rfl), h _ _ (Or.inr rfl) (Or.inr rfl)]

/-- `2β_c = (F2 E)_c ≡ σ_E (mod 2)` for odd `F2`. -/
lemma dotR_parity (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (E : Fin 5 → ℤ) (c : Fin 5) :
    Even (dotR F2 E c - ∑ d, E d) := by
  unfold dotR; rw [← sum_sub_distrib]
  refine Finset.even_sum _ fun d _ => ?_
  obtain ⟨a, ha⟩ := hodd c d
  exact ⟨a * E d, by rw [ha]; ring⟩

lemma dotR_odd_of_bind (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (E : Fin 5 → ℤ)
    (hs : (∑ d, E d) % 2 = 1) (c : Fin 5) : Odd (dotR F2 E c) := by
  have hE : Odd (∑ d, E d) := Int.odd_iff.mpr hs
  have : dotR F2 E c = (dotR F2 E c - ∑ d, E d) + ∑ d, E d := by ring
  rw [this]; exact (dotR_parity F2 hodd E c).add_odd hE

/-- The harmful indicator of coordinate `c`. -/
def harmI (F2 D1 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) : ℤ :=
  if dotR D1 E c ≠ 0 ∧ Int.sign (dotR D1 E c) = sgnS F2 E c then 1 else 0

/-- **Binding steps**: `2b_c ≥ p² − p (2dr_c(E) + 2[c harmful]) − 2|v_c| − 2`. -/
lemma bR2_bind (p : ℕ) (hp : 0 < p) (F2 D1 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (E : Fin 5 → ℤ) (hE : E ∈ bind5) (c : Fin 5) (hB : |dotR F2 E c| + 2 ≤ p) (hv : |dotR D1 E c| < p) :
    (p : ℤ) ^ 2 - p * (drc2 F2 E c + 2 * harmI F2 D1 E c) - 2 * |dotR D1 E c| - 2 ≤ bR2 p F2 D1 E c := by
  rw [TD.mem_bind5] at hE
  have hs : (∑ d, E d) % 2 = 1 := by rw [Fin.sum_univ_five]; exact hE.2
  have he : E c = -1 ∨ E c = 0 ∨ E c = 1 := by have := hE.1 c; omega
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  refine bR2_ge_odd p F2 D1 E c hs _ fun t2 u ht hu => ?_
  have := bind_opt p (E c) (dotR F2 E c) (dotR D1 E c) t2 u hp' he (dotR_odd_of_bind F2 hodd E hs c) hB hv ht hu
  unfold drc2 harmI sgnS
  exact this

/-- **Any step**: `2b_c ≥ p² · 2ℓ_c(E) − p(|2β_c| + 2) − 2`. -/
lemma bR2_gen (p : ℕ) (hp : 0 < p) (F2 D1 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5)
    (hv : |dotR D1 E c| < p) :
    (p : ℤ) ^ 2 * ell2 F2 E c - p * (|dotR F2 E c| + 2) - 2 ≤ bR2 p F2 D1 E c := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  unfold ell2
  split_ifs with hs
  · exact bR2_ge_odd p F2 D1 E c hs _ fun t2 u ht hu =>
      gen_opt_odd p (E c) (dotR F2 E c) (dotR D1 E c) t2 u hp' hv ht hu
  · exact bR2_ge_even p F2 D1 E c hs _ fun t2 u ht hu =>
      gen_opt_even p (E c) (dotR F2 E c) (dotR D1 E c) t2 u hp' hv ht hu

lemma ell2_nonneg (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) : 0 ≤ ell2 F2 E c := by
  unfold ell2; split_ifs <;> exact le_min (abs_nonneg _) (abs_nonneg _)

lemma ell2_le (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (hE : ∀ d, |E d| ≤ 2) (c : Fin 5) : ell2 F2 E c ≤ 5 := by
  have h := hE c
  rw [abs_le] at h
  unfold ell2; split_ifs
  · refine (min_le_left _ _).trans ?_; rw [abs_le]; constructor <;> linarith
  · refine (min_le_left _ _).trans ?_; rw [abs_le]; constructor <;> linarith

/-! ## Summed over the coordinates -/

lemma sum_harmI (F2 D1 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) :
    ∑ c, (drc2 F2 E c + 2 * harmI F2 D1 E c) = drift2E F2 E + 2 * (nHarm F2 D1 E : ℤ) := by
  unfold drift2E nHarm harmI
  rw [sum_add_distrib, ← mul_sum, card_filter]
  push_cast
  rfl

/-- On a binding step: `∑_c (2b_c)² ≥ 5p⁴ − 2p³ (2dr(E) + 2#harmful) − 10(4V+2)p²`. -/
lemma sum_bind (p : ℕ) (F2 D1 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (E : Fin 5 → ℤ) (hE : E ∈ bind5) (A V : ℤ) (hA : ∀ c, |dotR F2 E c| ≤ A) (hV : ∀ c, |dotR D1 E c| ≤ V)
    (hpA : A + 4 * V + 4 ≤ p) :
    5 * (p : ℤ) ^ 4 - 2 * p ^ 3 * (drift2E F2 E + 2 * (nHarm F2 D1 E : ℤ)) - 10 * (2 * V + 2) * p ^ 2
      ≤ ∑ c, bR2 p F2 D1 E c ^ 2 := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hp1 : (1 : ℤ) ≤ p := by linarith
  have hp : 0 < p := by exact_mod_cast hp1
  have key : ∀ c, (p : ℤ) ^ 4 - 2 * p ^ 3 * (drc2 F2 E c + 2 * harmI F2 D1 E c) - 2 * (2 * V + 2) * p ^ 2
      ≤ bR2 p F2 D1 E c ^ 2 := by
    intro c
    have hB := hA c
    have hv := hV c
    have hb := bR2_bind p hp F2 D1 hodd E hE c (by linarith) (by linarith)
    set X := drc2 F2 E c + 2 * harmI F2 D1 E c with hX
    have hX1 : X ≤ A + 2 := by
      have h1 : drc2 F2 E c ≤ |dotR F2 E c| := by
        unfold drc2; split_ifs
        · exact le_rfl
        · have := abs_mul (E c) (dotR F2 E c)
          have h2 : |E c| ≤ 1 := by
            rw [TD.mem_bind5] at hE; have := hE.1 c; rw [abs_le]; constructor <;> linarith
          have := neg_abs_le (E c * dotR F2 E c)
          nlinarith [abs_nonneg (dotR F2 E c)]
      have h3 : harmI F2 D1 E c ≤ 1 := by unfold harmI; split_ifs <;> norm_num
      linarith
    set K := 2 * |dotR D1 E c| + 2 with hK
    have hK1 : K ≤ 2 * V + 2 := by linarith
    have hpos : 0 ≤ (p : ℤ) ^ 2 - p * X - K := by nlinarith [abs_nonneg (dotR D1 E c)]
    have hb' : (p : ℤ) ^ 2 - p * X - K ≤ bR2 p F2 D1 E c := by linarith
    have hsq : ((p : ℤ) ^ 2 - p * X - K) ^ 2 ≤ bR2 p F2 D1 E c ^ 2 := pow_le_pow_left₀ hpos hb' 2
    have hK0 : 0 ≤ K := by positivity
    nlinarith [sq_nonneg ((p : ℤ) * X + K)]
  calc 5 * (p : ℤ) ^ 4 - 2 * p ^ 3 * (drift2E F2 E + 2 * (nHarm F2 D1 E : ℤ)) - 10 * (2 * V + 2) * p ^ 2
      = ∑ c : Fin 5, ((p : ℤ) ^ 4 - 2 * p ^ 3 * (drc2 F2 E c + 2 * harmI F2 D1 E c) -
          2 * (2 * V + 2) * p ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_harmI]
        simp; ring
    _ ≤ _ := Finset.sum_le_sum fun c _ => key c

/-- On a step with `∑_c (2ℓ_c)² ≥ 6`: `∑_c (2b_c)² ≥ 6p⁴ − 50 K p³` with `K = 2A + 4`. -/
lemma sum_gen (p : ℕ) (F2 D1 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (hE : ∀ d, |E d| ≤ 2)
    (A V : ℤ) (hA : ∀ c, |dotR F2 E c| ≤ A) (hV : ∀ c, |dotR D1 E c| ≤ V) (hpV : V < p) (hp1 : 1 ≤ p)
    (hl : 6 ≤ ∑ c, ell2 F2 E c ^ 2) :
    6 * (p : ℤ) ^ 4 - 50 * (A + 4) * p ^ 3 ≤ ∑ c, bR2 p F2 D1 E c ^ 2 := by
  have hp1' : (1 : ℤ) ≤ p := by exact_mod_cast hp1
  have : NeZero p := ⟨by omega⟩
  have key : ∀ c, (p : ℤ) ^ 4 * ell2 F2 E c ^ 2 - 2 * (A + 4) * p ^ 3 * 5 ≤ bR2 p F2 D1 E c ^ 2 := by
    intro c
    have hb := bR2_gen p (by omega) F2 D1 E c (by linarith [hV c])
    have hl0 := ell2_nonneg F2 E c
    have hl5 := ell2_le F2 E hE c
    have hB := hA c
    have hb0 := bR2_nonneg (p : ℕ) F2 D1 E c
    have hb2 : (p : ℤ) ^ 2 * ell2 F2 E c - (A + 4) * p ≤ bR2 p F2 D1 E c := by nlinarith
    have hA0 : 0 ≤ A := (abs_nonneg _).trans hB
    have hp3 : (0 : ℤ) ≤ (p : ℤ) ^ 3 := by positivity
    have hK : 2 * (A + 4) * p ^ 3 * ell2 F2 E c ≤ 2 * (A + 4) * p ^ 3 * 5 :=
      mul_le_mul_of_nonneg_left hl5 (by positivity)
    have hexp : ((p : ℤ) ^ 2 * ell2 F2 E c - (A + 4) * p) ^ 2 =
        (p : ℤ) ^ 4 * ell2 F2 E c ^ 2 - 2 * (A + 4) * p ^ 3 * ell2 F2 E c + ((A + 4) * p) ^ 2 := by ring
    rcases le_total 0 ((p : ℤ) ^ 2 * ell2 F2 E c - (A + 4) * p) with h | h
    · have := pow_le_pow_left₀ h hb2 2
      nlinarith [sq_nonneg ((A + 4) * (p : ℤ))]
    · have h3 : (p : ℤ) ^ 4 * ell2 F2 E c ^ 2 ≤ (A + 4) * p ^ 3 * ell2 F2 E c := by
        have e : (p : ℤ) ^ 4 * ell2 F2 E c ^ 2 - (A + 4) * p ^ 3 * ell2 F2 E c =
          ((p : ℤ) ^ 2 * ell2 F2 E c - (A + 4) * p) * ((p : ℤ) ^ 2 * ell2 F2 E c) := by ring
        have h0 : 0 ≤ (p : ℤ) ^ 2 * ell2 F2 E c := by positivity
        nlinarith [mul_nonpos_of_nonpos_of_nonneg h h0]
      have h4 : 0 ≤ (A + 4) * p ^ 3 * ell2 F2 E c := by positivity
      nlinarith [sq_nonneg (bR2 p F2 D1 E c)]
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ (univ : Finset (Fin 5))) => key c
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have h6 := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℤ) ≤ (p : ℤ) ^ 4)
  push_cast at hsum
  linarith

/-! ## Every step -/

lemma bind_sub_halfSteps (E : Fin 5 → ℤ) (hE : E ∈ bind5) : E ∈ halfSteps 5 := by
  rw [TD.mem_bind5] at hE
  refine mem_halfSteps.mpr ⟨fun d => by have := hE.1 d; rw [abs_le]; constructor <;> linarith, fun h0 => ?_⟩
  have := hE.2; rw [h0] at this; simp at this

lemma le_dj2 (F2 D1 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (hE : E ∈ bind5) :
    drift2E F2 E + 2 * (nHarm F2 D1 E : ℤ) ≤ dj2 F2 D1 :=
  Finset.le_sup' (fun E => drift2E F2 E + 2 * (nHarm F2 D1 E : ℤ)) hE

/-- **The first-order bound on every step** (with (Λ)): for `p ≥ P₀`, every `E ∈ {-2,…,2}⁵ \ {0}` has
`∑_c (2b_c)² ≥ 5p⁴ − 2p³ · 2dj − C p²`, `C = 10 (2V + 2)`, `V = 2 · max_c ∑_d |D₁[c][d]|`. -/
lemma sum_bR2_ge (F2 D1 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (hΛ : LamHyp F2) (p : ℕ)
    (hp : 2 * (halfA2 F2 : ℤ) + 4 * (2 * halfA2 D1) + 4 + 50 * (2 * halfA2 F2 + 4) + 2 * |dj2 F2 D1| + 1 ≤ p) :
    ∀ E ∈ halfSteps 5, 5 * (p : ℤ) ^ 4 - 2 * p ^ 3 * dj2 F2 D1 - 10 * (2 * (2 * halfA2 D1) + 2) * p ^ 2
      ≤ ∑ c, bR2 p F2 D1 E c ^ 2 := by
  intro E hE
  have hE2 := (mem_halfSteps.mp hE).1
  have hA : ∀ c, |dotR F2 E c| ≤ 2 * (halfA2 F2 : ℤ) := fun c => abs_beta2_le F2 E hE2 c
  have hV : ∀ c, |dotR D1 E c| ≤ 2 * (halfA2 D1 : ℤ) := fun c => abs_beta2_le D1 E hE2 c
  have hA0 : (0 : ℤ) ≤ 2 * (halfA2 F2 : ℤ) := by positivity
  have hV0 : (0 : ℤ) ≤ 2 * (halfA2 D1 : ℤ) := by positivity
  have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  have hp3 : (0 : ℤ) ≤ (p : ℤ) ^ 3 := pow_nonneg hp0 3
  have hp2 : (0 : ℤ) ≤ (p : ℤ) ^ 2 := pow_nonneg hp0 2
  generalize 2 * (halfA2 F2 : ℤ) = A at hA hA0 hp
  generalize 2 * (halfA2 D1 : ℤ) = V at hV hV0 hp ⊢
  have hdj0 := abs_nonneg (dj2 F2 D1)
  have hp1 : (1 : ℤ) ≤ p := by linarith
  by_cases hb : E ∈ bind5
  · have h := sum_bind p F2 D1 hodd E hb A V hA hV (by linarith)
    have hle := le_dj2 F2 D1 E hb
    have := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℤ) ≤ 2 * (p : ℤ) ^ 3)
    linarith
  · have hl := hΛ E hE hb
    have h := sum_gen p F2 D1 E hE2 A V hA hV (by linarith) (by exact_mod_cast hp1) (by linarith)
    have hdj := neg_abs_le (dj2 F2 D1)
    have hbig : 50 * (A + 4) * (p : ℤ) ^ 3 + 2 * p ^ 3 * |dj2 F2 D1| ≤ (p : ℤ) ^ 4 := by
      have : (50 * (A + 4) + 2 * |dj2 F2 D1|) * (p : ℤ) ^ 3 ≤ p * (p : ℤ) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) hp3
      nlinarith
    have h2 : -(2 * (p : ℤ) ^ 3 * dj2 F2 D1) ≤ 2 * p ^ 3 * |dj2 F2 D1| := by
      have := mul_le_mul_of_nonneg_left hdj (by linarith : (0 : ℤ) ≤ 2 * (p : ℤ) ^ 3)
      linarith
    have h3 : 0 ≤ 10 * (2 * V + 2) * (p : ℤ) ^ 2 := mul_nonneg (by linarith) hp2
    linarith

/-! ## Real bookkeeping -/

/-- `√(a² − u) ≥ a − u/(2a) − u²/(2a³)` for `|u| ≤ a²` (the second-order expansion of the square root). -/
lemma lower_of_sq (a X u : ℝ) (ha : 0 < a) (hX : 0 ≤ X) (h : a ^ 2 - u ≤ X ^ 2) (hu : |u| ≤ a ^ 2) :
    a - u / (2 * a) - u ^ 2 / (2 * a ^ 3) ≤ X := by
  set t := u / a ^ 2 with ht
  have ha2 : 0 < a ^ 2 := by positivity
  have hut : u = t * a ^ 2 := by rw [ht]; field_simp
  have htb : |t| ≤ 1 := by rw [ht, abs_div, abs_of_pos ha2, div_le_one ha2]; exact hu
  rw [abs_le] at htb
  have e : a - u / (2 * a) - u ^ 2 / (2 * a ^ 3) = a * (1 - t / 2 - t ^ 2 / 2) := by
    rw [hut]; field_simp; try ring
  rw [e]
  by_cases hw : a * (1 - t / 2 - t ^ 2 / 2) ≤ 0
  · linarith
  push Not at hw
  have hpoly : (1 - t / 2 - t ^ 2 / 2) ^ 2 ≤ 1 - t := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ 1 - t)) (by linarith : (0 : ℝ) ≤ 3 + t)]
  have h2 : (a * (1 - t / 2 - t ^ 2 / 2)) ^ 2 ≤ X ^ 2 := by
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left hpoly ha2.le
    have e2 : a ^ 2 * (1 - t) = a ^ 2 - u := by rw [hut]; ring
    linarith
  exact (pow_le_pow_iff_left₀ hw.le hX two_ne_zero).mp h2

/-- `√5/2 ≥ 1`. -/
lemma one_le_a : (1 : ℝ) ≤ Real.sqrt 5 / 2 := by
  have : (2 : ℝ) ≤ Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

lemma a_sq : (Real.sqrt 5 / 2) ^ 2 = 5 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- **`LB₂(p) ≥ (√5/2)(1 − 2dj/(5p)) − C'/p²`** from the integer bound on every step. -/
lemma LB2R_ge (F2 D1 : Fin 5 → Fin 5 → ℤ) (p : ℕ) (D C : ℤ) (hC : 0 ≤ C)
    (hp : |D| + C + 1 ≤ p)
    (h : ∀ E ∈ halfSteps 5, 5 * (p : ℤ) ^ 4 - 2 * p ^ 3 * D - C * p ^ 2 ≤ ∑ c, bR2 p F2 D1 E c ^ 2) :
    Real.sqrt 5 / 2 * (1 - (D : ℝ) / (5 * p)) - ((C : ℝ) / 8 + ((|D| : ℝ) / 2 + (C : ℝ) / 4) ^ 2 / 2) / p ^ 2
      ≤ LB2R p F2 D1 := by
  set a : ℝ := Real.sqrt 5 / 2 with ha
  have ha1 := one_le_a
  have ha2 := a_sq
  rw [← ha] at ha1 ha2
  have ha0 : 0 < a := by linarith
  have hp1 : (1 : ℝ) ≤ p := by
    have : (1 : ℤ) ≤ p := by linarith [abs_nonneg D]
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by linarith
  have hpR : (|D| : ℝ) + C + 1 ≤ p := by exact_mod_cast hp
  set u : ℝ := (D : ℝ) / (2 * p) + (C : ℝ) / (4 * p ^ 2) with hu
  have hDabs : |(D : ℝ)| = (|D| : ℝ) := by push_cast; rfl
  have hC0 : (0 : ℝ) ≤ C := by exact_mod_cast hC
  have hD0 : (0 : ℝ) ≤ (|D| : ℝ) := by positivity
  have hub : |u| ≤ ((|D| : ℝ) / 2 + (C : ℝ) / 4) / p := by
    rw [hu]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_div, hDabs, abs_of_pos (by positivity : (0 : ℝ) < 2 * p),
      abs_of_nonneg hC0, abs_of_pos (by positivity : (0 : ℝ) < 4 * p ^ 2)]
    have : (C : ℝ) / (4 * p ^ 2) ≤ (C : ℝ) / (4 * p) := by
      apply div_le_div_of_nonneg_left hC0 (by positivity); nlinarith
    calc (|D| : ℝ) / (2 * p) + C / (4 * p ^ 2) ≤ (|D| : ℝ) / (2 * p) + C / (4 * p) := by linarith
      _ = _ := by field_simp
  have hu1 : |u| ≤ a ^ 2 := by
    refine hub.trans ?_
    rw [div_le_iff₀ hp0, ha2]; nlinarith
  set T : ℝ := a - u / (2 * a) - u ^ 2 / (2 * a ^ 3) with hT
  -- every step is at least `T`
  have hstep : ∀ E : halfSteps 5,
      T ≤ Real.sqrt (∑ c, ((bR2 p F2 D1 (E : Fin 5 → ℤ) c : ℤ) : ℝ) ^ 2) / (2 * (p : ℝ) ^ 2) := by
    intro E
    apply lower_of_sq a _ u ha0 (by positivity) _ hu1
    have hX2 : (Real.sqrt (∑ c, ((bR2 p F2 D1 (E : Fin 5 → ℤ) c : ℤ) : ℝ) ^ 2) / (2 * (p : ℝ) ^ 2)) ^ 2 =
        (∑ c, ((bR2 p F2 D1 (E : Fin 5 → ℤ) c : ℤ) : ℝ) ^ 2) / (2 * (p : ℝ) ^ 2) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]
    rw [hX2]
    have hZ := h E.1 E.2
    have hZ' : (5 * (p : ℝ) ^ 4 - 2 * p ^ 3 * D - C * p ^ 2) ≤ ∑ c, ((bR2 p F2 D1 (E : Fin 5 → ℤ) c : ℤ) : ℝ) ^ 2 := by
      exact_mod_cast hZ
    rw [le_div_iff₀ (by positivity), hu, ha2]
    have e : (5 / 4 - ((D : ℝ) / (2 * p) + C / (4 * p ^ 2))) * (2 * (p : ℝ) ^ 2) ^ 2 =
        5 * (p : ℝ) ^ 4 - 2 * p ^ 3 * D - C * p ^ 2 := by field_simp; ring
    rw [e]; exact hZ'
  have hT2 : T ≤ 2 := by
    have h1 : -(u / (2 * a)) ≤ a / 2 := by
      have : |u / (2 * a)| ≤ a / 2 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * a), div_le_iff₀ (by positivity)]
        nlinarith
      linarith [neg_abs_le (u / (2 * a))]
    have h2 : 0 ≤ u ^ 2 / (2 * a ^ 3) := by positivity
    have ha3 : a ≤ 5 / 4 := by nlinarith
    linarith
  have hLB : T ≤ LB2R p F2 D1 := by
    unfold LB2R
    have : Nonempty (halfSteps 5) := (halfSteps_nonempty (by norm_num)).to_subtype
    exact le_min hT2 (le_ciInf hstep)
  refine le_trans ?_ hLB
  -- `T ≥ a(1 − D/(5p)) − C'/p²`
  have e1 : a - u / (2 * a) = a * (1 - (D : ℝ) / (5 * p)) - (C : ℝ) / (8 * a * p ^ 2) := by
    have h4a : 1 / (4 * a) = a / 5 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]; nlinarith [ha2]
    have : u / (2 * a) = (D : ℝ) / p * (1 / (4 * a)) + (C : ℝ) / (8 * a * p ^ 2) := by
      rw [hu]; field_simp; ring
    rw [this, h4a]; ring
  have e2 : (C : ℝ) / (8 * a * p ^ 2) ≤ (C : ℝ) / 8 / p ^ 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hC0 (by positivity); nlinarith
  have e3 : u ^ 2 / (2 * a ^ 3) ≤ ((|D| : ℝ) / 2 + (C : ℝ) / 4) ^ 2 / 2 / p ^ 2 := by
    have hu2 : u ^ 2 ≤ (((|D| : ℝ) / 2 + (C : ℝ) / 4) / p) ^ 2 := by
      rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg _) hub 2
    have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha1
    calc u ^ 2 / (2 * a ^ 3) ≤ u ^ 2 / 2 := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num); linarith
      _ ≤ (((|D| : ℝ) / 2 + (C : ℝ) / 4) / p) ^ 2 / 2 := by linarith
      _ = _ := by field_simp
  rw [hT]
  have : ((C : ℝ) / 8 + ((|D| : ℝ) / 2 + (C : ℝ) / 4) ^ 2 / 2) / p ^ 2 =
      (C : ℝ) / 8 / p ^ 2 + ((|D| : ℝ) / 2 + (C : ℝ) / 4) ^ 2 / 2 / p ^ 2 := by ring
  rw [this]
  linarith

/-! ## The bound for the net -/

lemma row1_half (p : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) :
    Row1Design 5 p (halfPhi 5 p F2 D) (fun c d => D c 1 d) := by
  intro c d r hr
  simp [halfPhi, hr]

/-- `lem:R2` for `halfNet` in terms of `sepN`: `δN^{1/5} ≥ LB₂(p)` for every odd prime `p > |2β|, |v|` on
`{-2, …, 2}⁵` (here: `p > 2 · 2 max_c ∑_d |F₀[c][d]|` and `p > 2 max_c ∑_d |D₁[c][d]|`). -/
lemma LB2R_le_sepN (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ)
    (hodd : ∀ c d, Odd (F2 c d)) (hA : 2 * halfA2 F2 < p) (hV : 2 * halfA2 (fun c d => D c 1 d) < p) :
    LB2R p F2 (fun c d => D c 1 d) ≤ sepN p (halfNet p F2 D) := by
  have hoddp : Odd p := hp.odd_of_ne_two hp2
  refine le_sepN p hp.two_le _ _ fun x y hxy => pairVal_eq p hp.one_lt.le _ x y _ ?_
  refine R2_sep_core 5 p (halfPhi 5 p F2 D) F2 (fun c d => D c 1 d) (by norm_num) hoddp
    (halfPhi_row 5 p (by norm_num) hoddp F2 D) (row1_half p F2 D) hodd
    (fun E c hE => ?_) (fun E c hE => ?_) x y hxy
  · have := abs_beta2_le F2 E hE c
    have h' : (2 * halfA2 F2 : ℤ) < p := by exact_mod_cast hA
    exact lt_of_le_of_lt this h'
  · have := abs_beta2_le (fun c d => D c 1 d) E hE c
    have h' : (2 * halfA2 (fun c d => D c 1 d) : ℤ) < p := by exact_mod_cast hV
    exact lt_of_le_of_lt this h'

/-- **`rem:accounting`, `limsup K_eff ≤ dj`** (the first half of the printed proof): under (Λ), for every prime `p ≥ P`,
`δN^{1/5} ≥ (√5/2)(1 − 2dj(F₀,D₁)/(5p)) − C/p²` (toroidal), for all deeper rows. -/
theorem acct_upper_core (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hΛ : LamHyp F2) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      Real.sqrt 5 / 2 * (1 - (dj2 F2 (fun c d => D c 1 d) : ℝ) / (5 * p)) - C / (p : ℝ) ^ 2
        ≤ sepN p (halfNet p F2 D) := by
  set D1 : Fin 5 → Fin 5 → ℤ := fun c d => D c 1 d with hD1
  set Dz : ℤ := dj2 F2 D1 with hDz
  set Cz : ℤ := 10 * (2 * (2 * (halfA2 D1 : ℤ)) + 2) with hCz
  set P0 : ℤ := 2 * (halfA2 F2 : ℤ) + 4 * (2 * halfA2 D1) + 4 + 50 * (2 * halfA2 F2 + 4) + 2 * |Dz| + 1
    with hP0
  refine ⟨(Cz : ℝ) / 8 + (|(Dz : ℝ)| / 2 + (Cz : ℝ) / 4) ^ 2 / 2, (P0 + |Dz| + Cz + 3).toNat,
    fun p hp hPp => ?_⟩
  have hA0 : (0 : ℤ) ≤ halfA2 F2 := Int.natCast_nonneg _
  have hV0 : (0 : ℤ) ≤ halfA2 D1 := Int.natCast_nonneg _
  have hCz0 : 0 ≤ Cz := by rw [hCz]; linarith
  have hdz := abs_nonneg Dz
  have hPp' : P0 + |Dz| + Cz + 3 ≤ (p : ℤ) := by
    have := Int.self_le_toNat (P0 + |Dz| + Cz + 3)
    have h2 : ((P0 + |Dz| + Cz + 3).toNat : ℤ) ≤ p := by exact_mod_cast hPp
    linarith
  have hstep := sum_bR2_ge F2 D1 hodd hΛ p (by linarith)
  have hLB := LB2R_ge F2 D1 p Dz Cz hCz0 (by linarith) hstep
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hPp'
    linarith
  refine hLB.trans (LB2R_le_sepN p hp hp2 F2 D hodd ?_ ?_)
  · have : (2 * halfA2 F2 : ℤ) < p := by linarith
    exact_mod_cast this
  · have : (2 * halfA2 D1 : ℤ) < p := by linarith
    exact_mod_cast this

end

end Z3NetHL.Proofs.Acct

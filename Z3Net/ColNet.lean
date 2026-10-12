/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColMin
public import Z3Net.FNie

@[expose] public section

/-!
# V14 stage S9′: digital column nets — steps (`lem:drift`(1), (2), (4)) and the net `𝒞_q` (`thm:col`(1))

* `step_formula`: a step along `e_i` changes the shared digit `a·n` by `a_i` and the third digit
  `ℓ·n` by `r_i` modulo `q`, so `Δ_i = q α_i + r_i - q² κ - q κ'` with the wraps `κ`, `κ'` of the two
  digits (`α_i`, `r_i` the residues of `a_i`, `ℓ_i`).
* `drift_step` (`lem:drift`(1)), `wraps_card` (`lem:drift`(2): `r_i` wraps per cycle, by summing the
  increments of the third digit around the cycle), `excess_sum` (`lem:drift`(2): under the range
  hypothesis of revision 15.1 the excesses of a cycle sum to `⅓q²w_i`), `drift_net`
  (`lem:drift`(4)).
* `colW_boxMinor`, `col_boxMinor_unit`, `col_net` (`thm:col`(1), via `lem:nie`), `col_cover`.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-! ## Steps of digital column nets -/

lemma colH_add_single (w : Fin 3 → ℤ) (n : Fin 3 → ZMod q) (i : Fin 3) (t : ZMod q) :
    colH q w (n + Pi.single i t) = colH q w n + ((colA q w i : ℤ) : ZMod q) * t := by
  unfold colH
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

lemma colJ_add_single (ℓ : Fin 3 → ℤ) (n : Fin 3 → ZMod q) (i : Fin 3) (t : ZMod q) :
    colJ q ℓ (n + Pi.single i t) = colJ q ℓ n + ((ℓ i : ℤ) : ZMod q) * t := by
  unfold colJ
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

lemma mod_wrap (h α : ℕ) (hh : h < q) (hα : α < q) :
    (((h + α) % q : ℕ) : ℤ) = h + α - q * (if h + α < q then 0 else 1) := by
  split_ifs with hl
  · rw [Nat.mod_eq_of_lt hl]; simp
  · push Not at hl
    have : (h + α) % q = h + α - q := by
      rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt (by omega)]
    rw [this]; push_cast [hl]; ring

/-- The wrap indicator `[x + y ≥ q]` of a digit `x` increased by `y`. -/
def wrapI (q x y : ℕ) : ℤ := if x + y < q then 0 else 1

lemma step_formula (w ℓ : Fin 3 → ℤ) (i : Fin 3) (n : Fin 3 → ZMod q) :
    colStep q (colPhi q w ℓ) i n =
      q * (((colA q w i : ℤ) : ZMod q).val : ℤ) + (((ℓ i : ℤ) : ZMod q).val : ℤ)
        - (q : ℤ) ^ 2 * wrapI q (colH q w n).val (((colA q w i : ℤ) : ZMod q)).val
        - q * wrapI q (colJ q ℓ n).val (((ℓ i : ℤ) : ZMod q)).val := by
  unfold colStep colPhi
  rw [colH_add_single, colJ_add_single, mul_one, mul_one, ZMod.val_add, ZMod.val_add]
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [mod_wrap _ _ (ZMod.val_lt _) (ZMod.val_lt _), mod_wrap _ _ (ZMod.val_lt _) (ZMod.val_lt _)]
  simp only [wrapI]
  ring

lemma val_cast_sub_dvd (z : ℤ) : (q : ℤ) ∣ (((z : ZMod q).val : ℕ) : ℤ) - z := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
  push_cast; simp

/-- **`lem:drift`(1)**: `Δ_i ≡ q a_i + r_i - q κ'` modulo `q²`, `κ'` the wrap of the third digit. -/
lemma drift_step (w ℓ : Fin 3 → ℤ) (i : Fin 3) (n : Fin 3 → ZMod q) :
    colStep q (colPhi q w ℓ) i n ≡
      q * colA q w i + (((ℓ i : ℤ) : ZMod q).val : ℤ) -
        q * wrapI q (colJ q ℓ n).val (((ℓ i : ℤ) : ZMod q)).val [ZMOD (q : ℤ) ^ 2] := by
  rw [step_formula]
  obtain ⟨m, hm⟩ := val_cast_sub_dvd (q := q) (colA q w i)
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact ⟨m - wrapI q (colH q w n).val (((colA q w i : ℤ) : ZMod q)).val, by
    linear_combination (q : ℤ) * hm⟩

/-! ## Cycles: the wraps of the third digit (`lem:drift`(2)) -/

lemma wraps_card (ℓ : Fin 3 → ℤ) (n : Fin 3 → ZMod q) (i : Fin 3) :
    ((univ.filter fun t : ZMod q =>
        ¬ (colJ q ℓ (n + Pi.single i t)).val + (((ℓ i : ℤ) : ZMod q)).val < q).card : ℤ) =
      (((ℓ i : ℤ) : ZMod q)).val := by
  set ρ := (((ℓ i : ℤ) : ZMod q)).val
  set f : ZMod q → ℤ := fun t => ((colJ q ℓ (n + Pi.single i t)).val : ℤ)
  have hstep : ∀ t, f (t + 1) = f t + ρ - q * wrapI q (colJ q ℓ (n + Pi.single i t)).val ρ := by
    intro t
    have hj : colJ q ℓ (n + Pi.single i (t + 1)) =
        colJ q ℓ (n + Pi.single i t) + ((ℓ i : ℤ) : ZMod q) := by
      rw [colJ_add_single, colJ_add_single]; ring
    simp only [f]
    rw [hj, ZMod.val_add, mod_wrap _ _ (ZMod.val_lt _) (ZMod.val_lt _)]
    simp only [wrapI, ρ]
  have hsum : ∑ t : ZMod q, f (t + 1) = ∑ t : ZMod q, f t :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  simp only [hstep, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  have hc : (Fintype.card (ZMod q) : ℤ) = q := by rw [ZMod.card]
  simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hw : ∑ t : ZMod q, wrapI q (colJ q ℓ (n + Pi.single i t)).val ρ =
      ((univ.filter fun t : ZMod q => ¬ (colJ q ℓ (n + Pi.single i t)).val + ρ < q).card : ℤ) := by
    simp only [wrapI]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← hw]
  have hq0 : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have : (q : ℤ) * ρ = q * ∑ t : ZMod q, wrapI q (colJ q ℓ (n + Pi.single i t)).val ρ := by
    linarith
  exact (mul_left_cancel₀ hq0.ne' this).symm

lemma abs_two (x B : ℤ) (h : 2 * |x| < B) : -B < 2 * x ∧ 2 * x < B := by
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at h <;> constructor <;> linarith

lemma two_abs_lt (x B : ℤ) (h1 : -B < 2 * x) (h2 : 2 * x < B) : 2 * |x| < B := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- The excess (times three) of a step value congruent to a representative `x₀` in the window. -/
lemma excess3_eq (Δ x₀ : ℤ) (hmod : Δ ≡ x₀ [ZMOD (q : ℤ) ^ 2])
    (h1 : -(q : ℤ) ^ 2 < 6 * x₀) (h2 : 6 * x₀ ≤ 5 * (q : ℤ) ^ 2) :
    excess3 q Δ = 3 * x₀ - q ^ 2 := by
  have hq2 : (0 : ℤ) < (q : ℤ) ^ 2 := by
    have : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    positivity
  have hr : Δ % ((q : ℤ) ^ 2) = x₀ % ((q : ℤ) ^ 2) := hmod
  unfold excess3
  rw [hr]
  rcases le_or_gt 0 x₀ with h0 | h0
  · have : x₀ % ((q : ℤ) ^ 2) = x₀ := Int.emod_eq_of_lt h0 (by linarith)
    rw [this, if_pos h2]
  · have : x₀ % ((q : ℤ) ^ 2) = x₀ + (q : ℤ) ^ 2 := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by linarith) (by linarith)]
    rw [this, if_neg (by linarith)]; ring

/-- **`lem:drift`(2)**, the excess sum: if `|ε_i| < ½q²` and `|ε_i - q| < ½q²` (in units of thirds:
`2|q w_i + 3r_i| < 3q²` and `2|q w_i + 3r_i - 3q| < 3q²`), the excesses of the steps of a cycle in
the direction `e_i` sum to `⅓q²w_i`. -/
lemma excess_sum (w ℓ : Fin 3 → ℤ) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (i : Fin 3)
    (hR : 2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val| < 3 * (q : ℤ) ^ 2 ∧
      2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q| < 3 * (q : ℤ) ^ 2)
    (n : Fin 3 → ZMod q) :
    ∑ t : ZMod q, excess3 q (colStep q (colPhi q w ℓ) i (n + Pi.single i t)) = (q : ℤ) ^ 2 * w i := by
  set ρ := (((ℓ i : ℤ) : ZMod q)).val
  have ha : 3 * colA q w i = q + w i := Int.mul_ediv_cancel' (hw3 i)
  have hex : ∀ t : ZMod q, excess3 q (colStep q (colPhi q w ℓ) i (n + Pi.single i t)) =
      q * w i + 3 * ρ - 3 * q * wrapI q (colJ q ℓ (n + Pi.single i t)).val ρ := by
    intro t
    have hwr : wrapI q (colJ q ℓ (n + Pi.single i t)).val ρ = 0 ∨
        wrapI q (colJ q ℓ (n + Pi.single i t)).val ρ = 1 := by
      unfold wrapI; split_ifs <;> simp
    have hqa : 3 * ((q : ℤ) * colA q w i) = (q : ℤ) ^ 2 + q * w i := by
      rw [show 3 * ((q : ℤ) * colA q w i) = q * (3 * colA q w i) by ring, ha]; ring
    have b1 := abs_two _ _ hR.1
    have b2 := abs_two _ _ hR.2
    rw [excess3_eq _ _ (drift_step w ℓ i _)]
    · rw [show (3 : ℤ) * (q * colA q w i + ρ - q * wrapI q (colJ q ℓ (n + Pi.single i t)).val ρ) =
        3 * (q * colA q w i) + 3 * ρ - 3 * q * wrapI q (colJ q ℓ (n + Pi.single i t)).val ρ by ring,
        hqa]; ring
    · rcases hwr with h | h <;> rw [h] <;> linarith
    · rcases hwr with h | h <;> rw [h] <;> linarith
  simp only [hex, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, ← Finset.mul_sum]
  have hw : ∑ t : ZMod q, wrapI q (colJ q ℓ (n + Pi.single i t)).val ρ = ρ := by
    rw [← wraps_card ℓ n i]
    simp only [wrapI]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hw]; ring

/-- The instance of the range hypothesis of `lem:drift`(2): `|w_i| ≤ 2` and `q ≥ 4`. -/
lemma drift_range (w ℓ : Fin 3 → ℤ) (i : Fin 3) (hw : |w i| ≤ 2) (hq : 4 ≤ q) :
    2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val| < 3 * (q : ℤ) ^ 2 ∧
      2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q| < 3 * (q : ℤ) ^ 2 := by
  have hρ := ZMod.val_lt (((ℓ i : ℤ) : ZMod q))
  have hρ' : ((((ℓ i : ℤ) : ZMod q)).val : ℤ) ≤ q - 1 := by omega
  have hρ0 : (0 : ℤ) ≤ ((((ℓ i : ℤ) : ZMod q)).val : ℤ) := by positivity
  have hw' := abs_le.1 hw
  have hq' : (4 : ℤ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have m1 := mul_le_mul_of_nonneg_left hw'.2 hq0
  have m2 := mul_le_mul_of_nonneg_left hw'.1 hq0
  constructor <;> apply two_abs_lt <;> nlinarith

/-! ## `lem:drift`(4) -/

/-- **`lem:drift`(4)**: if the digital column net is a `(0,3,3)`-net then the residues `r_i` of `ℓ`
sum to at least `q`. -/
lemma drift_net_r (hq : 2 ≤ q) (w ℓ : Fin 3 → ℤ) (hℓ : (q : ℤ) ∣ ∑ c, ℓ c)
    (hnet : IsNet0 3 q 3 (digPoint q 3 (colGenW q w ℓ))) :
    (q : ℤ) ≤ ∑ i, ((((ℓ i : ℤ) : ZMod q)).val : ℤ) := by
  have hmod : (q : ℤ) ∣ ∑ i, ((((ℓ i : ℤ) : ZMod q)).val : ℤ) := by
    have : ∑ i, ((((ℓ i : ℤ) : ZMod q)).val : ℤ) = ∑ i, ℓ i + ∑ i, (((((ℓ i : ℤ) : ZMod q)).val : ℤ) - ℓ i) := by
      rw [← Finset.sum_add_distrib]; congr 1; funext i; ring
    rw [this]
    exact dvd_add hℓ (Finset.dvd_sum fun i _ => val_cast_sub_dvd (ℓ i))
  have hpos : 0 < ∑ i, ((((ℓ i : ℤ) : ZMod q)).val : ℤ) := by
    by_contra h0
    push Not at h0
    have hz : ∀ i, (((ℓ i : ℤ) : ZMod q)) = 0 := by
      intro i
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (by positivity :
        (0 : ℤ) ≤ ((((ℓ i : ℤ) : ZMod q)).val : ℤ)))).1 (le_antisymm h0 (by positivity)) i (mem_univ _)
      have : (((ℓ i : ℤ) : ZMod q)).val = 0 := by exact_mod_cast hall
      exact (ZMod.val_eq_zero _).1 this
    have hJ : ∀ n, colJ q ℓ n = 0 := by intro n; simp [colJ, hz]
    obtain ⟨v, hv, -⟩ := hnet ![3, 0, 0] (by simp [Fin.sum_univ_three]) ![1, 0, 0]
      (by intro c; fin_cases c <;> simp <;> omega)
    have h0 := hv 0
    simp only [Matrix.cons_val_zero, Nat.sub_self, pow_zero, Nat.div_one] at h0
    rw [digPoint_colGenW] at h0
    simp only [colPt, colPhi, hJ, ZMod.val_zero, add_zero] at h0
    have : q ∣ 1 := ⟨q * (v 0).val + (colH q w v).val, by rw [← h0]; ring⟩
    have := Nat.le_of_dvd one_pos this
    omega
  obtain ⟨m, hm⟩ := hmod
  rw [hm] at hpos ⊢
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  have : 0 < m := by
    by_contra h; push Not at h; nlinarith
  nlinarith

/-! ## Box minors and the net (`thm:col`(1)) -/

lemma sum_three_cases (d : Fin 3 → ℕ) (hd : ∑ c, d c = 3) :
    d = ![3, 0, 0] ∨ d = ![0, 3, 0] ∨ d = ![0, 0, 3] ∨ d = ![2, 1, 0] ∨ d = ![2, 0, 1] ∨
      d = ![1, 2, 0] ∨ d = ![0, 2, 1] ∨ d = ![1, 0, 2] ∨ d = ![0, 1, 2] ∨ d = ![1, 1, 1] := by
  simp only [Fin.sum_univ_three] at hd
  have e : d = ![d 0, d 1, d 2] := by funext c; fin_cases c <;> rfl
  obtain ⟨a, ha⟩ : ∃ a, d 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, d 1 = b := ⟨_, rfl⟩
  have hc : d 2 = 3 - a - b := by omega
  have h0 : a ≤ 3 := by omega
  have h1 : b ≤ 3 - a := by omega
  rw [e, ha, hb, hc]
  interval_cases a <;> interval_cases b <;> decide

section box
variable {R : Type*} [Zero R] (C : Fin 3 → Matrix (Fin 3) (Fin 3) R)
lemma box300 : boxMatrix C ![3, 0, 0] = Matrix.of ![C 0 0, C 0 1, C 0 2] := by
  ext r l; fin_cases r <;> rfl
lemma box030 : boxMatrix C ![0, 3, 0] = Matrix.of ![C 1 0, C 1 1, C 1 2] := by
  ext r l; fin_cases r <;> rfl
lemma box003 : boxMatrix C ![0, 0, 3] = Matrix.of ![C 2 0, C 2 1, C 2 2] := by
  ext r l; fin_cases r <;> rfl
lemma box210 : boxMatrix C ![2, 1, 0] = Matrix.of ![C 0 0, C 0 1, C 1 0] := by
  ext r l; fin_cases r <;> rfl
lemma box201 : boxMatrix C ![2, 0, 1] = Matrix.of ![C 0 0, C 0 1, C 2 0] := by
  ext r l; fin_cases r <;> rfl
lemma box120 : boxMatrix C ![1, 2, 0] = Matrix.of ![C 0 0, C 1 0, C 1 1] := by
  ext r l; fin_cases r <;> rfl
lemma box021 : boxMatrix C ![0, 2, 1] = Matrix.of ![C 1 0, C 1 1, C 2 0] := by
  ext r l; fin_cases r <;> rfl
lemma box102 : boxMatrix C ![1, 0, 2] = Matrix.of ![C 0 0, C 2 0, C 2 1] := by
  ext r l; fin_cases r <;> rfl
lemma box012 : boxMatrix C ![0, 1, 2] = Matrix.of ![C 1 0, C 2 0, C 2 1] := by
  ext r l; fin_cases r <;> rfl
lemma box111 : boxMatrix C ![1, 1, 1] = Matrix.of ![C 0 0, C 1 0, C 2 0] := by
  ext r l; fin_cases r <;> rfl
end box

/-- The box minors of the digital column net with `ℓ = (-1, 1, 0)`: `±1`, `±a_c`, `a_x + a_y`. -/
lemma colW_boxMinor (w : Fin 3 → ℤ) (d : Fin 3 → ℕ) (hd : ∑ c, d c = 3) :
    (boxMatrix (colGenW q w ellCol) d).det ∈ ({1, ((colA q w 0 : ℤ) : ZMod q),
      -((colA q w 0 : ℤ) : ZMod q), ((colA q w 1 : ℤ) : ZMod q), -((colA q w 1 : ℤ) : ZMod q),
      -((colA q w 2 : ℤ) : ZMod q), ((colA q w 2 : ℤ) : ZMod q),
      ((colA q w 0 : ℤ) : ZMod q) + ((colA q w 1 : ℤ) : ZMod q)} : Set (ZMod q)) := by
  rcases sum_three_cases d hd with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [box300, box030, box003, box210, box201, box120, box021, box102, box012, box111] <;>
    rw [Matrix.det_fin_three] <;>
    simp [colGenW, ellCol, Pi.single_apply]

end Z3NetC.Proofs

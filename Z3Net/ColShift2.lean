/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColShift

@[expose] public section

/-!
# V14 stage S9′: every digital shift of `𝒞_q`, part (3) of `prop:colshift`

* `shift_U`: for a step `E ∈ {-1,0,1}³ \ {0}` and per-coordinate shared-digit differences
  `Δh_c ≡ a·E (mod q)`, `|Δh_c| < q`, the vector `U = qE + Δh` has `3|U|² ≥ (q - W)²`
  (`W = 2` for `q ≡ 2`, `4` for `q ≡ 1 (mod 3)`): the printed case split `σ_E = 0`, `E = ±𝟏`,
  otherwise `‖θ‖ ≥ (q - W)/(3q)`, here as `|3U_c| = |q s + w·E| ≥ q - W` with `s ≢ 0 (mod 3)`.
* `colshift_lower`: `δN^{1/3} ≥ (1 - (W+3)/q + 3/q²)/√3`; `colshift_4693`: `> 0.4693` for `q ≥ 37`.
* `arc_exists`: the arc argument of the upper bound (three residues `b_d`, not all equal; arcs of
  `a_c` consecutive residues), by explicit case analysis on the order of the residues.
* `colshift_upper`: a pair at Euclidean (hence toroidal) distance at most `√3 (q a_max + q - 1)`.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-- `W` of `prop:colshift`. -/
def Wsh (q : ℕ) : ℤ := if q % 3 = 2 then 2 else 4

lemma wE_facts (h6 : Nat.Coprime q 6) (E : Fin 3 → ℤ) (hE1 : ∀ c, -1 ≤ E c ∧ E c ≤ 1) :
    |∑ d, wCol q d * E d| ≤ 4 ∧
    ((E 0 + E 1 + E 2 = 1 ∨ E 0 + E 1 + E 2 = -2) → -Wsh q ≤ ∑ d, wCol q d * E d) ∧
    ((E 0 + E 1 + E 2 = -1 ∨ E 0 + E 1 + E 2 = 2) → ∑ d, wCol q d * E d ≤ Wsh q) := by
  have h0 := hE1 0; have h1 := hE1 1; have h2 := hE1 2
  rcases q_mod3 h6 with h | h
  · have hw : wCol q = ![-1, -1, 2] := by simp [wCol, h]
    have hW : Wsh q = 4 := by simp [Wsh, show q % 3 ≠ 2 by omega]
    simp only [hw, hW, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨abs_le.2 ⟨by omega, by omega⟩, fun _ => by omega, fun _ => by omega⟩
  · have hw : wCol q = ![-2, 1, 1] := by simp [wCol, h]
    have hW : Wsh q = 2 := by simp [Wsh, h]
    simp only [hw, hW, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨abs_le.2 ⟨by omega, by omega⟩, fun hs => by omega, fun hs => by omega⟩

lemma eq_zero_of_dvd_abs (x : ℤ) (hx : |x| < q) (hd : (q : ℤ) ∣ x) : x = 0 :=
  Int.eq_zero_of_abs_lt_dvd hd hx

lemma pair_sq (x y : ℤ) (hq : 0 < (q : ℤ)) (hx : |x| < q) (hy : |y| < q) (hd : (q : ℤ) ∣ x - y) :
    (q : ℤ) ^ 2 ≤ 2 * (((q : ℤ) + x) ^ 2 + (-(q : ℤ) + y) ^ 2) := by
  obtain ⟨m, hm⟩ := hd
  have hx' := abs_lt.1 hx; have hy' := abs_lt.1 hy
  have hm1 : -1 ≤ m := by
    by_contra hc; push Not at hc
    have : (q : ℤ) * m ≤ (q : ℤ) * (-2) := by
      apply mul_le_mul_of_nonneg_left (by omega) hq.le
    linarith
  have hAB : (q : ℤ) ≤ ((q : ℤ) + x) - (-(q : ℤ) + y) := by
    have : (q : ℤ) * (-1) ≤ (q : ℤ) * m := mul_le_mul_of_nonneg_left hm1 hq.le
    linarith
  nlinarith [sq_nonneg (((q : ℤ) + x) + (-(q : ℤ) + y))]

lemma two_coord (U : Fin 3 → ℤ) (c d : Fin 3) (hcd : c ≠ d) : U c ^ 2 + U d ^ 2 ≤ ∑ i, U i ^ 2 := by
  rw [← Finset.sum_pair (f := fun i => U i ^ 2) hcd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => sq_nonneg _)

lemma shift_U (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (E : Fin 3 → ℤ)
    (hE1 : ∀ c, -1 ≤ E c ∧ E c ≤ 1) (hE0 : E ≠ 0) (dh : Fin 3 → ℤ) (hdh : ∀ c, |dh c| < q)
    (hcong : ∀ c, (q : ℤ) ∣ dh c - ∑ d, colA q (wCol q) d * E d) :
    ((q : ℤ) - Wsh q) ^ 2 ≤ 3 * ∑ c, ((q : ℤ) * E c + dh c) ^ 2 := by
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℤ) < q := by omega
  have hW : 2 ≤ Wsh q ∧ Wsh q ≤ 4 := by unfold Wsh; split_ifs <;> norm_num
  obtain ⟨hw0, hw3, -, -⟩ := wCol_props (q := q) h6
  have ha : ∀ d, 3 * colA q (wCol q) d = q + wCol q d := fun d => Int.mul_ediv_cancel' (hw3 d)
  have hsA : ∑ d, colA q (wCol q) d = q := sum_colA q _ hw0 hw3
  have h0 := hE1 0; have h1 := hE1 1; have h2 := hE1 2
  have hE0' : E 0 ≠ 0 ∨ E 1 ≠ 0 ∨ E 2 ≠ 0 := by
    by_contra hc; push Not at hc; apply hE0; funext c; fin_cases c <;> simp [hc.1, hc.2.1, hc.2.2]
  have hWq : ((q : ℤ) - Wsh q) ^ 2 ≤ (q : ℤ) ^ 2 := by nlinarith
  have hpos : 0 ≤ ∑ c, ((q : ℤ) * E c + dh c) ^ 2 := by positivity
  rcases (show E 0 + E 1 + E 2 = 0 ∨ E 0 + E 1 + E 2 = 3 ∨ E 0 + E 1 + E 2 = -3 ∨
      (E 0 + E 1 + E 2 = 1 ∨ E 0 + E 1 + E 2 = -2) ∨ (E 0 + E 1 + E 2 = -1 ∨ E 0 + E 1 + E 2 = 2)
      by omega) with hs | hs | hs | hs | hs
  · -- `σ_E = 0`: two moving coordinates in opposite directions
    have hd : ∀ c d, (q : ℤ) ∣ dh c - dh d := fun c d => by
      have := dvd_sub (hcong c) (hcong d); simpa using this
    have gen : ∀ c d : Fin 3, c ≠ d → E c = 1 → E d = -1 →
        ((q : ℤ) - Wsh q) ^ 2 ≤ 3 * ∑ c, ((q : ℤ) * E c + dh c) ^ 2 := by
      intro c d hcd hc hd'
      have hp := pair_sq (dh c) (dh d) hq0 (hdh c) (hdh d) (hd c d)
      have ht := two_coord (fun i => (q : ℤ) * E i + dh i) c d hcd
      simp only [hc, hd', mul_one, mul_neg] at ht
      nlinarith
    rcases (show (E 0 = 1 ∧ E 1 = -1) ∨ (E 0 = 1 ∧ E 2 = -1) ∨ (E 1 = 1 ∧ E 0 = -1) ∨
        (E 1 = 1 ∧ E 2 = -1) ∨ (E 2 = 1 ∧ E 0 = -1) ∨ (E 2 = 1 ∧ E 1 = -1) by omega) with
      h | h | h | h | h | h
    · exact gen 0 1 (by decide) h.1 h.2
    · exact gen 0 2 (by decide) h.1 h.2
    · exact gen 1 0 (by decide) h.1 h.2
    · exact gen 1 2 (by decide) h.1 h.2
    · exact gen 2 0 (by decide) h.1 h.2
    · exact gen 2 1 (by decide) h.1 h.2
  · -- `E = 𝟏`
    have he : ∀ c, E c = 1 := fun c => by fin_cases c <;> simp <;> omega
    have hz : ∀ c, dh c = 0 := by
      intro c
      apply eq_zero_of_dvd_abs _ (hdh c)
      have := hcong c
      rw [Finset.sum_congr rfl (fun d _ => by rw [he d]), ← Finset.sum_mul, hsA, mul_one] at this
      simpa using dvd_add this (dvd_refl (q : ℤ))
    rw [Fin.sum_univ_three, he 0, he 1, he 2, hz 0, hz 1, hz 2]; nlinarith
  · -- `E = -𝟏`
    have he : ∀ c, E c = -1 := fun c => by fin_cases c <;> simp <;> omega
    have hz : ∀ c, dh c = 0 := by
      intro c
      apply eq_zero_of_dvd_abs _ (hdh c)
      have := hcong c
      rw [Finset.sum_congr rfl (fun d _ => by rw [he d]), ← Finset.sum_mul, hsA] at this
      have := dvd_sub this (dvd_mul_right (q : ℤ) (-1))
      simpa using this
    rw [Fin.sum_univ_three, he 0, he 1, he 2, hz 0, hz 1, hz 2]; nlinarith
  all_goals
    -- `σ_E ∈ {±1, ±2}`: `|3U_c| ≥ q - W` for every `c`
    obtain ⟨hwE, hwl, hwu⟩ := wE_facts h6 E hE1
    have key : ∀ c, ((q : ℤ) - Wsh q) ^ 2 ≤ 9 * ((q : ℤ) * E c + dh c) ^ 2 := by
      intro c
      obtain ⟨r, hr⟩ := hcong c
      have h3U : 3 * ((q : ℤ) * E c + dh c) =
          q * (E 0 + E 1 + E 2 + 3 * (E c + r)) + ∑ d, wCol q d * E d := by
        have : 3 * ∑ d, colA q (wCol q) d * E d = q * (E 0 + E 1 + E 2) + ∑ d, wCol q d * E d := by
          simp only [Fin.sum_univ_three]
          linear_combination E 0 * ha 0 + E 1 * ha 1 + E 2 * ha 2
        linear_combination 3 * hr + this
      have hb : (q : ℤ) - Wsh q ≤ |3 * ((q : ℤ) * E c + dh c)| := by
        rw [h3U]
        obtain ⟨s, hsdef⟩ : ∃ s, s = E 0 + E 1 + E 2 + 3 * (E c + r) := ⟨_, rfl⟩
        rw [← hsdef]
        have hwE' := abs_le.1 hwE
        rcases (show s ≤ -2 ∨ s = -1 ∨ s = 0 ∨ s = 1 ∨ 2 ≤ s by omega) with hs' | hs' | hs' | hs' | hs'
        · have : (q : ℤ) * s ≤ (q : ℤ) * (-2) := mul_le_mul_of_nonneg_left hs' hq0.le
          rw [abs_of_neg (by linarith)]; linarith
        · rw [hs']
          have : ∑ d, wCol q d * E d ≤ Wsh q := hwu (by omega)
          rw [abs_of_neg (by linarith)]; linarith
        · exfalso; omega
        · rw [hs']
          have : -Wsh q ≤ ∑ d, wCol q d * E d := hwl (by omega)
          rw [abs_of_nonneg (by linarith)]; linarith
        · have : (q : ℤ) * 2 ≤ (q : ℤ) * s := mul_le_mul_of_nonneg_left hs' hq0.le
          rw [abs_of_pos (by linarith)]; linarith
      have h0' : (0 : ℤ) ≤ (q : ℤ) - Wsh q := by linarith
      calc ((q : ℤ) - Wsh q) ^ 2 ≤ |3 * ((q : ℤ) * E c + dh c)| ^ 2 := pow_le_pow_left₀ h0' hb 2
        _ = 9 * ((q : ℤ) * E c + dh c) ^ 2 := by rw [sq_abs]; ring
    have hk := Finset.sum_le_sum (s := univ) fun c _ => key c
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum] at hk
    push_cast at hk
    linarith

/-! ## (3), the lower bound -/

lemma colshift_lower (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (sh : Fin 3 → Fin 3 → ZMod q)
    (v w : Fin 3 → ZMod q) (hvw : v ≠ w) :
    ((q : ℝ) ^ 2 - (Wsh q + 3) * q + 3) / Real.sqrt 3 ≤
      Real.sqrt (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℝ) := by
  have hq0 : 0 < q := by omega
  have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hs := sqrt3_pos
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 3 := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hWR : (2 : ℝ) ≤ Wsh q ∧ (Wsh q : ℝ) ≤ 4 := by
    unfold Wsh; split_ifs <;> norm_num
  set n := v + sh0 sh with hn
  set n' := w + sh0 sh with hn'
  have hnn : n ≠ n' := fun h => hvw (add_right_cancel h)
  obtain ⟨k, hk⟩ := torus_exists (q ^ 3) (by positivity) (digPointShift q 3 (colGen q) sh v)
    (digPointShift q 3 (colGen q) sh w)
  obtain ⟨E, hE⟩ : ∃ E : Fin 3 → ℤ, E = fun c => ((n' c).val : ℤ) - (n c).val + q * k c := ⟨_, rfl⟩
  obtain ⟨dh, hdh⟩ : ∃ x : Fin 3 → ℤ, x = fun c => ((colH q (wCol q) n' + shB sh c).val : ℤ) -
      (colH q (wCol q) n + shB sh c).val := ⟨_, rfl⟩
  obtain ⟨dj, hdj⟩ : ∃ x : Fin 3 → ℤ, x = fun c => ((colJ q ellCol n' + shB' sh c).val : ℤ) -
      (colJ q ellCol n + shB' sh c).val := ⟨_, rfl⟩
  have hD : ∀ c, ((digPointShift q 3 (colGen q) sh w c : ℕ) : ℤ) -
      (digPointShift q 3 (colGen q) sh v c : ℕ) + ((q ^ 3 : ℕ) : ℤ) * k c =
      (q : ℤ) * ((q : ℤ) * E c + dh c) + dj c := by
    intro c; rw [shiftPt_eq, shiftPt_eq, ← hn, ← hn', hE, hdh, hdj]; push_cast; ring
  have hT : (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
      (digPointShift q 3 (colGen q) sh w) : ℝ) =
      ∑ c, ((q : ℝ) * (((q : ℤ) * E c + dh c : ℤ) : ℝ) + (dj c : ℝ)) ^ 2 := by
    have : (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℤ) = ∑ c, ((q : ℤ) * ((q : ℤ) * E c + dh c) + dj c) ^ 2 := by
      rw [hk]; exact Finset.sum_congr rfl fun c _ => by rw [hD c]
    exact_mod_cast this
  rw [hT]
  have hdh1 : ∀ c, |dh c| < q := by
    intro c; rw [hdh]; beta_reduce
    have := ZMod.val_lt (colH q (wCol q) n' + shB sh c)
    have := ZMod.val_lt (colH q (wCol q) n + shB sh c)
    rw [abs_lt]; constructor <;> omega
  have hdj1 : ∀ c, |(dj c : ℝ)| ≤ q - 1 := by
    intro c
    have : |dj c| ≤ q - 1 := by
      rw [hdj]; beta_reduce
      have := ZMod.val_lt (colJ q ellCol n' + shB' sh c)
      have := ZMod.val_lt (colJ q ellCol n + shB' sh c)
      rw [abs_le]; constructor <;> omega
    exact_mod_cast this
  have hcast : ∀ c, ((E c : ℤ) : ZMod q) = n' c - n c := by intro c; rw [hE]; simp
  have hbound_le : ((q : ℝ) ^ 2 - (Wsh q + 3) * q + 3) / Real.sqrt 3 ≤ (q : ℝ) ^ 2 := by
    rw [div_le_iff₀ hs]; nlinarith
  by_cases hbig : ∃ c, 2 ≤ |E c|
  · obtain ⟨c, hc⟩ := hbig
    have hDc : (q : ℝ) ^ 2 ≤ |(q : ℝ) * (((q : ℤ) * E c + dh c : ℤ) : ℝ) + (dj c : ℝ)| := by
      have h1 : 2 * (q : ℝ) ^ 2 ≤ |(q : ℝ) * ((q : ℤ) * E c : ℤ)| := by
        push_cast
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q)]
        have : (2 : ℝ) ≤ |(E c : ℝ)| := by exact_mod_cast hc
        nlinarith
      have h2 : |(q : ℝ) * (dh c : ℝ) + dj c| ≤ q * (q - 1) + (q - 1) := by
        calc |(q : ℝ) * (dh c : ℝ) + dj c| ≤ |(q : ℝ) * (dh c : ℝ)| + |(dj c : ℝ)| := abs_add_le _ _
          _ ≤ q * (q - 1) + (q - 1) := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q)]
            have : |(dh c : ℝ)| ≤ q - 1 := by
              have := hdh1 c; have : |dh c| ≤ q - 1 := by omega
              exact_mod_cast this
            nlinarith [hdj1 c]
      have e : (q : ℝ) * (((q : ℤ) * E c + dh c : ℤ) : ℝ) + (dj c : ℝ) =
          (q : ℝ) * ((q : ℤ) * E c : ℤ) + ((q : ℝ) * (dh c : ℝ) + dj c) := by push_cast; ring
      rw [e]
      have := abs_sub_abs_le_abs_sub ((q : ℝ) * ((q : ℤ) * E c : ℤ)) (-((q : ℝ) * (dh c : ℝ) + dj c))
      rw [abs_neg, sub_neg_eq_add] at this
      nlinarith
    have hsq : ((q : ℝ) ^ 2) ^ 2 ≤ ∑ c, ((q : ℝ) * (((q : ℤ) * E c + dh c : ℤ) : ℝ) + (dj c : ℝ)) ^ 2 := by
      have : ((q : ℝ) ^ 2) ^ 2 ≤ ((q : ℝ) * (((q : ℤ) * E c + dh c : ℤ) : ℝ) + (dj c : ℝ)) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hDc 2
        rwa [sq_abs] at this
      exact this.trans (Finset.single_le_sum (f := fun c =>
        ((q : ℝ) * (((q : ℤ) * E c + dh c : ℤ) : ℝ) + (dj c : ℝ)) ^ 2) (fun c _ => sq_nonneg _) (mem_univ c))
    exact hbound_le.trans (Real.le_sqrt_of_sq_le hsq)
  · push Not at hbig
    have hE1 : ∀ c, -1 ≤ E c ∧ E c ≤ 1 := fun c => by have := abs_lt.1 (hbig c); omega
    have hE0 : E ≠ 0 := by
      intro h; apply hnn; funext c; have := hcast c; rw [h] at this; simp at this
      exact (sub_eq_zero.1 this.symm).symm
    have hcong : ∀ c, (q : ℤ) ∣ dh c - ∑ d, colA q (wCol q) d * E d := by
      intro c
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      rw [hdh]; push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id]
      simp only [colH, hcast, mul_sub, Finset.sum_sub_distrib]
      ring
    have hU := shift_U h6 hq E hE1 hE0 dh hdh1 hcong
    set U : Fin 3 → ℝ := fun c => (((q : ℤ) * E c + dh c : ℤ) : ℝ) with hUdef
    have hUR : ((q : ℝ) - Wsh q) ^ 2 ≤ 3 * ∑ c, U c ^ 2 := by
      have : (((q : ℤ) - Wsh q) ^ 2 : ℤ) ≤ 3 * ∑ c, ((q : ℤ) * E c + dh c) ^ 2 := hU
      simp only [hUdef]; exact_mod_cast this
    set α := (q : ℝ) * ((q : ℝ) - Wsh q) / Real.sqrt 3 with hα
    set β := Real.sqrt 3 * ((q : ℝ) - 1) with hβ
    have hgoal : ((q : ℝ) ^ 2 - (Wsh q + 3) * q + 3) / Real.sqrt 3 = α - β := by
      rw [hα, hβ]; field_simp; rw [hs2]; ring
    rw [hgoal]
    by_cases hle : β ≤ α
    · have hu : α ^ 2 ≤ ∑ c, ((q : ℝ) * U c) ^ 2 := by
        have e : ∑ c, ((q : ℝ) * U c) ^ 2 = (q : ℝ) ^ 2 * ∑ c, U c ^ 2 := by
          rw [Finset.mul_sum]; congr 1; funext c; ring
        rw [e, hα, div_pow, hs2, mul_pow]
        rw [div_le_iff₀ (by norm_num)]
        nlinarith [sq_nonneg (q : ℝ)]
      have hr : ∑ c, (dj c : ℝ) ^ 2 ≤ β ^ 2 := by
        have : ∀ c, (dj c : ℝ) ^ 2 ≤ ((q : ℝ) - 1) ^ 2 := fun c => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdj1 c) 2
        calc ∑ c, (dj c : ℝ) ^ 2 ≤ ∑ _c : Fin 3, ((q : ℝ) - 1) ^ 2 := Finset.sum_le_sum fun c _ => this c
          _ = β ^ 2 := by rw [hβ, mul_pow, hs2]; simp
      have hβ0 : 0 ≤ β := by
        rw [hβ]; have : (0 : ℝ) ≤ q - 1 := by linarith
        positivity
      have := tri_lower (fun c => (q : ℝ) * U c) (fun c => (dj c : ℝ)) α β hβ0 hle hu hr
      exact Real.le_sqrt_of_sq_le this
    · push Not at hle
      linarith [Real.sqrt_nonneg (∑ c, ((q : ℝ) * (((q : ℤ) * E c + dh c : ℤ) : ℝ) + (dj c : ℝ)) ^ 2)]

/-- **`prop:colshift`(3)**: the lower bound exceeds `0.4693` for every `q ≥ 37`. -/
lemma colshift_4693 (hq : 37 ≤ q) :
    0.4693 < (1 - (Wsh q + 3) / (q : ℝ) + 3 / (q : ℝ) ^ 2) / Real.sqrt 3 := by
  have hqR : (37 : ℝ) ≤ q := by exact_mod_cast hq
  have hW : (Wsh q : ℝ) ≤ 4 := by unfold Wsh; split_ifs <;> norm_num
  have hs : Real.sqrt 3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 := sqrt3_pos
  set x : ℝ := 1 / q with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 37 := one_div_le_one_div_of_le (by norm_num) hqR
  have e : 1 - (Wsh q + 3) / (q : ℝ) + 3 / (q : ℝ) ^ 2 = 1 - (Wsh q + 3) * x + 3 * x ^ 2 := by
    rw [hx]; field_simp
  rw [e, lt_div_iff₀ hs0]
  have hg : 1113 / 1369 ≤ 1 - (Wsh q + 3) * x + 3 * x ^ 2 := by
    have : 1113 / 1369 ≤ 1 - 7 * x + 3 * x ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-! ## (3), the upper bound: arcs -/

/-- `(T - p) mod q` for `T, p < q`. -/
def md (q T p : ℕ) : ℕ := if p ≤ T then T - p else T + q - p

lemma val_sub_md (x y : ZMod q) : (x - y).val = md q x.val y.val := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  unfold md
  split_ifs with h
  · exact ZMod.val_sub h
  · push Not at h
    have e : x - y = ((x.val + q - y.val : ℕ) : ZMod q) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val]; ring
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

lemma arc_sorted (q ax ay az px py pz : ℕ) (h1 : px < py) (h2 : py < pz) (h3 : pz < q)
    (hax : 1 ≤ ax) (hay : 1 ≤ ay) (haz : 1 ≤ az) (hs : ax + ay + az = q) :
    (∃ T, T < q ∧ q - ax ≤ md q T px ∧ md q T py < q - ax ∧ md q T pz < q - ax) ∨
    (∃ T, T < q ∧ q - ay ≤ md q T py ∧ md q T px < q - ay ∧ md q T pz < q - ay) ∨
    (∃ T, T < q ∧ q - az ≤ md q T pz ∧ md q T px < q - az ∧ md q T py < q - az) := by
  by_cases hx : ax ≤ py - px
  · left
    by_cases h0 : px = 0
    · refine ⟨q - 1, by omega, ?_⟩
      simp only [md]; split_ifs <;> omega
    · refine ⟨px - 1, by omega, ?_⟩
      simp only [md]; split_ifs <;> omega
  · by_cases hy : ay ≤ pz - py
    · right; left
      refine ⟨py - 1, by omega, ?_⟩
      simp only [md]; split_ifs <;> omega
    · right; right
      refine ⟨pz - 1, by omega, ?_⟩
      simp only [md]; split_ifs <;> omega

lemma arc_two (q a pe po : ℕ) (hne : pe ≠ po) (hpe : pe < q) (hpo : po < q) (ha : 1 ≤ a)
    (ha2 : 2 * a < q) : ∃ T, T < q ∧ q - a ≤ md q T po ∧ md q T pe < q - a := by
  by_cases hf : a ≤ md q pe po
  · by_cases h0 : po = 0
    · refine ⟨q - 1, by omega, ?_⟩
      simp only [md] at hf ⊢; split_ifs at hf ⊢ <;> omega
    · refine ⟨po - 1, by omega, ?_⟩
      simp only [md] at hf ⊢; split_ifs at hf ⊢ <;> omega
  · push Not at hf
    by_cases h0 : a ≤ po
    · refine ⟨po - a, by omega, ?_⟩
      simp only [md] at hf ⊢; split_ifs at hf ⊢ <;> omega
    · refine ⟨po + q - a, by omega, ?_⟩
      simp only [md] at hf ⊢; split_ifs at hf ⊢ <;> omega

lemma fin3_mem (x y z d : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d = x ∨ d = y ∨ d = z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases d <;> simp_all

lemma arc_fin (q : ℕ) (A p : Fin 3 → ℕ) (hA1 : ∀ c, 1 ≤ A c) (hsum : A 0 + A 1 + A 2 = q)
    (hp : ∀ c, p c < q) (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : p x < p y) (h2 : p y < p z) :
    ∃ c T, T < q ∧ q - A c ≤ md q T (p c) ∧ ∀ d, d ≠ c → md q T (p d) < q - A c := by
  have hs : A x + A y + A z = q := by
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all <;> omega
  rcases arc_sorted q (A x) (A y) (A z) (p x) (p y) (p z) h1 h2 (hp z) (hA1 x) (hA1 y) (hA1 z) hs with
    ⟨T, hT, a, b, c⟩ | ⟨T, hT, a, b, c⟩ | ⟨T, hT, a, b, c⟩
  · refine ⟨x, T, hT, a, fun d hd => ?_⟩
    rcases fin3_mem x y z d hxy hxz hyz with rfl | rfl | rfl
    · exact absurd rfl hd
    · exact b
    · exact c
  · refine ⟨y, T, hT, a, fun d hd => ?_⟩
    rcases fin3_mem x y z d hxy hxz hyz with rfl | rfl | rfl
    · exact b
    · exact absurd rfl hd
    · exact c
  · refine ⟨z, T, hT, a, fun d hd => ?_⟩
    rcases fin3_mem x y z d hxy hxz hyz with rfl | rfl | rfl
    · exact b
    · exact c
    · exact absurd rfl hd

/-- The arc argument of the proof of `prop:colshift`(3): for residues `p_d` (the paper's `b_d`), not
all equal, some `c` and `T` have `T` in the arc of `c` and in no arc of `d ≠ c`. -/
lemma arc_exists (q : ℕ) (A p : Fin 3 → ℕ) (hA1 : ∀ c, 1 ≤ A c) (hA2 : ∀ c, 2 * A c < q)
    (hsum : A 0 + A 1 + A 2 = q) (hp : ∀ c, p c < q) (hne : ¬ (p 0 = p 1 ∧ p 1 = p 2)) :
    ∃ c T, T < q ∧ q - A c ≤ md q T (p c) ∧ ∀ d, d ≠ c → md q T (p d) < q - A c := by
  have two : ∀ e e' o : Fin 3, e ≠ e' → e ≠ o → e' ≠ o → p e = p e' → p e ≠ p o →
      ∃ c T, T < q ∧ q - A c ≤ md q T (p c) ∧ ∀ d, d ≠ c → md q T (p d) < q - A c := by
    intro e e' o hee' heo he'o hpe hpo
    obtain ⟨T, hT, h1, h2⟩ := arc_two q (A o) (p e) (p o) hpo (hp e) (hp o) (hA1 o) (hA2 o)
    refine ⟨o, T, hT, h1, fun d hd => ?_⟩
    rcases fin3_mem e e' o d hee' heo he'o with rfl | rfl | rfl
    · exact h2
    · rw [← hpe]; exact h2
    · exact absurd rfl hd
  have d01 : (0 : Fin 3) ≠ 1 := by decide
  have d02 : (0 : Fin 3) ≠ 2 := by decide
  have d12 : (1 : Fin 3) ≠ 2 := by decide
  rcases lt_trichotomy (p 0) (p 1) with h01 | h01 | h01 <;>
  rcases lt_trichotomy (p 1) (p 2) with h12 | h12 | h12 <;>
  rcases lt_trichotomy (p 0) (p 2) with h02 | h02 | h02
  all_goals first
    | exact arc_fin q A p hA1 hsum hp 0 1 2 d01 d02 d12 (by omega) (by omega)
    | exact arc_fin q A p hA1 hsum hp 0 2 1 d02 d01 d12.symm (by omega) (by omega)
    | exact arc_fin q A p hA1 hsum hp 1 0 2 d01.symm d12 d02 (by omega) (by omega)
    | exact arc_fin q A p hA1 hsum hp 1 2 0 d12 d01.symm d02.symm (by omega) (by omega)
    | exact arc_fin q A p hA1 hsum hp 2 0 1 d02.symm d12.symm d01 (by omega) (by omega)
    | exact arc_fin q A p hA1 hsum hp 2 1 0 d12.symm d02.symm d01.symm (by omega) (by omega)
    | exact two 0 1 2 d01 d02 d12 (by omega) (by omega)
    | exact two 0 2 1 d02 d01 d12.symm (by omega) (by omega)
    | exact two 1 2 0 d12 d01.symm d02.symm (by omega) (by omega)
    | exact absurd ⟨by omega, by omega⟩ hne

/-! ## (3), the upper bound -/

/-- `a_max = max_c a_c`. -/
noncomputable def aMax (q : ℕ) : ℤ := univ.sup' univ_nonempty (colA q (wCol q))

/-- `w_max = max_c w_c`. -/
noncomputable def wMax (q : ℕ) : ℤ := univ.sup' univ_nonempty (wCol q)

lemma aMax_eq (h6 : Nat.Coprime q 6) : 3 * aMax q = q + wMax q := by
  obtain ⟨hw0, hw3, -, -⟩ := wCol_props (q := q) h6
  have ha : ∀ d, 3 * colA q (wCol q) d = q + wCol q d := fun d => Int.mul_ediv_cancel' (hw3 d)
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin 3)) (colA q (wCol q))
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin 3)) (wCol q)
  unfold aMax wMax
  rw [hi, hj]
  have h1 := Finset.le_sup' (colA q (wCol q)) (mem_univ j)
  have h2 := Finset.le_sup' (wCol q) (mem_univ i)
  rw [hi] at h1; rw [hj] at h2
  have := ha i; have := ha j
  linarith

lemma colA_unit (h6 : Nat.Coprime q 6) (c : Fin 3) : IsUnit (((colA q (wCol q) c : ℤ) : ZMod q)) := by
  obtain ⟨hw0, hw3, -, hwu⟩ := wCol_props (q := q) h6
  have := hwu c
  rw [← three_colA _ hw3 c] at this
  exact isUnit_of_mul_isUnit_right this

lemma colA_bounds (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (c : Fin 3) :
    1 ≤ colA q (wCol q) c ∧ 2 * colA q (wCol q) c < q := by
  rcases q_mod3 h6 with h | h <;> fin_cases c <;> simp [colA, wCol, h] <;> omega

/-- **`prop:colshift`(3)**, the upper bound: if the second shift digits are not all equal, some pair
of points has Euclidean difference `q a_c 𝟏 + Δj` in every coordinate, `|Δj_d| < q`. -/
lemma colshift_upper (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (sh : Fin 3 → Fin 3 → ZMod q)
    (hne : ¬ (sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1)) :
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧ ∀ d,
      |((digPointShift q 3 (colGen q) sh w d : ℕ) : ℤ) - (digPointShift q 3 (colGen q) sh v d : ℕ)| ≤
        q * aMax q + q - 1 := by
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  obtain ⟨hval, -, -⟩ := col_vals h6 hq
  obtain ⟨hw0, hw3, -, -⟩ := wCol_props (q := q) h6
  obtain ⟨A, hAdef⟩ : ∃ A : Fin 3 → ℕ, A = fun c => (((colA q (wCol q) c : ℤ) : ZMod q)).val :=
    ⟨_, rfl⟩
  have hAv : ∀ c, (((colA q (wCol q) c : ℤ) : ZMod q)).val = A c := fun c => by rw [hAdef]
  have hA : ∀ c, (A c : ℤ) = colA q (wCol q) c := fun c => by rw [← hAv]; exact hval c
  have hA1 : ∀ c, 1 ≤ A c := fun c => by have := (colA_bounds h6 hq c).1; have := hA c; omega
  have hA2 : ∀ c, 2 * A c < q := fun c => by have := (colA_bounds h6 hq c).2; have := hA c; omega
  have hAs : A 0 + A 1 + A 2 = q := by
    have := sum_colA q _ hw0 hw3
    simp only [Fin.sum_univ_three] at this
    have := hA 0; have := hA 1; have := hA 2; omega
  obtain ⟨p, hpdef⟩ : ∃ p : Fin 3 → ℕ, p = fun c => (-shB sh c).val := ⟨_, rfl⟩
  have hpv : ∀ c, (-shB sh c).val = p c := fun c => by rw [hpdef]
  have hp : ∀ c, p c < q := fun c => by rw [← hpv]; exact ZMod.val_lt _
  have hpne : ¬ (p 0 = p 1 ∧ p 1 = p 2) := by
    rintro ⟨h01, h12⟩
    apply hne
    have e : ∀ c d, p c = p d → sh c 1 = sh d 1 := by
      intro c d h
      rw [← hpv, ← hpv] at h
      have : -shB sh c = -shB sh d := ZMod.val_injective _ h
      simpa [shB] using this
    exact ⟨e 0 1 h01, e 1 2 h12⟩
  obtain ⟨c, T, hT, hc, hd⟩ := arc_exists q A p hA1 hA2 hAs hp hpne
  -- the cell `n` with `a·n = T` and `n_c = 0`
  obtain ⟨c', hc'⟩ : ∃ c', c' = c + 1 := ⟨_, rfl⟩
  have hcc' : c ≠ c' := by rw [hc']; simp
  obtain ⟨u, hu⟩ := colA_unit (q := q) h6 c'
  obtain ⟨n, hn⟩ : ∃ n : Fin 3 → ZMod q, n = Pi.single c' ((↑u⁻¹ : ZMod q) * (T : ZMod q)) :=
    ⟨_, rfl⟩
  have hHn : colH q (wCol q) n = (T : ZMod q) := by
    have := colH_add_single (wCol q) (0 : Fin 3 → ZMod q) c' ((↑u⁻¹ : ZMod q) * (T : ZMod q))
    simp only [zero_add] at this
    rw [hn, this]
    have h0 : colH q (wCol q) 0 = 0 := by simp [colH]
    rw [h0, zero_add, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have hnc : n c = 0 := by rw [hn]; simp [Pi.single_eq_of_ne hcc']
  refine ⟨n - sh0 sh, n + Pi.single c 1 - sh0 sh, fun h => ?_, fun d => ?_⟩
  · have := congrFun (sub_left_inj.1 h) c
    simp [hnc] at this
  · rw [shiftPt_eq, shiftPt_eq, sub_add_cancel, sub_add_cancel, colH_add_single, colJ_add_single,
      mul_one, mul_one, hHn]
    -- the shared digit
    have hx : ∀ e, ((T : ZMod q) + shB sh e).val = md q T (p e) := by
      intro e
      have : (T : ZMod q) + shB sh e = (T : ZMod q) - (((-shB sh e).val : ℕ) : ZMod q) := by
        rw [ZMod.natCast_zmod_val]; ring
      rw [this, val_sub_md, ZMod.val_natCast, Nat.mod_eq_of_lt hT, ZMod.val_natCast,
        Nat.mod_eq_of_lt (ZMod.val_lt _), hpv]
    have hpd := hp d
    have hlt : md q T (p d) < q := by simp only [md]; split_ifs <;> omega
    have hAc := hA2 c
    have hwrap : (((T : ZMod q) + ((colA q (wCol q) c : ℤ) : ZMod q) + shB sh d).val : ℤ) =
        md q T (p d) + A c - q * (if d = c then 1 else 0) := by
      rw [show (T : ZMod q) + ((colA q (wCol q) c : ℤ) : ZMod q) + shB sh d =
        ((T : ZMod q) + shB sh d) + ((colA q (wCol q) c : ℤ) : ZMod q) by ring, ZMod.val_add, hx d,
        hAv]
      rw [mod_wrap _ _ hlt (by omega)]
      by_cases hdc : d = c
      · rw [hdc]
        have h1 : ¬ (md q T (p c) + A c < q) := by omega
        simp [h1]
      · have h1 : md q T (p d) + A c < q := by have := hd d hdc; omega
        simp [h1, hdc]
    have hcell : (((n + Pi.single c (1 : ZMod q) : Fin 3 → ZMod q) d).val : ℤ) - (n d).val = if d = c then 1 else 0 := by
      by_cases hdc : d = c
      · rw [hdc, if_pos rfl]; simp [hnc, ZMod.val_one]
      · rw [if_neg hdc]; simp [Pi.single_eq_of_ne hdc]
    have hJ1 := ZMod.val_lt (colJ q ellCol n + ((ellCol c : ℤ) : ZMod q) + shB' sh d)
    have hJ2 := ZMod.val_lt (colJ q ellCol n + shB' sh d)
    have hxv : (((T : ZMod q) + shB sh d).val : ℤ) = md q T (p d) := by rw [hx d]
    have e : ((q ^ 2 * ((n + Pi.single c (1 : ZMod q) : Fin 3 → ZMod q) d).val +
        q * ((T : ZMod q) + ((colA q (wCol q) c : ℤ) : ZMod q) + shB sh d).val +
        (colJ q ellCol n + ((ellCol c : ℤ) : ZMod q) + shB' sh d).val : ℕ) : ℤ) -
        ((q ^ 2 * (n d).val + q * ((T : ZMod q) + shB sh d).val + (colJ q ellCol n + shB' sh d).val : ℕ) : ℤ) =
        q * A c + (((colJ q ellCol n + ((ellCol c : ℤ) : ZMod q) + shB' sh d).val : ℤ) -
          (colJ q ellCol n + shB' sh d).val) := by
      push_cast
      rw [hwrap, hxv]
      have := hcell
      by_cases hdc : d = c
      · rw [if_pos hdc] at this ⊢; linear_combination (q : ℤ) ^ 2 * this
      · rw [if_neg hdc] at this ⊢; linear_combination (q : ℤ) ^ 2 * this
    rw [e]
    have hAm : (A c : ℤ) ≤ aMax q := by rw [hA]; exact Finset.le_sup' _ (mem_univ c)
    have hqA : (q : ℤ) * A c ≤ q * aMax q := mul_le_mul_of_nonneg_left hAm (by positivity)
    have hA1' : (1 : ℤ) ≤ A c := by exact_mod_cast hA1 c
    have hJ1' : (((colJ q ellCol n + ((ellCol c : ℤ) : ZMod q) + shB' sh d).val : ℕ) : ℤ) < q := by
      exact_mod_cast hJ1
    have hJ2' : (((colJ q ellCol n + shB' sh d).val : ℕ) : ℤ) < q := by exact_mod_cast hJ2
    have hJ1'' : (0 : ℤ) ≤ (((colJ q ellCol n + ((ellCol c : ℤ) : ZMod q) + shB' sh d).val : ℕ) : ℤ) :=
      by positivity
    have hJ2'' : (0 : ℤ) ≤ (((colJ q ellCol n + shB' sh d).val : ℕ) : ℤ) := by positivity
    rw [abs_le]; constructor
    · nlinarith
    · linarith

end Z3NetC.Proofs

/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColShift
public import Z3Net.ColDist

@[expose] public section

/-!
# V14 stage S10′: the Euclidean exactness in `prop:colshift`(1)

With equal second and third shift digits, `𝒞_q ⊕ τ` is the column point set with heights `φ(n + u)`
(`shift_column`). The closest pair of `thm:col`(2), the cells `𝟏`, `e_{i*}` (difference exactly `D`),
translated by `t𝟏 - u`, stays a closest pair; for a suitable `t` (one of `0, 1, 2`) no coordinate of
its cells wraps, so its Euclidean difference is exactly `D` and `3‖D‖² = 2q⁴ + τ²`
(`colshift_eq_eucl`). Hence the minimum distance of `prop:colshift`(1) is also the Euclidean one.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

lemma val_sub_one_of_ne (hq : 2 ≤ q) (x : ZMod q) (hx : x ≠ 0) :
    ((x - 1).val : ℤ) = (x.val : ℤ) - 1 := by
  have : Fact (1 < q) := ⟨by omega⟩
  have h1 : (1 : ZMod q).val = 1 := ZMod.val_one q
  have hx1 : 1 ≤ x.val := by
    rcases Nat.eq_zero_or_pos x.val with h | h
    · exact absurd ((ZMod.val_eq_zero x).mp h) hx
    · exact h
  rw [ZMod.val_sub (by rw [h1]; exact hx1), h1]
  omega

lemma avoid_two (hq : 3 ≤ q) (a b : ZMod q) : ∃ t : ZMod q, t ≠ a ∧ t ≠ b := by
  have : Fact (1 < q) := ⟨by omega⟩
  have h10 : (1 : ZMod q) ≠ 0 := one_ne_zero
  have h20 : (2 : ZMod q) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 q).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h21 : (2 : ZMod q) ≠ 1 := by
    intro h
    have : (1 : ZMod q) = 0 := by linear_combination h
    exact h10 this
  by_cases ha : a = 0
  · by_cases hb : b = 1
    · exact ⟨2, by rw [ha]; exact h20, by rw [hb]; exact h21⟩
    · by_cases hb0 : b = 0
      · exact ⟨1, by rw [ha]; exact h10, by rw [hb0]; exact h10⟩
      · exact ⟨1, by rw [ha]; exact h10, fun h => hb h.symm⟩
  · by_cases hb : b = 0
    · by_cases ha1 : a = 1
      · exact ⟨2, by rw [ha1]; exact h21, by rw [hb]; exact h20⟩
      · exact ⟨1, fun h => ha1 h.symm, by rw [hb]; exact h10⟩
    · exact ⟨0, fun h => ha h.symm, fun h => hb h.symm⟩

lemma fin3_other (i c : Fin 3) (h : c ≠ i) : c = i + 1 ∨ c = i + 2 := by
  fin_cases i <;> fin_cases c <;> simp_all

/-- **`prop:colshift`(1), Euclidean exactness**: with equal second and third shift digits, two points of
`𝒞_q ⊕ τ` differ by exactly `D` (no coordinate wraps), so their Euclidean distance is the minimum distance:
`3‖D‖² = 2q⁴ + τ²`. -/
theorem colshift_eq_eucl (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (sh : Fin 3 → Fin 3 → ZMod q)
    (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) (h3 : sh 0 2 = sh 1 2 ∧ sh 1 2 = sh 2 2) :
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧
      (∀ c, (digPointShift q 3 (colGen q) sh w c : ℤ) - digPointShift q 3 (colGen q) sh v c = DCol q c) ∧
      3 * ∑ c, ((digPointShift q 3 (colGen q) sh w c : ℤ) - digPointShift q 3 (colGen q) sh v c) ^ 2 =
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
  obtain ⟨u, hu⟩ := shift_column h6 sh h2 h3
  obtain ⟨hne, hpair⟩ := col_pair h6 hq
  obtain ⟨-, hH⟩ := isHeight_phiC (q := q) h6
  set i := iStar q
  obtain ⟨t, ht1, ht2⟩ := avoid_two (by omega) (u (i + 1) - 1) (u (i + 2) - 1)
  have ht : ∀ c, c ≠ i → (1 : ZMod q) + t - u c ≠ 0 := by
    intro c hc h0
    rcases fin3_other i c hc with rfl | rfl
    · exact ht1 (by linear_combination h0)
    · exact ht2 (by linear_combination h0)
  set n0 : Fin 3 → ZMod q := 1 + (fun _ => t) - u
  set n1 : Fin 3 → ZMod q := Pi.single i 1 + (fun _ => t) - u
  have hpt : ∀ n, digPointShift q 3 (colGen q) sh (n - sh0 sh) = colPt q (fun n => phiC q (n + u)) n := by
    intro n; rw [hu, sub_add_cancel]
  have hφ0 : phiC q (n0 + u) = phiC q 1 := by
    simp only [n0, sub_add_cancel]; exact height_const hH 1 t
  have hφ1 : phiC q (n1 + u) = phiC q (Pi.single i 1) := by
    simp only [n1, sub_add_cancel]; exact height_const hH _ t
  have hdiff : ∀ c, (digPointShift q 3 (colGen q) sh (n1 - sh0 sh) c : ℤ) -
      digPointShift q 3 (colGen q) sh (n0 - sh0 sh) c = DCol q c := by
    intro c
    rw [hpt, hpt, ← hpair c]
    simp only [colPt, hφ0, hφ1]
    push_cast
    have hcell : ((n1 c).val : ℤ) - (n0 c).val = ((Pi.single i (1 : ZMod q) : Fin 3 → ZMod q) c).val -
        ((1 : Fin 3 → ZMod q) c).val := by
      have : Fact (1 < q) := ⟨by omega⟩
      by_cases hc : c = i
      · subst hc
        simp [n0, n1]
      · have e : n1 c = n0 c - 1 := by
          simp only [n0, n1, Pi.sub_apply, Pi.add_apply, Pi.one_apply, Pi.single_eq_of_ne hc]; ring
        rw [e, val_sub_one_of_ne (by omega) _ (by simpa [n0] using ht c hc)]
        simp [Pi.single_eq_of_ne hc, ZMod.val_one]
    linear_combination (q : ℤ) ^ 2 * hcell
  refine ⟨n0 - sh0 sh, n1 - sh0 sh, fun h => hne ?_, hdiff, ?_⟩
  · have h' : n0 = n1 := by simpa using h
    have := congrArg (· + u - (fun _ => t)) h'
    simpa [n0, n1] using this
  · simp only [hdiff]
    exact DCol_norm h6

/-- **`rem:shiftshared`**, the column net: for `q ≥ 11` (`gcd(q, 6) = 1`) the upper bound
`(1 + (3 + w_max)/q - 3/q²)/√3` of `prop:colshift`(3) for shifts with unequal second digits lies below the
value `cCol q` of `thm:col`(2) (for every `q ≥ 11`): the exact value does not extend to those shifts. -/
theorem shiftshared_col (hq : 11 ≤ q) :
    (1 + (3 + univ.sup' univ_nonempty (wCol q)) / (q : ℝ) - 3 / (q : ℝ) ^ 2) / Real.sqrt 3 < cCol q := by
  have hq0 : (11 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hs3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  -- `w_max ≤ 2` and `τ ≥ q² - 2q`
  have hw : ((univ.sup' univ_nonempty (wCol q) : ℤ) : ℝ) ≤ 2 := by
    have : univ.sup' univ_nonempty (wCol q) ≤ 2 := by
      rw [Finset.sup'_le_iff]; intro c _
      unfold wCol; split_ifs <;> fin_cases c <;> simp
    exact_mod_cast this
  have hτ : (q : ℝ) ^ 2 - 2 * q ≤ (tauCol q : ℝ) := by
    unfold tauCol; split_ifs
    · push_cast; nlinarith
    · push_cast; linarith
  have hτ0 : 0 ≤ (q : ℝ) ^ 2 - 2 * q := by nlinarith
  set w := ((univ.sup' univ_nonempty (wCol q) : ℤ) : ℝ) with hwdef
  have hw1 : -2 ≤ w := by
    have : -2 ≤ univ.sup' univ_nonempty (wCol q) := by
      refine le_trans ?_ (Finset.le_sup' (wCol q) (mem_univ 0))
      unfold wCol; split_ifs <;> simp
    rw [hwdef]; exact_mod_cast this
  set A : ℝ := (q : ℝ) ^ 2 + (3 + w) * q - 3
  have hA0 : 0 ≤ A := by simp only [A]; nlinarith
  have hAlt : A ^ 2 < 2 * (q : ℝ) ^ 4 + (tauCol q : ℝ) ^ 2 := by
    have h1 : A ≤ (q : ℝ) ^ 2 + 5 * q := by simp only [A]; nlinarith
    have h2 : ((q : ℝ) ^ 2 - 2 * q) ^ 2 ≤ (tauCol q : ℝ) ^ 2 := pow_le_pow_left₀ hτ0 hτ 2
    have h3 : A ^ 2 ≤ ((q : ℝ) ^ 2 + 5 * q) ^ 2 := pow_le_pow_left₀ hA0 h1 2
    nlinarith
  have hlhs : (1 + (3 + w) / (q : ℝ) - 3 / (q : ℝ) ^ 2) / Real.sqrt 3 = A / (Real.sqrt 3 * (q : ℝ) ^ 2) := by
    simp only [A]; field_simp
  have hrhs : cCol q = Real.sqrt (2 * (q : ℝ) ^ 4 + (tauCol q : ℝ) ^ 2) / (Real.sqrt 3 * (q : ℝ) ^ 2) := by
    unfold cCol
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 3), div_div]
  rw [hlhs, hrhs]
  apply div_lt_div_of_pos_right _ (by positivity)
  rw [show A = Real.sqrt (A ^ 2) by rw [Real.sqrt_sq hA0]]
  exact Real.sqrt_lt_sqrt (by positivity) hAlt

end Z3NetC.Proofs

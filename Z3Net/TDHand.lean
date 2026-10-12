/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.TDEnum

@[expose] public section

/-!
# V14 stage S11′: `thm:D`, the hand parts

Doubled throughout (`G = 2F₀`, odd entries). In the order of the printed proof of `thm:D`:
* (MIN) gives the disjoint `2 × 2` minors (`min2_of_disj`); two rows that are `±1` on the three columns outside
  them violate (MIN) (`two_rows`).
* *Diagonal.* `lower F` lowers every `α_c` to `m_c` (`mrow`); `drift_lower`: `2 dr(E)` does not increase.
* *Minor tax.* At most one light row (`mrow = 1`; `minor_tax`).
* *Balance on the full steps.* `drift_full`, `exists_full_ge` (some full step has `2 dr ≥ 2∑α`),
  `exists_full_gt` (if the off-diagonal part is not skew: `2 dr ≥ 2∑α + 2`).
* *Skew layers.* `drift_skew` (the skew cross terms cancel), `pair_bound` (the pair `{x, y}`), the graph
  lemma `graph_lemma` (kernel `decide` over the `2¹⁰` graphs on five vertices) and `skew_drift`.
-/

namespace Z3NetHL.Proofs.TD

open Finset

/-! ## (MIN) -/

lemma min2_of_disj (F : Fin 5 → Fin 5 → ℤ) (h : DisjMinors F) : Min2 F := by
  intro a b c d hab hcd hac had hbc hbd heq
  have hr : Function.Injective ![a, b] := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have hc : Function.Injective ![c, d] := by
    intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  have hd : ∀ i j, ![a, b] i ≠ ![c, d] j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp_all
  apply h 2 ![a, b] ![c, d] hr hc hd
  rw [Matrix.det_fin_two]
  simp [heq]

lemma three_cols : ∀ a b : Fin 5, a ≠ b → ∃ c1 c2 c3 : Fin 5, c1 ≠ c2 ∧ c1 ≠ c3 ∧ c2 ≠ c3 ∧
    c1 ≠ a ∧ c1 ≠ b ∧ c2 ≠ a ∧ c2 ≠ b ∧ c3 ≠ a ∧ c3 ≠ b := by decide

lemma pm1 {x : ℤ} (h : |x| = 1) : x = 1 ∨ x = -1 := by
  rcases abs_eq (zero_le_one) |>.1 h with h | h <;> simp [h]

/-- Two rows that are `±1` on the three columns outside them violate (MIN) (the minor tax of `thm:D`: two of the
three ratios coincide). -/
lemma two_rows (G : Fin 5 → Fin 5 → ℤ) (hmin : Min2 G) (a b : Fin 5) (hab : a ≠ b)
    (h : ∀ d, d ≠ a → d ≠ b → |G a d| = 1 ∧ |G b d| = 1) : False := by
  obtain ⟨c1, c2, c3, h12, h13, h23, h1a, h1b, h2a, h2b, h3a, h3b⟩ := three_cols a b hab
  have k12 := hmin a b c1 c2 hab h12 (Ne.symm h1a) (Ne.symm h2a) (Ne.symm h1b) (Ne.symm h2b)
  have k13 := hmin a b c1 c3 hab h13 (Ne.symm h1a) (Ne.symm h3a) (Ne.symm h1b) (Ne.symm h3b)
  have k23 := hmin a b c2 c3 hab h23 (Ne.symm h2a) (Ne.symm h3a) (Ne.symm h2b) (Ne.symm h3b)
  rcases pm1 (h c1 h1a h1b).1 with x1 | x1 <;> rcases pm1 (h c1 h1a h1b).2 with y1 | y1 <;>
  rcases pm1 (h c2 h2a h2b).1 with x2 | x2 <;> rcases pm1 (h c2 h2a h2b).2 with y2 | y2 <;>
  rcases pm1 (h c3 h3a h3b).1 with x3 | x3 <;> rcases pm1 (h c3 h3a h3b).2 with y3 | y3 <;>
  · rw [x1, x2, y1, y2] at k12; rw [x1, x3, y1, y3] at k13; rw [x2, x3, y2, y3] at k23
    omega

/-! ## The diagonal -/

/-- `m_c = max_{d ≠ c} |F[c][d]|` (doubled). -/
def mrow (F : Fin 5 → Fin 5 → ℤ) (c : Fin 5) : ℤ :=
  (((univ.erase c).sup fun d => (F c d).natAbs : ℕ) : ℤ)

lemma le_mrow (F : Fin 5 → Fin 5 → ℤ) (c d : Fin 5) (hd : d ≠ c) : |F c d| ≤ mrow F c := by
  have : (F c d).natAbs ≤ (univ.erase c).sup fun d => (F c d).natAbs :=
    Finset.le_sup (f := fun d => (F c d).natAbs) (mem_erase.mpr ⟨hd, mem_univ _⟩)
  rw [mrow, Int.abs_eq_natAbs]; exact_mod_cast this

lemma mrow_attained (F : Fin 5 → Fin 5 → ℤ) (c : Fin 5) : ∃ d, d ≠ c ∧ |F c d| = mrow F c := by
  have hne : (univ.erase c).Nonempty := ⟨c + 1, mem_erase.mpr ⟨by fin_cases c <;> decide, mem_univ _⟩⟩
  obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup _ hne fun d => (F c d).natAbs
  refine ⟨d, (mem_erase.mp hd).1, ?_⟩
  rw [mrow, he, Int.abs_eq_natAbs]

lemma mrow_odd (F : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F c d)) (c : Fin 5) : Odd (mrow F c) := by
  obtain ⟨d, -, he⟩ := mrow_attained F c
  rw [← he, Int.abs_eq_natAbs, Int.odd_coe_nat]
  exact Int.natAbs_odd.mpr (hodd c d)

lemma mrow_congr (F G : Fin 5 → Fin 5 → ℤ) (h : ∀ c d, c ≠ d → G c d = F c d) (c : Fin 5) :
    mrow G c = mrow F c := by
  unfold mrow
  have : ((univ.erase c).sup fun d => (G c d).natAbs) = (univ.erase c).sup fun d => (F c d).natAbs :=
    Finset.sup_congr rfl fun d hd => by rw [h c d (Ne.symm (mem_erase.mp hd).1)]
  rw [this]

/-- The layer with every `α_c` lowered to `m_c`. -/
def lower (F : Fin 5 → Fin 5 → ℤ) (c d : Fin 5) : ℤ := if c = d then -mrow F c else F c d

lemma dotR_lower (F : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) :
    dotR (lower F) E c = dotR F E c + (-mrow F c - F c c) * E c := by
  have : ∀ d, lower F c d * E d = F c d * E d + (if c = d then (-mrow F c - F c c) * E c else 0) := by
    intro d; unfold lower; split_ifs with h
    · subst h; ring
    · ring
  simp only [dotR, this, sum_add_distrib, sum_ite_eq, mem_univ, ite_true]

/-- *Diagonal* (`thm:D`): lowering the diagonal to `m` does not increase `2 dr(E)` (under (B2)). -/
lemma drift_lower (F : Fin 5 → Fin 5 → ℤ) (hB2 : B2D F) (E : Fin 5 → ℤ)
    (hE : ∀ d, -1 ≤ E d ∧ E d ≤ 1) : drift2E (lower F) E ≤ drift2E F E := by
  unfold drift2E
  refine sum_le_sum fun c _ => ?_
  unfold drc2
  rw [dotR_lower]
  have hm : mrow F c ≤ -F c c := by
    obtain ⟨d, hd, he⟩ := mrow_attained F c
    rw [← he]; exact hB2 c d hd
  split_ifs with h0
  · rw [h0]; simp
  · have h1 : E c * E c = 1 := by
      have := hE c; rcases (show E c = 1 ∨ E c = -1 by omega) with h | h <;> rw [h] <;> norm_num
    nlinarith

lemma lower_offdiag (F : Fin 5 → Fin 5 → ℤ) (c d : Fin 5) (h : c ≠ d) : lower F c d = F c d := by
  simp [lower, h]

lemma lower_diag (F : Fin 5 → Fin 5 → ℤ) (c : Fin 5) : lower F c c = -mrow (lower F) c := by
  rw [mrow_congr F (lower F) (fun c d h => lower_offdiag F c d h)]; simp [lower]

lemma lower_odd (F : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F c d)) (c d : Fin 5) : Odd (lower F c d) := by
  unfold lower; split_ifs
  · exact (mrow_odd F hodd c).neg
  · exact hodd c d

lemma lower_min2 (F : Fin 5 → Fin 5 → ℤ) (h : Min2 F) : Min2 (lower F) := by
  intro a b c d hab hcd hac had hbc hbd
  rw [lower_offdiag F a c hac, lower_offdiag F b d hbd, lower_offdiag F a d had, lower_offdiag F b c hbc]
  exact h a b c d hab hcd hac had hbc hbd

/-! ## The minor tax -/

lemma light_row (G : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (G c d)) (c : Fin 5) (h : mrow G c = 1)
    (d : Fin 5) (hd : d ≠ c) : |G c d| = 1 := by
  have h1 := le_mrow G c d hd
  have h2 : (1 : ℤ) ≤ |G c d| := Int.one_le_abs (by obtain ⟨k, hk⟩ := hodd c d; omega)
  omega

/-- *Minor tax* (`thm:D`): at most one light row. -/
lemma minor_tax (G : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (G c d)) (hmin : Min2 G) (a b : Fin 5)
    (hab : a ≠ b) (ha : mrow G a = 1) (hb : mrow G b = 1) : False :=
  two_rows G hmin a b hab fun d hda hdb => ⟨light_row G hodd a ha d hda, light_row G hodd b hb d hdb⟩

lemma mrow_pos (G : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (G c d)) (c : Fin 5) : 1 ≤ mrow G c := by
  obtain ⟨d, hd, he⟩ := mrow_attained G c
  rw [← he]; exact Int.one_le_abs (by obtain ⟨k, hk⟩ := hodd c d; omega)

/-- `∑ m ≥ 13`, and `∑ m ≤ 14` only with one light row and `m = 3` on the other four (doubled). -/
lemma sum_mrow (G : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (G c d)) (hmin : Min2 G) :
    13 ≤ ∑ c, mrow G c ∧ (∑ c, mrow G c ≤ 14 →
      ∃ l, mrow G l = 1 ∧ ∀ c, c ≠ l → mrow G c = 3) := by
  have hp := mrow_pos G hodd
  have ho : ∀ c, mrow G c % 2 = 1 := fun c => by
    obtain ⟨k, hk⟩ := mrow_odd G hodd c; omega
  have ht : ∀ a b, a ≠ b → mrow G a ≠ 1 ∨ mrow G b ≠ 1 := fun a b hab => by
    by_contra hc; push Not at hc; exact minor_tax G hodd hmin a b hab hc.1 hc.2
  rw [Fin.sum_univ_five]
  have p0 := hp 0; have p1 := hp 1; have p2 := hp 2; have p3 := hp 3; have p4 := hp 4
  have o0 := ho 0; have o1 := ho 1; have o2 := ho 2; have o3 := ho 3; have o4 := ho 4
  have t01 := ht 0 1 (by decide); have t02 := ht 0 2 (by decide); have t03 := ht 0 3 (by decide)
  have t04 := ht 0 4 (by decide); have t12 := ht 1 2 (by decide); have t13 := ht 1 3 (by decide)
  have t14 := ht 1 4 (by decide); have t23 := ht 2 3 (by decide); have t24 := ht 2 4 (by decide)
  have t34 := ht 3 4 (by decide)
  refine ⟨by omega, fun hle => ?_⟩
  by_cases e0 : mrow G 0 = 1
  · refine ⟨0, e0, fun c hc => ?_⟩
    fin_cases c
    · exact absurd rfl hc
    all_goals first | (show mrow G 1 = 3; omega) | (show mrow G 2 = 3; omega) | (show mrow G 3 = 3; omega) |
      (show mrow G 4 = 3; omega)
  by_cases e1 : mrow G 1 = 1
  · refine ⟨1, e1, fun c hc => ?_⟩
    fin_cases c
    · show mrow G 0 = 3; omega
    · exact absurd rfl hc
    all_goals first | (show mrow G 2 = 3; omega) | (show mrow G 3 = 3; omega) | (show mrow G 4 = 3; omega)
  by_cases e2 : mrow G 2 = 1
  · refine ⟨2, e2, fun c hc => ?_⟩
    fin_cases c
    · show mrow G 0 = 3; omega
    · show mrow G 1 = 3; omega
    · exact absurd rfl hc
    all_goals first | (show mrow G 3 = 3; omega) | (show mrow G 4 = 3; omega)
  by_cases e3 : mrow G 3 = 1
  · refine ⟨3, e3, fun c hc => ?_⟩
    fin_cases c
    · show mrow G 0 = 3; omega
    · show mrow G 1 = 3; omega
    · show mrow G 2 = 3; omega
    · exact absurd rfl hc
    · show mrow G 4 = 3; omega
  by_cases e4 : mrow G 4 = 1
  · refine ⟨4, e4, fun c hc => ?_⟩
    fin_cases c
    · show mrow G 0 = 3; omega
    · show mrow G 1 = 3; omega
    · show mrow G 2 = 3; omega
    · show mrow G 3 = 3; omega
    · exact absurd rfl hc
  omega

end Z3NetHL.Proofs.TD

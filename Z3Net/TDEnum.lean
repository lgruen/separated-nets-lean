/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.TDCertAll

@[expose] public section

/-!
# V14 stage S11′: `thm:D`, soundness of the enumeration

`normal_drift`: every normalized layer (doubled; row `4` = `(1, 1, 1, 1, −1)`, heavy rows `c < 4` with diagonal
`−3`, off-diagonal entries in `{±1, ±3}` and at least one `±3`) whose disjoint `2 × 2` minors are nonzero has a
binding step `E` with `2 dr(E) ≥ 17`. From the kernel runs `chkTop_cand0` (`Z3Net/TDCertAll.lean`).
-/

namespace Z3NetHL.Proofs.TD

open Finset

/-- (MIN) at `s = 5` as it is used: every `2 × 2` minor on two rows `{a, b}` and two columns `{c, d}` disjoint
from them is nonzero. -/
def Min2 (F : Fin 5 → Fin 5 → ℤ) : Prop :=
  ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d → F a c * F b d ≠ F a d * F b c

lemma m3_true {x0 x1 x2 y0 y1 y2 : ℤ} (h1 : x0 * y1 ≠ x1 * y0) (h2 : x0 * y2 ≠ x2 * y0)
    (h3 : x1 * y2 ≠ x2 * y1) : m3 x0 x1 x2 y0 y1 y2 = true := by
  simp [m3, h1, h2, h3]

section
variable (F : Fin 5 → Fin 5 → ℤ) (h : Min2 F)
include h

lemma pOK01 : pairOK 0 1 (toR5 (F 0)) (toR5 (F 1)) = true :=
  m3_true (h 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
lemma pOK02 : pairOK 0 2 (toR5 (F 0)) (toR5 (F 2)) = true :=
  m3_true (h 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 0 2 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
lemma pOK03 : pairOK 0 3 (toR5 (F 0)) (toR5 (F 3)) = true :=
  m3_true (h 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 0 3 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 0 3 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
lemma pOK12 : pairOK 1 2 (toR5 (F 1)) (toR5 (F 2)) = true :=
  m3_true (h 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 1 2 0 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
lemma pOK13 : pairOK 1 3 (toR5 (F 1)) (toR5 (F 3)) = true :=
  m3_true (h 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 1 3 0 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 1 3 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
lemma pOK23 : pairOK 2 3 (toR5 (F 2)) (toR5 (F 3)) = true :=
  m3_true (h 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 2 3 0 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 2 3 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
lemma pOK04 : pairOK 0 4 (toR5 (F 0)) (toR5 (F 4)) = true :=
  m3_true (h 0 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 0 4 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 0 4 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
lemma pOK14 : pairOK 1 4 (toR5 (F 1)) (toR5 (F 4)) = true :=
  m3_true (h 1 4 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 1 4 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 1 4 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
lemma pOK24 : pairOK 2 4 (toR5 (F 2)) (toR5 (F 4)) = true :=
  m3_true (h 2 4 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 2 4 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 2 4 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
lemma pOK34 : pairOK 3 4 (toR5 (F 3)) (toR5 (F 4)) = true :=
  m3_true (h 3 4 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 3 4 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (h 3 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

end

lemma mem_allRows (c : ℕ) {x y z w : ℤ} (hx : x ∈ vals) (hy : y ∈ vals) (hz : z ∈ vals) (hw : w ∈ vals) :
    mkRow c x y z w ∈ allRows c := by
  simp only [allRows, List.mem_flatMap, List.mem_map]
  exact ⟨x, hx, y, hy, z, hz, w, hw, rfl⟩

lemma heavy_of (c : Fin 5) (hc : c ≠ 4) (r : Fin 5 → ℤ) (h : ∃ d, d ≠ c ∧ |r d| = 3) :
    heavyR (c : ℕ) (toR5 r) = true := by
  obtain ⟨d, hd, h3⟩ := h
  have h3' : (r d).natAbs = 3 := by have := Int.abs_eq_natAbs (r d); omega
  fin_cases c <;> fin_cases d <;> simp_all [heavyR, toR5]

lemma mem_bind5 (E : Fin 5 → ℤ) :
    E ∈ bind5 ↔ (∀ d, -1 ≤ E d ∧ E d ≤ 1) ∧ (E 0 + E 1 + E 2 + E 3 + E 4) % 2 = 1 := by
  simp [bind5, Fintype.mem_piFinset, Fin.sum_univ_five]

lemma W_bind : ∀ E ∈ W, E.f ∈ bind5 := by
  intro E hE
  rw [mem_bind5]
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> decide

lemma drc_eq (F : Fin 5 → Fin 5 → ℤ) (E : R5) (c : Fin 5) :
    drc2 F E.f c = drc (toR5 (F c)) c E := by
  have hd : dotR F E.f c = dot5 (toR5 (F c)) E := by
    simp only [dotR, Fin.sum_univ_five, dot5, toR5, R5.f]
    simp
  have hg : E.f c = E.g c := by fin_cases c <;> rfl
  rw [drc2, drc, hd, hg]

lemma drift2E_eq (F : Fin 5 → Fin 5 → ℤ) (E : R5) :
    drift2E F E.f = drc (toR5 (F 0)) 0 E + drc (toR5 (F 1)) 1 E + drc (toR5 (F 2)) 2 E +
      drc (toR5 (F 3)) 3 E + drc (toR5 (F 4)) 4 E := by
  rw [drift2E, Fin.sum_univ_five, drc_eq, drc_eq, drc_eq, drc_eq, drc_eq]
  rfl

/-- **Soundness of the enumeration** (`thm:D`, the non-skew case): every normalized layer with (MIN) has a binding
step with `2 dr(E) ≥ 17`. -/
theorem normal_drift (F : Fin 5 → Fin 5 → ℤ) (h4 : toR5 (F 4) = row4)
    (hdiag : ∀ c : Fin 5, c ≠ 4 → F c c = -3) (hval : ∀ c d : Fin 5, c ≠ 4 → d ≠ c → F c d ∈ vals)
    (hheavy : ∀ c : Fin 5, c ≠ 4 → ∃ d, d ≠ c ∧ |F c d| = 3) (hmin : Min2 F) :
    ∃ E ∈ bind5, 17 ≤ drift2E F E := by
  have e0 : toR5 (F 0) = mkRow 0 (F 0 1) (F 0 2) (F 0 3) (F 0 4) := by
    simp [toR5, mkRow, hdiag 0 (by decide)]
  have e1 : toR5 (F 1) = mkRow 1 (F 1 0) (F 1 2) (F 1 3) (F 1 4) := by
    simp [toR5, mkRow, hdiag 1 (by decide)]
  have e2 : toR5 (F 2) = mkRow 2 (F 2 0) (F 2 1) (F 2 3) (F 2 4) := by
    simp [toR5, mkRow, hdiag 2 (by decide)]
  have e3 : toR5 (F 3) = mkRow 3 (F 3 0) (F 3 1) (F 3 2) (F 3 4) := by
    simp [toR5, mkRow, hdiag 3 (by decide)]
  have v := fun c d (hc : c ≠ (4 : Fin 5)) (hd : d ≠ c) => hval c d hc hd
  have m0 : toR5 (F 0) ∈ cand 0 := by
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · rw [e0]; exact mem_allRows 0 (v 0 1 (by decide) (by decide)) (v 0 2 (by decide) (by decide))
        (v 0 3 (by decide) (by decide)) (v 0 4 (by decide) (by decide))
    · have hh := heavy_of 0 (by decide) _ (hheavy 0 (by decide))
      rw [← h4, pOK04 F hmin]; simpa using hh
  have m1 : toR5 (F 1) ∈ cand 1 := by
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · rw [e1]; exact mem_allRows 1 (v 1 0 (by decide) (by decide)) (v 1 2 (by decide) (by decide))
        (v 1 3 (by decide) (by decide)) (v 1 4 (by decide) (by decide))
    · have hh := heavy_of 1 (by decide) _ (hheavy 1 (by decide))
      rw [← h4, pOK14 F hmin]; simpa using hh
  have m2 : toR5 (F 2) ∈ cand 2 := by
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · rw [e2]; exact mem_allRows 2 (v 2 0 (by decide) (by decide)) (v 2 1 (by decide) (by decide))
        (v 2 3 (by decide) (by decide)) (v 2 4 (by decide) (by decide))
    · have hh := heavy_of 2 (by decide) _ (hheavy 2 (by decide))
      rw [← h4, pOK24 F hmin]; simpa using hh
  have m3' : toR5 (F 3) ∈ cand 3 := by
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · rw [e3]; exact mem_allRows 3 (v 3 0 (by decide) (by decide)) (v 3 1 (by decide) (by decide))
        (v 3 2 (by decide) (by decide)) (v 3 4 (by decide) (by decide))
    · have hh := heavy_of 3 (by decide) _ (hheavy 3 (by decide))
      rw [← h4, pOK34 F hmin]; simpa using hh
  have htop := chkTop_cand0 _ m0
  simp only [chkTop, List.all_eq_true, List.mem_filter, Bool.and_eq_true] at htop
  have hleaf := htop _ ⟨m1, pOK01 F hmin⟩ _ ⟨m2, pOK02 F hmin, pOK12 F hmin⟩ _
    ⟨m3', ⟨pOK03 F hmin, pOK13 F hmin⟩, pOK23 F hmin⟩
  simp only [leaf, List.any_eq_true, decide_eq_true_eq] at hleaf
  obtain ⟨E, hE, hle⟩ := hleaf
  refine ⟨E.f, W_bind E hE, ?_⟩
  rw [drift2E_eq, h4]
  exact hle

end Z3NetHL.Proofs.TD

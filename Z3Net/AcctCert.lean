/-
`rem:accounting` (first-order accounting): the finite checks for `𝒬*_p` and for the printed layer without (Λ), of the
manuscript *Low-discrepancy quasi-uniform digital nets in every dimension* (`paper/core.tex`). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.AcctLow
public import Z3Net.Q5Sep

@[expose] public section

/-!
# V14 stage S13′: `rem:accounting`, the finite checks (kernel `decide`)

* `𝒬*_p`: `2 dj(F₀*, D₁) = 17` (`dj2_star`, the `3⁵` steps of `{-1,0,1}⁵`), `det 2F₀* = −880` (`detL`), and
  `∑_c (2ℓ_c(E))² ≥ 8` (`|ℓ(E)|² ≥ 2`) on every non-binding step (`lam_star8`, the `5⁵ − 1` steps).
* The printed layer `F2cex`: (Half), (B2), (MIN), `det = 560`, and at `E = (1,−1,−2,−1,−1)`: `2β = (4,−6,−2,−2,−2)`,
  not binding, `∑_c (2ℓ_c(E))² = 4` (`|ℓ(E)| = 1`).
-/

namespace Z3NetHL.Proofs.Acct

open Finset Matrix Z3NetHL Z3NetHL.Proofs Z3NetHL.Proofs.Q5

set_option maxRecDepth 100000

/-! ## `2ℓ` as `hLinf` -/

lemma ell2_eq (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) :
    ell2 F2 E c = hLinf (oddB E) (E c) (dotR F2 E c) := by
  unfold ell2 hLinf oddB
  by_cases h : (∑ d, E d) % 2 = 1
  · rw [if_pos h, if_pos (by simpa using h)]
  · rw [if_neg h, if_neg (by simpa using h),
      show 2 * E c - 2 * Int.sign (dotR F2 E c) = 2 * (E c - Int.sign (dotR F2 E c)) by ring,
      abs_mul, abs_mul, abs_two, mul_min_of_nonneg _ _ (by norm_num : (0 : ℤ) ≤ 2)]

/-! ## `2 dj(F₀*, D₁) = 17` -/

lemma dj_star_le : ∀ E ∈ bind5, drift2E F2star E + 2 * (nHarm F2star D1star E : ℤ) ≤ 17 := by
  intro E hE
  rw [TD.mem_bind5] at hE
  obtain ⟨hr, hs⟩ := hE
  have m : ∀ d, E d = -1 ∨ E d = 0 ∨ E d = 1 := fun d => by have := hr d; omega
  have key : ∀ e0 e1 e2 e3 e4 : ℤ, (e0 = -1 ∨ e0 = 0 ∨ e0 = 1) → (e1 = -1 ∨ e1 = 0 ∨ e1 = 1) →
      (e2 = -1 ∨ e2 = 0 ∨ e2 = 1) → (e3 = -1 ∨ e3 = 0 ∨ e3 = 1) → (e4 = -1 ∨ e4 = 0 ∨ e4 = 1) →
      (e0 + e1 + e2 + e3 + e4) % 2 = 1 →
      drift2E F2star ![e0, e1, e2, e3, e4] + 2 * (nHarm F2star D1star ![e0, e1, e2, e3, e4] : ℤ) ≤ 17 := by
    intro e0 e1 e2 e3 e4 h0 h1 h2 h3 h4 hp
    rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      rcases h3 with rfl | rfl | rfl <;> rcases h4 with rfl | rfl | rfl <;> revert hp <;> decide
  have e : E = ![E 0, E 1, E 2, E 3, E 4] := by funext i; fin_cases i <;> rfl
  rw [e]
  exact key _ _ _ _ _ (m 0) (m 1) (m 2) (m 3) (m 4) hs

/-- `2 dj(F₀*, D₁) = 17` (`= 2 dr(F₀*)`: `D₁` is lean). -/
theorem dj2_star : dj2 F2star D1star = 17 := by
  refine le_antisymm (Finset.sup'_le _ _ dj_star_le) ?_
  have h := TD.F2star_attained
  have h1 : (17 : ℤ) ≤ drift2E F2star ![0, 1, 1, 1, 0] + 2 * (nHarm F2star D1star ![0, 1, 1, 1, 0] : ℤ) := by
    rw [h.2]; have := Int.natCast_nonneg (nHarm F2star D1star ![0, 1, 1, 1, 0]); linarith
  exact h1.trans (le_dj2 F2star D1star _ h.1)

/-- `det 2F₀* = −880`. -/
theorem det_star : (Matrix.of F2star).det = -880 := by
  rw [← detL_eq]; decide +kernel

/-! ## `|ℓ(E)|² ≥ 2` on the non-binding steps of `F₀*` -/

/-- `E = 0`, or `E` binding, or `∑_c (2ℓ_c)² ≥ 8`, at the step `e` (for `F₀*`). -/
def okL8 (e0 e1 e2 e3 e4 : ℤ) : Bool :=
  decide (e0 = 0 ∧ e1 = 0 ∧ e2 = 0 ∧ e3 = 0 ∧ e4 = 0) ||
  decide (((-1 ≤ e0 ∧ e0 ≤ 1) ∧ (-1 ≤ e1 ∧ e1 ≤ 1) ∧ (-1 ≤ e2 ∧ e2 ≤ 1) ∧ (-1 ≤ e3 ∧ e3 ≤ 1) ∧
    (-1 ≤ e4 ∧ e4 ≤ 1)) ∧ (e0 + e1 + e2 + e3 + e4) % 2 = 1) ||
  (fun o : Bool => decide (8 ≤ hLinf o e0 (fF 0 e0 e1 e2 e3 e4) ^ 2 +
      hLinf o e1 (fF 1 e0 e1 e2 e3 e4) ^ 2 +
      hLinf o e2 (fF 2 e0 e1 e2 e3 e4) ^ 2 +
      hLinf o e3 (fF 3 e0 e1 e2 e3 e4) ^ 2 +
      hLinf o e4 (fF 4 e0 e1 e2 e3 e4) ^ 2)) (decide ((e0 + e1 + e2 + e3 + e4) % 2 = 1))

def chkL8 (e0 : ℤ) : Bool :=
  vals5.all fun e1 => vals5.all fun e2 => vals5.all fun e3 => vals5.all fun e4 => okL8 e0 e1 e2 e3 e4

set_option maxHeartbeats 0 in
theorem chkL8_all : ∀ e0 ∈ vals5, chkL8 e0 = true :=
  forall_vals5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- **(Λ) for `F₀*`, with margin**: `|ℓ(E)|² ≥ 2` (i.e. `∑_c (2ℓ_c(E))² ≥ 8`) on every non-binding step. -/
theorem lam_star8 : ∀ E ∈ halfSteps 5, E ∉ bind5 → 8 ≤ ∑ c, ell2 F2star E c ^ 2 := by
  intro E hE hnb
  have m := vals5_of E hE
  have h := chkL8_all (E 0) (m 0)
  simp only [chkL8, List.all_eq_true] at h
  have h' := h _ (m 1) _ (m 2) _ (m 3) _ (m 4)
  simp only [okL8, Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with (h' | h') | h'
  · exact absurd h' (ne_zero5 E (halfSteps_mem hE).1)
  · exfalso; apply hnb
    rw [TD.mem_bind5]
    refine ⟨fun d => ?_, h'.2⟩
    obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, ⟨c0, c1⟩, ⟨d0, d1⟩, ⟨e0, e1⟩⟩ := h'.1
    fin_cases d <;> simp_all
  · have e : ∀ c, ell2 F2star E c = hLinf (oddB E) (E c) (fF c (E 0) (E 1) (E 2) (E 3) (E 4)) := fun c => by
      rw [ell2_eq, dotF]
    simp only [Fin.sum_univ_five, e, oddB]
    exact h'

/-! ## The printed layer without (Λ) -/

lemma F2cex_odd : ∀ c d, Odd (F2cex c d) := by decide

lemma F2cex_B2 : B2D F2cex := by unfold B2D; decide

lemma F2cex_min2 : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    F2cex a c * F2cex b d - F2cex a d * F2cex b c ≠ 0 := by decide

lemma F2cex_disj : DisjMinors F2cex := by
  intro n r c hr hc hdisj
  have hn : n ≤ 2 := by
    have h1 : (univ.image r).card = n := by rw [card_image_of_injective _ hr]; simp
    have h2 : (univ.image c).card = n := by rw [card_image_of_injective _ hc]; simp
    have hd : Disjoint (univ.image r) (univ.image c) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨i, -, rfl⟩ := mem_image.mp ha
      obtain ⟨j, -, hj⟩ := mem_image.mp hb
      exact hdisj i j hj.symm
    have := card_union_of_disjoint hd
    have h5 : (univ.image r ∪ univ.image c).card ≤ 5 := by
      calc _ ≤ (univ : Finset (Fin 5)).card := card_le_univ _
        _ = 5 := by simp
    omega
  interval_cases n
  · simp
  · rw [Matrix.det_unique, Matrix.of_apply]
    obtain ⟨k, hk⟩ := F2cex_odd (r default) (c default)
    omega
  · rw [Matrix.det_fin_two]
    exact F2cex_min2 (r 0) (r 1) (c 0) (c 1) (fun h => by have := hr h; simp at this)
      (fun h => by have := hc h; simp at this) (Ne.symm (hdisj 0 0) |>.symm) (hdisj 0 1)
      (hdisj 1 0) (hdisj 1 1)

theorem det_cex : (Matrix.of F2cex).det = 560 := by
  rw [← detL_eq]; decide +kernel

theorem cex_step : ![1, -1, -2, -1, -1] ∈ halfSteps 5 ∧ ![1, -1, -2, -1, -1] ∉ bind5 ∧
    (fun c => dotR F2cex ![1, -1, -2, -1, -1] c) = ![4, -6, -2, -2, -2] ∧
    ∑ c, ell2 F2cex ![1, -1, -2, -1, -1] c ^ 2 = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_halfSteps]; refine ⟨fun d => by fin_cases d <;> decide, by decide⟩
  · rw [TD.mem_bind5]; decide
  · funext c; fin_cases c <;> decide
  · decide

theorem cex_not_lam : ¬ LamHyp F2cex := fun h => by
  have := h _ cex_step.1 cex_step.2.1
  rw [cex_step.2.2.2] at this
  norm_num at this

end Z3NetHL.Proofs.Acct

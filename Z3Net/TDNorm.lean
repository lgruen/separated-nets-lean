/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.TDSkew

@[expose] public section

/-!
# V14 stage S11′: `thm:D`, the normalization and the assembly

* `conj_drift`, `conj_bind`, `conj_min2`: conjugation by a permutation `σ` and a diagonal sign matrix `ε`
  (`N_cd = ε_c ε_d G_{σc,σd}`) maps binding steps to binding steps (`E ↦ E'`, `E'_{σc} = ε_c E_c`) and keeps
  `2 dr` and the disjoint minors (up to sign); this is the symmetry reduction of the printed proof.
* `light_normal`: a layer with one light row `ℓ` and `m = 3/2` on the four other rows is conjugated (by the
  transposition `(ℓ 4)` and the signs of row `ℓ`) to a normalized layer of `Z3Net/TDEnum.lean`, whose enumeration
  gives the bound.
* `thmD_core`: `thm:D` (the lower bound), in the order of the printed proof: *Diagonal*, then skew layers
  (`skew_drift`, hand proof) or *balance* (`skew_of_full_le`) with the *minor tax* (`sum_mrow`), the normalized
  case by the enumeration.
* `F2star_*`: `F₀*` satisfies (Half), (B2), (MIN) and `2 dr(F₀*) = 17`.
-/

namespace Z3NetHL.Proofs.TD

open Finset

/-! ## Conjugation -/

section conj

variable (G : Fin 5 → Fin 5 → ℤ) (σ : Equiv.Perm (Fin 5)) (ε : Fin 5 → ℤ)

/-- The conjugate layer `N_cd = ε_c ε_d G_{σc,σd}`. -/
def conjL (c d : Fin 5) : ℤ := ε c * ε d * G (σ c) (σ d)

/-- The conjugate step: `E'_i = ε_{σ⁻¹ i} E_{σ⁻¹ i}`. -/
def conjE (E : Fin 5 → ℤ) (i : Fin 5) : ℤ := ε (σ.symm i) * E (σ.symm i)

variable {G σ ε}

lemma conjE_apply (E : Fin 5 → ℤ) (c : Fin 5) : conjE σ ε E (σ c) = ε c * E c := by
  simp [conjE]

lemma dotR_conj (hε : ∀ c, ε c = 1 ∨ ε c = -1) (E : Fin 5 → ℤ) (c : Fin 5) :
    dotR (conjL G σ ε) E c = ε c * dotR G (conjE σ ε E) (σ c) := by
  unfold dotR conjL
  rw [mul_sum, ← Equiv.sum_comp σ (fun d' => ε c * (G (σ c) d' * conjE σ ε E d'))]
  refine sum_congr rfl fun d _ => ?_
  rw [conjE_apply]; ring

lemma drc2_conj (hε : ∀ c, ε c = 1 ∨ ε c = -1) (E : Fin 5 → ℤ) (c : Fin 5) :
    drc2 (conjL G σ ε) E c = drc2 G (conjE σ ε E) (σ c) := by
  unfold drc2
  rw [dotR_conj hε, conjE_apply]
  have hε0 : ε c ≠ 0 := by rcases hε c with h | h <;> rw [h] <;> decide
  by_cases h0 : E c = 0
  · rw [if_pos h0, if_pos (by rw [h0, mul_zero]), abs_mul]
    rcases hε c with h | h <;> rw [h] <;> simp
  · rw [if_neg h0, if_neg (mul_ne_zero hε0 h0)]; ring

lemma conj_drift (hε : ∀ c, ε c = 1 ∨ ε c = -1) (E : Fin 5 → ℤ) :
    drift2E (conjL G σ ε) E = drift2E G (conjE σ ε E) := by
  unfold drift2E
  rw [sum_congr rfl fun c _ => drc2_conj hε E c]
  exact Equiv.sum_comp σ (fun c => drc2 G (conjE σ ε E) c)

lemma conj_bind (hε : ∀ c, ε c = 1 ∨ ε c = -1) (E : Fin 5 → ℤ) (hE : E ∈ bind5) :
    conjE σ ε E ∈ bind5 := by
  rw [mem_bind5] at hE ⊢
  obtain ⟨hr, hs⟩ := hE
  refine ⟨fun d => ?_, ?_⟩
  · simp only [conjE]
    have := hr (σ.symm d)
    rcases hε (σ.symm d) with h | h <;> rw [h] <;> constructor <;> linarith
  · have e1 : ∑ i, conjE σ ε E i = ∑ c, ε c * E c := by
      rw [← Equiv.sum_comp σ]; exact sum_congr rfl fun c _ => conjE_apply E c
    have hev : Even (∑ c, ε c * E c - ∑ c, E c) := by
      rw [← sum_sub_distrib]
      refine Finset.even_sum _ fun c _ => ?_
      rcases hε c with h | h <;> rw [h]
      · simp
      · exact ⟨-E c, by ring⟩
    rw [← Fin.sum_univ_five (f := conjE σ ε E), e1]
    rw [← Fin.sum_univ_five (f := E)] at hs
    obtain ⟨k, hk⟩ := hev
    omega

lemma conj_min2 (hε : ∀ c, ε c = 1 ∨ ε c = -1) (hmin : Min2 G) : Min2 (conjL G σ ε) := by
  intro a b c d hab hcd hac had hbc hbd heq
  have hne : ∀ x, ε x ≠ 0 := fun x => by rcases hε x with h | h <;> rw [h] <;> decide
  apply hmin (σ a) (σ b) (σ c) (σ d) (σ.injective.ne hab) (σ.injective.ne hcd) (σ.injective.ne hac)
    (σ.injective.ne had) (σ.injective.ne hbc) (σ.injective.ne hbd)
  unfold conjL at heq
  have h4 : ε a * ε b * ε c * ε d ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hne a) (hne b)) (hne c)) (hne d)
  apply mul_left_cancel₀ h4
  linear_combination heq

end conj

/-! ## The normalized case -/

lemma vals_mem {z : ℤ} (ho : Odd z) (h : |z| ≤ 3) : z ∈ vals := by
  obtain ⟨k, hk⟩ := ho
  simp only [vals, List.mem_cons, List.not_mem_nil, or_false]
  rcases abs_cases z with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- **The normalized case** (`thm:D`, non-skew, `∑ α = 13/2`): one light row `ℓ` and `m = 3/2` elsewhere. The
transposition `(ℓ 4)` and the signs of row `ℓ` normalize the layer; the enumeration gives the bound. -/
theorem light_normal (G : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (G c d)) (hdiag : ∀ c, G c c = -mrow G c)
    (hmin : Min2 G) (l : Fin 5) (hl : mrow G l = 1) (h3 : ∀ c, c ≠ l → mrow G c = 3) :
    ∃ E ∈ bind5, 17 ≤ drift2E G E := by
  set σ : Equiv.Perm (Fin 5) := Equiv.swap l 4 with hσ
  have hσσ : ∀ i, σ (σ i) = i := fun i => Equiv.swap_apply_self _ _ _
  have hσl : ∀ i, σ i = l ↔ i = 4 := fun i => by
    constructor
    · intro h; rw [← hσσ i, h]; simp [hσ]
    · intro h; rw [h]; simp [hσ]
  have hrowl : ∀ d, d ≠ l → |G l d| = 1 := light_row G hodd l hl
  set ε : Fin 5 → ℤ := fun i => if i = 4 then 1 else G l (σ i) with hεdef
  have hε : ∀ c, ε c = 1 ∨ ε c = -1 := by
    intro c; simp only [hεdef]; split_ifs with h
    · exact Or.inl rfl
    · exact pm1 (hrowl _ (fun e => h ((hσl c).mp e)))
  have hε2 : ∀ c, ε c * ε c = 1 := fun c => by rcases hε c with h | h <;> rw [h] <;> norm_num
  set N := conjL G σ ε with hN
  -- the normalized shape
  have h4 : toR5 (N 4) = row4 := by
    have hε4 : ε 4 = 1 := by simp [hεdef]
    have hσ4 : σ 4 = l := by simp [hσ]
    have e : ∀ d : Fin 5, d ≠ 4 → N 4 d = 1 := by
      intro d hd
      have hεd : ε d = G l (σ d) := by simp [hεdef, hd]
      show ε 4 * ε d * G (σ 4) (σ d) = 1
      rw [hε4, hεd, hσ4, one_mul]
      rcases pm1 (hrowl (σ d) (fun e => hd ((hσl d).mp e))) with h | h <;> rw [h] <;> norm_num
    have e4 : N 4 4 = -1 := by
      show ε 4 * ε 4 * G (σ 4) (σ 4) = -1
      rw [hε4, hσ4, hdiag l, hl]; norm_num
    simp only [toR5, row4, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e4]
  have hdiagN : ∀ c : Fin 5, c ≠ 4 → N c c = -3 := by
    intro c hc
    simp only [hN, conjL]
    rw [hε2, one_mul, hdiag, h3 _ (fun e => hc ((hσl c).mp e))]
  have hle3 : ∀ c d, c ≠ l → |G c d| ≤ 3 ∨ d = c := by
    intro c d hc
    by_cases hdc : d = c
    · exact Or.inr hdc
    · exact Or.inl ((le_mrow G c d hdc).trans (h3 c hc).le)
  have habsN : ∀ c d, |N c d| = |G (σ c) (σ d)| := by
    intro c d
    simp only [hN, conjL, abs_mul]
    rcases hε c with h | h <;> rcases hε d with h' | h' <;> rw [h, h'] <;> simp
  have hvalN : ∀ c d : Fin 5, c ≠ 4 → d ≠ c → N c d ∈ vals := by
    intro c d hc hdc
    have hoddN : Odd (N c d) := by
      simp only [hN, conjL]
      rcases hε c with h | h <;> rcases hε d with h' | h' <;> rw [h, h'] <;> simp [hodd]
    refine vals_mem hoddN ?_
    rw [habsN]
    rcases hle3 (σ c) (σ d) (fun e => hc ((hσl c).mp e)) with h | h
    · exact h
    · exact absurd (σ.injective h) hdc
  have hheavyN : ∀ c : Fin 5, c ≠ 4 → ∃ d, d ≠ c ∧ |N c d| = 3 := by
    intro c hc
    obtain ⟨d', hd', he⟩ := mrow_attained G (σ c)
    refine ⟨σ d', fun e => hd' (by rw [← e, hσσ]), ?_⟩
    rw [habsN, hσσ, he, h3 _ (fun e => hc ((hσl c).mp e))]
  obtain ⟨E, hE, hle⟩ := normal_drift N h4 hdiagN hvalN hheavyN (conj_min2 hε hmin)
  exact ⟨conjE σ ε E, conj_bind hε E hE, by rw [← conj_drift hε]; exact hle⟩

/-! ## Assembly -/

/-- **`thm:D`, the lower bound** (doubled): every layer with (Half), (B2) and (MIN) has a binding step `E` with
`2 dr(E) ≥ 17`. -/
theorem thmD_core (F : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F c d)) (hB2 : B2D F) (hmin : DisjMinors F) :
    ∃ E ∈ bind5, 17 ≤ drift2E F E := by
  set G := lower F with hG
  have hGodd : ∀ c d, Odd (G c d) := lower_odd F hodd
  have hGdiag : ∀ c, G c c = -mrow G c := lower_diag F
  have hGmin : Min2 G := lower_min2 F (min2_of_disj F hmin)
  suffices h : ∃ E ∈ bind5, 17 ≤ drift2E G E by
    obtain ⟨E, hE, hle⟩ := h
    refine ⟨E, hE, hle.trans (drift_lower F hB2 E ((mem_bind5 E).mp hE).1)⟩
  by_cases hs : SkewOff G
  · exact skew_drift G hGodd hs hGdiag hGmin
  · -- not skew: some full step has `2 dr ≥ ∑ m + 2`
    have hfull : ∃ E ∈ bind5, ∑ c, mrow G c + 1 < drift2E G E := by
      by_contra hc
      push Not at hc
      exact hs (skew_of_full_le G hGodd hGdiag fun E hE _ => hc E hE)
    obtain ⟨E, hE, hlt⟩ := hfull
    obtain ⟨h13, hstr⟩ := sum_mrow G hGodd hGmin
    have hodd5 : (∑ c, mrow G c) % 2 = 1 := by
      rw [Fin.sum_univ_five]
      have := fun c => mrow_odd G hGodd c
      obtain ⟨a, ha⟩ := this 0; obtain ⟨b, hb⟩ := this 1; obtain ⟨c, hc⟩ := this 2
      obtain ⟨d, hd⟩ := this 3; obtain ⟨e, he⟩ := this 4
      omega
    by_cases h15 : 15 ≤ ∑ c, mrow G c
    · exact ⟨E, hE, by linarith⟩
    · obtain ⟨l, hl, h3⟩ := hstr (by omega)
      exact light_normal G hGodd hGdiag hGmin l hl h3

/-! ## The layer `F₀*` -/

lemma F2star_odd : ∀ c d, Odd (F2star c d) := by decide

lemma F2star_B2 : B2D F2star := by unfold B2D; decide

lemma F2star_min2 : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    F2star a c * F2star b d - F2star a d * F2star b c ≠ 0 := by decide

/-- `F₀*` satisfies (MIN): there are no disjoint square minors of size `≥ 3` in dimension five, the entries are
odd, and the `2 × 2` minors are checked. -/
lemma F2star_disj : DisjMinors F2star := by
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
    obtain ⟨k, hk⟩ := F2star_odd (r default) (c default)
    omega
  · rw [Matrix.det_fin_two]
    exact F2star_min2 (r 0) (r 1) (c 0) (c 1) (fun h => by have := hr h; simp at this)
      (fun h => by have := hc h; simp at this) (Ne.symm (hdisj 0 0) |>.symm) (hdisj 0 1)
      (hdisj 1 0) (hdisj 1 1)

/-- `2 dr(E) ≤ 17` on every binding step of `F₀*`. -/
lemma F2star_le : ∀ E ∈ bind5, drift2E F2star E ≤ 17 := by
  intro E hE
  rw [mem_bind5] at hE
  obtain ⟨hr, hs⟩ := hE
  have m : ∀ d, E d = -1 ∨ E d = 0 ∨ E d = 1 := fun d => by have := hr d; omega
  have key : ∀ e0 e1 e2 e3 e4 : ℤ, (e0 = -1 ∨ e0 = 0 ∨ e0 = 1) → (e1 = -1 ∨ e1 = 0 ∨ e1 = 1) →
      (e2 = -1 ∨ e2 = 0 ∨ e2 = 1) → (e3 = -1 ∨ e3 = 0 ∨ e3 = 1) → (e4 = -1 ∨ e4 = 0 ∨ e4 = 1) →
      (e0 + e1 + e2 + e3 + e4) % 2 = 1 → drift2E F2star ![e0, e1, e2, e3, e4] ≤ 17 := by
    intro e0 e1 e2 e3 e4 h0 h1 h2 h3 h4 hp
    rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      rcases h3 with rfl | rfl | rfl <;> rcases h4 with rfl | rfl | rfl <;> revert hp <;> decide
  have e : E = ![E 0, E 1, E 2, E 3, E 4] := by funext i; fin_cases i <;> rfl
  rw [e]
  exact key _ _ _ _ _ (m 0) (m 1) (m 2) (m 3) (m 4) hs

lemma F2star_attained : ![0, 1, 1, 1, 0] ∈ bind5 ∧ drift2E F2star ![0, 1, 1, 1, 0] = 17 := by
  rw [mem_bind5]; decide

/-- `2 dr(F₀*) = 17`. -/
theorem F2star_drift : drift2 F2star = 17 :=
  le_antisymm (Finset.sup'_le _ _ F2star_le)
    (F2star_attained.2 ▸ Finset.le_sup' (drift2E F2star) F2star_attained.1)

/-- **`thm:D`** (doubled): `2 dr(F₀) ≥ 17` for every `F₀` with (Half), (B2), (MIN). -/
theorem thmD_bound (F : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F c d)) (hB2 : B2D F)
    (hmin : DisjMinors F) : 17 ≤ drift2 F := by
  obtain ⟨E, hE, hle⟩ := thmD_core F hodd hB2 hmin
  exact hle.trans (Finset.le_sup' (drift2E F) hE)

/-- `thm:D`, the skew case alone (the hand part: `skew_drift` after lowering the diagonal). -/
theorem thmD_skew_core (F : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F c d)) (hB2 : B2D F)
    (hmin : DisjMinors F) (hs : ∀ c d, c ≠ d → F c d + F d c = 0) : 17 ≤ drift2 F := by
  have hsG : SkewOff (lower F) := fun c d h => by
    rw [lower_offdiag F c d h, lower_offdiag F d c (Ne.symm h)]; exact hs c d h
  obtain ⟨E, hE, hle⟩ := skew_drift (lower F) (lower_odd F hodd) hsG (lower_diag F)
    (lower_min2 F (min2_of_disj F hmin))
  exact (hle.trans (drift_lower F hB2 E ((mem_bind5 E).mp hE).1)).trans (Finset.le_sup' (drift2E F) hE)

lemma drift2_conj_le (G : Fin 5 → Fin 5 → ℤ) (σ : Equiv.Perm (Fin 5)) (ε : Fin 5 → ℤ)
    (hε : ∀ c, ε c = 1 ∨ ε c = -1) : drift2 (conjL G σ ε) ≤ drift2 G :=
  Finset.sup'_le _ _ fun E hE => by
    rw [conj_drift hε]; exact Finset.le_sup' (drift2E G) (conj_bind hε E hE)

/-- The symmetry of `thm:D`: conjugation by a permutation and a diagonal sign matrix keeps `dr`. -/
theorem drift2_conj (G : Fin 5 → Fin 5 → ℤ) (σ : Equiv.Perm (Fin 5)) (ε : Fin 5 → ℤ)
    (hε : ∀ c, ε c = 1 ∨ ε c = -1) : drift2 (conjL G σ ε) = drift2 G := by
  refine le_antisymm (drift2_conj_le G σ ε hε) ?_
  have hε' : ∀ c, ε (σ.symm c) = 1 ∨ ε (σ.symm c) = -1 := fun c => hε _
  have e : conjL (conjL G σ ε) σ.symm (fun c => ε (σ.symm c)) = G := by
    funext c d
    simp only [conjL, Equiv.apply_symm_apply]
    have h1 : ε (σ.symm c) * ε (σ.symm c) = 1 := by rcases hε (σ.symm c) with h | h <;> rw [h] <;> norm_num
    have h2 : ε (σ.symm d) * ε (σ.symm d) = 1 := by rcases hε (σ.symm d) with h | h <;> rw [h] <;> norm_num
    linear_combination (G c d * ε (σ.symm d) * ε (σ.symm d)) * h1 + G c d * h2
  calc drift2 G = drift2 (conjL (conjL G σ ε) σ.symm (fun c => ε (σ.symm c))) := by rw [e]
    _ ≤ drift2 (conjL G σ ε) := drift2_conj_le _ _ _ hε'

end Z3NetHL.Proofs.TD

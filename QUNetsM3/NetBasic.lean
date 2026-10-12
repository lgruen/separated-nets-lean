/-
`def:dshift` for the nets of `prop:twocoset` and `sec:wnet`: the shifted point set `digitalPtS` of V14 stage S12′ is
the digit-by-digit shift `Z3NetF.dshiftPt` of V14 stage S10′ applied to the unshifted point set `digitalPt`
(`paper/core.tex`). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.NetDefs
public import QUNetsM3.Digits

@[expose] public section

/-!
# Digital `(0,3,3)`-nets: basic lemmas

`digitalPt_eq`, the box-map criterion `isDigitalNet033_of_inj` (three generator matrices), the cell
`cellDigits` of an index and the triangle inequality `sq_tri_lower` in `ℝ³`, used by the proofs of
`prop:twocoset` and `sec:wnet`. V14 stage S16′: moved here from the former modules `EisensteinNet/E1Net`,
`E1Sep`, `E1Core` (the lemmas of the former net 𝓔_p are in the retired Eisenstein development (research history)).
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

theorem digitalPt_eq (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (x : ℕ) (c : Fin 3) :
    digitalPt p C x c = coord p (C c *ᵥ digits p x) := rfl

/-- The box-map criterion for three generator matrices. -/
theorem isDigitalNet033_of_inj [NeZero p] (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p))
    (hC : ∀ d : Fin 3 → ℕ, ∑ c, d c = 3 → ∀ s s' : Fin 3 → ZMod p,
      (∀ c : Fin 3, ∀ i : Fin 3, (i : ℕ) < d c → (C c *ᵥ s) i = (C c *ᵥ s') i) → s = s') :
    IsDigitalNet033 p C := by
  intro d hsum b hb
  have hd : ∀ c, d c ≤ 3 := by
    intro c; rw [Fin.sum_univ_three] at hsum; fin_cases c <;> simp <;> omega
  let f : ℕ → Fin 3 → ℕ := fun x c => digitalPt p C x c / p ^ (3 - d c)
  have hinj : ∀ x x', x < p ^ 3 → x' < p ^ 3 → f x = f x' → x = x' := by
    intro x x' hx hx' hf
    have hs := hC d hsum (digits p x) (digits p x') (fun c =>
      (coord_div_eq_iff _ _ (hd c)).1 (by simpa [f, digitalPt_eq] using congrFun hf c))
    rw [← coord_digits hx, ← coord_digits hx', hs]
  have hcard : (Fintype.piFinset fun c => Finset.range (p ^ d c)).card ≤
      (Finset.range (p ^ 3)).card := by
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range]
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range (p ^ 3))
    (t := Fintype.piFinset fun c => Finset.range (p ^ d c))
    (fun x _ => f x)
    (by
      intro x _
      rw [Fintype.mem_piFinset]
      intro c
      simp only [f, Finset.mem_range, digitalPt_eq]
      exact div_lt_of_lt_cube (hd c) (coord_lt _))
    (fun a₁ a₂ h₁ h₂ h => hinj a₁ a₂ (Finset.mem_range.1 h₁) (Finset.mem_range.1 h₂) h)
    hcard
  obtain ⟨x, hx, hfx⟩ := hsurj b (by rw [Fintype.mem_piFinset]; exact fun c => Finset.mem_range.2 (hb c))
  rw [Finset.mem_range] at hx
  refine ⟨x, ⟨hx, fun c => (congrFun hfx c).symm⟩, ?_⟩
  rintro x' ⟨hx', h'⟩
  apply hinj x' x hx' hx
  funext c
  exact (h' c).trans (congrFun hfx c)

/-- The cell of `x` (its digit values). -/
def cellDigits (p x : ℕ) : Fin 3 → ℕ := fun c => (digits p x c).val

/-- Cauchy–Schwarz form of the triangle inequality in `ℝ³`:
`|u + r|² ≥ (|u| − |r|)²`, with `|u| ≥ α ≥ β ≥ |r|` given through squares. -/
theorem sq_tri_lower (u0 u1 u2 r0 r1 r2 α β : ℝ) (hβ : 0 ≤ β) (hαβ : β ≤ α)
    (hu : α ^ 2 ≤ u0 ^ 2 + u1 ^ 2 + u2 ^ 2) (hr : r0 ^ 2 + r1 ^ 2 + r2 ^ 2 ≤ β ^ 2) :
    (α - β) ^ 2 ≤ (u0 + r0) ^ 2 + (u1 + r1) ^ 2 + (u2 + r2) ^ 2 := by
  set A := u0 ^ 2 + u1 ^ 2 + u2 ^ 2 with hA
  set B := r0 ^ 2 + r1 ^ 2 + r2 ^ 2 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hcs : (u0 * r0 + u1 * r1 + u2 * r2) ^ 2 ≤ A * B := by
    nlinarith [sq_nonneg (u0 * r1 - u1 * r0), sq_nonneg (u0 * r2 - u2 * r0),
      sq_nonneg (u1 * r2 - u2 * r1)]
  have hdot : -(Real.sqrt A * Real.sqrt B) ≤ u0 * r0 + u1 * r1 + u2 * r2 := by
    rw [← Real.sqrt_mul hA0]
    exact (abs_le.1 (Real.abs_le_sqrt hcs)).1
  have hsA : α ≤ Real.sqrt A := Real.le_sqrt_of_sq_le hu
  have hsB : Real.sqrt B ≤ β := by
    rw [show β = Real.sqrt (β ^ 2) from (Real.sqrt_sq hβ).symm]
    exact Real.sqrt_le_sqrt hr
  have hsA2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
  have hsB2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hexp : (u0 + r0) ^ 2 + (u1 + r1) ^ 2 + (u2 + r2) ^ 2 =
      A + 2 * (u0 * r0 + u1 * r1 + u2 * r2) + B := by rw [hA, hB]; ring
  rw [hexp]
  have h1 : (α - β) ^ 2 ≤ (Real.sqrt A - Real.sqrt B) ^ 2 := by
    have : 0 ≤ α - β := by linarith
    have : α - β ≤ Real.sqrt A - Real.sqrt B := by linarith
    nlinarith
  nlinarith

end QUNetsM3

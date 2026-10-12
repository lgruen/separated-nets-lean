/-
`prop:wnet` (1) and the net part of `rem:wstar`: the nets `𝒲_p`, `𝒲*_p` are `(0,3,3)`-nets
(`paper/core.tex`). V14 stage S12′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.WWrap

@[expose] public section

/-!
# `prop:wnet` (1): `genWr p r` is a `(0,3,3)`-net when `1 ≤ ρ < p` and `1 ≤ h − r < p`

Box criterion (`isDigitalNet033_of_inj`) with the ten compositions of `3`; the minors of the proof of
`prop:wnet` (1) are `−ρ, 2ρ, h − r` (depth `2` on one coordinate) and `−4ρ, −3ρ, h − r` (depth `3`),
units for `p ≥ 5` when `1 ≤ ρ < p` and `1 ≤ h − r < p` (the remark `rem:wstar`: the proof needs only this).
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

section rows
variable (r : ℕ) (s : Fin 3 → ZMod p)

theorem genWr_x0 : (genWr p r 0 *ᵥ s) 0 = s 0 := by
  simp [genWr, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genWr_x1 : (genWr p r 0 *ᵥ s) 1 = rhoZ p r * (-s 0 - s 1 + 2 * s 2) := by
  simp [genWr, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
theorem genWr_x2 : (genWr p r 0 *ᵥ s) 2 = s 1 + 2 * s 2 := by
  simp [genWr, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genWr_y0 : (genWr p r 1 *ᵥ s) 0 = s 1 := by
  simp [genWr, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genWr_y1 : (genWr p r 1 *ᵥ s) 1 = rhoZ p r * (-s 0 - s 1 + 2 * s 2) := by
  simp [genWr, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
theorem genWr_y2 : (genWr p r 1 *ᵥ s) 2 = s 0 + s 2 := by
  simp [genWr, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genWr_z0 : (genWr p r 2 *ᵥ s) 0 = s 2 := by
  simp [genWr, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genWr_z1 : (genWr p r 2 *ᵥ s) 1 =
    ((hW p : ZMod p) - r) * (s 0 + s 1) + rhoZ p r * s 2 := by
  simp [genWr, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
theorem genWr_z2 : (genWr p r 2 *ᵥ s) 2 = s 1 := by
  simp [genWr, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem genWr_row0 (c : Fin 3) : (genWr p r c *ᵥ s) 0 = s c := by
  fin_cases c
  · exact genWr_x0 r s
  · exact genWr_y0 r s
  · exact genWr_z0 r s

end rows

/-- `2h = −1` in `𝔽_p` for odd `p`. -/
theorem two_hW (hodd : p % 2 = 1) : 2 * (hW p : ZMod p) = -1 := by
  have h1 : 2 * hW p + 1 = p := by unfold hW; omega
  have : ((2 * hW p + 1 : ℕ) : ZMod p) = 0 := by rw [h1]; simp
  push_cast at this
  linear_combination this

/-- The hypotheses of the net property: `ρ = 2r + 1 < p` and `r < h`. -/
structure WParamOK (p r : ℕ) : Prop where
  rho_lt : 2 * r + 1 < p
  r_lt : r < hW p

theorem rhoZ_ne_zero {r : ℕ} (hr : 2 * r + 1 < p) : rhoZ p r ≠ 0 :=
  natCast_ne_zero_of_lt (by omega) hr

theorem hr_ne_zero {r : ℕ} (hr : r < hW p) (hp : 2 ≤ p) : ((hW p : ZMod p) - r) ≠ 0 := by
  have : ((hW p : ZMod p) - r) = ((hW p - r : ℕ) : ZMod p) := by
    rw [Nat.cast_sub hr.le]
  rw [this]
  exact natCast_ne_zero_of_lt (by omega) (by unfold hW at hr ⊢; omega)

theorem small_ne_zero (hp5 : 5 ≤ p) {k : ℕ} (hk0 : k ≠ 0) (hk : k < 5) :
    (k : ZMod p) ≠ 0 :=
  natCast_ne_zero_of_lt hk0 (by omega)

/-- Injectivity of the selected rows for each of the ten compositions of `3`. -/
theorem w_inj (hp : p.Prime) (hp5 : 5 ≤ p) {r : ℕ} (hpar : WParamOK p r) (d₁ d₂ d₃ : ℕ)
    (hsum : d₁ + d₂ + d₃ = 3) (s s' : Fin 3 → ZMod p)
    (h1 : ∀ i : Fin 3, (i : ℕ) < d₁ → (genWr p r 0 *ᵥ s) i = (genWr p r 0 *ᵥ s') i)
    (h2 : ∀ i : Fin 3, (i : ℕ) < d₂ → (genWr p r 1 *ᵥ s) i = (genWr p r 1 *ᵥ s') i)
    (h3 : ∀ i : Fin 3, (i : ℕ) < d₃ → (genWr p r 2 *ᵥ s) i = (genWr p r 2 *ᵥ s') i) : s = s' := by
  have := Fact.mk hp
  have hρ := rhoZ_ne_zero (p := p) hpar.rho_lt
  have hh := hr_ne_zero (p := p) hpar.r_lt (by omega)
  have h2' : (2 : ZMod p) ≠ 0 := by exact_mod_cast small_ne_zero hp5 (k := 2) (by norm_num) (by norm_num)
  have h3' : (3 : ZMod p) ≠ 0 := by exact_mod_cast small_ne_zero hp5 (k := 3) (by norm_num) (by norm_num)
  have h4' : (4 : ZMod p) ≠ 0 := by exact_mod_cast small_ne_zero hp5 (k := 4) (by norm_num) (by norm_num)
  set ρ := rhoZ p r
  set a : ZMod p := (hW p : ZMod p) - r
  have x0 : 1 ≤ d₁ → s 0 = s' 0 := fun hd => by
    have := h1 0 (by simp; omega); rwa [genWr_x0, genWr_x0] at this
  have x1 : 2 ≤ d₁ → ρ * (-s 0 - s 1 + 2 * s 2) = ρ * (-s' 0 - s' 1 + 2 * s' 2) := fun hd => by
    have := h1 1 (by simp; omega); rwa [genWr_x1, genWr_x1] at this
  have x2 : 3 ≤ d₁ → s 1 + 2 * s 2 = s' 1 + 2 * s' 2 := fun hd => by
    have := h1 2 (by simp; omega); rwa [genWr_x2, genWr_x2] at this
  have y0 : 1 ≤ d₂ → s 1 = s' 1 := fun hd => by
    have := h2 0 (by simp; omega); rwa [genWr_y0, genWr_y0] at this
  have y1 : 2 ≤ d₂ → ρ * (-s 0 - s 1 + 2 * s 2) = ρ * (-s' 0 - s' 1 + 2 * s' 2) := fun hd => by
    have := h2 1 (by simp; omega); rwa [genWr_y1, genWr_y1] at this
  have y2 : 3 ≤ d₂ → s 0 + s 2 = s' 0 + s' 2 := fun hd => by
    have := h2 2 (by simp; omega); rwa [genWr_y2, genWr_y2] at this
  have z0 : 1 ≤ d₃ → s 2 = s' 2 := fun hd => by
    have := h3 0 (by simp; omega); rwa [genWr_z0, genWr_z0] at this
  have z1 : 2 ≤ d₃ → a * (s 0 + s 1) + ρ * s 2 = a * (s' 0 + s' 1) + ρ * s' 2 := fun hd => by
    have := h3 1 (by simp; omega); rwa [genWr_z1, genWr_z1] at this
  have z2 : 3 ≤ d₃ → s 1 = s' 1 := fun hd => by
    have := h3 2 (by simp; omega); rwa [genWr_z2, genWr_z2] at this
  have fin3 : s 0 = s' 0 → s 1 = s' 1 → s 2 = s' 2 → s = s' := by
    intro a b c; funext l; fin_cases l
    · exact a
    · exact b
    · exact c
  have cancel : ∀ {c x : ZMod p}, c ≠ 0 → c * x = 0 → x = 0 := fun hc h =>
    (mul_eq_zero.1 h).resolve_left hc
  have hc : (d₁ = 3 ∧ d₂ = 0 ∧ d₃ = 0) ∨ (d₁ = 0 ∧ d₂ = 3 ∧ d₃ = 0) ∨
      (d₁ = 0 ∧ d₂ = 0 ∧ d₃ = 3) ∨ (d₁ = 2 ∧ d₂ = 1 ∧ d₃ = 0) ∨ (d₁ = 2 ∧ d₂ = 0 ∧ d₃ = 1) ∨
      (d₁ = 1 ∧ d₂ = 2 ∧ d₃ = 0) ∨ (d₁ = 0 ∧ d₂ = 2 ∧ d₃ = 1) ∨ (d₁ = 1 ∧ d₂ = 0 ∧ d₃ = 2) ∨
      (d₁ = 0 ∧ d₂ = 1 ∧ d₃ = 2) ∨ (d₁ = 1 ∧ d₂ = 1 ∧ d₃ = 1) := by
    obtain rfl : d₃ = 3 - d₁ - d₂ := by omega
    have hd₁ : d₁ ≤ 3 := by omega
    have hd₂ : d₂ ≤ 3 := by omega
    interval_cases d₁ <;> interval_cases d₂ <;> first | decide | (exfalso; simp at hsum)
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · -- (3,0,0): minor −4ρ
    have a0 := x0 (by norm_num)
    have u := x1 (by norm_num)
    have v := x2 (by norm_num)
    have e2 : s 2 - s' 2 = 0 := cancel h4' (cancel hρ (by linear_combination u + ρ * v + ρ * a0))
    have e1 : s 1 = s' 1 := by linear_combination v - 2 * e2
    exact fin3 a0 e1 (by linear_combination e2)
  · -- (0,3,0): minor −3ρ
    have b := y0 (by norm_num)
    have u := y1 (by norm_num)
    have v := y2 (by norm_num)
    have e2 : s 2 - s' 2 = 0 := cancel h3' (cancel hρ (by linear_combination u + ρ * v + ρ * b))
    exact fin3 (by linear_combination v - e2) b (by linear_combination e2)
  · -- (0,0,3): minor h − r
    have c := z0 (by norm_num)
    have u := z1 (by norm_num)
    have v := z2 (by norm_num)
    have e0 : s 0 - s' 0 = 0 := cancel hh (by linear_combination u - ρ * c - a * v)
    exact fin3 (by linear_combination e0) v c
  · -- (2,1,0): the entry 2ρ
    have a0 := x0 (by norm_num)
    have u := x1 (by norm_num)
    have b := y0 (by norm_num)
    have e2 : s 2 - s' 2 = 0 := cancel h2' (cancel hρ (by linear_combination u + ρ * a0 + ρ * b))
    exact fin3 a0 b (by linear_combination e2)
  · -- (2,0,1): the entry −ρ
    have a0 := x0 (by norm_num)
    have u := x1 (by norm_num)
    have c := z0 (by norm_num)
    have e1 : s 1 - s' 1 = 0 := cancel hρ (by linear_combination -u - ρ * a0 + 2 * ρ * c)
    exact fin3 a0 (by linear_combination e1) c
  · -- (1,2,0): the entry 2ρ
    have a0 := x0 (by norm_num)
    have b := y0 (by norm_num)
    have u := y1 (by norm_num)
    have e2 : s 2 - s' 2 = 0 := cancel h2' (cancel hρ (by linear_combination u + ρ * a0 + ρ * b))
    exact fin3 a0 b (by linear_combination e2)
  · -- (0,2,1): the entry −ρ
    have b := y0 (by norm_num)
    have u := y1 (by norm_num)
    have c := z0 (by norm_num)
    have e0 : s 0 - s' 0 = 0 := cancel hρ (by linear_combination -u - ρ * b + 2 * ρ * c)
    exact fin3 (by linear_combination e0) b c
  · -- (1,0,2): the entry h − r
    have a0 := x0 (by norm_num)
    have c := z0 (by norm_num)
    have u := z1 (by norm_num)
    have e1 : s 1 - s' 1 = 0 := cancel hh (by linear_combination u - a * a0 - ρ * c)
    exact fin3 a0 (by linear_combination e1) c
  · -- (0,1,2): the entry h − r
    have b := y0 (by norm_num)
    have c := z0 (by norm_num)
    have u := z1 (by norm_num)
    have e0 : s 0 - s' 0 = 0 := cancel hh (by linear_combination u - a * b - ρ * c)
    exact fin3 (by linear_combination e0) b c
  · exact fin3 (x0 (by norm_num)) (y0 (by norm_num)) (z0 (by norm_num))

/-- **`prop:wnet` (1), general `r`**: `genWr p r` is a `(0,3,3)`-net for every prime `p ≥ 5` when
`2r + 1 < p` and `r < h`. -/
theorem w_net_gen (hp : p.Prime) (hp5 : 5 ≤ p) {r : ℕ} (hpar : WParamOK p r) :
    IsDigitalNet033 p (genWr p r) := by
  have := Fact.mk hp
  apply isDigitalNet033_of_inj
  intro d hsum s s' h
  rw [Fin.sum_univ_three] at hsum
  exact w_inj hp hp5 hpar (d 0) (d 1) (d 2) hsum s s' (h 0) (h 1) (h 2)

/-- Every cell of side `p⁻¹` holds exactly one point, for any generator matrices whose first rows are
`e_x, e_y, e_z`. -/
theorem cells_of_row0 [NeZero p] (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p))
    (hC : ∀ c s, (C c *ᵥ s) 0 = s c) (b : Fin 3 → ℕ) (hb : ∀ c, b c < p) :
    ∃! x : ℕ, x < p ^ 3 ∧ ∀ c, digitalPt p C x c / p ^ 2 = b c := by
  let w : Fin 3 → ZMod p := fun c => (b c : ZMod p)
  have hcell : ∀ y : Fin 3 → ZMod p, ∀ c, coord p (C c *ᵥ y) / p ^ 2 = (y c).val := by
    intro y c
    rw [coord_def, pack_div_p2 (ZMod.val_lt _) (ZMod.val_lt _), hC]
  refine ⟨coord p w, ⟨coord_lt w, fun c => ?_⟩, ?_⟩
  · rw [digitalPt_eq, digits_coord, hcell]
    simp only [w, ZMod.val_natCast, Nat.mod_eq_of_lt (hb c)]
  · rintro x ⟨hx, hxc⟩
    have hd : digits p x = w := by
      funext c
      have := hxc c
      rw [digitalPt_eq, hcell] at this
      simp only [w, ← this, ZMod.natCast_zmod_val]
    rw [← coord_digits hx, hd]

theorem rW_param (hp5 : 5 ≤ p) : WParamOK p (rW p) :=
  ⟨by unfold rW; omega, by unfold rW hW; omega⟩

/-- **`prop:wnet` (1)** (proof of `W_net`). -/
theorem w_net (hp : p.Prime) (hp5 : 5 ≤ p) : IsDigitalNet033 p (genW p) :=
  w_net_gen hp hp5 (rW_param hp5)

/-- **`prop:wnet` (1), the cells** (proof of `W_cells`). -/
theorem w_cells (hp : p.Prime) (b : Fin 3 → ℕ) (hb : ∀ c, b c < p) :
    ∃! x : ℕ, x < p ^ 3 ∧ ∀ c, digitalPt p (genW p) x c / p ^ 2 = b c := by
  have := Fact.mk hp
  exact cells_of_row0 _ (fun c s => genWr_row0 _ s c) b hb

end QUNetsM3

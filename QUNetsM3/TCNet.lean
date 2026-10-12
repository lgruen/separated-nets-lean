/-
Entry TwoCoset: `prop:twocoset` (1), the net property of `𝒯_p` (`paper/core.tex`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import QUNetsM3.TCDefs
public import QUNetsM3.NetBasic

@[expose] public section

/-!
# `prop:twocoset` (1): `𝒯_p` is a `(0,3,3)`-net iff `p ≠ 23`

Box criterion (`isDigitalNet033_of_inj`, entry E1) with the ten compositions of `3`: the
selected rows of `(C_x, C_y, C_z)` determine the index vector iff `h`, `r`, `r − 3`, `5r + 1`
are nonzero in `𝔽_p` (the box minors of the proof of `prop:twocoset`).  `r = 3` iff
`20 ≤ p ≤ 27`, i.e. `p = 23` among primes; at `p = 23` the box with depth `3` on `y` contains
the indices `0` and `549 = (1, 0, 20)₂₃`.
-/

namespace QUNetsM3

open Matrix

variable {p : ℕ}

theorem genTC_x0 (s : Fin 3 → ZMod p) : (genTC p 0 *ᵥ s) 0 = s 0 := by
  simp [genTC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genTC_x1 (s : Fin 3 → ZMod p) : (genTC p 0 *ᵥ s) 1 = hTC p * (s 1 + s 2) := by
  simp [genTC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
theorem genTC_x2 (s : Fin 3 → ZMod p) : (genTC p 0 *ᵥ s) 2 = s 1 + 2 * s 2 := by
  simp [genTC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genTC_y0 (s : Fin 3 → ZMod p) : (genTC p 1 *ᵥ s) 0 = s 1 := by
  simp [genTC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genTC_y1 (s : Fin 3 → ZMod p) :
    (genTC p 1 *ᵥ s) 1 = (rTC p : ZMod p) * s 0 - s 1 + s 2 := by
  simp [genTC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
theorem genTC_y2 (s : Fin 3 → ZMod p) : (genTC p 1 *ᵥ s) 2 = 3 * s 0 + s 2 := by
  simp [genTC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genTC_z0 (s : Fin 3 → ZMod p) : (genTC p 2 *ᵥ s) 0 = s 2 := by
  simp [genTC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
theorem genTC_z1 (s : Fin 3 → ZMod p) :
    (genTC p 2 *ᵥ s) 1 = (rTC p : ZMod p) * s 0 - s 1 + s 2 := by
  simp [genTC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
theorem genTC_z2 (s : Fin 3 → ZMod p) : (genTC p 2 *ᵥ s) 2 = s 0 + 5 * s 1 := by
  simp [genTC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- `2h = −1` in `ZMod p` for odd `p`. -/
theorem two_hTC (hodd : p % 2 = 1) : 2 * hTC p = -1 := by
  unfold hTC
  have h1 : 2 * ((p - 1) / 2) + 1 = p := by omega
  have : ((2 * ((p - 1) / 2) + 1 : ℕ) : ZMod p) = 0 := by rw [h1]; simp
  push_cast at this
  linear_combination this

theorem odd_of_prime5 (hp : p.Prime) (hp5 : 5 ≤ p) : p % 2 = 1 := by
  by_contra h
  have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
  rcases (Nat.dvd_prime hp).1 h2 with h' | h' <;> omega

theorem hTC_ne_zero (hp : p.Prime) (hp5 : 5 ≤ p) : hTC p ≠ 0 := by
  have := Fact.mk hp
  intro h
  have := two_hTC (odd_of_prime5 hp hp5)
  rw [h, mul_zero] at this
  exact one_ne_zero (neg_eq_zero.1 this.symm)

/-- The natural number `n < p`, `n ≠ 0` is a nonzero element of `ZMod p`. -/
theorem natCast_ne_zero_of_lt {n : ℕ} (h0 : n ≠ 0) (hlt : n < p) : (n : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact h0 (Nat.eq_zero_of_dvd_of_lt h hlt)

theorem rTC_pos (hp5 : 5 ≤ p) : 1 ≤ rTC p := by unfold rTC; omega
theorem rTC_lt (hp5 : 5 ≤ p) : rTC p < p := by unfold rTC; omega

theorem rTC_ne_zero (hp5 : 5 ≤ p) : (rTC p : ZMod p) ≠ 0 :=
  natCast_ne_zero_of_lt (by have := rTC_pos hp5; omega) (rTC_lt hp5)

theorem rTC_sub3_ne_zero (hp5 : 5 ≤ p) (h23 : p ≠ 23) (hp : p.Prime) :
    (rTC p : ZMod p) - 3 ≠ 0 := by
  have hr := rTC_pos hp5
  rcases lt_or_ge (rTC p) 3 with h | h
  · -- r ∈ {1, 2}: 3 - r ∈ {1, 2} is a nonzero natural below p
    intro h0
    have : ((3 - rTC p : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub h.le]; push_cast; linear_combination -h0
    exact natCast_ne_zero_of_lt (by omega) (by omega) this
  · rcases eq_or_lt_of_le h with h3 | h3
    · exfalso
      -- r = 3 ⟺ 20 ≤ p ≤ 27; the only prime there is 23
      have hlo : 20 ≤ p := by unfold rTC at h3; omega
      have hhi : p ≤ 27 := by unfold rTC at h3; omega
      interval_cases p <;> first | exact h23 rfl | exact absurd hp (by decide)
    · intro h0
      have : ((rTC p - 3 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub h]; push_cast; exact h0
      exact natCast_ne_zero_of_lt (by omega) (by have := rTC_lt hp5; omega) this

theorem rTC_5_ne_zero (hp : p.Prime) (hp5 : 5 ≤ p) : 5 * (rTC p : ZMod p) + 1 ≠ 0 := by
  have hcast : 5 * (rTC p : ZMod p) + 1 = ((5 * rTC p + 1 : ℕ) : ZMod p) := by push_cast; ring
  rw [hcast]
  rcases lt_or_ge p 11 with h | h
  · -- p ∈ {5, 7}: r = 1, 5r + 1 = 6
    have hr : rTC p = 1 := by unfold rTC; omega
    rw [hr]
    interval_cases p <;> first | exact absurd hp (by decide) | decide
  · exact natCast_ne_zero_of_lt (by omega) (by unfold rTC; omega)

/-- Injectivity of the selected rows for each of the ten compositions of `3`. -/
theorem tc_inj (hp : p.Prime) (hp5 : 5 ≤ p) (h23 : p ≠ 23) (d₁ d₂ d₃ : ℕ)
    (hsum : d₁ + d₂ + d₃ = 3) (s s' : Fin 3 → ZMod p)
    (h1 : ∀ i : Fin 3, (i : ℕ) < d₁ → (genTC p 0 *ᵥ s) i = (genTC p 0 *ᵥ s') i)
    (h2 : ∀ i : Fin 3, (i : ℕ) < d₂ → (genTC p 1 *ᵥ s) i = (genTC p 1 *ᵥ s') i)
    (h3 : ∀ i : Fin 3, (i : ℕ) < d₃ → (genTC p 2 *ᵥ s) i = (genTC p 2 *ᵥ s') i) : s = s' := by
  have := Fact.mk hp
  have hh := hTC_ne_zero hp hp5
  have hr := rTC_ne_zero hp5
  have hr3 := rTC_sub3_ne_zero hp5 h23 hp
  have hr5 := rTC_5_ne_zero hp hp5
  set r : ZMod p := (rTC p : ZMod p)
  -- the equations, as differences
  have x0 : 1 ≤ d₁ → s 0 = s' 0 := fun hd => by
    have := h1 0 (by simp; omega); rwa [genTC_x0, genTC_x0] at this
  have x1 : 2 ≤ d₁ → hTC p * (s 1 + s 2) = hTC p * (s' 1 + s' 2) := fun hd => by
    have := h1 1 (by simp; omega); rwa [genTC_x1, genTC_x1] at this
  have x2 : 3 ≤ d₁ → s 1 + 2 * s 2 = s' 1 + 2 * s' 2 := fun hd => by
    have := h1 2 (by simp; omega); rwa [genTC_x2, genTC_x2] at this
  have y0 : 1 ≤ d₂ → s 1 = s' 1 := fun hd => by
    have := h2 0 (by simp; omega); rwa [genTC_y0, genTC_y0] at this
  have y1 : 2 ≤ d₂ → r * s 0 - s 1 + s 2 = r * s' 0 - s' 1 + s' 2 := fun hd => by
    have := h2 1 (by simp; omega); rwa [genTC_y1, genTC_y1] at this
  have y2 : 3 ≤ d₂ → 3 * s 0 + s 2 = 3 * s' 0 + s' 2 := fun hd => by
    have := h2 2 (by simp; omega); rwa [genTC_y2, genTC_y2] at this
  have z0 : 1 ≤ d₃ → s 2 = s' 2 := fun hd => by
    have := h3 0 (by simp; omega); rwa [genTC_z0, genTC_z0] at this
  have z1 : 2 ≤ d₃ → r * s 0 - s 1 + s 2 = r * s' 0 - s' 1 + s' 2 := fun hd => by
    have := h3 1 (by simp; omega); rwa [genTC_z1, genTC_z1] at this
  have z2 : 3 ≤ d₃ → s 0 + 5 * s 1 = s' 0 + 5 * s' 1 := fun hd => by
    have := h3 2 (by simp; omega); rwa [genTC_z2, genTC_z2] at this
  have fin3 : s 0 = s' 0 → s 1 = s' 1 → s 2 = s' 2 → s = s' := by
    intro a b c; funext l; fin_cases l
    · exact a
    · exact b
    · exact c
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
  · -- (3,0,0): minor h
    have a := x0 (by norm_num)
    have b := mul_left_cancel₀ hh (x1 (by norm_num))
    have c := x2 (by norm_num)
    have e2 : s 2 = s' 2 := by linear_combination c - b
    exact fin3 a (by linear_combination b - e2) e2
  · -- (0,3,0): minor r - 3
    have b := y0 (by norm_num)
    have u := y1 (by norm_num)
    have v := y2 (by norm_num)
    have e0 : (r - 3) * (s 0 - s' 0) = 0 := by linear_combination u - v + b
    have a : s 0 = s' 0 := sub_eq_zero.1 ((mul_eq_zero.1 e0).resolve_left hr3)
    exact fin3 a b (by linear_combination v - 3 * a)
  · -- (0,0,3): minor 5r + 1
    have c := z0 (by norm_num)
    have u := z1 (by norm_num)
    have v := z2 (by norm_num)
    have e1 : (5 * r + 1) * (s 1 - s' 1) = 0 := by linear_combination -u + c + r * v
    have b : s 1 = s' 1 := sub_eq_zero.1 ((mul_eq_zero.1 e1).resolve_left hr5)
    exact fin3 (by linear_combination v - 5 * b) b c
  · -- (2,1,0)
    have a := x0 (by norm_num)
    have u := mul_left_cancel₀ hh (x1 (by norm_num))
    have b := y0 (by norm_num)
    exact fin3 a b (by linear_combination u - b)
  · -- (2,0,1)
    have a := x0 (by norm_num)
    have u := mul_left_cancel₀ hh (x1 (by norm_num))
    have c := z0 (by norm_num)
    exact fin3 a (by linear_combination u - c) c
  · -- (1,2,0)
    have a := x0 (by norm_num)
    have b := y0 (by norm_num)
    have u := y1 (by norm_num)
    exact fin3 a b (by linear_combination u - r * a + b)
  · -- (0,2,1)
    have b := y0 (by norm_num)
    have u := y1 (by norm_num)
    have c := z0 (by norm_num)
    have e0 : r * (s 0 - s' 0) = 0 := by linear_combination u + b - c
    exact fin3 (sub_eq_zero.1 ((mul_eq_zero.1 e0).resolve_left hr)) b c
  · -- (1,0,2)
    have a := x0 (by norm_num)
    have c := z0 (by norm_num)
    have u := z1 (by norm_num)
    exact fin3 a (by linear_combination r * a + c - u) c
  · -- (0,1,2)
    have b := y0 (by norm_num)
    have c := z0 (by norm_num)
    have u := z1 (by norm_num)
    have e0 : r * (s 0 - s' 0) = 0 := by linear_combination u + b - c
    exact fin3 (sub_eq_zero.1 ((mul_eq_zero.1 e0).resolve_left hr)) b c
  · exact fin3 (x0 (by norm_num)) (y0 (by norm_num)) (z0 (by norm_num))

/-- `prop:twocoset` (1), "if": `𝒯_p` is a `(0,3,3)`-net for `p ≠ 23`. -/
theorem tc_net (hp : p.Prime) (hp5 : 5 ≤ p) (h23 : p ≠ 23) : IsDigitalNet033 p (genTC p) := by
  have := Fact.mk hp
  apply isDigitalNet033_of_inj
  intro d hsum s s' h
  rw [Fin.sum_univ_three] at hsum
  exact tc_inj hp hp5 h23 (d 0) (d 1) (d 2) hsum s s' (h 0) (h 1) (h 2)

/-- `prop:twocoset` (1), "only if": at `p = 23` the box with depth `3` on `y` holds the two
indices `0` and `549`. -/
theorem tc_not_net23 : ¬ IsDigitalNet033 23 (genTC 23) := by
  intro h
  obtain ⟨x, _, hu⟩ := h ![0, 3, 0] (by decide) ![0, 0, 0] (by decide)
  have e0 := hu 0 ⟨by norm_num, by decide +kernel⟩
  have e1 := hu 549 ⟨by norm_num, by decide +kernel⟩
  omega

/-- The box of shape `(1,1,1)` (cells of side `p⁻¹`): one point per cell, every prime `p ≥ 5`. -/
theorem tc_cells (hp : p.Prime) (hp5 : 5 ≤ p) (b : Fin 3 → ℕ) (hb : ∀ c, b c < p) :
    ∃! x : ℕ, x < p ^ 3 ∧ ∀ c, digitalPt p (genTC p) x c / p ^ 2 = b c := by
  have := Fact.mk hp
  have hpos : 0 < p := hp.pos
  -- the point with digits `b` in its cells
  let w : Fin 3 → ZMod p := fun c => (b c : ZMod p)
  have hcell : ∀ y : Fin 3 → ZMod p, ∀ c, coord p (genTC p c *ᵥ y) / p ^ 2 = (y c).val := by
    intro y c
    rw [coord_def, pack_div_p2 (ZMod.val_lt _) (ZMod.val_lt _)]
    fin_cases c
    · simp [genTC_x0]
    · simp [genTC_y0]
    · simp [genTC_z0]
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

end QUNetsM3

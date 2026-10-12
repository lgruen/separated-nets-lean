/-
Proof module of entry Obs: the Cauchy identities `lem:CH`, the frame layer in homogeneous
coordinates, `rem:pm1` and `prop:P`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsDefs

@[expose] public section

/-!
# Entry Obs: `lem:CH`, `rem:pm1`, `prop:P`

Everything follows from `D_dc = -D_cd` and the Plücker relation
`D_ab D_cd - D_ac D_bd + D_ad D_bc = 0`, a polynomial identity in `α, β`. Inverses are handled by
`Ring.inverse` and the relations `D_cd · D_cd⁻¹ = 1` for units.

`rem:pm1` is proved from (X) (not from (P) as in the paper): with all twelve entries `±1` the two
terms of (X) are `±1`, and `±1 ± 1 = 1` forces `1 = 0` or `3 = 0`. This needs no case `p = 5`.
-/

namespace Z3NetF.Proofs

open Finset

noncomputable section

namespace ObsCH

variable {R : Type*} [CommRing R] {ι : Type*}

lemma inverse_neg (x : R) : Ring.inverse (-x) = -Ring.inverse x := by
  by_cases h : IsUnit x
  · obtain ⟨u, rfl⟩ := h
    rw [← Units.val_neg, Ring.inverse_unit, Ring.inverse_unit]
    simp
  · have h' : ¬ IsUnit (-x) := fun h2 => h (by simpa using h2.neg)
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', neg_zero]

lemma Dh_swap (α β : ι → R) (c d : ι) : Z3NetF.Dh α β d c = -Z3NetF.Dh α β c d := by
  unfold Z3NetF.Dh; ring

lemma plucker (α β : ι → R) (a b c d : ι) :
    Z3NetF.Dh α β a b * Z3NetF.Dh α β c d - Z3NetF.Dh α β a c * Z3NetF.Dh α β b d +
      Z3NetF.Dh α β a d * Z3NetF.Dh α β b c = 0 := by
  unfold Z3NetF.Dh; ring

lemma invD_swap (α β : ι → R) (c d : ι) :
    Ring.inverse (Z3NetF.Dh α β d c) = -Ring.inverse (Z3NetF.Dh α β c d) := by
  rw [Dh_swap, inverse_neg]

/-- `X * inverse Y = Z` from `Z * Y = X` for a unit `Y`. -/
lemma mul_inv_eq_of {X Y Z : R} (hY : IsUnit Y) (h : Z * Y = X) : X * Ring.inverse Y = Z := by
  rw [← h, mul_assoc, Ring.mul_inverse_cancel _ hY, mul_one]

variable (α β lam mu : ι → R)

lemma W_unit (h : Z3NetF.CauchyOK α β lam mu) (c d : ι) (hcd : c ≠ d) :
    IsUnit (Z3NetF.cauchyW α β lam mu c d) := by
  unfold Z3NetF.cauchyW
  exact ((h.1 c).mul (h.2.1 d)).mul (h.2.2 c d hcd).ringInverse

lemma Pi_unit (h : Z3NetF.CauchyOK α β lam mu) (c d : ι) (hcd : c ≠ d) :
    IsUnit (Z3NetF.cauchyPi α β lam mu c d) :=
  (W_unit α β lam mu h c d hcd).mul (W_unit α β lam mu h d c hcd.symm)

lemma DI (h : Z3NetF.CauchyOK α β lam mu) (c d : ι) (hcd : c ≠ d) :
    Z3NetF.Dh α β c d * Ring.inverse (Z3NetF.Dh α β c d) = 1 :=
  Ring.mul_inverse_cancel _ (h.2.2 c d hcd)

/-- `π_cd = -ν_c ν_d e_cd²` with `e_cd = D_cd⁻¹`. -/
lemma Pi_eq (c d : ι) : Z3NetF.cauchyPi α β lam mu c d =
    -(lam c * mu c) * (lam d * mu d) * Ring.inverse (Z3NetF.Dh α β c d) ^ 2 := by
  unfold Z3NetF.cauchyPi Z3NetF.cauchyW
  rw [invD_swap α β c d]
  ring

theorem CH_C (h : Z3NetF.CauchyOK α β lam mu) (c d e : ι) (hcd : c ≠ d) (hde : d ≠ e)
    (hce : c ≠ e) :
    Z3NetF.cauchyW α β lam mu c d * Z3NetF.cauchyW α β lam mu d e *
        Z3NetF.cauchyW α β lam mu e c =
      -(Z3NetF.cauchyW α β lam mu d c * Z3NetF.cauchyW α β lam mu e d *
        Z3NetF.cauchyW α β lam mu c e) := by
  unfold Z3NetF.cauchyW
  rw [invD_swap α β c d, invD_swap α β d e, invD_swap α β e c]
  ring

theorem CH_X (h : Z3NetF.CauchyOK α β lam mu) (i j l d : ι) (hij : i ≠ j) (hil : i ≠ l)
    (hid : i ≠ d) (hjl : j ≠ l) (hjd : j ≠ d) (hld : l ≠ d) :
    Z3NetF.cauchyW α β lam mu j i * Z3NetF.cauchyW α β lam mu l d *
        Ring.inverse (Z3NetF.cauchyW α β lam mu j d * Z3NetF.cauchyW α β lam mu l i) +
      Z3NetF.cauchyW α β lam mu i j * Z3NetF.cauchyW α β lam mu l d *
        Ring.inverse (Z3NetF.cauchyW α β lam mu i d * Z3NetF.cauchyW α β lam mu l j) = 1 := by
  set D := Z3NetF.Dh α β
  set e := fun x y => Ring.inverse (D x y)
  have eji : e j i = -e i j := invD_swap α β i j
  have eli : e l i = -e i l := invD_swap α β i l
  have elj : e l j = -e j l := invD_swap α β j l
  have hij' := DI α β lam mu h i j hij
  have hld' := DI α β lam mu h l d hld
  have hjd' := DI α β lam mu h j d hjd
  have hil' := DI α β lam mu h i l hil
  have hid' := DI α β lam mu h i d hid
  have hjl' := DI α β lam mu h j l hjl
  have t1 : Z3NetF.cauchyW α β lam mu j i * Z3NetF.cauchyW α β lam mu l d *
      Ring.inverse (Z3NetF.cauchyW α β lam mu j d * Z3NetF.cauchyW α β lam mu l i) =
      e i j * e l d * D j d * D i l := by
    apply mul_inv_eq_of
    · exact (W_unit α β lam mu h j d hjd).mul (W_unit α β lam mu h l i hil.symm)
    · unfold Z3NetF.cauchyW
      change e i j * e l d * D j d * D i l * (lam j * mu d * e j d * (lam l * mu i * e l i)) =
        lam j * mu i * e j i * (lam l * mu d * e l d)
      rw [eji, eli]
      linear_combination (-(e i j * e l d * lam j * mu d * lam l * mu i) * (D i l * e i l)) * hjd' +
        (-(e i j * e l d * lam j * mu d * lam l * mu i)) * hil'
  have t2 : Z3NetF.cauchyW α β lam mu i j * Z3NetF.cauchyW α β lam mu l d *
      Ring.inverse (Z3NetF.cauchyW α β lam mu i d * Z3NetF.cauchyW α β lam mu l j) =
      -(e i j * e l d * D i d * D j l) := by
    apply mul_inv_eq_of
    · exact (W_unit α β lam mu h i d hid).mul (W_unit α β lam mu h l j hjl.symm)
    · unfold Z3NetF.cauchyW
      change -(e i j * e l d * D i d * D j l) * (lam i * mu d * e i d * (lam l * mu j * e l j)) =
        lam i * mu j * e i j * (lam l * mu d * e l d)
      rw [elj]
      linear_combination (e i j * e l d * lam i * mu d * lam l * mu j * (D j l * e j l)) * hid' +
        (e i j * e l d * lam i * mu d * lam l * mu j) * hjl'
  rw [t1, t2]
  have hp := plucker α β i j l d
  -- `D_il D_jd - D_id D_jl = D_ij D_ld`
  linear_combination (-(e i j * e l d)) * hp + (D l d * e l d) * hij' + hld'

theorem CH_P (h : Z3NetF.CauchyOK α β lam mu) (a b c d : ι) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Z3NetF.chiCH α β a b c d - Z3NetF.psiCH α β a b c d = 1 ∧
      Z3NetF.chiCH α β a b c d ^ 2 = Z3NetF.cauchyPi α β lam mu a b *
        Z3NetF.cauchyPi α β lam mu c d *
        Ring.inverse (Z3NetF.cauchyPi α β lam mu a c * Z3NetF.cauchyPi α β lam mu b d) ∧
      Z3NetF.psiCH α β a b c d ^ 2 = Z3NetF.cauchyPi α β lam mu a b *
        Z3NetF.cauchyPi α β lam mu c d *
        Ring.inverse (Z3NetF.cauchyPi α β lam mu a d * Z3NetF.cauchyPi α β lam mu b c) ∧
      (Z3NetF.chiCH α β a b c d ^ 2 - Z3NetF.psiCH α β a b c d ^ 2 - 1) ^ 2 =
        4 * Z3NetF.psiCH α β a b c d ^ 2 := by
  set D := Z3NetF.Dh α β
  set e := fun x y => Ring.inverse (D x y)
  have hab' := DI α β lam mu h a b hab
  have hcd' := DI α β lam mu h c d hcd
  have hac' := DI α β lam mu h a c hac
  have hbd' := DI α β lam mu h b d hbd
  have had' := DI α β lam mu h a d had
  have hbc' := DI α β lam mu h b c hbc
  have hden : Ring.inverse (D a b * D c d) = e a b * e c d := by
    rw [Ring.mul_inverse_rev, mul_comm]
  have hchi : Z3NetF.chiCH α β a b c d = D a c * D b d * (e a b * e c d) := by
    unfold Z3NetF.chiCH; rw [hden]
  have hpsi : Z3NetF.psiCH α β a b c d = D a d * D b c * (e a b * e c d) := by
    unfold Z3NetF.psiCH; rw [hden]
  have h1 : Z3NetF.chiCH α β a b c d - Z3NetF.psiCH α β a b c d = 1 := by
    rw [hchi, hpsi]
    have hp := plucker α β a b c d
    linear_combination (-(e a b * e c d)) * hp + (D c d * e c d) * hab' + hcd'
  refine ⟨h1, ?_, ?_, ?_⟩
  · symm
    apply mul_inv_eq_of
    · exact (Pi_unit α β lam mu h a c hac).mul (Pi_unit α β lam mu h b d hbd)
    · rw [hchi, Pi_eq, Pi_eq, Pi_eq, Pi_eq]
      change (D a c * D b d * (e a b * e c d)) ^ 2 *
          (-(lam a * mu a) * (lam c * mu c) * e a c ^ 2 * (-(lam b * mu b) * (lam d * mu d) *
            e b d ^ 2)) =
        -(lam a * mu a) * (lam b * mu b) * e a b ^ 2 * (-(lam c * mu c) * (lam d * mu d) *
          e c d ^ 2)
      linear_combination ((lam a * mu a) * (lam b * mu b) * (lam c * mu c) * (lam d * mu d) *
        e a b ^ 2 * e c d ^ 2) * ((D a c * e a c + 1) * (D b d * e b d) ^ 2 * hac' +
          (D b d * e b d + 1) * hbd')
  · symm
    apply mul_inv_eq_of
    · exact (Pi_unit α β lam mu h a d had).mul (Pi_unit α β lam mu h b c hbc)
    · rw [hpsi, Pi_eq, Pi_eq, Pi_eq, Pi_eq]
      change (D a d * D b c * (e a b * e c d)) ^ 2 *
          (-(lam a * mu a) * (lam d * mu d) * e a d ^ 2 * (-(lam b * mu b) * (lam c * mu c) *
            e b c ^ 2)) =
        -(lam a * mu a) * (lam b * mu b) * e a b ^ 2 * (-(lam c * mu c) * (lam d * mu d) *
          e c d ^ 2)
      linear_combination ((lam a * mu a) * (lam b * mu b) * (lam c * mu c) * (lam d * mu d) *
        e a b ^ 2 * e c d ^ 2) * ((D a d * e a d + 1) * (D b c * e b c) ^ 2 * had' +
          (D b c * e b c + 1) * hbc')
  · have : Z3NetF.chiCH α β a b c d = Z3NetF.psiCH α β a b c d + 1 := by
      linear_combination h1
    rw [this]; ring

/-! ## Ordered fields: (C) signs and classes -/

section ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable (α β lam mu : ι → K)

lemma Pi_symm (c d : ι) : Z3NetF.cauchyPi α β lam mu c d = Z3NetF.cauchyPi α β lam mu d c := by
  unfold Z3NetF.cauchyPi; ring

theorem CH_C_neg (h : Z3NetF.CauchyOK α β lam mu) (c d e : ι) (hcd : c ≠ d) (hde : d ≠ e)
    (hce : c ≠ e) :
    Z3NetF.cauchyPi α β lam mu c d * Z3NetF.cauchyPi α β lam mu d e *
      Z3NetF.cauchyPi α β lam mu e c < 0 := by
  have hC := CH_C α β lam mu h c d e hcd hde hce
  have hne : Z3NetF.cauchyW α β lam mu d c * Z3NetF.cauchyW α β lam mu e d *
      Z3NetF.cauchyW α β lam mu c e ≠ 0 :=
    (((W_unit α β lam mu h d c hcd.symm).mul (W_unit α β lam mu h e d hde.symm)).mul
      (W_unit α β lam mu h c e hce)).ne_zero
  have : Z3NetF.cauchyPi α β lam mu c d * Z3NetF.cauchyPi α β lam mu d e *
      Z3NetF.cauchyPi α β lam mu e c =
      -(Z3NetF.cauchyW α β lam mu d c * Z3NetF.cauchyW α β lam mu e d *
        Z3NetF.cauchyW α β lam mu c e) ^ 2 := by
    unfold Z3NetF.cauchyPi
    linear_combination (Z3NetF.cauchyW α β lam mu d c * Z3NetF.cauchyW α β lam mu e d *
        Z3NetF.cauchyW α β lam mu c e) * hC
  rw [this]
  have : 0 < (Z3NetF.cauchyW α β lam mu d c * Z3NetF.cauchyW α β lam mu e d *
      Z3NetF.cauchyW α β lam mu c e) ^ 2 := by positivity
  linarith

theorem CH_C_classes (h : Z3NetF.CauchyOK α β lam mu) :
    Equivalence (fun c d : ι => c = d ∨ Z3NetF.cauchyPi α β lam mu c d < 0) ∧
      ∀ c d e : ι, (c = d ∨ Z3NetF.cauchyPi α β lam mu c d < 0) ∨
        (d = e ∨ Z3NetF.cauchyPi α β lam mu d e < 0) ∨
        (c = e ∨ Z3NetF.cauchyPi α β lam mu c e < 0) := by
  refine ⟨⟨fun c => Or.inl rfl, ?_, ?_⟩, ?_⟩
  · rintro c d (rfl | hcd)
    · exact Or.inl rfl
    · exact Or.inr (by rwa [Pi_symm])
  · rintro c d e (rfl | hcd) (rfl | hde)
    · exact Or.inl rfl
    · exact Or.inr hde
    · exact Or.inr hcd
    · by_cases hce : c = e
      · exact Or.inl hce
      have hcd' : c ≠ d := by
        rintro rfl
        have := mul_self_nonneg (Z3NetF.cauchyW α β lam mu c c)
        unfold Z3NetF.cauchyPi at hcd; linarith
      have hde' : d ≠ e := by
        rintro rfl
        have := mul_self_nonneg (Z3NetF.cauchyW α β lam mu d d)
        unfold Z3NetF.cauchyPi at hde; linarith
      have hneg := CH_C_neg α β lam mu h c d e hcd' hde' hce
      right
      rw [Pi_symm]
      by_contra hpos
      push Not at hpos
      have : 0 ≤ Z3NetF.cauchyPi α β lam mu c d * Z3NetF.cauchyPi α β lam mu d e *
          Z3NetF.cauchyPi α β lam mu e c :=
        mul_nonneg (le_of_lt (mul_pos_of_neg_of_neg hcd hde)) hpos
      linarith
  · intro c d e
    by_cases hcd : c = d
    · exact Or.inl (Or.inl hcd)
    by_cases hde : d = e
    · exact Or.inr (Or.inl (Or.inl hde))
    by_cases hce : c = e
    · exact Or.inr (Or.inr (Or.inl hce))
    have hneg := CH_C_neg α β lam mu h c d e hcd hde hce
    by_contra hno
    push Not at hno
    obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩⟩ := hno
    rw [Pi_symm α β lam mu c e] at h3
    have : 0 ≤ Z3NetF.cauchyPi α β lam mu c d * Z3NetF.cauchyPi α β lam mu d e *
        Z3NetF.cauchyPi α β lam mu e c := mul_nonneg (mul_nonneg h1 h2) h3
    linarith

end ordered

/-! ## (H) over `ℝ` -/

lemma abs_sum_of_add {A B C : ℝ} (h : A - B + C = 0) :
    |A| = |B| + |C| ∨ |B| = |A| + |C| ∨ |C| = |A| + |B| := by
  have nA := abs_nonneg A; have nB := abs_nonneg B; have nC := abs_nonneg C
  rcases abs_choice A with eA | eA <;> rcases abs_choice B with eB | eB <;>
    rcases abs_choice C with eC | eC <;>
    first
    | (left; linarith)
    | (right; left; linarith)
    | (right; right; linarith)

theorem CH_H (α β lam mu : ι → ℝ) (h : Z3NetF.CauchyOK α β lam mu) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    0 < 1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i j * Z3NetF.cauchyPi α β lam mu k l| ∧
      0 < 1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i k * Z3NetF.cauchyPi α β lam mu j l| ∧
      0 < 1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i l * Z3NetF.cauchyPi α β lam mu j k| ∧
      (1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i j * Z3NetF.cauchyPi α β lam mu k l| =
          1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i k * Z3NetF.cauchyPi α β lam mu j l| +
            1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i l * Z3NetF.cauchyPi α β lam mu j k| ∨
        1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i k * Z3NetF.cauchyPi α β lam mu j l| =
          1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i j * Z3NetF.cauchyPi α β lam mu k l| +
            1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i l * Z3NetF.cauchyPi α β lam mu j k| ∨
        1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i l * Z3NetF.cauchyPi α β lam mu j k| =
          1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i j * Z3NetF.cauchyPi α β lam mu k l| +
            1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu i k * Z3NetF.cauchyPi α β lam mu j l|) := by
  have hD : ∀ x y, x ≠ y → Z3NetF.Dh α β x y ≠ 0 := fun x y hxy => (h.2.2 x y hxy).ne_zero
  have hn : ∀ x, lam x * mu x ≠ 0 := fun x => ((h.1 x).mul (h.2.1 x)).ne_zero
  have hNpos : 0 < |lam i * mu i * (lam j * mu j) * (lam k * mu k) * (lam l * mu l)| :=
    abs_pos.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (hn i) (hn j)) (hn k)) (hn l))
  have hPP : ∀ a b c d : ι, a ≠ b → c ≠ d →
      Z3NetF.cauchyPi α β lam mu a b * Z3NetF.cauchyPi α β lam mu c d =
        lam a * mu a * (lam b * mu b) * (lam c * mu c) * (lam d * mu d) /
          (Z3NetF.Dh α β a b * Z3NetF.Dh α β c d) ^ 2 := by
    intro a b c d hab hcd
    rw [Pi_eq, Pi_eq, Ring.inverse_eq_inv']
    have := hD a b hab; have := hD c d hcd
    field_simp
  have key : ∀ a b c d : ι, a ≠ b → c ≠ d → ∀ N : ℝ,
      lam a * mu a * (lam b * mu b) * (lam c * mu c) * (lam d * mu d) = N →
      1 / Real.sqrt |Z3NetF.cauchyPi α β lam mu a b * Z3NetF.cauchyPi α β lam mu c d| =
        |Z3NetF.Dh α β a b * Z3NetF.Dh α β c d| / Real.sqrt |N| := by
    intro a b c d hab hcd N hN'
    rw [hPP a b c d hab hcd, hN', abs_div, abs_pow, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (abs_nonneg _)]
    have : 0 < |Z3NetF.Dh α β a b * Z3NetF.Dh α β c d| :=
      abs_pos.mpr (mul_ne_zero (hD a b hab) (hD c d hcd))
    rw [one_div_div]
  have e2 := key i k j l hik hjl (lam i * mu i * (lam j * mu j) * (lam k * mu k) * (lam l * mu l))
    (by ring)
  have e3 := key i l j k hil hjk (lam i * mu i * (lam j * mu j) * (lam k * mu k) * (lam l * mu l))
    (by ring)
  rw [key i j k l hij hkl _ rfl, e2, e3]
  have hs := Real.sqrt_pos.mpr hNpos
  have p1 : 0 < |Z3NetF.Dh α β i j * Z3NetF.Dh α β k l| :=
    abs_pos.mpr (mul_ne_zero (hD i j hij) (hD k l hkl))
  have p2 : 0 < |Z3NetF.Dh α β i k * Z3NetF.Dh α β j l| :=
    abs_pos.mpr (mul_ne_zero (hD i k hik) (hD j l hjl))
  have p3 : 0 < |Z3NetF.Dh α β i l * Z3NetF.Dh α β j k| :=
    abs_pos.mpr (mul_ne_zero (hD i l hil) (hD j k hjk))
  refine ⟨div_pos p1 hs, div_pos p2 hs, div_pos p3 hs, ?_⟩
  rcases abs_sum_of_add (plucker α β i j k l) with h1 | h1 | h1
  · left; rw [h1, add_div]
  · right; left; rw [h1, add_div]
  · right; right; rw [h1, add_div]

/-! ## The frame layer in homogeneous coordinates -/

theorem wN_cauchy {s : ℕ} (inf : Fin s) (x : Fin s → R) (hx : Z3NetF.PlacesOK inf x)
    (lam mu : Fin s → R) (hl : ∀ c, IsUnit (lam c)) (hm : ∀ d, IsUnit (mu d)) :
    Z3NetF.CauchyOK (fun c => if c = inf then 1 else x c) (fun c => if c = inf then 0 else 1) lam
        (fun d => if d = inf then -mu d else mu d) ∧
      ∀ c d, c ≠ d → lam c * mu d * Z3NetF.wN inf x c d =
        Z3NetF.cauchyW (fun c => if c = inf then 1 else x c) (fun c => if c = inf then 0 else 1)
          lam (fun d => if d = inf then -mu d else mu d) c d := by
  have hD : ∀ c d, c ≠ d → Z3NetF.Dh (fun c => if c = inf then 1 else x c)
      (fun c => if c = inf then 0 else 1) c d =
        if c = inf then 1 else if d = inf then -1 else x c - x d := by
    intro c d hcd
    unfold Z3NetF.Dh
    by_cases hc : c = inf
    · subst hc; simp [Ne.symm hcd]
    · by_cases hd : d = inf
      · subst hd; simp [hc]
      · simp [hc, hd]
  refine ⟨⟨hl, fun d => ?_, fun c d hcd => ?_⟩, fun c d hcd => ?_⟩
  · show IsUnit (if d = inf then -mu d else mu d)
    split_ifs
    · exact (hm d).neg
    · exact hm d
  · rw [hD c d hcd]
    split_ifs with hc hd
    · exact isUnit_one
    · exact isUnit_one.neg
    · exact hx c d hc hd hcd
  · unfold Z3NetF.cauchyW Z3NetF.wN
    rw [hD c d hcd]
    by_cases hc : c = inf
    · subst hc; simp [Ne.symm hcd, Ring.inverse_one _]
    · by_cases hd : d = inf
      · subst hd
        simp only [hc, ite_false, ite_true, or_true]
        rw [inverse_neg, Ring.inverse_one _]; ring
      · simp [hc, hd]

/-! ## `rem:pm1` -/

lemma pm_mul {x y : R} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) : x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

lemma pm_inv {x : R} (hx : x = 1 ∨ x = -1) : Ring.inverse x = 1 ∨ Ring.inverse x = -1 := by
  rcases hx with rfl | rfl
  · left; exact Ring.inverse_one _
  · right; rw [inverse_neg, Ring.inverse_one _]

theorem pm1_ring [Nontrivial R] (h3 : (3 : R) ≠ 0) (α β lam mu : Fin 4 → R)
    (h : Z3NetF.CauchyOK α β lam mu) :
    ¬ ∀ c d : Fin 4, c ≠ d →
      Z3NetF.cauchyW α β lam mu c d = 1 ∨ Z3NetF.cauchyW α β lam mu c d = -1 := by
  intro hall
  have hX := CH_X α β lam mu h 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have w : ∀ c d : Fin 4, c ≠ d → _ := hall
  have t1 := pm_mul (pm_mul (w 1 0 (by decide)) (w 2 3 (by decide)))
    (pm_inv (pm_mul (w 1 3 (by decide)) (w 2 0 (by decide))))
  have t2 := pm_mul (pm_mul (w 0 1 (by decide)) (w 2 3 (by decide)))
    (pm_inv (pm_mul (w 0 3 (by decide)) (w 2 1 (by decide))))
  rcases t1 with e1 | e1 <;> rcases t2 with e2 | e2 <;> rw [e1, e2] at hX
  · -- `1 + 1 = 1`
    exact one_ne_zero (by linear_combination hX)
  · exact one_ne_zero (by linear_combination -hX)
  · exact one_ne_zero (by linear_combination -hX)
  · exact h3 (by linear_combination -hX)

theorem pm1 {q : ℕ} (hq : 5 ≤ q) (hodd : Odd q) (α β lam mu : Fin 4 → ZMod q)
    (h : Z3NetF.CauchyOK α β lam mu) :
    ¬ ∀ c d : Fin 4, c ≠ d →
      Z3NetF.cauchyW α β lam mu c d = 1 ∨ Z3NetF.cauchyW α β lam mu c d = -1 := by
  have : Fact (1 < q) := ⟨by omega⟩
  refine pm1_ring ?_ α β lam mu h
  intro h3
  have : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h3
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-! ## `prop:P` -/

section half

variable {K : Type*} [Field K]

/-- `Z = (A₁A₃ - A₁A₂ - A₂A₃)² - 4A₁A₂²A₃` of `prop:P`. -/
def Zof (A₁ A₂ A₃ : ℤ) : ℤ := (A₁ * A₃ - A₁ * A₂ - A₂ * A₃) ^ 2 - 4 * A₁ * A₂ ^ 2 * A₃

lemma Zof_odd {A₁ A₂ A₃ : ℤ} (h1 : Odd A₁) (h2 : Odd A₂) (h3 : Odd A₃) :
    Odd (Zof A₁ A₂ A₃) := by
  unfold Zof
  have hb : Odd (A₁ * A₃ - A₁ * A₂ - A₂ * A₃) :=
    ((h1.mul h3).sub_odd (h1.mul h2)).sub_odd (h2.mul h3)
  exact (hb.pow).sub_even ⟨2 * (A₁ * A₂ ^ 2 * A₃), by ring⟩

lemma abs_prod4 {a b c d : ℤ} {H : ℕ} (ha : |a| ≤ H) (hb : |b| ≤ H) (hc : |c| ≤ H)
    (hd : |d| ≤ H) : |a * b * c * d| ≤ (H : ℤ) ^ 4 := by
  rw [abs_mul, abs_mul, abs_mul]
  have := abs_nonneg a; have := abs_nonneg b; have := abs_nonneg c; have := abs_nonneg d
  calc |a| * |b| * |c| * |d| ≤ (H : ℤ) * H * H * H := by gcongr
    _ = (H : ℤ) ^ 4 := by ring

lemma Zof_bound {A₁ A₂ A₃ M : ℤ} (h1 : |A₁| ≤ M) (h2 : |A₂| ≤ M) (h3 : |A₃| ≤ M) :
    |Zof A₁ A₂ A₃| ≤ 13 * M ^ 4 := by
  unfold Zof
  have n1 := abs_nonneg A₁; have n2 := abs_nonneg A₂; have n3 := abs_nonneg A₃
  have hM : 0 ≤ M := le_trans n1 h1
  have hb : |A₁ * A₃ - A₁ * A₂ - A₂ * A₃| ≤ 3 * M ^ 2 := by
    calc |A₁ * A₃ - A₁ * A₂ - A₂ * A₃| ≤ |A₁ * A₃| + |A₁ * A₂| + |A₂ * A₃| := by
          have := abs_sub (A₁ * A₃ - A₁ * A₂) (A₂ * A₃)
          have := abs_sub (A₁ * A₃) (A₁ * A₂)
          linarith
      _ = |A₁| * |A₃| + |A₁| * |A₂| + |A₂| * |A₃| := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ M * M + M * M + M * M := by
          have := mul_le_mul h1 h3 n3 hM; have := mul_le_mul h1 h2 n2 hM
          have := mul_le_mul h2 h3 n3 hM; linarith
      _ = 3 * M ^ 2 := by ring
  have hsq : |(A₁ * A₃ - A₁ * A₂ - A₂ * A₃) ^ 2| ≤ 9 * M ^ 4 := by
    rw [abs_pow]
    calc |A₁ * A₃ - A₁ * A₂ - A₂ * A₃| ^ 2 ≤ (3 * M ^ 2) ^ 2 := by
          gcongr
      _ = 9 * M ^ 4 := by ring
  have h4 : |4 * A₁ * A₂ ^ 2 * A₃| ≤ 4 * M ^ 4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow]
    calc |(4 : ℤ)| * |A₁| * |A₂| ^ 2 * |A₃| ≤ 4 * M * M ^ 2 * M := by
          rw [show |(4 : ℤ)| = 4 by norm_num]
          have e1 := mul_le_mul h1 (pow_le_pow_left₀ n2 h2 2) (by positivity) hM
          have e2 := mul_le_mul e1 h3 n3 (by positivity)
          nlinarith
      _ = 4 * M ^ 4 := by ring
  calc _ ≤ |(A₁ * A₃ - A₁ * A₂ - A₂ * A₃) ^ 2| + |4 * A₁ * A₂ ^ 2 * A₃| := abs_sub _ _
    _ ≤ 9 * M ^ 4 + 4 * M ^ 4 := add_le_add hsq h4
    _ = 13 * M ^ 4 := by ring

/-- The common computation of `prop:P`: if `2 W_xy = h_xy` on four distinct coordinates of a
Cauchy layer over a field with `2 ≠ 0`, then `Z` vanishes in the field. -/
lemma half_core (h2 : (2 : K) ≠ 0) (α β lam mu : ι → K) (h : Z3NetF.CauchyOK α β lam mu)
    (a b c d : ι) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hh : ι → ι → ℤ)
    (hw : ∀ x y, (x = a ∨ x = b ∨ x = c ∨ x = d) → (y = a ∨ y = b ∨ y = c ∨ y = d) → x ≠ y →
      2 * Z3NetF.cauchyW α β lam mu x y = (hh x y : K)) :
    ((Zof (hh a b * hh b a * hh c d * hh d c) (hh a c * hh c a * hh b d * hh d b)
      (hh a d * hh d a * hh b c * hh c b) : ℤ) : K) = 0 := by
  obtain ⟨-, hχ, hψ, hE⟩ := CH_P α β lam mu h a b c d hab hac had hbc hbd hcd
  simp only [Ring.inverse_eq_inv'] at hχ hψ
  have S : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d → x = a ∨ x = b ∨ x = c ∨ x = d := fun _ h => h
  have hpi : ∀ x y, (x = a ∨ x = b ∨ x = c ∨ x = d) → (y = a ∨ y = b ∨ y = c ∨ y = d) → x ≠ y →
      4 * Z3NetF.cauchyPi α β lam mu x y = (hh x y : K) * (hh y x : K) := by
    intro x y hx hy hxy
    unfold Z3NetF.cauchyPi
    rw [← hw x y hx hy hxy, ← hw y x hy hx hxy.symm]; ring
  have hne : ∀ x y, x ≠ y → Z3NetF.cauchyPi α β lam mu x y ≠ 0 :=
    fun x y hxy => (Pi_unit α β lam mu h x y hxy).ne_zero
  have pab := hpi a b (Or.inl rfl) (Or.inr (Or.inl rfl)) hab
  have pcd := hpi c d (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl))) hcd
  have pac := hpi a c (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) hac
  have pbd := hpi b d (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl))) hbd
  have pad := hpi a d (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) had
  have pbc := hpi b c (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) hbc
  have nab := hne a b hab; have ncd := hne c d hcd; have nac := hne a c hac
  have nbd := hne b d hbd; have nad := hne a d had; have nbc := hne b c hbc
  set X := Z3NetF.chiCH α β a b c d
  set Y := Z3NetF.psiCH α β a b c d
  set Pab := Z3NetF.cauchyPi α β lam mu a b
  set Pcd := Z3NetF.cauchyPi α β lam mu c d
  set Pac := Z3NetF.cauchyPi α β lam mu a c
  set Pbd := Z3NetF.cauchyPi α β lam mu b d
  set Pad := Z3NetF.cauchyPi α β lam mu a d
  set Pbc := Z3NetF.cauchyPi α β lam mu b c
  have hX : X ^ 2 * (Pac * Pbd) = Pab * Pcd := by rw [hχ]; field_simp
  have hY : Y ^ 2 * (Pad * Pbc) = Pab * Pcd := by rw [hψ]; field_simp
  unfold Zof
  push_cast
  rw [show (hh a b : K) * hh b a * hh c d * hh d c = 16 * (Pab * Pcd) by
      rw [show (16 : K) = 4 * 4 by norm_num]; linear_combination (-(4 * Pcd)) * pab - (hh a b : K) *
        hh b a * pcd,
    show (hh a c : K) * hh c a * hh b d * hh d b = 16 * (Pac * Pbd) by
      rw [show (16 : K) = 4 * 4 by norm_num]; linear_combination (-(4 * Pbd)) * pac - (hh a c : K) *
        hh c a * pbd,
    show (hh a d : K) * hh d a * hh b c * hh c b = 16 * (Pad * Pbc) by
      rw [show (16 : K) = 4 * 4 by norm_num]; linear_combination (-(4 * Pbc)) * pad - (hh a d : K) *
        hh d a * pbc]
  -- `(X² - Y² - 1)² = 4 Y²` with `X² = P/A`, `Y² = P/B`
  set P := Pab * Pcd
  set A := Pac * Pbd
  set B := Pad * Pbc
  have hA : A ≠ 0 := mul_ne_zero nac nbd
  have hB : B ≠ 0 := mul_ne_zero nad nbc
  have hX' : X ^ 2 = P / A := by rw [eq_div_iff hA]; exact hX
  have hY' : Y ^ 2 = P / B := by rw [eq_div_iff hB]; exact hY
  rw [hX', hY'] at hE
  field_simp at hE
  linear_combination (16 : K) ^ 4 * hE

theorem P_half_mod (p : ℕ) [Fact p.Prime] (α β lam mu : ι → ZMod p)
    (h : Z3NetF.CauchyOK α β lam mu) (a b c d : ι) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hh : ι → ι → ℤ) (H : ℕ)
    (hodd : ∀ x y, (x = a ∨ x = b ∨ x = c ∨ x = d) → (y = a ∨ y = b ∨ y = c ∨ y = d) → x ≠ y →
      Odd (hh x y) ∧ |hh x y| ≤ H ∧ 2 * Z3NetF.cauchyW α β lam mu x y = (hh x y : ZMod p)) :
    ∃ Z : ℤ, Odd Z ∧ |Z| ≤ 13 * (H : ℤ) ^ 16 ∧ (p : ℤ) ∣ Z := by
  have Sa : a = a ∨ a = b ∨ a = c ∨ a = d := Or.inl rfl
  have Sb : b = a ∨ b = b ∨ b = c ∨ b = d := Or.inr (Or.inl rfl)
  have Sc : c = a ∨ c = b ∨ c = c ∨ c = d := Or.inr (Or.inr (Or.inl rfl))
  have Sd : d = a ∨ d = b ∨ d = c ∨ d = d := Or.inr (Or.inr (Or.inr rfl))
  by_cases hp2 : p = 2
  · exfalso
    subst hp2
    obtain ⟨ho, -, hw⟩ := hodd a b Sa Sb hab
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul] at hw
    obtain ⟨t, ht⟩ := ho
    rw [ht] at hw
    push_cast at hw
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add] at hw
    exact one_ne_zero hw.symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have hp := (Fact.out : p.Prime)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hcore := half_core h2 α β lam mu h a b c d hab hac had hbc hbd hcd hh
    (fun x y hx hy hxy => (hodd x y hx hy hxy).2.2)
  refine ⟨_, ?_, ?_, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hcore⟩
  · have o := fun x y hx hy hxy => (hodd x y hx hy hxy).1
    exact Zof_odd ((((o a b Sa Sb hab).mul (o b a Sb Sa hab.symm)).mul (o c d Sc Sd hcd)).mul
      (o d c Sd Sc hcd.symm)) ((((o a c Sa Sc hac).mul (o c a Sc Sa hac.symm)).mul
      (o b d Sb Sd hbd)).mul (o d b Sd Sb hbd.symm)) ((((o a d Sa Sd had).mul
      (o d a Sd Sa had.symm)).mul (o b c Sb Sc hbc)).mul (o c b Sc Sb hbc.symm))
  · have B := fun x y hx hy hxy => (hodd x y hx hy hxy).2.1
    have := Zof_bound (abs_prod4 (B a b Sa Sb hab) (B b a Sb Sa hab.symm) (B c d Sc Sd hcd)
      (B d c Sd Sc hcd.symm)) (abs_prod4 (B a c Sa Sc hac) (B c a Sc Sa hac.symm)
      (B b d Sb Sd hbd) (B d b Sd Sb hbd.symm)) (abs_prod4 (B a d Sa Sd had)
      (B d a Sd Sa had.symm) (B b c Sb Sc hbc) (B c b Sc Sb hbc.symm))
    calc _ ≤ 13 * ((H : ℤ) ^ 4) ^ 4 := this
      _ = 13 * (H : ℤ) ^ 16 := by ring

theorem P_half_mod_large (p : ℕ) [Fact p.Prime] (α β lam mu : ι → ZMod p)
    (h : Z3NetF.CauchyOK α β lam mu) (a b c d : ι) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (H : ℕ) (hp : 13 * H ^ 16 < p) :
    ¬ ∃ hh : ι → ι → ℤ, ∀ x y, (x = a ∨ x = b ∨ x = c ∨ x = d) →
      (y = a ∨ y = b ∨ y = c ∨ y = d) → x ≠ y →
        Odd (hh x y) ∧ |hh x y| ≤ H ∧ 2 * Z3NetF.cauchyW α β lam mu x y = (hh x y : ZMod p) := by
  rintro ⟨hh, hodd⟩
  obtain ⟨Z, hZ, hZb, hpZ⟩ := P_half_mod p α β lam mu h a b c d hab hac had hbc hbd hcd hh H hodd
  have hZ0 : Z = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hpZ
    have : (13 * (H : ℤ) ^ 16) < p := by exact_mod_cast hp
    have h1 : (Z.natAbs : ℤ) < p := by rw [Int.natCast_natAbs]; linarith
    simp only [Int.natAbs_natCast]
    exact_mod_cast h1
  rw [hZ0] at hZ
  exact (Int.not_even_iff_odd.mpr hZ) ⟨0, by norm_num⟩

theorem P_half_rat (α β lam mu : ι → ℚ) (h : Z3NetF.CauchyOK α β lam mu) (a b c d : ι)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ ∀ x y, (x = a ∨ x = b ∨ x = c ∨ x = d) → (y = a ∨ y = b ∨ y = c ∨ y = d) → x ≠ y →
      ∃ n : ℤ, Z3NetF.cauchyW α β lam mu x y = n + 1 / 2 := by
  intro hall
  classical
  let S : ι → Prop := fun x => x = a ∨ x = b ∨ x = c ∨ x = d
  let hh : ι → ι → ℤ := fun x y =>
    if hxy : S x ∧ S y ∧ x ≠ y then 2 * (hall x y hxy.1 hxy.2.1 hxy.2.2).choose + 1 else 0
  have hw : ∀ x y, S x → S y → x ≠ y → 2 * Z3NetF.cauchyW α β lam mu x y = (hh x y : ℚ) ∧
      Odd (hh x y) := by
    intro x y hx hy hxy
    have e : hh x y = 2 * (hall x y hx hy hxy).choose + 1 := by
      simp only [hh]; rw [dif_pos ⟨hx, hy, hxy⟩]
    have hs := (hall x y hx hy hxy).choose_spec
    rw [e]
    generalize (hall x y hx hy hxy).choose = n at hs ⊢
    rw [hs]
    refine ⟨by push_cast; ring, ⟨_, rfl⟩⟩
  have hcore := half_core (by norm_num : (2 : ℚ) ≠ 0) α β lam mu h a b c d hab hac had hbc hbd
    hcd hh (fun x y hx hy hxy => (hw x y hx hy hxy).1)
  have hZ : Zof (hh a b * hh b a * hh c d * hh d c) (hh a c * hh c a * hh b d * hh d b)
      (hh a d * hh d a * hh b c * hh c b) = 0 := by exact_mod_cast hcore
  have Sa : S a := Or.inl rfl
  have Sb : S b := Or.inr (Or.inl rfl)
  have Sc : S c := Or.inr (Or.inr (Or.inl rfl))
  have Sd : S d := Or.inr (Or.inr (Or.inr rfl))
  have o := fun x y hx hy hxy => (hw x y hx hy hxy).2
  have hodd := Zof_odd ((((o a b Sa Sb hab).mul (o b a Sb Sa hab.symm)).mul (o c d Sc Sd hcd)).mul
      (o d c Sd Sc hcd.symm)) ((((o a c Sa Sc hac).mul (o c a Sc Sa hac.symm)).mul
      (o b d Sb Sd hbd)).mul (o d b Sd Sb hbd.symm)) ((((o a d Sa Sd had).mul
      (o d a Sd Sa had.symm)).mul (o b c Sb Sc hbc)).mul (o c b Sc Sb hbc.symm))
  rw [hZ] at hodd
  exact (Int.not_even_iff_odd.mpr hodd) ⟨0, by norm_num⟩

end half

end ObsCH

alias CH_C := ObsCH.CH_C
alias CH_C_neg := ObsCH.CH_C_neg
alias CH_C_classes := ObsCH.CH_C_classes
alias CH_P := ObsCH.CH_P
alias CH_H := ObsCH.CH_H
alias CH_X := ObsCH.CH_X
alias wN_cauchy := ObsCH.wN_cauchy
alias pm1_ring := ObsCH.pm1_ring
alias pm1 := ObsCH.pm1
alias P_half_mod := ObsCH.P_half_mod
alias P_half_mod_large := ObsCH.P_half_mod_large
alias P_half_rat := ObsCH.P_half_rat

end

end Z3NetF.Proofs

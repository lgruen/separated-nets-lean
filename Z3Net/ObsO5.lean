/-
Proof module of entry Obs: `thm:O5` (`K_pair ≥ 2` for integer frame designs, `s ≥ 5`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsK
public import Z3Net.ObsCH
public import Z3Net.FTsk
public import Z3Net.FGs
public import Z3Net.FDsep

@[expose] public section

/-!
# Entry Obs: `thm:O5`

The level-`0` layer of an integer design reachable over `ℚ` is a rational Cauchy layer
`M_cd = λ_c μ_d / D_cd` (`wN_cauchy`). If `K_pair ≤ 1`, the pair rule gives
`π_cd = M_cd M_dc ∈ {-1} ∪ [1, ∞)`. With `ν_c = λ_c μ_c`, `D_cd² π_cd = -ν_c ν_d`, so `π_cd = -1`
exactly when `ν_c ν_d > 0`: the two classes of `lem:CH`(C) are the sign classes of `ν`. The
Plücker relation then excludes four coordinates in one class (three numbers of equal square
cannot satisfy `A - B + C = 0`, the form of `lem:CH`(H) used here) and the configuration of
three plus two coordinates (`D`-products give `1 - 1/U + 1/V = 0` with integers `U, V`, hence
`U = 2`, `V = -2`, and then four coordinates with three equal squares). For `s ≥ 5` one of
these occurs.
-/

namespace Z3NetF.Proofs

open Matrix Finset ObsCount ObsStep ObsCeil ObsP2 ObsL ObsK

noncomputable section

namespace ObsO5

lemma three_eq_sq {A B C : ℚ} (hA : A ≠ 0) (h1 : A ^ 2 = B ^ 2) (h2 : A ^ 2 = C ^ 2)
    (h : A - B + C = 0) : False := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with hB | hB <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with hC | hC <;>
    exact hA (by linarith)

lemma int_of_sq {u : ℚ} {n : ℤ} (h : u ^ 2 = n) : ∃ m : ℤ, u = m := by
  refine ⟨u.num, ?_⟩
  have hd : (u ^ 2).den = 1 := by rw [h]; rfl
  rw [Rat.den_pow] at hd
  have : u.den = 1 := by
    rcases Nat.eq_zero_or_pos u.den with h0 | h0
    · exact absurd h0 u.den_nz
    · nlinarith [pow_le_pow_left₀ (Nat.zero_le 1) (show 1 ≤ u.den from h0) 2]
  exact (Rat.coe_int_num_of_den_eq_one this).symm

lemma uv_sol {U V : ℤ} (hU : U ≠ 0) (hV : V ≠ 0)
    (h : (1 : ℚ) - 1 / (U : ℚ) + 1 / (V : ℚ) = 0) : U = 2 ∧ V = -2 := by
  have hU' : (U : ℚ) ≠ 0 := by exact_mod_cast hU
  have hV' : (V : ℚ) ≠ 0 := by exact_mod_cast hV
  have h2 : ((U - 1) * (V + 1) : ℚ) = -1 := by
    field_simp at h
    linear_combination h
  have h3 : (U - 1) * (V + 1) = -1 := by exact_mod_cast h2
  rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one h3 with h4 | h4
  · constructor <;> [omega; (rw [h4] at h3; omega)]
  · exfalso; apply hU; omega

section core

variable {s : ℕ} (M : Fin s → Fin s → ℤ) (α β lam mu : Fin s → ℚ)

/-- `D_cd² π_cd = -ν_c ν_d` with `π_cd = M_cd M_dc`, `ν_c = λ_c μ_c`. -/
lemma rel (hC : Z3NetF.CauchyOK α β lam mu)
    (hM : ∀ c d, c ≠ d → (M c d : ℚ) = Z3NetF.cauchyW α β lam mu c d) (c d : Fin s) (hcd : c ≠ d) :
    Z3NetF.Dh α β c d ^ 2 * ((M c d * M d c : ℤ) : ℚ) = -((lam c * mu c) * (lam d * mu d)) := by
  push_cast
  rw [hM c d hcd, hM d c hcd.symm]
  have hP := ObsCH.Pi_eq α β lam mu c d
  unfold Z3NetF.cauchyPi at hP
  rw [hP, Ring.inverse_eq_inv']
  have hD : Z3NetF.Dh α β c d ≠ 0 := (hC.2.2 c d hcd).ne_zero
  field_simp

/-- The pair rule (proof of `thm:O5`). -/
lemma pair_rule (hdiag : ∀ c, M c c ≠ 0) (hoff : ∀ c d, c ≠ d → M c d ≠ 0)
    (hfin : ¬ Z3NetF.PairInf M) (hK : Z3NetF.pairVal M ≤ 1) (a b : Fin s) (hab : a ≠ b) :
    M a b * M b a = -1 ∨ 1 ≤ M a b * M b a := by
  have hd : ∀ c, M c c = -1 := by
    intro c
    have h1 : ¬ 0 < M c c := fun h => hfin (Or.inl ⟨c, h⟩)
    have h2 := diag_le M c
    have := hdiag c
    omega
  have big : ∀ a b : Fin s, a ≠ b → 2 ≤ M a b → M b a = 1 := by
    intro a b hab hx
    have hσa : 0 < Z3NetF.sig M a b 1 a := by unfold Z3NetF.sig; rw [hd a]; omega
    have h1 : ¬ 0 < 1 * Z3NetF.sig M a b 1 b := fun h =>
      hfin (Or.inr ⟨a, b, hab, 1, by simp, hσa, h⟩)
    have hy := hoff b a (Ne.symm hab)
    by_cases hlt : 1 * Z3NetF.sig M a b 1 b < 0
    · have h2 := config_le M a b hab 1 (by simp) hσa hlt
      simp only [Z3NetF.sig, hd b] at h1 h2 hlt
      omega
    · simp only [Z3NetF.sig, hd b] at h1 hlt
      omega
  have bigneg : ∀ a b : Fin s, a ≠ b → M a b ≤ -2 → M b a = -1 := by
    intro a b hab hx
    have hσa : 0 < Z3NetF.sig M a b (-1) a := by unfold Z3NetF.sig; rw [hd a]; omega
    have h1 : ¬ 0 < (-1) * Z3NetF.sig M a b (-1) b := fun h =>
      hfin (Or.inr ⟨a, b, hab, -1, by simp, hσa, h⟩)
    have hy := hoff b a (Ne.symm hab)
    by_cases hlt : (-1) * Z3NetF.sig M a b (-1) b < 0
    · have h2 := config_le M a b hab (-1) (by simp) hσa hlt
      simp only [Z3NetF.sig, hd b] at h1 h2 hlt
      omega
    · simp only [Z3NetF.sig, hd b] at h1 hlt
      omega
  have hx := hoff a b hab
  have hy := hoff b a (Ne.symm hab)
  by_cases h1 : 2 ≤ M a b
  · rw [big a b hab h1]; omega
  by_cases h2 : M a b ≤ -2
  · rw [bigneg a b hab h2]; omega
  by_cases h3 : 2 ≤ M b a
  · rw [big b a (Ne.symm hab) h3]; omega
  by_cases h4 : M b a ≤ -2
  · rw [bigneg b a (Ne.symm hab) h4]; omega
  have ex : M a b = 1 ∨ M a b = -1 := by omega
  have ey : M b a = 1 ∨ M b a = -1 := by omega
  rcases ex with ex | ex <;> rcases ey with ey | ey <;> rw [ex, ey] <;> norm_num

variable (hC : Z3NetF.CauchyOK α β lam mu)
  (hM : ∀ c d, c ≠ d → (M c d : ℚ) = Z3NetF.cauchyW α β lam mu c d)
  (hrule : ∀ a b, a ≠ b → M a b * M b a = -1 ∨ 1 ≤ M a b * M b a)

include hC hM hrule

lemma same_sign (a b : Fin s) (hab : a ≠ b) (h : 0 < (lam a * mu a) * (lam b * mu b)) :
    Z3NetF.Dh α β a b ^ 2 = (lam a * mu a) * (lam b * mu b) := by
  have hr := rel M α β lam mu hC hM a b hab
  have hD : Z3NetF.Dh α β a b ≠ 0 := (hC.2.2 a b hab).ne_zero
  rcases hrule a b hab with hp | hp
  · rw [hp] at hr; push_cast at hr; linarith
  · exfalso
    have : (0 : ℚ) < Z3NetF.Dh α β a b ^ 2 * ((M a b * M b a : ℤ) : ℚ) := by
      have : (1 : ℚ) ≤ ((M a b * M b a : ℤ) : ℚ) := by exact_mod_cast hp
      positivity
    linarith

lemma opp_sign (a b : Fin s) (hab : a ≠ b) (h : (lam a * mu a) * (lam b * mu b) < 0) :
    1 ≤ M a b * M b a := by
  have hr := rel M α β lam mu hC hM a b hab
  have hD : Z3NetF.Dh α β a b ≠ 0 := (hC.2.2 a b hab).ne_zero
  rcases hrule a b hab with hp | hp
  · exfalso
    rw [hp] at hr; push_cast at hr
    have : 0 < Z3NetF.Dh α β a b ^ 2 := by positivity
    linarith
  · exact hp

omit hrule in
lemma four_contra (ε : ℚ) (hε : ε = 1 ∨ ε = -1) (i j k l : Fin s) (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hsq : ∀ x y, x ≠ y → (x = i ∨ x = j ∨ x = k ∨ x = l) → (y = i ∨ y = j ∨ y = k ∨ y = l) →
      Z3NetF.Dh α β x y ^ 2 = (lam x * mu x) * (lam y * mu y)) : False := by
  have hp := ObsCH.plucker α β i j k l
  have hD : ∀ x y, x ≠ y → Z3NetF.Dh α β x y ≠ 0 := fun x y hxy => (hC.2.2 x y hxy).ne_zero
  have e1 := hsq i j hij (Or.inl rfl) (Or.inr (Or.inl rfl))
  have e2 := hsq k l hkl (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
  have e3 := hsq i k hik (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
  have e4 := hsq j l hjl (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl)))
  have e5 := hsq i l hil (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))
  have e6 := hsq j k hjk (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))
  refine three_eq_sq (A := Z3NetF.Dh α β i j * Z3NetF.Dh α β k l)
    (B := Z3NetF.Dh α β i k * Z3NetF.Dh α β j l) (C := Z3NetF.Dh α β i l * Z3NetF.Dh α β j k)
    (mul_ne_zero (hD i j hij) (hD k l hkl)) ?_ ?_ hp
  · rw [mul_pow, mul_pow, e1, e2, e3, e4]; ring
  · rw [mul_pow, mul_pow, e1, e2, e5, e6]; ring

lemma quad (xi xj y1 y2 : Fin s) (h1 : xi ≠ xj) (h2 : y1 ≠ y2) (h3 : xi ≠ y1) (h4 : xi ≠ y2)
    (h5 : xj ≠ y1) (h6 : xj ≠ y2)
    (hxx : 0 < (lam xi * mu xi) * (lam xj * mu xj)) (hyy : 0 < (lam y1 * mu y1) * (lam y2 * mu y2))
    (c1 : (lam xi * mu xi) * (lam y1 * mu y1) < 0) (c2 : (lam xj * mu xj) * (lam y2 * mu y2) < 0)
    (c3 : (lam xi * mu xi) * (lam y2 * mu y2) < 0) (c4 : (lam xj * mu xj) * (lam y1 * mu y1) < 0) :
    (M xi y1 * M y1 xi) * (M xj y2 * M y2 xj) = 4 ∧
      (M xi y2 * M y2 xi) * (M xj y1 * M y1 xj) = 4 := by
  set D := Z3NetF.Dh α β
  have hD : ∀ x y, x ≠ y → D x y ≠ 0 := fun x y hxy => (hC.2.2 x y hxy).ne_zero
  have dxx := same_sign M α β lam mu hC hM hrule xi xj h1 hxx
  have dyy := same_sign M α β lam mu hC hM hrule y1 y2 h2 hyy
  have r1 := rel M α β lam mu hC hM xi y1 h3
  have r2 := rel M α β lam mu hC hM xj y2 h6
  have r3 := rel M α β lam mu hC hM xi y2 h4
  have r4 := rel M α β lam mu hC hM xj y1 h5
  have hp := ObsCH.plucker α β xi xj y1 y2
  set A := D xi xj * D y1 y2 with hA
  set B := D xi y1 * D xj y2 with hB
  set C := D xi y2 * D xj y1 with hCdef
  have hA0 : A ≠ 0 := mul_ne_zero (hD _ _ h1) (hD _ _ h2)
  have hB0 : B ≠ 0 := mul_ne_zero (hD _ _ h3) (hD _ _ h6)
  have hC0 : C ≠ 0 := mul_ne_zero (hD _ _ h4) (hD _ _ h5)
  have eB : B ^ 2 * (((M xi y1 * M y1 xi) * (M xj y2 * M y2 xj) : ℤ) : ℚ) = A ^ 2 := by
    have : B ^ 2 * (((M xi y1 * M y1 xi) * (M xj y2 * M y2 xj) : ℤ) : ℚ) =
        (D xi y1 ^ 2 * ((M xi y1 * M y1 xi : ℤ) : ℚ)) * (D xj y2 ^ 2 * ((M xj y2 * M y2 xj : ℤ) : ℚ)) := by
      rw [hB]; push_cast; ring
    rw [this, r1, r2, hA, mul_pow, dxx, dyy]; ring
  have eC : C ^ 2 * (((M xi y2 * M y2 xi) * (M xj y1 * M y1 xj) : ℤ) : ℚ) = A ^ 2 := by
    have : C ^ 2 * (((M xi y2 * M y2 xi) * (M xj y1 * M y1 xj) : ℤ) : ℚ) =
        (D xi y2 ^ 2 * ((M xi y2 * M y2 xi : ℤ) : ℚ)) * (D xj y1 ^ 2 * ((M xj y1 * M y1 xj : ℤ) : ℚ)) := by
      rw [hCdef]; push_cast; ring
    rw [this, r3, r4, hA, mul_pow, dxx, dyy]; ring
  have su : (A / B) ^ 2 = (((M xi y1 * M y1 xi) * (M xj y2 * M y2 xj) : ℤ) : ℚ) := by
    rw [div_pow, ← eB]; field_simp
  have sv : (A / C) ^ 2 = (((M xi y2 * M y2 xi) * (M xj y1 * M y1 xj) : ℤ) : ℚ) := by
    rw [div_pow, ← eC]; field_simp
  obtain ⟨U, hU⟩ := int_of_sq su
  obtain ⟨V, hV⟩ := int_of_sq sv
  have hU0 : U ≠ 0 := by
    intro h; rw [h] at hU; simp at hU; rcases hU with h' | h' <;> contradiction
  have hV0 : V ≠ 0 := by
    intro h; rw [h] at hV; simp at hV; rcases hV with h' | h' <;> contradiction
  have heq : (1 : ℚ) - 1 / (U : ℚ) + 1 / (V : ℚ) = 0 := by
    rw [← hU, ← hV]
    field_simp
    linear_combination hp
  obtain ⟨rfl, rfl⟩ := uv_sol hU0 hV0 heq
  constructor
  · have : (((M xi y1 * M y1 xi) * (M xj y2 * M y2 xj) : ℤ) : ℚ) = 4 := by
      rw [← su, hU]; norm_num
    exact_mod_cast this
  · have : (((M xi y2 * M y2 xi) * (M xj y1 * M y1 xj) : ℤ) : ℚ) = 4 := by
      rw [← sv, hV]; norm_num
    exact_mod_cast this

lemma five_contra (x1 x2 x3 y1 y2 : Fin s) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hy : y1 ≠ y2) (hxy : ∀ x, (x = x1 ∨ x = x2 ∨ x = x3) → x ≠ y1 ∧ x ≠ y2)
    (ε : ℚ) (hε : ε = 1 ∨ ε = -1)
    (hX : ∀ x, (x = x1 ∨ x = x2 ∨ x = x3) → 0 < ε * (lam x * mu x))
    (hY : ∀ y, (y = y1 ∨ y = y2) → ε * (lam y * mu y) < 0) : False := by
  set n : Fin s → ℚ := fun x => lam x * mu x with hn
  have hsame : ∀ x y, (x = x1 ∨ x = x2 ∨ x = x3) → (y = x1 ∨ y = x2 ∨ y = x3) →
      0 < n x * n y := by
    intro x y hx hy
    have a := hX x hx; have b := hX y hy
    have : n x * n y = (ε * n x) * (ε * n y) := by
      rcases hε with rfl | rfl <;> ring
    rw [this]; exact mul_pos a b
  have hsameY : 0 < n y1 * n y2 := by
    have a := hY y1 (Or.inl rfl); have b := hY y2 (Or.inr rfl)
    have : n y1 * n y2 = (ε * n y1) * (ε * n y2) := by
      rcases hε with rfl | rfl <;> ring
    rw [this]; exact mul_pos_of_neg_of_neg a b
  have hcross : ∀ x y, (x = x1 ∨ x = x2 ∨ x = x3) → (y = y1 ∨ y = y2) → n x * n y < 0 := by
    intro x y hx hy
    have a := hX x hx; have b := hY y hy
    have : n x * n y = (ε * n x) * (ε * n y) := by
      rcases hε with rfl | rfl <;> ring
    rw [this]; exact mul_neg_of_pos_of_neg a b
  have X1 : x1 = x1 ∨ x1 = x2 ∨ x1 = x3 := Or.inl rfl
  have X2 : x2 = x1 ∨ x2 = x2 ∨ x2 = x3 := Or.inr (Or.inl rfl)
  have X3 : x3 = x1 ∨ x3 = x2 ∨ x3 = x3 := Or.inr (Or.inr rfl)
  have Y1 : y1 = y1 ∨ y1 = y2 := Or.inl rfl
  have Y2 : y2 = y1 ∨ y2 = y2 := Or.inr rfl
  have q12 := quad M α β lam mu hC hM hrule x1 x2 y1 y2 h12 hy (hxy x1 X1).1 (hxy x1 X1).2
    (hxy x2 X2).1 (hxy x2 X2).2 (hsame _ _ X1 X2) hsameY (hcross _ _ X1 Y1) (hcross _ _ X2 Y2)
    (hcross _ _ X1 Y2) (hcross _ _ X2 Y1)
  have q13 := quad M α β lam mu hC hM hrule x1 x3 y1 y2 h13 hy (hxy x1 X1).1 (hxy x1 X1).2
    (hxy x3 X3).1 (hxy x3 X3).2 (hsame _ _ X1 X3) hsameY (hcross _ _ X1 Y1) (hcross _ _ X3 Y2)
    (hcross _ _ X1 Y2) (hcross _ _ X3 Y1)
  have q23 := quad M α β lam mu hC hM hrule x2 x3 y1 y2 h23 hy (hxy x2 X2).1 (hxy x2 X2).2
    (hxy x3 X3).1 (hxy x3 X3).2 (hsame _ _ X2 X3) hsameY (hcross _ _ X2 Y1) (hcross _ _ X3 Y2)
    (hcross _ _ X2 Y2) (hcross _ _ X3 Y1)
  -- the cross products are `≥ 1`
  have P : ∀ x y, (x = x1 ∨ x = x2 ∨ x = x3) → (y = y1 ∨ y = y2) → 1 ≤ M x y * M y x :=
    fun x y hx hy => opp_sign M α β lam mu hC hM hrule x y (by
      rcases hy with rfl | rfl
      · exact (hxy x hx).1
      · exact (hxy x hx).2) (hcross x y hx hy)
  have p11 := P x1 y1 X1 Y1; have p12 := P x1 y2 X1 Y2
  have p21 := P x2 y1 X2 Y1; have p22 := P x2 y2 X2 Y2
  have p31 := P x3 y1 X3 Y1; have p32 := P x3 y2 X3 Y2
  have e1 : M x1 y1 * M y1 x1 = M x3 y1 * M y1 x3 := by nlinarith [q12.1, q23.2]
  have e2 : M x2 y1 * M y1 x2 = M x3 y1 * M y1 x3 := by nlinarith [q12.2, q13.2]
  -- four coordinates `x1, x2, x3, y1` with three equal squares
  set D := Z3NetF.Dh α β
  have hD : ∀ x y, x ≠ y → D x y ≠ 0 := fun x y hxy => (hC.2.2 x y hxy).ne_zero
  set α' : ℚ := ((M x3 y1 * M y1 x3 : ℤ) : ℚ) with hα'
  have hα0 : α' ≠ 0 := by
    have : (1 : ℚ) ≤ α' := by rw [hα']; exact_mod_cast p31
    linarith
  have d12 := same_sign M α β lam mu hC hM hrule x1 x2 h12 (hsame _ _ X1 X2)
  have d13 := same_sign M α β lam mu hC hM hrule x1 x3 h13 (hsame _ _ X1 X3)
  have d23 := same_sign M α β lam mu hC hM hrule x2 x3 h23 (hsame _ _ X2 X3)
  have r1 := rel M α β lam mu hC hM x1 y1 (hxy x1 X1).1
  have r2 := rel M α β lam mu hC hM x2 y1 (hxy x2 X2).1
  have r3 := rel M α β lam mu hC hM x3 y1 (hxy x3 X3).1
  rw [e1] at r1
  rw [e2] at r2
  have hp := ObsCH.plucker α β x1 x2 x3 y1
  have hA0 : D x1 x2 * D x3 y1 ≠ 0 := mul_ne_zero (hD _ _ h12) (hD _ _ (hxy x3 X3).1)
  refine three_eq_sq hA0 ?_ ?_ hp
  · apply mul_right_cancel₀ hα0
    have : (D x1 x2 * D x3 y1) ^ 2 * α' = D x1 x2 ^ 2 * (D x3 y1 ^ 2 * α') := by ring
    have h2 : (D x1 x3 * D x2 y1) ^ 2 * α' = D x1 x3 ^ 2 * (D x2 y1 ^ 2 * α') := by ring
    rw [this, h2, r3, r2, d12, d13]; ring
  · apply mul_right_cancel₀ hα0
    have : (D x1 x2 * D x3 y1) ^ 2 * α' = D x1 x2 ^ 2 * (D x3 y1 ^ 2 * α') := by ring
    have h2 : (D x1 y1 * D x2 x3) ^ 2 * α' = (D x1 y1 ^ 2 * α') * D x2 x3 ^ 2 := by ring
    rw [this, h2, r3, r1, d12, d23]; ring

end core

/-- **The core of `thm:O5`**: an integer matrix with nonzero diagonal whose off-diagonal part is a
rational Cauchy layer has `K_pair ≥ 2` when `s ≥ 5`. -/
theorem O5_core {s : ℕ} (hs : 5 ≤ s) (M : Fin s → Fin s → ℤ) (α β lam mu : Fin s → ℚ)
    (hC : Z3NetF.CauchyOK α β lam mu)
    (hM : ∀ c d, c ≠ d → (M c d : ℚ) = Z3NetF.cauchyW α β lam mu c d) (hdiag : ∀ c, M c c ≠ 0) :
    2 ≤ Z3NetF.Kpair M := by
  classical
  by_cases hP : Z3NetF.PairInf M
  · rw [Kpair_top M hP]; exact le_top
  rw [Kpair_fin M hP]
  by_contra hlt
  have hK : Z3NetF.pairVal M ≤ 1 := by
    by_contra h; push Not at h
    exact hlt (by exact_mod_cast h)
  have hoff : ∀ c d, c ≠ d → M c d ≠ 0 := by
    intro c d hcd h0
    have := hM c d hcd
    rw [h0] at this
    exact (ObsCH.W_unit α β lam mu hC c d hcd).ne_zero (by rw [← this]; simp)
  have hrule := pair_rule M hdiag hoff hP hK
  set n : Fin s → ℚ := fun x => lam x * mu x with hn
  have hn0 : ∀ x, n x ≠ 0 := fun x => ((hC.1 x).mul (hC.2.1 x)).ne_zero
  set Pc := univ.filter fun x : Fin s => 0 < n x
  set Qc := univ.filter fun x : Fin s => n x < 0
  have hcard : Pc.card + Qc.card = s := by
    have hdisj : Disjoint Pc Qc := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; linarith
    rw [← card_union_of_disjoint hdisj]
    have : Pc ∪ Qc = univ := by
      ext x; simp only [Pc, Qc, mem_union, mem_filter, mem_univ, true_and, iff_true]
      rcases lt_or_gt_of_ne (hn0 x) with h | h
      · exact Or.inr h
      · exact Or.inl h
    rw [this, card_univ, Fintype.card_fin]
  -- four in one class
  have four : ∀ (ε : ℚ), (ε = 1 ∨ ε = -1) → ∀ S : Finset (Fin s), (∀ x ∈ S, 0 < ε * n x) →
      4 ≤ S.card → False := by
    intro ε hε S hS h4
    obtain ⟨i, hi⟩ : S.Nonempty := card_pos.mp (by omega)
    have h3 : 2 < (S.erase i).card := by rw [card_erase_of_mem hi]; omega
    obtain ⟨j, k, l, hj, hk, hl, hjk, hjl, hkl⟩ := two_lt_card_iff.mp h3
    have hj' := mem_erase.mp hj; have hk' := mem_erase.mp hk; have hl' := mem_erase.mp hl
    refine four_contra M α β lam mu hC hM ε hε i j k l (Ne.symm hj'.1) (Ne.symm hk'.1)
      (Ne.symm hl'.1) hjk hjl hkl ?_
    intro x y hxy hx hy
    have hxS : x ∈ S := by rcases hx with rfl | rfl | rfl | rfl <;> simp_all
    have hyS : y ∈ S := by rcases hy with rfl | rfl | rfl | rfl <;> simp_all
    apply same_sign M α β lam mu hC hM hrule x y hxy
    have a := hS x hxS; have b := hS y hyS
    have : n x * n y = (ε * n x) * (ε * n y) := by rcases hε with rfl | rfl <;> ring
    change 0 < n x * n y
    rw [this]; exact mul_pos a b
  have hPpos : ∀ x ∈ Pc, 0 < (1 : ℚ) * n x := fun x hx => by
    simp only [Pc, mem_filter, mem_univ, true_and] at hx; linarith
  have hQpos : ∀ x ∈ Qc, 0 < (-1 : ℚ) * n x := fun x hx => by
    simp only [Qc, mem_filter, mem_univ, true_and] at hx; linarith
  by_cases hP4 : 4 ≤ Pc.card
  · exact four 1 (Or.inl rfl) Pc hPpos hP4
  by_cases hQ4 : 4 ≤ Qc.card
  · exact four (-1) (Or.inr rfl) Qc hQpos hQ4
  -- three plus two
  have five : ∀ (ε : ℚ), (ε = 1 ∨ ε = -1) → ∀ X Y : Finset (Fin s),
      (∀ x ∈ X, 0 < ε * n x) → (∀ y ∈ Y, ε * n y < 0) → 3 ≤ X.card → 2 ≤ Y.card → False := by
    intro ε hε X Y hX hY h3 h2
    obtain ⟨x1, x2, x3, h1, h2', h3', h12, h13, h23⟩ := (two_lt_card_iff (s := X)).mp (by omega)
    obtain ⟨y1, y2, hy1, hy2, hy⟩ := (one_lt_card_iff (s := Y)).mp (by omega)
    refine five_contra M α β lam mu hC hM hrule x1 x2 x3 y1 y2 h12 h13 h23 hy ?_ ε hε ?_ ?_
    · intro x hx
      have hxX : x ∈ X := by rcases hx with rfl | rfl | rfl <;> assumption
      have a := hX x hxX
      constructor
      · rintro rfl; have := hY x hy1; linarith
      · rintro rfl; have := hY x hy2; linarith
    · intro x hx
      exact hX x (by rcases hx with rfl | rfl | rfl <;> assumption)
    · intro y hy'
      exact hY y (by rcases hy' with rfl | rfl <;> assumption)
  have hQneg : ∀ x ∈ Qc, (1 : ℚ) * n x < 0 := fun x hx => by
    simp only [Qc, mem_filter, mem_univ, true_and] at hx; linarith
  have hPneg : ∀ x ∈ Pc, (-1 : ℚ) * n x < 0 := fun x hx => by
    simp only [Pc, mem_filter, mem_univ, true_and] at hx; linarith
  by_cases hP3 : 3 ≤ Pc.card
  · exact five 1 (Or.inl rfl) Pc Qc hPpos hQneg hP3 (by omega)
  · exact five (-1) (Or.inr rfl) Qc Pc hQpos hPneg (by omega) (by omega)

theorem O5_Kpair {s : ℕ} (hs : 5 ≤ s) (inf : Fin s) (x : Fin s → ℚ) (hx : Z3NetF.PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ) (Ur : Fin s → ℕ → ℕ → ℚ)
    (hres : Z3NetF.Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur) (hdiag : ∀ c, F 0 c c ≠ 0) :
    2 ≤ Z3NetF.Kpair (F 0) := by
  obtain ⟨hl, -, hUu, heq⟩ := hres
  have hm : ∀ d, IsUnit (Ur d 0 0) := fun d => hUu d 0 (by omega)
  obtain ⟨hCK, hW⟩ := ObsCH.wN_cauchy inf x hx lam (fun d => Ur d 0 0) hl hm
  refine O5_core hs (F 0) _ _ lam _ hCK (fun c d hcd => ?_) hdiag
  have := heq c d hcd 0 (by omega)
  simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one] at this
  rw [this, ← hW c d hcd]
  ring

/-! ## Reduction of the residual problem along ring maps -/

section map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma inv_map (u : R) (hu : IsUnit u) : f (Ring.inverse u) = Ring.inverse (f u) := by
  obtain ⟨v, rfl⟩ := hu
  rw [Ring.inverse_unit]
  have : f (v : R) = ((Units.map (f : R →* S) v : Sˣ) : S) := rfl
  rw [this, Ring.inverse_unit]
  simp

variable {s : ℕ} (inf : Fin s) (x : Fin s → R)

lemma wN_map (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) :
    f (Z3NetF.wN inf x c d) = Z3NetF.wN inf (fun c => f (x c)) c d := by
  unfold Z3NetF.wN
  split_ifs with h
  · simp
  · push Not at h
    by_cases hcd : c = d
    · subst hcd; simp [Ring.inverse_zero]
    · rw [inv_map f _ (hx c d h.1 h.2 hcd), map_sub]

lemma yN_map (hx : Z3NetF.PlacesOK inf x) (c d : Fin s) :
    f (Z3NetF.yN inf x c d) = Z3NetF.yN inf (fun c => f (x c)) c d := by
  unfold Z3NetF.yN
  split_ifs with h1 h2
  · simp
  · rfl
  · by_cases hcd : c = d
    · subst hcd; simp [Ring.inverse_zero]
    · rw [inv_map f _ (hx c d h1 h2 hcd), map_sub]

lemma PlacesOK_map (hx : Z3NetF.PlacesOK inf x) : Z3NetF.PlacesOK inf (fun c => f (x c)) := by
  intro c d hc hd hcd
  rw [← map_sub]
  exact (hx c d hc hd hcd).map f

lemma Residual_map (hx : Z3NetF.PlacesOK inf x) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x F lam Ur) :
    Z3NetF.Residual inf (fun c => f (x c)) (fun n c d => f (F n c d)) (fun c => f (lam c))
      (fun d n' n => f (Ur d n' n)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hres
  refine ⟨fun c => (h1 c).map f, fun d n' n h h' => by simp [h2 d n' n h h'],
    fun d n h => (h3 d n h).map f, fun c d hcd n hn => ?_⟩
  show f (F n c d) = f (lam c) * ∑ n' ∈ Finset.range (n + 1), Z3NetF.wN inf (fun c => f (x c)) c d *
    Z3NetF.yN inf (fun c => f (x c)) c d ^ n' * f (Ur d n' n)
  rw [h4 c d hcd n hn, map_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [map_mul, map_mul, map_pow, wN_map f inf x hx, yN_map f inf x hx]

end map

theorem O5_sep {R : Type*} [CommRing R] {s q k C : ℕ} (hs : 5 ≤ s) (hk : 3 ≤ k)
    (h3k : 3 * k + 4 ≤ s * k) (ι : R →+* ℚ) (ψ : R →+* ZMod q) (inf : Fin s) (x : Fin s → R)
    (hx : Z3NetF.PlacesOK inf x) (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R)
    (hres : Z3NetF.Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : Z3NetF.BetaRel inf x (fun n c d => (F n c d : R)) lam β) (hdiag : ∀ c, F 0 c c ≠ 0)
    (hC : ∀ c d, |F 0 c d| ≤ C) (hq : 4 * s * C < q) :
    Z3NetF.PairBelow q (s * k) k
      (Z3NetF.digPoint q (s * k) fun c =>
        (Z3NetF.PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ)
      ((1 - 2 / (q : ℝ) + 6 * s * (C : ℝ) ^ 2 / (q : ℝ) ^ 2) ^ 2) := by
  classical
  haveI : NeZero q := ⟨Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) hq)⟩
  -- `K_pair(F_0) ≥ 2` over `ℚ`
  have hres' := Residual_map ι inf x hx _ lam Ur hres
  simp only [map_intCast] at hres'
  have hK2 := O5_Kpair hs inf (fun c => ι (x c)) (PlacesOK_map ι inf x hx) F _ _ hres' hdiag
  -- the net and its layer
  set Φ' : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q) := fun c d =>
    (Z3NetF.PPhi k inf x (fun n c d => (F n c d : R)) lam Ur β c d).map ψ with hΦ'
  have hgf : Z3NetF.gfPoint q k Φ' = Z3NetF.digPoint q (s * k) fun c =>
      (Z3NetF.PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ := by
    unfold Z3NetF.gfPoint Z3NetF.PGen
    congr 1
    funext c
    rw [graphGenK_map]
  have hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ') := by
    rw [hgf]; exact tsk_net_core k inf x ψ hx _ lam Ur β hres
  have hsk : 0 < s * k - k := by
    have : 2 * k ≤ s * k := Nat.mul_le_mul_right k (by omega)
    omega
  have hMt : ∀ c d, Z3NetF.Mt Φ' c d = F 0 c d := by
    intro c d
    have hent : Z3NetF.ent (Φ' c d) 0 (k - 1) = ((F 0 c d : ℤ) : ZMod q) := by
      unfold Z3NetF.ent
      rw [dif_pos ⟨hsk, by omega⟩]
      simp only [hΦ', Matrix.map_apply]
      by_cases hcd : c = d
      · subst hcd
        have hP : Z3NetF.PPhi k inf x (fun n c d => (F n c d : R)) lam Ur β c c =
            fun (r : Fin (s * k - k)) (l : Fin k) => if (r : ℕ) = 0 ∧ k - 1 - (l : ℕ) < s - 1 then
              ((F (k - 1 - (l : ℕ)) c c : ℤ) : R) else 0 := by
          unfold Z3NetF.PPhi; exact if_pos rfl
        rw [hP]
        simp only [true_and]
        rw [if_pos (by omega), show k - 1 - (k - 1) = 0 by omega, map_intCast]
      · have hP : Z3NetF.PPhi k inf x (fun n c d => (F n c d : R)) lam Ur β c d =
            Z3NetF.Lmat k inf x lam c * Z3NetF.frameGraph R k inf x c d *
              Z3NetF.Ugauge k inf x Ur β d := by
          unfold Z3NetF.PPhi; exact if_neg hcd
        rw [hP, Gs_row0_core k inf x _ lam Ur β hx hres hβ c d hcd ⟨0, hsk⟩ rfl
          ⟨k - 1, by omega⟩]
        simp only
        rw [if_pos (by omega), show k - 1 - (k - 1) = 0 by omega, map_intCast]
    unfold Z3NetF.Mt
    rw [hent, ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    have h1 := hC c d
    have h2 : (2 * C : ℤ) < q := by
      have : ((4 * s * C : ℕ) : ℤ) < q := by exact_mod_cast hq
      push_cast at this
      have : (0 : ℤ) ≤ C := by positivity
      nlinarith
    rw [abs_le] at h1
    constructor <;> omega
  have hMeq : Z3NetF.Mt Φ' = F 0 := by funext c d; exact hMt c d
  have hKmin : Z3NetF.Kpair (Z3NetF.Mt Φ') = ⊤ ∨
      ∃ K : ℕ, Z3NetF.Kpair (Z3NetF.Mt Φ') = K ∧ (2 : ℝ) ≤ K := by
    rw [hMeq]
    revert hK2
    induction Z3NetF.Kpair (F 0) using ENat.recTopCoe with
    | top => intro _; left; rfl
    | coe K =>
      intro hK2
      right
      refine ⟨K, rfl, ?_⟩
      have : 2 ≤ K := by exact_mod_cast hK2
      exact_mod_cast this
  have := ceiling_of_Kmin (by omega) hk h3k Φ' hnet (fun a => by rw [hMt]; exact hdiag a)
    (fun c d => by rw [hMt]; exact hC c d) hq 2 (by norm_num)
    (by exact_mod_cast (show 2 ≤ s by omega)) hKmin
  rwa [hgf] at this

end ObsO5

alias O5_Kpair := ObsO5.O5_Kpair
alias O5_sep := ObsO5.O5_sep

end

end Z3NetF.Proofs

/-
Proof module (stage 6, entry PP): `prop:pp2`, existence of a net carrying a design for every `k`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.KNDefs
public import Z3Net.KNNetProof

@[expose] public section

/-!
# `prop:pp2` (`m ≡ 2`)

For a design with (S2), (N2), (K) we write down a gauge `(L, U, μ)` from the constant window
`Can2` (the frame's windows for every `k` lie in its gauge orbit, `KNNetGauge.act_h2`) to the
design's windows: `μ` from the nine (N2) entries, `U_x = diag(1, -Y0|x_{k-1}/Y0|x_k, 1)`,
`U_y = diag(1, -X0|y_{k-1}/X0|y_k, 1)`, `L_z = [[1, 0], [Z1|x_k/Z0|x_k - λ, λ]]` with
`λ = Z1|x_{k-1}/(Z0|x_k U_x[1,1])`. The two remaining window equations are exactly `κ₁ = -1` and
`κ₂ = -1`. The target pivot blocks are invertible by the (N2) entries and brackets. Then
`KNNetProof.net_of_cert2` realizes the design for every `k ≥ 2`.
-/

namespace Z3NetKN.PP

open Matrix Z3NetKN.NetKN Z3NetKN.Gauge

variable {p : ℕ} [Fact p.Prime]

section Pp2

variable (R : Rows)

/-- Short names for the window entries. -/
abbrev X0 (d : Fin 3) (i : Fin 4) : ZMod p := eF p (R.jt 0) d i
abbrev Y0 (d : Fin 3) (i : Fin 4) : ZMod p := eF p (R.jt 1) d i
abbrev Z0 (d : Fin 3) (i : Fin 4) : ZMod p := eF p (R.sk 2) d i
abbrev Z1 (d : Fin 3) (i : Fin 4) : ZMod p := eF p (R.jt 2) d i

noncomputable def ux (R : Rows) : ZMod p := -(Y0 (p := p) R 0 1) / Y0 R 0 0
noncomputable def uy (R : Rows) : ZMod p := -(X0 (p := p) R 1 1) / X0 R 1 0
noncomputable def lz (R : Rows) : ZMod p := Z1 (p := p) R 0 1 / (Z0 R 0 0 * ux R)

/-- The certificate of a design satisfying (S2), (N2), (K). -/
noncomputable def cert2 (R : Rows) : Cert p where
  L := ![fun a b => if a = b then 1 else 0, fun a b => if a = b then 1 else 0,
    fun a b => if a = 0 then (if b = 0 then 1 else 0)
      else (if b = 0 then Z1 R 0 0 / Z0 R 0 0 - lz R else lz R)]
  U := ![fun a b => if a = b then (if a = 1 then ux R else 1) else 0,
    fun a b => if a = b then (if a = 1 then uy R else 1) else 0,
    fun a b => if a = b then 1 else 0]
  μ := ![![1, X0 R 1 0, X0 R 2 0], ![Y0 R 0 0, 1, -Y0 R 2 0], ![Z0 R 0 0, Z0 R 1 0, 1]]
  Ti := fun d => ((TpadF 2 p R d)⁻¹ : Matrix (Fin 4) (Fin 4) (ZMod p))

end Pp2

section Alg

variable {F : Type*} [Field F]

lemma alg_k1 (z1y1 z1y0 z0y1 z0y0 y0x1 y0x0 z0x1 z0x0 x0y0 x0y1 z1x1 z1x0 : F)
    (h1 : z0x1 = 0) (h2 : z0y1 = 0) (hD : z1x1 * y0x0 * x0y1 * z0y0 ≠ 0)
    (H : (z1y1 - z0y1 * z0y0⁻¹ * z1y0) * (y0x1 - z0x1 * z0x0⁻¹ * y0x0) * x0y0 * z0x0 *
      ((z1x1 - z0x1 * z0x0⁻¹ * z1x0) * y0x0 * (x0y1 - z0y1 * z0y0⁻¹ * x0y0) * z0y0)⁻¹ = -1) :
    z1y1 * y0x1 * x0y0 * z0x0 = -(z1x1 * y0x0 * x0y1 * z0y0) := by
  subst h1 h2
  simp only [zero_mul, sub_zero] at H
  rw [mul_inv_eq_iff_eq_mul₀ hD] at H
  rw [H]; ring

lemma alg_k2 (z1x0 z0x0 z1y0 z0y0 y0x1 z0x1 y0x0 z1x1 : F) (h1 : z0x1 = 0)
    (hb : z0x0 ≠ 0) (hd : z0y0 ≠ 0) (hD : z1x1 * y0x0 ≠ 0)
    (H : (z1x0 * z0x0⁻¹ - z1y0 * z0y0⁻¹) * (z0x0 * (y0x1 - z0x1 * z0x0⁻¹ * y0x0)) *
      ((z1x1 - z0x1 * z0x0⁻¹ * z1x0) * y0x0)⁻¹ = -1) :
    (z1x0 * z0y0 - z1y0 * z0x0) * y0x1 = -(z1x1 * y0x0 * z0y0) := by
  subst h1
  simp only [zero_mul, sub_zero] at H
  rw [mul_inv_eq_iff_eq_mul₀ hD] at H
  have : (z1x0 * z0y0 - z1y0 * z0x0) * y0x1 =
      (z1x0 * z0x0⁻¹ - z1y0 * z0y0⁻¹) * (z0x0 * y0x1) * z0y0 := by
    field_simp
  rw [this, H]; ring

lemma alg_w2 (a b : F) (ha : a ≠ 0) : -(a * (-b / a)) = b := by field_simp

lemma alg_w9 (a b : F) (ha : a ≠ 0) : a * (b / a) = b := by field_simp

lemma alg_w10 (a b u : F) (ha : a ≠ 0) (hu : u ≠ 0) : a * (b / (a * u) * u) = b := by field_simp

lemma alg_w13 (z1x0 z0x0 z1x1 y0x1 y0x0 z0y0 z1y0 : F) (h1 : z0x0 ≠ 0) (h2 : y0x1 ≠ 0)
    (h3 : y0x0 ≠ 0) (h4 : z0y0 ≠ 0)
    (hk2 : (z1x0 * z0y0 - z1y0 * z0x0) * y0x1 = -(z1x1 * y0x0 * z0y0)) :
    z0y0 * (z1x0 / z0x0 - z1x1 / (z0x0 * (-y0x1 / y0x0))) = z1y0 := by
  field_simp
  linear_combination hk2

lemma alg_w14 (z1x1 z0x0 y0x1 y0x0 x0y1 x0y0 z0y0 z1y1 : F) (h1 : z0x0 ≠ 0) (h2 : y0x1 ≠ 0)
    (h3 : y0x0 ≠ 0) (h4 : x0y0 ≠ 0)
    (hk1 : z1y1 * y0x1 * x0y0 * z0x0 = -(z1x1 * y0x0 * x0y1 * z0y0)) :
    -(z0y0 * (z1x1 / (z0x0 * (-y0x1 / y0x0)) * (-x0y1 / x0y0))) = z1y1 := by
  field_simp
  linear_combination (-1 : F) * hk1

lemma det4a (a0 a1 a2 b0 b1 b2 c0 c1 c2 : F) (h1 : b1 = 0) (h2 : b2 = 0)
    (hb : b0 ≠ 0) (hbr : a2 * c1 - a1 * c2 ≠ 0) :
    (!![a0, a1, a2, 0; b0, b1, b2, 0; c0, c1, c2, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by
  subst h1 h2
  have : (!![a0, a1, a2, 0; b0, 0, 0, 0; c0, c1, c2, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) F).det =
      b0 * (a2 * c1 - a1 * c2) := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    ring
  rw [this]; exact mul_ne_zero hb hbr

lemma det4b (a0 a1 b0 b1 : F) (hbr : a1 * b0 - a0 * b1 ≠ 0) :
    (!![a0, a1, 0, 0; b0, b1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by
  have : (!![a0, a1, 0, 0; b0, b1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) F).det =
      -(a1 * b0 - a0 * b1) := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    ring
  rw [this]; exact neg_ne_zero.mpr hbr

end Alg

section Pp2Tpad

variable (R : Rows)

lemma tpad0 : TpadF 2 p R 0 = !![Y0 R 0 0, Y0 R 0 1, Y0 R 0 2, 0; Z0 R 0 0, Z0 R 0 1, Z0 R 0 2, 0;
    Z1 R 0 0, Z1 R 0 1, Z1 R 0 2, 0; 0, 0, 0, 1] := by
  ext a i; fin_cases a <;> fin_cases i <;> simp [TpadF, PF, gF, rwF, rwList, Tgt, geoRow] <;> rfl

lemma tpad1 : TpadF 2 p R 1 = !![X0 R 1 0, X0 R 1 1, X0 R 1 2, 0; Z0 R 1 0, Z0 R 1 1, Z0 R 1 2, 0;
    Z1 R 1 0, Z1 R 1 1, Z1 R 1 2, 0; 0, 0, 0, 1] := by
  ext a i; fin_cases a <;> fin_cases i <;> simp [TpadF, PF, gF, rwF, rwList, Tgt, geoRow] <;> rfl

lemma tpad2 : TpadF 2 p R 2 = !![X0 R 2 0, X0 R 2 1, 0, 0; Y0 R 2 0, Y0 R 2 1, 0, 0;
    0, 0, 1, 0; 0, 0, 0, 1] := by
  ext a i; fin_cases a <;> fin_cases i <;> simp [TpadF, PF, gF, rwF, rwList, Tgt, geoRow] <;> rfl

end Pp2Tpad

section Pp2Proof

variable (R : Rows)

lemma cast_zero_of {z : ℤ} (h : z = 0) : ((z : ℤ) : ZMod p) = 0 := by rw [h]; simp

theorem cert2_ok (hS : CondS2 R) (hN : CondN2 p R) (hK1 : kap1 p R = -1) (hK2 : kap2 p R = -1) :
    CertOK 2 p R (cert2 R) := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hS
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, b1, b2, b3⟩ := hN
  have z01 : Z0 (p := p) R 0 1 = 0 := cast_zero_of s1
  have z02 : Z0 (p := p) R 0 2 = 0 := cast_zero_of s2
  have z11 : Z0 (p := p) R 1 1 = 0 := cast_zero_of s3
  have z12 : Z0 (p := p) R 1 2 = 0 := cast_zero_of s4
  -- the invariants as polynomial identities
  have hk1 : Z1 R 1 1 * Y0 R 0 1 * X0 R 1 0 * Z0 R 0 0 =
      -(Z1 (p := p) R 0 1 * Y0 R 0 0 * X0 R 1 1 * Z0 R 1 0) := by
    unfold kap1 tilde2 at hK1
    exact alg_k1 _ _ _ _ _ _ _ _ _ _ _ _ z01 z11
      (mul_ne_zero (mul_ne_zero (mul_ne_zero n5 n3) n7) n2) hK1
  have hk2 : (Z1 R 0 0 * Z0 R 1 0 - Z1 R 1 0 * Z0 R 0 0) * Y0 R 0 1 =
      -(Z1 (p := p) R 0 1 * Y0 R 0 0 * Z0 R 1 0) := by
    unfold kap2 tilde2 at hK2
    exact alg_k2 _ _ _ _ _ _ _ _ z01 n1 n2 (mul_ne_zero n5 n3) hK2
  have hux : ux (p := p) R ≠ 0 := by
    unfold ux; exact div_ne_zero (neg_ne_zero.mpr n4) n3
  have huy : uy (p := p) R ≠ 0 := by
    unfold uy; exact div_ne_zero (neg_ne_zero.mpr n7) n6
  have hlz : lz (p := p) R ≠ 0 := by
    unfold lz; exact div_ne_zero n5 (mul_ne_zero n1 hux)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c; fin_cases c <;> simp [cert2]
  · intro c a ha
    fin_cases c <;> fin_cases a <;> simp_all [cert2, gF]
  · intro d a b hab
    fin_cases d <;> simp [cert2] <;> intro h <;> subst h <;> exact absurd hab (lt_irrefl _)
  · intro d a ha
    fin_cases d <;> fin_cases a <;> simp_all [cert2, PF, gF]
  · intro c d hcd
    fin_cases c <;> fin_cases d <;> simp [cert2] at hcd ⊢ <;>
      first | exact n6 | exact n8 | exact n3 | exact neg_ne_zero.mpr n9 | exact n1 | exact n2
  · intro c d hcd ρ i hρ hi
    fin_cases c <;> fin_cases d <;> fin_cases ρ <;> fin_cases i <;>
      simp [gF, PF] at hcd hρ hi <;>
      simp [actE, act, Can, Can2, cert2, Cert.Lm, Cert.Um, Matrix.mul_apply, Fin.sum_univ_succ, Tgt,
        geoRow]
    · rfl
    · unfold uy; exact alg_w2 _ _ n6
    · rfl
    · rfl
    · unfold ux; exact alg_w2 _ _ n3
    · exact neg_neg _
    · rfl
    · exact z01.symm
    · exact alg_w9 _ _ n1
    · unfold lz; exact alg_w10 _ _ _ n1 hux
    · rfl
    · exact z11.symm
    · unfold lz ux; exact alg_w13 _ _ _ _ _ _ _ n1 n4 n3 n2 hk2
    · unfold lz ux uy; exact alg_w14 _ _ _ _ _ _ _ _ n1 n4 n3 n6 hk1
  · intro d a b
    have hT : IsUnit (TpadF 2 p R d).det := by
      rw [isUnit_iff_ne_zero]
      fin_cases d <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      · rw [tpad0]; exact det4a _ _ _ _ _ _ _ _ _ z01 z02 n1 b1
      · rw [tpad1]; exact det4a _ _ _ _ _ _ _ _ _ z11 z12 n2 b2
      · rw [tpad2]; exact det4b _ _ _ _ b3
    show (TpadF 2 p R d * (TpadF 2 p R d)⁻¹) a b = _
    rw [mul_nonsing_inv _ hT, one_apply]
  · intro c d hcd ρ hρ i hi1 hi2
    fin_cases c <;> fin_cases d <;> fin_cases ρ <;> fin_cases i <;>
      simp [gF, PF, win] at hcd hρ hi1 hi2 <;> simp [geoRow] <;> assumption

/-- **`prop:pp2`**. -/
theorem pp2_net (p k : ℕ) (hp : p.Prime) (R : Rows) (hS : CondS2 R) (hN : CondN2 p R)
    (hK1 : kap1 p R = -1) (hK2 : kap2 p R = -1) (hk : 2 ≤ k) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p),
      IsKN 2 p k R C ∧ IsNet0 p (3 * k + 2) (digPoint p (3 * k + 2) C) := by
  haveI := Fact.mk hp
  exact net_of_cert2 p k hk R (cert2 R) (cert2_ok R hS hN hK1 hK2)

end Pp2Proof

end Z3NetKN.PP

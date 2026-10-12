/-
Proof module (stage 6, entry PP): `prop:pp1`, existence of a net carrying a design for every `k`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.PP2

@[expose] public section

/-!
# `prop:pp1` (`m ≡ 1`)

As for `prop:pp2`: an explicit gauge from the constant window `Can1` to the design's windows
(`μ` from the (N1) entries, the column gauges from the (N1) entries and brackets, the row gauges of
the skeleton coordinates `y`, `z` from the `x`-window); the five remaining window equations are
equivalent to `J₁, …, J₅ = 1, -1, 2, 2, 1`. Then `KNNetProof.net_of_cert1` (`p ≥ 5`).
-/

namespace Z3NetKN.PP1

open Matrix Z3NetKN.NetKN Z3NetKN.Gauge

variable {p : ℕ} [Fact p.Prime]

section Alg

variable {F : Type*} [Field F]

lemma g_div (a b : F) (ha : a ≠ 0) : a * (b / a) = b := by field_simp

lemma g9 (a f b g u : F) (ha : a ≠ 0) (hu : u ≠ 0) :
    a * (f / a * (b / a) + (g / a - f / a * (b / a)) / u * u) = g := by field_simp; ring

lemma g10 (a l y : F) (ha : a ≠ 0) (hl : l ≠ 0) : -(a * (l * (-y / (a * l)))) = y := by
  field_simp

lemma g12 (yz0 xz0 xz1 yz1 : F) (h : yz0 ≠ 0) :
    -yz0 * (-(xz1 / xz0) + (xz1 / xz0 - yz1 / yz0)) = yz1 := by field_simp; ring

lemma g16 (c a b e : F) (hc : c ≠ 0) : c * (b / a + (e / c - b / a)) = e := by field_simp; ring

lemma g19 (c i l210 u001 u : F) (hc : c ≠ 0) (hu : u ≠ 0) :
    c * (l210 * u001 + (l210 + ((i / c - l210 * u001) / u - l210)) * u) = i := by field_simp; ring

/-- `l111 = R_Y|ζ₀ / Y0|ζ₀` from `J₁ = 1`. -/
lemma gl111 (a b c e f g yz0 w0 : F) (ha : a ≠ 0) (hc : c ≠ 0) (hyz : yz0 ≠ 0)
    (hdx : a * e - b * c ≠ 0)
    (H : (g - f * a⁻¹ * b) * c * yz0 * ((w0 - f * a⁻¹ * yz0) * (a * e - b * c))⁻¹ = 1) :
    (g / a - f / a * (b / a)) / (e / c - b / a) = (w0 - f * a⁻¹ * yz0) / yz0 := by
  have hw : w0 - f * a⁻¹ * yz0 ≠ 0 := by
    intro h; rw [h, zero_mul, _root_.inv_zero, mul_zero] at H; exact zero_ne_one H
  rw [mul_inv_eq_one₀ (mul_ne_zero hw hdx)] at H
  obtain ⟨D, hD⟩ : ∃ D, D = a * e - b * c := ⟨_, rfl⟩
  rw [← hD] at H hdx
  have e1 : e / c - b / a = D / (a * c) := by rw [hD]; field_simp
  have e2 : w0 - f * a⁻¹ * yz0 = (g - f * a⁻¹ * b) * c * yz0 / D := by
    rw [eq_div_iff hdx]; exact H.symm
  rw [e1, e2]
  field_simp

lemma gl211 (a b c e h i zy0 v0 : F) (ha : a ≠ 0) (hc : c ≠ 0) (hzy : zy0 ≠ 0)
    (hdx : a * e - b * c ≠ 0)
    (H : (i - h * c⁻¹ * e) * a * zy0 * ((v0 - h * c⁻¹ * zy0) * (a * e - b * c))⁻¹ = -1) :
    (i / c - h / c * (b / a)) / (e / c - b / a) - h / c = -((v0 - h * c⁻¹ * zy0) / zy0) := by
  have hw : v0 - h * c⁻¹ * zy0 ≠ 0 := by
    intro h'; rw [h', zero_mul, _root_.inv_zero, mul_zero] at H
    exact absurd H (by intro h''; have := congrArg (· + 1) h''; simp at this)
  rw [mul_inv_eq_iff_eq_mul₀ (mul_ne_zero hw hdx)] at H
  obtain ⟨D, hD⟩ : ∃ D, D = a * e - b * c := ⟨_, rfl⟩
  rw [← hD] at H hdx
  have e1 : e / c - b / a = D / (a * c) := by rw [hD]; field_simp
  have e2 : v0 - h * c⁻¹ * zy0 = -((i - h * c⁻¹ * e) * a * zy0) / D := by
    rw [eq_div_iff hdx, H]; ring
  rw [e1, e2]
  field_simp
  rw [hD]; ring

lemma g13 (a f yz0 w0 : F) (ha : a ≠ 0) (hyz : yz0 ≠ 0) :
    -yz0 * (-(f / a) + -((w0 - f * a⁻¹ * yz0) / yz0)) = w0 := by field_simp; ring

lemma g23 (c h zy0 v0 : F) (hc : c ≠ 0) (hzy : zy0 ≠ 0) :
    zy0 * (h / c + -(-((v0 - h * c⁻¹ * zy0) / zy0))) = v0 := by field_simp; ring

lemma g14 (a f yz0 yz1 xz0 xz1 w0 w1 : F) (ha : a ≠ 0) (hyz : yz0 ≠ 0) (hx : xz0 ≠ 0)
    (hR : w0 - f * a⁻¹ * yz0 ≠ 0) (hZ : yz1 - xz1 * xz0⁻¹ * yz0 ≠ 0)
    (H : (w1 - f * a⁻¹ * yz1 - xz1 * xz0⁻¹ * (w0 - f * a⁻¹ * yz0)) * yz0 *
      ((yz1 - xz1 * xz0⁻¹ * yz0) * (w0 - f * a⁻¹ * yz0))⁻¹ = 2) :
    -yz0 * ((-(f / a) + -((w0 - f * a⁻¹ * yz0) / yz0)) * (xz1 / xz0) +
      (f / a + (w0 - f * a⁻¹ * yz0) / yz0 * 2) * (xz1 / xz0 - yz1 / yz0)) = w1 := by
  rw [mul_inv_eq_iff_eq_mul₀ (mul_ne_zero hZ hR)] at H
  have e : w1 = f * a⁻¹ * yz1 + xz1 * xz0⁻¹ * (w0 - f * a⁻¹ * yz0) +
      2 * ((yz1 - xz1 * xz0⁻¹ * yz0) * (w0 - f * a⁻¹ * yz0)) / yz0 := by
    rw [← H]; field_simp; ring
  rw [e]; field_simp; ring

lemma g24 (c h zy0 zy1 xy0 xy1 v0 v1 : F) (hc : c ≠ 0) (hzy : zy0 ≠ 0) (hx : xy0 ≠ 0)
    (hR : v0 - h * c⁻¹ * zy0 ≠ 0) (hZ : zy1 - xy1 * xy0⁻¹ * zy0 ≠ 0)
    (H : (v1 - h * c⁻¹ * zy1 - xy1 * xy0⁻¹ * (v0 - h * c⁻¹ * zy0)) * zy0 *
      ((zy1 - xy1 * xy0⁻¹ * zy0) * (v0 - h * c⁻¹ * zy0))⁻¹ = 2) :
    zy0 * ((h / c + -(-((v0 - h * c⁻¹ * zy0) / zy0))) * (xy1 / xy0) +
      (h / c + -(-((v0 - h * c⁻¹ * zy0) / zy0) * 2)) * (zy1 / zy0 - xy1 / xy0)) = v1 := by
  rw [mul_inv_eq_iff_eq_mul₀ (mul_ne_zero hZ hR)] at H
  have e : v1 = h * c⁻¹ * zy1 + xy1 * xy0⁻¹ * (v0 - h * c⁻¹ * zy0) +
      2 * ((zy1 - xy1 * xy0⁻¹ * zy0) * (v0 - h * c⁻¹ * zy0)) / zy0 := by
    rw [← H]; field_simp; ring
  rw [e]; field_simp; ring

lemma g20 (a b c e f g h i y2 z2 yz0 zy0 w0 v0 y02 z02 : F) (ha : a ≠ 0) (hc : c ≠ 0)
    (hyz : yz0 ≠ 0) (hzy : zy0 ≠ 0) (hRy : w0 - f * a⁻¹ * yz0 ≠ 0) (hRz : v0 - h * c⁻¹ * zy0 ≠ 0)
    (hy2 : y2 ≠ 0) (h1 : y02 = 0) (h2 : z02 = 0)
    (H : (z2 - h * c⁻¹ * z02 + (a * z02 - y02 * c) * (b * c - a * e)⁻¹ * (i - h * c⁻¹ * e) +
        (y02 * e - b * z02) * (b * c - a * e)⁻¹ * (h - h * c⁻¹ * c)) * a * zy0 *
        (w0 - f * a⁻¹ * yz0) *
      ((y2 - f * a⁻¹ * y02 + (a * z02 - y02 * c) * (b * c - a * e)⁻¹ * (g - f * a⁻¹ * b) +
        (y02 * e - b * z02) * (b * c - a * e)⁻¹ * (f - f * a⁻¹ * a)) * c * yz0 *
        (v0 - h * c⁻¹ * zy0))⁻¹ = 1) :
    c * (-((v0 - h * c⁻¹ * zy0) / zy0) * (-y2 / (a * ((w0 - f * a⁻¹ * yz0) / yz0)))) = z2 := by
  subst h1 h2
  simp only [mul_zero, zero_mul, sub_zero, zero_sub, add_zero] at H
  rw [mul_inv_eq_one₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero hy2 hc) hyz) hRz)] at H
  generalize w0 - f * a⁻¹ * yz0 = Ry at *
  generalize v0 - h * c⁻¹ * zy0 = Rz at *
  field_simp
  linear_combination (-1 : F) * H

lemma gRy (a f yz0 w0 : F) (ha : a ≠ 0) (hb : f * yz0 - w0 * a ≠ 0) : w0 - f * a⁻¹ * yz0 ≠ 0 := by
  intro h; apply hb
  have : w0 = f * a⁻¹ * yz0 := by linear_combination h
  rw [this]; field_simp; ring

lemma gZ (x0 x1 y0 y1 : F) (hx : x0 ≠ 0) (hb : x1 * y0 - x0 * y1 ≠ 0) : y1 - x1 * x0⁻¹ * y0 ≠ 0 := by
  intro h; apply hb
  have : y1 = x1 * x0⁻¹ * y0 := by linear_combination h
  rw [this]; field_simp; ring

lemma gU (a b c e : F) (ha : a ≠ 0) (hc : c ≠ 0) (hdx : a * e - b * c ≠ 0) : e / c - b / a ≠ 0 := by
  intro h; apply hdx; field_simp at h; linear_combination h

lemma gU' (x0 x1 z0 z1 : F) (hx : x0 ≠ 0) (hz : z0 ≠ 0) (hb : x1 * z0 - x0 * z1 ≠ 0) :
    z1 / z0 - x1 / x0 ≠ 0 := by
  intro h; apply hb; field_simp at h; linear_combination -h

lemma gU'' (x0 x1 y0 y1 : F) (hx : x0 ≠ 0) (hy : y0 ≠ 0) (hb : x1 * y0 - x0 * y1 ≠ 0) :
    x1 / x0 - y1 / y0 ≠ 0 := by
  intro h; apply hb; field_simp at h; linear_combination h

lemma det4x (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 e0 e1 e2 e3 : F) (h2 : a2 = 0) (h3 : a3 = 0)
    (h4 : c2 = 0) (h5 : c3 = 0) (h1 : a0 * c1 - a1 * c0 ≠ 0) (h6 : b2 * e3 - b3 * e2 ≠ 0) :
    (!![a0, a1, a2, a3; b0, b1, b2, b3; c0, c1, c2, c3; e0, e1, e2, e3] :
      Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by
  subst h2 h3 h4 h5
  have : (!![a0, a1, 0, 0; b0, b1, b2, b3; c0, c1, 0, 0; e0, e1, e2, e3] :
      Matrix (Fin 4) (Fin 4) F).det = -((a0 * c1 - a1 * c0) * (b2 * e3 - b3 * e2)) := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    ring
  rw [this]; exact neg_ne_zero.mpr (mul_ne_zero h1 h6)

lemma det4y (a0 a1 a2 b0 b1 b2 c0 c1 c2 : F) (h2 : a2 = 0) (h3 : b2 = 0)
    (h1 : a0 * b1 - a1 * b0 ≠ 0) (hc : c2 ≠ 0) :
    (!![a0, a1, a2, 0; b0, b1, b2, 0; c0, c1, c2, 0; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by
  subst h2 h3
  have : (!![a0, a1, 0, 0; b0, b1, 0, 0; c0, c1, c2, 0; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) F).det = c2 * (a0 * b1 - a1 * b0) := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    ring
  rw [this]; exact mul_ne_zero hc h1

end Alg

section Defs

variable (R : Rows)

abbrev X0 (d : Fin 3) (i : Fin 4) : ZMod p := eF p (R.jt 0) d i
abbrev Y0 (d : Fin 3) (i : Fin 4) : ZMod p := eF p (R.sk 1) d i
abbrev Y1 (d : Fin 3) (i : Fin 4) : ZMod p := eF p (R.jt 1) d i
abbrev Z0 (d : Fin 3) (i : Fin 4) : ZMod p := eF p (R.sk 2) d i
abbrev Z1 (d : Fin 3) (i : Fin 4) : ZMod p := eF p (R.jt 2) d i

noncomputable def u001 : ZMod p := Y0 R 0 1 / Y0 R 0 0
noncomputable def u011 : ZMod p := Z0 R 0 1 / Z0 R 0 0 - Y0 R 0 1 / Y0 R 0 0
noncomputable def u101 : ZMod p := X0 R 1 1 / X0 R 1 0
noncomputable def u111 : ZMod p := Z0 R 1 1 / Z0 R 1 0 - X0 R 1 1 / X0 R 1 0
noncomputable def u201 : ZMod p := X0 R 2 1 / X0 R 2 0
noncomputable def u211 : ZMod p := X0 R 2 1 / X0 R 2 0 - Y0 R 2 1 / Y0 R 2 0
noncomputable def l110 : ZMod p := Y1 R 0 0 / Y0 R 0 0
noncomputable def l111 : ZMod p := (Y1 R 0 1 / Y0 R 0 0 - l110 R * u001 R) / u011 R
noncomputable def l210 : ZMod p := Z1 R 0 0 / Z0 R 0 0
noncomputable def l211 : ZMod p := (Z1 R 0 1 / Z0 R 0 0 - l210 R * u001 R) / u011 R - l210 R
noncomputable def u022 : ZMod p := -(Y1 R 0 2) / (Y0 R 0 0 * l111 R)

/-- The certificate of a design satisfying (S1), (N1), (J). -/
noncomputable def cert1 : Cert p where
  L := ![fun a b => if a = b then 1 else 0,
    fun a b => if a = 0 then (if b = 0 then 1 else 0) else (if b = 0 then l110 R else l111 R),
    fun a b => if a = 0 then (if b = 0 then 1 else 0) else (if b = 0 then l210 R else l211 R)]
  U := ![![![1, u001 R, 0], ![0, u011 R, 0], ![0, 0, u022 R]],
    ![![1, u101 R, 0], ![0, u111 R, 0], ![0, 0, 1]],
    ![![1, u201 R, 0], ![0, u211 R, 0], ![0, 0, 1]]]
  μ := ![![1, X0 R 1 0, X0 R 2 0], ![Y0 R 0 0, 1, -Y0 R 2 0], ![Z0 R 0 0, Z0 R 1 0, 1]]
  Ti := fun d => ((TpadF 1 p R d)⁻¹ : Matrix (Fin 4) (Fin 4) (ZMod p))

end Defs

section Tpad

variable (R : Rows)

lemma tpadx : TpadF 1 p R 0 = !![Y0 R 0 0, Y0 R 0 1, Y0 R 0 2, Y0 R 0 3;
    Y1 R 0 0, Y1 R 0 1, Y1 R 0 2, Y1 R 0 3; Z0 R 0 0, Z0 R 0 1, Z0 R 0 2, Z0 R 0 3;
    Z1 R 0 0, Z1 R 0 1, Z1 R 0 2, Z1 R 0 3] := by
  ext a i; fin_cases a <;> fin_cases i <;> simp [TpadF, PF, gF, rwF, rwList, Tgt, geoRow] <;> rfl

lemma tpady : TpadF 1 p R 1 = !![X0 R 1 0, X0 R 1 1, X0 R 1 2, 0; Z0 R 1 0, Z0 R 1 1, Z0 R 1 2, 0;
    Z1 R 1 0, Z1 R 1 1, Z1 R 1 2, 0; 0, 0, 0, 1] := by
  ext a i; fin_cases a <;> fin_cases i <;> simp [TpadF, PF, gF, rwF, rwList, Tgt, geoRow] <;> rfl

lemma tpadz : TpadF 1 p R 2 = !![X0 R 2 0, X0 R 2 1, X0 R 2 2, 0; Y0 R 2 0, Y0 R 2 1, Y0 R 2 2, 0;
    Y1 R 2 0, Y1 R 2 1, Y1 R 2 2, 0; 0, 0, 0, 1] := by
  ext a i; fin_cases a <;> fin_cases i <;> simp [TpadF, PF, gF, rwF, rwList, Tgt, geoRow] <;> rfl

end Tpad

section Proof

variable (R : Rows)

theorem cert1_ok (hS : CondS1 R) (hN : CondN1 p R) (hJ1 : J1 p R = 1) (hJ2 : J2 p R = -1)
    (hJ3 : J3 p R = 2) (hJ4 : J4 p R = 2) (hJ5 : J5 p R = 1) :
    CertOK 1 p R (cert1 R) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hS
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, b1, b2, b3, b4, b5, b6⟩ := hN
  have y02 : Y0 (p := p) R 0 2 = 0 := PP.cast_zero_of s1
  have z02 : Z0 (p := p) R 0 2 = 0 := PP.cast_zero_of s3
  have hdx : Y0 (p := p) R 0 0 * Z0 R 0 1 - Y0 R 0 1 * Z0 R 0 0 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp b1))
  have hRy : RYv p R 2 0 ≠ 0 := by unfold RYv; exact gRy _ _ _ _ n1 b5
  have hRz : RZv p R 1 0 ≠ 0 := by unfold RZv; exact gRy _ _ _ _ n2 b6
  have hZz : Y0 (p := p) R 2 1 - X0 R 2 1 * (X0 R 2 0)⁻¹ * Y0 R 2 0 ≠ 0 := gZ _ _ _ _ n5 b3
  have hZy : Z0 (p := p) R 1 1 - X0 R 1 1 * (X0 R 1 0)⁻¹ * Z0 R 1 0 ≠ 0 := gZ _ _ _ _ n3 b2
  have hu011 : u011 (p := p) R ≠ 0 := by unfold u011; exact gU _ _ _ _ n1 n2 hdx
  have hu111 : u111 (p := p) R ≠ 0 := by unfold u111; exact gU' _ _ _ _ n3 n4 b2
  have hu211 : u211 (p := p) R ≠ 0 := by unfold u211; exact gU'' _ _ _ _ n5 n6 b3
  unfold J1 RYv dxJ brk2 at hJ1
  unfold J2 RZv dxJ brk2 at hJ2
  unfold J3 tlz RYv at hJ3
  unfold J4 tly RZv at hJ4
  unfold J5 tlx xiA xiB RYv RZv at hJ5
  have hl111 : l111 R = RYv p R 2 0 / Y0 R 2 0 := by
    unfold l111 l110 u001 u011 RYv; exact gl111 _ _ _ _ _ _ _ _ n1 n2 n6 hdx hJ1
  have hl211 : l211 R = -(RZv p R 1 0 / Z0 R 1 0) := by
    unfold l211 l210 u001 u011 RZv; exact gl211 _ _ _ _ _ _ _ _ n1 n2 n4 hdx hJ2
  have hl111n : l111 (p := p) R ≠ 0 := by rw [hl111]; exact div_ne_zero hRy n6
  have hl211n : l211 (p := p) R ≠ 0 := by rw [hl211]; exact neg_ne_zero.mpr (div_ne_zero hRz n4)
  have hu022 : u022 (p := p) R ≠ 0 := by
    unfold u022; exact div_ne_zero (neg_ne_zero.mpr n7) (mul_ne_zero n1 hl111n)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c; fin_cases c <;> simp [cert1]
  · intro c a ha
    fin_cases c <;> fin_cases a <;> simp [cert1, gF] at ha ⊢ <;> assumption
  · intro d a b hab
    fin_cases d <;> fin_cases a <;> fin_cases b <;> simp [cert1] at hab ⊢
  · intro d a ha
    fin_cases d <;> fin_cases a <;> simp [cert1, PF, gF] at ha ⊢ <;> assumption
  · intro c d hcd
    fin_cases c <;> fin_cases d <;> simp [cert1] at hcd ⊢ <;>
      first | exact n3 | exact n5 | exact n1 | exact neg_ne_zero.mpr n6 | exact n2 | exact n4
  · intro c d hcd ρ i hρ hi
    fin_cases c <;> fin_cases d <;> fin_cases ρ <;> fin_cases i <;>
      simp [gF, PF] at hcd hρ hi <;>
      simp [actE, act, Can, Can1, cert1, Cert.Lm, Cert.Um, Matrix.mul_apply, Fin.sum_univ_succ, Tgt,
        geoRow]
    · rfl
    · unfold u101; exact PP1.g_div _ _ n3
    · rfl
    · unfold u201; exact PP1.g_div _ _ n5
    · rfl
    · unfold u001; exact PP1.g_div _ _ n1
    · exact y02.symm
    · unfold l110; exact PP1.g_div _ _ n1
    · unfold l111 l110 u001; exact g9 _ _ _ _ _ n1 hu011
    · unfold u022; exact g10 _ _ _ n1 hl111n
    · exact neg_neg _
    · unfold u201 u211; exact g12 _ _ _ _ n6
    · rw [hl111]; unfold l110 RYv; exact g13 _ _ _ _ n1 n6
    · rw [hl111]; unfold l110 u201 u211 RYv; exact g14 _ _ _ _ _ _ _ _ n1 n6 n5 hRy hZz hJ3
    · rfl
    · unfold u001 u011; exact g16 _ _ _ _ n2
    · exact z02.symm
    · unfold l210; exact PP1.g_div _ _ n2
    · unfold l211; exact g19 _ _ _ _ _ n2 hu011
    · rw [hl211]; unfold u022; rw [hl111]; unfold RYv RZv
      exact g20 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n1 n2 n6 n4 hRy hRz n7 y02 z02 hJ5
    · rfl
    · unfold u101 u111; exact g16 _ _ _ _ n4
    · rw [hl211]; unfold l210 RZv; exact g23 _ _ _ _ n2 n4
    · rw [hl211]; unfold l210 u101 u111 RZv; exact g24 _ _ _ _ _ _ _ _ n2 n4 n3 hRz hZy hJ4
  · intro d a b
    have hT : IsUnit (TpadF 1 p R d).det := by
      rw [isUnit_iff_ne_zero]
      fin_cases d <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      · rw [tpadx]
        exact det4x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y02 (PP.cast_zero_of s2) z02 (PP.cast_zero_of s4)
          hdx (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp b4)))
      · rw [tpady]
        exact det4y _ _ _ _ _ _ _ _ _ (PP.cast_zero_of s5) (PP.cast_zero_of s6)
          (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp b2))) n8
      · rw [tpadz]
        exact det4y _ _ _ _ _ _ _ _ _ (PP.cast_zero_of s7) (PP.cast_zero_of s8)
          (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp b3))) n9
    show (TpadF 1 p R d * (TpadF 1 p R d)⁻¹) a b = _
    rw [mul_nonsing_inv _ hT, one_apply]
  · intro c d hcd ρ hρ i hi1 hi2
    fin_cases c <;> fin_cases d <;> simp [PF, gF, win] at hi1 hi2 hcd <;> omega

/-- `net_of_cert1` for every odd prime (only `2 ≠ 0` is used). -/
theorem net_of_cert1' (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hk : 3 ≤ k) (R : Rows) (X : Cert p)
    (hX : CertOK 1 p R X) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKN 1 p k R C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have hp := (Fact.out : p.Prime)
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h' | h'
    · exact hp.one_lt.ne' h'
    · exact hp2 h'
  have hs : ((-1 : ZMod p) ^ k) = 1 ∨ ((-1 : ZMod p) ^ k) = -1 := neg_one_pow_eq_or _ k
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hs0 : ((-1 : ZMod p) ^ k) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr h1)
  refine net_of_cert_gen 1 p k (Or.inl rfl) (by omega) R X hX (Wcf1 (k : ZMod p) ((-1) ^ k))
    (hL1 (k : ZMod p)) (fun c => by fin_cases c <;> simp [hL1])
    (fun c a => by fin_cases c <;> fin_cases a <;> simp [hL1])
    (hU1 (k : ZMod p)) (fun d a b hab => by fin_cases d <;> fin_cases a <;> fin_cases b <;> simp_all [hU1])
    (fun d a => by fin_cases d <;> fin_cases a <;> simp [hU1])
    (hμ1 ((-1) ^ k)) (fun c d => by fin_cases c <;> fin_cases d <;> simp [hμ1, hs0])
    (fun c d hcd => by rw [Can, if_pos rfl]; exact act_h1 _ _ h2 hs c d hcd)
    (Wm_eq1 h2 k hk)

/-- **`prop:pp1`** (every odd prime `p`). -/
theorem pp1_net (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (R : Rows) (hS : CondS1 R)
    (hN : CondN1 p R) (hJ1 : J1 p R = 1) (hJ2 : J2 p R = -1) (hJ3 : J3 p R = 2)
    (hJ4 : J4 p R = 2) (hJ5 : J5 p R = 1) (hk : 3 ≤ k) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKN 1 p k R C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) := by
  haveI := Fact.mk hp
  exact net_of_cert1' p k hp2 hk R (cert1 R) (cert1_ok R hS hN hJ1 hJ2 hJ3 hJ4 hJ5)

end Proof

end Z3NetKN.PP1

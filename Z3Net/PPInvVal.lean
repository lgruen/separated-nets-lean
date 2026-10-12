module
public import Z3Net.PPInvA
public import Z3Net.KNNetWm

@[expose] public section

/-!
# `lem:ppinv` (b): the values of the invariants on the windows of the frame `(φ_∞, φ_0, φ_1)`
(entry PPInv)

* `win1_xi2'`: the column `ξ₂ = x_{k-2}` of the frame `(φ_∞, φ_0, φ_1)` for `m = 3k + 1` in every
  characteristic (entry KN's `win1_xi2` assumes `2 ≠ 0`; here `c₂ = C(k+1, 2)` is the cast of a
  natural number);
* `val2`, `val1`: window data with the entries of the table in the proof of `lem:ppinv`(b) have
  `κ₁ = κ₂ = -1` resp. `(J₁, …, J₅) = (1, -1, 2, 2, 1)`, all divisors being `±1`.
-/

namespace Z3NetPI.Val

open Polynomial Z3NetKN.Phi Z3NetKN.Realize Z3NetKN.Frame Z3NetKN.Win

variable {F : Type*} [Field F]

lemma two_choose (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

lemma two_choose_cast (n : ℕ) : 2 * (n.choose 2 : F) = (n : F) * n - n := by
  have := congrArg (fun x : ℕ => (x : F)) (two_choose n)
  push_cast at this
  linear_combination this

local notation "G1" kk:max c:max => (G0 (F := F) (m := 3 * kk + 1) (Z3NetKN.depth 1 kk) c)

/-- `ξ₂ = x_{k-2} : t^k (t-1)^k (t² + a t + c₂)`, `c₂ = C(k, 2) + k`, at `k + 2`, every
characteristic. -/
lemma win1_xi2' (k : ℕ) :
    Z3NetKN.ent (G1 (k + 2) 1) (k + 2) k =
      (-1) ^ (k + 2) * (((k + 2).choose 2 : F) + ((k : F) + 2)) ∧
    Z3NetKN.ent (G1 (k + 2) 1) (k + 3) k =
      (-1) ^ (k + 2) * (((k : F) + 2) * (1 - (((k + 2).choose 2 : F) + ((k : F) + 2)))) ∧
    Z3NetKN.ent (G1 (k + 2) 2) (k + 2) k =
      1 + ((k : F) + 2) + (((k + 2).choose 2 : F) + ((k : F) + 2)) ∧
    Z3NetKN.ent (G1 (k + 2) 2) (k + 3) k = (2 + ((k : F) + 2)) +
      (1 + ((k : F) + 2) + (((k + 2).choose 2 : F) + ((k : F) + 2))) * ((k : F) + 2) := by
  set a : F := ((k + 2 : ℕ) : F) with ha
  set c0 : F := ((k + 2).choose 2 : F) with hc0
  set c : F := c0 + a with hcd
  set W : F[X] := X ^ (k + 2) * ((X - 1) ^ (k + 2) * (X ^ 2 + C a * X + C c)) with hWd
  have hQ : (X ^ 2 + C a * X + C c : F[X]).natDegree ≤ 2 := by
    calc (X ^ 2 + C a * X + C c : F[X]).natDegree
        ≤ max (X ^ 2 + C a * X : F[X]).natDegree (C c).natDegree := natDegree_add_le _ _
      _ ≤ 2 := by
          apply max_le _ (by simp)
          calc (X ^ 2 + C a * X : F[X]).natDegree
              ≤ max (X ^ 2 : F[X]).natDegree (C a * X).natDegree := natDegree_add_le _ _
            _ ≤ 2 := by
                apply max_le (natDegree_X_pow_le 2)
                exact (natDegree_C_mul_le a X).trans (natDegree_X_le.trans (by norm_num))
  have hdeg : W.natDegree ≤ 2 * k + 6 := by
    rw [hWd]; have := natDeg_shape (k + 2) (k + 2) (X ^ 2 + C a * X + C c); omega
  have hcomp : W.comp (X + 1) =
      X ^ (k + 2) * ((X + 1) ^ (k + 2) * (X ^ 2 + C (2 + a) * X + C (1 + a + c))) := by
    rw [hWd, shape_comp, comp_shift_quad]
  have hc := phi_col' (Z3NetKN.depth 1 (k + 2)) (hK1 (k + 2)) W (by omega) k (by omega)
    (by
      intro j hj; rw [d1_0] at hj; rw [o1_0]
      by_cases hjk : j = k
      · rw [if_pos (by omega), hWd, cXpow_at (k + 2) _ (k + 4) _ (by omega),
          cQuad_at _ _ _ (k + 4) (k + 2) rfl, cXm1_top, cXm1_hi _ _ (by omega),
          cXm1_hi _ _ (by omega)]
        ring
      by_cases hjk1 : j = k + 1
      · rw [if_neg (by omega), hWd, cXpow_at (k + 2) _ (k + 3) _ (by omega),
          cQuad_at _ _ _ (k + 3) (k + 1) rfl, cXm1_top1_at _ _ rfl, cXm1_top,
          cXm1_hi _ _ (by omega), ha]
        push_cast; ring
      by_cases hjk2 : j = k + 2
      · rw [if_neg (by omega), hWd, cXpow_at (k + 2) _ (k + 2) _ (by omega),
          cQuad_at _ _ _ (k + 2) k rfl, cXm1_top1_at _ _ rfl, cXm1_top]
        have : ((X - 1 : F[X]) ^ (k + 2)).coeff k = c0 := by
          rw [cXm1, show k + 2 - k = 2 by omega, hc0, Nat.choose_symm_of_eq_add (show k + 2 = k + 2 from rfl)]
          ring
        rw [this, hcd, ha]
        have h2 := two_choose_cast (F := F) (k + 2)
        rw [← hc0] at h2
        push_cast at h2 ⊢
        linear_combination h2
      · rw [if_neg (by omega), coeff_hi W _ _ hdeg (by omega)])
    (by
      intro j hj; rw [d1_1] at hj; rw [o1_1, if_neg (by omega), hWd, cXpow_lt' _ _ _ hj])
    (by
      intro j hj; rw [d1_2] at hj
      rw [o1_2, if_neg (by omega), hcomp, cXpow_lt' _ _ _ hj])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc.2.1 (k + 2) (by omega), hWd, cXpow_at (k + 2) (k + 2) 0 _ (by omega), cQuad_zero,
      cXm1_zero, hcd, ha]
    push_cast; ring
  · rw [hc.2.1 (k + 3) (by omega), hWd, cXpow_at (k + 2) (k + 3) 1 _ (by omega), cQuad_one,
      cXm1_zero, cXm1_one', hcd, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 2) (by omega), hcomp, cXpow_at (k + 2) (k + 2) 0 _ (by omega), cQuad_zero,
      cXp1_zero, hcd, ha]
    push_cast; ring
  · rw [hc.2.2 (k + 3) (by omega), hcomp, cXpow_at (k + 2) (k + 3) 1 _ (by omega), cQuad_one,
      cXp1_zero, cXp1_one, hcd, ha]
    push_cast; ring

/-! ## The values on window data with the entries of the frame -/

/-- `m ≡ 2`: `κ₁ = κ₂ = -1` (proof of `lem:ppinv`(b): `x̃ = x_{k-1} - (a+1) x_k`, `ỹ = y_{k-1} - (a+1) y_k`). -/
theorem val2 (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (a S : F) (hS : S = 1 ∨ S = -1)
    (y0 : W 1 0 0 0 = S) (y1 : W 1 0 0 1 = a * S)
    (z0 : W 2 0 0 0 = 1) (z1 : W 2 0 0 1 = a + 1) (z2 : W 2 0 1 0 = a + 1)
    (z3 : W 2 0 1 1 = a ^ 2 + 2 * a + 2)
    (x0 : W 0 1 0 0 = S) (x1 : W 0 1 0 1 = a * S)
    (w0 : W 2 1 0 0 = S) (w1 : W 2 1 0 1 = (a + 1) * S) (w2 : W 2 1 1 0 = a * S)
    (w3 : W 2 1 1 1 = (a ^ 2 + a - 1) * S) :
    DefK W ∧ kapW1 W = -1 ∧ kapW2 W = -1 := by
  have hS0 : S ≠ 0 := by rcases hS with rfl | rfl <;> norm_num
  have hS2 : S * S = 1 := by rcases hS with rfl | rfl <;> norm_num
  have tx1 : tlx2 W 1 0 = -S := by
    unfold tlx2; rw [y0, y1, z0, z1]; field_simp <;> ring
  have tx2 : tlx2 W 2 1 = 1 := by
    unfold tlx2; rw [z0, z1, z2, z3]; field_simp <;> ring
  have ty0 : tly2 W 0 0 = -S := by
    unfold tly2; rw [x0, x1, w0, w1]; field_simp <;> ring
  have ty2 : tly2 W 2 1 = -S := by
    unfold tly2; rw [w0, w1, w2, w3]; field_simp <;> ring
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [z0]; exact one_ne_zero
  · rw [w0]; exact hS0
  · rw [y0]; exact hS0
  · rw [tx2]; exact one_ne_zero
  · rw [ty0]; exact neg_ne_zero.2 hS0
  · unfold kapW1
    rw [ty2, tx1, x0, z0, tx2, y0, ty0, w0]
    field_simp <;> linear_combination (-S) * hS2
  · unfold kapW2
    rw [z2, z0, w2, w0, tx1, tx2, y0]
    field_simp <;> ring

/-- `m ≡ 1`: `(J₁, …, J₅) = (1, -1, 2, 2, 1)` (the table in the proof of `lem:ppinv`(b);
`c = C(a, 2)`, `2c = a² - a`). -/
theorem val1 (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) (a S c : F) (hS : S = 1 ∨ S = -1)
    (hc : 2 * c = a * a - a)
    (y00 : W 1 0 0 0 = S) (y01 : W 1 0 0 1 = a * S) (y02 : W 1 0 0 2 = S * (c + a))
    (y10 : W 1 0 1 0 = -(a * S)) (y11 : W 1 0 1 1 = -((a ^ 2 - 1) * S))
    (y12 : W 1 0 1 2 = -(S * c * (a + 2)))
    (z00 : W 2 0 0 0 = 1) (z01 : W 2 0 0 1 = a + 1) (z02 : W 2 0 0 2 = c + 2 * a + 1)
    (z10 : W 2 0 1 0 = a) (z11 : W 2 0 1 1 = a ^ 2 + a + 1)
    (z12 : W 2 0 1 2 = (a + 2) * (c + a + 1))
    (e00 : W 0 1 0 0 = S) (e01 : W 0 1 0 1 = a * S)
    (f00 : W 2 1 0 0 = S) (f01 : W 2 1 0 1 = (a + 1) * S) (f10 : W 2 1 1 0 = (a - 1) * S)
    (f11 : W 2 1 1 1 = (a ^ 2 - 2) * S)
    (g00 : W 0 2 0 0 = 1) (g01 : W 0 2 0 1 = -a)
    (h00 : W 1 2 0 0 = -S) (h01 : W 1 2 0 1 = (a + 1) * S) (h10 : W 1 2 1 0 = (a - 1) * S)
    (h11 : W 1 2 1 1 = (2 - a ^ 2) * S) :
    DefJ W ∧ JW1 W = 1 ∧ JW2 W = -1 ∧ JW3 W = 2 ∧ JW4 W = 2 ∧ JW5 W = 1 := by
  have hS0 : S ≠ 0 := by rcases hS with rfl | rfl <;> norm_num
  have hS2 : S * S = 1 := by rcases hS with rfl | rfl <;> norm_num
  have dx : dxW W = S := by unfold dxW; rw [y00, y01, z00, z01]; ring
  have ry : ∀ d i, RYW W d i = W 1 d 1 i + a * W 1 d 0 i := by
    intro d i; unfold RYW; rw [y10, y00]; field_simp <;> ring
  have rz : ∀ d i, RZW W d i = W 2 d 1 i - a * W 2 d 0 i := by
    intro d i; unfold RZW; rw [z10, z00]; field_simp <;> ring
  have ry01 : RYW W 0 1 = S := by rw [ry, y11, y01]; ring
  have ry20 : RYW W 2 0 = -S := by rw [ry, h10, h00]; ring
  have ry21 : RYW W 2 1 = (2 + a) * S := by rw [ry, h11, h01]; ring
  have rz01 : RZW W 0 1 = 1 := by rw [rz, z11, z01]; ring
  have rz10 : RZW W 1 0 = -S := by rw [rz, f10, f00]; ring
  have rz11 : RZW W 1 1 = (-2 - a) * S := by rw [rz, f11, f01]; ring
  have hD : W 1 0 0 1 * W 2 0 0 0 - W 1 0 0 0 * W 2 0 0 1 = -S := by
    rw [y01, z00, y00, z01]; ring
  have xa : xiAW W = -a - 1 := by
    unfold xiAW; rw [hD, y00, z02, y02, z00]; field_simp <;> ring
  have xb : xiBW W = a ^ 2 - c := by
    unfold xiBW; rw [hD, y02, z01, y01, z02]; field_simp <;> ring
  have ry00 : RYW W 0 0 = 0 := by rw [ry, y10, y00]; ring
  have rz00 : RZW W 0 0 = 0 := by rw [rz, z10, z00]; ring
  have ry02 : RYW W 0 2 = S * (a ^ 2 - 2 * c) := by rw [ry, y12, y02]; ring
  have rz02 : RZW W 0 2 = -a ^ 2 + 2 * a + 2 * c + 2 := by rw [rz, z12, z02]; ring
  have txy : tlxW W (RYW W 0 0) (RYW W 0 1) (RYW W 0 2) = -S := by
    unfold tlxW; rw [xa, xb, ry00, ry01, ry02]; linear_combination (-S) * hc
  have txz : tlxW W (RZW W 0 0) (RZW W 0 1) (RZW W 0 2) = 1 := by
    unfold tlxW; rw [xa, xb, rz00, rz01, rz02]; linear_combination hc
  have tzy : tlzW W (RYW W 2 0) (RYW W 2 1) = 2 * S := by
    unfold tlzW; rw [g00, g01, ry20, ry21]; field_simp <;> ring
  have tzY : tlzW W (W 1 2 0 0) (W 1 2 0 1) = S := by
    unfold tlzW; rw [g00, g01, h00, h01]; field_simp <;> ring
  have tyz : tlyW W (RZW W 1 0) (RZW W 1 1) = -2 * S := by
    unfold tlyW; rw [e00, e01, rz10, rz11]; field_simp <;> ring
  have tyZ : tlyW W (W 2 1 0 0) (W 2 1 0 1) = S := by
    unfold tlyW; rw [e00, e01, f00, f01]; field_simp <;> ring
  have hm : -S ≠ 0 := neg_ne_zero.2 hS0
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [y00]; exact hS0
  · rw [z00]; exact one_ne_zero
  · rw [dx]; exact hS0
  · rw [ry20]; exact hm
  · rw [rz10]; exact hm
  · rw [g00]; exact one_ne_zero
  · rw [e00]; exact hS0
  · rw [tzY]; exact hS0
  · rw [tyZ]; exact hS0
  · rw [h00]; exact hm
  · rw [f00]; exact hS0
  · rw [txy]; exact hm
  · unfold JW1; rw [ry01, z00, h00, ry20, dx]; field_simp
  · unfold JW2; rw [rz01, y00, f00, rz10, dx]; field_simp
  · unfold JW3; rw [tzy, tzY, h00, ry20]; field_simp
  · unfold JW4; rw [tyz, tyZ, f00, rz10]; field_simp
  · unfold JW5; rw [txz, txy, y00, f00, ry20, z00, h00, rz10]; field_simp

end Z3NetPI.Val

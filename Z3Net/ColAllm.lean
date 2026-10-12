/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColShift2

@[expose] public section

/-!
# V14 stage S9′: the `m = 3` constant of `cor:allmshift`

From `prop:colshift` for prime `p ≥ 37`: every shift keeps one point per cell (covering `√3 N^{-1/3}`) and
`δN^{1/3} > 0.4693`; equal second and third shift digits keep the exact value of `thm:col`(2); equal
second digits keep `1 - (7p-3)/(√3p²)`; otherwise `1/√3 - 7/(√3p) ≤ δN^{1/3} ≤ 1/√3 + 5/(√3p)`
(`W + 3 ≤ 7`, `w_max ≤ 2`).
-/

namespace Z3NetC.Proofs

open Z3NetF Finset

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-- One point per cell gives the covering radius `√3/q`. -/
lemma cover_cells (X : (Fin 3 → ZMod q) → Fin 3 → ℕ)
    (hX : ∀ n c, q ^ 2 * (n c).val ≤ X n c ∧ X n c < q ^ 2 * ((n c).val + 1))
    (y : Fin 3 → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ n : Fin 3 → ZMod q, Real.sqrt (∑ c, (y c - (X n c : ℝ) / (q : ℝ) ^ 3) ^ 2) ≤
      Real.sqrt 3 * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set f : Fin 3 → ℕ := fun c => ⌊y c * q⌋₊
  have hf : ∀ c, f c < q := by
    intro c
    have : y c * q < q := by nlinarith [(hy c).2]
    exact (Nat.floor_lt (by nlinarith [(hy c).1])).2 (by exact_mod_cast this)
  refine ⟨fun c => (f c : ZMod q), ?_⟩
  rw [cube_rpow _ hq]
  have hval : ∀ c, (((f c : ℕ) : ZMod q)).val = f c := fun c => ZMod.val_cast_of_lt (hf c)
  have hb : ∀ c, (y c - (X (fun c => (f c : ZMod q)) c : ℝ) / (q : ℝ) ^ 3) ^ 2 ≤ ((q : ℝ)⁻¹) ^ 2 := by
    intro c
    obtain ⟨h1, h2⟩ := hX (fun c => (f c : ZMod q)) c
    rw [hval] at h1 h2
    have h1' : (q : ℝ) ^ 2 * f c ≤ X (fun c => (f c : ZMod q)) c := by exact_mod_cast h1
    have h2' : (X (fun c => (f c : ZMod q)) c : ℝ) < (q : ℝ) ^ 2 * (f c + 1) := by exact_mod_cast h2
    have hy1 : (f c : ℝ) ≤ y c * q := Nat.floor_le (by nlinarith [(hy c).1])
    have hy2 : y c * q < f c + 1 := Nat.lt_floor_add_one _
    set u : ℝ := (X (fun c => (f c : ZMod q)) c : ℝ) / (q : ℝ) ^ 3
    have hu1 : (f c : ℝ) ≤ q * u := by
      simp only [u]; rw [show (q : ℝ) * ((X (fun c => (f c : ZMod q)) c : ℝ) / (q : ℝ) ^ 3) =
        (X (fun c => (f c : ZMod q)) c : ℝ) / (q : ℝ) ^ 2 by field_simp]
      rw [le_div_iff₀ (by positivity)]; linarith
    have hu2 : q * u < f c + 1 := by
      simp only [u]; rw [show (q : ℝ) * ((X (fun c => (f c : ZMod q)) c : ℝ) / (q : ℝ) ^ 3) =
        (X (fun c => (f c : ZMod q)) c : ℝ) / (q : ℝ) ^ 2 by field_simp]
      rw [div_lt_iff₀ (by positivity)]; linarith
    have e : y c - u = (q : ℝ)⁻¹ * ((q : ℝ) * y c - (q : ℝ) * u) := by field_simp
    have hi : 0 < (q : ℝ)⁻¹ := inv_pos.2 hq
    rw [e]
    apply sq_le_sq'
    · nlinarith
    · nlinarith
  calc Real.sqrt (∑ c, (y c - (X (fun c => (f c : ZMod q)) c : ℝ) / (q : ℝ) ^ 3) ^ 2)
      ≤ Real.sqrt (3 * ((q : ℝ)⁻¹) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc _ ≤ ∑ _c : Fin 3, ((q : ℝ)⁻¹) ^ 2 := Finset.sum_le_sum fun c _ => hb c
          _ = 3 * ((q : ℝ)⁻¹) ^ 2 := by simp
    _ = Real.sqrt 3 * (q : ℝ)⁻¹ := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]

lemma shift_cells (sh : Fin 3 → Fin 3 → ZMod q) (n : Fin 3 → ZMod q) (c : Fin 3) :
    q ^ 2 * (n c).val ≤ digPointShift q 3 (colGen q) sh (n - sh0 sh) c ∧
      digPointShift q 3 (colGen q) sh (n - sh0 sh) c < q ^ 2 * ((n c).val + 1) := by
  rw [shiftPt_eq, sub_add_cancel]
  have h1 := ZMod.val_lt (colH q (wCol q) n + shB sh c)
  have h2 := ZMod.val_lt (colJ q ellCol n + shB' sh c)
  constructor
  · omega
  · have : q * (colH q (wCol q) n + shB sh c).val + (colJ q ellCol n + shB' sh c).val < q ^ 2 := by
      calc q * (colH q (wCol q) n + shB sh c).val + (colJ q ellCol n + shB' sh c).val
          < q * (colH q (wCol q) n + shB sh c).val + q := by omega
        _ = q * ((colH q (wCol q) n + shB sh c).val + 1) := by ring
        _ ≤ q * q := Nat.mul_le_mul_left _ h1
        _ = q ^ 2 := by ring
    nlinarith

lemma sep_norm (q : ℕ) (hq : 0 < q) (x y : Fin 3 → ℕ) :
    Real.sqrt (∑ c, ((cres (q ^ 3) ((x c : ℤ) - (y c : ℤ)) : ℝ) / (q : ℝ) ^ 3) ^ 2) =
      Real.sqrt (torusDist2 (q ^ 3) x y : ℝ) / (q : ℝ) ^ 2 * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e := sqrt_cres_sum (q ^ 3) (by positivity) x y
  push_cast at e
  rw [e, cube_rpow _ hq']
  field_simp

end Z3NetC.Proofs

/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColConst

@[expose] public section

/-!
# V14 stage S9′: free jitter (`prop:colfree`)

The printed proof: a representative of the difference is `D = q²E + qΔh𝟏 + Δj` with
`E ≡ n' - n (mod q)`, `|Δh| < q`, `|Δj_c| < q`. If some `|E_c| ≥ 2`, `|D_c| > q²`. Otherwise
`3Δh = w·E + Kq` with `K = σ_E + 3L` (`Δh = a·E + qL`), and `3D = q²(3E + K𝟏) + R`,
`R = q(w·E)𝟏 + 3Δj`, `|R_c| ≤ q‖w‖₁ + 3(q-1)`; `|3E + K𝟏|² = 9|z|²` for the integer vector
`z = E - (σ_E + L)𝟏` (the paper's `z = E - ⅓(K + 2σ_E)𝟏`, `Hz = E + ⅓K𝟏`, `H` orthogonal), and
`z = 0` forces `E = 0`.
-/

namespace Z3NetC.Proofs

open Z3NetF Finset Matrix

set_option linter.unusedSectionVars false

variable {q : ℕ} [NeZero q]

/-- The points of `prop:colfree`: `X(n) = q² n + q h(n) 𝟏 + j(n)`. -/
def freePt (q : ℕ) (h : (Fin 3 → ZMod q) → ℕ) (j : (Fin 3 → ZMod q) → Fin 3 → ℕ)
    (n : Fin 3 → ZMod q) : Fin 3 → ℕ :=
  fun c => q ^ 2 * (n c).val + q * h n + j n c

lemma sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

/-- The real conclusion from an integer representative bound: if `T = ∑ D_c²` where
`3D_c = q² y_c + R_c` with `∑ y_c² ≥ 9` and `|R_c| ≤ B`, then `√T ≥ q² - B/√3`. -/
lemma tri_conclude (Q B : ℝ) (_hQ : 0 ≤ Q) (hB : 0 ≤ B) (y R D : Fin 3 → ℝ)
    (hD : ∀ c, 3 * D c = Q * y c + R c) (hy : 9 ≤ ∑ c, y c ^ 2) (hR : ∀ c, |R c| ≤ B) :
    Q - B / Real.sqrt 3 ≤ Real.sqrt (∑ c, D c ^ 2) := by
  have hs := sqrt3_pos
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  by_cases hle : Real.sqrt 3 * B ≤ 3 * Q
  · have hu : (3 * Q) ^ 2 ≤ ∑ c, (Q * y c) ^ 2 := by
      have : ∑ c, (Q * y c) ^ 2 = Q ^ 2 * ∑ c, y c ^ 2 := by
        rw [Finset.mul_sum]; congr 1; funext c; ring
      rw [this]; nlinarith [sq_nonneg Q]
    have hr : ∑ c, R c ^ 2 ≤ (Real.sqrt 3 * B) ^ 2 := by
      have : ∀ c, R c ^ 2 ≤ B ^ 2 := fun c => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hR c) 2
      calc ∑ c, R c ^ 2 ≤ ∑ _c : Fin 3, B ^ 2 := Finset.sum_le_sum fun c _ => this c
        _ = (Real.sqrt 3 * B) ^ 2 := by rw [mul_pow, hs2]; simp
    have ht := tri_lower (fun c => Q * y c) R (3 * Q) (Real.sqrt 3 * B) (by positivity) hle hu hr
    have e : ∑ c, (Q * y c + R c) ^ 2 = 9 * ∑ c, D c ^ 2 := by
      rw [Finset.mul_sum]; congr 1; funext c; rw [← hD c]; ring
    rw [e] at ht
    have h0 : 0 ≤ 3 * Q - Real.sqrt 3 * B := by linarith
    have : 3 * Q - Real.sqrt 3 * B ≤ 3 * Real.sqrt (∑ c, D c ^ 2) := by
      rw [show 3 * Real.sqrt (∑ c, D c ^ 2) = Real.sqrt (9 * ∑ c, D c ^ 2) by
        rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.le_sqrt_of_sq_le ht
    have e2 : B / Real.sqrt 3 = Real.sqrt 3 * B / 3 := by
      field_simp; rw [hs2]
    rw [e2]; linarith
  · push Not at hle
    have : Q - B / Real.sqrt 3 < 0 := by
      have e2 : B / Real.sqrt 3 = Real.sqrt 3 * B / 3 := by
        field_simp; rw [hs2]
      rw [e2]; linarith
    linarith [Real.sqrt_nonneg (∑ c, D c ^ 2)]

/-- **`prop:colfree`**, in `ℤ`-representative form. -/
lemma colfree_core (hq : 2 ≤ q) (w : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (β : ℤ) (h : (Fin 3 → ZMod q) → ℕ)
    (j : (Fin 3 → ZMod q) → Fin 3 → ℕ) (hh : ∀ n, h n < q)
    (hcong : ∀ n, ((h n : ℕ) : ZMod q) = colH q w n + β) (hj : ∀ n c, j n c < q)
    (n n' : Fin 3 → ZMod q) (hne : n ≠ n') :
    (q : ℝ) ^ 2 - (((∑ c, |w c|) + 3) * q - 3) / Real.sqrt 3 ≤
      Real.sqrt (torusDist2 (q ^ 3) (freePt q h j n) (freePt q h j n') : ℝ) := by
  have hq0 : 0 < q := by omega
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨k, hk⟩ := torus_exists (q ^ 3) (by positivity) (freePt q h j n) (freePt q h j n')
  obtain ⟨E, hE⟩ : ∃ E : Fin 3 → ℤ, E = fun c => ((n' c).val : ℤ) - (n c).val + q * k c := ⟨_, rfl⟩
  obtain ⟨dh, hdh⟩ : ∃ x : ℤ, x = (h n' : ℤ) - h n := ⟨_, rfl⟩
  obtain ⟨dj, hdj⟩ : ∃ x : Fin 3 → ℤ, x = fun c => (j n' c : ℤ) - j n c := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Fin 3 → ℤ, D = fun c => (q : ℤ) ^ 2 * E c + q * dh + dj c := ⟨_, rfl⟩
  have hTD : (torusDist2 (q ^ 3) (freePt q h j n) (freePt q h j n') : ℤ) = ∑ c, D c ^ 2 := by
    rw [hk]; congr 1; funext c; rw [hDdef, hE, hdh, hdj]; simp only [freePt]; push_cast; ring
  have hTR : (torusDist2 (q ^ 3) (freePt q h j n) (freePt q h j n') : ℝ) = ∑ c, (D c : ℝ) ^ 2 := by
    exact_mod_cast hTD
  rw [hTR]
  have hdh1 : |dh| < q := by
    rw [hdh]; have := hh n; have := hh n'; rw [abs_lt]; constructor <;> omega
  have hdj1 : ∀ c, |dj c| ≤ q - 1 := by
    intro c; rw [hdj]; have := hj n c; have := hj n' c; rw [abs_le]; constructor <;> simp <;> omega
  have hW0 : (0 : ℝ) ≤ ((∑ c, |w c|) + 3) * q - 3 := by
    have : (0 : ℝ) ≤ ∑ c, |(w c : ℝ)| := by positivity
    push_cast; nlinarith
  have hcast : ∀ c, ((E c : ℤ) : ZMod q) = n' c - n c := by intro c; rw [hE]; simp
  by_cases hbig : ∃ c, 2 ≤ |E c|
  · -- a coordinate moves by two cells
    obtain ⟨c, hc⟩ := hbig
    have hDc : (q : ℤ) ^ 2 ≤ |D c| := by
      rw [hDdef]
      have h1 : 2 * (q : ℤ) ^ 2 ≤ |(q : ℤ) ^ 2 * E c| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]; nlinarith
      have h2 : |(q : ℤ) * dh + dj c| ≤ q * (q - 1) + (q - 1) := by
        calc |(q : ℤ) * dh + dj c| ≤ |(q : ℤ) * dh| + |dj c| := abs_add_le _ _
          _ ≤ q * (q - 1) + (q - 1) := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
            have := hdj1 c
            nlinarith
      have := abs_sub_abs_le_abs_sub ((q : ℤ) ^ 2 * E c) (-((q : ℤ) * dh + dj c))
      rw [abs_neg] at this
      simp only [sub_neg_eq_add] at this
      show (q : ℤ) ^ 2 ≤ |(q : ℤ) ^ 2 * E c + q * dh + dj c|
      rw [add_assoc]
      nlinarith
    have hsq : ((q : ℝ) ^ 2) ^ 2 ≤ ∑ c, (D c : ℝ) ^ 2 := by
      have : ((q : ℝ) ^ 2) ^ 2 ≤ (D c : ℝ) ^ 2 := by
        have : ((q : ℤ) ^ 2) ^ 2 ≤ D c ^ 2 := by
          rw [← sq_abs (D c)]; exact pow_le_pow_left₀ (by positivity) hDc 2
        exact_mod_cast this
      exact this.trans (Finset.single_le_sum (fun c _ => sq_nonneg (D c : ℝ)) (mem_univ c))
    have := Real.le_sqrt_of_sq_le hsq
    have : (0 : ℝ) ≤ (((∑ c, |w c|) + 3) * q - 3) / Real.sqrt 3 := by
      have := sqrt3_pos; positivity
    push_cast at *; linarith
  · push Not at hbig
    have hE1 : ∀ c, -1 ≤ E c ∧ E c ≤ 1 := fun c => by have := abs_lt.1 (hbig c); omega
    -- `Δh = a·E + qL`
    have hdvd : (q : ℤ) ∣ dh - ∑ d, colA q w d * E d := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
      push_cast
      rw [hdh]
      push_cast
      rw [hcong n', hcong n]
      simp only [colH, hcast]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    obtain ⟨L, hL⟩ := hdvd
    have ha : ∀ d, 3 * colA q w d = q + w d := fun d => Int.mul_ediv_cancel' (hw3 d)
    have hsA : ∑ d, colA q w d = q := sum_colA q w hw0 hw3
    set σ := E 0 + E 1 + E 2 with hσ
    set we := ∑ d, w d * E d with hwe
    have h3dh : 3 * dh = q * σ + we + 3 * q * L := by
      have : 3 * ∑ d, colA q w d * E d = q * σ + we := by
        rw [Finset.mul_sum]
        simp only [Fin.sum_univ_three, hσ, hwe]
        linear_combination E 0 * ha 0 + E 1 * ha 1 + E 2 * ha 2
      linear_combination 3 * hL + this
    -- `z`
    by_cases hz : ∀ c, E c = σ + L
    · exfalso
      have he : ∀ c, E c = E 0 := fun c => by rw [hz c, hz 0]
      have hσ3 : σ = 3 * E 0 := by rw [hσ, he 1, he 2]; ring
      have hL2 : L = -2 * E 0 := by have := hz 0; rw [hσ3] at this; linarith
      have hdhq : dh = -(E 0) * q := by
        have : dh = ∑ d, colA q w d * E d + q * L := by linarith
        rw [this, show ∑ d, colA q w d * E d = (∑ d, colA q w d) * E 0 by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun d _ => by rw [he d], hsA, hL2]
        ring
      have hE0 : E 0 = 0 := by
        rw [hdhq] at hdh1
        rw [abs_mul, abs_neg] at hdh1
        have : |E 0| < 1 := by
          by_contra hc; push Not at hc
          have : (q : ℤ) ≤ |E 0| * q := by nlinarith
          rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ q)] at hdh1; linarith
        rw [abs_lt] at this; omega
      apply hne
      funext c
      have h1 := hcast c
      rw [he c, hE0] at h1
      simp at h1
      exact (sub_eq_zero.1 h1.symm).symm
    · push Not at hz
      obtain ⟨c0, hc0⟩ := hz
      -- `y = 3E + K𝟏`, `K = σ + 3L`, `∑ y² = 9 ∑ z²`
      have hy : (9 : ℝ) ≤ ∑ c, ((3 * E c + σ + 3 * L : ℤ) : ℝ) ^ 2 := by
        have hz1 : 1 ≤ ∑ c, (E c - σ - L) ^ 2 := by
          have : 1 ≤ (E c0 - σ - L) ^ 2 := by
            have : E c0 - σ - L ≠ 0 := by intro h'; apply hc0; linarith
            have := sq_pos_of_ne_zero this
            omega
          exact this.trans (Finset.single_le_sum (fun c _ => sq_nonneg (E c - σ - L)) (mem_univ c0))
        have hid : ∑ c, (3 * E c + σ + 3 * L) ^ 2 = 9 * ∑ c, (E c - σ - L) ^ 2 := by
          simp only [Fin.sum_univ_three, hσ]; ring
        have : (9 : ℤ) ≤ ∑ c, (3 * E c + σ + 3 * L) ^ 2 := by rw [hid]; linarith
        exact_mod_cast this
      have hwe1 : |we| ≤ ∑ d, |w d| := by
        rw [hwe]
        calc |∑ d, w d * E d| ≤ ∑ d, |w d * E d| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ d, |w d| := Finset.sum_le_sum fun d _ => by
              rw [abs_mul]
              have : |E d| ≤ 1 := abs_le.2 ⟨(hE1 d).1, (hE1 d).2⟩
              nlinarith [abs_nonneg (w d)]
      apply tri_conclude ((q : ℝ) ^ 2) ((∑ c, |(w c : ℝ)|) * q + 3 * (q - 1)) (by positivity)
        (by have : (0 : ℝ) ≤ ∑ c, |(w c : ℝ)| := by positivity
            nlinarith)
        (fun c => ((3 * E c + σ + 3 * L : ℤ) : ℝ)) (fun c => ((q * we + 3 * dj c : ℤ) : ℝ))
        (fun c => (D c : ℝ)) ?_ hy ?_ |>.trans' (le_of_eq ?_)
      · intro c
        rw [hDdef]
        push_cast
        have := h3dh
        have hR : (3 : ℝ) * dh = q * σ + we + 3 * q * L := by exact_mod_cast this
        linear_combination (q : ℝ) * hR
      · intro c
        push_cast
        calc |(q : ℝ) * we + 3 * dj c| ≤ |(q : ℝ) * we| + |3 * (dj c : ℝ)| := abs_add_le _ _
          _ ≤ (∑ c, |(w c : ℝ)|) * q + 3 * (q - 1) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q)]
            have h1 : |(we : ℝ)| ≤ ∑ c, |(w c : ℝ)| := by
              have := hwe1; push_cast at this ⊢; exact_mod_cast this
            have h2 : |(dj c : ℝ)| ≤ q - 1 := by
              have := hdj1 c; exact_mod_cast this
            have : (0 : ℝ) ≤ q := by positivity
            norm_num
            nlinarith
      · push_cast; ring

end Z3NetC.Proofs

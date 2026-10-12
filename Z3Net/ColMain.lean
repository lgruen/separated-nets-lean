/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ColOpt2
public import Z3Net.ColShift2
public import Z3Net.ColDrift
public import Z3Net.KOne
public import Z3Net.ColAllm

@[expose] public section

/-!
# Solution side of the statements added in V14 stage S9′ (column nets, drift and jitter)

The compared theorems of `scripts/v14_delta.py` (stage S9′, `NEW`), restated by name with the same
statements as in `QUNets/Statements/Dim3.lean` (`sec:m3`), `Deficit.lean` (`lem:Kone`, `sec:drift`)
and `DGS.lean` (`cor:allmshift`, the `m = 3` constant), and closed by `Z3Net/Col*.lean`,
`Z3Net/KOne.lean`.
-/

namespace Z3NetC

open Z3NetF Finset Matrix

/-! ## `sec:m3` -/

/-- **`thm:colmin`**: for every column point set in base `q ≥ 2`, with `G = 3g`
(`g = min_{i,[n]} dist(Δ_i([n]), ⅔q² + q²ℤ)`), the toroidal minimum distance `d` at integer scale `q³`
satisfies `3d² = 2q⁴ + G²` (i.e. `d² = ⅔q⁴ + 3g²`): every pair of distinct points has
`3 d² ≥ 2q⁴ + G²`, and a pair in neighbouring columns `[n]`, `[n + e_i]` attains it. -/
theorem colmin {q : ℕ} [NeZero q] (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    (∀ n n' : Fin 3 → ZMod q, n ≠ n' →
      2 * q ^ 4 + colGap q φ ^ 2 ≤ 3 * torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n')) ∧
    ∃ (i : Fin 3) (n : Fin 3 → ZMod q) (t : ZMod q), n + Pi.single i 1 + (fun _ => t) ≠ n ∧
      3 * torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ (n + Pi.single i 1 + fun _ => t)) =
        2 * q ^ 4 + colGap q φ ^ 2 :=
  ⟨fun n n' h => by exact_mod_cast Proofs.colmin_lower hq φ hφ n n' h,
    Proofs.colmin_attained hq φ hφ⟩

/-- **`thm:colmin`**: `δN^{1/3} ≥ √(2/3)` for every column point set (`N = q³`, toroidal). -/
theorem colmin_real {q : ℕ} [NeZero q] (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ)
    (n n' : Fin 3 → ZMod q) (hne : n ≠ n') :
    Real.sqrt (2 / 3) ≤ Real.sqrt (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℝ) / (q : ℝ) ^ 2 := by
  have h := Proofs.colmin_lower hq φ hφ n n' hne
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hT : 2 * (q : ℝ) ^ 4 ≤ 3 * (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℝ) := by
    have : (2 * (q : ℤ) ^ 4 : ℤ) ≤ 3 * (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℤ) := by
      nlinarith [sq_nonneg (colGap q φ : ℤ)]
    exact_mod_cast this
  rw [le_div_iff₀ (by positivity), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2),
    ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  nlinarith

/-- **`def:col`** (and the setting of `lem:drift`): the digital net with the digits `n_c`, `a·n`, `ℓ·n`
in every coordinate (`a = (q𝟏 + w)/3`, `∑ w = 0`, `w_c ≡ -q (mod 3)`, `∑ ℓ ≡ 0 (mod q)`) is a column
point set: its point with index `n` is `q² n + φ([n]) 𝟏` with the heights `φ = q (a·n) + ℓ·n`. -/
theorem colW_column {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (hℓ : (q : ℤ) ∣ ∑ c, ℓ c) :
    IsHeight q (colPhi q w ℓ) ∧ ∀ n, digPoint q 3 (colGenW q w ℓ) n = colPt q (colPhi q w ℓ) n :=
  ⟨Proofs.isHeight_colPhi q w ℓ hw0 hw3 hℓ, Proofs.digPoint_colGenW q w ℓ⟩

/-- **`def:col`**: `𝒞_q` is a column point set (`gcd(q, 6) = 1`). -/
theorem col_column {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) :
    IsHeight q (colPhi q (wCol q) ellCol) ∧
      ∀ n, digPoint q 3 (colGen q) n = colPt q (colPhi q (wCol q) ellCol) n :=
  ⟨Proofs.isHeight_phiC h6, Proofs.digPoint_colGen⟩

/-- **`thm:col`(1)**: for `q ≥ 5` with `gcd(q, 6) = 1`, `𝒞_q` is a digital `(0,3,3)`-net over `ℤ/qℤ`; its
box minors are units, each one of `1`, `±a_x`, `±a_y`, `±a_z`, `a_x + a_y`. -/
theorem col_net {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    IsNet0 3 q 3 (digPoint q 3 (colGen q)) ∧ ∀ d : Fin 3 → ℕ, ∑ c, d c = 3 →
      IsUnit (boxMatrix (colGen q) d).det ∧
      (boxMatrix (colGen q) d).det ∈ ({1, ((colA q (wCol q) 0 : ℤ) : ZMod q),
        -((colA q (wCol q) 0 : ℤ) : ZMod q), ((colA q (wCol q) 1 : ℤ) : ZMod q),
        -((colA q (wCol q) 1 : ℤ) : ZMod q), -((colA q (wCol q) 2 : ℤ) : ZMod q),
        ((colA q (wCol q) 2 : ℤ) : ZMod q),
        ((colA q (wCol q) 0 : ℤ) : ZMod q) + ((colA q (wCol q) 1 : ℤ) : ZMod q)} : Set (ZMod q)) :=
  ⟨Proofs.col_net h6, fun d hd => ⟨Proofs.col_boxMinor_unit h6 d hd, Proofs.colW_boxMinor _ d hd⟩⟩

/-- **`thm:col`(1)**: every cell of side `q⁻¹` holds a point of `𝒞_q`, so `h ≤ √3 N^{-1/3}`. -/
theorem col_covering {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (y : Fin 3 → ℝ)
    (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v : Fin 3 → ZMod q, Real.sqrt (∑ c, (y c - (digPoint q 3 (colGen q) v c : ℝ) / (q : ℝ) ^ 3) ^ 2) ≤
      Real.sqrt 3 * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) := by
  obtain ⟨n, hn⟩ := Proofs.col_cover (Proofs.phiC q) (Proofs.isHeight_phiC h6).1 y hy
  exact ⟨n, by simpa only [Proofs.digPoint_colGen] using hn⟩

/-- **`thm:col`(2)**: the toroidal minimum distance `d` of `𝒞_q` at integer scale `q³` satisfies
`3d² = 2q⁴ + τ²` (`τ = q² - q - 3` for `q ≡ 2`, `q² - 2q` for `q ≡ 1 (mod 3)`): every pair has
`3 d² ≥ 2q⁴ + τ²`, toroidally and hence Euclidean, and a pair attains it in both. -/
theorem col_mindist {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    (∀ v w : Fin 3 → ZMod q, v ≠ w →
      2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ≤
        3 * (torusDist2 (q ^ 3) (digPoint q 3 (colGen q) v) (digPoint q 3 (colGen q) w) : ℤ) ∧
      2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ≤
        3 * ∑ c, ((digPoint q 3 (colGen q) w c : ℤ) - (digPoint q 3 (colGen q) v c : ℤ)) ^ 2) ∧
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧
      3 * ∑ c, ((digPoint q 3 (colGen q) w c : ℤ) - (digPoint q 3 (colGen q) v c : ℤ)) ^ 2 =
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ∧
      3 * (torusDist2 (q ^ 3) (digPoint q 3 (colGen q) v) (digPoint q 3 (colGen q) w) : ℤ) =
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
  have hX : ∀ n, digPoint q 3 (colGen q) n = colPt q (Proofs.phiC q) n := Proofs.digPoint_colGen
  have hq3 : 0 < q ^ 3 := by have := Nat.pos_of_ne_zero (NeZero.ne q); positivity
  refine ⟨fun v w hvw => ?_, ?_⟩
  · have h1 := Proofs.col_lower h6 hq v w hvw
    rw [← hX, ← hX] at h1
    refine ⟨h1, h1.trans ?_⟩
    have := Proofs.torus_le_eucl (q ^ 3) hq3 (digPoint q 3 (colGen q) v) (digPoint q 3 (colGen q) w)
    linarith
  · obtain ⟨hne, hD⟩ := Proofs.col_pair h6 hq
    refine ⟨1, Pi.single (Proofs.iStar q) 1, hne, ?_, ?_⟩
    · rw [hX, hX, ← Proofs.DCol_norm h6]
      congr 1; exact Finset.sum_congr rfl fun c _ => by rw [hD c]
    · apply le_antisymm
      · have := Proofs.torus_le_eucl (q ^ 3) hq3 (digPoint q 3 (colGen q) 1)
          (digPoint q 3 (colGen q) (Pi.single (Proofs.iStar q) 1))
        have e : 3 * ∑ c, ((digPoint q 3 (colGen q) (Pi.single (Proofs.iStar q) 1) c : ℤ) -
            (digPoint q 3 (colGen q) 1 c : ℤ)) ^ 2 = 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
          rw [hX, hX, ← Proofs.DCol_norm h6]
          congr 1; exact Finset.sum_congr rfl fun c _ => by rw [hD c]
        linarith
      · have h1 := Proofs.col_lower h6 hq 1 _ hne
        rw [← hX, ← hX] at h1; exact h1

/-- **`thm:col`(2)**, closest pairs: two distinct points of `𝒞_q` are at the minimum distance if and
only if their difference is `±D` modulo `q³` (`D` = `DCol q`). -/
theorem col_closest {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (v w : Fin 3 → ZMod q)
    (hvw : v ≠ w) :
    3 * (torusDist2 (q ^ 3) (digPoint q 3 (colGen q) v) (digPoint q 3 (colGen q) w) : ℤ) =
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ↔
      (∀ c, (digPoint q 3 (colGen q) w c : ℤ) ≡ (digPoint q 3 (colGen q) v c : ℤ) + DCol q c
        [ZMOD (q : ℤ) ^ 3]) ∨
      (∀ c, (digPoint q 3 (colGen q) w c : ℤ) ≡ (digPoint q 3 (colGen q) v c : ℤ) - DCol q c
        [ZMOD (q : ℤ) ^ 3]) := by
  simp only [Proofs.digPoint_colGen]
  exact Proofs.col_closest h6 hq v w hvw

/-- **`thm:col`(2)**: for `q ≡ 2 (mod 3)`, `2q⁴ + τ² = 3q⁴ - 2q³ - 5q² + 6q + 9`
(`d² = q⁴ - ⅔q³ - (5/3)q² + 2q + 3`) and `δN^{1/3} = 1 - 1/(3q) - 8/(9q²) + O(q⁻³)`; for `q ≡ 1`,
`2q⁴ + τ² = 3q⁴ - 4q³ + 4q²` (`d² = q⁴ - (4/3)q³ + (4/3)q²`) and `δN^{1/3} = 1 - 2/(3q) + 4/(9q²) + O(q⁻³)`;
with the explicit `O(q⁻³)` bounds `2/q³` resp. `1/q³` (`cCol q = √((2q⁴ + τ²)/3)/q²`). -/
theorem col_expansion {q : ℕ} [NeZero q] (hq : 5 ≤ q) :
    (q % 3 = 2 → 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 = 3 * (q : ℤ) ^ 4 - 2 * q ^ 3 - 5 * q ^ 2 + 6 * q + 9 ∧
      |cCol q - (1 - 1 / (3 * q) - 8 / (9 * (q : ℝ) ^ 2))| ≤ 2 / (q : ℝ) ^ 3) ∧
    (q % 3 = 1 → 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 = 3 * (q : ℤ) ^ 4 - 4 * q ^ 3 + 4 * q ^ 2 ∧
      |cCol q - (1 - 2 / (3 * q) + 4 / (9 * (q : ℝ) ^ 2))| ≤ 1 / (q : ℝ) ^ 3) := by
  refine ⟨fun h => ⟨?_, Proofs.cCol_exp2 q hq h⟩, fun h => ⟨?_, Proofs.cCol_exp1 q hq h⟩⟩
  · simp only [tauCol, h, if_true]; ring
  · simp only [tauCol, show q % 3 ≠ 2 by omega, if_false]; ring

/-- **`thm:col`(2)**, real form: `δN^{1/3} = cCol q` for `𝒞_q` (toroidal, `N = q³`). -/
theorem col_sep_real {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    (∀ v w : Fin 3 → ZMod q, v ≠ w → cCol q * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
      Real.sqrt (∑ c, ((cres (q ^ 3) ((digPoint q 3 (colGen q) v c : ℤ) -
        (digPoint q 3 (colGen q) w c : ℤ)) : ℝ) / (q : ℝ) ^ 3) ^ 2)) ∧
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧ Real.sqrt (∑ c, ((cres (q ^ 3) ((digPoint q 3 (colGen q) v c : ℤ) -
        (digPoint q 3 (colGen q) w c : ℤ)) : ℝ) / (q : ℝ) ^ 3) ^ 2) =
      cCol q * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  obtain ⟨hlow, v0, w0, hne, -, heq⟩ := col_mindist h6 hq
  have hG : (0 : ℝ) ≤ 2 * (q : ℝ) ^ 4 + (tauCol q : ℝ) ^ 2 := by positivity
  refine ⟨fun v w hvw => ?_, v0, w0, hne, ?_⟩
  · have h := (hlow v w hvw).1
    have h' : 2 * (q : ℝ) ^ 4 + (tauCol q : ℝ) ^ 2 ≤
        3 * (torusDist2 (q ^ 3) (digPoint q 3 (colGen q) v) (digPoint q 3 (colGen q) w) : ℝ) := by
      exact_mod_cast h
    exact Proofs.sep_real q hq0 _ _ _ hG h'
  · have e := Proofs.sqrt_cres_sum (q ^ 3) (by positivity) (digPoint q 3 (colGen q) v0)
      (digPoint q 3 (colGen q) w0)
    push_cast at e
    rw [e, Proofs.cube_rpow _ hqR]
    have hT : (torusDist2 (q ^ 3) (digPoint q 3 (colGen q) v0) (digPoint q 3 (colGen q) w0) : ℝ) =
        (2 * (q : ℝ) ^ 4 + (tauCol q : ℝ) ^ 2) / 3 := by
      have : (3 : ℝ) * (torusDist2 (q ^ 3) (digPoint q 3 (colGen q) v0) (digPoint q 3 (colGen q) w0) : ℝ) =
          2 * (q : ℝ) ^ 4 + (tauCol q : ℝ) ^ 2 := by exact_mod_cast heq
      linarith
    rw [hT]; unfold cCol; field_simp

/-- **`thm:col`(3)**: within each residue class modulo `3`, `δN^{1/3} = cCol q` increases with `q`. -/
theorem col_mono (q q' : ℕ) (hq : 5 ≤ q) (hlt : q < q') (hmod : q % 3 = q' % 3) : cCol q < cCol q' :=
  Proofs.cCol_lt q q' hq hlt hmod

/-- **`thm:col`(3)**: `cCol 5 = √513/25 = 0.9059…`, `cCol 7 = √2009/49 = 0.9147…`, `cCol 37 = 0.9823…`,
`cCol 41 > 0.9913`; so `δN^{1/3} > 0.9059` for every `q ≥ 5` coprime to `6`, and `> 0.9823` from
`q ≥ 37` on. -/
theorem col_values :
    cCol 5 = Real.sqrt 513 / 25 ∧ cCol 7 = Real.sqrt 2009 / 49 ∧
    0.9059 < cCol 5 ∧ cCol 5 < 0.9060 ∧ 0.9147 < cCol 7 ∧ cCol 7 < 0.9148 ∧
    0.9823 < cCol 37 ∧ cCol 37 < 0.9824 ∧ 0.9913 < cCol 41 ∧
    ∀ q : ℕ, Nat.Coprime q 6 → 5 ≤ q → 0.9059 < cCol q ∧ (37 ≤ q → 0.9823 < cCol q) := by
  obtain ⟨a, b, c, d, e, f, g⟩ := Proofs.col_values
  exact ⟨Proofs.cCol_5, Proofs.cCol_7, a, b, c, d, e, f, g, fun q h6 hq => Proofs.col_bounds q h6 hq⟩

/-- **`lem:shared`**: in a `(0,m,s)`-net in base `q`, digital or not (a family `X` of `q^m` points at
integer scale `q^m`), for two coordinates `a ≠ b` and `2(j+1) ≤ m`, every value `(α, β)` of the pair of
digits with index `j` of `a` and `b` occurs at exactly `q^{m-2}` points. -/
theorem shared_count {s q m : ℕ} [NeZero q] (X : (Fin m → ZMod q) → Fin s → ℕ)
    (hX : IsNet0 s q m X) (a b : Fin s) (hab : a ≠ b) (j : ℕ) (hj : 2 * (j + 1) ≤ m)
    (α β : ℕ) (hα : α < q) (hβ : β < q) :
    (univ.filter fun v : Fin m → ZMod q =>
        X v a / q ^ (m - 1 - j) % q = α ∧ X v b / q ^ (m - 1 - j) % q = β).card = q ^ (m - 2) :=
  Proofs.shared_count X hX a b hab j hj α β hα hβ

/-- **`lem:shared`**: if the digit with index `j` of `b` is a function `f` of the digit with index `j`
of `a` at every point (`q ≥ 2`), then `2(j+1) > m`. -/
theorem shared_fun {s q m : ℕ} [NeZero q] (hq : 2 ≤ q) (X : (Fin m → ZMod q) → Fin s → ℕ)
    (hX : IsNet0 s q m X) (a b : Fin s) (hab : a ≠ b) (j : ℕ) (f : ℕ → ℕ)
    (hf : ∀ v, X v b / q ^ (m - 1 - j) % q = f (X v a / q ^ (m - 1 - j) % q)) :
    m < 2 * (j + 1) :=
  Proofs.shared_fun hq X hX a b hab j f hf

/-- **`prop:colfree`**: points `X(n) = q² n + q h(n) 𝟏 + j(n)` (one per cell `n`, integer scale `q³`),
`h(n) ∈ [0, q)` with `h(n) ≡ a·n + β (mod q)`, `a = (q𝟏 + w)/3` (`∑ w = 0`, `w_c ≡ -q (mod 3)`), and
arbitrary `j(n) ∈ [0, q)³`: any two distinct points have toroidal distance at least
`q² - ((‖w‖₁ + 3) q - 3)/√3`. -/
theorem colfree {q : ℕ} [NeZero q] (hq : 2 ≤ q) (w : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (β : ℤ) (h : (Fin 3 → ZMod q) → ℕ)
    (j : (Fin 3 → ZMod q) → Fin 3 → ℕ) (hh : ∀ n, h n < q)
    (hcong : ∀ n, ((h n : ℕ) : ZMod q) = colH q w n + β) (hj : ∀ n c, j n c < q)
    (n n' : Fin 3 → ZMod q) (hne : n ≠ n') :
    (q : ℝ) ^ 2 - (((∑ c, |w c|) + 3) * q - 3) / Real.sqrt 3 ≤
      Real.sqrt (torusDist2 (q ^ 3) (fun c => q ^ 2 * (n c).val + q * h n + j n c)
        (fun c => q ^ 2 * (n' c).val + q * h n' + j n' c) : ℝ) :=
  Proofs.colfree_core hq w hw0 hw3 β h j hh hcong hj n n' hne

/-- **`prop:colshift`(1)**: if the digital shift `τ` of `𝒞_q` has equal second digits `τ_{c,2}` and equal
third digits `τ_{c,3}` (Lean: `sh c 1`, `sh c 2`), the minimum distance of `𝒞_q ⊕ τ` is that of `𝒞_q`:
`3d² = 2q⁴ + τ²` (toroidal). -/
theorem colshift_eq {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q)
    (sh : Fin 3 → Fin 3 → ZMod q) (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1)
    (h3 : sh 0 2 = sh 1 2 ∧ sh 1 2 = sh 2 2) :
    (∀ v w : Fin 3 → ZMod q, v ≠ w → 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ≤
      3 * (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℤ)) ∧
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧
      3 * (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℤ) = 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 :=
  Proofs.colshift_eq h6 hq sh h2 h3

/-- **`prop:colshift`(2)**: equal second shift digits: `δN^{1/3} ≥ 1 - (7q - 3)/(√3 q²)` (toroidal; integer
scale: `d ≥ q² - (7q - 3)/√3`). -/
theorem colshift_agree2 {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q)
    (sh : Fin 3 → Fin 3 → ZMod q) (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) (v w : Fin 3 → ZMod q)
    (hvw : v ≠ w) :
    (q : ℝ) ^ 2 - (7 * q - 3) / Real.sqrt 3 ≤
      Real.sqrt (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℝ) :=
  Proofs.colshift_agree2 h6 hq sh h2 v w hvw

/-- **`prop:colshift`(3)**, lower bound: for every digital shift,
`δN^{1/3} ≥ (1 - (W+3)/q + 3/q²)/√3` (`W = 2` for `q ≡ 2`, `4` for `q ≡ 1 (mod 3)`; integer scale:
`d ≥ (q² - (W+3)q + 3)/√3`), and this exceeds `0.4693` for every `q ≥ 37`. -/
theorem colshift_lower {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q)
    (sh : Fin 3 → Fin 3 → ZMod q) :
    (∀ v w : Fin 3 → ZMod q, v ≠ w →
      ((q : ℝ) ^ 2 - ((if q % 3 = 2 then (2 : ℤ) else 4 : ℤ) + 3) * q + 3) / Real.sqrt 3 ≤
        Real.sqrt (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
          (digPointShift q 3 (colGen q) sh w) : ℝ)) ∧
    (37 ≤ q → 0.4693 < (1 - ((if q % 3 = 2 then (2 : ℤ) else 4 : ℤ) + 3) / (q : ℝ) + 3 / (q : ℝ) ^ 2) /
      Real.sqrt 3) :=
  ⟨fun v w hvw => Proofs.colshift_lower h6 hq sh v w hvw, fun h => Proofs.colshift_4693 h⟩

/-- **`prop:colshift`(3)**, upper bound: if the second shift digits are not all equal, some pair of points
of `𝒞_q ⊕ τ` has Euclidean (hence toroidal) distance at most `√3 (q a_max + q - 1)` at integer scale
`q³`, `a_max = max_c a_c`; i.e. `δN^{1/3} ≤ (1 + (3 + w_max)/q - 3/q²)/√3`, `w_max = max_c w_c`
(`3 a_max = q + w_max`). -/
theorem colshift_upper {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q)
    (sh : Fin 3 → Fin 3 → ZMod q) (hne : ¬ (sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1)) :
    3 * univ.sup' univ_nonempty (colA q (wCol q)) = q + univ.sup' univ_nonempty (wCol q) ∧
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧
      (∀ c, |(digPointShift q 3 (colGen q) sh w c : ℤ) - (digPointShift q 3 (colGen q) sh v c : ℤ)| ≤
        q * univ.sup' univ_nonempty (colA q (wCol q)) + q - 1) ∧
      Real.sqrt (∑ c, ((digPointShift q 3 (colGen q) sh w c : ℝ) -
          (digPointShift q 3 (colGen q) sh v c : ℝ)) ^ 2) / (q : ℝ) ^ 2 ≤
        (1 + (3 + univ.sup' univ_nonempty (wCol q)) / (q : ℝ) - 3 / (q : ℝ) ^ 2) / Real.sqrt 3 ∧
      Real.sqrt (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
          (digPointShift q 3 (colGen q) sh w) : ℝ) / (q : ℝ) ^ 2 ≤
        (1 + (3 + univ.sup' univ_nonempty (wCol q)) / (q : ℝ) - 3 / (q : ℝ) ^ 2) / Real.sqrt 3 := by
  have hA := Proofs.aMax_eq (q := q) h6
  refine ⟨hA, ?_⟩
  obtain ⟨v, w, hvw, hb⟩ := Proofs.colshift_upper h6 hq sh hne
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs := Proofs.sqrt3_pos
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set B : ℝ := q * (Proofs.aMax q : ℝ) + q - 1 with hB
  have hB0 : 0 ≤ B := by
    have : (1 : ℤ) ≤ Proofs.aMax q := by
      have := (Proofs.colA_bounds h6 hq 0).1
      exact this.trans (Finset.le_sup' _ (mem_univ 0))
    have : (1 : ℝ) ≤ Proofs.aMax q := by exact_mod_cast this
    have := mul_le_mul_of_nonneg_left this hq0.le
    have : (5 : ℝ) ≤ q := by exact_mod_cast hq
    rw [hB]; nlinarith
  have hE : Real.sqrt (∑ c, ((digPointShift q 3 (colGen q) sh w c : ℝ) -
      (digPointShift q 3 (colGen q) sh v c : ℝ)) ^ 2) ≤ Real.sqrt 3 * B := by
    rw [show Real.sqrt 3 * B = Real.sqrt (3 * B ^ 2) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hB0]]
    apply Real.sqrt_le_sqrt
    have : ∀ c, ((digPointShift q 3 (colGen q) sh w c : ℝ) - (digPointShift q 3 (colGen q) sh v c : ℝ)) ^ 2
        ≤ B ^ 2 := by
      intro c
      have h1 : |((digPointShift q 3 (colGen q) sh w c : ℤ) - (digPointShift q 3 (colGen q) sh v c : ℤ) : ℝ)|
          ≤ B := by
        have := hb c
        rw [hB]; exact_mod_cast this
      push_cast at h1
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc _ ≤ ∑ _c : Fin 3, B ^ 2 := Finset.sum_le_sum fun c _ => this c
      _ = 3 * B ^ 2 := by simp
  have hval : Real.sqrt 3 * B / (q : ℝ) ^ 2 =
      (1 + (3 + univ.sup' univ_nonempty (wCol q)) / (q : ℝ) - 3 / (q : ℝ) ^ 2) / Real.sqrt 3 := by
    have hA' : (3 : ℝ) * (Proofs.aMax q : ℝ) = q + univ.sup' univ_nonempty (wCol q) := by
      have := hA; unfold Proofs.aMax at this ⊢; exact_mod_cast this
    rw [hB]; field_simp; rw [hs2]; nlinarith [hA']
  have hq3 : 0 < q ^ 3 := by have := Nat.pos_of_ne_zero (NeZero.ne q); positivity
  have hT : Real.sqrt (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
      (digPointShift q 3 (colGen q) sh w) : ℝ) ≤ Real.sqrt (∑ c, ((digPointShift q 3 (colGen q) sh w c : ℝ) -
      (digPointShift q 3 (colGen q) sh v c : ℝ)) ^ 2) := by
    apply Real.sqrt_le_sqrt
    have := Proofs.torus_le_eucl (q ^ 3) hq3 (digPointShift q 3 (colGen q) sh v)
      (digPointShift q 3 (colGen q) sh w)
    exact_mod_cast this
  refine ⟨v, w, hvw, hb, ?_, ?_⟩
  · rw [← hval]; gcongr
  · rw [← hval]; gcongr; exact hT.trans hE

/-! ## `sec:drift` -/

/-- **`lem:drift`(1)**: for the digital column net with the digits `n_c`, `a·n`, `ℓ·n`
(`a = (q𝟏 + w)/3`), a step along `e_i` has `Δ_i ≡ q a_i + r_i - q κ' (mod q²)` (`= ⅓q² + ε_i` or
`⅓q² + ε_i - q` with `3ε_i = q w_i + 3 r_i` when `3 a_i = q + w_i`), `r_i` the residue of `ℓ_i` and
`κ' = [j(n) + r_i ≥ q]` the wrap of the third digit; if `r_i ≠ 0`, both cases occur. -/
theorem drift_step {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (i : Fin 3) :
    (∀ n, colStep q (colPhi q w ℓ) i n ≡
      q * colA q w i + (((ℓ i : ℤ) : ZMod q)).val -
        q * (if (colJ q ℓ n).val + (((ℓ i : ℤ) : ZMod q)).val < q then 0 else 1) [ZMOD (q : ℤ) ^ 2]) ∧
    ((((ℓ i : ℤ) : ZMod q)).val ≠ 0 →
      (∃ n, (colJ q ℓ n).val + (((ℓ i : ℤ) : ZMod q)).val < q) ∧
      ∃ n, ¬ (colJ q ℓ n).val + (((ℓ i : ℤ) : ZMod q)).val < q) := by
  refine ⟨fun n => Proofs.drift_step w ℓ i n, fun hr => ⟨⟨0, ?_⟩, ?_⟩⟩
  · have : colJ q ℓ (0 : Fin 3 → ZMod q) = 0 := by simp [colJ]
    rw [this, ZMod.val_zero, zero_add]; exact ZMod.val_lt _
  · have h := Proofs.wraps_card ℓ (0 : Fin 3 → ZMod q) i
    have hpos : 0 < (univ.filter fun t : ZMod q =>
        ¬ (colJ q ℓ ((0 : Fin 3 → ZMod q) + Pi.single i t)).val + (((ℓ i : ℤ) : ZMod q)).val < q).card := by
      have : (0 : ℤ) < (((ℓ i : ℤ) : ZMod q)).val := by exact_mod_cast Nat.pos_of_ne_zero hr
      rw [← h] at this; exact_mod_cast this
    obtain ⟨t, ht⟩ := Finset.card_pos.1 hpos
    have ht' := (Finset.mem_filter.1 ht).2
    exact ⟨_, ht'⟩

/-- **`lem:drift`(2)**: along each cycle of `q` steps in the direction `e_i` the third digit wraps exactly
`r_i` times; if moreover `|ε_i| < ½q²` and `|ε_i - q| < ½q²` (in thirds: `2|q w_i + 3 r_i| < 3q²` and
`2|q w_i + 3 r_i - 3q| < 3q²`; revision 15.1), the excesses of the cycle sum to `⅓q² w_i` (Lean: three
times the excess, `excess3`, summing to `q² w_i`). -/
theorem drift_cycle {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (i : Fin 3)
    (n : Fin 3 → ZMod q) :
    (((univ.filter fun t : ZMod q =>
        ¬ (colJ q ℓ (n + Pi.single i t)).val + (((ℓ i : ℤ) : ZMod q)).val < q).card : ℕ) : ℤ) =
      (((ℓ i : ℤ) : ZMod q)).val ∧
    (2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val| < 3 * (q : ℤ) ^ 2 →
      2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q| < 3 * (q : ℤ) ^ 2 →
      ∑ t : ZMod q, excess3 q (colStep q (colPhi q w ℓ) i (n + Pi.single i t)) = (q : ℤ) ^ 2 * w i) :=
  ⟨Proofs.wraps_card ℓ n i, fun h1 h2 => Proofs.excess_sum w ℓ hw3 i ⟨h1, h2⟩ n⟩

/-- **`lem:drift`(2)**, the instance of the range hypothesis: `|w_i| ≤ 2` and `q ≥ 4`. -/
theorem drift_range {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (i : Fin 3) (hw : |w i| ≤ 2) (hq : 4 ≤ q) :
    2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val| < 3 * (q : ℤ) ^ 2 ∧
      2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q| < 3 * (q : ℤ) ^ 2 :=
  Proofs.drift_range w ℓ i hw hq

/-- **`lem:drift`(3)**: if `q ≥ 10` and `|w_c| ≤ 2`, every excess (thirds) lies in `[-½q², q²]` (the paper's
`[-⅙q², ⅓q²]`), the largest one is `M = max_i (q w_i + 3 r_i)` (`3 max_i ε_i`), and
`3g = q² - M` in `thm:colmin`, i.e. `d² = q⁴ - 2q²η + 3η²` with `η = M/3`. -/
theorem drift_eta {q : ℕ} [NeZero q] (hq : 10 ≤ q) (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (hw2 : ∀ c, |w c| ≤ 2) :
    (∀ i n, -(q : ℤ) ^ 2 ≤ 2 * excess3 q (colStep q (colPhi q w ℓ) i n) ∧
      excess3 q (colStep q (colPhi q w ℓ) i n) ≤ (q : ℤ) ^ 2) ∧
    (∀ i n, excess3 q (colStep q (colPhi q w ℓ) i n) ≤
      univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) ∧
    (∃ i n, excess3 q (colStep q (colPhi q w ℓ) i n) =
      univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) ∧
    (colGap q (colPhi q w ℓ) : ℤ) =
      (q : ℤ) ^ 2 - univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val :=
  Proofs.drift_eta_core hq w ℓ hw0 hw3 hw2

/-- **`lem:drift`(4)**: if the digital column net is a `(0,3,3)`-net, then `∑_i ε_i ≥ q` (thirds:
`∑_i (q w_i + 3 r_i) ≥ 3q`), `max_i ε_i ≥ ⅓q` (thirds: `≥ q`), and `max_i ε_i ≥ ⅔q` (thirds: `≥ 2q`)
if `q ≡ 1 (mod 3)`. -/
theorem drift_net {q : ℕ} [NeZero q] (hq : 2 ≤ q) (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (hℓ : (q : ℤ) ∣ ∑ c, ℓ c)
    (hnet : IsNet0 3 q 3 (digPoint q 3 (colGenW q w ℓ))) :
    3 * (q : ℤ) ≤ ∑ i, ((q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) ∧
    (q : ℤ) ≤ (univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) ∧
    (q % 3 = 1 →
      2 * (q : ℤ) ≤ univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) :=
  Proofs.drift_net_core hq w ℓ hw0 hw3 hℓ hnet

/-- **`cor:colceil`**: every column point set in base `q ≥ 2` has `3g ≤ q²`, i.e. a pair of distinct points
at toroidal distance at most `q²` at integer scale `q³` (`δN^{1/3} ≤ 1`). -/
theorem colceil {q : ℕ} [NeZero q] (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    colGap q φ ≤ q ^ 2 ∧ ∃ n n' : Fin 3 → ZMod q, n ≠ n' ∧
      torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') ≤ q ^ 4 :=
  ⟨Proofs.colceil_gap hq φ hφ, Proofs.colceil_pair hq φ hφ⟩

/-- **`thm:O`(1)** (every `q ≥ 2`): a column point set is a `(0,3,3)`-net in base `q` if and only if `φ` is a
bijection from `T` onto `{0, …, q²-1}` (onto, and equal heights only within a column) and `⌊φ/q⌋` is
injective on every line of `T` in the directions `[e_x], [e_y], [e_z]`. -/
theorem colO_net_iff {q : ℕ} [NeZero q] (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    IsNet0 3 q 3 (colPt q φ) ↔
      ((∀ y, y < q ^ 2 → ∃ n, φ n = y) ∧
        (∀ n n', φ n = φ n' → ∃ t : ZMod q, n' = n + fun _ => t)) ∧
      (∀ (c : Fin 3) n (t : ZMod q), φ (n + Pi.single c t) / q = φ n / q → t = 0) :=
  Proofs.colPt_net_iff hq φ hφ

/-- **`thm:O`(2)** (every even `q ≥ 2`): no column point set is a `(0,3,3)`-net in base `q`. -/
theorem colO_even {q : ℕ} [NeZero q] (hq : 2 ≤ q) (he : Even q) (φ : (Fin 3 → ZMod q) → ℕ)
    (hφ : IsHeight q φ) : ¬ IsNet0 3 q 3 (colPt q φ) :=
  Proofs.colPt_not_net_even hq he φ hφ

/-- **`thm:O`(3)**: for odd `q ≥ 4` with `3 ∤ q`, every column point set that is a `(0,3,3)`-net has
`3g ≤ τ`, i.e. toroidal minimum distance `d` with `3d² ≤ 2q⁴ + τ² = 3d²(𝒞_q)` (`thm:col`(2)). -/
theorem colO_opt {q : ℕ} [NeZero q] (hq : 4 ≤ q) (h3 : ¬ 3 ∣ q) (hodd : Odd q)
    (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) (hnet : IsNet0 3 q 3 (colPt q φ)) :
    (colGap q φ : ℤ) ≤ tauCol q ∧ ∃ n n' : Fin 3 → ZMod q, n ≠ n' ∧
      3 * (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℤ) ≤ 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
  have h6 : Nat.Coprime q 6 := by
    have h2 : Nat.Coprime 2 q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by
      intro hd; obtain ⟨k, hk⟩ := hd; have := Nat.odd_iff.1 hodd; omega)
    have h3' : Nat.Coprime 3 q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    exact Nat.Coprime.mul_right (Nat.coprime_comm.1 h2) (Nat.coprime_comm.1 h3')
  have hq5 : 5 ≤ q := by
    have := Nat.odd_iff.1 hodd
    rcases (show q = 4 ∨ 5 ≤ q by omega) with h | h
    · omega
    · exact h
  have hG := Proofs.colO_opt h6 hq5 φ hφ hnet
  refine ⟨hG, ?_⟩
  obtain ⟨i, n, t, hne, heq⟩ := Proofs.colmin_attained (by omega) φ hφ
  refine ⟨n, _, hne.symm, ?_⟩
  have h0 : (0 : ℤ) ≤ colGap q φ := by positivity
  have : (colGap q φ : ℤ) ^ 2 ≤ tauCol q ^ 2 := by nlinarith
  have heq' : (3 * torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ (n + Pi.single i 1 + fun _ => t)) : ℤ) =
      2 * (q : ℤ) ^ 4 + (colGap q φ : ℤ) ^ 2 := by exact_mod_cast heq
  linarith

/-! ## `sec:dgs`: the `m = 3` constant of `cor:allmshift` -/

/-- **`cor:allmshift`**, the resolution `m = 3` (the column net `𝒞_p`): for every prime `p ≥ 37` and every
digital shift `τ` (Lean: `sh c k` is the digit `k+1` of the shift of coordinate `c`), `𝒞_p ⊕ τ` keeps one
point in every cell (`h ≤ √3 N^{-1/3}`) and has `δN^{1/3} > 0.4693` (toroidal); if the shift digits of
the three coordinates agree at the second and third digit, `δN^{1/3}` is the exact value of
`thm:col`(2) (`cCol p`); if they agree at the second digit, `δN^{1/3} ≥ 1 - (7p-3)/(√3p²)`; otherwise
`1/√3 - 7/(√3p) ≤ δN^{1/3} ≤ 1/√3 + 5/(√3p)`. -/
theorem allmshift_m3 (p : ℕ) [NeZero p] (hp : p.Prime) (hp37 : 37 ≤ p) (sh : Fin 3 → Fin 3 → ZMod p) :
    (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin 3 → ZMod p,
      Real.sqrt (∑ c, (y c - (digPointShift p 3 (colGen p) sh v c : ℝ) / (p : ℝ) ^ 3) ^ 2) ≤
        Real.sqrt 3 * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ)))) ∧
    (∀ v w : Fin 3 → ZMod p, v ≠ w → 0.4693 * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) <
      Real.sqrt (∑ c, ((cres (p ^ 3) ((digPointShift p 3 (colGen p) sh v c : ℤ) -
        (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2)) ∧
    ((sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) → (sh 0 2 = sh 1 2 ∧ sh 1 2 = sh 2 2) →
      (∀ v w : Fin 3 → ZMod p, v ≠ w → cCol p * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
        Real.sqrt (∑ c, ((cres (p ^ 3) ((digPointShift p 3 (colGen p) sh v c : ℤ) -
          (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2)) ∧
      ∃ v w : Fin 3 → ZMod p, v ≠ w ∧ Real.sqrt (∑ c, ((cres (p ^ 3)
        ((digPointShift p 3 (colGen p) sh v c : ℤ) - (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) /
          (p : ℝ) ^ 3) ^ 2) = cCol p * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ)))) ∧
    ((sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) → ∀ v w : Fin 3 → ZMod p, v ≠ w →
      (1 - (7 * p - 3) / (Real.sqrt 3 * (p : ℝ) ^ 2)) * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
        Real.sqrt (∑ c, ((cres (p ^ 3) ((digPointShift p 3 (colGen p) sh v c : ℤ) -
          (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2)) ∧
    (¬ (sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) →
      (∀ v w : Fin 3 → ZMod p, v ≠ w →
        (1 / Real.sqrt 3 - 7 / (Real.sqrt 3 * p)) * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (p ^ 3) ((digPointShift p 3 (colGen p) sh v c : ℤ) -
            (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2)) ∧
      ∃ v w : Fin 3 → ZMod p, v ≠ w ∧ Real.sqrt (∑ c, ((cres (p ^ 3)
        ((digPointShift p 3 (colGen p) sh v c : ℤ) - (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) /
          (p : ℝ) ^ 3) ^ 2) ≤ (1 / Real.sqrt 3 + 5 / (Real.sqrt 3 * p)) * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ)))) := by
  have hp5 : 5 ≤ p := by omega
  have hp0 : 0 < p := by omega
  have hpR : (37 : ℝ) ≤ p := by exact_mod_cast hp37
  have h6 : Nat.Coprime p 6 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hs := Proofs.sqrt3_pos
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hN : (0 : ℝ) < ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) := by positivity
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  -- the separation through `√T / p²`
  have hsep : ∀ v w : Fin 3 → ZMod p, Real.sqrt (∑ c, ((cres (p ^ 3)
      ((digPointShift p 3 (colGen p) sh v c : ℤ) - (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) /
        (p : ℝ) ^ 3) ^ 2) = Real.sqrt (torusDist2 (p ^ 3) (digPointShift p 3 (colGen p) sh v)
          (digPointShift p 3 (colGen p) sh w) : ℝ) / (p : ℝ) ^ 2 * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) :=
    fun v w => Proofs.sep_norm p hp0 _ _
  have hW : ((if p % 3 = 2 then (2 : ℤ) else 4 : ℤ) : ℝ) ≤ 4 := by split_ifs <;> norm_num
  have hW0 : (0 : ℝ) ≤ ((if p % 3 = 2 then (2 : ℤ) else 4 : ℤ) : ℝ) := by split_ifs <;> norm_num
  have hlow : ∀ v w : Fin 3 → ZMod p, v ≠ w →
      (1 - (((if p % 3 = 2 then (2 : ℤ) else 4 : ℤ) : ℝ) + 3) / (p : ℝ) + 3 / (p : ℝ) ^ 2) / Real.sqrt 3 ≤
        Real.sqrt (torusDist2 (p ^ 3) (digPointShift p 3 (colGen p) sh v)
          (digPointShift p 3 (colGen p) sh w) : ℝ) / (p : ℝ) ^ 2 := by
    intro v w hvw
    have h := (colshift_lower h6 hp5 sh).1 v w hvw
    rw [le_div_iff₀ hp2]
    calc (1 - (((if p % 3 = 2 then (2 : ℤ) else 4 : ℤ) : ℝ) + 3) / (p : ℝ) + 3 / (p : ℝ) ^ 2) /
          Real.sqrt 3 * (p : ℝ) ^ 2 =
          ((p : ℝ) ^ 2 - (((if p % 3 = 2 then (2 : ℤ) else 4 : ℤ) : ℝ) + 3) * p + 3) / Real.sqrt 3 := by
          field_simp
      _ ≤ _ := h
  refine ⟨fun y hy => ?_, fun v w hvw => ?_, fun h2 h3 => ⟨fun v w hvw => ?_, ?_⟩, fun h2 v w hvw => ?_,
    fun hne => ⟨fun v w hvw => ?_, ?_⟩⟩
  · obtain ⟨n, hn⟩ := Proofs.cover_cells (fun n => digPointShift p 3 (colGen p) sh (n - Proofs.sh0 sh))
      (fun n c => Proofs.shift_cells sh n c) y hy
    exact ⟨_, hn⟩
  · rw [hsep]
    have h1 := (colshift_lower h6 hp5 sh).2 hp37
    have h2 := hlow v w hvw
    exact mul_lt_mul_of_pos_right (lt_of_lt_of_le h1 h2) hN
  · rw [hsep]
    obtain ⟨hl, -⟩ := colshift_eq h6 hp5 sh h2 h3
    have h := hl v w hvw
    have hT : 2 * (p : ℝ) ^ 4 + (tauCol p : ℝ) ^ 2 ≤
        3 * (torusDist2 (p ^ 3) (digPointShift p 3 (colGen p) sh v)
          (digPointShift p 3 (colGen p) sh w) : ℝ) := by exact_mod_cast h
    apply mul_le_mul_of_nonneg_right _ hN.le
    unfold cCol
    apply div_le_div_of_nonneg_right _ hp2.le
    apply Real.sqrt_le_sqrt; linarith
  · obtain ⟨-, v, w, hvw, heq⟩ := colshift_eq h6 hp5 sh h2 h3
    refine ⟨v, w, hvw, ?_⟩
    rw [hsep]
    have hT : (torusDist2 (p ^ 3) (digPointShift p 3 (colGen p) sh v)
        (digPointShift p 3 (colGen p) sh w) : ℝ) = (2 * (p : ℝ) ^ 4 + (tauCol p : ℝ) ^ 2) / 3 := by
      have : (3 : ℝ) * (torusDist2 (p ^ 3) (digPointShift p 3 (colGen p) sh v)
          (digPointShift p 3 (colGen p) sh w) : ℝ) = 2 * (p : ℝ) ^ 4 + (tauCol p : ℝ) ^ 2 := by
        exact_mod_cast heq
      linarith
    rw [hT]; rfl
  · rw [hsep]
    have h := colshift_agree2 h6 hp5 sh h2 v w hvw
    apply mul_le_mul_of_nonneg_right _ hN.le
    rw [le_div_iff₀ hp2]
    calc (1 - (7 * p - 3) / (Real.sqrt 3 * (p : ℝ) ^ 2)) * (p : ℝ) ^ 2 =
        (p : ℝ) ^ 2 - (7 * p - 3) / Real.sqrt 3 := by field_simp
      _ ≤ _ := h
  · rw [hsep]
    apply mul_le_mul_of_nonneg_right _ hN.le
    refine le_trans ?_ (hlow v w hvw)
    have e : (1 / Real.sqrt 3 - 7 / (Real.sqrt 3 * p)) =
        (1 - 7 / (p : ℝ)) / Real.sqrt 3 := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hs.le
    have : (0 : ℝ) < 3 / (p : ℝ) ^ 2 := by positivity
    have : (((if p % 3 = 2 then (2 : ℤ) else 4 : ℤ) : ℝ) + 3) / (p : ℝ) ≤ 7 / p := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    linarith
  · obtain ⟨-, v, w, hvw, -, -, hT⟩ := colshift_upper h6 hp5 sh hne
    refine ⟨v, w, hvw, ?_⟩
    rw [hsep]
    apply mul_le_mul_of_nonneg_right _ hN.le
    refine le_trans hT ?_
    have hwm : univ.sup' univ_nonempty (wCol p) ≤ 2 := by
      apply Finset.sup'_le; intro c _
      have := (Proofs.wCol_props (q := p) h6).2.2.1 c
      exact (abs_le.1 this).2
    have hwm' : ((univ.sup' univ_nonempty (wCol p) : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hwm
    have e : (1 / Real.sqrt 3 + 5 / (Real.sqrt 3 * p)) = (1 + 5 / (p : ℝ)) / Real.sqrt 3 := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hs.le
    have : (3 + ((univ.sup' univ_nonempty (wCol p) : ℤ) : ℝ)) / (p : ℝ) ≤ 5 / p := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    have : (0 : ℝ) < 3 / (p : ℝ) ^ 2 := by positivity
    linarith

end Z3NetC

namespace Z3NetF

open Finset

/-- **`lem:Kone`**: a design `F` (with `L ≥ 1` levels) with some nonzero off-diagonal entry `F₀[a][b]` has
deficit `K(F) ≥ 1`. -/
theorem Kone {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (hL : 1 ≤ L) (a b : Fin s) (hab : a ≠ b)
    (h : F 0 a b ≠ 0) : 1 ≤ Kdef F L :=
  Proofs.KOne.Kone F L hL a b hab h

end Z3NetF

/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.FDefs

@[expose] public section

/-!
# Definitions: column point sets and column nets (`sec:m3`, `sec:drift`)

V14 stage S9′. Cells and indices are `n : Fin 3 → ZMod q` (the cell digit of coordinate `c` is
`(n c).val`); the torus is `(ℤ/q³ℤ)³` (integer scale `q³`), distances are `Z3NetF.torusDist2`
(squared toroidal distance) and `Z3NetF.cres`.

* `IsHeight q φ`, `colPt q φ`: a **column point set** (the text before `def:col`): one point in
  each cell `n`, at `X(n) = q² n + φ([n]) 𝟏` with heights `0 ≤ φ < q²` constant on the columns
  `[n] = n + ⟨𝟏⟩` (`φ(n + 𝟏) = φ(n)`).
* `colStep q φ i n = φ([n + e_i]) - φ([n])` (`Δ_i([n])` of `thm:colmin`).
* `colGap q φ = min_{i,[n]} dist(3Δ_i([n]), 2q² + 3q²ℤ)`: three times the `g` of `thm:colmin`
  (`3 g = dist(3Δ, 2q² + 3q²ℤ)` since `g = dist(Δ, ⅔q² + q²ℤ)`); the minimum is over all cells.
* `colA q w = (q𝟏 + w)/3`, `colGenW q w ℓ`: the digital column net with the digits `n_c`, `a·n`,
  `ℓ·n` in every coordinate (`lem:drift`); `colH`, `colJ`, `colPhi`: its shared digits `a·n`,
  `ℓ·n` and heights `φ = q (a·n) + ℓ·n`.
* `wCol q`, `ellCol`, `colGen q`: the column net `𝒞_q` of `def:col` (`w = (-2,1,1)` for
  `q ≡ 2`, `w = (-1,-1,2)` for `q ≡ 1 (mod 3)`, `ℓ = (-1,1,0)`).
* `tauCol q`, `DCol q`, `cCol q`: `τ`, the closest difference `D` and the constant
  `δN^{1/3} = √((2q⁴ + τ²)/3)/q²` of `thm:col`(2).
* `excess3 q Δ`: three times the excess `e = x - ⅓q²` of a step value `Δ` (`sec:drift`), `x` the
  representative of `Δ` modulo `q²` in `(-⅙q², ⅚q²]`.
-/

namespace Z3NetC

open Z3NetF Finset Matrix

/-! ## Column point sets (`sec:m3`) -/

/-- Heights of a **column point set**: `φ(n) < q²` and `φ` is constant on the columns
`[n] = n + ⟨𝟏⟩` (`φ(n + 𝟏) = φ(n)`), i.e. `φ` is a function `T → {0, …, q²-1}`,
`T = (ℤ/qℤ)³/⟨𝟏⟩`. -/
def IsHeight (q : ℕ) (φ : (Fin 3 → ZMod q) → ℕ) : Prop :=
  (∀ n, φ n < q ^ 2) ∧ ∀ n, φ (n + 1) = φ n

/-- The point `X(n) = q² n + φ([n]) 𝟏` of the cell `n` of a column point set, at integer scale
`q³`. -/
def colPt (q : ℕ) (φ : (Fin 3 → ZMod q) → ℕ) (n : Fin 3 → ZMod q) : Fin 3 → ℕ :=
  fun c => q ^ 2 * (n c).val + φ n

/-- The step value `Δ_i([n]) = φ([n + e_i]) - φ([n])` of `thm:colmin`. -/
def colStep (q : ℕ) (φ : (Fin 3 → ZMod q) → ℕ) (i : Fin 3) (n : Fin 3 → ZMod q) : ℤ :=
  (φ (n + Pi.single i 1) : ℤ) - φ n

/-- `3 g` of `thm:colmin`: the least distance of `3 Δ_i([n])` from `2q² + 3q²ℤ`, over all
directions `i` and all cells `n` (`g = min dist(Δ_i([n]), ⅔q² + q²ℤ)`). -/
def colGap (q : ℕ) [NeZero q] (φ : (Fin 3 → ZMod q) → ℕ) : ℕ :=
  (univ : Finset (Fin 3 × (Fin 3 → ZMod q))).inf' univ_nonempty fun x =>
    cres (3 * q ^ 2) (3 * colStep q φ x.1 x.2 - 2 * q ^ 2)

/-! ## Digital column nets (`def:col`, `lem:drift`) -/

/-- `a = (q𝟏 + w)/3` (an integer vector when `w_c ≡ -q (mod 3)`). -/
def colA (q : ℕ) (w : Fin 3 → ℤ) (c : Fin 3) : ℤ := ((q : ℤ) + w c) / 3

/-- The digital column net over `ℤ/qℤ` whose coordinates all have the digits `n_c`, `a·n`, `ℓ·n`:
generator matrix of coordinate `c` with the rows `e_c`, `a = (q𝟏 + w)/3`, `ℓ`. -/
def colGenW (q : ℕ) (w ℓ : Fin 3 → ℤ) (c : Fin 3) : Matrix (Fin 3) (Fin 3) (ZMod q) :=
  Matrix.of ![Pi.single c 1, fun d => ((colA q w d : ℤ) : ZMod q), fun d => ((ℓ d : ℤ) : ZMod q)]

/-- The shared second digit `h(n) = a·n` of a digital column net. -/
def colH (q : ℕ) (w : Fin 3 → ℤ) (n : Fin 3 → ZMod q) : ZMod q :=
  ∑ d, ((colA q w d : ℤ) : ZMod q) * n d

/-- The shared third digit `j(n) = ℓ·n` of a digital column net. -/
def colJ (q : ℕ) (ℓ : Fin 3 → ℤ) (n : Fin 3 → ZMod q) : ZMod q :=
  ∑ d, ((ℓ d : ℤ) : ZMod q) * n d

/-- The heights `φ = q h + j` of a digital column net. -/
def colPhi (q : ℕ) (w ℓ : Fin 3 → ℤ) (n : Fin 3 → ZMod q) : ℕ :=
  q * (colH q w n).val + (colJ q ℓ n).val

/-- `w` of `def:col`: `(-2, 1, 1)` if `q ≡ 2 (mod 3)`, `(-1, -1, 2)` otherwise (`q ≡ 1`). -/
def wCol (q : ℕ) : Fin 3 → ℤ := if q % 3 = 2 then ![-2, 1, 1] else ![-1, -1, 2]

/-- `ℓ = (-1, 1, 0)` of `def:col`. -/
def ellCol : Fin 3 → ℤ := ![-1, 1, 0]

/-- **`def:col`**: the generator matrices of the column net `𝒞_q`, rows `e_c`, `a`, `ℓ`. -/
def colGen (q : ℕ) : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod q) := colGenW q (wCol q) ellCol

/-- `τ` of `thm:col`(2): `q² - q - 3` if `q ≡ 2 (mod 3)`, `q² - 2q` otherwise (`q ≡ 1`). -/
def tauCol (q : ℕ) : ℤ := if q % 3 = 2 then (q : ℤ) ^ 2 - q - 3 else (q : ℤ) ^ 2 - 2 * q

/-- The closest difference `D` of `thm:col`(2):
`⅓(-(2q²-q-3), q²+q+3, -(2q²-q-3))` if `q ≡ 2`, `⅓(-(2q²-2q), -(2q²-2q), q²+2q)` otherwise. -/
def DCol (q : ℕ) : Fin 3 → ℤ :=
  if q % 3 = 2 then
    ![-((2 * (q : ℤ) ^ 2 - q - 3) / 3), ((q : ℤ) ^ 2 + q + 3) / 3, -((2 * (q : ℤ) ^ 2 - q - 3) / 3)]
  else ![-((2 * (q : ℤ) ^ 2 - 2 * q) / 3), -((2 * (q : ℤ) ^ 2 - 2 * q) / 3), ((q : ℤ) ^ 2 + 2 * q) / 3]

/-- `δN^{1/3}` of `𝒞_q` (`thm:col`(2)): `√((2q⁴ + τ²)/3)/q²`. -/
noncomputable def cCol (q : ℕ) : ℝ :=
  Real.sqrt ((2 * (q : ℝ) ^ 4 + (tauCol q : ℝ) ^ 2) / 3) / (q : ℝ) ^ 2

/-- Three times the **excess** of a step value `Δ` (`sec:drift`): `3x - q²`, where `x` is the
representative of `Δ` modulo `q²` in `(-⅙q², ⅚q²]`. -/
def excess3 (q : ℕ) (Δ : ℤ) : ℤ :=
  3 * (if 6 * (Δ % ((q : ℤ) ^ 2)) ≤ 5 * (q : ℤ) ^ 2 then Δ % ((q : ℤ) ^ 2)
    else Δ % ((q : ℤ) ^ 2) - (q : ℤ) ^ 2) - (q : ℤ) ^ 2

end Z3NetC

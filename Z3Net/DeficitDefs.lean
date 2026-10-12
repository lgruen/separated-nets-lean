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
# Definitions: the first-order deficit (`def:K`), `Q_D` (`prop:Dprime`), one-level designs (`prop:k1`)

V14 stage S2. The configurations, `σ`, `b_i`, the backward coordinates and the relaxation value
`LBval` of `lem:Ss` are those of `Z3Net/FDefs.lean` (`cfgs`, `sigma`, `bval`, `bwd`, `LBval`).

* `jit e i`: the jitter indicator of `lem:Ss` (`0` iff only axis `i` moves), as in `bval`.
* `cost F L e j`, `Kdef F L`, `Sdef F L`: `def:K`. A configuration is an element of
  `cfgs s L`: a step `e ∈ {-1,0,1}^s \ {0}` with carry classes `j_d ∈ {0, …, L-1}` (given on every
  axis; `σ` does not depend on the classes of the axes that do not move). The cost is
  `|σ_b| + jit_b` if exactly one moving coordinate `b` is backward, `0` if at least two are,
  and `⊤` (`+∞`) if none is; `K(F)` is the maximum cost (in `WithTop ℕ`), `S(F)` the maximum of
  `|σ_i|`.
* `QD K S = max(S + 1, ⌈(√2 (S+1) - K)/(√2 - 1)⌉)` (`prop:Dprime`).
* `layer1 F₀`: the one-level design `(F₀)` of `prop:k1` (`F₀` at level `0`, zero beyond).
* `k1Frame4`, `k1Frame5`, `k1Frame6`, `k1Free5`, `k1Free6a`, `k1Free6b`: the level-0 layers of
  `tab:practical` as printed in `app:designs` ("The layers of Table `tab:practical`"); `k1Places6`,
  `k1Lam6`, `k1Mu6`: the places `∞, 0, 1, 2, 3, 4` and the searched scalars `λ'`, `μ` of the
  `s = 6` frame layer (`prop:k1designs`(1)).
-/

namespace Z3NetF

open Finset

/-- The jitter indicator `jit_i` of `lem:Ss`: `0` if the step is `e = ±e_i` (only axis `i`
moves), `1` otherwise (the same rule as in `bval`). -/
def jit {s : ℕ} (e : Fin s → ℤ) (i : Fin s) : ℕ :=
  if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then 0 else 1

/-- **`def:K`**, the cost of a configuration `(e, j)` of the design `F` with `L` levels:
`|σ_b| + jit_b` if exactly one moving coordinate `b` is backward (`e_b σ_b ≤ 0`), `0` if at least
two are, and `⊤` (`+∞`) if none is. -/
def cost {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (e : Fin s → ℤ) (j : Fin s → ℕ) :
    WithTop ℕ :=
  if (bwd F L e j).card = 0 then ⊤
  else if (bwd F L e j).card = 1 then
    ((∑ b ∈ bwd F L e j, ((sigma F L e j b).natAbs + jit e b) : ℕ) : WithTop ℕ)
  else 0

/-- **`def:K`**: the first-order deficit `K(F)`, the maximum of the cost over all configurations
`(e, j)`, `e ∈ {-1,0,1}^s \ {0}`, carry classes `j_d ∈ {0, …, L-1}` (`⊤` if some configuration has
no backward coordinate). -/
def Kdef {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) : WithTop ℕ :=
  (cfgs s L).sup fun ej => cost F L ej.1 ej.2

/-- **`def:K`**: `S(F)`, the maximum of `|σ_i|` over all configurations `(e, j)` and all `i`. -/
def Sdef {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) : ℕ :=
  (cfgs s L).sup fun ej => univ.sup fun i => (sigma F L ej.1 ej.2 i).natAbs

/-- `Q_D` of `prop:Dprime`: `max(S + 1, ⌈(√2 (S + 1) - K)/(√2 - 1)⌉)` (the ceiling taken in `ℕ`;
this does not change the maximum, since `S + 1 ≥ 1`). -/
noncomputable def QD (K S : ℕ) : ℕ :=
  max (S + 1) ⌈(Real.sqrt 2 * ((S : ℝ) + 1) - K) / (Real.sqrt 2 - 1)⌉₊

/-- The one-level design `(F₀)` of `prop:k1`: `F₀` at level `0` and `0` at the deeper levels. -/
def layer1 {s : ℕ} (F₀ : Fin s → Fin s → ℤ) : ℕ → Fin s → Fin s → ℤ :=
  fun n => if n = 0 then F₀ else 0

/-! ## The layers of `tab:practical` (`app:designs`; `prop:k1designs`) -/

/-- The `s = 4` frame layer of `tab:practical` (the off-diagonal part of `U*_4`, diagonal chosen for
`k = 1`), as printed in `app:designs`. -/
def k1Frame4 : Fin 4 → Fin 4 → ℤ :=
  ![![-1, 2, 1, 2], ![1, -1, -1, -1], ![1, 2, -2, -2], ![1, 1, 1, -2]]

/-- The `s = 5` frame layer of `tab:practical` (the off-diagonal part of the `s = 5` design of
`tab:Kdesigns`, diagonal chosen for `k = 1`), as printed in `app:designs`. -/
def k1Frame5 : Fin 5 → Fin 5 → ℤ :=
  ![![-3, -3, 1, -1, 3], ![-1, -3, -2, 1, -2], ![-1, -6, -3, 2, -3], ![-1, -3, 2, -3, -6],
    ![-1, -2, 1, -2, -3]]

/-- The `s = 6` frame layer of `tab:practical` (searched scalars), as printed in `app:designs`. -/
def k1Frame6 : Fin 6 → Fin 6 → ℤ :=
  ![![-6, 18, 3, 3, 9, 6], ![1, -4, -2, -1, -2, -1], ![-3, -36, -6, 6, 9, 4],
    ![-1, -6, -2, -6, 6, 2], ![1, 4, 1, 2, -4, -4], ![-3, -9, -2, -3, -18, -3]]

/-- The places `∞, 0, 1, 2, 3, 4` of the `s = 6` frame layer (coordinate `0` is read at `∞`; its
entry is not used). -/
def k1Places6 : Fin 6 → ℚ := ![0, 0, 1, 2, 3, 4]

/-- The row scalars `λ' = (1, 2/3, -2, -2/3, 2/3, -2)` of the `s = 6` frame layer. -/
def k1Lam6 : Fin 6 → ℚ := ![1, 2 / 3, -2, -2 / 3, 2 / 3, -2]

/-- The column scalars `μ = (3/2, 18, 3, 3, 9, 6)` of the `s = 6` frame layer. -/
def k1Mu6 : Fin 6 → ℚ := ![3 / 2, 18, 3, 3, 9, 6]

/-- The free `s = 5` layer of `tab:practical` (`K₁ = 2`), as printed in `app:designs`. -/
def k1Free5 : Fin 5 → Fin 5 → ℤ :=
  ![![-2, 1, -1, -2, -1], ![-1, -2, -2, 2, -1], ![-1, 1, -1, -1, 2], ![-2, 1, -2, -2, 1],
    ![-1, -2, 1, 1, -2]]

/-- The first free `s = 6` layer of `tab:practical` (`K₁ = 3`), as printed in `app:designs`. -/
def k1Free6a : Fin 6 → Fin 6 → ℤ :=
  ![![-3, -3, 2, -1, 2, 1], ![1, -3, 2, 1, 3, -2], ![1, -2, -3, 3, -1, -1],
    ![2, 3, 1, -2, -1, 1], ![-3, -2, 1, 1, -3, 2], ![-1, -1, 3, 2, 2, -3]]

/-- The second free `s = 6` layer of `tab:practical` (`K₁ = 5`), as printed in `app:designs`. -/
def k1Free6b : Fin 6 → Fin 6 → ℤ :=
  ![![-4, 1, 3, -1, 2, 4], ![-2, -4, 1, -1, 1, 3], ![-4, -2, -4, 4, 1, -2],
    ![-2, 4, -2, -4, -4, -2], ![1, -3, 3, 1, -5, 2], ![-1, 4, 4, -2, 1, -5]]

end Z3NetF

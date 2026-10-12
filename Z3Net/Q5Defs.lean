/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.HLDefs

@[expose] public section

/-!
# V14 stage S11′: definitions for the `s = 5` layer `𝒬*`, `lem:R2` and `thm:D`

* `prop:half5`: the matrices `2F₀*` (`F2star`), `D₁`, `D₂`, `D₃` and the net `𝒬*_p` (`Qstar`), the graph form
  `halfPhi` of `prop:Hk` at `k = 1` with these rows (coordinate `c` of the point with index `n` has the digits
  `n_c`, `(F₀* n)_c`, `(D₁ n)_c`, `(D₂ n)_c`, `(D₃ n)_c`, with `½ ≡ (p+1)/2`).
* `lem:R2`: the second offset rows (`Row1Design`), `2b_c` (`bR2`) and `LB₂(p)` (`LB2R`).
* `thm:D` (doubled, `F2 = 2F₀`): the binding steps (`bind5`), `2 dr(E)` (`drift2E`), `2 dr(F₀)` (`drift2`) and
  the condition (B2) (`B2D`); (MIN) is `DisjMinors` of `Z3Net/HLDefs.lean`.
-/

namespace Z3NetHL

open Finset

/-! ## `prop:half5` -/

/-- `2F₀*` of `prop:half5`. -/
def F2star : Fin 5 → Fin 5 → ℤ :=
  ![![-3, -3, -3, -1, -1],
    ![3, -3, -1, -3, 1],
    ![3, 1, -3, 1, -1],
    ![1, 3, -1, -3, -1],
    ![1, -1, 1, 1, -1]]

/-- `D₁` of `prop:half5`. -/
def D1star : Fin 5 → Fin 5 → ℤ :=
  ![![-2, 0, -1, -1, 1],
    ![0, -1, -1, -1, -1],
    ![2, -1, -3, 1, 0],
    ![-1, 2, -1, -2, 0],
    ![-1, -1, 3, 2, -5]]

/-- `D₂` of `prop:half5`. -/
def D2star : Fin 5 → Fin 5 → ℤ :=
  ![![0, -1, -1, 0, 0],
    ![-1, 0, 0, 0, -1],
    ![-1, -1, 0, 0, 0],
    ![-1, -1, 0, 0, 0],
    ![-1, -1, 0, 0, 0]]

/-- `D₃` of `prop:half5`. -/
def D3star : Fin 5 → Fin 5 → ℤ :=
  ![![0, -1, 0, 0, 0],
    ![-1, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0]]

/-- The deeper rows of `𝒬*`: row `r = 1, 2, 3` of coordinate `c` is row `c` of `D_r`. -/
def Dstar (c : Fin 5) (r : ℕ) (d : Fin 5) : ℤ :=
  if r = 1 then D1star c d else if r = 2 then D2star c d else if r = 3 then D3star c d else 0

/-- **`𝒬*_p`** (`prop:half5`): the digital net over `ℤ/pℤ` whose point with index `n` has, in coordinate `c`,
the digits `n_c`, `(F₀* n)_c`, `(D₁ n)_c`, `(D₂ n)_c`, `(D₃ n)_c` (`½ ≡ (p+1)/2`); integer point in
`[0, p⁵)⁵`. -/
def Qstar (p : ℕ) : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ :=
  GFpoint 5 p 1 (halfPhi 5 p F2star Dstar)

/-! ## `lem:R2` -/

/-- `(A E)_c = ∑_d A_cd E_d`. -/
def dotR {s : ℕ} (A : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) : ℤ :=
  ∑ d, A c d * E d

/-- **The second offset rows** (`lem:R2`): row `1` of every block `Φ_cd` (the second offset digit of
coordinate `c`, depths `(1, …, 1)`) is the integer `D₁[c][d]`. -/
def Row1Design (s q : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (D1 : Fin s → Fin s → ℤ) : Prop :=
  ∀ (c d : Fin s) (r : Fin (s * 1 - 1)), (r : ℕ) = 1 → Φ c d r 0 = (D1 c d : ZMod q)

/-- One option of `lem:R2`, doubled: `max(0, |2q²E_c + q·(2t) + 2u| − 2)`. -/
def oR2 (q : ℕ) (e t2 u : ℤ) : ℤ :=
  max 0 (|2 * (q : ℤ) ^ 2 * e + q * t2 + 2 * u| - 2)

/-- **`2b_c` of `lem:R2`.** With `b = 2β_c = (2F₀ E)_c` and `v = (D₁ E)_c`: the first-digit options
`2t ∈ {b + q, b − q}` if `σ_E = ∑ E` is odd and `2t ∈ {b, b − 2q sgn b}` if it is even (those of `prop:Hk`
with `σ_c = β_c`; a single option if `β_c = 0`), the second-digit options `u ∈ {v, v − q sgn v}` (a single
option if `v = 0`), and `2b_c = min_{t,u} max(0, |2q²E_c + q·2t + 2u| − 2)`. -/
def bR2 {s : ℕ} (q : ℕ) (F2 D1 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) : ℤ :=
  if (∑ d, E d) % 2 = 1 then
    min (min (oR2 q (E c) (dotR F2 E c + q) (dotR D1 E c))
        (oR2 q (E c) (dotR F2 E c + q) (dotR D1 E c - q * Int.sign (dotR D1 E c))))
      (min (oR2 q (E c) (dotR F2 E c - q) (dotR D1 E c))
        (oR2 q (E c) (dotR F2 E c - q) (dotR D1 E c - q * Int.sign (dotR D1 E c))))
  else
    min (min (oR2 q (E c) (dotR F2 E c) (dotR D1 E c))
        (oR2 q (E c) (dotR F2 E c) (dotR D1 E c - q * Int.sign (dotR D1 E c))))
      (min (oR2 q (E c) (dotR F2 E c - 2 * q * Int.sign (dotR F2 E c)) (dotR D1 E c))
        (oR2 q (E c) (dotR F2 E c - 2 * q * Int.sign (dotR F2 E c))
          (dotR D1 E c - q * Int.sign (dotR D1 E c))))

/-- **`LB₂(p)` of `lem:R2`**: `min(2, min_{0 ≠ E ∈ {-2,…,2}^s} |b|/q²)`, with `|b| = (∑_c (2b_c)²)^(1/2) / 2`. -/
noncomputable def LB2R {s : ℕ} (q : ℕ) (F2 D1 : Fin s → Fin s → ℤ) : ℝ :=
  min 2 (⨅ E : halfSteps s,
    Real.sqrt (∑ c, ((bR2 q F2 D1 (E : Fin s → ℤ) c : ℤ) : ℝ) ^ 2) / (2 * (q : ℝ) ^ 2))

/-! ## `thm:D` (the least drift), doubled: `F2 = 2F₀` -/

/-- The binding steps of `sec:halfms`: `E ∈ {-1, 0, 1}⁵` with `σ_E = ∑ E` odd. -/
def bind5 : Finset (Fin 5 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 5 => Finset.Icc (-1 : ℤ) 1).filter fun E => (∑ d, E d) % 2 = 1

theorem bind5_nonempty : bind5.Nonempty :=
  ⟨![1, 0, 0, 0, 0], by decide⟩

/-- `2 dr_c(E)`: `|2β_c|` if `E_c = 0`, `−E_c · 2β_c` otherwise (`β = F₀ E`). -/
def drc2 (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) : ℤ :=
  if E c = 0 then |dotR F2 E c| else -(E c * dotR F2 E c)

/-- `2 dr(E) = ∑_c 2 dr_c(E)`. -/
def drift2E (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) : ℤ :=
  ∑ c, drc2 F2 E c

/-- **`2 dr(F₀)`**: the maximum of `2 dr(E)` over the binding steps. -/
def drift2 (F2 : Fin 5 → Fin 5 → ℤ) : ℤ :=
  bind5.sup' bind5_nonempty (drift2E F2)

/-- **(B2)**, doubled: `α_c = −F₀[c][c] ≥ m_c = max_{d ≠ c} |F₀[c][d]|` for every `c`. -/
def B2D (F2 : Fin 5 → Fin 5 → ℤ) : Prop :=
  ∀ c d, d ≠ c → |F2 c d| ≤ -F2 c c

end Z3NetHL

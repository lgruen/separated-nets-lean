/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib

@[expose] public section

/-!
# V14 stage S15′: definitions for `prop:k1designs`(1), the `s = 5` frame layer

The geometric layer of the `s = 5` design of `tab:Kdesigns` as printed in `app:designs`, its places and row scalars, and
the column scalars of the frame layer (`Z3Net/K1ComplMain.lean`, `frame5_cauchy`).
-/

namespace Z3NetF

/-- The geometric layer `F₀` of the `s = 5` design of `tab:Kdesigns`, as printed in `app:designs` (places
`∞, 0, 1, 2, 3`). -/
def kdes5F0 : Fin 5 → Fin 5 → ℤ :=
  ![![-4, -3, 1, -1, 3], ![-1, -5, -2, 1, -2], ![-1, -6, -5, 2, -3], ![-1, -3, 2, -5, -6],
    ![-1, -2, 1, -2, -5]]

/-- The places `∞, 0, 1, 2, 3` of the `s = 5` design (coordinate `0` is read at `∞`; its entry is not used). -/
def kdes5Places : Fin 5 → ℚ := ![0, 0, 1, 2, 3]

/-- The row scalars `λ' = (1/2, 1, 1, 1, 1)` of the `s = 5` design of `tab:Kdesigns`. -/
def kdes5Lam : Fin 5 → ℚ := ![1 / 2, 1, 1, 1, 1]

/-- Column scalars `μ = (-1, -6, 2, -2, 6)` of the `s = 5` frame layer (computed; not printed in the paper). -/
def kdes5Mu : Fin 5 → ℚ := ![-1, -6, 2, -2, 6]

end Z3NetF

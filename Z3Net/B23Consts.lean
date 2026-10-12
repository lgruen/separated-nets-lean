/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23Fam

@[expose] public section

/-! # The every-shift certificates `v°_L ≥ v` of `thm:base23` (statement side; V14 stage S14′) -/

namespace Z3NetB23

/-- The certified lower bounds `v` for `v°_L` at the certificate levels: `168, 110, 3` (`b = 2`) and `8, 86, 9`
(`b = 3`) for `r = 0, 1, 2` (the research notes). -/
def b23Vcert : ℕ → ℕ → ℕ
  | 2, 0 => 168
  | 2, 1 => 110
  | 2, 2 => 3
  | 3, 0 => 8
  | 3, 1 => 86
  | 3, 2 => 9
  | _, _ => 0

end Z3NetB23

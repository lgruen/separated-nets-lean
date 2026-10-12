/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.Q5Defs

@[expose] public section

/-!
# V14 stage S11′: `thm:D`, the enumeration of the normalized layers (checker)

The normalized layers of the non-skew case of `thm:D` (doubled, `F2 = 2F₀`): row `4` is `(1, 1, 1, 1, −1)`
(the light row), the heavy rows `c < 4` have diagonal `−3` and off-diagonal entries in `{±1, ±3}`, at least one
`±3`. The checker `chkTop r₀` enumerates, for a fixed row `0`, the rows `1, 2, 3` (each from its candidate list
`cand c`: heavy, and the three minors with row `4` nonzero), keeping only those whose disjoint `2 × 2` minors with
the rows already chosen are nonzero (`pairOK`, forward checking), and for every admissible layer it finds a binding
step of the witness list `W` with `2 dr(E) ≥ 17` (`leaf`). The kernel runs (`decide +kernel`, one theorem per row
`0`) are in `Z3Net/TDCert0.lean` … `TDCert5.lean`; the soundness of the checker is `Z3Net/TDEnum.lean`.
-/

namespace Z3NetHL.Proofs.TD

/-- A row of a layer, as five integers (kernel friendly). -/
structure R5 where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a4 : ℤ
deriving DecidableEq

/-- Entry `i` of a row (`i ≥ 4` gives entry `4`). -/
def R5.g (r : R5) : ℕ → ℤ
  | 0 => r.a0
  | 1 => r.a1
  | 2 => r.a2
  | 3 => r.a3
  | _ => r.a4

/-- The row as a vector. -/
def R5.f (r : R5) : Fin 5 → ℤ := ![r.a0, r.a1, r.a2, r.a3, r.a4]

/-- A vector as a row. -/
def toR5 (v : Fin 5 → ℤ) : R5 := ⟨v 0, v 1, v 2, v 3, v 4⟩

/-- The off-diagonal values of a heavy row. -/
def vals : List ℤ := [-3, -1, 1, 3]

/-- The heavy row `c` with diagonal `−3` and the off-diagonal entries `x, y, z, w` (in column order). -/
def mkRow (c : ℕ) (x y z w : ℤ) : R5 :=
  match c with
  | 0 => ⟨-3, x, y, z, w⟩
  | 1 => ⟨x, -3, y, z, w⟩
  | 2 => ⟨x, y, -3, z, w⟩
  | _ => ⟨x, y, z, -3, w⟩

/-- The normalized light row `4`. -/
def row4 : R5 := ⟨1, 1, 1, 1, -1⟩

/-- The three `2 × 2` minors of two rows on three columns are nonzero. -/
def m3 (x0 x1 x2 y0 y1 y2 : ℤ) : Bool :=
  x0 * y1 != x1 * y0 && x0 * y2 != x2 * y0 && x1 * y2 != x2 * y1

/-- The disjoint `2 × 2` minors of the rows `a < b`: the three columns outside `{a, b}`. -/
def pairOK (a b : ℕ) (ra rb : R5) : Bool :=
  match a, b with
  | 0, 1 => m3 ra.a2 ra.a3 ra.a4 rb.a2 rb.a3 rb.a4
  | 0, 2 => m3 ra.a1 ra.a3 ra.a4 rb.a1 rb.a3 rb.a4
  | 0, 3 => m3 ra.a1 ra.a2 ra.a4 rb.a1 rb.a2 rb.a4
  | 1, 2 => m3 ra.a0 ra.a3 ra.a4 rb.a0 rb.a3 rb.a4
  | 1, 3 => m3 ra.a0 ra.a2 ra.a4 rb.a0 rb.a2 rb.a4
  | 2, 3 => m3 ra.a0 ra.a1 ra.a4 rb.a0 rb.a1 rb.a4
  | 0, 4 => m3 ra.a1 ra.a2 ra.a3 rb.a1 rb.a2 rb.a3
  | 1, 4 => m3 ra.a0 ra.a2 ra.a3 rb.a0 rb.a2 rb.a3
  | 2, 4 => m3 ra.a0 ra.a1 ra.a3 rb.a0 rb.a1 rb.a3
  | 3, 4 => m3 ra.a0 ra.a1 ra.a2 rb.a0 rb.a1 rb.a2
  | _, _ => false

/-- Some off-diagonal entry of the heavy row `c` is `±3`. -/
def heavyR (c : ℕ) (r : R5) : Bool :=
  match c with
  | 0 => r.a1.natAbs == 3 || r.a2.natAbs == 3 || r.a3.natAbs == 3 || r.a4.natAbs == 3
  | 1 => r.a0.natAbs == 3 || r.a2.natAbs == 3 || r.a3.natAbs == 3 || r.a4.natAbs == 3
  | 2 => r.a0.natAbs == 3 || r.a1.natAbs == 3 || r.a3.natAbs == 3 || r.a4.natAbs == 3
  | _ => r.a0.natAbs == 3 || r.a1.natAbs == 3 || r.a2.natAbs == 3 || r.a4.natAbs == 3

/-- All `4⁴` heavy-row shapes at position `c`. -/
def allRows (c : ℕ) : List R5 :=
  vals.flatMap fun x => vals.flatMap fun y => vals.flatMap fun z => vals.map fun w => mkRow c x y z w

/-- The candidates for the heavy row `c < 4`: heavy, and the minors with row `4` nonzero. -/
def cand (c : ℕ) : List R5 :=
  (allRows c).filter fun r => heavyR c r && pairOK c 4 r row4

/-- `(r · E)`. -/
def dot5 (r E : R5) : ℤ := r.a0 * E.a0 + r.a1 * E.a1 + r.a2 * E.a2 + r.a3 * E.a3 + r.a4 * E.a4

/-- `2 dr_c(E)` for the row `r` at position `c`. -/
def drc (r : R5) (c : ℕ) (E : R5) : ℤ :=
  if E.g c = 0 then |dot5 r E| else -(E.g c * dot5 r E)

/-- The witness steps (binding). -/
def W : List R5 :=
  [⟨1, 1, 1, 1, -1⟩, ⟨1, 1, -1, -1, -1⟩, ⟨1, -1, 1, -1, -1⟩, ⟨1, -1, -1, 1, -1⟩, ⟨-1, 1, 0, 0, -1⟩,
   ⟨-1, -1, 1, 1, -1⟩, ⟨-1, -1, 0, -1, 0⟩, ⟨-1, -1, -1, 0, 0⟩, ⟨-1, 0, 1, 0, -1⟩, ⟨0, 1, -1, 0, -1⟩,
   ⟨1, -1, 0, 0, -1⟩, ⟨-1, 0, 0, 1, -1⟩, ⟨1, 0, -1, 0, -1⟩, ⟨0, -1, 1, 0, -1⟩, ⟨0, 1, 0, -1, -1⟩,
   ⟨0, -1, 0, 1, -1⟩, ⟨1, 1, 0, -1, 0⟩, ⟨1, 0, 0, -1, -1⟩]

/-- Some witness step has `2 dr(E) ≥ 17` for the layer with rows `r₀, r₁, r₂, r₃` and `row4`. -/
def leaf (r0 r1 r2 r3 : R5) : Bool :=
  W.any fun E => decide (17 ≤ drc r0 0 E + drc r1 1 E + drc r2 2 E + drc r3 3 E + drc row4 4 E)

/-- The enumeration below a fixed row `0`. -/
def chkTop (r0 : R5) : Bool :=
  ((cand 1).filter (pairOK 0 1 r0)).all fun r1 =>
    ((cand 2).filter fun r2 => pairOK 0 2 r0 r2 && pairOK 1 2 r1 r2).all fun r2 =>
      ((cand 3).filter fun r3 => pairOK 0 3 r0 r3 && pairOK 1 3 r1 r3 && pairOK 2 3 r2 r3).all
        fun r3 => leaf r0 r1 r2 r3

end Z3NetHL.Proofs.TD

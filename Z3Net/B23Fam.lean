/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/module
public import Z3Net.B23Nets

@[expose] public section

/-!
# Definitions: the nets of `thm:base23` (V14 stage S14′)

* `b23Lev b r k`: the level `M₀ + 3k` of the chain of the residue class `r` (`M₀ = b23SeedM b r`);
  `b23NL b r`: the number of lifts up to the certificate level `b23L b r`.
* `b23Cols`, `b23Gen b r k`: the generator matrices at level `b23Lev b r k`: the seed `(I, A_y, A_z)` of
  `tab:b23seeds` (`seedCols`, from the printed rows), then `k` lifts (`liftCols`, `def:lift`) with the parameters
  `b23Lifts b r`; `b23Shift b r k`: the explicit shift (that of the seed, embedded by the lifts).
* `IsB23Gen b m C`: `C` are the generator matrices of a net of `thm:base23` at level `m`: an explicit witness
  (`m` below the seed level of its class), a chain level up to the certificate level, or **any** continuation from a
  level `ℓ ≥ L` by a lift with admissible shifts vanishing on the first `⌊ℓ/2⌋` digits (`D_ℓ = ⌊ℓ/2⌋`).
-/

namespace Z3NetB23

/-- The chain level `M₀ + 3k`. -/
def b23Lev (b r k : ℕ) : ℕ := b23SeedM b r + 3 * k

/-- The number of lifts from the seed to the certificate level. -/
def b23NL (b r : ℕ) : ℕ := (b23L b r - b23SeedM b r) / 3

/-- Column codes of the chain level `k`. -/
def b23Cols (b r : ℕ) : ℕ → List (List ℕ)
  | 0 => seedCols b (b23SeedM b r) (b23RowsY b r) (b23RowsZ b r)
  | k + 1 => liftCols b (b23Lev b r k) (b23Cols b r k) ((b23Lifts b r).getD k ([], [])).1
      ((b23Lifts b r).getD k ([], [])).2

/-- Shift codes of the chain level `k` (the shift of the seed, embedded). -/
def b23Sh (b r : ℕ) : ℕ → List ℕ
  | 0 => b23Tau b r
  | k + 1 => liftShCode b (b23Sh b r k)

/-- **The generator matrices of the chain level `k`** of the residue class `r` (`thm:base23`). -/
def b23Gen (b r k : ℕ) : Fin 3 → Matrix (Fin (b23Lev b r k)) (Fin (b23Lev b r k)) (ZMod b) :=
  colMat b (b23Lev b r k) (b23Cols b r k)

/-- **The explicit shift of the chain level `k`** (part (1) of `thm:base23`). -/
def b23Shift (b r k : ℕ) : Fin 3 → Fin (b23Lev b r k) → ZMod b := shOf b (b23Lev b r k) (b23Sh b r k)

/-- **The nets of `thm:base23`**: `IsB23Gen b m C` says that `C` are the generator matrices of a net of the
theorem at level `m`: an explicit witness below the seed level of the class `m mod 3` (`b23Wit`), a level of the
fixed chain up to the certificate level, or a continuation by a lift from a level `ℓ ≥ L` of its class with
admissible shifts vanishing on the first `⌊ℓ/2⌋` digits. -/
inductive IsB23Gen (b : ℕ) : (m : ℕ) → (Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)) → Prop
  | wit (m : ℕ) (h1 : 1 ≤ m) (h2 : m < b23SeedM b (m % 3)) : IsB23Gen b m (colMat b m (b23Wit b m))
  | chain (r k : ℕ) (hr : r < 3) (hk : k ≤ b23NL b r) : IsB23Gen b (b23Lev b r k) (b23Gen b r k)
  | cont {ℓ : ℕ} {C : Fin 3 → Matrix (Fin ℓ) (Fin ℓ) (ZMod b)} (sA sB : Fin 3 → Fin ℓ → ZMod b) :
      IsB23Gen b ℓ C → b23L b (ℓ % 3) ≤ ℓ → Admissible C sA sB → VanishTop (ℓ / 2) sA → VanishTop (ℓ / 2) sB →
      IsB23Gen b (ℓ + 3) (liftGen C sA sB)

/-- The constants of `thm:base23`(3) (every digital shift) per residue class, times `10⁴` (`tab:base23`, column (3)
of the research notes, with the replacement witnesses for `b = 2`). -/
def b23Cnum : ℕ → ℕ → ℕ
  | 2, 0 => 4050
  | 2, 1 => 4129
  | 2, 2 => 1718
  | 3, 0 => 1047
  | 3, 1 => 1651
  | 3, 2 => 770
  | _, _ => 0

/-- **The constants of `thm:base23`(3)**: `.4050, .4129, .1718` (`b = 2`) and `.1047, .1651, .0770` (`b = 3`) for
`m ≡ 0, 1, 2 (mod 3)`. -/
noncomputable def b23C (b r : ℕ) : ℝ := (b23Cnum b r : ℝ) / 10000

end Z3NetB23

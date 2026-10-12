/-
Development copy (Solution side) of the second Challenge for the paper: Well-separated (0,3k,3)-nets in every base q ≥ 4: one linear scramble of the
Faure–Hammersley net (draft, revision 4, 2026-10-07) — Remark on m ≡ 1, 2 (mod 3)
(`core.tex`, the `m ≡ 1, 2` paragraph of the Remarks and Appendix `app:verify`) and the
supporting notes the research notes.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
The centred residue `cres` is adapted from Lennart Rudolph's Palomar formalization of the
even-order Grünschloß–Keller nets (github.com/lennrt/palomar-formalizations, MIT licence).
-/
module
public import Z3Net.KNDefs
public import Z3Net.KNSepMain
public import Z3Net.KNBnet2
public import Z3Net.KNBnet1
public import Z3Net.KNBsep
public import Z3Net.KNNetMain

@[expose] public section

/-!
# Main statements of the second entry (same statements as `ChallengeKN.lean`)

Each theorem is closed by the identically-typed `Z3NetKN.Proofs.*` theorem of its proof module
(`KNNetMain`, `KNSepMain`, `KNBnet1`, `KNBnet2`, `KNBsep`).
-/

namespace Z3NetKN

/-- **`m ≡ 1`, net part.** For each design of `table1` and every `k ≥ 3` there is a
`(0,3k+1,3)`-net over `𝔽_p` in graph form with exactly these rows. -/
theorem KN1_net (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table1) (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKN 1 p k R C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) :=
  Proofs.KN1_net p T R hmem k hk

/-- **`m ≡ 1`, separation.** For each design `(p, T_p, R)` of `table1`, every `k ≥ 3`, every net
`C` with these rows and distinct indices `v ≠ w`, with `N = p^(3k+1)`:
`T_p · p^(4k-2) ≤ N² δ²`, i.e. `δ ≥ √T_p · p^(-5/3) · N^(-1/3)`. -/
theorem KN1_sep (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table1) (k : ℕ) (hk : 3 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (hC : IsKN 1 p k R C)
    (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    T * p ^ (4 * k - 2) ≤
      torusDist2 (p ^ (3 * k + 1)) (digPoint p (3 * k + 1) C v) (digPoint p (3 * k + 1) C w) :=
  Proofs.KN1_sep p T R hmem k hk C hC v w hvw

/-- **`m ≡ 2`, net part.** For each design of `table2` and every `k ≥ 2` there is a
`(0,3k+2,3)`-net over `𝔽_p` in graph form with exactly these rows. -/
theorem KN2_net (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table2) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p),
      IsKN 2 p k R C ∧ IsNet0 p (3 * k + 2) (digPoint p (3 * k + 2) C) :=
  Proofs.KN2_net p T R hmem k hk

/-- **`m ≡ 2`, separation.** For each design `(p, T_p, R)` of `table2`, every `k ≥ 2`, every net
`C` with these rows and `v ≠ w`, with `N = p^(3k+2)`: `T_p · p^(4k) ≤ N² δ²`,
i.e. `δ ≥ √T_p · p^(-4/3) · N^(-1/3)`. -/
theorem KN2_sep (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table2) (k : ℕ) (hk : 2 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p)) (hC : IsKN 2 p k R C)
    (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    T * p ^ (4 * k) ≤
      torusDist2 (p ^ (3 * k + 2)) (digPoint p (3 * k + 2) C v) (digPoint p (3 * k + 2) C w) :=
  Proofs.KN2_sep p T R hmem k hk C hC v w hvw

/-- **`m ≡ 2`, all primes, net part.** For every prime `p`, `k ≥ 1` and `ρ ≥ 1` with
`ρ(1 + ρ + ρ²) ≤ p` there is a `(0,3k+2,3)`-net over `𝔽_p` with skeleton rows `skB2 ρ`. -/
theorem B2_net (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 1 ≤ ρ)
    (hρp : ρ * (1 + ρ + ρ ^ 2) ≤ p) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p),
      IsKNskel 2 p k (skB2 ρ) C ∧ IsNet0 p (3 * k + 2) (digPoint p (3 * k + 2) C) :=
  Proofs.B2_net p k ρ hp hk hρ hρp

/-- **`m ≡ 2`, all primes, separation.** Same hypotheses; every net with skeleton rows
`skB2 ρ` has `(ρ - 1)² p^(4k+2) ≤ N² δ²` (`N = p^(3k+2)`), i.e.
`δ ≥ (ρ - 1) p^(-1/3) N^(-1/3)`. -/
theorem B2_sep (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 1 ≤ ρ)
    (hρp : ρ * (1 + ρ + ρ ^ 2) ≤ p)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p))
    (hC : IsKNskel 2 p k (skB2 ρ) C) (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    (ρ - 1) ^ 2 * p ^ (4 * k + 2) ≤
      torusDist2 (p ^ (3 * k + 2)) (digPoint p (3 * k + 2) C v) (digPoint p (3 * k + 2) C w) :=
  Proofs.B2_sep p k ρ hp hk hρ hρp C hC v w hvw

/-- **`m ≡ 1`, all primes, net part.** For every prime `p`, `k ≥ 1` and `ρ ≥ 2` with
`ρ²(ρ + 1) ≤ p` there is a `(0,3k+1,3)`-net over `𝔽_p` with skeleton rows `skB1 ρ`. -/
theorem B1_net (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 2 ≤ ρ)
    (hρp : ρ ^ 2 * (ρ + 1) ≤ p) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKNskel 1 p k (skB1 ρ) C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) :=
  Proofs.B1_net p k ρ hp hk hρ hρp

/-- **`m ≡ 1`, all primes, separation.** Same hypotheses; every net with skeleton rows
`skB1 ρ` has `(ρ² - 4)² p^(4k) ≤ N² δ²` (`N = p^(3k+1)`), i.e.
`δ ≥ (ρ² - 4) p^(-2/3) N^(-1/3)`. -/
theorem B1_sep (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 2 ≤ ρ)
    (hρp : ρ ^ 2 * (ρ + 1) ≤ p)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p))
    (hC : IsKNskel 1 p k (skB1 ρ) C) (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    (ρ ^ 2 - 4) ^ 2 * p ^ (4 * k) ≤
      torusDist2 (p ^ (3 * k + 1)) (digPoint p (3 * k + 1) C v) (digPoint p (3 * k + 1) C w) :=
  Proofs.B1_sep p k ρ hp hk hρ hρp C hC v w hvw

end Z3NetKN

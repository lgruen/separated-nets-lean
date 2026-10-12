/-
Development copy (Solution side) of Challenge4D. Note: Theorem 4D of the research notes (2026-10-07; independently audited in
the research notes): explicit well-separated digital `(0,4k,4)`-nets over `ℤ/qℤ` for every
odd `q`, built from design A (`witnesses/dim4_designs.json : hill_q11`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
The centred residue `cres` is adapted from Lennart Rudolph's Palomar formalization of the
even-order Grünschloß–Keller nets (github.com/lennrt/palomar-formalizations, MIT licence).
-/
module
public import Z3Net.D4Defs
public import Z3Net.D4Thm1
public import Z3Net.D4Sep
public import Z3Net.D4Cover
public import Z3Net.D4BoxMinor
public import Z3Net.D4DefN
public import Z3Net.D4Exp

@[expose] public section

/-!
# Main statements of the 4D entry (same statements as `Challenge4D.lean`)

Each theorem is closed by the identically typed `Z3NetD4.Proofs.*` theorem of its proof module.
-/

namespace Z3NetD4

open Matrix Finset

/-! ## Theorem 4D -/

/-- **Definition N, literally.** Over `ℚ` (entries in `ℤ[1/2]`), every off-diagonal block of the
Challenge net is `Φ'_cd = L_c Φ^F_cd U_d` with the raw frame graph form `Φ^F` (Mathlib inverse of
the frame's `(k,k,k,k)` box matrix), `L_c = diag(λ'_c Q_c^(-k), 1, …, 1)` and
`U_d = Q_d^k Toep(g_d) U'^(k)_d`; every `k ≥ 1`. -/
theorem D4_defN (k : ℕ) (hk : 1 ≤ k) (c d : Fin 4) (hcd : c ≠ d) (r : Fin (3 * k)) (l : Fin k) :
    D4Phi ℚ (1 / 2) k c d r l =
      (if (r : ℕ) = 0 then (lamRes c : ℚ) * (Qval c ^ k)⁻¹ else 1) * (frameGraph k c d * Ulit k d) r l :=
  Proofs.D4_defN k hk c d hcd r l

/-- **Proposition N** (normal form of the first offset row, every `k ≥ 1`): after the gauge
`λ_c = Q_c^(-k)`, `U_d = Q_d^k Toep(g_d)`, level `k-1-n` of row `0` of `Φ^F_cd` is
`w_cd y_cd^n`. -/
theorem D4_propN (k : ℕ) (hk : 1 ≤ k) (c d : Fin 4) (hcd : c ≠ d) (j : Fin k) :
    (Qval c ^ k)⁻¹ * (frameGraph k c d * ((Qval d ^ k) • toep k (gpoly k d)))
        ⟨0, Nat.mul_pos (Nat.succ_pos 2) hk⟩ j = wN c d * yN c d ^ (k - 1 - (j : ℕ)) :=
  Proofs.D4_propN k hk c d hcd j

/-- **Proposition G**, the defining relation of `α_n, β_n` (`n ≥ 3`): for every `c ≠ d`,
`v_n = α_n v_1 + β_n v_2` with `v_n = (w_cd y_cd^n)_c`. (In each column `d` two of the three `y_cd`
are nonzero and distinct, so this determines `α_n, β_n`.) -/
theorem D4_propG (c d : Fin 4) (hcd : c ≠ d) (n : ℕ) (hn : 3 ≤ n) :
    wN c d * yN c d ^ n =
      alpha (1 / 2 : ℚ) d n * (wN c d * yN c d) + beta (1 / 2 : ℚ) d n * (wN c d * yN c d ^ 2) :=
  Proofs.D4_propG c d hcd n hn

/-- **Theorem 4D(1), box minors.** Over `ℚ` (`h = 1/2`, i.e. the `ℤ[1/2]` matrices of
Definition N), every box minor of the generator matrices of `𝒫⁴_{k,·}` is `±2^j`, `j ∈ ℤ`,
for every `k ≥ 2`. -/
theorem D4_boxMinor (k : ℕ) (hk : 2 ≤ k) (d : Fin 4 → ℕ) (hd : d 0 + d 1 + d 2 + d 3 = 4 * k) :
    ∃ j : ℤ, (boxMatrix (graphGen k (D4Phi ℚ (1 / 2) k)) d).det = 2 ^ j ∨
      (boxMatrix (graphGen k (D4Phi ℚ (1 / 2) k)) d).det = -2 ^ j :=
  Proofs.D4_boxMinor k hk d hd

/-- **Theorem 4D(1).** For every odd `q` (composite allowed) and `k ≥ 2`, `𝒫⁴_{k,q}` is a
`(0,4k,4)`-net over `ℤ/qℤ`. (With `d = (k,k,k,k)` this is the one-point-per-cell statement of
Theorem 4D(2).) -/
theorem D4_net (q k : ℕ) (hq : Odd q) (hk : 2 ≤ k) : IsNet0 q (4 * k) (D4point q k) :=
  Proofs.D4_net q k hq hk

/-- **Theorem 4D(2), covering radius.** Every `x ∈ [0,1]⁴` has a point of `𝒫⁴_{k,q}` at Euclidean
distance at most `2 q^(-k) = 2 N^(-1/4)` (`N = q^(4k)`; every base `q ≥ 2`, the graph form puts
one point in every cell). -/
theorem D4_covering (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) (x : Fin 4 → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (4 * k) → ZMod q,
      ∑ c, (x c - (D4point q k v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2 ≤ 4 / ((q : ℝ) ^ k) ^ 2 :=
  Proofs.D4_covering q k hq hk x hx

/-- **Theorem 4D(3), exact integer form.** For odd `q ≥ 5`, `k ≥ 2` and distinct indices `v ≠ w`,
with `N = q^(4k)` and `D² = torusDist2 N X(v) X(w)` (the squared toroidal distance times `N²`):
`q² D² ≥ q^(6k) K4(q)`, i.e. `δ ≥ c₄(q) N^(-1/4)` with `c₄(q)² = K4(q)/q²`
(`= ((q-5)² + 4)/q²` for odd `q ≥ 9`, `1/25` for `q = 5`, `5/49` for `q = 7`). -/
theorem D4_sep (q k : ℕ) (hq : Odd q) (hq5 : 5 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (6 * k) * K4 q ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (4 * k)) (D4point q k v) (D4point q k w) : ℤ) :=
  Proofs.D4_sep q k hq hq5 hk v w hvw

/-- **Theorem 4D(3), real form.** The toroidal distance between any two distinct points of
`𝒫⁴_{k,q}` (points `X / N` in `[0,1)⁴`, `N = q^(4k)`) is at least `c₄(q) · N^(-1/4)`. -/
theorem D4_sep_real (q k : ℕ) (hq : Odd q) (hq5 : 5 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    c4 q * ((q : ℝ) ^ (4 * k)) ^ (-(1 / 4 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (4 * k)) ((D4point q k v c : ℤ) - (D4point q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (4 * k)) ^ 2) :=
  Proofs.D4_sep_real q k hq hq5 hk v w hvw

/-- **Theorem 4D(3), the expansion** `c₄(q) = 1 - 5/q + 2/q² + O(q^(-3))`, with explicit constant:
`1 - 5/q + 2/q² < c₄(q) ≤ 1 - 5/q + 2/q² + 20/q³` for every `q ≥ 11`. -/
theorem c4_expansion (q : ℕ) (hq : 11 ≤ q) :
    1 - 5 / (q : ℝ) + 2 / (q : ℝ) ^ 2 < c4 q ∧
      c4 q ≤ 1 - 5 / (q : ℝ) + 2 / (q : ℝ) ^ 2 + 20 / (q : ℝ) ^ 3 :=
  Proofs.c4_expansion q hq

end Z3NetD4

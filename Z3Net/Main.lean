/-
Development copy (Solution side) of the Challenge for the paper: Well-separated (0,3k,3)-nets in every base q ≥ 4: one linear scramble of the
Faure–Hammersley net (draft, revision 4, 2026-10-07).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
The centred residue `cres` is adapted from Lennart Rudolph's Palomar formalization of the
even-order Grünschloß–Keller nets (github.com/lennrt/palomar-formalizations, MIT licence).
-/
module
public import Z3Net.Defs
public import Z3Net.Net
public import Z3Net.NetQ
public import Z3Net.NetQOdd
public import Z3Net.Sep
public import Z3Net.Two
public import Z3Net.TwoOdd
public import Z3Net.Ceil

@[expose] public section

/-!
# Main statements (same statements as `Challenge.lean`)

Each theorem is closed by the identically-typed `Z3Net.Proofs.*` theorem of the
corresponding proof module (`Net`, `NetQ`, `NetQOdd`, `Sep`, `Two`, `TwoOdd`, `Ceil`).
-/

namespace Z3Net

open Matrix

/-! ## Theorem 1 (`thm:main`): the nets `𝒫_{k,q}` -/

/-- **Theorem `thm:t0`, first sentence.** Every box minor of `(L T², L, L T)` is `±1`
(over `ℤ`), for every `k ≥ 1`. -/
theorem P_boxMinor (k : ℕ) (hk : 1 ≤ k) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    (boxMatrix (PGen k) d).det = 1 ∨ (boxMatrix (PGen k) d).det = -1 :=
  Proofs.P_boxMinor k hk d hd

/-- **Theorem `thm:t0` / Theorem 1(1).** `𝒫_{k,q}` is a `(0,3k,3)`-net in base `q`, for every
`q ≥ 2` and `k ≥ 1`.  (With `d = (k,k,k)` this is also the cell statement of Theorem 1(2).) -/
theorem P_net (q k : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) : IsNet0 q (3 * k) (Ppoint q k) :=
  Proofs.P_net q k hq hk

/-- **Theorem 1(2), covering radius.** Every `x ∈ [0,1]³` has a point of `𝒫_{k,q}` at Euclidean
distance at most `√3 · q^(-k) = √3 N^(-1/3)`. -/
theorem P_covering (q k : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (x : Fin 3 → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (3 * k) → ZMod q,
      ∑ c, (x c - (Ppoint q k v c : ℝ) / (q : ℝ) ^ (3 * k)) ^ 2 ≤ 3 / ((q : ℝ) ^ k) ^ 2 :=
  Proofs.P_covering q k hq hk x hx

/-- **Theorem `thm:sep` / Theorem 1(3), exact integer form.** For `q ≥ 4`, `k ≥ 2` and distinct
indices `v ≠ w`, with `N = q^(3k)` and `D² = torusDist2 N X(v) X(w)` (the squared toroidal
distance times `N²`):
`q² D² ≥ q^(4k) · min{(q-1)², (q-2)² + (q-4)², 3(q-3)²}`,
i.e. `δ ≥ c(q) N^(-1/3)` with
`c(q)² = min{(1-1/q)², (1-2/q)² + (1-4/q)², 3(1-3/q)²}`. -/
theorem P_sep (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) *
        min (((q : ℤ) - 1) ^ 2) (min (((q : ℤ) - 2) ^ 2 + ((q : ℤ) - 4) ^ 2) (3 * ((q : ℤ) - 3) ^ 2))
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k)) (Ppoint q k v) (Ppoint q k w) : ℤ) :=
  Proofs.P_sep q k hq hk v w hvw

/-- **Theorem 1(3), "in particular".** For `q ≥ 8`: `q² D² ≥ q^(4k) (q-1)²`, i.e.
`δ ≥ (1 - 1/q) N^(-1/3)`. -/
theorem P_sep_ge8 (q k : ℕ) (hq : 8 ≤ q) (hk : 2 ≤ k) (v w : Fin (3 * k) → ZMod q)
    (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * ((q : ℤ) - 1) ^ 2
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k)) (Ppoint q k v) (Ppoint q k w) : ℤ) :=
  Proofs.P_sep_ge8 q k hq hk v w hvw

/-- **Theorem 1(3), real form.** The toroidal distance between any two distinct points of
`𝒫_{k,q}` (points `X / N` in `[0,1)³`, `N = q^(3k)`) is at least `c(q) · N^(-1/3)`. -/
theorem P_sep_real (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (v w : Fin (3 * k) → ZMod q)
    (hvw : v ≠ w) :
    cP q * ((q : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (3 * k)) ((Ppoint q k v c : ℤ) - (Ppoint q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (3 * k)) ^ 2) :=
  Proofs.P_sep_real q k hq hk v w hvw

/-! ## Theorem 2 (`thm:two`): the nets `𝒬_{k,p}` -/

/-- **Net part of `thm:two`** (stated, as in the text after Definition `def:Q`, for every odd
prime `p`; Theorem 2 itself needs only `p ≥ 11`). `𝒬_{k,p}` is a `(0,3k,3)`-net over `𝔽_p`. -/
theorem Q_net (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) :
    IsNet0 p (3 * k) (Qpoint p k) :=
  Proofs.Q_net p k hp hp2 hk

/-- **Separation part of `thm:two`, exact integer form.** For primes `p ≥ 11`, `k ≥ 2`, distinct
`v ≠ w`, with `N = p^(3k)`:
`p⁴ D² ≥ p^(4k) · (p²(p-1)² + (p-1)² + (p-2)²)`, i.e. `δ ≥ c*(p) N^(-1/3)` with
`c*(p)² = (1-1/p)² + ((p-1)² + (p-2)²)/p⁴`. -/
theorem Q_sep (p k : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod p) (hvw : v ≠ w) :
    (p : ℤ) ^ (4 * k) * ((p : ℤ) ^ 2 * ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 2) ^ 2)
      ≤ (p : ℤ) ^ 4 * (torusDist2 (p ^ (3 * k)) (Qpoint p k v) (Qpoint p k w) : ℤ) :=
  Proofs.Q_sep p k hp hp11 hk v w hvw

/-- **Theorem 2, real form.** The toroidal distance between distinct points of `𝒬_{k,p}` is at
least `c*(p) · N^(-1/3)`. -/
theorem Q_sep_real (p k : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod p) (hvw : v ≠ w) :
    cQ p * ((p : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k)) ((Qpoint p k v c : ℤ) - (Qpoint p k w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k)) ^ 2) :=
  Proofs.Q_sep_real p k hp hp11 hk v w hvw

/-! ### `thm:two` over `ℤ/qℤ` for every odd modulus `q`

`QGen k` is an integer matrix; `Qpoint q k` reduces it mod `q`, so the definition of `𝒬_{k,q}` is
the same for composite `q` (only `ZMod q` is no longer a field). -/

/-- **Box minors of `QGen`.** For `k ≥ 2`, every box minor of the integer generator matrices
`QGen k` of `𝒬_{k,·}` is `±2^a` for some `a`. -/
theorem Q_boxMinor_pow_two (k : ℕ) (hk : 2 ≤ k) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    ∃ a : ℕ, (boxMatrix (QGen k) d).det = 2 ^ a ∨ (boxMatrix (QGen k) d).det = -2 ^ a :=
  Proofs.Q_boxMinor_pow_two k hk d hd

/-- **Net part of `thm:two`, every odd modulus.** For every odd `q` (composite allowed) and
`k ≥ 2`, `𝒬_{k,q}` is a `(0,3k,3)`-net over `ℤ/qℤ`. -/
theorem Q_net_odd (q k : ℕ) (hq : Odd q) (hk : 2 ≤ k) : IsNet0 q (3 * k) (Qpoint q k) :=
  Proofs.Q_net_odd q k hq hk

/-- **Separation part of `thm:two`, exact integer form, odd `q ≥ 11`** (composite allowed). -/
theorem Q_sep_odd (q k : ℕ) (_hq : Odd q) (hq11 : 11 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * ((q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 2 + ((q : ℤ) - 1) ^ 2 + ((q : ℤ) - 2) ^ 2)
      ≤ (q : ℤ) ^ 4 * (torusDist2 (q ^ (3 * k)) (Qpoint q k v) (Qpoint q k w) : ℤ) :=
  Proofs.Q_sep_odd q k _hq hq11 hk v w hvw

/-- **Theorem 2, real form, odd `q ≥ 11`.** The toroidal distance between distinct points of
`𝒬_{k,q}` is at least `c*(q) · N^(-1/3)`. -/
theorem Q_sep_real_odd (q k : ℕ) (_hq : Odd q) (hq11 : 11 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    cQ q * ((q : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (3 * k)) ((Qpoint q k v c : ℤ) - (Qpoint q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (3 * k)) ^ 2) :=
  Proofs.Q_sep_real_odd q k _hq hq11 hk v w hvw

/-- **Separation part of `thm:two`, exact integer form, every integer `q ≥ 11`.** Even `q` is
included; for even `q` the point set `Qpoint q k` is in general not a net (`k ≥ 3`), but the
separation bound still holds. -/
theorem Q_sep_ge11 (q k : ℕ) (hq11 : 11 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * ((q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 2 + ((q : ℤ) - 1) ^ 2 + ((q : ℤ) - 2) ^ 2)
      ≤ (q : ℤ) ^ 4 * (torusDist2 (q ^ (3 * k)) (Qpoint q k v) (Qpoint q k w) : ℤ) :=
  Proofs.Q_sep_ge11 q k hq11 hk v w hvw

/-- **Theorem 2, real form, every integer `q ≥ 11`.** -/
theorem Q_sep_real_ge11 (q k : ℕ) (hq11 : 11 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    cQ q * ((q : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (3 * k)) ((Qpoint q k v c : ℤ) - (Qpoint q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (3 * k)) ^ 2) :=
  Proofs.Q_sep_real_ge11 q k hq11 hk v w hvw

/-! ## Proposition `prop:ceil` and Proposition A: the first-order ceiling -/

/-- **Proposition `prop:ceil` (i).** Let `p` be an odd prime, `k ≥ 2`, `C` a digital
`(0,3k,3)`-net over `𝔽_p`, and `a` a coordinate with `M̃_aa ≤ -1`; let `b, c'` be the other two.
Then some pair of distinct points has Euclidean (hence also toroidal) squared distance, in cell
units, `< (1 - 1/p + p^(1-k))² + ((|M̃_ba|+1)² + (|M̃_c'a|+1)²)/p²`; so
`c = δ N^(1/3)` satisfies the same strict bound. -/
theorem ceil_neg (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : Mtilde k C a a ≤ -1) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w)
        < (1 - 1 / (p : ℝ) + 1 / (p : ℝ) ^ (k - 1)) ^ 2
          + (((|Mtilde k C (a + 1) a| + 1 : ℤ) : ℝ) ^ 2 + ((|Mtilde k C (a + 2) a| + 1 : ℤ) : ℝ) ^ 2)
            / (p : ℝ) ^ 2 :=
  Proofs.ceil_neg p k hp hp2 hk C hC a ha

/-- **Proposition `prop:ceil` (ii).** Same setting with `M̃_aa ≥ 1`: some pair of distinct
points has squared distance, in cell units,
`< ((M̃_aa+1)² + (|M̃_ba|+1)² + (|M̃_c'a|+1)²)/p²`. -/
theorem ceil_pos (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : 1 ≤ Mtilde k C a a) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w)
        < (((Mtilde k C a a + 1 : ℤ) : ℝ) ^ 2 + ((|Mtilde k C (a + 1) a| + 1 : ℤ) : ℝ) ^ 2
            + ((|Mtilde k C (a + 2) a| + 1 : ℤ) : ℝ) ^ 2) / (p : ℝ) ^ 2 :=
  Proofs.ceil_pos p k hp hp2 hk C hC a ha

/-- **Proposition A, first part, explicit constant.** Odd prime `p`, `k ≥ 3`, digital
`(0,3k,3)`-net over `𝔽_p`, `M̃_aa ≤ -1`, and `|M̃_ba|, |M̃_c'a| ≤ C₀` with `C₀ ≥ 1`. Then some
pair of distinct points is at distance (cell units, Euclidean hence toroidal)
`< 1 - 1/p + 7 C₀²/p²`; i.e. `δ N^(1/3) ≤ 1 - 1/p + O(C₀²/p²)` with explicit constant `7`. -/
theorem propA_neg (p k C₀ : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k) (hC₀ : 1 ≤ C₀)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : Mtilde k C a a ≤ -1)
    (hb : |Mtilde k C (a + 1) a| ≤ C₀) (hc : |Mtilde k C (a + 2) a| ≤ C₀) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      Real.sqrt (cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w))
        < 1 - 1 / (p : ℝ) + 7 * (C₀ : ℝ) ^ 2 / (p : ℝ) ^ 2 :=
  Proofs.propA_neg p k C₀ hp hp2 hk hC₀ C hC a ha hb hc

/-- **Proposition A, second part, explicit constant.** Same setting with `1 ≤ M̃_aa ≤ C₀`:
some pair of distinct points is at distance (cell units) `< 4 C₀ / p`; i.e.
`δ N^(1/3) = O(C₀/p)` with explicit constant `4`. -/
theorem propA_pos (p k C₀ : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k) (hC₀ : 1 ≤ C₀)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : 1 ≤ Mtilde k C a a)
    (ha' : Mtilde k C a a ≤ C₀)
    (hb : |Mtilde k C (a + 1) a| ≤ C₀) (hc : |Mtilde k C (a + 2) a| ≤ C₀) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      Real.sqrt (cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w))
        < 4 * (C₀ : ℝ) / (p : ℝ) :=
  Proofs.propA_pos p k C₀ hp hp2 hk hC₀ C hC a ha ha' hb hc

/-- **Proposition A, second part, for every `k ≥ 2`.** The same conclusion as `propA_pos`
(distance `< 4 C₀ / p` in cell units) under `k ≥ 2` instead of `k ≥ 3`. -/
theorem propA_pos_k2 (p k C₀ : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) (hC₀ : 1 ≤ C₀)
    (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (hC : IsNet0 p (3 * k) (digPoint p (3 * k) C)) (a : Fin 3) (ha : 1 ≤ Mtilde k C a a)
    (ha' : Mtilde k C a a ≤ C₀)
    (hb : |Mtilde k C (a + 1) a| ≤ C₀) (hc : |Mtilde k C (a + 2) a| ≤ C₀) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      Real.sqrt (cellDist2 p k (digPoint p (3 * k) C v) (digPoint p (3 * k) C w))
        < 4 * (C₀ : ℝ) / (p : ℝ) :=
  Proofs.propA_pos_k2 p k C₀ hp hp2 hk hC₀ C hC a ha ha' hb hc

end Z3Net

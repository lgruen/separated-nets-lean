/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.D4D2
public import Z3Net.K1Ceil

@[expose] public section

/-!
# Solution side of the statements added in V14 stage S8 (`prop:4D2`, `prop:k1`(3))

The compared theorems of `scripts/v14_delta.py` (stage S8, `NEW`), restated by name with the same
statements as in `QUNets/Statements/Deficit.lean` and closed by `Z3Net/D4D2.lean` (with the kernel
certificates `Z3Net/D4D2CertKS.lean`, `Z3Net/D4D2CertLB.lean`) and `Z3Net/K1Ceil.lean`.
-/

namespace Z3NetF

open Matrix Finset

/-- **`prop:4D2`**(1), exact interpolation: for the design `F` of `prop:4D2` (`app:designs`, places
`∞, 0, 1, 2`, `λ' ≡ 1`) the residual problem (`prop:F`) is solvable over `ℤ[1/2]`, and so are the
relations of `prop:Gs`: the chosen `U' = Ur4D2` and `β = beta4D2` of the net `P4D2` satisfy them. -/
theorem D4D2_data :
    Residual (0 : Fin 4) Z3NetA.placeA F4D2R 1 Ur4D2 ∧
      BetaRel (0 : Fin 4) Z3NetA.placeA F4D2R 1 beta4D2 :=
  Proofs.D4D2.data_core

/-- **`prop:4D2`**(1): `𝒫^F_{k,q}` is a digital `(0,4k,4)`-net over `ℤ/qℤ` for every odd `q ≥ 3` and
every `k`: every elementary box of volume `q^(-4k)` holds exactly one point (so does every cell). -/
theorem D4D2_net {q : ℕ} (k : ℕ) (hq : Odd q) (h3 : 3 ≤ q) : IsNet0 4 q (4 * k) (P4D2 q k) :=
  Proofs.D4D2.net_core q k hq h3

/-- **`prop:4D2`**(1): every box minor of the generator matrices of `𝒫^F_k` over `ℤ[1/2]` is `±2^i`
(`i ∈ ℤ`): for `d` with `∑ d_c = 4k` the box minor is `ε 2^i` or `ε 2^(-i)`, `ε = ±1`, `i ∈ ℕ`. -/
theorem D4D2_boxMinor (k : ℕ) (d : Fin 4 → ℕ) (hd : ∑ c, d c = 4 * k) :
    ∃ (i : ℕ) (ε : Z3NetA.RS 4), (ε = 1 ∨ ε = -1) ∧
      ((boxMatrix (PGen k (0 : Fin 4) Z3NetA.placeA F4D2R 1 Ur4D2 beta4D2) d).det = ε * 2 ^ i ∨
        (boxMatrix (PGen k (0 : Fin 4) Z3NetA.placeA F4D2R 1 Ur4D2 beta4D2) d).det * 2 ^ i = ε) :=
  Proofs.D4D2.boxMinor_core k d hd

/-- **`prop:4D2`**(1): `h ≤ 2 N^(-1/4)`: for every odd `q ≥ 3`, every `k` and every `x ∈ [0,1]^4`
there is a point of `𝒫^F_{k,q}` at Euclidean distance at most `2 q^(-k)` from `x`. -/
theorem D4D2_covering {q : ℕ} (k : ℕ) (hq : Odd q) (h3 : 3 ≤ q) (x : Fin 4 → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (4 * k) → ZMod q,
      ∑ c, (x c - (P4D2 q k v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2 ≤ 4 / ((q : ℝ) ^ k) ^ 2 :=
  Proofs.D4D2.covering_core q k hq h3 x hx

/-- **`prop:4D2`**(2), the two finite maxima (computer-assisted: kernel `decide` over all
configurations of `def:K` with `L = 3` levels): `K(F) = 2` and `S(F) = 7`, so `Q_D = 23`
(`prop:Dprime`). -/
theorem D4D2_KS : Kdef F4D2 3 = 2 ∧ Sdef F4D2 3 = 7 ∧ QD 2 7 = 23 :=
  ⟨Proofs.D4D2.K_eq, Proofs.D4D2.S_eq, Proofs.D4D2.QD_eq⟩

/-- **`prop:4D2`**(2), the values at `q = 17, 19, 21` (computer-assisted: kernel `decide`): the exact
relaxation of `lem:Ss` with `L = 3` levels is `LB = (q - 2)/q`. -/
theorem D4D2_LB_small (q : ℕ) (hq : q = 17 ∨ q = 19 ∨ q = 21) :
    LBval q F4D2 3 3 = 1 - (2 : ℝ) / q :=
  Proofs.D4D2.LB_small q hq

/-- **`prop:4D2`**(2), the relaxation: `LB ≥ 1 - 2/q` for every odd `q ≥ 17` and every `k ≥ 1`
(the relaxation of `lem:Ss` for `𝒫^F_{k,q}`, `L = min(k, 3)` levels; `prop:Dprime` for `q ≥ 23`, the
exact values with `L = 3` for `q = 17, 19, 21`). -/
theorem D4D2_LB {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k) :
    1 - (2 : ℝ) / q ≤ LBval q F4D2 (min k 3) k :=
  Proofs.D4D2.LB_core q k hq hq17 hk

/-- **`prop:4D2`**(2): for every odd `q ≥ 17` and every `k ≥ 1` the toroidal minimum distance of
`𝒫^F_{k,q}` satisfies `δ N^(1/4) ≥ 1 - 2/q` (`N = q^(4k)`). -/
theorem D4D2_sep {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (2 : ℝ) / q) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (4 * k)) ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (4 * k)) ^ 2) :=
  Proofs.D4D2.sep_real_core q k hq hq17 hk v w hvw

/-- **`prop:4D2`**(2), "hence also Euclidean": `δ N^(1/4) ≥ 1 - 2/q` for the Euclidean distance. -/
theorem D4D2_sep_eucl {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (2 : ℝ) / q) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ)))
      ≤ Real.sqrt (∑ c, (((P4D2 q k v c : ℝ) - P4D2 q k w c) / (q : ℝ) ^ (4 * k)) ^ 2) :=
  Proofs.D4D2.sep_eucl_core q k hq hq17 hk v w hvw

/-- **`prop:4D2`**(3), the ceiling (`cor:ceils`(i) with `a = ∞`, column `(-2, 1, 1, 1)` of `F_0`): for
every odd `q ≥ 17` and every `k ≥ 2` (the paper states `k ≥ 3`) two distinct points of `𝒫^F_{k,q}`
have squared Euclidean and toroidal distance, in units of `N^(-1/4) = q^(-k)`, `< (1 - 2/q)² + 12/q²`. -/
theorem D4D2_ceil {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 2 ≤ k) :
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((P4D2 q k v c : ℝ) - P4D2 q k w c) / (q : ℝ) ^ (4 * k)) ^ 2
        < (1 - (2 : ℝ) / q) ^ 2 + 12 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (4 * k))
          ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2
        < (1 - (2 : ℝ) / q) ^ 2 + 12 / (q : ℝ) ^ 2 :=
  Proofs.D4D2.ceil_core q k hq hq17 hk

/-- **`prop:4D2`**(3): for every odd `q ≥ 17` and every `k ≥ 2` (the paper states `k ≥ 3`),
`δ N^(1/4) < 1 - 2/q + 8/q²`, toroidal and Euclidean; with (2), the first-order deficit of these nets is
exactly `2`. -/
theorem D4D2_ceil_real {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 2 ≤ k) :
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (4 * k)) ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (4 * k)) ^ 2) <
        (1 - (2 : ℝ) / q + 8 / (q : ℝ) ^ 2) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ))) ∧
      Real.sqrt (∑ c, (((P4D2 q k v c : ℝ) - P4D2 q k w c) / (q : ℝ) ^ (4 * k)) ^ 2) <
        (1 - (2 : ℝ) / q + 8 / (q : ℝ) ^ 2) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ))) :=
  Proofs.D4D2.ceil_real_core q k hq hq17 hk

/-- **`prop:k1`(3)**, the ceiling at one cell level (toroidal): a digital net over `ℤ/qℤ`, `q ≥ 3`, in
graph form with depths `(1, …, 1)` (`N = q^s`) whose first offset rows form the integer matrix `F₀`
and whose deeper rows vanish in their own column; a coordinate `a` with `F₀[a][a] = -K₁`
(`K₁ = K((F₀))` in the paper), `q > 2 max |F₀|`. If `gcd(det F₀, q) = 1`, or if the net is a
`(0,s,s)`-net with `s ≥ 4` and `∑_{u ≠ a} |F₀[u][a]| < q`, then two distinct points have toroidal
distance with `(δ N^(1/s))² < (1 - K₁/q)² + ∑_{u ≠ a} (|F₀[u][a]| + 1)²/q²`. -/
theorem k1_ceil {s q K₁ : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (a : Fin s) (ha : F₀ a a = -(K₁ : ℤ)) (hF : ∀ c d, 2 * |F₀ c d| < q)
    (hcase : Int.gcd (Matrix.of F₀).det q = 1 ∨
      (4 ≤ s ∧ IsNet0 s q (s * 1) (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ)) ∧
        ∑ u ∈ univ.erase a, |F₀ u a| < q)) :
    ∃ v w : Fin (s * 1) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ 2 * ∑ c, ((cres (q ^ (s * 1))
        ((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℤ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℤ)) : ℝ) /
          (q : ℝ) ^ (s * 1)) ^ 2 <
        (1 - (K₁ : ℝ) / q) ^ 2 + ∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 :=
  Proofs.K1Ceil.k1_ceil_core hs hq F₀ Φ h1 h2 a K₁ ha hF hcase

/-- **`prop:k1`(3)**, the `(0,s,s)`-net case (`s ≥ 4`, `∑_{u ≠ a} |F₀[u][a]| < q`): the bound of `k1_ceil`
holds for the Euclidean distance too. -/
theorem k1_ceil_eucl {s q K₁ : ℕ} [NeZero q] (hs : 4 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (a : Fin s) (ha : F₀ a a = -(K₁ : ℤ)) (hF : ∀ c d, 2 * |F₀ c d| < q)
    (hnet : IsNet0 s q (s * 1) (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ)))
    (hcol : ∑ u ∈ univ.erase a, |F₀ u a| < q) :
    ∃ v w : Fin (s * 1) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ 2 * ∑ c, (((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℝ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℝ)) /
          (q : ℝ) ^ (s * 1)) ^ 2 <
        (1 - (K₁ : ℝ) / q) ^ 2 + ∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 :=
  Proofs.K1Ceil.k1_ceil_eucl_core hs hq F₀ Φ h1 h2 a K₁ ha hF hnet hcol

/-- **`prop:k1`(3)**, real form (toroidal): under the hypotheses of `k1_ceil`,
`δ N^(1/s) < 1 - K₁/q + C/q²` with `C = ∑_{u ≠ a} (|F₀[u][a]| + 1)²`; with `prop:k1`(1) (`k1_sep`,
`k1_tail`), `δ N^(1/s) = 1 - K₁/q + O(q⁻²)`. -/
theorem k1_ceil_real {s q K₁ : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (a : Fin s) (ha : F₀ a a = -(K₁ : ℤ)) (hF : ∀ c d, 2 * |F₀ c d| < q)
    (hcase : Int.gcd (Matrix.of F₀).det q = 1 ∨
      (4 ≤ s ∧ IsNet0 s q (s * 1) (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ)) ∧
        ∑ u ∈ univ.erase a, |F₀ u a| < q)) :
    ∃ v w : Fin (s * 1) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * 1))
        ((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℤ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℤ)) : ℝ) /
          (q : ℝ) ^ (s * 1)) ^ 2) <
        (1 - (K₁ : ℝ) / q + (∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2) / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) :=
  Proofs.K1Ceil.k1_ceil_real_core hs hq F₀ Φ h1 h2 a K₁ ha hF hcase

end Z3NetF

/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.Lstar

@[expose] public section

/-!
# Solution side of the statements added in V14 stage S7 (`lem:O`, `prop:E`, `lem:C`, `thm:Lstar`)

The compared theorems of `scripts/v14_delta.py` (stage S7, `NEW`), restated by name with the same
statements as in `QUNets/Statements/Deficit.lean` and closed by `Z3Net/Lstar.lean`.
-/

namespace Z3NetF

open Matrix Finset

/-- **`lem:O`** (orientation): if `K = K(F) < ∞`, then for every pair `a ≠ b` of coordinates,
`|M^(j)[a][b]| ≤ K` for all `j < L`, or `|M^(j)[b][a]| ≤ K` for all `j < L`. -/
theorem O_orient {s L K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (hK : Kdef F L = (K : WithTop ℕ))
    (a b : Fin s) (hab : a ≠ b) :
    (∀ j < L, |Msum F j a b| ≤ K) ∨ ∀ j < L, |Msum F j b a| ≤ K :=
  Proofs.Lstar.O_core F L hK a b hab

/-- **`prop:E`** (constant row scalars): `s ≥ 4`, an integer design `F` with `L ≥ 1` levels whose
residual problem is solvable over `ℚ` (`prop:F`) for the places `∞, 0, 1, …, s-2` (in any
assignment `π` to the coordinates: the place of `c ≠ inf` is `π c - 1`, `inf` is `∞`) with row
scalars `λ'` that take one value on all finite places (`λ'_∞` arbitrary). If `K(F) = K < ∞`, then
`K ≥ lcm(1, …, s-3)`. -/
theorem E_lcm {s L K : ℕ} [NeZero s] (hs : 4 ≤ s) (hL : 1 ≤ L) (inf : Fin s) (x : Fin s → ℚ)
    (π : Fin s ≃ Fin s) (hinf : π inf = 0) (hx : ∀ c, c ≠ inf → x c = Z3NetA.placeA (π c))
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ) (Ur : Fin s → ℕ → ℕ → ℚ)
    (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur)
    (hlam : ∀ c d, c ≠ inf → d ≠ inf → lam c = lam d) (hK : Kdef F L = (K : WithTop ℕ)) :
    Nat.lcmUpto (s - 3) ≤ K :=
  Proofs.Lstar.E_core hs hL inf x π hinf hx F lam Ur hres hlam hK

/-- **`prop:E`**, the elementary form printed after it (Chebyshev's
`2^n ≤ (n+1) lcm(1, …, n)`, `n = s - 3`): under the hypotheses of `E_lcm`,
`2^(s-3) ≤ (s-2) K`, i.e. `K(F) ≥ 2^(s-3)/(s-2)`. -/
theorem E_two_pow {s L K : ℕ} [NeZero s] (hs : 4 ≤ s) (hL : 1 ≤ L) (inf : Fin s) (x : Fin s → ℚ)
    (π : Fin s ≃ Fin s) (hinf : π inf = 0) (hx : ∀ c, c ≠ inf → x c = Z3NetA.placeA (π c))
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ) (Ur : Fin s → ℕ → ℕ → ℚ)
    (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur)
    (hlam : ∀ c d, c ≠ inf → d ≠ inf → lam c = lam d) (hK : Kdef F L = (K : WithTop ℕ)) :
    2 ^ (s - 3) ≤ (s - 2) * K :=
  Proofs.Lstar.E_two_pow_core hs hL inf x π hinf hx F lam Ur hres hlam hK

/-- **`prop:E`** for the design `U*_s` of Theorem A (`def:Ustar`; "The class of
Proposition `prop:E` contains … the design `U*_s` of Theorem A"): if `K(U*_s) = K < ∞` (`L ≥ 1`
levels), then `K ≥ lcm(1, …, s-3)`. -/
theorem E_Ustar {s L K : ℕ} [NeZero s] (hs : 4 ≤ s) (hL : 1 ≤ L)
    (hK : Kdef (Z3NetA.UstarF s) L = (K : WithTop ℕ)) : Nat.lcmUpto (s - 3) ≤ K :=
  Proofs.Lstar.E_Ustar_core hs hL hK

/-- **`lem:C`** (a cross-ratio count): the places `∞, 0, 1, …, n` on the coordinates
`0, 1, …, n+1`, two distinct places `d, d'`, a rational `r ≠ 0`, and `w_cd` as in `prop:Ns`. If `C`
is a nonempty set of places `c ∉ {d, d'}` with `w_cd / w_cd' ∈ r Q_K` for all `c ∈ C`, then
`|C| ≤ 1 + 2Kτ*(n)τ*(nK)²`. -/
theorem C_count {n K : ℕ} (d d' : Fin (n + 2)) (hdd : d ≠ d') (r : ℚ) (hr : r ≠ 0)
    (C : Finset (Fin (n + 2))) (hC : C.Nonempty)
    (hmem : ∀ c ∈ C, c ≠ d ∧ c ≠ d' ∧ ∃ z ∈ QK K,
      wN (0 : Fin (n + 2)) Z3NetA.placeA c d / wN (0 : Fin (n + 2)) Z3NetA.placeA c d' = r * z) :
    C.card ≤ 1 + 2 * K * tauStar n * tauStar (n * K) ^ 2 :=
  Proofs.Lstar.C_core d d' hdd r hr C hC hmem

/-- **`lem:C`**, the sharper bound the proof gives: `|C| ≤ 1 + 2Kτ*(n)τ*(nK)` (for two finite places
`d, d'` the place `c` is determined by `h ∣ d - d'`, `B ∣ P` and `β`; the divisor `A ∣ Q` of the
printed count is not needed). -/
theorem C_count_sharp {n K : ℕ} (d d' : Fin (n + 2)) (hdd : d ≠ d') (r : ℚ) (hr : r ≠ 0)
    (C : Finset (Fin (n + 2))) (hC : C.Nonempty)
    (hmem : ∀ c ∈ C, c ≠ d ∧ c ≠ d' ∧ ∃ z ∈ QK K,
      wN (0 : Fin (n + 2)) Z3NetA.placeA c d / wN (0 : Fin (n + 2)) Z3NetA.placeA c d' = r * z) :
    C.card ≤ 1 + 2 * K * tauStar n * tauStar (n * K) :=
  Proofs.Lstar.C_core_sharp d d' hdd r hr C hC hmem

/-- `thm:Lstar`: the places `∞, 0, 1, …, s-2` themselves are an instance of `PGLImage`. -/
theorem PGLImage_self {s : ℕ} [NeZero s] : PGLImage (0 : Fin s) (Z3NetA.placeA : Fin s → ℚ) :=
  Proofs.Lstar.PGLImage_self_core

/-- **`thm:Lstar`** (frame designs): `s ≥ 5`, an integer design `F` with `L ≥ 1` levels whose
residual problem is solvable over `ℚ` (`prop:F`), with arbitrary row scalars, for a frame whose
places are the image of `∞, 0, 1, …, s-2` under an element of `PGL₂(ℚ)` (`PGLImage`; the places
themselves included, `PGLImage_self`). If `K(F) = K < ∞`, then
`(s-3)/4 ≤ 1 + 2Kτ*(s-2)τ*((s-2)K)²`. -/
theorem Lstar_bound {s L K : ℕ} [NeZero s] (hs : 5 ≤ s) (hL : 1 ≤ L) (inf : Fin s)
    (x : Fin s → ℚ) (hplace : PGLImage inf x) (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ)
    (Ur : Fin s → ℕ → ℕ → ℚ) (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur)
    (hK : Kdef F L = (K : WithTop ℕ)) :
    ((s : ℝ) - 3) / 4 ≤ 1 + 2 * (K : ℝ) * tauStar (s - 2) * (tauStar ((s - 2) * K) : ℝ) ^ 2 :=
  Proofs.Lstar.Lstar_core hs hL inf x hplace F lam Ur hres hK

end Z3NetF

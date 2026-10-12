/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmALocal
public import Z3Net.ThmASharp
public import Z3Net.ThmAStar3

@[expose] public section

/-!
# Solution side of the statements added in V14 stage S5; Theorem A assembled

The compared theorems of `scripts/v14_delta.py` (stage S5, `NEW`), restated by name with the same
statements as in `QUNets/Statements/ThmA.lean` and closed by the proof modules imported above:
the local bounds of the proof of `thm:A` (`Ainf_fin_le`, `prodAp_fin_le`, `Ainf_inf_le`,
`prodAp_inf_le`, `hS_le_Hs`), the bound on `a*_s` and its asymptotic form (`aStar_bound`,
`aStar_bound_log`), the first-order sharpness (`A_sharp`, `A_sharp_real`), and `thmA`, the
statement of Theorem A in one piece.
-/

namespace Z3NetA

open Matrix Finset Z3NetF

/-- **`thm:A`, proof, finite column, the place `∞`**: for a finite column `d` (coordinate `d ≠ 0`)
and `j ≤ s - 2`, the monic Chebyshev polynomial `2^{1-j} T_j` (nodes and weights in `[-1, 1]`) gives
`A_{j,∞} ≤ √(s-1)` (the paper prints the weaker `2√(s-1)`). -/
theorem Ainf_fin_le {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (hd : d ≠ 0) (j : ℕ)
    (hj : j ≤ s - 2) : Ainf d j ≤ Real.sqrt ((s : ℝ) - 1) :=
  Proofs.Ainf_fin_le hs d hd j hj

/-- **`thm:A`, proof, finite column, the places `p ∈ S`**: the root-placing polynomials
`g_p = ∏_{r ∈ R'} (X - y_r) · X^{j-|R'|}` give `∏_{p ∈ S} A_{j,p} ≤ d!(n-d)!`, where the paper's `d` is the
place value `d - 1` of the coordinate `d ≠ 0`, i.e. `∏_{p ∈ S} A_{j,p} ≤ (d-1)!(s-1-d)!`. -/
theorem prodAp_fin_le {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (hd : d ≠ 0) (j : ℕ)
    (hj : j ≤ s - 2) :
    ∏ p ∈ primesS s, Ap p d j ≤ (((d : ℕ) - 1).factorial * (s - 1 - (d : ℕ)).factorial : ℕ) :=
  Proofs.prodAp_fin_le hs d hd j hj

/-- **`thm:A`, proof, the column `∞`, the place `∞`**: the monic Chebyshev polynomial of `[0, n]`,
`n = s - 2`, gives `A_{j,∞} ≤ 2√(s-1)(n/4)^j` (column `∞` = coordinate `0`, `j ≤ s - 2`). -/
theorem Ainf_inf_le {s : ℕ} [NeZero s] (hs : 3 ≤ s) (j : ℕ) (hj : j ≤ s - 2) :
    Ainf (0 : Fin s) j ≤ 2 * Real.sqrt ((s : ℝ) - 1) * (((s : ℝ) - 2) / 4) ^ j :=
  Proofs.Ainf_inf_le hs j hj

/-- **`thm:A`, proof, the column `∞`, the places `p ∈ S`**: the falling factorial
`X(X-1)⋯(X-j+1)` takes the values `j! binom(c, j)` at the nodes `c = 0, …, n`, so `A_{j,p} ≤ |j!|_p`
and `∏_{p ∈ S} A_{j,p} ≤ 1/j!`. -/
theorem prodAp_inf_le {s : ℕ} [NeZero s] (hs : 3 ≤ s) (j : ℕ) (hj : j ≤ s - 2) :
    ∏ p ∈ primesS s, Ap p (0 : Fin s) j ≤ ((j.factorial : ℕ) : ℝ)⁻¹ :=
  Proofs.prodAp_inf_le hs j hj

/-- **`thm:A`, proof, the local bounds**: for `s ≥ 4`, every column `d` and every level `j ≤ s - 2`,
`h_{d,j} ≤ H_s = 2√(s-1)(s-2)!` (finite columns: `√(s-1) · d!(n-d)! ≤ √(s-1) n!`; the column `∞`:
`2√(s-1)(n/4)^j/j! ≤ 2√(s-1)e^{n/4} ≤ 2√(s-1) n!`). -/
theorem hS_le_Hs {s : ℕ} [NeZero s] (hs : 4 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    hS d j ≤ 2 * Real.sqrt ((s : ℝ) - 1) * ((s - 2).factorial : ℝ) :=
  Proofs.hS_le_Hs hs d j hj

/-- **`thm:A`, the bound on `a*_s`**: for `s ≥ 4`, every entry `M^(j)[c][d] = E_{d,j}[c]` of `U*_s`
has absolute value at most `(3/2)^{s-2} H_s`, `H_s = 2√(s-1)(s-2)!`, and
`a*_s ≤ 2(s-1)^{3/2}(3/2)^{s-2}(s-2)!`. -/
theorem aStar_bound {s : ℕ} [NeZero s] (hs : 4 ≤ s) :
    (∀ d c : Fin s, ∀ j ≤ s - 2,
        |(Ecol d j c : ℝ)| ≤ (3 / 2) ^ (s - 2) * (2 * Real.sqrt ((s : ℝ) - 1) * ((s - 2).factorial : ℝ))) ∧
      (aStar s : ℝ) ≤ 2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ) :=
  Proofs.aStar_bound_core hs

/-- **`thm:A`, the asymptotic form of the bound**, `2(s-1)^{3/2}(3/2)^{s-2}(s-2)! = e^{s log s + O(s)}`,
with an explicit constant: for every `s ≥ 4`,
`|log(2(s-1)^{3/2}(3/2)^{s-2}(s-2)!) - s log s| ≤ 3s`. -/
theorem aStar_bound_log (s : ℕ) (hs : 4 ≤ s) :
    |Real.log (2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ)) -
      s * Real.log s| ≤ 3 * s :=
  Proofs.aStar_bound_log_core s hs

/-- **`thm:A`(2), the first-order sharpness for `k ≥ 2`** (the printed proof): let `i` attain
`a*_s = α_i`. For `q` as in (1) with `q > 2a*_s` and `q > ∑_{u ≠ i} |F_0[u][i]|`, two distinct points of
`𝒫^{U*_s}_{k,q}` have squared Euclidean and squared toroidal distance, in cell units (times
`q^(2k)`), `< (1 - a*_s/q)² + ∑_{u ≠ i} (|F_0[u][i]| + 1)²/q²` (`F_0 = UstarF s 0`). -/
theorem A_sharp {s : ℕ} [NeZero s] (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k)
    (i : Fin s) (hi : alphaS i = aStar s) (hq2 : 2 * aStar s < q)
    (hcol : ∑ u ∈ univ.erase i, |UstarF s 0 u i| < q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 +
          ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (s * k))
          ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 +
          ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 :=
  Proofs.A_sharp_core hs q k hq hk i hi hq2 hcol

/-- **`thm:A`(2), the first-order sharpness for `k ≥ 2`, real form**: for `q` as in (1) with
`q ≥ 5a*_s + 4` and `q > (s-1) a*_s`, some two distinct points of `𝒫^{U*_s}_{k,q}` have toroidal and
Euclidean distance `< (1 - a*_s/q + (s-1)(a*_s+1)²/q²) N^(-1/s)`, `N = q^(sk)`. With the lower bound
(`A_sep_real`): `δ N^(1/s) = 1 - a*_s/q + O(q⁻²)` as `q → ∞`, the `O` with the constant
`(s-1)(a*_s+1)²`. -/
theorem A_sharp_real {s : ℕ} [NeZero s] (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k)
    (hqa : 5 * aStar s + 4 ≤ q) (hqs : (s - 1) * aStar s < q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ∧
      Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) :=
  Proofs.A_sharp_real_core hs q k hq hk hqa hqs

/-- **Theorem A** (`thm:A`), in one statement. Let `s ≥ 3`, let `q ≥ 2` be an integer all of whose
prime factors are at least `s - 1` (`AdmBase s q`), and let `k ≥ 1`. Let `𝒫^{U*_s}_{k,q}` (`Apoint s q k`)
be the digital net over `ℤ/qℤ` of `def:Ns` for the places `∞, 0, 1, …, s-2` and the design `U*_s` of
`def:Ustar`, with `N = q^(sk)` points `Apoint s q k v / N`, `v ∈ (ℤ/qℤ)^(sk)`. Then:
1. it is a digital `(0, sk, s)`-net over `ℤ/qℤ` (`IsNet0`; with depths `(k, …, k)` every cell
   `∏_i [n_i q^(-k), (n_i+1) q^(-k))` holds exactly one point), and every `x ∈ [0,1]^s` lies within
   Euclidean distance `√s N^(-1/s)` of a point (`h ≤ √s N^(-1/s)`);
2. if `q ≥ 5a*_s + 4`, any two distinct points have toroidal, hence also Euclidean, distance at least
   `(1 - a*_s/q) N^(-1/s)`, for every `k ≥ 1`; and if moreover `k ≥ 2` and `q > (s-1) a*_s`, two
   distinct points have toroidal and Euclidean distance `< (1 - a*_s/q + (s-1)(a*_s+1)²/q²) N^(-1/s)`
   (first-order sharpness: `δ N^(1/s) = 1 - a*_s/q + O(q⁻²)`);
3. `a*_3 = 2`, and for `s ≥ 4`, `a*_s ≤ 2(s-1)^{3/2}(3/2)^{s-2}(s-2)!` with
   `|log(2(s-1)^{3/2}(3/2)^{s-2}(s-2)!) - s log s| ≤ 3s`, i.e. the bound is `e^{s log s + O(s)}`. -/
theorem thmA (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hk : 1 ≤ k) :
    IsNet0 s q (s * k) (Apoint s q k) ∧
    (∀ x : Fin s → ℝ, (∀ c, 0 ≤ x c ∧ x c ≤ 1) → ∃ v : Fin (s * k) → ZMod q,
      Real.sqrt (∑ c, (x c - (Apoint s q k v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) ≤
        Real.sqrt s * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))) ∧
    (5 * aStar s + 4 ≤ q → ∀ v w : Fin (s * k) → ZMod q, v ≠ w →
      (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) ∧
        (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ≤
          Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2)) ∧
    (2 ≤ k → 5 * aStar s + 4 ≤ q → (s - 1) * aStar s < q → ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ∧
      Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))) ∧
    aStar 3 = 2 ∧
    (4 ≤ s →
      (aStar s : ℝ) ≤ 2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ) ∧
      |Real.log (2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ)) -
        s * Real.log s| ≤ 3 * s) := by
  have hq0 : 0 < q := by have := hq.1; omega
  refine ⟨Proofs.A_net_core s q k hs hq, fun x hx => ?_, fun hqa v w hvw =>
    ⟨Proofs.A_sep_real_core s q k hs hq hqa hk v w hvw,
      Proofs.A_sep_eucl_core s q k hs hq hqa hk v w hvw⟩,
    fun hk2 hqa hqs => Proofs.A_sharp_real_core hs q k hq hk2 hqa hqs, Proofs.aStar_three_core,
    fun hs4 => ⟨(Proofs.aStar_bound_core hs4).2, Proofs.aStar_bound_log_core s hs4⟩⟩
  obtain ⟨v, hv⟩ := Proofs.A_covering_core s q k hs hq x hx
  refine ⟨v, ?_⟩
  rw [Proofs.rpow_N s q k (by omega) hq0]
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  calc Real.sqrt (∑ c, (x c - (Apoint s q k v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2)
      ≤ Real.sqrt ((s : ℝ) / ((q : ℝ) ^ k) ^ 2) := Real.sqrt_le_sqrt hv
    _ = Real.sqrt s * (1 / (q : ℝ) ^ k) := by
        rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hqk.le, mul_one_div]

end Z3NetA

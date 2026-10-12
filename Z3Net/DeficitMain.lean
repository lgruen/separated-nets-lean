/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.FDeficit
public import Z3Net.K1Designs

@[expose] public section

/-!
# Solution side of the statements added in V14 stage S2 (`def:K`, `prop:Dprime`, `prop:k1` (1), (2),
`prop:k1designs`: the deficits of the printed layers)

The compared theorems of `scripts/v14_delta.py` (stage S2, `NEW`), restated by name with the same
statements as in `QUNets/Statements/Deficit.lean` and closed by `Z3Net/FDeficit.lean` and the
kernel certificates of `Z3Net/K1Designs.lean`. The changed
statements `Ss_coord`, `Ss_sep`, `D_sep` (`1 ≤ k`) are restated in `Z3Net/FMain.lean`.
-/

namespace Z3NetF

open Matrix Finset

/-- **`def:K`** (with `rem:K`): the deficit `K(F)` of a design with `L ≥ 1` levels is finite iff every
own partial sum `M^(j)[a][a]` (`j < L`) is `≤ 0` and every multi-axis configuration has a backward
coordinate (configurations with `k ≥ L` cell levels; `σ` caps the carry lengths at `L - 1`). -/
theorem Kdef_ne_top_iff {s L k : ℕ} (hL : 1 ≤ L) (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ) :
    Kdef F L ≠ ⊤ ↔ (∀ a, ∀ j < L, Msum F j a a ≤ 0) ∧
      ∀ e j, IsConfig k e j → 2 ≤ (moving e).card → ∃ i, e i ≠ 0 ∧ e i * sigma F L e j i ≤ 0 :=
  Proofs.Deficit.Kdef_ne_top_iff_core hL hLk F

/-- **`def:K`** (with `rem:K`): a finite deficit `K(F)` equals the constant `Kexp` of `rem:K`, the
maximum of the `|M^(j)[a][a]|` (`j < L`) and of `|σ_b| + 1` over the multi-axis configurations with a
single backward coordinate `b` (for any number `k ≥ L` of cell levels). -/
theorem Kdef_eq_Kexp {s L k : ℕ} (hL : 1 ≤ L) (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ)
    (h : Kdef F L ≠ ⊤) : Kdef F L = (Kexp F L k : WithTop ℕ) :=
  Proofs.Deficit.Kdef_eq_Kexp_core hL hLk F h

/-- **`def:K`**, the constant of `rem:K` made a definition: if `K(F) = K < ∞`, the relaxation of
`lem:Ss` satisfies `LB = 1 - K/q + O(q⁻²)` (`k ≥ L` cell levels). -/
theorem K_expansion {s L k K : ℕ} (hs : 1 ≤ s) (hL : 1 ≤ L) (hLk : L ≤ k)
    (F : ℕ → Fin s → Fin s → ℤ) (hK : Kdef F L = (K : WithTop ℕ)) :
    ∃ C : ℝ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      1 - (K : ℝ) / q ≤ LBval q F L k ∧ LBval q F L k ≤ 1 - (K : ℝ) / q + C / (q : ℝ) ^ 2 :=
  Proofs.Deficit.K_expansion_core hs hL hLk F hK

/-- **`prop:Dprime`**, integer form: let `F` have `L` levels, `K = K(F) < ∞` and `S = S(F)`. For every
`q ≥ Q_D(K, S)`, `B = (q - K)²` bounds `q²` and `∑_i b_i²` for every configuration of `lem:Ss` (any
number `k` of cell levels) of `F` or of any truncation `(F_0, …, F_{L'-1})`, `1 ≤ L' ≤ L`; i.e.
`LB ≥ 1 - K/q` (`B` is a valid hypothesis of `Ss_sep`). -/
theorem Dprime_LB {s q L L' k K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (hL' : 1 ≤ L') (hL'L : L' ≤ L)
    (hK : Kdef F L = (K : WithTop ℕ)) (hq : QD K (Sdef F L) ≤ q) :
    ((q : ℤ) - K) ^ 2 ≤ (q : ℤ) ^ 2 ∧
      ∀ e j, IsConfig k e j → ((q : ℤ) - K) ^ 2 ≤ ∑ i, bval q F L' e j i ^ 2 :=
  Proofs.Deficit.Dprime_LB_core F hL' hL'L hK hq

/-- **`prop:Dprime`**: let `F` have `L` levels, `K = K(F) < ∞` and `S = S(F)`. Then
`LB ≥ 1 - K/q` for every `q ≥ Q_D(K, S)`, where `LB` is the relaxation of `lem:Ss` for `F` or for any
truncation `(F_0, …, F_{L'-1})`, `1 ≤ L' ≤ L` (any number `k` of cell levels). -/
theorem Dprime {s q L L' k K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (hL' : 1 ≤ L') (hL'L : L' ≤ L)
    (hK : Kdef F L = (K : WithTop ℕ)) (hq : QD K (Sdef F L) ≤ q) :
    1 - (K : ℝ) / q ≤ LBval q F L' k :=
  Proofs.Deficit.Dprime_core F hL' hL'L hK hq

/-- **`prop:Dprime`** applied to `𝒫^F_{k,q}` (as `D_sep`, without the dominance hypothesis): for a
design reachable by the frame with `K(F) = K < ∞` for its `s - 1` levels, `q ≥ Q_D(K, S(F))`,
`q ≥ 3` and every `k ≥ 1`, `q^(2(sk-k)) (q - K)² ≤ q² D²` for distinct indices, i.e.
`δ ≥ (1 - K/q) N^(-1/s)`. -/
theorem Dprime_sep {R : Type*} [CommRing R] {s q K : ℕ} [NeZero q] (hs : 2 ≤ s)
    (ψ : R →+* ZMod q) (k : ℕ) (hk : 1 ≤ k) (inf : Fin s) (x : Fin s → R)
    (hx : PlacesOK inf x) (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : BetaRel inf x (fun n c d => (F n c d : R)) lam β)
    (hK : Kdef F (s - 1) = (K : WithTop ℕ)) (hq : QD K (Sdef F (s - 1)) ≤ q) (hq3 : 3 ≤ q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - K) ^ 2 ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * k))
        (digPoint q (s * k) (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) v)
        (digPoint q (s * k) (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) w) : ℤ) :=
  Proofs.Deficit.Dprime_sep_core hs ψ k hk inf x hx F lam Ur β hres hβ hK hq hq3 v w hvw

/-- **`prop:k1`(1)**: let `q ≥ 3` and let a digital net over `ℤ/qℤ` be in graph form with depths
`(1, …, 1)` (`m = s`, `N = q^s`) whose first offset rows form the integer matrix `F₀` (diagonal
included, reduced modulo `q`) and whose deeper rows vanish in their own column ((H2)). Then
`δ N^{1/s} ≥ LB₁(q)` for the toroidal distance, `LB₁(q)` the relaxation of `lem:Ss` for the design
`(F₀)` (`L = 1`, `σ = F₀ e`). -/
theorem k1_sep {s q : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    LBval q (layer1 F₀) 1 1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) ≤
      Real.sqrt (∑ c, ((cres (q ^ (s * 1))
        ((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℤ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℤ)) : ℝ) /
          (q : ℝ) ^ (s * 1)) ^ 2) :=
  Proofs.Deficit.k1_sep_core hs hq F₀ Φ h1 h2 v w hvw

/-- **`prop:k1`(1)**, "hence Euclidean": under the hypotheses of `k1_sep`, `δ N^{1/s} ≥ LB₁(q)` for
the Euclidean distance. -/
theorem k1_sep_eucl {s q : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    LBval q (layer1 F₀) 1 1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) ≤
      Real.sqrt (∑ c, (((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℝ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℝ)) /
          (q : ℝ) ^ (s * 1)) ^ 2) :=
  Proofs.Deficit.k1_sep_eucl_core hs hq F₀ Φ h1 h2 v w hvw

/-- **`prop:k1`(1)**, the tail: `LB₁(q) ≥ 1 - K₁/q` for `q ≥ Q_D(K₁, S₁)`, where `K₁ = K((F₀))`,
`S₁ = S((F₀))` (`def:K`). -/
theorem k1_tail {s q K₁ : ℕ} (F₀ : Fin s → Fin s → ℤ)
    (hK : Kdef (layer1 F₀) 1 = (K₁ : WithTop ℕ)) (hq : QD K₁ (Sdef (layer1 F₀) 1) ≤ q) :
    1 - (K₁ : ℝ) / q ≤ LBval q (layer1 F₀) 1 1 :=
  Proofs.Deficit.k1_tail_core F₀ hK hq

/-- **`prop:k1`(2)**: `LB₁(q)`, the relaxation of the one-level design `(F_0)`, is at least the
relaxation of the design `F` with `L` levels at the same `q`, for every number `k ≥ 1` of cell
levels. -/
theorem k1_transfer {s q L k : ℕ} (hk : 1 ≤ k) (F : ℕ → Fin s → Fin s → ℤ) :
    LBval q F L k ≤ LBval q (layer1 (F 0)) 1 1 :=
  Proofs.Deficit.k1_transfer_real_core hk F

/-- **`prop:k1`(2)**: for a design `F` realized by `def:Ns` at one cell level (`𝒫^F_{1,q}`, `m = s`),
every lower bound `B` proved through `lem:Ss` for `F` (with any `L` levels and `k' ≥ 1` cell
levels) holds: `q^(2(s-1)) B ≤ q² D²` for distinct indices. So the lower bounds of `prop:D`
(`D_LB`) and `prop:Dprime` (`Dprime_LB`) hold at `k = 1`. -/
theorem k1_Ns_sep {R : Type*} [CommRing R] {s q L k' : ℕ} [NeZero q] (hs : 2 ≤ s)
    (hq : 3 ≤ q) (ψ : R →+* ZMod q) (hk' : 1 ≤ k') (inf : Fin s) (x : Fin s → R)
    (hx : PlacesOK inf x) (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : BetaRel inf x (fun n c d => (F n c d : R)) lam β) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, IsConfig k' e j → B ≤ ∑ i, bval q F L e j i ^ 2)
    (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * 1 - 1)) * B ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * 1))
        (digPoint q (s * 1) (fun c => (PGen 1 inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) v)
        (digPoint q (s * 1) (fun c => (PGen 1 inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) w) : ℤ) :=
  Proofs.Deficit.k1_Ns_sep_core hs hq ψ hk' inf x hx F lam Ur β hres hβ B hBq hB v w hvw

/-- **`prop:k1designs`(1)**, the deficits (computer-assisted: kernel `decide`): the level-0 frame
layers of `tab:practical` as printed in `app:designs` (`s = 4`: the off-diagonal part of `U*_4`;
`s = 5`: that of the `s = 5` design of `tab:Kdesigns`; diagonals chosen for `k = 1`; `s = 6`:
searched scalars) have `K₁ = K((F₀)) = 2, 3, 6` (`def:K`). -/
theorem k1designs_frame_K :
    Kdef (layer1 k1Frame4) 1 = 2 ∧ Kdef (layer1 k1Frame5) 1 = 3 ∧ Kdef (layer1 k1Frame6) 1 = 6 :=
  ⟨Proofs.K1Designs.frame4_K, Proofs.K1Designs.frame5_K, Proofs.K1Designs.frame6_K⟩

/-- **`prop:k1designs`(1)**, the `s = 6` layer is a Cauchy layer: on the places `∞, 0, 1, 2, 3, 4`
(admissible), its off-diagonal entries are `λ'_c μ_d w_cd` (`w_cd` of `prop:Ns`) with the row and
column scalars `λ' = (1, 2/3, -2, -2/3, 2/3, -2)`, `μ = (3/2, 18, 3, 3, 9, 6)` of `app:designs`. -/
theorem k1designs_frame6_cauchy :
    PlacesOK (0 : Fin 6) k1Places6 ∧
      ∀ c d : Fin 6, c ≠ d → (k1Frame6 c d : ℚ) = k1Lam6 c * k1Mu6 d * wN (0 : Fin 6) k1Places6 c d :=
  ⟨Proofs.K1Designs.places6_ok, Proofs.K1Designs.frame6_cauchy⟩

/-- **`prop:k1designs`(2)** and `tab:practical`, the deficits of the free layers (computer-assisted:
kernel `decide`): the free layers of `app:designs` have `K₁ = 2` (`s = 5`), `3` and `5` (`s = 6`),
and the first two have entries of absolute value at most `3`. (The `t = 0` completions and the
separation scans of `prop:k1designs`(2) are not part of this statement.) -/
theorem k1designs_free_K :
    Kdef (layer1 k1Free5) 1 = 2 ∧ Kdef (layer1 k1Free6a) 1 = 3 ∧ Kdef (layer1 k1Free6b) 1 = 5 ∧
      (∀ c d, |k1Free5 c d| ≤ 3) ∧ (∀ c d, |k1Free6a c d| ≤ 3) :=
  ⟨Proofs.K1Designs.free5_K, Proofs.K1Designs.free6a_K, Proofs.K1Designs.free6b_K,
    Proofs.K1Designs.free_small.1, Proofs.K1Designs.free_small.2⟩
end Z3NetF

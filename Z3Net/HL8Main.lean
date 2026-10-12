/-
Solution-side restatement of ChallengeHL8 (entry HL8).
-/
module
public import Z3Net.HL8Defs
public import Z3Net.HL8B5
public import Z3Net.HL8B8
public import Z3Net.HL8Lim

@[expose] public section

/-!
# Main statements of entry HL8 (same statements as `ChallengeHL8.lean`)

Each theorem is closed by the corresponding `Z3NetHL.Proofs.*` theorem of its proof module.
-/

namespace Z3NetHL

open Matrix Finset

/-! ## Statements -/

/-! ### Level-truncated admissibility (`prop:Gsplit` and the remark after it) -/

/-- **(H1) per level.** As `HL_row0` (entry HL), with admissibility only up to level
`min(k, s-1)`: row `0` of every block of the net is the design. -/
theorem HL_row0_lev (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (hs : 2 ≤ s) (hq : HLAdmL s q (min k (s - 1)) u v lam gco)
    (hden : HLDen s q gco dg) (hk : 1 ≤ k) (c d : Fin s) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0)
    (j : Fin k) :
    HLPhi s q k u v lam gco dg c d r j = qr q (HLdes u v lam gco dg (k - 1 - (j : ℕ)) c d) :=
  Proofs.HL_row0_lev s q k u v lam gco dg hs hq hden hk c d r hr j

/-- **Split-frame nets, per level.** For every `s ≥ 2`, every `k ≥ 1` and every `q` admissible up
to level `min(k, s-1)` (composite allowed), the net is a digital `(0,sk,s)`-net over `ℤ/qℤ`. -/
theorem HL_net_lev (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (hs : 2 ≤ s) (hq : HLAdmL s q (min k (s - 1)) u v lam gco) (hk : 1 ≤ k) :
    IsNet0 s q (s * k) (HLpoint s q k u v lam gco dg) :=
  Proofs.HL_net_lev s q k u v lam gco dg hs hq hk

/-- **`prop:Hk`(1) per level** (the carry relaxation), as `HL_relax` (entry HL) with admissibility
only up to level `min(k, s-1)`. -/
theorem HL_relax_lev (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdmL s q (min k (s - 1)) u v lam gco) (hden : HLDen s q gco dg) (hq7 : 7 ≤ q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d) (hk : 1 ≤ k)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤
        (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) :=
  Proofs.HL_relax_lev s q k u v lam gco dg F2 hs hq hden hq7 hF2 hk x y hxy

/-- **`prop:Hk`(2) per level** (dominance limit, exact integer form), as `HL_dom` (entry HL) with
admissibility only up to level `min(k, s-1)`. -/
theorem HL_dom_lev (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdmL s q (min k (s - 1)) u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    (q : ℤ) ^ (2 * (s * k - k - 1)) *
        min ((s : ℤ) * ((q : ℤ) - 2 * Bdom s F2 - 2) ^ 2) (8 * ((q : ℤ) - Bdom s F2 - 1) ^ 2) ≤
      4 * (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) :=
  Proofs.HL_dom_lev s q k u v lam gco dg F2 hs hq hden hqodd hF2 hhalf0 hhalf hdiag hdom hqB hk x y hxy

/-- **`prop:Hk`(2) per level, real form**: `δ N^(1/s) ≥ min(√s (1/2 - η), √2 (1 - η))`,
`η = (B + 1)/q`, under the hypotheses of `HL_dom_lev`. -/
theorem HL_dom_lev_real (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdmL s q (min k (s - 1)) u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((Bdom s F2 : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((Bdom s F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((HLpoint s q k u v lam gco dg x c : ℤ) - (HLpoint s q k u v lam gco dg y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) :=
  Proofs.HL_dom_lev_real s q k u v lam gco dg F2 hs hq hden hqodd hF2 hhalf0 hhalf hdiag hdom hqB hk x y hxy

/-! ### `prop:HL5`: `97` and `101` matter only for `k ≥ 4` -/

/-- **`prop:HL5`, net clause per level.** For every prime `q ∉ {2, 3, 5, 7}` and every `k ≥ 1`,
with `q ∉ {97, 101}` required only when `k ≥ 4`, the `B₅` net is a digital `(0,5k,5)`-net over
`𝔽_q`. -/
theorem B5_net_lev (q k : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7} : Finset ℕ))
    (h4 : 4 ≤ k → q ∉ ({97, 101} : Finset ℕ)) (hk : 1 ≤ k) :
    IsNet0 5 q (5 * k) (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5) :=
  Proofs.B5_net_lev q k hq hbad h4 hk

/-! ### The `s = 8` design (`sec:large`, "Dimension eight") -/

/-- **The `s = 8` design is the witness.** `2 F_x[c][d]` of the design (`HLdes` from the points,
`λ'`, the interpolated `f_{d,n}` and the diagonal) is the witness matrix `F2B8`, for every `x`. -/
theorem B8_design (x : ℕ) (c d : Fin 8) :
    2 * HLdes uB8 vB8 lamB8 gcoB8 dgB8 x c d = F2B8 x c d :=
  Proofs.B8_design x c d

/-- **The `s = 8` design is half-integer and dominant**: `2F_0` odd (diagonal included), `2F_x`
even with zero diagonal for `x ≥ 1`, `A_c ≤ a_c` with `A_c` over all levels `j ≤ 6`, and
`B = max_c (2a_c + 2A_c) = 328183862`. -/
theorem B8_dom :
    (∀ c d, Odd (F2B8 0 c d)) ∧ (∀ x c d, 1 ≤ x → Even (F2B8 x c d)) ∧
      (∀ x c, 1 ≤ x → F2B8 x c c = 0) ∧ (∀ c, (A2 8 F2B8 c : ℤ) ≤ -F2B8 0 c c) ∧
      Bdom 8 F2B8 = 328183862 :=
  Proofs.B8_dom

/-- **The `s = 8` net at every admissible prime, per level.** For every prime `q` and every
`k ≥ 1` such that `q` divides none of the exceptional numbers `B8exc j` of the levels
`j < min(k, 7)`, the net is a digital `(0,8k,8)`-net over `𝔽_q`. (The listed numbers are primes —
checked outside Lean, not certified here — so for them the hypothesis says that `q` is not one of
them: the paper's "`t = 0` for every `k` at every prime outside the 40 exceptional primes", with
the level at which each prime enters.) -/
theorem B8_net (q k : ℕ) (hq : q.Prime) (hk : 1 ≤ k)
    (hexc : ∀ j < min k 7, ∀ p ∈ B8exc j, ¬ q ∣ p) :
    IsNet0 8 q (8 * k) (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8) :=
  Proofs.B8_net q k hq hk hexc

/-- **The `s = 8` separation bound** (`prop:Hk`(2) with `B = 328183862`, per level). For every
prime `q ≥ 2B + 2 = 656367726` and every `k ≥ 1`, with `q ≠ 736578889` when `k ≥ 6` and
`q ∉ {743720623, 979256059, 5526505499, 3061420595773}` when `k ≥ 7` (the exceptional primes
`≥ 2B + 2` and their levels, `app:designs`): any two distinct points of the net satisfy
`δ N^(1/8) ≥ min(√8 (1/2 - η), √2 (1 - η))`, `η = (B + 1)/q` (which tends to `√2`). -/
theorem B8_sep_real (q k : ℕ) (hq : q.Prime) (hqB : 656367726 ≤ q) (hk : 1 ≤ k)
    (h6 : 6 ≤ k → q ≠ 736578889)
    (h7 : 7 ≤ k → q ∉ ({743720623, 979256059, 5526505499, 3061420595773} : Finset ℕ))
    (x y : Fin (8 * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt 8 * (1 / 2 - ((328183862 : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((328183862 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (8 * k))
          ((HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 x c : ℤ) -
            (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 y c : ℤ)) : ℝ) / (q : ℝ) ^ (8 * k)) ^ 2) :=
  Proofs.B8_sep_real q k hq hqB hk h6 h7 x y hxy

/-- **The `s = 8` headline** (the italic claim of `sec:large`). For every prime `q > 2.25·10⁹` and
every `k ≥ 1`, except `q ∈ {5526505499, 3061420595773}` when `k ≥ 7`, the net of the `s = 8`
design is a digital `(0,8k,8)`-net over `𝔽_q`, and every two distinct points have toroidal
distance `> N^(-1/8)`, `N = q^(8k)`, i.e. `δ N^(1/8) > 1`. -/
theorem B8_main (q k : ℕ) (hq : q.Prime) (hq0 : 2250000000 < q) (hk : 1 ≤ k)
    (hexc : 7 ≤ k → q ≠ 5526505499 ∧ q ≠ 3061420595773) :
    IsNet0 8 q (8 * k) (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8) ∧
      ∀ x y : Fin (8 * k) → ZMod q, x ≠ y →
        ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ)))
          < Real.sqrt (∑ c, ((cres (q ^ (8 * k))
              ((HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 x c : ℤ) -
                (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 y c : ℤ)) : ℝ) / (q : ℝ) ^ (8 * k)) ^ 2) :=
  Proofs.B8_main q k hq hq0 hk hexc

/-- **The `s = 8` limit** (`sec:large`, "Dimension eight": `δ N^(1/8) → √2`, the `E_8` value),
uniformly in `k`: for every `ε > 0` there is `P` such that for every prime `q ≥ P` and every
`k ≥ 1`, every two distinct points have toroidal distance `≥ (√2 - ε) N^(-1/8)` and some two
distinct points have Euclidean distance `≤ (√2 + ε) N^(-1/8)`, `N = q^(8k)`. -/
theorem B8_limit (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ q k : ℕ, q.Prime → P ≤ q → 1 ≤ k →
      (∀ x y : Fin (8 * k) → ZMod q, x ≠ y →
        (Real.sqrt 2 - ε) * ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ)))
          ≤ Real.sqrt (∑ c, ((cres (q ^ (8 * k))
              ((HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 x c : ℤ) -
                (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 y c : ℤ)) : ℝ) / (q : ℝ) ^ (8 * k)) ^ 2)) ∧
      ∃ x y : Fin (8 * k) → ZMod q, x ≠ y ∧
        Real.sqrt (∑ c, (((HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 x c : ℝ) -
            (HLpoint 8 q k uB8 vB8 lamB8 gcoB8 dgB8 y c : ℝ)) / (q : ℝ) ^ (8 * k)) ^ 2)
          ≤ (Real.sqrt 2 + ε) * ((q : ℝ) ^ (8 * k)) ^ (-(1 / (8 : ℝ))) :=
  Proofs.B8_limit ε hε

end Z3NetHL

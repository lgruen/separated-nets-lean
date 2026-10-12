/-
Solution-side restatement of ChallengeHL. Note: Theorem HL of the research notes (2026-10-07; independently
audited in the research notes): split-frame digital `(0,sk,s)`-nets
over `ℤ/qℤ` whose first offset digit carries a half-integer geometric layer (the packing `D_s⁺`),
for every `k`; separation tending to `min(√s/2, √2)`; the `s = 5` design with
`δ N^(1/5) > 1.0265` for every prime `q ≥ 1511` and every `k ≥ 1`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
The centred residue `cres` is adapted from Lennart Rudolph's Palomar formalization of the
even-order Grünschloß–Keller nets (github.com/lennrt/palomar-formalizations, MIT licence).
-/
module
public import Z3Net.HLDefs
public import Z3Net.HLSep
public import Z3Net.HLMainH
public import Z3Net.HLB5Final
public import Z3Net.HLUpMain

@[expose] public section

/-!
# Main statements of entry HL (same statements as `ChallengeHL.lean`)

Each theorem is closed by the corresponding `Z3NetHL.Proofs.*` theorem of its proof module.
-/

namespace Z3NetHL

open Matrix Finset

/-! ## Statements -/


/-- **Lemma T′** (split-frame box minors, exact value). For every `s`, `m`, `k` and every
composition `d` of `m`, the box minor of the split frame equals the confluent Vandermonde
determinant of the `2s` points in the order `(0,0) < (0,1) < (1,0) < …` (`(c,0) = v_c`,
`(c,1) = u_c`) with multiplicities `splitMult`:
`∏_{(c',e') < (c,e)} (x_(c,e) - x_(c',e'))^(mult(c',e') · mult(c,e))`. -/
theorem HL_frameMinor (s m k : ℕ) (u v : Fin s → ℤ) (d : Fin s → ℕ) (hd : ∑ c, d c = m) :
    (boxMatrix (splitGen m k u v) d).det =
      ∏ c : Fin s, ∏ e : Fin 2, ∏ c' : Fin s, ∏ e' : Fin 2,
        (if c' < c ∨ (c' = c ∧ e' < e) then
          (splitPt u v c e - splitPt u v c' e') ^ (splitMult k d c' e' * splitMult k d c e)
        else 1) :=
  Proofs.HL_frameMinor s m k u v d hd

/-- **Prop N′** (the Cauchy kernel): over `ℚ`, for `c ≠ d` with `u_c ≠ v_{d'}` for all `d'`,
`Ψ_cd[0, j] = P_c^k · y_cd^(k-j)` (so `P_c^(-k) Ψ_cd[0, ·]` is `w_cd y_cd^n` at `x`-index
`n = k-1-j`, `w = y = 1/(u_c - v_d)`). -/
theorem HL_propN (s k : ℕ) (u v : Fin s → ℤ) (c d : Fin s) (hcd : c ≠ d)
    (huv : ∀ d', u c ≠ v d') (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) (j : Fin k) :
    (Psi k u v c d r j : ℚ) =
      (∏ d' : Fin s, ((u c - v d' : ℤ) : ℚ)) ^ k * yQ u v c d ^ (k - (j : ℕ)) :=
  Proofs.HL_propN s k u v c d hcd huv r hr j

/-- **(H1).** For admissible `q` and every `k ≥ 1`, row `0` of every block `Φ'_cd` of the net is
the design: level `j` carries `F_{k-1-j}[c][d]` (`0` for `k-1-j ≥ s-1`). -/
theorem HL_row0 (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (hs : 2 ≤ s) (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg)
    (hk : 1 ≤ k) (c d : Fin s) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) (j : Fin k) :
    HLPhi s q k u v lam gco dg c d r j = qr q (HLdes u v lam gco dg (k - 1 - (j : ℕ)) c d) :=
  Proofs.HL_row0 s q k u v lam gco dg hs hq hden hk c d r hr j

/-- **Split-frame nets are `(0,sk,s)`-nets.** For every `s ≥ 2`, every admissible `q` (composite
allowed) and every `k ≥ 1`, the net is a digital `(0,sk,s)`-net over `ℤ/qℤ`. -/
theorem HL_net (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (hs : 2 ≤ s) (hq : HLAdm s q u v lam gco) (hk : 1 ≤ k) :
    IsNet0 s q (s * k) (HLpoint s q k u v lam gco dg) :=
  Proofs.HL_net s q k u v lam gco dg hs hq hk

/-- **Prop H_k(a)** (the carry relaxation). Let `F2 = 2 F` be the doubled design (integers).
For admissible `q ≥ 7`, every `k ≥ 1` and distinct indices `x ≠ y` (with `D² = torusDist2` at
scale `N = q^(sk)`): either `D² ≥ 4 q^(2(s-1)k)` (two cells apart in some coordinate), or there
are cell steps `E ∈ {-2,…,2}^s \ {0}`, carry lengths `J_d < min(k, s-1)` and first-offset-digit
changes `Δ_c` with `2Δ_c ≡ 2σ_c (mod q)` (`2σ_c = sig2 F2 E J c`), `|Δ_c| < q`, and
`D² ≥ q^(2(s-1)k-2) ∑_c max(0, |q E_c + Δ_c| - 1)²`. -/
theorem HL_relax (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hq7 : 7 ≤ q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d) (hk : 1 ≤ k)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤
        (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) :=
  Proofs.HL_relax s q k u v lam gco dg F2 hs hq hden hq7 hF2 hk x y hxy

/-- **Prop H_k(b)** (dominance limit), exact integer form. For a half-integer design
(`2F_0` odd including the diagonal, `2F_x` even and with zero diagonal for `x ≥ 1`) with dominant
diagonal (`2a_c = -2F_0[c][c] ≥ 2A_c`), odd admissible `q ≥ 2B + 2` (`B = Bdom`), every `k ≥ 1`
and distinct indices: `q^(2(s-1)k-2) · min(s (q - 2B - 2)², 8 (q - B - 1)²) ≤ 4 D²`,
i.e. `δ N^(1/s) ≥ min(√s (1/2 - η), √2 (1 - η))` with `η = (B + 1)/q`. -/
theorem HL_dom (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    (q : ℤ) ^ (2 * (s * k - k - 1)) *
        min ((s : ℤ) * ((q : ℤ) - 2 * Bdom s F2 - 2) ^ 2) (8 * ((q : ℤ) - Bdom s F2 - 1) ^ 2) ≤
      4 * (torusDist2 (q ^ (s * k)) (HLpoint s q k u v lam gco dg x) (HLpoint s q k u v lam gco dg y) : ℤ) :=
  Proofs.HL_dom s q k u v lam gco dg F2 hs hq hden hqodd hF2 hhalf0 hhalf hdiag hdom hqB hk x y hxy

/-- **Prop H_k(b), real form.** Under the hypotheses of `HL_dom`, the toroidal distance between
any two distinct points (points `X / N`, `N = q^(sk)`) is at least
`min(√s (1/2 - η), √2 (1 - η)) · N^(-1/s)`, `η = (B + 1)/q`. -/
theorem HL_dom_real (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((Bdom s F2 : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((Bdom s F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((HLpoint s q k u v lam gco dg x c : ℤ) - (HLpoint s q k u v lam gco dg y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) :=
  Proofs.HL_dom_real s q k u v lam gco dg F2 hs hq hden hqodd hF2 hhalf0 hhalf hdiag hdom hqB hk x y hxy

/-- **Theorem HL** (the explicit design `H_s`, Lemma 2). For every `s ≥ 2`, every prime
`q ≥ max(2s, 2 B_s + 2)` and every `k ≥ 1`, the net of `H_s` is a digital `(0,sk,s)`-net over
`𝔽_q`, and any two distinct points satisfy
`q^(2(s-1)k-2) · min(s (q - 2B_s - 2)², 8 (q - B_s - 1)²) ≤ 4 D²`. -/
theorem HL_main (s q k : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q) (hqB : 2 * BH s + 2 ≤ q)
    (hk : 1 ≤ k) :
    IsNet0 s q (s * k) (HLpoint s q k uH vH (lamH s) gcoH (dgH s)) ∧
      ∀ x y : Fin (s * k) → ZMod q, x ≠ y →
        (q : ℤ) ^ (2 * (s * k - k - 1)) *
            min ((s : ℤ) * ((q : ℤ) - 2 * BH s - 2) ^ 2) (8 * ((q : ℤ) - BH s - 1) ^ 2) ≤
          4 * (torusDist2 (q ^ (s * k)) (HLpoint s q k uH vH (lamH s) gcoH (dgH s) x)
            (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y) : ℤ) :=
  Proofs.HL_main s q k hs hq hqs hqB hk

/-- **Theorem HL, real form**: `δ N^(1/s) ≥ min(√s (1/2 - η), √2 (1 - η))`, `η = (B_s + 1)/q`,
uniformly in `k` (which tends to `min(√s/2, √2)` as `q → ∞`). -/
theorem HL_main_real (s q k : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q)
    (hqB : 2 * BH s + 2 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BH s : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((BH s : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((HLpoint s q k uH vH (lamH s) gcoH (dgH s) x c : ℤ) -
            (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) :=
  Proofs.HL_main_real s q k hs hq hqs hqB hk x y hxy

/-- **The `s = 5` design is the witness.** `2 F_x[c][d]` of `B₅` (`HLdes` from the points,
`λ'`, the interpolated `f_{d,n}` and the diagonal) is the witness matrix `F2`, for every `x`. -/
theorem B5_design (x : ℕ) (c d : Fin 5) :
    2 * HLdes uB5 vB5 lamB5 gcoB5 dgB5 x c d = F2B5 x c d :=
  Proofs.B5_design x c d

/-- **`B₅` is a net** for every prime `q ∉ {2, 3, 5, 7, 97, 101}` and every `k ≥ 1`. -/
theorem B5_net (q k : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7, 97, 101} : Finset ℕ))
    (hk : 1 ≤ k) : IsNet0 5 q (5 * k) (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5) :=
  Proofs.B5_net q k hq hbad hk

/-- **The `s = 5` headline, integer form.** For every prime `q ≥ 1511`, every `k ≥ 1` and
distinct indices: `1.02652² · q^(8k) ≤ D²` (`D² = torusDist2` at scale `N = q^(5k)`), i.e.
`δ N^(1/5) ≥ 1.02652`. -/
theorem B5_sep (q k : ℕ) (hq : q.Prime) (hq1511 : 1511 ≤ q) (hk : 1 ≤ k)
    (x y : Fin (5 * k) → ZMod q) (hxy : x ≠ y) :
    (102652 : ℤ) ^ 2 * (q : ℤ) ^ (2 * (5 * k - k)) ≤
      100000 ^ 2 * (torusDist2 (q ^ (5 * k)) (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 x)
        (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 y) : ℤ) :=
  Proofs.B5_sep q k hq hq1511 hk x y hxy

/-- **The `s = 5` headline, real form**: `δ N^(1/5) > 1.0265` for every prime `q ≥ 1511` and
every `k ≥ 1`. -/
theorem B5_sep_real (q k : ℕ) (hq : q.Prime) (hq1511 : 1511 ≤ q) (hk : 1 ≤ k)
    (x y : Fin (5 * k) → ZMod q) (hxy : x ≠ y) :
    1.0265 * ((q : ℝ) ^ (5 * k)) ^ (-(1 / (5 : ℝ)))
      < Real.sqrt (∑ c, ((cres (q ^ (5 * k))
          ((HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 x c : ℤ) -
            (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5 y c : ℤ)) : ℝ) / (q : ℝ) ^ (5 * k)) ^ 2) :=
  Proofs.B5_sep_real q k hq hq1511 hk x y hxy

/-! ## Stage 1 additions: Prop H_k for arbitrary graph forms, the upper bound and the limit -/

/-- **Prop H_k(1)** (`prop:Hk`(1)), for an arbitrary graph form over `ℤ/qℤ`, `q` odd (prime or
not), whose row `0` is a design satisfying (Half) on the levels `< L = min(k, s-1)`. If
`q > 2 max|σ_c| = max |sig2|` over all `E ∈ {-2,…,2}^s` and carry lengths `J_d < L`, then any
`LB` below `min(2, |b|/q)` for every `E ≠ 0` and `J` (with `|b| = √(∑ (2b_c)²)/2`, `bOpt2`; the
paper's `LB` is the least such value) satisfies `δ N^(1/s) ≥ LB` (toroidal distance). -/
theorem GF_relax (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 3 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hσ : ∀ (E : Fin s → ℤ) (J : Fin s → ℕ) (c : Fin s), (∀ d, |E d| ≤ 2) →
      (∀ d, J d < min k (s - 1)) → |sig2 F2 E J c| < q)
    (LB : ℝ) (hLB : ∀ (E : Fin s → ℤ) (J : Fin s → ℕ), (∀ d, |E d| ≤ 2) → (∃ d, E d ≠ 0) →
      (∀ d, J d < min k (s - 1)) →
      LB ≤ min 2 (Real.sqrt (∑ c, ((bOpt2 q F2 E J c : ℤ) : ℝ) ^ 2) / (2 * q)))
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    LB * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((GFpoint s q k Φ x c : ℤ) - (GFpoint s q k Φ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) :=
  Proofs.GF_relax_core s q k Φ F2 hs hqodd hk hrow hhalf0 hhalf hσ LB hLB x y hxy

/-- **Prop H_k(2)** (`prop:Hk`(2)) as printed, integer form, for an arbitrary graph form over
`ℤ/qℤ` (`q` odd): (Half), zero deeper diagonal and dominance `a_c ≥ A_c` only on the levels
`< L = min(k, s-1)`; if `q ≥ 2B + 2` (`B = BdomL s L F2`), then
`q^(2(s-1)k-2) · min(s (q - 2B - 2)², 8 (q - B - 1)²) ≤ 4 D²`. -/
theorem GF_dom (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 + 2 ≤ q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    (q : ℤ) ^ (2 * (s * k - k - 1)) *
        min ((s : ℤ) * ((q : ℤ) - 2 * BdomL s (min k (s - 1)) F2 - 2) ^ 2)
          (8 * ((q : ℤ) - BdomL s (min k (s - 1)) F2 - 1) ^ 2) ≤
      4 * (torusDist2 (q ^ (s * k)) (GFpoint s q k Φ x) (GFpoint s q k Φ y) : ℤ) :=
  Proofs.GF_dom_core s q k Φ F2 hs hqodd hk hrow hhalf0 hhalf hdiag hdom hqB x y hxy

/-- **Prop H_k(2)** as printed, real form, under the paper's hypothesis `q > 2B`:
`δ N^(1/s) ≥ min(√s (1/2 - η), √2 (1 - η))`, `η = (B + 1)/q`, `B` over the levels `< L`. -/
theorem GF_dom_real (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 < q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q))
        (Real.sqrt 2 * (1 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((GFpoint s q k Φ x c : ℤ) - (GFpoint s q k Φ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) :=
  Proofs.GF_dom_real_core s q k Φ F2 hs hqodd hk hrow hhalf0 hhalf hdiag hdom hqB x y hxy

/-- **Prop H_k(3)** (`prop:Hk`(3)), for an arbitrary graph form over `𝔽_q`: if `F_0` is
half-integral and `q > 4sC + 2` (`2C = C2max`), there are two distinct points at Euclidean
(hence also toroidal) distance at most `(min(√s/2, √2) + √s (2C + 1)/q) N^(-1/s)`. -/
theorem GF_upper (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 3 ≤ s) (hq : q.Prime) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hqC : 2 * s * C2max s F2 + 2 < q) :
    ∃ x y : Fin (s * k) → ZMod q, x ≠ y ∧
      Real.sqrt (∑ c, (((GFpoint s q k Φ x c : ℝ) - (GFpoint s q k Φ y c : ℝ)) / (q : ℝ) ^ (s * k)) ^ 2)
        ≤ (min (Real.sqrt s / 2) (Real.sqrt 2) + Real.sqrt s * ((C2max s F2 : ℝ) + 1) / q) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) :=
  Proofs.GF_upper_core s q k Φ F2 hs hq hk hrow hhalf0 hqC

/-- **(H1) as `RowDesign`.** For admissible `q` and `k ≥ 1`, the split-frame net satisfies the
row-`0` hypothesis of Prop H_k with the doubled design `F2 = 2F` (so `GF_relax`, `GF_dom`,
`GF_dom_real`, `GF_upper` apply to `HLpoint = GFpoint … (HLPhi …)`); only the design levels
`< min(k, s-1)` need to be half-integral. -/
theorem HL_rowDesign (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg)
    (hF2 : ∀ x c d, x < min k (s - 1) → 2 * HLdes u v lam gco dg x c d = F2 x c d) (hk : 1 ≤ k) :
    RowDesign s q k (HLPhi s q k u v lam gco dg) F2 ∧
      ∀ x, HLpoint s q k u v lam gco dg x = GFpoint s q k (HLPhi s q k u v lam gco dg) x :=
  Proofs.HL_rowDesign_core s q k u v lam gco dg F2 hs hq hden hF2 hk

/-- **Prop H_k(2) as printed, for the split-frame nets** (real form): the design data only on
the levels `< L = min(k, s-1)` (`2F` integral there, (Half), zero deeper diagonal, dominance
with `A_c` over `j < L`), odd admissible `q > 2B` (`B = BdomL s L F2`), every `k ≥ 1`:
`δ N^(1/s) ≥ min(√s (1/2 - η), √2 (1 - η))`, `η = (B + 1)/q`. -/
theorem HL_domL_real (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, x < min k (s - 1) → 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 < q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q)
    (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q))
        (Real.sqrt 2 * (1 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((HLpoint s q k u v lam gco dg x c : ℤ) - (HLpoint s q k u v lam gco dg y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) :=
  Proofs.HL_domL_real_core s q k u v lam gco dg F2 hs hq hden hqodd hF2 hhalf0 hhalf hdiag hdom hqB hk x y hxy

/-- **Theorem HL, upper bound** (`thm:HL`). For the design `H_s`, every `s ≥ 3`, every prime
`q ≥ 2s` with `q > 4 s C_s + 2` (`2C_s = CH2 s = max_c 2a_c`) and every `k ≥ 1` there are two
distinct points at Euclidean (hence toroidal) distance at most
`(min(√s/2, √2) + √s (2C_s + 1)/q) N^(-1/s)`. -/
theorem HL_upper (s q k : ℕ) (hs : 3 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q)
    (hqC : 2 * s * CH2 s + 2 < q) (hk : 1 ≤ k) :
    ∃ x y : Fin (s * k) → ZMod q, x ≠ y ∧
      Real.sqrt (∑ c, (((HLpoint s q k uH vH (lamH s) gcoH (dgH s) x c : ℝ) -
          (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y c : ℝ)) / (q : ℝ) ^ (s * k)) ^ 2)
        ≤ (min (Real.sqrt s / 2) (Real.sqrt 2) + Real.sqrt s * ((CH2 s : ℝ) + 1) / q) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) :=
  Proofs.HL_upper_core s q k hs hq hqs hqC hk

/-- **Theorem HL, the limit** (`thm:HL`, last sentence): `δ N^(1/s) → min(√s/2, √2)` as the
prime `q → ∞`, uniformly in `k`: for every `ε > 0` there is `P` such that for every prime
`q ≥ P` and every `k ≥ 1` all distinct points have toroidal distance `≥ (min - ε) N^(-1/s)`, and
some two distinct points have Euclidean distance `≤ (min + ε) N^(-1/s)`. -/
theorem HL_limit (s : ℕ) (hs : 3 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ q k : ℕ, q.Prime → P ≤ q → 1 ≤ k →
      (∀ x y : Fin (s * k) → ZMod q, x ≠ y →
        (min (Real.sqrt s / 2) (Real.sqrt 2) - ε) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
          ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
              ((HLpoint s q k uH vH (lamH s) gcoH (dgH s) x c : ℤ) -
                (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2)) ∧
      ∃ x y : Fin (s * k) → ZMod q, x ≠ y ∧
        Real.sqrt (∑ c, (((HLpoint s q k uH vH (lamH s) gcoH (dgH s) x c : ℝ) -
            (HLpoint s q k uH vH (lamH s) gcoH (dgH s) y c : ℝ)) / (q : ℝ) ^ (s * k)) ^ 2)
          ≤ (min (Real.sqrt s / 2) (Real.sqrt 2) + ε) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) :=
  Proofs.HL_limit_core s hs ε hε

/-- **Growth of `B_s`** (`thm:HL`, `B_s = e^(O(s² log s))`): for every `s ≥ 2`,
`B_s ≤ 6 (s-1) (2s-1)^((s-1)²) + 2` and `B_s ≤ (2s)^(s²) = e^(s² log 2s)`. -/
theorem HL_Bbound (s : ℕ) (hs : 2 ≤ s) :
    BH s ≤ 6 * (s - 1) * (2 * s - 1) ^ ((s - 1) ^ 2) + 2 ∧ BH s ≤ (2 * s) ^ (s ^ 2) :=
  Proofs.HL_Bbound_core s hs

end Z3NetHL

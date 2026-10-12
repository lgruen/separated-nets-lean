#!/usr/bin/env python3
"""Statement-library delta after V14 stage S1 (the research notes), read by `gen_v14_statements.py`,
`check_statements.py` and `check_statement_identity.py`.

* CHANGED: compared theorems whose statement changed after S1 (name -> new docstring and text, proof
  `sorry`; namespace and `open`s unchanged). They are exempt from the stage-13c byte comparison and
  are compared with the text here instead; the identity check skips them (their constants are dumped
  into the next baseline).
* NEW: compared theorems added after S1, each with its statement file, its paper label (for the
  order within the file), namespace, `open`s, docstring and text.
* EXTRA_MODS: proof-side `*Defs` modules a statement file imports in addition to those of S0.
* EXTRA_SOLUTION: proof modules the Solution root imports in addition to those of S0.
* DROP_SOLUTION: S0 Solution imports dropped although they restate no theorem (stage S9′).

Stage S16′: the legacy rename (`scripts/v16_rename.py`): the namespace and modules `EisensteinNet` of the texts
below are now `QUNetsM3` (the research notes); `DROP_SOLUTION` keeps the old root name (a stage-13c import).

Stage S2 (2026-10-12): `lem:Ss` for every k ≥ 1 (`Ss_coord`, `Ss_sep`, `D_sep` restated with
`1 ≤ k`); `def:K`, `prop:Dprime`, `prop:k1` (1), (2) (statement review: the statement-review notes (research repository)).
"""

STAGE = {}  # name -> stage that changed / added it

CHANGED = {}
NEW = []
EXTRA_MODS = {}
EXTRA_SOLUTION = []
DROP_SOLUTION = []


def _chg(stage, name, doc, body):
    CHANGED[name] = dict(doc=doc.strip('\n'), body=body.strip('\n'))
    STAGE[name] = stage


def _new(stage, name, file, label, ns, opens, doc, body):
    NEW.append(dict(name=name, file=file, label=label, ns=ns, opens=tuple(opens),
                    doc=doc.strip('\n'), body=body.strip('\n')))
    STAGE[name] = stage


# ---------------------------------------------------------------- stage S2: changed (k ≥ 2 → k ≥ 1)
_chg('S2', 'Z3NetF.Ss_coord', r'''
/-- **`lem:Ss`**, the coordinate bounds, every `k ≥ 1`. Let a digital net over `ℤ/qℤ` be in graph form
with depths `(k, …, k)` satisfying (H1), (H2), and let the cells of `w` be the toroidal neighbours
`n + e` of those of `v`, with carry lengths `j`. Then `q |Δ_i| ≥ b_i` for every `i`, where
`q^(m-k) Δ_i = e_i q^(m-k) + (X_i(w) mod q^(m-k)) - (X_i(v) mod q^(m-k))` (cell units). -/
''', r'''
theorem Ss_coord {s q k L : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (F : ℕ → Fin s → Fin s → ℤ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (h1 : H1 F L Φ) (h2 : H2 Φ) (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ)
    (he : ∀ d, -1 ≤ e d ∧ e d ≤ 1)
    (hcell : ∀ d, ((digPoint q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) w d /
        q ^ (s * k - k) : ℕ) : ℤ) = ((digPoint q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) v d /
        q ^ (s * k - k) : ℕ) + e d) % (q ^ k : ℕ))
    (i : Fin s) :
    bval q F L e (fun d => carryLen q k (digPoint q (s * k) (graphGenK (m := s * k)
        (fun _ => k) Φ) v d / q ^ (s * k - k)) (e d)) i * (q ^ (s * k - k) : ℕ) ≤
      (q : ℤ) * |e i * (q ^ (s * k - k) : ℕ) +
        ((digPoint q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) w i % q ^ (s * k - k) : ℕ) : ℤ) -
        ((digPoint q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) v i % q ^ (s * k - k) : ℕ) : ℤ)| := by
  sorry
''')

_chg('S2', 'Z3NetF.Ss_sep', r'''
/-- **`lem:Ss`**, the separation, every `k ≥ 1` (at `k = 1` the torus has period `q ≥ 3` cells; the
toroidal case split of the proof): `δ q^k ≥ LB = min(1, min_{e,j} (∑_i b_i²)^(1/2)/q)`, in the
integer form: for every `B ≤ q²` with `B ≤ ∑_i b_i²` for all steps `(e, j)`,
`q^(2(m-k)) B ≤ q² D²` for any two distinct points (`D²` the squared toroidal distance times
`N²`, `N = q^m`, `m = s k`). -/
''', r'''
theorem Ss_sep {s q k L : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (F : ℕ → Fin s → Fin s → ℤ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (h1 : H1 F L Φ) (h2 : H2 Φ) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, IsConfig k e j → B ≤ ∑ i, bval q F L e j i ^ 2)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * k)) (digPoint q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) v)
        (digPoint q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) w) : ℤ) := by
  sorry
''')

_chg('S2', 'Z3NetF.D_sep', r'''
/-- **`prop:D`** applied to `𝒫^F_{k,q}` (the step of `thm:U`, for an arbitrary dominant reachable
design with integer entries): for `q ≥ 5a+4`, every `k ≥ 1` and distinct indices,
`q^(2(sk-k)) (q - a)² ≤ q² D²`, i.e. `δ ≥ (1 - a/q) N^(-1/s)`. -/
''', r'''
theorem D_sep {R : Type*} [CommRing R] {s q a : ℕ} [NeZero q] (hs : 2 ≤ s) (ψ : R →+* ZMod q)
    (k : ℕ) (hk : 1 ≤ k) (inf : Fin s) (x : Fin s → R) (hx : PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : BetaRel inf x (fun n c d => (F n c d : R)) lam β)
    (α : Fin s → ℕ) (h0 : ∀ c, F 0 c c = -(α c : ℤ)) (hdiag : ∀ n c, 1 ≤ n → F n c c = 0)
    (hdom : ∀ c, ∑ d ∈ univ.filter (fun d => d ≠ c),
      (range (s - 1)).sup (fun j => (Msum F j c d).natAbs) ≤ α c)
    (ha : ∀ c, α c ≤ a) (hq : 5 * a + 4 ≤ q) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - a) ^ 2 ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * k))
        (digPoint q (s * k) (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) v)
        (digPoint q (s * k) (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) w) : ℤ) := by
  sorry
''')

# ---------------------------------------------------------------- stage S2: new (`sec:deficit`, `sec:k1`)
_F = ('Deficit', 'Z3NetF', ['open Matrix Finset'])
EXTRA_MODS['Deficit'] = ['Z3Net.DeficitDefs']
EXTRA_SOLUTION.append('Z3Net.DeficitMain')

_new('S2', 'Z3NetF.Kdef_ne_top_iff', _F[0], 'def:K', _F[1], _F[2], r'''
/-- **`def:K`** (with `rem:K`): the deficit `K(F)` of a design with `L ≥ 1` levels is finite iff every
own partial sum `M^(j)[a][a]` (`j < L`) is `≤ 0` and every multi-axis configuration has a backward
coordinate (configurations with `k ≥ L` cell levels; `σ` caps the carry lengths at `L - 1`). -/
''', r'''
theorem Kdef_ne_top_iff {s L k : ℕ} (hL : 1 ≤ L) (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ) :
    Kdef F L ≠ ⊤ ↔ (∀ a, ∀ j < L, Msum F j a a ≤ 0) ∧
      ∀ e j, IsConfig k e j → 2 ≤ (moving e).card → ∃ i, e i ≠ 0 ∧ e i * sigma F L e j i ≤ 0 := by
  sorry
''')

_new('S2', 'Z3NetF.Kdef_eq_Kexp', _F[0], 'def:K', _F[1], _F[2], r'''
/-- **`def:K`** (with `rem:K`): a finite deficit `K(F)` equals the constant `Kexp` of `rem:K`, the
maximum of the `|M^(j)[a][a]|` (`j < L`) and of `|σ_b| + 1` over the multi-axis configurations with a
single backward coordinate `b` (for any number `k ≥ L` of cell levels). -/
''', r'''
theorem Kdef_eq_Kexp {s L k : ℕ} (hL : 1 ≤ L) (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ)
    (h : Kdef F L ≠ ⊤) : Kdef F L = (Kexp F L k : WithTop ℕ) := by
  sorry
''')

_new('S2', 'Z3NetF.K_expansion', _F[0], 'def:K', _F[1], _F[2], r'''
/-- **`def:K`**, the constant of `rem:K` made a definition: if `K(F) = K < ∞`, the relaxation of
`lem:Ss` satisfies `LB = 1 - K/q + O(q⁻²)` (`k ≥ L` cell levels). -/
''', r'''
theorem K_expansion {s L k K : ℕ} (hs : 1 ≤ s) (hL : 1 ≤ L) (hLk : L ≤ k)
    (F : ℕ → Fin s → Fin s → ℤ) (hK : Kdef F L = (K : WithTop ℕ)) :
    ∃ C : ℝ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      1 - (K : ℝ) / q ≤ LBval q F L k ∧ LBval q F L k ≤ 1 - (K : ℝ) / q + C / (q : ℝ) ^ 2 := by
  sorry
''')

_new('S2', 'Z3NetF.Dprime_LB', _F[0], 'prop:Dprime', _F[1], _F[2], r'''
/-- **`prop:Dprime`**, integer form: let `F` have `L` levels, `K = K(F) < ∞` and `S = S(F)`. For every
`q ≥ Q_D(K, S)`, `B = (q - K)²` bounds `q²` and `∑_i b_i²` for every configuration of `lem:Ss` (any
number `k` of cell levels) of `F` or of any truncation `(F_0, …, F_{L'-1})`, `1 ≤ L' ≤ L`; i.e.
`LB ≥ 1 - K/q` (`B` is a valid hypothesis of `Ss_sep`). -/
''', r'''
theorem Dprime_LB {s q L L' k K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (hL' : 1 ≤ L') (hL'L : L' ≤ L)
    (hK : Kdef F L = (K : WithTop ℕ)) (hq : QD K (Sdef F L) ≤ q) :
    ((q : ℤ) - K) ^ 2 ≤ (q : ℤ) ^ 2 ∧
      ∀ e j, IsConfig k e j → ((q : ℤ) - K) ^ 2 ≤ ∑ i, bval q F L' e j i ^ 2 := by
  sorry
''')

_new('S2', 'Z3NetF.Dprime', _F[0], 'prop:Dprime', _F[1], _F[2], r'''
/-- **`prop:Dprime`**: let `F` have `L` levels, `K = K(F) < ∞` and `S = S(F)`. Then
`LB ≥ 1 - K/q` for every `q ≥ Q_D(K, S)`, where `LB` is the relaxation of `lem:Ss` for `F` or for any
truncation `(F_0, …, F_{L'-1})`, `1 ≤ L' ≤ L` (any number `k` of cell levels). -/
''', r'''
theorem Dprime {s q L L' k K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (hL' : 1 ≤ L') (hL'L : L' ≤ L)
    (hK : Kdef F L = (K : WithTop ℕ)) (hq : QD K (Sdef F L) ≤ q) :
    1 - (K : ℝ) / q ≤ LBval q F L' k := by
  sorry
''')

_new('S2', 'Z3NetF.Dprime_sep', _F[0], 'prop:Dprime', _F[1], _F[2], r'''
/-- **`prop:Dprime`** applied to `𝒫^F_{k,q}` (as `D_sep`, without the dominance hypothesis): for a
design reachable by the frame with `K(F) = K < ∞` for its `s - 1` levels, `q ≥ Q_D(K, S(F))`,
`q ≥ 3` and every `k ≥ 1`, `q^(2(sk-k)) (q - K)² ≤ q² D²` for distinct indices, i.e.
`δ ≥ (1 - K/q) N^(-1/s)`. -/
''', r'''
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
        (digPoint q (s * k) (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) w) : ℤ) := by
  sorry
''')

_new('S2', 'Z3NetF.k1_sep', _F[0], 'prop:k1', _F[1], _F[2], r'''
/-- **`prop:k1`(1)**: let `q ≥ 3` and let a digital net over `ℤ/qℤ` be in graph form with depths
`(1, …, 1)` (`m = s`, `N = q^s`) whose first offset rows form the integer matrix `F₀` (diagonal
included, reduced modulo `q`) and whose deeper rows vanish in their own column ((H2)). Then
`δ N^{1/s} ≥ LB₁(q)` for the toroidal distance, `LB₁(q)` the relaxation of `lem:Ss` for the design
`(F₀)` (`L = 1`, `σ = F₀ e`). -/
''', r'''
theorem k1_sep {s q : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    LBval q (layer1 F₀) 1 1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) ≤
      Real.sqrt (∑ c, ((cres (q ^ (s * 1))
        ((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℤ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℤ)) : ℝ) /
          (q : ℝ) ^ (s * 1)) ^ 2) := by
  sorry
''')

_new('S2', 'Z3NetF.k1_sep_eucl', _F[0], 'prop:k1', _F[1], _F[2], r'''
/-- **`prop:k1`(1)**, "hence Euclidean": under the hypotheses of `k1_sep`, `δ N^{1/s} ≥ LB₁(q)` for
the Euclidean distance. -/
''', r'''
theorem k1_sep_eucl {s q : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    LBval q (layer1 F₀) 1 1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) ≤
      Real.sqrt (∑ c, (((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℝ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℝ)) /
          (q : ℝ) ^ (s * 1)) ^ 2) := by
  sorry
''')

_new('S2', 'Z3NetF.k1_tail', _F[0], 'prop:k1', _F[1], _F[2], r'''
/-- **`prop:k1`(1)**, the tail: `LB₁(q) ≥ 1 - K₁/q` for `q ≥ Q_D(K₁, S₁)`, where `K₁ = K((F₀))`,
`S₁ = S((F₀))` (`def:K`). -/
''', r'''
theorem k1_tail {s q K₁ : ℕ} (F₀ : Fin s → Fin s → ℤ)
    (hK : Kdef (layer1 F₀) 1 = (K₁ : WithTop ℕ)) (hq : QD K₁ (Sdef (layer1 F₀) 1) ≤ q) :
    1 - (K₁ : ℝ) / q ≤ LBval q (layer1 F₀) 1 1 := by
  sorry
''')

_new('S2', 'Z3NetF.k1_transfer', _F[0], 'prop:k1', _F[1], _F[2], r'''
/-- **`prop:k1`(2)**: `LB₁(q)`, the relaxation of the one-level design `(F_0)`, is at least the
relaxation of the design `F` with `L` levels at the same `q`, for every number `k ≥ 1` of cell
levels. -/
''', r'''
theorem k1_transfer {s q L k : ℕ} (hk : 1 ≤ k) (F : ℕ → Fin s → Fin s → ℤ) :
    LBval q F L k ≤ LBval q (layer1 (F 0)) 1 1 := by
  sorry
''')

_new('S2', 'Z3NetF.k1_Ns_sep', _F[0], 'prop:k1', _F[1], _F[2], r'''
/-- **`prop:k1`(2)**: for a design `F` realized by `def:Ns` at one cell level (`𝒫^F_{1,q}`, `m = s`),
every lower bound `B` proved through `lem:Ss` for `F` (with any `L` levels and `k' ≥ 1` cell
levels) holds: `q^(2(s-1)) B ≤ q² D²` for distinct indices. So the lower bounds of `prop:D`
(`D_LB`) and `prop:Dprime` (`Dprime_LB`) hold at `k = 1`. -/
''', r'''
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
        (digPoint q (s * 1) (fun c => (PGen 1 inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) w) : ℤ) := by
  sorry
''')

_new('S2', 'Z3NetF.k1designs_frame_K', _F[0], 'prop:k1designs', _F[1], _F[2], r'''
/-- **`prop:k1designs`(1)**, the deficits (computer-assisted: kernel `decide`): the level-0 frame
layers of `tab:practical` as printed in `app:designs` (`s = 4`: the off-diagonal part of `U*_4`;
`s = 5`: that of the `s = 5` design of `tab:Kdesigns`; diagonals chosen for `k = 1`; `s = 6`:
searched scalars) have `K₁ = K((F₀)) = 2, 3, 6` (`def:K`). -/
''', r'''
theorem k1designs_frame_K :
    Kdef (layer1 k1Frame4) 1 = 2 ∧ Kdef (layer1 k1Frame5) 1 = 3 ∧ Kdef (layer1 k1Frame6) 1 = 6 := by
  sorry
''')

_new('S2', 'Z3NetF.k1designs_frame6_cauchy', _F[0], 'prop:k1designs', _F[1], _F[2], r'''
/-- **`prop:k1designs`(1)**, the `s = 6` layer is a Cauchy layer: on the places `∞, 0, 1, 2, 3, 4`
(admissible), its off-diagonal entries are `λ'_c μ_d w_cd` (`w_cd` of `prop:Ns`) with the row and
column scalars `λ' = (1, 2/3, -2, -2/3, 2/3, -2)`, `μ = (3/2, 18, 3, 3, 9, 6)` of `app:designs`. -/
''', r'''
theorem k1designs_frame6_cauchy :
    PlacesOK (0 : Fin 6) k1Places6 ∧
      ∀ c d : Fin 6, c ≠ d → (k1Frame6 c d : ℚ) = k1Lam6 c * k1Mu6 d * wN (0 : Fin 6) k1Places6 c d := by
  sorry
''')

_new('S2', 'Z3NetF.k1designs_free_K', _F[0], 'prop:k1designs', _F[1], _F[2], r'''
/-- **`prop:k1designs`(2)** and `tab:practical`, the deficits of the free layers (computer-assisted:
kernel `decide`): the free layers of `app:designs` have `K₁ = 2` (`s = 5`), `3` and `5` (`s = 6`),
and the first two have entries of absolute value at most `3`. (The `t = 0` completions and the
separation scans of `prop:k1designs`(2) are not part of this statement.) -/
''', r'''
theorem k1designs_free_K :
    Kdef (layer1 k1Free5) 1 = 2 ∧ Kdef (layer1 k1Free6a) 1 = 3 ∧ Kdef (layer1 k1Free6b) 1 = 5 ∧
      (∀ c d, |k1Free5 c d| ≤ 3) ∧ (∀ c d, |k1Free6a c d| ≤ 3) := by
  sorry
''')

# ---------------------------------------------------------------- stage S3: new (`thm:A` part I, `lem:sat`, `def:Ustar`)
# Statement review: the statement-review notes (research repository). Definitions: `Z3Net/ThmADefs.lean`; proofs `Z3Net/ThmASat.lean`,
# `ThmAUstar.lean`, `ThmACover.lean`, `ThmAThm.lean`; restatements `Z3Net/ThmAMain.lean`.
_A = ('ThmA', 'Z3NetA', ['open Matrix Finset Z3NetF'])
EXTRA_MODS['ThmA'] = ['Z3Net.ThmADefs']
EXTRA_SOLUTION.append('Z3Net.ThmAMain')

_new('S3', 'Z3NetA.A_hom', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`**, the reduction modulo `q`: for `s ≥ 3` and every `q ≥ 2` all of whose prime factors
are at least `s - 1` (`AdmBase s q`), there is a ring homomorphism `R_S = ℤ[1/(s-2)!] → ℤ/qℤ`, and
it is unique. (`Apoint` reduces the net of `def:Ns` over `R_S` by it.) -/
''', r'''
theorem A_hom (s q : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) :
    Nonempty (RS s →+* ZMod q) ∧ ∀ ψ ψ' : RS s →+* ZMod q, ψ = ψ' := by
  sorry
''')

_new('S3', 'Z3NetA.A_net', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`(1)**, the net: for every `s ≥ 3`, every `q ≥ 2` all of whose prime factors are at least
`s - 1` and every `k ≥ 1`, the net `𝒫^{U*_s}_{k,q}` (`Apoint`: the net of `def:Ns` for the places
`∞, 0, 1, …, s-2` and the design `U*_s` of `def:Ustar`, `N = q^(sk)` points) is a digital
`(0,sk,s)`-net over `ℤ/qℤ`; with `d = (k, …, k)` every cell `∏_i [n_i q^(-k), (n_i+1) q^(-k))`
holds exactly one point. -/
''', r'''
theorem A_net (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hk : 1 ≤ k) :
    IsNet0 s q (s * k) (Apoint s q k) := by
  sorry
''')

_new('S3', 'Z3NetA.A_covering', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`(1)**, the covering radius `h ≤ √s N^(-1/s)`: every `x ∈ [0,1]^s` has a point of
`𝒫^{U*_s}_{k,q}` at Euclidean distance at most `√s q^(-k) = √s N^(-1/s)` (`N = q^(sk)`). -/
''', r'''
theorem A_covering (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hk : 1 ≤ k)
    (x : Fin s → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (s * k) → ZMod q,
      ∑ c, (x c - (Apoint s q k v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤ (s : ℝ) / ((q : ℝ) ^ k) ^ 2 := by
  sorry
''')

_new('S3', 'Z3NetA.A_sep', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`(2)**, the lower bound, exact integer form: for `q ≥ 5 a*_s + 4` (and `q` as in (1)), every
`k ≥ 1` and distinct indices `v ≠ w`, with `N = q^(sk)` and `D² = torusDist2 N X(v) X(w)` (the squared
toroidal distance times `N²`): `q^(2(sk-k)) (q - a*_s)² ≤ q² D²`, i.e. `δ ≥ (1 - a*_s/q) N^(-1/s)`.
(`a*_s = aStar s` is the constant of `def:Ustar`; its bound is stage S5.) -/
''', r'''
theorem A_sep (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hqa : 5 * aStar s + 4 ≤ q)
    (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aStar s) ^ 2 ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (s * k)) (Apoint s q k v) (Apoint s q k w) : ℤ) := by
  sorry
''')

_new('S3', 'Z3NetA.A_sep_real', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`(2)**, the lower bound, real toroidal form: for `q ≥ 5 a*_s + 4` and every `k ≥ 1`, the
toroidal distance between any two distinct points of `𝒫^{U*_s}_{k,q}` (points `X / N` in `[0,1)^s`,
`N = q^(sk)`) is at least `(1 - a*_s/q) N^(-1/s)`. -/
''', r'''
theorem A_sep_real (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) := by
  sorry
''')

_new('S3', 'Z3NetA.A_sep_eucl', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`(2)**, the lower bound, Euclidean form ("hence also Euclidean"): for `q ≥ 5 a*_s + 4` and
every `k ≥ 1`, the Euclidean distance between any two distinct points of `𝒫^{U*_s}_{k,q}` is at least
`(1 - a*_s/q) N^(-1/s)`. -/
''', r'''
theorem A_sep_eucl (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2) := by
  sorry
''')

_new('S3', 'Z3NetA.covering_of_net', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`(1)**, the covering argument for any net: if the integer points `X v` (scale `N = q^(sk)`,
`q ≥ 2`, `s ≥ 1`) form a `(0,sk,s)`-net, so that every cell of side `q^(-k)` holds a point, every
`x ∈ [0,1]^s` is within Euclidean distance `√s q^(-k)` of a point. -/
''', r'''
theorem covering_of_net {s q k : ℕ} (hs : 1 ≤ s) (hq : 2 ≤ q)
    (X : (Fin (s * k) → ZMod q) → Fin s → ℕ) (hX : IsNet0 s q (s * k) X) (x : Fin s → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v, ∑ c, (x c - (X v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤ (s : ℝ) / ((q : ℝ) ^ k) ^ 2 := by
  sorry
''')

_new('S3', 'Z3NetA.Ustar_adm', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`**, proof, reachability: every column of partial sums of `U*_s` is admissible: for every
column `d` and level `j ≤ s - 2`, `(M^(j)[c][d])_{c ≠ d}` (`0` at the row `d`) is admissible at level
`j` (`AdmCol`, i.e. `prop:F` with `λ' ≡ 1` over `R_S`; `lem:sat`(iii)). -/
''', r'''
theorem Ustar_adm {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    AdmCol d j (fun c => if c = d then 0 else Msum (UstarF s) j c d) := by
  sorry
''')

_new('S3', 'Z3NetA.Ustar_reach', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`**, proof, reachability: over `R_S = ℤ[1/(s-2)!]` the places `∞, 0, 1, …, s-2` are
admissible (`PlacesOK`) and the residual problem of `U*_s` is solvable with `λ' ≡ 1` (by `prop:F`,
`F_poly_iff`). -/
''', r'''
theorem Ustar_reach {s : ℕ} [NeZero s] (hs : 3 ≤ s) :
    PlacesOK (0 : Fin s) (placeA : Fin s → RS s) ∧
      ∃ Ur : Fin s → ℕ → ℕ → RS s, Residual (0 : Fin s) placeA (UstarR s) 1 Ur := by
  sorry
''')

_new('S3', 'Z3NetA.Ustar_data', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`**, the data of the net `Apoint`: the chosen `U' = UrS s` solves the residual problem of
`U*_s` with `λ' ≡ 1`, and the chosen `β = betaS s` the defining relation of `prop:Gs`; so `Apoint` is
the net `𝒫^F_{k,q}` of `def:Ns` for `F = U*_s`. -/
''', r'''
theorem Ustar_data {s : ℕ} [NeZero s] (hs : 3 ≤ s) :
    Residual (0 : Fin s) placeA (UstarR s) 1 (UrS s) ∧
      BetaRel (0 : Fin s) placeA (UstarR s) 1 (betaS s) := by
  sorry
''')

_new('S3', 'Z3NetA.sat_poly', _A[0], 'lem:sat', _A[1], _A[2], r'''
/-- **`lem:sat`(i)**: let `s ≥ 3`, `d` a column and `j ≤ s - 2`. The polynomial `g` of degree `≤ j`
of an integer column `E` (`E_c = w_c g(y_c)` for the rows `c ≠ d`; in particular for `E ∈ Λ_j`) has
all its coefficients in `R_S = ℤ[1/(s-2)!]`. -/
''', r'''
theorem sat_poly {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (E : Fin s → ℤ) (g : Polynomial ℚ) (hg : g.natDegree ≤ j)
    (hrep : ∀ c, c ≠ d → (E c : ℚ) = wQ c d * g.eval (yQ c d)) (i : ℕ) : InRS s (g.coeff i) := by
  sorry
''')

_new('S3', 'Z3NetA.sat_gamma', _A[0], 'lem:sat', _A[1], _A[2], r'''
/-- **`lem:sat`(ii)**: `κ_j(Λ_j) = γ_j ℤ` for a positive `S`-unit `γ_j` (`gamS d j`), for every
column `d` and `j ≤ s - 2`. -/
''', r'''
theorem sat_gamma {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    0 < gamS d j ∧ SUnit s (gamS d j) ∧
      ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * gamS d j := by
  sorry
''')

_new('S3', 'Z3NetA.sat_adm', _A[0], 'lem:sat', _A[1], _A[2], r'''
/-- **`lem:sat`(iii)**: an integer column is admissible at level `j` iff it lies in `Λ_j` and
`κ_j(E)` is an `S`-unit; in particular every `E ∈ Λ_j` with `κ_j(E) = γ_j` is admissible. -/
''', r'''
theorem sat_adm {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (E : Fin s → ℤ) :
    (AdmCol d j E ↔ InLam d j E ∧ SUnit s (kappa d j E)) ∧
      (InLam d j E → kappa d j E = gamS d j → AdmCol d j E) := by
  sorry
''')

_new('S3', 'Z3NetA.sat_basis', _A[0], 'lem:sat', _A[1], _A[2], r'''
/-- **`lem:sat`(iv)**, the basis: if `E_i ∈ Λ_i` and `κ_i(E_i) = γ_i` for `i = 0, …, j`
(`j ≤ s - 2`), then `E_0, …, E_j` is a basis of `Λ_j`: every element of `Λ_j` is a unique integer
combination of them, and every such combination lies in `Λ_j`. -/
''', r'''
theorem sat_basis {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (B : ℕ → Fin s → ℤ) (hB : ∀ i ≤ j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i) :
    (∀ F, InLam d j F ↔ ∃ t : ℕ → ℤ, F = ∑ i ∈ range (j + 1), t i • B i) ∧
      ∀ t t' : ℕ → ℤ, ∑ i ∈ range (j + 1), t i • B i = ∑ i ∈ range (j + 1), t' i • B i →
        ∀ i ≤ j, t i = t' i := by
  sorry
''')

_new('S3', 'Z3NetA.sat_coset', _A[0], 'lem:sat', _A[1], _A[2], r'''
/-- **`lem:sat`(iv)**, the coset: under the hypotheses of `sat_basis`,
`{E ∈ Λ_j : κ_j(E) = γ_j} = E_j + Λ_{j-1}` with `Λ_{j-1} = ⊕_{i<j} ℤ E_i` (`Λ_{-1} = 0`). -/
''', r'''
theorem sat_coset {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (B : ℕ → Fin s → ℤ) (hB : ∀ i ≤ j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i)
    (F : Fin s → ℤ) :
    (InLam d j F ∧ kappa d j F = gamS d j) ↔ ∃ t : ℕ → ℤ, F - B j = ∑ i ∈ range j, t i • B i := by
  sorry
''')

_new('S3', 'Z3NetA.Ustar_cols', _A[0], 'def:Ustar', _A[1], _A[2], r'''
/-- **`def:Ustar`**, existence: for `s ≥ 3` and every column `d`, the columns `E_{d,j} = Ecol d j`
have the characterizing properties of `def:Ustar` (`IsUstarCols`): `E_{d,j} ∈ Λ_j`,
`κ_j(E_{d,j}) = +γ_j`, and the coefficients of the orthogonal projection of `E_{d,j}` onto the span of
`E_{d,0}, …, E_{d,j-1}` in these vectors lie in `[-1/2, 1/2)` (`j ≤ s - 2`). -/
''', r'''
theorem Ustar_cols {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) : IsUstarCols d (Ecol d) := by
  sorry
''')

_new('S3', 'Z3NetA.Ustar_cols_unique', _A[0], 'def:Ustar', _A[1], _A[2], r'''
/-- **`def:Ustar`**, uniqueness: the family with these properties is unique. -/
''', r'''
theorem Ustar_cols_unique {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (B : ℕ → Fin s → ℤ)
    (hB : IsUstarCols d B) : B = Ecol d := by
  sorry
''')

_new('S3', 'Z3NetA.Ustar_round', _A[0], 'def:Ustar', _A[1], _A[2], r'''
/-- **`def:Ustar`**, independence of `v`: for every `v ∈ Λ_j` with `κ_j(v) = γ_j` (`j ≤ s - 2`) the
coefficients `c_i` of the orthogonal projection of `v` onto the span of `E_{d,0}, …, E_{d,j-1}` exist,
and for any such coefficients `E_{d,j} = v - ∑_{i<j} ⌊c_i + 1/2⌋ E_{d,i}` (the vector of `lem:babai`,
ties rounded up). -/
''', r'''
theorem Ustar_round {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (v : Fin s → ℤ) (hv : InLam d j v) (hvk : kappa d j v = gamS d j) :
    (∃ cf : ℕ → ℚ, ProjCoef (Ecol d) j v cf) ∧
      ∀ cf : ℕ → ℚ, ProjCoef (Ecol d) j v cf →
        Ecol d j = v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • Ecol d i := by
  sorry
''')

_new('S3', 'Z3NetA.Ustar_Msum', _A[0], 'def:Ustar', _A[1], _A[2], r'''
/-- **`def:Ustar`**: the design `U*_s` has the partial sums `M^(j)[c][d] = E_{d,j}[c]` (`c ≠ d`,
`j ≤ s - 2`). -/
''', r'''
theorem Ustar_Msum {s : ℕ} [NeZero s] (hs : 3 ≤ s) (c d : Fin s) (hcd : c ≠ d) (j : ℕ)
    (hj : j ≤ s - 2) : Msum (UstarF s) j c d = Ecol d j c := by
  sorry
''')

_new('S3', 'Z3NetA.Ustar_dominant', _A[0], 'def:Ustar', _A[1], _A[2], r'''
/-- **`def:Ustar`** and the proof of `thm:A`(2): `U*_s` is diagonally dominant (`prop:D`) by
construction, with the maximum over all levels: `F_0[c][c] = -α_c`, the deeper diagonal vanishes,
`α_c = ∑_{d ≠ c} max_{j ≤ s-2} |M^(j)[c][d]|`, and `α_c ≤ a*_s = max_c α_c`. -/
''', r'''
theorem Ustar_dominant {s : ℕ} [NeZero s] (hs : 3 ≤ s) (c : Fin s) :
    UstarF s 0 c c = -(alphaS c : ℤ) ∧ (∀ n, 1 ≤ n → UstarF s n c c = 0) ∧
      ∑ d ∈ univ.filter (fun d => d ≠ c),
          (range (s - 1)).sup (fun j => (Msum (UstarF s) j c d).natAbs) = alphaS c ∧
      alphaS c ≤ aStar s := by
  sorry
''')

_new('S3', 'Z3NetA.Ustar_span', _A[0], 'def:Ustar', _A[1], _A[2], r'''
/-- **`def:Ustar`**, the projection: for `j ≤ s - 2` the rational vectors of `V_j` (vanishing at the
row `d`, `E_c = w_c g(y_c)` for `c ≠ d` with `deg g ≤ j`) are exactly the rational combinations of
`E_{d,0}, …, E_{d,j}`; so the orthogonal projection onto `V_{j-1}` of `def:Ustar` is the projection
onto the span of `E_{d,0}, …, E_{d,j-1}` used in `IsUstarCols` and `ProjCoef`. -/
''', r'''
theorem Ustar_span {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (E : Fin s → ℚ) :
    (E d = 0 ∧ ∃ g : Polynomial ℚ, g.natDegree ≤ j ∧ ∀ c, c ≠ d → E c = wQ c d * g.eval (yQ c d)) ↔
      ∃ u : ℕ → ℚ, E = ∑ i ∈ range (j + 1), u i • fun c => (Ecol d i c : ℚ) := by
  sorry
''')

# ---------------------------------------------------------------- stage S4: new (`lem:adelic`, `lem:babai`, `U*_s`)
# Statement review: the statement-review notes (research repository). Definitions: `Z3Net/ThmALatDefs.lean`; proofs `Z3Net/ThmALat.lean`,
# `ThmAAdelic.lean`, `ThmABabai.lean`; restatements `Z3Net/ThmALatMain.lean`.
EXTRA_MODS['ThmA'].append('Z3Net.ThmALatDefs')
EXTRA_SOLUTION.append('Z3Net.ThmALatMain')

_new('S4', 'Z3NetA.adelic_p', _A[0], 'lem:adelic', _A[1], _A[2], r'''
/-- **`lem:adelic`**, the places `p`: for `s ≥ 3`, a column `d`, `j ≤ s - 2` and every prime `p`,
the least `p`-adic size `max_c |w_c g(y_c)|_p` of the vectors of the monic rational polynomials `g`
of degree `j` exists and is `p^{v_p(γ_j)}`, i.e. `A_{j,p} = p^{v_p(γ_j)}` (`= 1` for `p ∉ S`). -/
''', r'''
theorem adelic_p {s : ℕ} [NeZero s] (hs : 3 ≤ s) (p : ℕ) (hp : p.Prime) (d : Fin s) (j : ℕ)
    (hj : j ≤ s - 2) :
    IsLeast (ApSet p d j) ((p : ℝ) ^ padicValRat p (gamS d j)) ∧
      Ap p d j = (p : ℝ) ^ padicValRat p (gamS d j) := by
  sorry
''')

_new('S4', 'Z3NetA.adelic_gamma', _A[0], 'lem:adelic', _A[1], _A[2], r'''
/-- **`lem:adelic`**: `γ_j = ∏_{p ∈ S} A_{j,p}`, `S` the primes `p ≤ s - 2` (column `d`,
`j ≤ s - 2`). -/
''', r'''
theorem adelic_gamma {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    (gamS d j : ℝ) = ∏ p ∈ primesS s, Ap p d j := by
  sorry
''')

_new('S4', 'Z3NetA.adelic_inf', _A[0], 'lem:adelic', _A[1], _A[2], r'''
/-- **`lem:adelic`**, the place `∞`: there is a unique `θ ∈ V_j ⊗ ℝ` with `κ_j = ⟨θ, ·⟩` on
`V_j ⊗ ℝ` (`κ_j` of the vector `(w_c g(y_c))_c` of a real polynomial `g` of degree `≤ j` is the
coefficient of `X^j`; on `Λ_j` it is `kappa`); `θ ⊥ V_{j-1}`, `θ ≠ 0`, and
`A_{j,∞} = min {‖E‖₂ : E ∈ V_j ⊗ ℝ, κ_j(E) = 1} = 1/‖θ‖`, attained at `θ/‖θ‖²` (the vector of a monic
real polynomial of degree `j`). -/
''', r'''
theorem adelic_inf {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ∃ θ : EuclideanSpace ℝ (Fin s), θ ∈ Vlt d (j + 1) ∧ θ ∈ (Vlt d j)ᗮ ∧
      (∀ g : Polynomial ℝ, g.natDegree ≤ j → inner ℝ θ (polyVecR d g) = g.coeff j) ∧
      (∀ E : Fin s → ℤ, InLam d j E → inner ℝ θ (colE E) = kappa d j E) ∧
      (∀ θ' ∈ Vlt d (j + 1),
        (∀ g : Polynomial ℝ, g.natDegree ≤ j → inner ℝ θ' (polyVecR d g) = g.coeff j) → θ' = θ) ∧
      θ ≠ 0 ∧ IsLeast (AinfSet d j) ‖θ‖⁻¹ ∧ Ainf d j = ‖θ‖⁻¹ ∧
      ∃ g : Polynomial ℝ, g.Monic ∧ g.natDegree = j ∧ polyVecR d g = (‖θ‖ ^ 2)⁻¹ • θ := by
  sorry
''')

_new('S4', 'Z3NetA.adelic_proj', _A[0], 'lem:adelic', _A[1], _A[2], r'''
/-- **`lem:adelic`**: `π_j(Λ_j)` is generated by a vector of length `h_j = A_{j,∞} ∏_{p ∈ S} A_{j,p}`:
there is a vector `u` of the line `V_j ∩ V_{j-1}^⊥` with `‖u‖₂ = h_j` and `π_j(Λ_j) = ℤ u` (`π_j` the
orthogonal projection of `ℝ^s` onto that line). -/
''', r'''
theorem adelic_proj {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ∃ u : EuclideanSpace ℝ (Fin s), u ∈ lineA d j ∧ ‖u‖ = hS d j ∧
      ∀ x, (∃ E : Fin s → ℤ, InLam d j E ∧ piA d j (colE E) = x) ↔ ∃ z : ℤ, x = (z : ℝ) • u := by
  sorry
''')

_new('S4', 'Z3NetA.adelic_norm', _A[0], 'lem:adelic', _A[1], _A[2], r'''
/-- **`lem:adelic`**: every `E ∈ Λ_j ∖ V_{j-1}` has `‖E‖₂ ≥ h_j`. -/
''', r'''
theorem adelic_norm {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (E : Fin s → ℤ) (hE : InLam d j E) (hnot : colE E ∉ Vlt d j) : hS d j ≤ ‖colE E‖ := by
  sorry
''')

_new('S4', 'Z3NetA.hS_le_monic', _A[0], 'lem:adelic', _A[1], _A[2], r'''
/-- **`lem:adelic`**, as used in the proof of `thm:A` ("it suffices to give, at each place, one monic
`g` of degree `j`"): for any monic real `g` of degree `j` and any monic rational `g_p` of degree `j`
(`p ∈ S`), `h_j ≤ ‖(w_c g(y_c))_c‖₂ · ∏_{p ∈ S} max_c |w_c g_p(y_c)|_p`. -/
''', r'''
theorem hS_le_monic {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (g : Polynomial ℝ) (hg : g.Monic) (hgd : g.natDegree = j) (gp : ℕ → Polynomial ℚ)
    (hgp : ∀ p ∈ primesS s, (gp p).Monic ∧ (gp p).natDegree = j) :
    hS d j ≤ ‖polyVecR d g‖ *
      ∏ p ∈ primesS s, ⨆ c, ((padicNorm p (polyVecQ d (gp p) c) : ℚ) : ℝ) := by
  sorry
''')

_new('S4', 'Z3NetA.babai', _A[0], 'lem:babai', _A[1], _A[2], r'''
/-- **`lem:babai`**: let `E_i ∈ Λ_i` with `κ_i(E_i) = γ_i` for `i < j` (`j ≤ s - 2`) and `v ∈ Λ_j` with
`κ_j(v) = γ_j`. The orthogonal projection of `v` onto `V_{j-1} ⊗ ℝ` can be written `∑_{i<j} c_i E_i`,
and for any such coefficients `E_j = v - ∑_{i<j} ⌊c_i + 1/2⌋ E_i` lies in `Λ_j`, has
`κ_j(E_j) = γ_j` and `‖E_j‖₂ ≤ h_j + ½ ∑_{i<j} ‖E_i‖₂`. -/
''', r'''
theorem babai {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (B : ℕ → Fin s → ℤ) (hB : ∀ i < j, InLam d i (B i) ∧ kappa d i (B i) = gamS d i)
    (v : Fin s → ℤ) (hv : InLam d j v) (hvk : kappa d j v = gamS d j) :
    (∃ cf : ℕ → ℝ, (Vlt d j).starProjection (colE v) = ∑ i ∈ range j, cf i • colE (B i)) ∧
      ∀ cf : ℕ → ℝ, (Vlt d j).starProjection (colE v) = ∑ i ∈ range j, cf i • colE (B i) →
        InLam d j (v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • B i) ∧
        kappa d j (v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • B i) = gamS d j ∧
        ‖colE (v - ∑ i ∈ range j, ⌊cf i + 1 / 2⌋ • B i)‖ ≤
          hS d j + 1 / 2 * ∑ i ∈ range j, ‖colE (B i)‖ := by
  sorry
''')

_new('S4', 'Z3NetA.babai_growth', _A[0], 'lem:babai', _A[1], _A[2], r'''
/-- **`lem:babai`**, the recursion of the consequence: if `x_i ≤ H + ½ ∑_{l<i} x_l` for every
`i ≤ j`, then `x_i ≤ (3/2)^i H` for every `i ≤ j` (in the proof, `T_i ≤ 2H((3/2)^{i+1} - 1)`). -/
''', r'''
theorem babai_growth (x : ℕ → ℝ) (H : ℝ) (j : ℕ)
    (hx : ∀ i ≤ j, x i ≤ H + 1 / 2 * ∑ l ∈ range i, x l) : ∀ i ≤ j, x i ≤ (3 / 2) ^ i * H := by
  sorry
''')

_new('S4', 'Z3NetA.babai_flag', _A[0], 'lem:babai', _A[1], _A[2], r'''
/-- **`lem:babai`**, the consequence: if `E_0, …, E_j` (`j ≤ s - 2`) are all obtained in this way
(each `E_i = v_i - ∑_{l<i} ⌊c_l + 1/2⌋ E_l` with `v_i ∈ Λ_i`, `κ_i(v_i) = γ_i` and `∑_{l<i} c_l E_l`
the orthogonal projection of `v_i` onto `V_{i-1} ⊗ ℝ`) and `h_i ≤ H` for every `i ≤ j`, then
`‖E_i‖₂ ≤ (3/2)^i H` for every `i ≤ j`. -/
''', r'''
theorem babai_flag {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (B : ℕ → Fin s → ℤ)
    (hB : ∀ i ≤ j, ∃ v : Fin s → ℤ, ∃ cf : ℕ → ℝ, InLam d i v ∧ kappa d i v = gamS d i ∧
      (Vlt d i).starProjection (colE v) = ∑ l ∈ range i, cf l • colE (B l) ∧
      B i = v - ∑ l ∈ range i, ⌊cf l + 1 / 2⌋ • B l)
    (H : ℝ) (hH : ∀ i ≤ j, hS d i ≤ H) : ∀ i ≤ j, ‖colE (B i)‖ ≤ (3 / 2) ^ i * H := by
  sorry
''')

_new('S4', 'Z3NetA.Ustar_proj', _A[0], 'def:Ustar', _A[1], _A[2], r'''
/-- **`def:Ustar`**, the projection: for `j ≤ s - 2`, rational coefficients `c` satisfy the
characterization `ProjCoef` of `IsUstarCols` for a column `E` iff `∑_{i<j} c_i E_{d,i}` is the
orthogonal projection of `E` onto `V_{j-1} ⊗ ℝ` (Mathlib's `Submodule.starProjection` in
`EuclideanSpace ℝ (Fin s)`), i.e. the projection of `def:Ustar`. -/
''', r'''
theorem Ustar_proj {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2)
    (E : Fin s → ℤ) (cf : ℕ → ℚ) :
    ProjCoef (Ecol d) j E cf ↔
      (Vlt d j).starProjection (colE E) = ∑ i ∈ range j, (cf i : ℝ) • colE (Ecol d i) := by
  sorry
''')

_new('S4', 'Z3NetA.Ustar_babai', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`**, proof of the bound on `a*_s` (with `def:Ustar` and `lem:babai`): the columns of
`U*_s` satisfy `‖E_{d,j}‖₂ ≤ h_{d,j} + ½ ∑_{i<j} ‖E_{d,i}‖₂` (`j ≤ s - 2`). -/
''', r'''
theorem Ustar_babai {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    ‖colE (Ecol d j)‖ ≤ hS d j + 1 / 2 * ∑ i ∈ range j, ‖colE (Ecol d i)‖ := by
  sorry
''')

_new('S4', 'Z3NetA.Ustar_growth', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`**, proof of the bound on `a*_s`: if `h_{d,i} ≤ H` for every `i ≤ j` (`j ≤ s - 2`), then
`‖E_{d,i}‖₂ ≤ (3/2)^i H` for every `i ≤ j`. -/
''', r'''
theorem Ustar_growth {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (H : ℝ)
    (hH : ∀ i ≤ j, hS d i ≤ H) : ∀ i ≤ j, ‖colE (Ecol d i)‖ ≤ (3 / 2) ^ i * H := by
  sorry
''')

_new('S4', 'Z3NetA.aStar_le', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`**, proof of the bound on `a*_s`, the reduction to the local bounds: if
`h_{d,j} ≤ H` for every column `d` and level `j ≤ s - 2`, then every entry `M^(j)[c][d] = E_{d,j}[c]`
of `U*_s` has absolute value at most `(3/2)^{s-2} H`, and `a*_s ≤ (s - 1)(3/2)^{s-2} H`. -/
''', r'''
theorem aStar_le {s : ℕ} [NeZero s] (hs : 3 ≤ s) (H : ℝ) (hH : ∀ d : Fin s, ∀ j ≤ s - 2, hS d j ≤ H) :
    (∀ d c : Fin s, ∀ j ≤ s - 2, |(Ecol d j c : ℝ)| ≤ (3 / 2) ^ (s - 2) * H) ∧
      (aStar s : ℝ) ≤ ((s : ℝ) - 1) * ((3 / 2) ^ (s - 2) * H) := by
  sorry
''')

# stage S4, S5 items taken early: `a*_3 = 2` and the `s = 3` display after `def:Ustar`; the `s = 4`
# frame layer of `prop:k1designs`(1) is the level-0 layer of `U*_4`.
_new('S4', 'Z3NetA.Ustar3_display', _A[0], 'def:Ustar', _A[1], _A[2], r'''
/-- **`def:Ustar`**, the display for `s = 3` (places `∞, 0, 1`, coordinate order `∞, 0, 1`): the
definition gives `F_0 = [[-2, 1, 1], [1, -2, -1], [1, 1, -2]]`, `F_1 = [[0, -2, -1], [-2, 0, 2],
[-1, -1, 0]]` (and `F_n = 0` for `n ≥ 2`). -/
''', r'''
theorem Ustar3_display :
    (∀ c d : Fin 3, UstarF 3 0 c d = ![![-2, 1, 1], ![1, -2, -1], ![1, 1, -2]] c d) ∧
      (∀ c d : Fin 3, UstarF 3 1 c d = ![![0, -2, -1], ![-2, 0, 2], ![-1, -1, 0]] c d) ∧
      ∀ n, 2 ≤ n → ∀ c d : Fin 3, UstarF 3 n c d = 0 := by
  sorry
''')

_new('S4', 'Z3NetA.aStar_three', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`**: `a*_3 = 2`. -/
''', r'''
theorem aStar_three : aStar 3 = 2 := by
  sorry
''')

EXTRA_MODS['Deficit'].append('Z3Net.ThmADefs')
_new('S4', 'Z3NetA.k1designs_frame4_Ustar', 'Deficit', 'prop:k1designs', 'Z3NetA', ['open Matrix Finset Z3NetF'], r'''
/-- **`prop:k1designs`(1)**: the printed `s = 4` frame layer (`k1Frame4`, `app:designs`) is the
level-`0` layer of `U*_4` with the diagonal re-chosen: its off-diagonal entries are those of `F_0` of
`U*_4` (`def:Ustar`, places `∞, 0, 1, 2`). -/
''', r'''
theorem k1designs_frame4_Ustar :
    ∀ c d : Fin 4, c ≠ d → UstarF 4 0 c d = k1Frame4 c d := by
  sorry
''')

# ---------------------------------------------------------------- stage S5: new (`thm:A` part III: local bounds, the bound
# on `a*_s` and its asymptotics, the sharpness for k ≥ 2, Theorem A assembled). Statement review:
# the statement-review notes (research repository). Proofs `Z3Net/ThmALocal.lean`, `ThmASharp.lean`; restatements `Z3Net/ThmAFinal.lean`.
EXTRA_SOLUTION.append('Z3Net.ThmAFinal')

_new('S5', 'Z3NetA.Ainf_fin_le', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`, proof, finite column, the place `∞`**: for a finite column `d` (coordinate `d ≠ 0`)
and `j ≤ s - 2`, the monic Chebyshev polynomial `2^{1-j} T_j` (nodes and weights in `[-1, 1]`) gives
`A_{j,∞} ≤ √(s-1)` (the paper prints the weaker `2√(s-1)`). -/
''', r'''
theorem Ainf_fin_le {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (hd : d ≠ 0) (j : ℕ)
    (hj : j ≤ s - 2) : Ainf d j ≤ Real.sqrt ((s : ℝ) - 1) := by
  sorry
''')

_new('S5', 'Z3NetA.prodAp_fin_le', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`, proof, finite column, the places `p ∈ S`**: the root-placing polynomials
`g_p = ∏_{r ∈ R'} (X - y_r) · X^{j-|R'|}` give `∏_{p ∈ S} A_{j,p} ≤ d!(n-d)!`, where the paper's `d` is the
place value `d - 1` of the coordinate `d ≠ 0`, i.e. `∏_{p ∈ S} A_{j,p} ≤ (d-1)!(s-1-d)!`. -/
''', r'''
theorem prodAp_fin_le {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (hd : d ≠ 0) (j : ℕ)
    (hj : j ≤ s - 2) :
    ∏ p ∈ primesS s, Ap p d j ≤ (((d : ℕ) - 1).factorial * (s - 1 - (d : ℕ)).factorial : ℕ) := by
  sorry
''')

_new('S5', 'Z3NetA.Ainf_inf_le', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`, proof, the column `∞`, the place `∞`**: the monic Chebyshev polynomial of `[0, n]`,
`n = s - 2`, gives `A_{j,∞} ≤ 2√(s-1)(n/4)^j` (column `∞` = coordinate `0`, `j ≤ s - 2`). -/
''', r'''
theorem Ainf_inf_le {s : ℕ} [NeZero s] (hs : 3 ≤ s) (j : ℕ) (hj : j ≤ s - 2) :
    Ainf (0 : Fin s) j ≤ 2 * Real.sqrt ((s : ℝ) - 1) * (((s : ℝ) - 2) / 4) ^ j := by
  sorry
''')

_new('S5', 'Z3NetA.prodAp_inf_le', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`, proof, the column `∞`, the places `p ∈ S`**: the falling factorial
`X(X-1)⋯(X-j+1)` takes the values `j! binom(c, j)` at the nodes `c = 0, …, n`, so `A_{j,p} ≤ |j!|_p`
and `∏_{p ∈ S} A_{j,p} ≤ 1/j!`. -/
''', r'''
theorem prodAp_inf_le {s : ℕ} [NeZero s] (hs : 3 ≤ s) (j : ℕ) (hj : j ≤ s - 2) :
    ∏ p ∈ primesS s, Ap p (0 : Fin s) j ≤ ((j.factorial : ℕ) : ℝ)⁻¹ := by
  sorry
''')

_new('S5', 'Z3NetA.hS_le_Hs', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`, proof, the local bounds**: for `s ≥ 4`, every column `d` and every level `j ≤ s - 2`,
`h_{d,j} ≤ H_s = 2√(s-1)(s-2)!` (finite columns: `√(s-1) · d!(n-d)! ≤ √(s-1) n!`; the column `∞`:
`2√(s-1)(n/4)^j/j! ≤ 2√(s-1)e^{n/4} ≤ 2√(s-1) n!`). -/
''', r'''
theorem hS_le_Hs {s : ℕ} [NeZero s] (hs : 4 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) :
    hS d j ≤ 2 * Real.sqrt ((s : ℝ) - 1) * ((s - 2).factorial : ℝ) := by
  sorry
''')

_new('S5', 'Z3NetA.aStar_bound', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`, the bound on `a*_s`**: for `s ≥ 4`, every entry `M^(j)[c][d] = E_{d,j}[c]` of `U*_s`
has absolute value at most `(3/2)^{s-2} H_s`, `H_s = 2√(s-1)(s-2)!`, and
`a*_s ≤ 2(s-1)^{3/2}(3/2)^{s-2}(s-2)!`. -/
''', r'''
theorem aStar_bound {s : ℕ} [NeZero s] (hs : 4 ≤ s) :
    (∀ d c : Fin s, ∀ j ≤ s - 2,
        |(Ecol d j c : ℝ)| ≤ (3 / 2) ^ (s - 2) * (2 * Real.sqrt ((s : ℝ) - 1) * ((s - 2).factorial : ℝ))) ∧
      (aStar s : ℝ) ≤ 2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ) := by
  sorry
''')

_new('S5', 'Z3NetA.aStar_bound_log', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`, the asymptotic form of the bound**, `2(s-1)^{3/2}(3/2)^{s-2}(s-2)! = e^{s log s + O(s)}`,
with an explicit constant: for every `s ≥ 4`,
`|log(2(s-1)^{3/2}(3/2)^{s-2}(s-2)!) - s log s| ≤ 3s`. -/
''', r'''
theorem aStar_bound_log (s : ℕ) (hs : 4 ≤ s) :
    |Real.log (2 * ((s : ℝ) - 1) ^ ((3 : ℝ) / 2) * (3 / 2) ^ (s - 2) * ((s - 2).factorial : ℝ)) -
      s * Real.log s| ≤ 3 * s := by
  sorry
''')

_new('S5', 'Z3NetA.A_sharp', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`(2), the first-order sharpness for `k ≥ 2`** (the printed proof): let `i` attain
`a*_s = α_i`. For `q` as in (1) with `q > 2a*_s` and `q > ∑_{u ≠ i} |F_0[u][i]|`, two distinct points of
`𝒫^{U*_s}_{k,q}` have squared Euclidean and squared toroidal distance, in cell units (times
`q^(2k)`), `< (1 - a*_s/q)² + ∑_{u ≠ i} (|F_0[u][i]| + 1)²/q²` (`F_0 = UstarF s 0`). -/
''', r'''
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
          ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  sorry
''')

_new('S5', 'Z3NetA.A_sharp_real', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`(2), the first-order sharpness for `k ≥ 2`, real form**: for `q` as in (1) with
`q ≥ 5a*_s + 4` and `q > (s-1) a*_s`, some two distinct points of `𝒫^{U*_s}_{k,q}` have toroidal and
Euclidean distance `< (1 - a*_s/q + (s-1)(a*_s+1)²/q²) N^(-1/s)`, `N = q^(sk)`. With the lower bound
(`A_sep_real`): `δ N^(1/s) = 1 - a*_s/q + O(q⁻²)` as `q → ∞`, the `O` with the constant
`(s-1)(a*_s+1)²`. -/
''', r'''
theorem A_sharp_real {s : ℕ} [NeZero s] (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k)
    (hqa : 5 * aStar s + 4 ≤ q) (hqs : (s - 1) * aStar s < q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ∧
      Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by
  sorry
''')

_new('S5', 'Z3NetA.thmA', _A[0], 'thm:A', _A[1], _A[2], r'''
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
''', r'''
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
  sorry
''')

# ---------------------------------------------------------------- stage S6b: new (the headline justifies its choice-defined
# data: the net of `def:Ns` does not depend on the choice of `U'`, `β`; uniqueness of `γ_j`). Statement review:
# the statement-review notes (research repository) (D1, D2). Proofs and restatements `Z3Net/ThmAChoice.lean`.
EXTRA_SOLUTION.append('Z3Net.ThmAChoice')

_new('S6b', 'Z3NetF.PGen_indep', 'Frames', 'prop:Gs', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:Gs`, `def:Ns`**, the net does not depend on the choices: for places with unit
differences (`PlacesOK`), any two solutions `U'`, `U''` of the residual problem of a design `F`
(with the same `λ'`) and any two `β`, `β'` with the defining relation of `prop:Gs` give the same
generator matrices of `𝒫^F_k`. (`U'^(k)_d` reads `U'_d` only on `n', n ≤ s - 2`, where it is unique,
and `β_n` only for `n ≥ s - 1`, where it is unique.) -/
''', r'''
theorem PGen_indep {R : Type*} [CommRing R] {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (inf : Fin s)
    (x : Fin s → R) (hx : PlacesOK inf x) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur Ur' β β' : Fin s → ℕ → ℕ → R) (hres : Residual inf x F lam Ur)
    (hres' : Residual inf x F lam Ur') (hβ : BetaRel inf x F lam β)
    (hβ' : BetaRel inf x F lam β') :
    PGen k inf x F lam Ur β = PGen k inf x F lam Ur' β' := by
  sorry
''')

_new('S6b', 'Z3NetA.Apoint_indep', _A[0], 'thm:A', _A[1], _A[2], r'''
/-- **`thm:A`, the net is well defined**: for every ring homomorphism `ψ : R_S → ℤ/qℤ`, every solution
`U'` of the residual problem of `U*_s` with `λ' ≡ 1` and every `β` with the defining relation of
`prop:Gs`, the net of `def:Ns` built from `(U', β)` and reduced by `ψ` is `Apoint s q k`. So `Apoint`
does not depend on the choices `UrS`, `betaS` and the chosen reduction. -/
''', r'''
theorem Apoint_indep (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (ψ : RS s →+* ZMod q)
    (Ur β : Fin s → ℕ → ℕ → RS s) (hres : Residual (0 : Fin s) placeA (UstarR s) 1 Ur)
    (hβ : BetaRel (0 : Fin s) placeA (UstarR s) 1 β) :
    Apoint s q k = digPoint q (s * k) (fun c =>
      (PGen k (0 : Fin s) placeA (UstarR s) 1 Ur β c).map ψ) := by
  sorry
''')

_new('S6b', 'Z3NetA.gamS_unique', _A[0], 'lem:sat', _A[1], _A[2], r'''
/-- **`lem:sat`(ii)**, uniqueness of `γ_j`: a positive rational `γ` with `κ_j(Λ_j) = γ ℤ` is
`gamS d j` (column `d`, `j ≤ s - 2`). -/
''', r'''
theorem gamS_unique {s : ℕ} [NeZero s] (hs : 3 ≤ s) (d : Fin s) (j : ℕ) (hj : j ≤ s - 2) (γ : ℚ)
    (hγ : 0 < γ)
    (hgen : ∀ t : ℚ, (∃ E, InLam d j E ∧ kappa d j E = t) ↔ ∃ z : ℤ, t = z * γ) :
    γ = gamS d j := by
  sorry
''')

# ---------------------------------------------------------------- stage S7: new (`sec:Lstar`: `lem:O`, `prop:E`, `lem:C`,
# `thm:Lstar`, with `PGL₂(ℚ)`-images of the places). Statement review: the statement-review notes (research repository). Definitions
# `Z3Net/LstarDefs.lean`; proofs `Z3Net/Lstar.lean`; restatements `Z3Net/LstarMain.lean`.
EXTRA_MODS['Deficit'].append('Z3Net.LstarDefs')
EXTRA_SOLUTION.append('Z3Net.LstarMain')

_new('S7', 'Z3NetF.O_orient', 'Deficit', 'lem:O', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`lem:O`** (orientation): if `K = K(F) < ∞`, then for every pair `a ≠ b` of coordinates,
`|M^(j)[a][b]| ≤ K` for all `j < L`, or `|M^(j)[b][a]| ≤ K` for all `j < L`. -/
''', r'''
theorem O_orient {s L K : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (hK : Kdef F L = (K : WithTop ℕ))
    (a b : Fin s) (hab : a ≠ b) :
    (∀ j < L, |Msum F j a b| ≤ K) ∨ ∀ j < L, |Msum F j b a| ≤ K := by
  sorry
''')

_new('S7', 'Z3NetF.E_lcm', 'Deficit', 'prop:E', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:E`** (constant row scalars): `s ≥ 4`, an integer design `F` with `L ≥ 1` levels whose
residual problem is solvable over `ℚ` (`prop:F`) for the places `∞, 0, 1, …, s-2` (in any
assignment `π` to the coordinates: the place of `c ≠ inf` is `π c - 1`, `inf` is `∞`) with row
scalars `λ'` that take one value on all finite places (`λ'_∞` arbitrary). If `K(F) = K < ∞`, then
`K ≥ lcm(1, …, s-3)`. -/
''', r'''
theorem E_lcm {s L K : ℕ} [NeZero s] (hs : 4 ≤ s) (hL : 1 ≤ L) (inf : Fin s) (x : Fin s → ℚ)
    (π : Fin s ≃ Fin s) (hinf : π inf = 0) (hx : ∀ c, c ≠ inf → x c = Z3NetA.placeA (π c))
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ) (Ur : Fin s → ℕ → ℕ → ℚ)
    (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur)
    (hlam : ∀ c d, c ≠ inf → d ≠ inf → lam c = lam d) (hK : Kdef F L = (K : WithTop ℕ)) :
    Nat.lcmUpto (s - 3) ≤ K := by
  sorry
''')

_new('S7', 'Z3NetF.E_two_pow', 'Deficit', 'prop:E', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:E`**, the elementary form printed after it (Chebyshev's
`2^n ≤ (n+1) lcm(1, …, n)`, `n = s - 3`): under the hypotheses of `E_lcm`,
`2^(s-3) ≤ (s-2) K`, i.e. `K(F) ≥ 2^(s-3)/(s-2)`. -/
''', r'''
theorem E_two_pow {s L K : ℕ} [NeZero s] (hs : 4 ≤ s) (hL : 1 ≤ L) (inf : Fin s) (x : Fin s → ℚ)
    (π : Fin s ≃ Fin s) (hinf : π inf = 0) (hx : ∀ c, c ≠ inf → x c = Z3NetA.placeA (π c))
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ) (Ur : Fin s → ℕ → ℕ → ℚ)
    (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur)
    (hlam : ∀ c d, c ≠ inf → d ≠ inf → lam c = lam d) (hK : Kdef F L = (K : WithTop ℕ)) :
    2 ^ (s - 3) ≤ (s - 2) * K := by
  sorry
''')

_new('S7', 'Z3NetF.E_Ustar', 'Deficit', 'prop:E', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:E`** for the design `U*_s` of Theorem A (`def:Ustar`; "The class of
Proposition `prop:E` contains … the design `U*_s` of Theorem A"): if `K(U*_s) = K < ∞` (`L ≥ 1`
levels), then `K ≥ lcm(1, …, s-3)`. -/
''', r'''
theorem E_Ustar {s L K : ℕ} [NeZero s] (hs : 4 ≤ s) (hL : 1 ≤ L)
    (hK : Kdef (Z3NetA.UstarF s) L = (K : WithTop ℕ)) : Nat.lcmUpto (s - 3) ≤ K := by
  sorry
''')

_new('S7', 'Z3NetF.C_count', 'Deficit', 'lem:C', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`lem:C`** (a cross-ratio count): the places `∞, 0, 1, …, n` on the coordinates
`0, 1, …, n+1`, two distinct places `d, d'`, a rational `r ≠ 0`, and `w_cd` as in `prop:Ns`. If `C`
is a nonempty set of places `c ∉ {d, d'}` with `w_cd / w_cd' ∈ r Q_K` for all `c ∈ C`, then
`|C| ≤ 1 + 2Kτ*(n)τ*(nK)²`. -/
''', r'''
theorem C_count {n K : ℕ} (d d' : Fin (n + 2)) (hdd : d ≠ d') (r : ℚ) (hr : r ≠ 0)
    (C : Finset (Fin (n + 2))) (hC : C.Nonempty)
    (hmem : ∀ c ∈ C, c ≠ d ∧ c ≠ d' ∧ ∃ z ∈ QK K,
      wN (0 : Fin (n + 2)) Z3NetA.placeA c d / wN (0 : Fin (n + 2)) Z3NetA.placeA c d' = r * z) :
    C.card ≤ 1 + 2 * K * tauStar n * tauStar (n * K) ^ 2 := by
  sorry
''')

_new('S7', 'Z3NetF.C_count_sharp', 'Deficit', 'lem:C', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`lem:C`**, the sharper bound the proof gives: `|C| ≤ 1 + 2Kτ*(n)τ*(nK)` (for two finite places
`d, d'` the place `c` is determined by `h ∣ d - d'`, `B ∣ P` and `β`; the divisor `A ∣ Q` of the
printed count is not needed). -/
''', r'''
theorem C_count_sharp {n K : ℕ} (d d' : Fin (n + 2)) (hdd : d ≠ d') (r : ℚ) (hr : r ≠ 0)
    (C : Finset (Fin (n + 2))) (hC : C.Nonempty)
    (hmem : ∀ c ∈ C, c ≠ d ∧ c ≠ d' ∧ ∃ z ∈ QK K,
      wN (0 : Fin (n + 2)) Z3NetA.placeA c d / wN (0 : Fin (n + 2)) Z3NetA.placeA c d' = r * z) :
    C.card ≤ 1 + 2 * K * tauStar n * tauStar (n * K) := by
  sorry
''')

_new('S7', 'Z3NetF.PGLImage_self', 'Deficit', 'thm:Lstar', 'Z3NetF', ['open Matrix Finset'], r'''
/-- `thm:Lstar`: the places `∞, 0, 1, …, s-2` themselves are an instance of `PGLImage`. -/
''', r'''
theorem PGLImage_self {s : ℕ} [NeZero s] : PGLImage (0 : Fin s) (Z3NetA.placeA : Fin s → ℚ) := by
  sorry
''')

_new('S7', 'Z3NetF.Lstar_bound', 'Deficit', 'thm:Lstar', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`thm:Lstar`** (frame designs): `s ≥ 5`, an integer design `F` with `L ≥ 1` levels whose
residual problem is solvable over `ℚ` (`prop:F`), with arbitrary row scalars, for a frame whose
places are the image of `∞, 0, 1, …, s-2` under an element of `PGL₂(ℚ)` (`PGLImage`; the places
themselves included, `PGLImage_self`). If `K(F) = K < ∞`, then
`(s-3)/4 ≤ 1 + 2Kτ*(s-2)τ*((s-2)K)²`. -/
''', r'''
theorem Lstar_bound {s L K : ℕ} [NeZero s] (hs : 5 ≤ s) (hL : 1 ≤ L) (inf : Fin s)
    (x : Fin s → ℚ) (hplace : PGLImage inf x) (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ)
    (Ur : Fin s → ℕ → ℕ → ℚ) (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur)
    (hK : Kdef F L = (K : WithTop ℕ)) :
    ((s : ℝ) - 3) / 4 ≤ 1 + 2 * (K : ℝ) * tauStar (s - 2) * (tauStar ((s - 2) * K) : ℝ) ^ 2 := by
  sorry
''')

# ---------------------------------------------------------------- stage S8: new (`prop:4D2`, `prop:k1`(3)). Statement
# review: the statement-review notes (research repository). Definitions `Z3Net/D4D2Defs.lean`; proofs `Z3Net/D4D2.lean` (kernel certificates
# `Z3Net/D4D2CertKS.lean`, `Z3Net/D4D2CertLB.lean`), `Z3Net/K1Ceil.lean`; restatements `Z3Net/D4D2Main.lean`.
EXTRA_MODS['Deficit'].append('Z3Net.D4D2Defs')
EXTRA_SOLUTION.append('Z3Net.D4D2Main')

_new('S8', 'Z3NetF.D4D2_data', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(1), exact interpolation: for the design `F` of `prop:4D2` (`app:designs`, places
`∞, 0, 1, 2`, `λ' ≡ 1`) the residual problem (`prop:F`) is solvable over `ℤ[1/2]`, and so are the
relations of `prop:Gs`: the chosen `U' = Ur4D2` and `β = beta4D2` of the net `P4D2` satisfy them. -/
''', r'''
theorem D4D2_data :
    Residual (0 : Fin 4) Z3NetA.placeA F4D2R 1 Ur4D2 ∧
      BetaRel (0 : Fin 4) Z3NetA.placeA F4D2R 1 beta4D2 := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_net', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(1): `𝒫^F_{k,q}` is a digital `(0,4k,4)`-net over `ℤ/qℤ` for every odd `q ≥ 3` and
every `k`: every elementary box of volume `q^(-4k)` holds exactly one point (so does every cell). -/
''', r'''
theorem D4D2_net {q : ℕ} (k : ℕ) (hq : Odd q) (h3 : 3 ≤ q) : IsNet0 4 q (4 * k) (P4D2 q k) := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_boxMinor', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(1): every box minor of the generator matrices of `𝒫^F_k` over `ℤ[1/2]` is `±2^i`
(`i ∈ ℤ`): for `d` with `∑ d_c = 4k` the box minor is `ε 2^i` or `ε 2^(-i)`, `ε = ±1`, `i ∈ ℕ`. -/
''', r'''
theorem D4D2_boxMinor (k : ℕ) (d : Fin 4 → ℕ) (hd : ∑ c, d c = 4 * k) :
    ∃ (i : ℕ) (ε : Z3NetA.RS 4), (ε = 1 ∨ ε = -1) ∧
      ((boxMatrix (PGen k (0 : Fin 4) Z3NetA.placeA F4D2R 1 Ur4D2 beta4D2) d).det = ε * 2 ^ i ∨
        (boxMatrix (PGen k (0 : Fin 4) Z3NetA.placeA F4D2R 1 Ur4D2 beta4D2) d).det * 2 ^ i = ε) := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_covering', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(1): `h ≤ 2 N^(-1/4)`: for every odd `q ≥ 3`, every `k` and every `x ∈ [0,1]^4`
there is a point of `𝒫^F_{k,q}` at Euclidean distance at most `2 q^(-k)` from `x`. -/
''', r'''
theorem D4D2_covering {q : ℕ} (k : ℕ) (hq : Odd q) (h3 : 3 ≤ q) (x : Fin 4 → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (4 * k) → ZMod q,
      ∑ c, (x c - (P4D2 q k v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2 ≤ 4 / ((q : ℝ) ^ k) ^ 2 := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_KS', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(2), the two finite maxima (computer-assisted: kernel `decide` over all
configurations of `def:K` with `L = 3` levels): `K(F) = 2` and `S(F) = 7`, so `Q_D = 23`
(`prop:Dprime`). -/
''', r'''
theorem D4D2_KS : Kdef F4D2 3 = 2 ∧ Sdef F4D2 3 = 7 ∧ QD 2 7 = 23 := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_LB_small', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(2), the values at `q = 17, 19, 21` (computer-assisted: kernel `decide`): the exact
relaxation of `lem:Ss` with `L = 3` levels is `LB = (q - 2)/q`. -/
''', r'''
theorem D4D2_LB_small (q : ℕ) (hq : q = 17 ∨ q = 19 ∨ q = 21) :
    LBval q F4D2 3 3 = 1 - (2 : ℝ) / q := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_LB', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(2), the relaxation: `LB ≥ 1 - 2/q` for every odd `q ≥ 17` and every `k ≥ 1`
(the relaxation of `lem:Ss` for `𝒫^F_{k,q}`, `L = min(k, 3)` levels; `prop:Dprime` for `q ≥ 23`, the
exact values with `L = 3` for `q = 17, 19, 21`). -/
''', r'''
theorem D4D2_LB {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k) :
    1 - (2 : ℝ) / q ≤ LBval q F4D2 (min k 3) k := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_sep', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(2): for every odd `q ≥ 17` and every `k ≥ 1` the toroidal minimum distance of
`𝒫^F_{k,q}` satisfies `δ N^(1/4) ≥ 1 - 2/q` (`N = q^(4k)`). -/
''', r'''
theorem D4D2_sep {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (2 : ℝ) / q) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (4 * k)) ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (4 * k)) ^ 2) := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_sep_eucl', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(2), "hence also Euclidean": `δ N^(1/4) ≥ 1 - 2/q` for the Euclidean distance. -/
''', r'''
theorem D4D2_sep_eucl {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 1 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (2 : ℝ) / q) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ)))
      ≤ Real.sqrt (∑ c, (((P4D2 q k v c : ℝ) - P4D2 q k w c) / (q : ℝ) ^ (4 * k)) ^ 2) := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_ceil', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(3), the ceiling (`cor:ceils`(i) with `a = ∞`, column `(-2, 1, 1, 1)` of `F_0`): for
every odd `q ≥ 17` and every `k ≥ 2` (the paper states `k ≥ 3`) two distinct points of `𝒫^F_{k,q}`
have squared Euclidean and toroidal distance, in units of `N^(-1/4) = q^(-k)`, `< (1 - 2/q)² + 12/q²`. -/
''', r'''
theorem D4D2_ceil {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 2 ≤ k) :
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((P4D2 q k v c : ℝ) - P4D2 q k w c) / (q : ℝ) ^ (4 * k)) ^ 2
        < (1 - (2 : ℝ) / q) ^ 2 + 12 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (4 * k))
          ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2
        < (1 - (2 : ℝ) / q) ^ 2 + 12 / (q : ℝ) ^ 2 := by
  sorry
''')

_new('S8', 'Z3NetF.D4D2_ceil_real', 'Deficit', 'prop:4D2', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:4D2`**(3): for every odd `q ≥ 17` and every `k ≥ 2` (the paper states `k ≥ 3`),
`δ N^(1/4) < 1 - 2/q + 8/q²`, toroidal and Euclidean; with (2), the first-order deficit of these nets is
exactly `2`. -/
''', r'''
theorem D4D2_ceil_real {q : ℕ} (k : ℕ) (hq : Odd q) (hq17 : 17 ≤ q) (hk : 2 ≤ k) :
    ∃ v w : Fin (4 * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (4 * k)) ((P4D2 q k v c : ℤ) - (P4D2 q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (4 * k)) ^ 2) <
        (1 - (2 : ℝ) / q + 8 / (q : ℝ) ^ 2) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ))) ∧
      Real.sqrt (∑ c, (((P4D2 q k v c : ℝ) - P4D2 q k w c) / (q : ℝ) ^ (4 * k)) ^ 2) <
        (1 - (2 : ℝ) / q + 8 / (q : ℝ) ^ 2) * ((q : ℝ) ^ (4 * k)) ^ (-(1 / (4 : ℝ))) := by
  sorry
''')

_new('S8', 'Z3NetF.k1_ceil', 'Deficit', 'prop:k1', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:k1`(3)**, the ceiling at one cell level (toroidal): a digital net over `ℤ/qℤ`, `q ≥ 3`, in
graph form with depths `(1, …, 1)` (`N = q^s`) whose first offset rows form the integer matrix `F₀`
and whose deeper rows vanish in their own column; a coordinate `a` with `F₀[a][a] = -K₁`
(`K₁ = K((F₀))` in the paper), `q > 2 max |F₀|`. If `gcd(det F₀, q) = 1`, or if the net is a
`(0,s,s)`-net with `s ≥ 4` and `∑_{u ≠ a} |F₀[u][a]| < q`, then two distinct points have toroidal
distance with `(δ N^(1/s))² < (1 - K₁/q)² + ∑_{u ≠ a} (|F₀[u][a]| + 1)²/q²`. -/
''', r'''
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
        (1 - (K₁ : ℝ) / q) ^ 2 + ∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  sorry
''')

_new('S8', 'Z3NetF.k1_ceil_eucl', 'Deficit', 'prop:k1', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:k1`(3)**, the `(0,s,s)`-net case (`s ≥ 4`, `∑_{u ≠ a} |F₀[u][a]| < q`): the bound of `k1_ceil`
holds for the Euclidean distance too. -/
''', r'''
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
        (1 - (K₁ : ℝ) / q) ^ 2 + ∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  sorry
''')

_new('S8', 'Z3NetF.k1_ceil_real', 'Deficit', 'prop:k1', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:k1`(3)**, real form (toroidal): under the hypotheses of `k1_ceil`,
`δ N^(1/s) < 1 - K₁/q + C/q²` with `C = ∑_{u ≠ a} (|F₀[u][a]| + 1)²`; with `prop:k1`(1) (`k1_sep`,
`k1_tail`), `δ N^(1/s) = 1 - K₁/q + O(q⁻²)`. -/
''', r'''
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
          ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) := by
  sorry
''')

# ---------------------------------------------------------------- stage S9′ (column nets, drift and jitter; retire the
# held block). Statement review: the statement-review notes (research repository). Definitions `Z3Net/ColDefs.lean`, `Z3Net/DShiftDefs.lean`
# (a minimal `def:dshift`); proofs `Z3Net/Col*.lean`, `Z3Net/KOne.lean`; restatements `Z3Net/ColMain.lean`.
# `cor:allm`: its `m = 3` family is now the column net `𝒞_p` (`thm:col`); `bndDim3` (`Z3Net/Dim3Defs.lean`) takes the
# exact constant `Z3NetC.cCol p` of `𝒞_p` in place of the bound of the former `thm:E1`, so the three statements that
# mention it are CHANGED (the text of `bndDim3_gt`, `bndDim3_tendsto` is unchanged, their constant is not).
EXTRA_MODS['Dim3'] = EXTRA_MODS.get('Dim3', []) + ['Z3Net.ColDefs', 'Z3Net.DShiftDefs']
EXTRA_MODS['Deficit'].append('Z3Net.ColDefs')
EXTRA_MODS['DGS'] = EXTRA_MODS.get('DGS', []) + ['Z3Net.ColDefs', 'Z3Net.DShiftDefs']
EXTRA_SOLUTION.append('Z3Net.ColMain')

# Solution imports that restate no compared theorem after S9′ (the retired Eisenstein block; `prop:twocoset`
# imports what it needs through `EisensteinNet.TCMain`).
DROP_SOLUTION = ['EisensteinNet']

_chg('S9′', 'Z3NetKN.cor_allm', r'''
/-- **`cor:allm`.** For every prime `p ≥ 37` and every `m ≥ 3` there is a digital `(0,m,3)`-net over
`𝔽_p` (the nets of `thm:col` (the column net `𝒞_p`) for `m = 3`, `thm:main` for `m ≡ 0`, `m ≥ 6`, `thm:allm` (`𝓑¹`) for
`m ≡ 1`, `thm:S1` at `s = 3` (`𝓑²`) for `m ≡ 2`, with `ρ` maximal) whose toroidal minimum distance
satisfies `δ N^(1/3) ≥ bndDim3 p` (`N = p^m`), and whose covering radius satisfies
`h N^(1/3) ≤ √3`, `p^(1/3) √(2 + p^(-2))`, `min{p^(2/3) √(1 + 2p^(-2)), 4.264}` for
`m ≡ 0, 1, 2 (mod 3)`. -/
''', r'''
theorem cor_allm (p m : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) (hm : 3 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p),
      IsNet0 p m (digPoint p m C) ∧
      (∀ v w : Fin m → ZMod p, v ≠ w →
        bndDim3 p * ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (p ^ m) ((digPoint p m C v c : ℤ) - (digPoint p m C w c : ℤ)) : ℝ)
            / (p : ℝ) ^ m) ^ 2)) ∧
      (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin m → ZMod p,
        Real.sqrt (∑ c, (y c - (digPoint p m C v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
          (if m % 3 = 0 then Real.sqrt 3
           else if m % 3 = 1 then (p : ℝ) ^ (1 / (3 : ℝ)) * Real.sqrt (2 + 1 / (p : ℝ) ^ 2)
           else min ((p : ℝ) ^ (2 / (3 : ℝ)) * Real.sqrt (1 + 2 / (p : ℝ) ^ 2)) 4.264) *
            ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ)))) := by
  sorry
''')

_chg('S9′', 'Z3NetKN.bndDim3_gt', r'''
/-- **`cor:allm`, the uniform constants**: for every prime `p ≥ 37`, `bndDim3 p > 0.2715`, and
`> 0.4250` if `p ≥ 83`. -/
''', r'''
theorem bndDim3_gt (p : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) :
    0.2715 < bndDim3 p ∧ (83 ≤ p → 0.4250 < bndDim3 p) := by
  sorry
''')

_chg('S9′', 'Z3NetKN.bndDim3_tendsto', r'''
/-- **`cor:allm`: the lower bound tends to `1`.** -/
''', r'''
theorem bndDim3_tendsto : Filter.Tendsto bndDim3 Filter.atTop (nhds 1) := by
  sorry
''')

_new('S9′', 'Z3NetC.colmin', 'Dim3', 'thm:colmin', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:colmin`**: for every column point set in base `q ≥ 2`, with `G = 3g`
(`g = min_{i,[n]} dist(Δ_i([n]), ⅔q² + q²ℤ)`), the toroidal minimum distance `d` at integer scale `q³`
satisfies `3d² = 2q⁴ + G²` (i.e. `d² = ⅔q⁴ + 3g²`): every pair of distinct points has
`3 d² ≥ 2q⁴ + G²`, and a pair in neighbouring columns `[n]`, `[n + e_i]` attains it. -/
''', r'''
theorem colmin {q : ℕ} [NeZero q] (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    (∀ n n' : Fin 3 → ZMod q, n ≠ n' →
      2 * q ^ 4 + colGap q φ ^ 2 ≤ 3 * torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n')) ∧
    ∃ (i : Fin 3) (n : Fin 3 → ZMod q) (t : ZMod q), n + Pi.single i 1 + (fun _ => t) ≠ n ∧
      3 * torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ (n + Pi.single i 1 + fun _ => t)) =
        2 * q ^ 4 + colGap q φ ^ 2 := by
  sorry
''')

_new('S9′', 'Z3NetC.colmin_real', 'Dim3', 'thm:colmin', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:colmin`**: `δN^{1/3} ≥ √(2/3)` for every column point set (`N = q³`, toroidal). -/
''', r'''
theorem colmin_real {q : ℕ} [NeZero q] (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ)
    (n n' : Fin 3 → ZMod q) (hne : n ≠ n') :
    Real.sqrt (2 / 3) ≤ Real.sqrt (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℝ) / (q : ℝ) ^ 2 := by
  sorry
''')

_new('S9′', 'Z3NetC.colW_column', 'Dim3', 'def:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`def:col`** (and the setting of `lem:drift`): the digital net with the digits `n_c`, `a·n`, `ℓ·n`
in every coordinate (`a = (q𝟏 + w)/3`, `∑ w = 0`, `w_c ≡ -q (mod 3)`, `∑ ℓ ≡ 0 (mod q)`) is a column
point set: its point with index `n` is `q² n + φ([n]) 𝟏` with the heights `φ = q (a·n) + ℓ·n`. -/
''', r'''
theorem colW_column {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (hℓ : (q : ℤ) ∣ ∑ c, ℓ c) :
    IsHeight q (colPhi q w ℓ) ∧ ∀ n, digPoint q 3 (colGenW q w ℓ) n = colPt q (colPhi q w ℓ) n := by
  sorry
''')

_new('S9′', 'Z3NetC.col_column', 'Dim3', 'def:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`def:col`**: `𝒞_q` is a column point set (`gcd(q, 6) = 1`). -/
''', r'''
theorem col_column {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) :
    IsHeight q (colPhi q (wCol q) ellCol) ∧
      ∀ n, digPoint q 3 (colGen q) n = colPt q (colPhi q (wCol q) ellCol) n := by
  sorry
''')

_new('S9′', 'Z3NetC.col_net', 'Dim3', 'thm:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:col`(1)**: for `q ≥ 5` with `gcd(q, 6) = 1`, `𝒞_q` is a digital `(0,3,3)`-net over `ℤ/qℤ`; its
box minors are units, each one of `1`, `±a_x`, `±a_y`, `±a_z`, `a_x + a_y`. -/
''', r'''
theorem col_net {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    IsNet0 3 q 3 (digPoint q 3 (colGen q)) ∧ ∀ d : Fin 3 → ℕ, ∑ c, d c = 3 →
      IsUnit (boxMatrix (colGen q) d).det ∧
      (boxMatrix (colGen q) d).det ∈ ({1, ((colA q (wCol q) 0 : ℤ) : ZMod q),
        -((colA q (wCol q) 0 : ℤ) : ZMod q), ((colA q (wCol q) 1 : ℤ) : ZMod q),
        -((colA q (wCol q) 1 : ℤ) : ZMod q), -((colA q (wCol q) 2 : ℤ) : ZMod q),
        ((colA q (wCol q) 2 : ℤ) : ZMod q),
        ((colA q (wCol q) 0 : ℤ) : ZMod q) + ((colA q (wCol q) 1 : ℤ) : ZMod q)} : Set (ZMod q)) := by
  sorry
''')

_new('S9′', 'Z3NetC.col_covering', 'Dim3', 'thm:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:col`(1)**: every cell of side `q⁻¹` holds a point of `𝒞_q`, so `h ≤ √3 N^{-1/3}`. -/
''', r'''
theorem col_covering {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (y : Fin 3 → ℝ)
    (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v : Fin 3 → ZMod q, Real.sqrt (∑ c, (y c - (digPoint q 3 (colGen q) v c : ℝ) / (q : ℝ) ^ 3) ^ 2) ≤
      Real.sqrt 3 * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) := by
  sorry
''')

_new('S9′', 'Z3NetC.col_mindist', 'Dim3', 'thm:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:col`(2)**: the toroidal minimum distance `d` of `𝒞_q` at integer scale `q³` satisfies
`3d² = 2q⁴ + τ²` (`τ = q² - q - 3` for `q ≡ 2`, `q² - 2q` for `q ≡ 1 (mod 3)`): every pair has
`3 d² ≥ 2q⁴ + τ²`, toroidally and hence Euclidean, and a pair attains it in both. -/
''', r'''
theorem col_mindist {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    (∀ v w : Fin 3 → ZMod q, v ≠ w →
      2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ≤
        3 * (torusDist2 (q ^ 3) (digPoint q 3 (colGen q) v) (digPoint q 3 (colGen q) w) : ℤ) ∧
      2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ≤
        3 * ∑ c, ((digPoint q 3 (colGen q) w c : ℤ) - (digPoint q 3 (colGen q) v c : ℤ)) ^ 2) ∧
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧
      3 * ∑ c, ((digPoint q 3 (colGen q) w c : ℤ) - (digPoint q 3 (colGen q) v c : ℤ)) ^ 2 =
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ∧
      3 * (torusDist2 (q ^ 3) (digPoint q 3 (colGen q) v) (digPoint q 3 (colGen q) w) : ℤ) =
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
  sorry
''')

_new('S9′', 'Z3NetC.col_closest', 'Dim3', 'thm:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:col`(2)**, closest pairs: two distinct points of `𝒞_q` are at the minimum distance if and
only if their difference is `±D` modulo `q³` (`D` = `DCol q`). -/
''', r'''
theorem col_closest {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) (v w : Fin 3 → ZMod q)
    (hvw : v ≠ w) :
    3 * (torusDist2 (q ^ 3) (digPoint q 3 (colGen q) v) (digPoint q 3 (colGen q) w) : ℤ) =
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ↔
      (∀ c, (digPoint q 3 (colGen q) w c : ℤ) ≡ (digPoint q 3 (colGen q) v c : ℤ) + DCol q c
        [ZMOD (q : ℤ) ^ 3]) ∨
      (∀ c, (digPoint q 3 (colGen q) w c : ℤ) ≡ (digPoint q 3 (colGen q) v c : ℤ) - DCol q c
        [ZMOD (q : ℤ) ^ 3]) := by
  sorry
''')

_new('S9′', 'Z3NetC.col_expansion', 'Dim3', 'thm:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:col`(2)**: for `q ≡ 2 (mod 3)`, `2q⁴ + τ² = 3q⁴ - 2q³ - 5q² + 6q + 9`
(`d² = q⁴ - ⅔q³ - (5/3)q² + 2q + 3`) and `δN^{1/3} = 1 - 1/(3q) - 8/(9q²) + O(q⁻³)`; for `q ≡ 1`,
`2q⁴ + τ² = 3q⁴ - 4q³ + 4q²` (`d² = q⁴ - (4/3)q³ + (4/3)q²`) and `δN^{1/3} = 1 - 2/(3q) + 4/(9q²) + O(q⁻³)`;
with the explicit `O(q⁻³)` bounds `2/q³` resp. `1/q³` (`cCol q = √((2q⁴ + τ²)/3)/q²`). -/
''', r'''
theorem col_expansion {q : ℕ} [NeZero q] (hq : 5 ≤ q) :
    (q % 3 = 2 → 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 = 3 * (q : ℤ) ^ 4 - 2 * q ^ 3 - 5 * q ^ 2 + 6 * q + 9 ∧
      |cCol q - (1 - 1 / (3 * q) - 8 / (9 * (q : ℝ) ^ 2))| ≤ 2 / (q : ℝ) ^ 3) ∧
    (q % 3 = 1 → 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 = 3 * (q : ℤ) ^ 4 - 4 * q ^ 3 + 4 * q ^ 2 ∧
      |cCol q - (1 - 2 / (3 * q) + 4 / (9 * (q : ℝ) ^ 2))| ≤ 1 / (q : ℝ) ^ 3) := by
  sorry
''')

_new('S9′', 'Z3NetC.col_sep_real', 'Dim3', 'thm:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:col`(2)**, real form: `δN^{1/3} = cCol q` for `𝒞_q` (toroidal, `N = q³`). -/
''', r'''
theorem col_sep_real {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q) :
    (∀ v w : Fin 3 → ZMod q, v ≠ w → cCol q * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
      Real.sqrt (∑ c, ((cres (q ^ 3) ((digPoint q 3 (colGen q) v c : ℤ) -
        (digPoint q 3 (colGen q) w c : ℤ)) : ℝ) / (q : ℝ) ^ 3) ^ 2)) ∧
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧ Real.sqrt (∑ c, ((cres (q ^ 3) ((digPoint q 3 (colGen q) v c : ℤ) -
        (digPoint q 3 (colGen q) w c : ℤ)) : ℝ) / (q : ℝ) ^ 3) ^ 2) =
      cCol q * ((q : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) := by
  sorry
''')

_new('S9′', 'Z3NetC.col_mono', 'Dim3', 'thm:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:col`(3)**: within each residue class modulo `3`, `δN^{1/3} = cCol q` increases with `q`. -/
''', r'''
theorem col_mono (q q' : ℕ) (hq : 5 ≤ q) (hlt : q < q') (hmod : q % 3 = q' % 3) : cCol q < cCol q' := by
  sorry
''')

_new('S9′', 'Z3NetC.col_values', 'Dim3', 'thm:col', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:col`(3)**: `cCol 5 = √513/25 = 0.9059…`, `cCol 7 = √2009/49 = 0.9147…`, `cCol 37 = 0.9823…`,
`cCol 41 > 0.9913`; so `δN^{1/3} > 0.9059` for every `q ≥ 5` coprime to `6`, and `> 0.9823` from
`q ≥ 37` on. -/
''', r'''
theorem col_values :
    cCol 5 = Real.sqrt 513 / 25 ∧ cCol 7 = Real.sqrt 2009 / 49 ∧
    0.9059 < cCol 5 ∧ cCol 5 < 0.9060 ∧ 0.9147 < cCol 7 ∧ cCol 7 < 0.9148 ∧
    0.9823 < cCol 37 ∧ cCol 37 < 0.9824 ∧ 0.9913 < cCol 41 ∧
    ∀ q : ℕ, Nat.Coprime q 6 → 5 ≤ q → 0.9059 < cCol q ∧ (37 ≤ q → 0.9823 < cCol q) := by
  sorry
''')

_new('S9′', 'Z3NetC.shared_count', 'Dim3', 'lem:shared', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`lem:shared`**: in a `(0,m,s)`-net in base `q`, digital or not (a family `X` of `q^m` points at
integer scale `q^m`), for two coordinates `a ≠ b` and `2(j+1) ≤ m`, every value `(α, β)` of the pair of
digits with index `j` of `a` and `b` occurs at exactly `q^{m-2}` points. -/
''', r'''
theorem shared_count {s q m : ℕ} [NeZero q] (X : (Fin m → ZMod q) → Fin s → ℕ)
    (hX : IsNet0 s q m X) (a b : Fin s) (hab : a ≠ b) (j : ℕ) (hj : 2 * (j + 1) ≤ m)
    (α β : ℕ) (hα : α < q) (hβ : β < q) :
    (univ.filter fun v : Fin m → ZMod q =>
        X v a / q ^ (m - 1 - j) % q = α ∧ X v b / q ^ (m - 1 - j) % q = β).card = q ^ (m - 2) := by
  sorry
''')

_new('S9′', 'Z3NetC.shared_fun', 'Dim3', 'lem:shared', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`lem:shared`**: if the digit with index `j` of `b` is a function `f` of the digit with index `j`
of `a` at every point (`q ≥ 2`), then `2(j+1) > m`. -/
''', r'''
theorem shared_fun {s q m : ℕ} [NeZero q] (hq : 2 ≤ q) (X : (Fin m → ZMod q) → Fin s → ℕ)
    (hX : IsNet0 s q m X) (a b : Fin s) (hab : a ≠ b) (j : ℕ) (f : ℕ → ℕ)
    (hf : ∀ v, X v b / q ^ (m - 1 - j) % q = f (X v a / q ^ (m - 1 - j) % q)) :
    m < 2 * (j + 1) := by
  sorry
''')

_new('S9′', 'Z3NetC.colfree', 'Dim3', 'prop:colfree', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`prop:colfree`**: points `X(n) = q² n + q h(n) 𝟏 + j(n)` (one per cell `n`, integer scale `q³`),
`h(n) ∈ [0, q)` with `h(n) ≡ a·n + β (mod q)`, `a = (q𝟏 + w)/3` (`∑ w = 0`, `w_c ≡ -q (mod 3)`), and
arbitrary `j(n) ∈ [0, q)³`: any two distinct points have toroidal distance at least
`q² - ((‖w‖₁ + 3) q - 3)/√3`. -/
''', r'''
theorem colfree {q : ℕ} [NeZero q] (hq : 2 ≤ q) (w : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (β : ℤ) (h : (Fin 3 → ZMod q) → ℕ)
    (j : (Fin 3 → ZMod q) → Fin 3 → ℕ) (hh : ∀ n, h n < q)
    (hcong : ∀ n, ((h n : ℕ) : ZMod q) = colH q w n + β) (hj : ∀ n c, j n c < q)
    (n n' : Fin 3 → ZMod q) (hne : n ≠ n') :
    (q : ℝ) ^ 2 - (((∑ c, |w c|) + 3) * q - 3) / Real.sqrt 3 ≤
      Real.sqrt (torusDist2 (q ^ 3) (fun c => q ^ 2 * (n c).val + q * h n + j n c)
        (fun c => q ^ 2 * (n' c).val + q * h n' + j n' c) : ℝ) := by
  sorry
''')

_new('S9′', 'Z3NetC.colshift_eq', 'Dim3', 'prop:colshift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`prop:colshift`(1)**: if the digital shift `τ` of `𝒞_q` has equal second digits `τ_{c,2}` and equal
third digits `τ_{c,3}` (Lean: `sh c 1`, `sh c 2`), the minimum distance of `𝒞_q ⊕ τ` is that of `𝒞_q`:
`3d² = 2q⁴ + τ²` (toroidal). -/
''', r'''
theorem colshift_eq {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q)
    (sh : Fin 3 → Fin 3 → ZMod q) (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1)
    (h3 : sh 0 2 = sh 1 2 ∧ sh 1 2 = sh 2 2) :
    (∀ v w : Fin 3 → ZMod q, v ≠ w → 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 ≤
      3 * (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℤ)) ∧
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧
      3 * (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℤ) = 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
  sorry
''')

_new('S9′', 'Z3NetC.colshift_agree2', 'Dim3', 'prop:colshift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`prop:colshift`(2)**: equal second shift digits: `δN^{1/3} ≥ 1 - (7q - 3)/(√3 q²)` (toroidal; integer
scale: `d ≥ q² - (7q - 3)/√3`). -/
''', r'''
theorem colshift_agree2 {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q)
    (sh : Fin 3 → Fin 3 → ZMod q) (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) (v w : Fin 3 → ZMod q)
    (hvw : v ≠ w) :
    (q : ℝ) ^ 2 - (7 * q - 3) / Real.sqrt 3 ≤
      Real.sqrt (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
        (digPointShift q 3 (colGen q) sh w) : ℝ) := by
  sorry
''')

_new('S9′', 'Z3NetC.colshift_lower', 'Dim3', 'prop:colshift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`prop:colshift`(3)**, lower bound: for every digital shift,
`δN^{1/3} ≥ (1 - (W+3)/q + 3/q²)/√3` (`W = 2` for `q ≡ 2`, `4` for `q ≡ 1 (mod 3)`; integer scale:
`d ≥ (q² - (W+3)q + 3)/√3`), and this exceeds `0.4693` for every `q ≥ 37`. -/
''', r'''
theorem colshift_lower {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q)
    (sh : Fin 3 → Fin 3 → ZMod q) :
    (∀ v w : Fin 3 → ZMod q, v ≠ w →
      ((q : ℝ) ^ 2 - ((if q % 3 = 2 then (2 : ℤ) else 4 : ℤ) + 3) * q + 3) / Real.sqrt 3 ≤
        Real.sqrt (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
          (digPointShift q 3 (colGen q) sh w) : ℝ)) ∧
    (37 ≤ q → 0.4693 < (1 - ((if q % 3 = 2 then (2 : ℤ) else 4 : ℤ) + 3) / (q : ℝ) + 3 / (q : ℝ) ^ 2) /
      Real.sqrt 3) := by
  sorry
''')

_new('S9′', 'Z3NetC.colshift_upper', 'Dim3', 'prop:colshift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`prop:colshift`(3)**, upper bound: if the second shift digits are not all equal, some pair of points
of `𝒞_q ⊕ τ` has Euclidean (hence toroidal) distance at most `√3 (q a_max + q - 1)` at integer scale
`q³`, `a_max = max_c a_c`; i.e. `δN^{1/3} ≤ (1 + (3 + w_max)/q - 3/q²)/√3`, `w_max = max_c w_c`
(`3 a_max = q + w_max`). -/
''', r'''
theorem colshift_upper {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q)
    (sh : Fin 3 → Fin 3 → ZMod q) (hne : ¬ (sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1)) :
    3 * univ.sup' univ_nonempty (colA q (wCol q)) = q + univ.sup' univ_nonempty (wCol q) ∧
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧
      (∀ c, |(digPointShift q 3 (colGen q) sh w c : ℤ) - (digPointShift q 3 (colGen q) sh v c : ℤ)| ≤
        q * univ.sup' univ_nonempty (colA q (wCol q)) + q - 1) ∧
      Real.sqrt (∑ c, ((digPointShift q 3 (colGen q) sh w c : ℝ) -
          (digPointShift q 3 (colGen q) sh v c : ℝ)) ^ 2) / (q : ℝ) ^ 2 ≤
        (1 + (3 + univ.sup' univ_nonempty (wCol q)) / (q : ℝ) - 3 / (q : ℝ) ^ 2) / Real.sqrt 3 ∧
      Real.sqrt (torusDist2 (q ^ 3) (digPointShift q 3 (colGen q) sh v)
          (digPointShift q 3 (colGen q) sh w) : ℝ) / (q : ℝ) ^ 2 ≤
        (1 + (3 + univ.sup' univ_nonempty (wCol q)) / (q : ℝ) - 3 / (q : ℝ) ^ 2) / Real.sqrt 3 := by
  sorry
''')

_new('S9′', 'Z3NetC.drift_step', 'Deficit', 'lem:drift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`lem:drift`(1)**: for the digital column net with the digits `n_c`, `a·n`, `ℓ·n`
(`a = (q𝟏 + w)/3`), a step along `e_i` has `Δ_i ≡ q a_i + r_i - q κ' (mod q²)` (`= ⅓q² + ε_i` or
`⅓q² + ε_i - q` with `3ε_i = q w_i + 3 r_i` when `3 a_i = q + w_i`), `r_i` the residue of `ℓ_i` and
`κ' = [j(n) + r_i ≥ q]` the wrap of the third digit; if `r_i ≠ 0`, both cases occur. -/
''', r'''
theorem drift_step {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (i : Fin 3) :
    (∀ n, colStep q (colPhi q w ℓ) i n ≡
      q * colA q w i + (((ℓ i : ℤ) : ZMod q)).val -
        q * (if (colJ q ℓ n).val + (((ℓ i : ℤ) : ZMod q)).val < q then 0 else 1) [ZMOD (q : ℤ) ^ 2]) ∧
    ((((ℓ i : ℤ) : ZMod q)).val ≠ 0 →
      (∃ n, (colJ q ℓ n).val + (((ℓ i : ℤ) : ZMod q)).val < q) ∧
      ∃ n, ¬ (colJ q ℓ n).val + (((ℓ i : ℤ) : ZMod q)).val < q) := by
  sorry
''')

_new('S9′', 'Z3NetC.drift_cycle', 'Deficit', 'lem:drift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`lem:drift`(2)**: along each cycle of `q` steps in the direction `e_i` the third digit wraps exactly
`r_i` times; if moreover `|ε_i| < ½q²` and `|ε_i - q| < ½q²` (in thirds: `2|q w_i + 3 r_i| < 3q²` and
`2|q w_i + 3 r_i - 3q| < 3q²`; revision 15.1), the excesses of the cycle sum to `⅓q² w_i` (Lean: three
times the excess, `excess3`, summing to `q² w_i`). -/
''', r'''
theorem drift_cycle {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (i : Fin 3)
    (n : Fin 3 → ZMod q) :
    (((univ.filter fun t : ZMod q =>
        ¬ (colJ q ℓ (n + Pi.single i t)).val + (((ℓ i : ℤ) : ZMod q)).val < q).card : ℕ) : ℤ) =
      (((ℓ i : ℤ) : ZMod q)).val ∧
    (2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val| < 3 * (q : ℤ) ^ 2 →
      2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q| < 3 * (q : ℤ) ^ 2 →
      ∑ t : ZMod q, excess3 q (colStep q (colPhi q w ℓ) i (n + Pi.single i t)) = (q : ℤ) ^ 2 * w i) := by
  sorry
''')

_new('S9′', 'Z3NetC.drift_range', 'Deficit', 'lem:drift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`lem:drift`(2)**, the instance of the range hypothesis: `|w_i| ≤ 2` and `q ≥ 4`. -/
''', r'''
theorem drift_range {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (i : Fin 3) (hw : |w i| ≤ 2) (hq : 4 ≤ q) :
    2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val| < 3 * (q : ℤ) ^ 2 ∧
      2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q| < 3 * (q : ℤ) ^ 2 := by
  sorry
''')

_new('S9′', 'Z3NetC.drift_eta', 'Deficit', 'lem:drift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`lem:drift`(3)**: if `q ≥ 10` and `|w_c| ≤ 2`, every excess (thirds) lies in `[-½q², q²]` (the paper's
`[-⅙q², ⅓q²]`), the largest one is `M = max_i (q w_i + 3 r_i)` (`3 max_i ε_i`), and
`3g = q² - M` in `thm:colmin`, i.e. `d² = q⁴ - 2q²η + 3η²` with `η = M/3`. -/
''', r'''
theorem drift_eta {q : ℕ} [NeZero q] (hq : 10 ≤ q) (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (hw2 : ∀ c, |w c| ≤ 2) :
    (∀ i n, -(q : ℤ) ^ 2 ≤ 2 * excess3 q (colStep q (colPhi q w ℓ) i n) ∧
      excess3 q (colStep q (colPhi q w ℓ) i n) ≤ (q : ℤ) ^ 2) ∧
    (∀ i n, excess3 q (colStep q (colPhi q w ℓ) i n) ≤
      univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) ∧
    (∃ i n, excess3 q (colStep q (colPhi q w ℓ) i n) =
      univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) ∧
    (colGap q (colPhi q w ℓ) : ℤ) =
      (q : ℤ) ^ 2 - univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val := by
  sorry
''')

_new('S9′', 'Z3NetC.drift_net', 'Deficit', 'lem:drift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`lem:drift`(4)**: if the digital column net is a `(0,3,3)`-net, then `∑_i ε_i ≥ q` (thirds:
`∑_i (q w_i + 3 r_i) ≥ 3q`), `max_i ε_i ≥ ⅓q` (thirds: `≥ q`), and `max_i ε_i ≥ ⅔q` (thirds: `≥ 2q`)
if `q ≡ 1 (mod 3)`. -/
''', r'''
theorem drift_net {q : ℕ} [NeZero q] (hq : 2 ≤ q) (w ℓ : Fin 3 → ℤ) (hw0 : ∑ c, w c = 0)
    (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (hℓ : (q : ℤ) ∣ ∑ c, ℓ c)
    (hnet : IsNet0 3 q 3 (digPoint q 3 (colGenW q w ℓ))) :
    3 * (q : ℤ) ≤ ∑ i, ((q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) ∧
    (q : ℤ) ≤ (univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) ∧
    (q % 3 = 1 →
      2 * (q : ℤ) ≤ univ.sup' univ_nonempty fun i => (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val) := by
  sorry
''')

_new('S9′', 'Z3NetC.colceil', 'Deficit', 'cor:colceil', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`cor:colceil`**: every column point set in base `q ≥ 2` has `3g ≤ q²`, i.e. a pair of distinct points
at toroidal distance at most `q²` at integer scale `q³` (`δN^{1/3} ≤ 1`). -/
''', r'''
theorem colceil {q : ℕ} [NeZero q] (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    colGap q φ ≤ q ^ 2 ∧ ∃ n n' : Fin 3 → ZMod q, n ≠ n' ∧
      torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') ≤ q ^ 4 := by
  sorry
''')

_new('S9′', 'Z3NetC.colO_net_iff', 'Deficit', 'thm:O', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:O`(1)** (every `q ≥ 2`): a column point set is a `(0,3,3)`-net in base `q` if and only if `φ` is a
bijection from `T` onto `{0, …, q²-1}` (onto, and equal heights only within a column) and `⌊φ/q⌋` is
injective on every line of `T` in the directions `[e_x], [e_y], [e_z]`. -/
''', r'''
theorem colO_net_iff {q : ℕ} [NeZero q] (hq : 2 ≤ q) (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) :
    IsNet0 3 q 3 (colPt q φ) ↔
      ((∀ y, y < q ^ 2 → ∃ n, φ n = y) ∧
        (∀ n n', φ n = φ n' → ∃ t : ZMod q, n' = n + fun _ => t)) ∧
      (∀ (c : Fin 3) n (t : ZMod q), φ (n + Pi.single c t) / q = φ n / q → t = 0) := by
  sorry
''')

_new('S9′', 'Z3NetC.colO_even', 'Deficit', 'thm:O', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:O`(2)** (every even `q ≥ 2`): no column point set is a `(0,3,3)`-net in base `q`. -/
''', r'''
theorem colO_even {q : ℕ} [NeZero q] (hq : 2 ≤ q) (he : Even q) (φ : (Fin 3 → ZMod q) → ℕ)
    (hφ : IsHeight q φ) : ¬ IsNet0 3 q 3 (colPt q φ) := by
  sorry
''')

_new('S9′', 'Z3NetC.colO_opt', 'Deficit', 'thm:O', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`thm:O`(3)**: for odd `q ≥ 4` with `3 ∤ q`, every column point set that is a `(0,3,3)`-net has
`3g ≤ τ`, i.e. toroidal minimum distance `d` with `3d² ≤ 2q⁴ + τ² = 3d²(𝒞_q)` (`thm:col`(2)). -/
''', r'''
theorem colO_opt {q : ℕ} [NeZero q] (hq : 4 ≤ q) (h3 : ¬ 3 ∣ q) (hodd : Odd q)
    (φ : (Fin 3 → ZMod q) → ℕ) (hφ : IsHeight q φ) (hnet : IsNet0 3 q 3 (colPt q φ)) :
    (colGap q φ : ℤ) ≤ tauCol q ∧ ∃ n n' : Fin 3 → ZMod q, n ≠ n' ∧
      3 * (torusDist2 (q ^ 3) (colPt q φ n) (colPt q φ n') : ℤ) ≤ 2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
  sorry
''')

_new('S9′', 'Z3NetC.allmshift_m3', 'DGS', 'cor:allmshift', 'Z3NetC', ['open Z3NetF Finset Matrix'], r'''
/-- **`cor:allmshift`**, the resolution `m = 3` (the column net `𝒞_p`): for every prime `p ≥ 37` and every
digital shift `τ` (Lean: `sh c k` is the digit `k+1` of the shift of coordinate `c`), `𝒞_p ⊕ τ` keeps one
point in every cell (`h ≤ √3 N^{-1/3}`) and has `δN^{1/3} > 0.4693` (toroidal); if the shift digits of
the three coordinates agree at the second and third digit, `δN^{1/3}` is the exact value of
`thm:col`(2) (`cCol p`); if they agree at the second digit, `δN^{1/3} ≥ 1 - (7p-3)/(√3p²)`; otherwise
`1/√3 - 7/(√3p) ≤ δN^{1/3} ≤ 1/√3 + 5/(√3p)`. -/
''', r'''
theorem allmshift_m3 (p : ℕ) [NeZero p] (hp : p.Prime) (hp37 : 37 ≤ p) (sh : Fin 3 → Fin 3 → ZMod p) :
    (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin 3 → ZMod p,
      Real.sqrt (∑ c, (y c - (digPointShift p 3 (colGen p) sh v c : ℝ) / (p : ℝ) ^ 3) ^ 2) ≤
        Real.sqrt 3 * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ)))) ∧
    (∀ v w : Fin 3 → ZMod p, v ≠ w → 0.4693 * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) <
      Real.sqrt (∑ c, ((cres (p ^ 3) ((digPointShift p 3 (colGen p) sh v c : ℤ) -
        (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2)) ∧
    ((sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) → (sh 0 2 = sh 1 2 ∧ sh 1 2 = sh 2 2) →
      (∀ v w : Fin 3 → ZMod p, v ≠ w → cCol p * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
        Real.sqrt (∑ c, ((cres (p ^ 3) ((digPointShift p 3 (colGen p) sh v c : ℤ) -
          (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2)) ∧
      ∃ v w : Fin 3 → ZMod p, v ≠ w ∧ Real.sqrt (∑ c, ((cres (p ^ 3)
        ((digPointShift p 3 (colGen p) sh v c : ℤ) - (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) /
          (p : ℝ) ^ 3) ^ 2) = cCol p * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ)))) ∧
    ((sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) → ∀ v w : Fin 3 → ZMod p, v ≠ w →
      (1 - (7 * p - 3) / (Real.sqrt 3 * (p : ℝ) ^ 2)) * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
        Real.sqrt (∑ c, ((cres (p ^ 3) ((digPointShift p 3 (colGen p) sh v c : ℤ) -
          (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2)) ∧
    (¬ (sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1) →
      (∀ v w : Fin 3 → ZMod p, v ≠ w →
        (1 / Real.sqrt 3 - 7 / (Real.sqrt 3 * p)) * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (p ^ 3) ((digPointShift p 3 (colGen p) sh v c : ℤ) -
            (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) / (p : ℝ) ^ 3) ^ 2)) ∧
      ∃ v w : Fin 3 → ZMod p, v ≠ w ∧ Real.sqrt (∑ c, ((cres (p ^ 3)
        ((digPointShift p 3 (colGen p) sh v c : ℤ) - (digPointShift p 3 (colGen p) sh w c : ℤ)) : ℝ) /
          (p : ℝ) ^ 3) ^ 2) ≤ (1 / Real.sqrt 3 + 5 / (Real.sqrt 3 * p)) * ((p : ℝ) ^ 3) ^ (-(1 / (3 : ℝ)))) := by
  sorry
''')

_new('S9′', 'Z3NetF.Kone', 'Deficit', 'lem:Kone', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`lem:Kone`**: a design `F` (with `L ≥ 1` levels) with some nonzero off-diagonal entry `F₀[a][b]` has
deficit `K(F) ≥ 1`. -/
''', r'''
theorem Kone {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (hL : 1 ≤ L) (a b : Fin s) (hab : a ≠ b)
    (h : F 0 a b ≠ 0) : 1 ≤ Kdef F L := by
  sorry
''')

# ---------------------------------------------------------------- stage S10′ (digital shifts and the DGS results:
# `def:dshift`, `lem:shift`, `prop:shift`, `cor:allmshift` for m ≥ 4, `prop:linf`, `cor:dgs`, `rem:dgsfinite`).
# Statement review: the statement-review notes (research repository). Definitions `Z3Net/DShiftDefs.lean` (`dshiftCoord`, `dshiftPt`, `cellOff`
# added), `Z3Net/DGSDefs.lean` (`Z3NetA.AGen`; the definitions of Dick, Goda and Suzuki, namespace `Z3NetDGS`);
# restatements `Z3Net/DGSMain.lean`.
EXTRA_MODS['Prelim'] = EXTRA_MODS.get('Prelim', []) + ['Z3Net.DShiftDefs']
EXTRA_MODS['DGS'] = EXTRA_MODS.get('DGS', []) + ['Z3Net.DGSDefs', 'Z3Net.Defs', 'Z3Net.ThmADefs']
EXTRA_SOLUTION.append('Z3Net.DGSMain')

_FO = ['open Matrix Finset']
_AO = ['open Matrix Finset Z3NetF']
_DO = ['open Finset Matrix']

_new('S10′', 'Z3NetF.digPointShift_eq_dshiftPt', 'Prelim', 'def:dshift', 'Z3NetF', _FO, r'''
/-- **`def:dshift`**: the digitally shifted digital point set `P ⊕ τ` (`digPointShift`: the digits `C_c v + τ_c`
of the point with index `v`, added digit by digit modulo `q` without carries) is the shift `dshiftPt q m τ`
of the points of `P`, where the digits of an integer coordinate `x ∈ [0, q^m)` are read off `x`
(`⌊x/q^(m-1-j)⌋ mod q`, digit `0` most significant). -/
''', r'''
theorem digPointShift_eq_dshiftPt {s q m : ℕ} [NeZero q] (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (τ : Fin s → Fin m → ZMod q) (v : Fin m → ZMod q) :
    digPointShift q m C τ v = dshiftPt q m τ (digPoint q m C v) := by
  sorry
''')

_new('S10′', 'Z3NetF.digPointShift_zero', 'Prelim', 'def:dshift', 'Z3NetF', _FO, r'''
/-- **`def:dshift`**: a digital net is the unshifted (`τ = 0`) digitally shifted net. -/
''', r'''
theorem digPointShift_zero {s q m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) :
    digPointShift q m C 0 = digPoint q m C := by
  sorry
''')

_new('S10′', 'Z3NetF.shift_net', 'DGS', 'lem:shift', 'Z3NetF', _FO, r'''
/-- **`lem:shift`**, the net property, for any point set: a digital shift maps every elementary box of shape
`d` bijectively onto one of the same shape, so the shift `X ⊕ τ` (`dshiftPt`) of a `(0,m,s)`-net `X` in base
`q` (integer points in `[0, q^m)^s`, digital or not) is a `(0,m,s)`-net. -/
''', r'''
theorem shift_net {s q m : ℕ} [NeZero q] (X : (Fin m → ZMod q) → Fin s → ℕ) (hX : ∀ v c, X v c < q ^ m)
    (τ : Fin s → Fin m → ZMod q) (h : IsNet0 s q m X) :
    IsNet0 s q m (fun v => dshiftPt q m τ (X v)) := by
  sorry
''')

_new('S10′', 'Z3NetF.digPointShift_net', 'DGS', 'lem:shift', 'Z3NetF', _FO, r'''
/-- **`lem:shift`**, the net property, digital nets: `P ⊕ τ` is a `(0,m,s)`-net if `P` is (every digital
shift `τ`). -/
''', r'''
theorem digPointShift_net {s q m : ℕ} [NeZero q] (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (τ : Fin s → Fin m → ZMod q) (h : IsNet0 s q m (digPoint q m C)) :
    IsNet0 s q m (digPointShift q m C τ) := by
  sorry
''')

_new('S10′', 'Z3NetF.shift_graph', 'DGS', 'lem:shift', 'Z3NetF', _FO, r'''
/-- **`lem:shift`**: let `P` be the graph form over `ℤ/qℤ` with depths `K` and blocks `Φ`, and `τ_c =
(τ^cell_c, τ^off_c)` (`cellOff`: the `K_c` cell digits followed by the `m - K_c` offset digits) a digital
shift. After re-indexing by the cells (`v ↦ v + T`), `P ⊕ τ` is the affine graph form whose coordinate `c`
has the digits `n_c` followed by `∑_d Φ_cd n_d + γ_c`, `γ_c = τ^off_c - ∑_d Φ_cd τ^cell_d` (the shift
`(0, γ_c)` of the graph form). -/
''', r'''
theorem shift_graph {s q m : ℕ} [NeZero q] (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) (ZMod q))
    (τc : (c : Fin s) → Fin (K c) → ZMod q) (τo : (c : Fin s) → Fin (m - K c) → ZMod q) :
    ∃ T : Fin m → ZMod q, ∀ v : Fin m → ZMod q,
      digPointShift q m (graphGenK K Φ) (fun c => cellOff (τc c) (τo c)) v =
        digPointShift q m (graphGenK K Φ)
          (fun c => cellOff 0 (fun r => τo c r - ∑ d, ∑ l, Φ c d r l * τc d l)) (v + T) := by
  sorry
''')

_new('S10′', 'Z3NetF.shift_graph_cells', 'DGS', 'lem:shift', 'Z3NetF', _FO, r'''
/-- **`lem:shift`**: every digital shift of a graph form with depths `K` holds exactly one point in every cell
(every box of shape `K`). -/
''', r'''
theorem shift_graph_cells {s q m : ℕ} [NeZero q] (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) (ZMod q)) (τ : Fin s → Fin m → ZMod q) :
    ∀ a : Fin s → ℕ, (∀ c, a c < q ^ K c) →
      ∃! v : Fin m → ZMod q, ∀ c, digPointShift q m (graphGenK K Φ) τ v c / q ^ (m - K c) = a c := by
  sorry
''')

_new('S10′', 'Z3NetF.Ss_coord_shift', 'DGS', 'prop:shift', 'Z3NetF', _FO, r'''
/-- **`prop:shift`**, `lem:Ss` (the coordinate bounds) verbatim for every digitally shifted net: the statement of
`Ss_coord` with the points of `P ⊕ τ` in place of those of `P`. -/
''', r'''
theorem Ss_coord_shift {s q k L : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (h1 : H1 F L Φ) (h2 : H2 Φ) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ) (he : ∀ d, -1 ≤ e d ∧ e d ≤ 1)
    (hcell : ∀ d, ((digPointShift q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) τ w d /
        q ^ (s * k - k) : ℕ) : ℤ) = ((digPointShift q (s * k)
          (graphGenK (m := s * k) (fun _ => k) Φ) τ v d / q ^ (s * k - k) : ℕ) + e d) % (q ^ k : ℕ))
    (i : Fin s) :
    bval q F L e (fun d => carryLen q k (digPointShift q (s * k)
        (graphGenK (m := s * k) (fun _ => k) Φ) τ v d / q ^ (s * k - k)) (e d)) i *
          (q ^ (s * k - k) : ℕ) ≤
      (q : ℤ) * |e i * (q ^ (s * k - k) : ℕ) +
        ((digPointShift q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) τ w i %
          q ^ (s * k - k) : ℕ) : ℤ) -
        ((digPointShift q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) τ v i %
          q ^ (s * k - k) : ℕ) : ℤ)| := by
  sorry
''')

_new('S10′', 'Z3NetF.Ss_sep_shift', 'DGS', 'prop:shift', 'Z3NetF', _FO, r'''
/-- **`prop:shift`**: `lem:Ss` (the separation) holds verbatim, with the same bound, for every digitally shifted
net: the statement of `Ss_sep` for `P ⊕ τ`. -/
''', r'''
theorem Ss_sep_shift {s q k L : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (h1 : H1 F L Φ) (h2 : H2 Φ) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, IsConfig k e j → B ≤ ∑ i, bval q F L e j i ^ 2)
    (τ : Fin s → Fin (s * k) → ZMod q) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * k))
        (digPointShift q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) τ v)
        (digPointShift q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) τ w) : ℤ) := by
  sorry
''')

_new('S10′', 'Z3NetF.D_sep_shift', 'DGS', 'prop:shift', 'Z3NetF', _FO, r'''
/-- **`prop:shift`**, `prop:D` applied to `𝒫^F_{k,q}` for every digital shift: the statement of `D_sep` for
`𝒫^F_{k,q} ⊕ τ`. -/
''', r'''
theorem D_sep_shift {R : Type*} [CommRing R] {s q a k : ℕ} [NeZero q] (hs : 2 ≤ s) (ψ : R →+* ZMod q)
    (hk : 1 ≤ k) (inf : Fin s) (x : Fin s → R) (hx : PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : BetaRel inf x (fun n c d => (F n c d : R)) lam β)
    (α : Fin s → ℕ) (h0 : ∀ c, F 0 c c = -(α c : ℤ)) (hdiag : ∀ n c, 1 ≤ n → F n c c = 0)
    (hdom : ∀ c, ∑ d ∈ univ.filter (fun d => d ≠ c),
      (range (s - 1)).sup (fun j => (Msum F j c d).natAbs) ≤ α c)
    (ha : ∀ c, α c ≤ a) (hq : 5 * a + 4 ≤ q) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - a) ^ 2 ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * k))
        (digPointShift q (s * k) (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) τ v)
        (digPointShift q (s * k) (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) τ w) :
          ℤ) := by
  sorry
''')

_new('S10′', 'Z3NetA.Apoint_eq_AGen', 'DGS', 'prop:shift', 'Z3NetA', _AO, r'''
/-- The net `𝒫^{U*_s}_{k,q}` of `thm:A` (`Apoint`) is the digital point set of the generator matrices `AGen`
(so that its digital shifts are `digPointShift q (s k) (AGen s q k) τ`, `def:dshift`). -/
''', r'''
theorem Apoint_eq_AGen (s q k : ℕ) [NeZero s] : Apoint s q k = digPoint q (s * k) (AGen s q k) := by
  sorry
''')

_new('S10′', 'Z3NetA.A_net_shift', 'DGS', 'prop:shift', 'Z3NetA', _AO, r'''
/-- **`lem:shift`** for `thm:A`(1): every digital shift of `𝒫^{U*_s}_{k,q}` is a `(0,sk,s)`-net over `ℤ/qℤ` (one
point in every cell), and every `x ∈ [0,1]^s` is within Euclidean distance `√s q^(-k) = √s N^(-1/s)` of one of
its points. -/
''', r'''
theorem A_net_shift (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (τ : Fin s → Fin (s * k) → ZMod q) :
    IsNet0 s q (s * k) (digPointShift q (s * k) (AGen s q k) τ) ∧
      ∀ x : Fin s → ℝ, (∀ c, 0 ≤ x c ∧ x c ≤ 1) → ∃ v : Fin (s * k) → ZMod q,
        ∑ c, (x c - (digPointShift q (s * k) (AGen s q k) τ v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤
          (s : ℝ) / ((q : ℝ) ^ k) ^ 2 := by
  sorry
''')

_new('S10′', 'Z3NetA.A_sep_shift', 'DGS', 'prop:shift', 'Z3NetA', _AO, r'''
/-- **`prop:shift`**, `thm:A`(2) for every digital shift, exact integer form: the statement of `A_sep` for
`𝒫^{U*_s}_{k,q} ⊕ τ`. -/
''', r'''
theorem A_sep_shift (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aStar s) ^ 2 ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (s * k)) (digPointShift q (s * k) (AGen s q k) τ v)
        (digPointShift q (s * k) (AGen s q k) τ w) : ℤ) := by
  sorry
''')

_new('S10′', 'Z3NetA.A_sep_shift_real', 'DGS', 'prop:shift', 'Z3NetA', _AO, r'''
/-- **`prop:shift`**, `thm:A`(2) for every digital shift, real toroidal form: `δ ≥ (1 - a*_s/q) N^(-1/s)`. -/
''', r'''
theorem A_sep_shift_real (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((digPointShift q (s * k) (AGen s q k) τ v c : ℤ) -
          (digPointShift q (s * k) (AGen s q k) τ w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetA.A_sep_shift_eucl', 'DGS', 'prop:shift', 'Z3NetA', _AO, r'''
/-- **`prop:shift`**, `thm:A`(2) for every digital shift, Euclidean form. -/
''', r'''
theorem A_sep_shift_eucl (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aStar s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, (((digPointShift q (s * k) (AGen s q k) τ v c : ℝ) -
          digPointShift q (s * k) (AGen s q k) τ w c) / (q : ℝ) ^ (s * k)) ^ 2) := by
  sorry
''')
EXTRA_MODS['DGS'] = EXTRA_MODS.get('DGS', []) + ['Z3Net.S1Defs', 'Z3Net.KNDefs', 'Z3Net.Dim3Defs']

_ZO = ['open Matrix']
_PS = '(Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ'

_new('S10′', 'Z3Net.P_sep_shift', 'DGS', 'prop:shift', 'Z3Net', _ZO, r'''
/-- **`prop:shift`, `thm:sep` / `thm:main`(3)** for every digital shift `τ`, exact integer form: the statement of
`P_sep` for `𝒫_{k,q} ⊕ τ`. -/
''', r'''
theorem P_sep_shift (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) *
        min (((q : ℤ) - 1) ^ 2) (min (((q : ℤ) - 2) ^ 2 + ((q : ℤ) - 4) ^ 2) (3 * ((q : ℤ) - 3) ^ 2))
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k))
          (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ v)
          (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ w) : ℤ) := by
  sorry
''')

_new('S10′', 'Z3Net.P_sep_shift_ge8', 'DGS', 'prop:shift', 'Z3Net', _ZO, r'''
/-- **`prop:shift`, `thm:main`(3), "in particular"**, for every digital shift: for `q ≥ 8`, `δ ≥ (1 - 1/q) N^(-1/3)`. -/
''', r'''
theorem P_sep_shift_ge8 (q k : ℕ) (hq : 8 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * ((q : ℤ) - 1) ^ 2
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k))
          (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ v)
          (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ w) : ℤ) := by
  sorry
''')

_new('S10′', 'Z3Net.P_sep_shift_real', 'DGS', 'prop:shift', 'Z3Net', _ZO, r'''
/-- **`prop:shift`, `thm:main`(3), real form**, for every digital shift: `δ ≥ c(q) N^(-1/3)` (toroidal). -/
''', r'''
theorem P_sep_shift_real (q k : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    cP q * ((q : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (3 * k))
          ((Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ v c : ℤ) -
            (Z3NetF.digPointShift q (3 * k) (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) τ w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (3 * k)) ^ 2) := by
  sorry
''')

# ---- thm:S1 (namespace Z3NetS1)
_SO = ['open Matrix Finset']
_SM = 's * k + (s - 1)'
_new('S10′', 'Z3NetS1.S1_sep_shift', 'DGS', 'prop:shift', 'Z3NetS1', _SO, r'''
/-- **`prop:shift`, `thm:S1`(1)** for every digital shift, integer form: the statement of `S1_sep` for `P ⊕ τ`. -/
''', r'''
theorem S1_sep_shift (s p k ρ : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k ρ C) (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p)
    (v w : Fin (s * k + (s - 1)) → ZMod p) (hvw : v ≠ w) :
    (ρ - 1) ^ 2 * p ^ (2 * ((s - 1) * (k + 1) - 1)) ≤
      torusDist2 (p ^ (s * k + (s - 1))) (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v)
        (Z3NetF.digPointShift p (s * k + (s - 1)) C τ w) := by
  sorry
''')

_new('S10′', 'Z3NetS1.S1_sep_shift_real', 'DGS', 'prop:shift', 'Z3NetS1', _SO, r'''
/-- **`prop:shift`, `thm:S1`(1)** for every digital shift, real form: `δ ≥ (ρ - 1) p^(-1/s) N^(-1/s)`. -/
''', r'''
theorem S1_sep_shift_real (s p k ρ : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k ρ C) (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p)
    (v w : Fin (s * k + (s - 1)) → ZMod p) (hvw : v ≠ w) :
    ((ρ : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 1)))
          ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℤ) -
            (Z3NetF.digPointShift p (s * k + (s - 1)) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (s * k + (s - 1))) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetS1.S1_cells_shift', 'DGS', 'prop:shift', 'Z3NetS1', _SO, r'''
/-- **`prop:shift`, `thm:S1`(2)** for every digital shift: the occupied fine cells of `P ⊕ τ` (the first `k + 1`
digits of every coordinate) are exactly the cells of a coset `g + Λ` of the lattice `Λ` (`S1lat`). -/
''', r'''
theorem S1_cells_shift (s p k ρ : ℕ) (hs : 2 ≤ s) (hp : p.Prime)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k ρ C) (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p) :
    ∃ g : Fin s → ℤ,
      (∀ v, (fun c => ((Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c /
          p ^ (s * k + (s - 1) - (k + 1)) : ℕ) : ℤ) - g c) ∈ S1lat s p ρ) ∧
      ∀ a : Fin s → ℕ, (∀ c, a c < p ^ (k + 1)) → (fun c => (a c : ℤ) - g c) ∈ S1lat s p ρ →
        ∃! v, ∀ c, Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c /
          p ^ (s * k + (s - 1) - (k + 1)) = a c := by
  sorry
''')

_new('S10′', 'Z3NetS1.S1_cover_shift', 'DGS', 'prop:shift', 'Z3NetS1', _SO, r'''
/-- **`prop:shift`, `thm:S1`(3), covering**, for every digital shift: `h N^(1/s) ≤ √s (μ + 1) p^(-1/s)`. -/
''', r'''
theorem S1_cover_shift (s p k : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hps : 2 ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k (rhoS s p) C) (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p)
    (y : Fin s → ℝ) (hy : ∀ c, 0 ≤ y c ∧ y c < 1) :
    ∃ v, Real.sqrt (∑ c, (y c - (Z3NetF.digPointShift p (s * k + (s - 1)) C τ v c : ℝ) /
        (p : ℝ) ^ (s * k + (s - 1))) ^ 2)
      < Real.sqrt s * ((muS s p (rhoS s p) : ℝ) + 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) *
          ((p : ℝ) ^ (s * k + (s - 1))) ^ (-(1 / (s : ℝ))) := by
  sorry
''')

# ---- thm:allm, rem:B2, cor:allmshift (namespace Z3NetKN)
_KO = ['open Matrix']
_new('S10′', 'Z3NetKN.B1_sep_shift', 'DGS', 'prop:shift', 'Z3NetKN', _KO, r'''
/-- **`prop:shift`, `thm:allm`** for every digital shift, integer form: the statement of `B1_sep` for `P ⊕ τ`. -/
''', r'''
theorem B1_sep_shift (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 2 ≤ ρ)
    (hρp : ρ ^ 2 * (ρ + 1) ≤ p)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p))
    (hC : IsKNskel 1 p k (skB1 ρ) C) (τ : Fin 3 → Fin (3 * k + 1) → ZMod p)
    (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    (ρ ^ 2 - 4) ^ 2 * p ^ (4 * k) ≤
      torusDist2 (p ^ (3 * k + 1)) (Z3NetF.digPointShift p (3 * k + 1) C τ v)
        (Z3NetF.digPointShift p (3 * k + 1) C τ w) := by
  sorry
''')

_new('S10′', 'Z3NetKN.B1_sep_shift_real', 'DGS', 'prop:shift', 'Z3NetKN', _KO, r'''
/-- **`prop:shift`, `thm:allm`** for every digital shift, real form: `δ ≥ (ρ² - 4) p^(-2/3) N^(-1/3)`. -/
''', r'''
theorem B1_sep_shift_real (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 2 ≤ ρ)
    (hρp : ρ ^ 2 * (ρ + 1) ≤ p)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p))
    (hC : IsKNskel 1 p k (skB1 ρ) C) (τ : Fin 3 → Fin (3 * k + 1) → ZMod p)
    (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    ((ρ : ℝ) ^ 2 - 4) * (p : ℝ) ^ (-(2 / (3 : ℝ))) * ((p : ℝ) ^ (3 * k + 1)) ^ (-(1 / (3 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k + 1))
          ((Z3NetF.digPointShift p (3 * k + 1) C τ v c : ℤ) -
            (Z3NetF.digPointShift p (3 * k + 1) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k + 1)) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetKN.B2_rem_sep_shift_real', 'DGS', 'prop:shift', 'Z3NetKN', _KO, r'''
/-- **`prop:shift`, `rem:B2`** (`thm:S1` at `s = 3`) for every digital shift, real form:
`δ ≥ (ρ - 1) p^(-1/3) N^(-1/3)`. -/
''', r'''
theorem B2_rem_sep_shift_real (p k ρ : ℕ) (hp : p.Prime) (hρ : 1 ≤ ρ) (hρp : ρ ^ 3 < p)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p))
    (hC : IsKNskel 2 p k (skB2 ρ) C) (τ : Fin 3 → Fin (3 * k + 2) → ZMod p)
    (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    ((ρ : ℝ) - 1) * (p : ℝ) ^ (-(1 / (3 : ℝ))) * ((p : ℝ) ^ (3 * k + 2)) ^ (-(1 / (3 : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k + 2))
          ((Z3NetF.digPointShift p (3 * k + 2) C τ v c : ℤ) -
            (Z3NetF.digPointShift p (3 * k + 2) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k + 2)) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetKN.allmshift', 'DGS', 'cor:allmshift', 'Z3NetKN', _KO, r'''
/-- **`cor:allmshift`**, every `m ≥ 4`: for every prime `p ≥ 37` there are digital `(0,m,3)`-nets over `𝔽_p` (those of
`cor:allm`: `thm:main` for `m ≡ 0`, `thm:allm` for `m ≡ 1`, `thm:S1` at `s = 3` for `m ≡ 2`, `ρ` maximal) such that
every digital shift `τ` of them (`τ = 0` included) is a `(0,m,3)`-net with the separation bound `bndDim3 p` of
`cor:allm` (`> 0.2715`, `> 0.4250` for `p ≥ 83`, `→ 1` as `p → ∞`: `bndDim3_gt`, `bndDim3_tendsto`), the covering
bounds of `cor:allm`, and, in some coordinate, toroidal distance at least `p^(-(⌊m/3⌋ + 1))` (used for `cor:dgs`). -/
''', r'''
theorem allmshift (p m : ℕ) (hp : p.Prime) (hp37 : 37 ≤ p) (hm : 4 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : Fin 3 → Fin m → ZMod p,
      IsNet0 p m (Z3NetF.digPointShift p m C τ) ∧
      (∀ v w : Fin m → ZMod p, v ≠ w →
        bndDim3 p * ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ))) ≤
          Real.sqrt (∑ c, ((cres (p ^ m) ((Z3NetF.digPointShift p m C τ v c : ℤ) -
            (Z3NetF.digPointShift p m C τ w c : ℤ)) : ℝ) / (p : ℝ) ^ m) ^ 2)) ∧
      (∀ y : Fin 3 → ℝ, (∀ c, 0 ≤ y c ∧ y c < 1) → ∃ v : Fin m → ZMod p,
        Real.sqrt (∑ c, (y c - (Z3NetF.digPointShift p m C τ v c : ℝ) / (p : ℝ) ^ m) ^ 2) ≤
          (if m % 3 = 0 then Real.sqrt 3
           else if m % 3 = 1 then (p : ℝ) ^ (1 / (3 : ℝ)) * Real.sqrt (2 + 1 / (p : ℝ) ^ 2)
           else min ((p : ℝ) ^ (2 / (3 : ℝ)) * Real.sqrt (1 + 2 / (p : ℝ) ^ 2)) 4.264) *
            ((p : ℝ) ^ m) ^ (-(1 / (3 : ℝ)))) ∧
      (∀ v w : Fin m → ZMod p, v ≠ w → ∃ c : Fin 3,
        p ^ (m - (m / 3 + 1)) ≤ cres (p ^ m) ((Z3NetF.digPointShift p m C τ v c : ℤ) -
          (Z3NetF.digPointShift p m C τ w c : ℤ))) := by
  sorry
''')

# ---- prop:colshift(1) Euclidean, rem:shiftshared (namespace Z3NetC)
_CO = ['open Z3NetF Finset Matrix']
_new('S10′', 'Z3NetC.colshift_eq_eucl', 'Dim3', 'prop:colshift', 'Z3NetC', _CO, r'''
/-- **`prop:colshift`(1), Euclidean exactness**: with equal second and third shift digits some two points of
`𝒞_q ⊕ τ` differ by exactly `D` (no coordinate wraps), so the Euclidean minimum distance is the toroidal one:
`3‖D‖² = 2q⁴ + τ²`. -/
''', r'''
theorem colshift_eq_eucl {q : ℕ} [NeZero q] (h6 : Nat.Coprime q 6) (hq : 5 ≤ q)
    (sh : Fin 3 → Fin 3 → ZMod q) (h2 : sh 0 1 = sh 1 1 ∧ sh 1 1 = sh 2 1)
    (h3 : sh 0 2 = sh 1 2 ∧ sh 1 2 = sh 2 2) :
    ∃ v w : Fin 3 → ZMod q, v ≠ w ∧
      (∀ c, (digPointShift q 3 (colGen q) sh w c : ℤ) - digPointShift q 3 (colGen q) sh v c = DCol q c) ∧
      3 * ∑ c, ((digPointShift q 3 (colGen q) sh w c : ℤ) - digPointShift q 3 (colGen q) sh v c) ^ 2 =
        2 * (q : ℤ) ^ 4 + tauCol q ^ 2 := by
  sorry
''')

_new('S10′', 'Z3NetC.shiftshared_col', 'DGS', 'rem:shiftshared', 'Z3NetC', _CO, r'''
/-- **`rem:shiftshared`**, the column net: for every `q ≥ 11` the upper bound `(1 + (3 + w_max)/q - 3/q²)/√3` of
`prop:colshift`(3) (shifts whose second digits are not all equal) lies strictly below the value `cCol q` of
`thm:col`(2), so the exact value does not extend to those shifts. -/
''', r'''
theorem shiftshared_col {q : ℕ} (hq : 11 ≤ q) :
    (1 + (3 + univ.sup' univ_nonempty (wCol q)) / (q : ℝ) - 3 / (q : ℝ) ^ 2) / Real.sqrt 3 < cCol q := by
  sorry
''')
EXTRA_MODS['DGS'] = EXTRA_MODS.get('DGS', []) + ['Z3Net.S2Defs', 'Z3Net.SkelDefs', 'Z3Net.HLDefs']

_new('S10′', 'Z3NetF.S2_sep4_shift', 'DGS', 'prop:shift', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `thm:S2`** for every digital shift: the statement of `S2_sep4` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem S2_sep4_shift (p k : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hk : 1 ≤ k)
    (C : Fin 4 → Matrix (Fin (4 * k + 2)) (Fin (4 * k + 2)) (ZMod p)) (hC : IsS2skel 4 p k {1} C)
    (τ : Fin 4 → Fin (4 * k + 2) → ZMod p) (v w : Fin (4 * k + 2) → ZMod p) (hvw : v ≠ w) :
    (rhoT p - 4) ^ 2 * p ^ (2 * (3 * k + 1)) ≤
      torusDist2 (p ^ (4 * k + 2)) (Z3NetF.digPointShift p (4 * k + 2) C τ v) (Z3NetF.digPointShift p (4 * k + 2) C τ w) := by
  sorry
''')

_new('S10′', 'Z3NetF.S2_sep4_shift_real', 'DGS', 'prop:shift', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `thm:S2`** for every digital shift: the statement of `S2_sep4_real` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem S2_sep4_shift_real (p k : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hk : 1 ≤ k)
    (C : Fin 4 → Matrix (Fin (4 * k + 2)) (Fin (4 * k + 2)) (ZMod p)) (hC : IsS2skel 4 p k {1} C)
    (τ : Fin 4 → Fin (4 * k + 2) → ZMod p) (v w : Fin (4 * k + 2) → ZMod p) (hvw : v ≠ w) :
    ((rhoT p : ℝ) - 4) * (p : ℝ) ^ (-(1 / 2 : ℝ)) * ((p : ℝ) ^ (4 * k + 2)) ^ (-(1 / 4 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (4 * k + 2))
          ((Z3NetF.digPointShift p (4 * k + 2) C τ v c : ℤ) - (Z3NetF.digPointShift p (4 * k + 2) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (4 * k + 2)) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetF.S2_sep_shift', 'DGS', 'prop:shift', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `thm:S2`** for every digital shift: the statement of `S2_sep` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem S2_sep_shift (s p k : ℕ) [Fact p.Prime] (hs : 5 ≤ s) (hk : 1 ≤ k) (D1 : Finset ℕ)
    (hD1 : D1 ⊆ range (s - 2)) (hD1c : D1.card = (s - 2) / 2)
    (C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p))
    (hC : IsS2skel s p k D1 C) (τ : Fin s → Fin (s * k + (s - 2)) → ZMod p) (v w : Fin (s * k + (s - 2)) → ZMod p) (hvw : v ≠ w) :
    (Bp s p - Fs s) ^ 2 * p ^ (2 * ((s - 1) * k + s - 3)) ≤
      torusDist2 (p ^ (s * k + (s - 2))) (Z3NetF.digPointShift p (s * k + (s - 2)) C τ v)
        (Z3NetF.digPointShift p (s * k + (s - 2)) C τ w) := by
  sorry
''')

_new('S10′', 'Z3NetF.S2_sep_shift_real', 'DGS', 'prop:shift', 'Z3NetF', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `thm:S2`** for every digital shift: the statement of `S2_sep_real` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem S2_sep_shift_real (s p k : ℕ) [Fact p.Prime] (hs : 5 ≤ s) (hk : 1 ≤ k) (D1 : Finset ℕ)
    (hD1 : D1 ⊆ range (s - 2)) (hD1c : D1.card = (s - 2) / 2)
    (C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p))
    (hC : IsS2skel s p k D1 C) (τ : Fin s → Fin (s * k + (s - 2)) → ZMod p) (v w : Fin (s * k + (s - 2)) → ZMod p) (hvw : v ≠ w) :
    ((Bp s p : ℝ) - Fs s) * (p : ℝ) ^ (-(2 / (s : ℝ))) *
        ((p : ℝ) ^ (s * k + (s - 2))) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 2)))
          ((Z3NetF.digPointShift p (s * k + (s - 2)) C τ v c : ℤ) - (Z3NetF.digPointShift p (s * k + (s - 2)) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (s * k + (s - 2))) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetHL.GF_relax_shift', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `prop:Hk`** for every digital shift: the statement of `GF_relax` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem GF_relax_shift (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 3 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hσ : ∀ (E : Fin s → ℤ) (J : Fin s → ℕ) (c : Fin s), (∀ d, |E d| ≤ 2) →
      (∀ d, J d < min k (s - 1)) → |sig2 F2 E J c| < q)
    (LB : ℝ) (hLB : ∀ (E : Fin s → ℤ) (J : Fin s → ℕ), (∀ d, |E d| ≤ 2) → (∃ d, E d ≠ 0) →
      (∀ d, J d < min k (s - 1)) →
      LB ≤ min 2 (Real.sqrt (∑ c, ((bOpt2 q F2 E J c : ℤ) : ℝ) ^ 2) / (2 * q)))
    (τ : Fin s → Fin (s * k) → ZMod q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    LB * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (graphGen s k Φ) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (graphGen s k Φ) τ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetHL.GF_dom_shift', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `prop:Hk`** for every digital shift: the statement of `GF_dom` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem GF_dom_shift (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 + 2 ≤ q) (τ : Fin s → Fin (s * k) → ZMod q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    (q : ℤ) ^ (2 * (s * k - k - 1)) *
        min ((s : ℤ) * ((q : ℤ) - 2 * BdomL s (min k (s - 1)) F2 - 2) ^ 2)
          (8 * ((q : ℤ) - BdomL s (min k (s - 1)) F2 - 1) ^ 2) ≤
      4 * (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (graphGen s k Φ) τ x) (Z3NetF.digPointShift q (s * k) (graphGen s k Φ) τ y) : ℤ) := by
  sorry
''')

_new('S10′', 'Z3NetHL.GF_dom_shift_real', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `prop:Hk`** for every digital shift: the statement of `GF_dom_real` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem GF_dom_shift_real (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s) (hqodd : Odd q) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 < q) (τ : Fin s → Fin (s * k) → ZMod q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q))
        (Real.sqrt 2 * (1 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (graphGen s k Φ) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (graphGen s k Φ) τ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetHL.HL_relax_shift', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `prop:Hk`** for every digital shift: the statement of `HL_relax` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem HL_relax_shift (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hq7 : 7 ≤ q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d) (hk : 1 ≤ k)
    (τ : Fin s → Fin (s * k) → ZMod q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤
        (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y) : ℤ) ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y) : ℤ) := by
  sorry
''')

_new('S10′', 'Z3NetHL.HL_dom_shift', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `prop:Hk`** for every digital shift: the statement of `HL_dom` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem HL_dom_shift (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    (q : ℤ) ^ (2 * (s * k - k - 1)) *
        min ((s : ℤ) * ((q : ℤ) - 2 * Bdom s F2 - 2) ^ 2) (8 * ((q : ℤ) - Bdom s F2 - 1) ^ 2) ≤
      4 * (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x) (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y) : ℤ) := by
  sorry
''')

_new('S10′', 'Z3NetHL.HL_dom_shift_real', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `prop:Hk`** for every digital shift: the statement of `HL_dom_real` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem HL_dom_shift_real (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d)) (hhalf : ∀ x c d, 1 ≤ x → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → F2 x c c = 0) (hdom : ∀ c, (A2 s F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * Bdom s F2 + 2 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((Bdom s F2 : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((Bdom s F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetHL.HL_domL_shift_real', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `prop:Hk`** for every digital shift: the statement of `HL_domL_real` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem HL_domL_shift_real (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 2 ≤ s)
    (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hqodd : Odd q)
    (hF2 : ∀ x c d, x < min k (s - 1) → 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hhalf : ∀ x c d, 1 ≤ x → x < min k (s - 1) → Even (F2 x c d))
    (hdiag : ∀ x c, 1 ≤ x → x < min k (s - 1) → F2 x c c = 0)
    (hdom : ∀ c, (A2L s (min k (s - 1)) F2 c : ℤ) ≤ -F2 0 c c)
    (hqB : 2 * BdomL s (min k (s - 1)) F2 < q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q) (x y : Fin (s * k) → ZMod q)
    (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q))
        (Real.sqrt 2 * (1 - ((BdomL s (min k (s - 1)) F2 : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ x c : ℤ) - (Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) τ y c : ℤ)) : ℝ)
            / (q : ℝ) ^ (s * k)) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetHL.HL_main_shift_real', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `thm:HL`** for every digital shift: the statement of `HL_main_real` with the points of `P ⊕ τ` (`digPointShift`, `τ` any digital shift) in place of those of `P`. -/
''', r'''
theorem HL_main_shift_real (s q k : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q)
    (hqB : 2 * BH s + 2 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q) (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    min (Real.sqrt s * (1 / 2 - ((BH s : ℝ) + 1) / q)) (Real.sqrt 2 * (1 - ((BH s : ℝ) + 1) / q)) *
        ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k))
          ((Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ x c : ℤ) -
            (Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) := by
  sorry
''')

_new('S10′', 'Z3NetHL.HL_main_shift', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- **`prop:shift`, `thm:HL`** for every digital shift: `𝓗^s_{k,q} ⊕ τ` is a `(0,sk,s)`-net and satisfies the separation bound of `HL_main`. -/
''', r'''
theorem HL_main_shift (s q k : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q) (hqB : 2 * BH s + 2 ≤ q)
    (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q) :
    IsNet0 s q (s * k) (Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ) ∧
      ∀ x y : Fin (s * k) → ZMod q, x ≠ y →
        (q : ℤ) ^ (2 * (s * k - k - 1)) *
            min ((s : ℤ) * ((q : ℤ) - 2 * BH s - 2) ^ 2) (8 * ((q : ℤ) - BH s - 1) ^ 2) ≤
          4 * (torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ x)
            (Z3NetF.digPointShift q (s * k) (HLGen s q k uH vH (lamH s) gcoH (dgH s)) τ y) : ℤ) := by
  sorry
''')

_new('S10′', 'Z3NetHL.GFpoint_shift_zero', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- The graph-form points `GFpoint` of `prop:Hk` are the digital point set of `graphGen s k Φ` (the case `τ = 0`), so
`digPointShift q (s k) (graphGen s k Φ) τ` are their digital shifts. -/
''', r'''
theorem GFpoint_shift_zero (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q)) :
    GFpoint s q k Φ = Z3NetF.digPointShift q (s * k) (graphGen s k Φ) 0 := by
  sorry
''')

_new('S10′', 'Z3NetHL.HLpoint_shift_zero', 'DGS', 'prop:shift', 'Z3NetHL', ['open Matrix Finset'], r'''
/-- The points `HLpoint` of the split-frame nets (`prop:Hk`, `thm:HL`) are the digital point set of `HLGen` (the case
`τ = 0`), so `digPointShift q (s k) (HLGen …) τ` are their digital shifts. -/
''', r'''
theorem HLpoint_shift_zero (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) :
    HLpoint s q k u v lam gco dg = Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) 0 := by
  sorry
''')

PRF_EXTRA = {'Z3NetF.S2_sep4_shift': 'Proofs.S2_sep4_shift_core p k hp hk C hC τ v w hvw', 'Z3NetF.S2_sep4_shift_real': 'Proofs.S2_sep4_real_shift_core p k hp hk C hC τ v w hvw', 'Z3NetF.S2_sep_shift': 'Proofs.S2_sep_shift_core s p k hs hk D1 hD1 hD1c C hC τ v w hvw', 'Z3NetF.S2_sep_shift_real': 'Proofs.S2_sep_real_shift_core s p k hs hk D1 hD1 hD1c C hC τ v w hvw', 'Z3NetHL.GF_relax_shift': 'by apply Proofs.GF_relax_shift_core <;> assumption', 'Z3NetHL.GF_dom_shift': 'by apply Proofs.GF_dom_shift_core <;> assumption', 'Z3NetHL.GF_dom_shift_real': 'by apply Proofs.GF_dom_real_shift_core <;> assumption', 'Z3NetHL.HL_relax_shift': 'by apply Proofs.HL_relax_shift_core <;> assumption', 'Z3NetHL.HL_dom_shift': 'by apply Proofs.HL_dom_shift_core <;> assumption', 'Z3NetHL.HL_dom_shift_real': 'by apply Proofs.HL_dom_real_shift_core <;> assumption', 'Z3NetHL.HL_domL_shift_real': 'by apply Proofs.HL_domL_real_shift_core <;> assumption', 'Z3NetHL.HL_main_shift_real': 'by apply Proofs.HL_main_real_shift_core <;> assumption', 'Z3NetHL.HL_main_shift': 'Proofs.HL_main_shift_core s q k hs hq hqs hqB hk τ', 'Z3NetHL.GFpoint_shift_zero': 'Proofs.GFpoint_shift_zero s q k Φ', 'Z3NetHL.HLpoint_shift_zero': 'Proofs.HLpoint_shift_zero s q k u v lam gco dg'}
MAIN_IMPORTS = ['Z3Net.S2Shift', 'Z3Net.HLShift2']

_new('S10′', 'Z3NetA.A_sharp_shift', 'DGS', 'prop:shift', 'Z3NetA', _AO, r'''
/-- **`prop:shift`, the first-order sharpness in `thm:A`(2)** for every digital shift: the statement of `A_sharp` for `𝒫^{U*_s}_{k,q} ⊕ τ` (two distinct points at squared distance, in cell units, `< (1 - a*_s/q)² + ∑_{u ≠ i} (|F_0[u][i]| + 1)²/q²`, Euclidean and toroidal). -/
''', r'''
theorem A_sharp_shift {s : ℕ} [NeZero s] (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k) (i : Fin s)
    (hi : alphaS i = aStar s) (hq2 : 2 * aStar s < q)
    (hcol : ∑ u ∈ univ.erase i, |UstarF s 0 u i| < q) (τ : Fin s → Fin (s * k) → ZMod q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((digPointShift q (s * k) (AGen s q k) τ v c : ℝ) -
          digPointShift q (s * k) (AGen s q k) τ w c) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 +
          ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (s * k))
          ((digPointShift q (s * k) (AGen s q k) τ v c : ℤ) -
            (digPointShift q (s * k) (AGen s q k) τ w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 +
          ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  sorry
''')

_new('S10′', 'Z3NetA.A_sharp_shift_real', 'DGS', 'prop:shift', 'Z3NetA', _AO, r'''
/-- **`prop:shift`, the first-order sharpness in `thm:A`(2)** for every digital shift, real form: the statement of `A_sharp_real` for `𝒫^{U*_s}_{k,q} ⊕ τ`. -/
''', r'''
theorem A_sharp_shift_real {s : ℕ} [NeZero s] (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k)
    (hqa : 5 * aStar s + 4 ≤ q) (hqs : (s - 1) * aStar s < q) (τ : Fin s → Fin (s * k) → ZMod q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((digPointShift q (s * k) (AGen s q k) τ v c : ℤ) -
          (digPointShift q (s * k) (AGen s q k) τ w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ∧
      Real.sqrt (∑ c, (((digPointShift q (s * k) (AGen s q k) τ v c : ℝ) -
          digPointShift q (s * k) (AGen s q k) τ w c) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by
  sorry
''')

PRF_EXTRA.update({'Z3NetA.A_sharp_shift': 'Proofs.A_sharp_shift_core hs q k hq hk i hi hq2 hcol τ', 'Z3NetA.A_sharp_shift_real': 'Proofs.A_sharp_shift_real_core hs q k hq hk hqa hqs τ'})
MAIN_IMPORTS.append("Z3Net.ThmASharpShift")

# ---- S10′: `Z3NetDGS` (the DGS corollaries), extracted from `Z3Net/DGS.lean`

_new('S10′', 'Z3NetDGS.lemma37', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **`cor:dgs`, Step 1** (`[DGS2, Lemma 3.7]` with strict inequality): if any two distinct points of
`P` have toroidal `ℓ^∞`-distance at least `b^{-κ}` (in some coordinate), then `P` is `κ`-separated and
toroidally `κ`-separated in base `b`. -/
''', r'''
theorem lemma37 {d : ℕ} (b κ : ℕ) (hb : 2 ≤ b) (P : Finset (Fin d → ℝ))
    (h : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ∃ j, 1 / (b : ℝ) ^ κ ≤ torCoord (x j) (y j)) :
    IsKSep b κ P ∧ IsKSepTor b κ P := by
  sorry
''')

_new('S10′', 'Z3NetDGS.lemma37_strict', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **`cor:dgs`, Step 1, contrapositive form** (`[DGS2, Lemma 3.7]` sharpened to a strict inequality):
a finite `P ⊂ [0,1)^d` that is not `κ`-separated has `q_∞(P) < 1/(2 b^κ)`; one that is not toroidally
`κ`-separated has `q_{∞,T}(P) < 1/(2 b^κ)`. -/
''', r'''
theorem lemma37_strict {d : ℕ} (b κ : ℕ) (hb : 2 ≤ b) (P : Finset (Fin d → ℝ))
    (hP : ∀ x ∈ P, ∀ j, 0 ≤ x j ∧ x j < 1) :
    (¬ IsKSep b κ P → sepRad distInf P < 1 / (2 * (b : ℝ) ^ κ)) ∧
      (¬ IsKSepTor b κ P → sepRad torDistInf P < 1 / (2 * (b : ℝ) ^ κ)) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.isTMSNet_of_isNet0', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- Our `(0,m,s)`-nets (`Z3NetF.IsNet0`, integer points at scale `q^m`) are `(0,m,s)`-nets in base `q`
in the sense of `[DGS2, Def. 3.1]` (as point sets in `[0,1)^s`). -/
''', r'''
theorem isTMSNet_of_isNet0 {d m q : ℕ} [NeZero q] (hd : 1 ≤ d) (X : (Fin m → ZMod q) → Fin d → ℕ) (hX : ∀ v c, X v c < q ^ m)
    (h : Z3NetF.IsNet0 d q m X) : IsTMSNet q 0 m (ptSet q X) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.dgsNet_eq', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **[DGS2, Defs. 2.1, 2.2]**: for a prime (or any) base `b ≥ 2`, the digitally shifted digital net
`Q(F_1, …, F_d) ⊕ δ` of [DGS2] is the point set of `digPointShift b m F δ` (`def:dshift`). -/
''', r'''
theorem dgsNet_eq {d : ℕ} (b m : ℕ) [NeZero b] (hb : 2 ≤ b) (F : Fin d → Matrix (Fin m) (Fin m) (ZMod b))
    (δ : Fin d → Fin m → ZMod b) :
    dgsNet b m F δ = ptSet b (Z3NetF.digPointShift b m F δ) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.dgs_main', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **`cor:dgs`, Step 2** (the general statement): `(0,m,s)`-nets in base `q` on an infinite `I ⊆ ℕ` whose
toroidal minimum distance is at least `c q^{-m/s}` are `κ_m`-separated and toroidally `κ_m`-separated,
`κ_m = ⌈m/s + log_q(√s/c)⌉ ≤ m/s + log_q(√s/c) + 1` (for `m ≥ 1`; then `κ_m ≥ 1`), so they form a
well-separated and toroidally well-separated family on `I` in the sense of `[DGS2, Def. 3.8]`. -/
''', r'''
theorem dgs_main (s q : ℕ) (hs : 2 ≤ s) (hq : 2 ≤ q) (I : Set ℕ) (hI : I.Infinite)
    (P : ℕ → Finset (Fin s → ℝ)) (c : ℝ) (hc : 0 < c)
    (hnet : ∀ m ∈ I, IsTMSNet q 0 m (P m))
    (hδ : ∀ m ∈ I, ∀ x ∈ P m, ∀ y ∈ P m, x ≠ y → c * (q : ℝ) ^ (-((m : ℝ) / s)) ≤ torDist2 x y) :
    (∀ m ∈ I, IsKSep q (kappaM s q c m) (P m) ∧ IsKSepTor q (kappaM s q c m) (P m)) ∧
    (∀ m ∈ I, 1 ≤ m → 1 ≤ ⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉ ∧
      (kappaM s q c m : ℤ) = ⌈(m : ℝ) / s + Real.logb q (Real.sqrt s / c)⌉ ∧
      (kappaM s q c m : ℝ) ≤ (m : ℝ) / s + Real.logb q (Real.sqrt s / c) + 1) ∧
    WellSepFamily q 0 s I P ∧ WellSepFamilyTor q 0 s I P := by
  sorry
''')

_new('S10′', 'Z3NetDGS.dgs_P', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **`cor:dgs`(1)** for every digital shift: `𝒫_{k,q} ⊕ τ` (`thm:main`, every `q ≥ 4`, `k ≥ 2`) is a
`(0,3k,3)`-net in base `q` and `(k+1)`-separated and toroidally `(k+1)`-separated. -/
''', r'''
theorem dgs_P (q k : ℕ) [NeZero q] (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q) :
    IsTMSNet q 0 (3 * k) (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) ∧
      IsKSep q (k + 1) (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) ∧
      IsKSepTor q (k + 1) (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.dgs_A', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **`cor:dgs`(2)** for every digital shift: the nets of `thm:A`(2) (`q ≥ 5a*_s + 4`, every `k ≥ 1`) are
`(0,sk,s)`-nets in base `q` and `(k+1)`-separated and toroidally `(k+1)`-separated. -/
''', r'''
theorem dgs_A (s q k : ℕ) [NeZero s] [NeZero q] (hs : 3 ≤ s) (hq : Z3NetA.AdmBase s q)
    (hqa : 5 * Z3NetA.aStar s + 4 ≤ q) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q) :
    IsTMSNet q 0 (s * k) (ptSet q (Z3NetF.digPointShift q (s * k) (Z3NetA.AGen s q k) τ)) ∧
      IsKSep q (k + 1) (ptSet q (Z3NetF.digPointShift q (s * k) (Z3NetA.AGen s q k) τ)) ∧
      IsKSepTor q (k + 1) (ptSet q (Z3NetF.digPointShift q (s * k) (Z3NetA.AGen s q k) τ)) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.dgs_S1', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **`cor:dgs`(4)** for every digital shift: the nets `𝒮¹_{k,p,ρ}` of `thm:S1` (`s ≥ 3`, `p` prime, `ρ ≥ 2`,
`ρ^s < p`; `m = sk + s - 1`) are `(0,m,s)`-nets in base `p`, `(k+1)`-separated and toroidally `(k+1)`-separated
if `(ρ - 1)² ≥ s`, and `(k+2)`-separated and toroidally `(k+2)`-separated in any case. -/
''', r'''
theorem dgs_S1 (s p k ρ : ℕ) [NeZero p] (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p)
    (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p) :
    IsTMSNet p 0 (s * k + (s - 1))
        (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) ∧
      (s ≤ (ρ - 1) ^ 2 →
        IsKSep p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) ∧
        IsKSepTor p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ))) ∧
      IsKSep p (k + 2) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) ∧
      IsKSepTor p (k + 2) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.dgs_HL', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **`cor:dgs`(3)** for every digital shift: the nets `𝓗^s_{k,p}` of `thm:HL` (`s ≥ 2`, `p` prime,
`p ≥ max(2s, 2B_s + 4)`, every `k ≥ 1`) are `(0,sk,s)`-nets in base `p`, `(k+1)`-separated and toroidally
`(k+1)`-separated. -/
''', r'''
theorem dgs_HL (s p k : ℕ) [NeZero p] (hs : 2 ≤ s) (hp : p.Prime) (hps : 2 * s ≤ p)
    (hpB : 2 * Z3NetHL.BH s + 4 ≤ p) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod p) :
    IsTMSNet p 0 (s * k) (ptSet p (Z3NetF.digPointShift p (s * k)
        (Z3NetHL.HLGen s p k Z3NetHL.uH Z3NetHL.vH (Z3NetHL.lamH s) Z3NetHL.gcoH (Z3NetHL.dgH s)) τ)) ∧
      IsKSep p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k)
        (Z3NetHL.HLGen s p k Z3NetHL.uH Z3NetHL.vH (Z3NetHL.lamH s) Z3NetHL.gcoH (Z3NetHL.dgH s)) τ)) ∧
      IsKSepTor p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k)
        (Z3NetHL.HLGen s p k Z3NetHL.uH Z3NetHL.vH (Z3NetHL.lamH s) Z3NetHL.gcoH (Z3NetHL.dgH s)) τ)) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.dgs_allm', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **`cor:dgs`(5)** for every digital shift: for every prime `p ≥ 37` and every `m ≥ 3` there are generator
matrices (in the proof, those of the nets of `cor:allm`: `𝒞_p` for `m = 3`, `thm:main`, `thm:allm`, `thm:S1` at
`s = 3` otherwise) such that every digital shift of the net is a `(0,m,3)`-net in base `p` and
`(⌊m/3⌋ + 1)`-separated and toroidally `(⌊m/3⌋ + 1)`-separated. -/
''', r'''
theorem dgs_allm (p m : ℕ) [NeZero p] (hp : p.Prime) (hp37 : 37 ≤ p) (hm : 3 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : Fin 3 → Fin m → ZMod p,
      IsTMSNet p 0 m (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSep p (m / 3 + 1) (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSepTor p (m / 3 + 1) (ptSet p (Z3NetF.digPointShift p m C τ)) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.dgsfinite_sep', 'DGS', 'rem:dgsfinite', 'Z3NetDGS', _DO, r'''
/-- **`rem:dgsfinite`**: a `(0,m,s)`-net in base `q` (`[DGS2, Def. 3.1]`, `s ≥ 1`) on the grid `q^{-m} ℤ^s` is
`m`-separated and toroidally `m`-separated: the boxes of shape `(m, 0, …, 0)` hold one point each, so the
first coordinates are distinct multiples of `q^{-m}`, at toroidal distance `≥ q^{-m}`. -/
''', r'''
theorem dgsfinite_sep {d : ℕ} (q m : ℕ) (hd : 1 ≤ d) (hq : 2 ≤ q) (Q : Finset (Fin d → ℝ))
    (hgrid : ∀ x ∈ Q, ∀ j, ∃ n : ℕ, x j = (n : ℝ) / (q : ℝ) ^ m) (hQ : IsTMSNet q 0 m Q) :
    IsKSep q m Q ∧ IsKSepTor q m Q := by
  sorry
''')

_new('S10′', 'Z3NetDGS.frame3_net', 'DGS', 'rem:dgsfinite', 'Z3NetDGS', _DO, r'''
/-- The frame of the places `∞, 0, 1` (`lem:Ts`): every box minor is `±1`, so it is a digital
`(0,m,3)`-net over `ℤ/qℤ` for every `q ≥ 1` and every `m` (`rem:dgsfinite`). -/
''', r'''
theorem frame3_net (q m : ℕ) [NeZero q] :
    Z3NetF.IsNet0 3 q m (Z3NetF.digPoint q m (Z3NetF.frameRead m (0 : Fin 3) ![0, 0, 1])) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.dgs_family', 'DGS', 'rem:dgsfinite', 'Z3NetDGS', _DO, r'''
/-- **`rem:dgsfinite`**, the assembly in dimension three for every prime `p ≥ 37`: there are digital
`(0,m,3)`-nets over `𝔽_p` for every `m ∈ ℕ` (the frame of the places `∞, 0, 1` for `m ≤ 2`, the nets of
`dgs_allm` for `m ≥ 3`) such that for every choice of digital shifts `τ_m` the family `(P_m ⊕ τ_m)_{m ∈ ℕ}` is
well separated and toroidally well separated on all of `ℕ` in the sense of `[DGS2, Def. 3.8]`, with
`κ_m = m` for `m ≤ 2` and `κ_m = ⌊m/3⌋ + 1` for `m ≥ 3`. -/
''', r'''
theorem dgs_family (p : ℕ) [NeZero p] (hp : p.Prime) (hp37 : 37 ≤ p) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p,
      WellSepFamily p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      WellSepFamilyTor p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.linf_dist', 'DGS', 'prop:linf', 'Z3NetDGS', _DO, r'''
/-- **`prop:linf`**, the distance: any two distinct points of `𝒫_{k,q} ⊕ τ` (`q ≥ 4`, `k ≥ 2`, every
digital shift) have toroidal `ℓ^∞`-distance at least `(1 - 3/q) q^{-k}`. -/
''', r'''
theorem linf_dist (q k : ℕ) [NeZero q] (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (1 - 3 / (q : ℝ)) / (q : ℝ) ^ k ≤
      torDistInf (ptReal q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ) v)
        (ptReal q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ) w) := by
  sorry
''')

_new('S10′', 'Z3NetDGS.linf_mesh', 'DGS', 'prop:linf', 'Z3NetDGS', _DO, r'''
/-- **`prop:linf`**, the mesh ratio: the `ℓ^∞` mesh ratio of `𝒫_{k,q} ⊕ τ` in the sense of `[DGS2, §2.2]`,
non-toroidal (`ρ_∞`) and toroidal (`ρ_{∞,T}`), is at most `2q/(q - 3)`. -/
''', r'''
theorem linf_mesh (q k : ℕ) [NeZero q] (hq : 4 ≤ q) (hk : 2 ≤ k) (τ : Fin 3 → Fin (3 * k) → ZMod q) :
    meshRatio distInf (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) ≤ 2 * q / ((q : ℝ) - 3) ∧
      meshRatio torDistInf (ptSet q (Z3NetF.digPointShift q (3 * k) (PGenZ q k) τ)) ≤
        2 * q / ((q : ℝ) - 3) := by
  sorry
''')

# ---------------------------------------------------------------- stage S11′ (the s = 5 layer 𝒬*: `prop:half5`, `lem:R2`,
# `thm:D`). Statement review: the statement-review notes (research repository). Definitions `Z3Net/Q5Defs.lean`; restatements
# `Z3Net/Q5Main.lean`. The former Half entry (the layer M₅ of the removed `prop:half`/`tab:half`) is retired
# (`gen_v14_statements.RETIRE`, reason `_RM5`).
EXTRA_MODS['Split'] = EXTRA_MODS.get('Split', []) + ['Z3Net.Q5Defs']
EXTRA_SOLUTION.append('Z3Net.Q5Main')
_HO = ['open Matrix Finset']

_new('S11′', 'Z3NetHL.thmD', 'Split', 'thm:D', 'Z3NetHL', _HO, r'''
/-- **`thm:D`** (the least drift), doubled (`F2 = 2F₀`): every `F₀ ∈ (½ + ℤ)^{5×5}` (`F2` odd) with (B2) and (MIN)
(`DisjMinors`: every minor of `F₀` with disjoint row and column sets is nonzero), with entries of any size, has
`dr(F₀) ≥ 17/2`: some binding step `E` (`E ∈ {-1, 0, 1}⁵`, `∑ E` odd) has `2 dr(E) ≥ 17`. -/
''', r'''
theorem thmD (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (hB2 : B2D F2)
    (hmin : DisjMinors F2) : 17 ≤ drift2 F2 := by
  sorry
''')

_new('S11′', 'Z3NetHL.thmD_star', 'Split', 'thm:D', 'Z3NetHL', _HO, r'''
/-- **`thm:D`, attained**: the layer `F₀*` of `prop:half5` satisfies (Half), (B2) and (MIN), and
`dr(F₀*) = 17/2`. -/
''', r'''
theorem thmD_star : (∀ c d, Odd (F2star c d)) ∧ B2D F2star ∧ DisjMinors F2star ∧ drift2 F2star = 17 := by
  sorry
''')

_new('S11′', 'Z3NetHL.thmD_skew', 'Split', 'thm:D', 'Z3NetHL', _HO, r'''
/-- **`thm:D`, the skew layers** (the part of the printed proof by hand): if moreover the off-diagonal part of
`F₀` is skew-symmetric, `dr(F₀) ≥ 17/2`. -/
''', r'''
theorem thmD_skew (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (hB2 : B2D F2)
    (hmin : DisjMinors F2) (hskew : ∀ c d, c ≠ d → F2 c d + F2 d c = 0) : 17 ≤ drift2 F2 := by
  sorry
''')

_new('S11′', 'Z3NetHL.thmD_conj', 'Split', 'thm:D', 'Z3NetHL', _HO, r'''
/-- **The symmetry of `thm:D`** (the normalization in its proof): conjugation by a permutation matrix and a diagonal
sign matrix, `F₀ ↦ (ε_c ε_d F₀[σc][σd])`, keeps `dr`. -/
''', r'''
theorem thmD_conj (F2 : Fin 5 → Fin 5 → ℤ) (σ : Equiv.Perm (Fin 5)) (ε : Fin 5 → ℤ)
    (hε : ∀ c, ε c = 1 ∨ ε c = -1) : drift2 (fun c d => ε c * ε d * F2 (σ c) (σ d)) = drift2 F2 := by
  sorry
''')

_new('S11′', 'Z3NetHL.R2_sep', 'Split', 'lem:R2', 'Z3NetHL', _HO, r'''
/-- **`lem:R2`** (the two-digit relaxation): let `q` be odd (the paper: an odd prime), `s ≥ 3`, and let a graph form
over `ℤ/qℤ` with depths `(1, …, 1)` have first offset rows `F₀ = F2/2 ∈ (½ + ℤ)^{s×s}` (`F2` odd, `½ ≡ (q+1)/2`)
and second offset rows `D₁ ∈ ℤ^{s×s}` (deeper rows arbitrary; a digital net or not). If `q > |2β_c|` and
`q > |v_c|` (`β = F₀E`, `v = D₁E`) for all `E ∈ {-2, …, 2}^s` and all `c`, then `δ N^(1/s) ≥ LB₂(q)` for the
toroidal distance (`N = q^s`; `LB₂` with the options of `prop:Hk` for the first digit and `{v_c, v_c − q sgn v_c}`
for the second). -/
''', r'''
theorem R2_sep (s q : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (F2 D1 : Fin s → Fin s → ℤ) (hs : 3 ≤ s) (hqodd : Odd q)
    (hrow : RowDesign s q 1 Φ (fun _ => F2)) (hrow1 : Row1Design s q Φ D1) (hodd : ∀ c d, Odd (F2 c d))
    (hβ : ∀ (E : Fin s → ℤ) (c : Fin s), (∀ d, |E d| ≤ 2) → |dotR F2 E c| < q)
    (hv : ∀ (E : Fin s → ℤ) (c : Fin s), (∀ d, |E d| ≤ 2) → |dotR D1 E c| < q)
    (x y : Fin (s * 1) → ZMod q) (hxy : x ≠ y) :
    LB2R q F2 D1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * 1))
          ((GFpoint s q 1 Φ x c : ℤ) - (GFpoint s q 1 Φ y c : ℤ)) : ℝ) / (q : ℝ) ^ (s * 1)) ^ 2) := by
  sorry
''')

_new('S11′', 'Z3NetHL.qstar_net', 'Split', 'prop:half5', 'Z3NetHL', _HO, r'''
/-- **`prop:half5`(1)**: `𝒬*_p` is a digital `(0,5,5)`-net over `𝔽_p` for every prime `p ≥ 7`. -/
''', r'''
theorem qstar_net (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) : IsNet0 5 p (5 * 1) (Qstar p) := by
  sorry
''')

_new('S11′', 'Z3NetHL.qstar_sep', 'Split', 'prop:half5', 'Z3NetHL', _HO, r'''
/-- **`prop:half5`(2)**: for every prime `p ≥ 37`, `δ N^(1/5) > 1` for `𝒬*_p` (toroidal distance, `N = p⁵`). -/
''', r'''
theorem qstar_sep (p : ℕ) (hp : p.Prime) (h37 : 37 ≤ p) (x y : Fin (5 * 1) → ZMod p) (hxy : x ≠ y) :
    ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
      < Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((Qstar p x c : ℤ) - (Qstar p y c : ℤ)) : ℝ) /
          (p : ℝ) ^ (5 * 1)) ^ 2) := by
  sorry
''')

_new('S11′', 'Z3NetHL.qstar_bounds', 'Split', 'prop:half5', 'Z3NetHL', _HO, r'''
/-- **`prop:half5`(2), the bounds of the proof of the limit**: for every prime `p > 32`, any two distinct points of
`𝒬*_p` have toroidal distance `≥ (√5/2 − 12√5/p) N^(-1/5)` (`λ − √5(2A+1)/p` with `λ = √5/2`, `A = 11/2`), and some
two distinct points have Euclidean distance `≤ (√5/2 + 4√5/p) N^(-1/5)` (`prop:Hk`(3) with `C = 3/2`). -/
''', r'''
theorem qstar_bounds (p : ℕ) (hp : p.Prime) (h32 : 32 < p) :
    (∀ x y : Fin (5 * 1) → ZMod p, x ≠ y →
      (Real.sqrt 5 / 2 - 12 * Real.sqrt 5 / p) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
        ≤ Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((Qstar p x c : ℤ) - (Qstar p y c : ℤ)) : ℝ) /
            (p : ℝ) ^ (5 * 1)) ^ 2)) ∧
    ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧
      Real.sqrt (∑ c, (((Qstar p x c : ℝ) - (Qstar p y c : ℝ)) / (p : ℝ) ^ (5 * 1)) ^ 2)
        ≤ (Real.sqrt 5 / 2 + 4 * Real.sqrt 5 / p) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by
  sorry
''')

_new('S11′', 'Z3NetHL.qstar_limit', 'Split', 'prop:half5', 'Z3NetHL', _HO, r'''
/-- **`prop:half5`(2), the limit**: `δ N^(1/5) → √5/2` as the prime `p → ∞`: for every `ε > 0` there is `P` such that
for every prime `p ≥ P` all distinct points of `𝒬*_p` have toroidal distance `≥ (√5/2 − ε) N^(-1/5)` and some two
distinct points have Euclidean distance `≤ (√5/2 + ε) N^(-1/5)`. -/
''', r'''
theorem qstar_limit (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      (∀ x y : Fin (5 * 1) → ZMod p, x ≠ y →
        (Real.sqrt 5 / 2 - ε) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
          ≤ Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((Qstar p x c : ℤ) - (Qstar p y c : ℤ)) : ℝ) /
              (p : ℝ) ^ (5 * 1)) ^ 2)) ∧
      ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧
        Real.sqrt (∑ c, (((Qstar p x c : ℝ) - (Qstar p y c : ℝ)) / (p : ℝ) ^ (5 * 1)) ^ 2)
          ≤ (Real.sqrt 5 / 2 + ε) * ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ))) := by
  sorry
''')

_new('S11′', 'Z3NetHL.qstar_hk', 'Split', 'prop:half5', 'Z3NetHL', _HO, r'''
/-- **`prop:half5`(3)**: for every prime `p ≥ 53`, every graph form over `𝔽_p` with depths `(1, …, 1)` and first
offset rows `F₀*` (row `0` of every block is `F₀*`, `½ ≡ (p+1)/2`; deeper rows arbitrary) has `δ N^(1/5) > 1`
(toroidal). -/
''', r'''
theorem qstar_hk (p : ℕ) (hp : p.Prime) (h53 : 53 ≤ p)
    (Φ : Fin 5 → Fin 5 → Matrix (Fin (5 * 1 - 1)) (Fin 1) (ZMod p))
    (hrow : RowDesign 5 p 1 Φ (fun _ => F2star)) (x y : Fin (5 * 1) → ZMod p) (hxy : x ≠ y) :
    ((p : ℝ) ^ (5 * 1)) ^ (-(1 / (5 : ℝ)))
      < Real.sqrt (∑ c, ((cres (p ^ (5 * 1)) ((GFpoint 5 p 1 Φ x c : ℤ) - (GFpoint 5 p 1 Φ y c : ℤ)) : ℝ) /
          (p : ℝ) ^ (5 * 1)) ^ 2) := by
  sorry
''')

# ---------------------------------------------------------------- stage S12′ (the rank-one layer at m = 3: `prop:wnet`,
# `lem:wwrap`, `prop:wfamily`, `rem:wstar`, the `𝒲_p` sentence of `rem:shiftshared`). Statement review:
# the statement-review notes (research repository). Definitions `QUNetsM3/WDefs.lean`; restatements `QUNetsM3/WMain.lean`
# (generated by `scripts/gen_wmain.py` from the texts below).
EXTRA_MODS['Large'] = EXTRA_MODS.get('Large', []) + ['QUNetsM3.WDefs']
EXTRA_MODS['DGS'] = EXTRA_MODS.get('DGS', []) + ['QUNetsM3.WDefs']
EXTRA_SOLUTION.append('QUNetsM3.WMain')
_WO = ['open Matrix Filter Topology']

_new('S12′', 'QUNetsM3.W_layer', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet`, the layer** (the sentence after it, and `rem:wstar`): for odd `p` and every `r`, the net `genWr p r`
(`𝒲_p` for `r = ⌊p/48⌋`, `𝒲*_p` for `r = ⌊pε*⌋`) is the net of `prop:wfamily` with `u = (h − r, h − r, ρ)` and the
third rows `(0,1,2)`, `(1,0,1)`, `(0,1,0)`: `x` and `y` read `2ζ`, `z` reads `ζ = u·n` (as `2(h − r) ≡ −ρ`); and for
`r < h`, `u/p = (½ − ε, ½ − ε, 2ε)` with `ε = ρ/(2p)`. -/
''', r'''
theorem W_layer (p : ℕ) (hodd : p % 2 = 1) (r : ℕ) :
    genWr p r = genWfam p (uW p r) (thirdW p) ∧
      (r < hW p → tauOf p (uW p r) = tauEps ((2 * (r : ℝ) + 1) / (2 * p))) := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_net', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (1)**: for every prime `p ≥ 5`, `𝒲_p` is a `(0,3,3)`-net in base `p`. -/
''', r'''
theorem W_net (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : IsDigitalNet033 p (genW p) := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_cells', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (1), one point per cell**: for every prime `p`, every cell of side `p⁻¹` holds exactly one point of
`𝒲_p`. -/
''', r'''
theorem W_cells (p : ℕ) (hp : p.Prime) (b : Fin 3 → ℕ) (hb : ∀ c, b c < p) :
    ∃! x : ℕ, x < p ^ 3 ∧ ∀ c, digitalPt p (genW p) x c / p ^ 2 = b c := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_freeJitter', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (2) for any third rows** (here: any third digits). Let `p ≥ 53` be prime. Place one point in each cell
`n ∈ [0,p)³` at `p²n + p·g(n) + f(n)` (integer scale `p³`), with second digits `g(n) ∈ [0,p)³`,
`g_x(n) ≡ ρ(−n_x − n_y + 2n_z)`, `g_y(n) = g_x(n)`, `g_z(n) ≡ (h − r)(n_x + n_y) + ρn_z (mod p)` (`r = ⌊p/48⌋`,
`ρ = 2r + 1`, `h = (p − 1)/2`) and arbitrary third digits `f(n) ∈ [0,p)³`. Then for distinct cells `n ≠ n'` and every
torus translate `p³·t`, the squared length of the difference is at least `(p² c_W(p))²`,
`c_W(p) = √(281/256 − 345/(128p)) − √3/p`. -/
''', r'''
theorem W_freeJitter (p : ℕ) (hp : p.Prime) (hp53 : 53 ≤ p) (g f : (Fin 3 → ℕ) → Fin 3 → ℕ)
    (hg : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, g n c < p)
    (hgx : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ((g n 0 : ℕ) : ZMod p) =
      rhoZ p (rW p) * (-(n 0 : ZMod p) - (n 1 : ZMod p) + 2 * (n 2 : ZMod p)))
    (hgy : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → g n 1 = g n 0)
    (hgz : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ((g n 2 : ℕ) : ZMod p) =
      ((hW p : ZMod p) - rW p) * ((n 0 : ZMod p) + (n 1 : ZMod p)) + rhoZ p (rW p) * (n 2 : ZMod p))
    (hf : ∀ n : Fin 3 → ℕ, (∀ c, n c < p) → ∀ c, f n c < p)
    (n n' : Fin 3 → ℕ) (hn : ∀ c, n c < p) (hn' : ∀ c, n' c < p) (hne : n ≠ n')
    (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * cW p) ^ 2 ≤
      ∑ c : Fin 3, ((((p : ℤ) ^ 2 * ((n' c : ℤ) - n c) + p * ((g n' c : ℤ) - g n c)
        + ((f n' c : ℤ) - f n c) + (p : ℤ) ^ 3 * t c : ℤ)) : ℝ) ^ 2 := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_sep', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (2), integer scale**: for every prime `p ≥ 53`, every pair of distinct points of `𝒲_p` and every torus
translate `p³·t`, the squared length of the difference is at least `(p² c_W(p))²`. -/
''', r'''
theorem W_sep (p : ℕ) (hp : p.Prime) (hp53 : 53 ≤ p) (x x' : ℕ) (hx : x < p ^ 3)
    (hx' : x' < p ^ 3) (hne : x ≠ x') (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * cW p) ^ 2 ≤ (sepSqG p (genW p) x x' t : ℝ) := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_sep_real', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (2), normalized**: for every prime `p ≥ 53`: `0 < c_W(p)` and, for every pair of distinct points and
every torus translate, the distance in the unit torus times `N^{1/3}` (`N = p³`) is at least
`c_W(p) = √(281/256 − 345/(128p)) − √3/p`. -/
''', r'''
theorem W_sep_real (p : ℕ) (hp : p.Prime) (hp53 : 53 ≤ p) :
    0 < cW p ∧ ∀ x x' : ℕ, x < p ^ 3 → x' < p ^ 3 → x ≠ x' → ∀ t : Fin 3 → ℤ,
      cW p ≤ Real.sqrt (sepSqG p (genW p) x x' t : ℝ) / (p : ℝ) ^ 3 *
        ((p : ℝ) ^ 3) ^ ((1 : ℝ) / 3) := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_bound', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (2), the bound**: `c_W(p)` increases with `p` (`p ≥ 53`); it exceeds `1` for `p ≥ 67` and `√66/8` for
`p ≥ 97`; the values of the proof: `1.0024 < c_W(67) < 1.0025`, `c_W(61) < 1`, `1.0164 < c_W(97) < 1.0165`,
`c_W(89) < √66/8`. -/
''', r'''
theorem W_bound :
    (∀ p p' : ℕ, 53 ≤ p → p ≤ p' → cW p ≤ cW p') ∧
    (∀ p : ℕ, 67 ≤ p → 1 < cW p) ∧ (∀ p : ℕ, 97 ≤ p → Real.sqrt 66 / 8 < cW p) ∧
    1.0024 < cW 67 ∧ cW 67 < 1.0025 ∧ cW 61 < 1 ∧ 1.0164 < cW 97 ∧ cW 97 < 1.0165 ∧
    cW 89 < Real.sqrt 66 / 8 := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_pair', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (3), the pair**: for every prime `p ≥ 53` the points of the cells `(1,0,0)` (index `p²`) and
`(2,0,p−1)` (index `2p² + p − 1`) have squared toroidal distance `d_*²` at integer scale `p³`,
`d_*² = (p² − (6r+2)p − 2)² + (6r+3)²p² + (h+3r+2)²p²`: it is attained at the translate `t = (0,0,−1)` and no
translate gives less. -/
''', r'''
theorem W_pair (p : ℕ) (hp : p.Prime) (hp53 : 53 ≤ p) :
    sepSqG p (genW p) (p ^ 2) (2 * p ^ 2 + p - 1) ![0, 0, -1] = dstarSqW p ∧
    ∀ t : Fin 3 → ℤ, dstarSqW p ≤ sepSqG p (genW p) (p ^ 2) (2 * p ^ 2 + p - 1) t := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_pair_lt', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (3), the bound**: for every prime `p ≥ 53`, `d_*/p² < √281/16 + 5/(2p)`. -/
''', r'''
theorem W_pair_lt (p : ℕ) (hp : p.Prime) (hp53 : 53 ≤ p) :
    Real.sqrt (dstarSqW p : ℝ) / (p : ℝ) ^ 2 < Real.sqrt 281 / 16 + 5 / (2 * p) := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_delta', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (2)–(3) for `δ N^{1/3}`**: for every prime `p ≥ 53` the normalized toroidal minimum distance
`δ N^{1/3}` of `𝒲_p` (`deltaW p`) satisfies `c_W(p) ≤ δ N^{1/3} ≤ d_*/p²`. -/
''', r'''
theorem W_delta (p : ℕ) (hp : p.Prime) (hp53 : 53 ≤ p) :
    cW p ≤ deltaW p ∧ deltaW p ≤ Real.sqrt (dstarSqW p : ℝ) / (p : ℝ) ^ 2 := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_limit', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (3), the limit**: `δ N^{1/3} → √281/16 = 1.0476…` as the prime `p → ∞`. -/
''', r'''
theorem W_limit : ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
    |deltaW p - Real.sqrt 281 / 16| < ε := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_exact', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (4), the exact minimum distances** at the primes `17 ≤ p ≤ 89`: the table `wExactTab` has an entry
`(p, d)` for each of them, and for each entry every pair of distinct points of `𝒲_p` has squared toroidal distance
`≥ d` at integer scale `p³`, some pair attains `d`, and `δ N^{1/3} = √d/p²`. -/
''', r'''
theorem W_exact :
    (∀ p : ℕ, p.Prime → 17 ≤ p → p ≤ 89 → ∃ d, (p, d) ∈ wExactTab) ∧
    ∀ q ∈ wExactTab, (∀ x x' : ℕ, ∀ t : Fin 3 → ℤ, x < q.1 ^ 3 → x' < q.1 ^ 3 → x ≠ x' →
      (q.2 : ℤ) ≤ sepSqG q.1 (genW q.1) x x' t) ∧
      (∃ x x' : ℕ, ∃ t : Fin 3 → ℤ, x < q.1 ^ 3 ∧ x' < q.1 ^ 3 ∧ x ≠ x' ∧ sepSqG q.1 (genW q.1) x x' t = q.2) ∧
      deltaW q.1 = Real.sqrt q.2 / (q.1 : ℝ) ^ 2 := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_four', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (4)**: `δ N^{1/3} > 1` for every prime `p ≥ 17`, and `δ N^{1/3} > √66/8` for every prime `p ≥ 53`. -/
''', r'''
theorem W_four : (∀ p : ℕ, p.Prime → 17 ≤ p → 1 < deltaW p) ∧
    (∀ p : ℕ, p.Prime → 53 ≤ p → Real.sqrt 66 / 8 < deltaW p) := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_least', 'Large', 'prop:wnet', 'QUNetsM3', _WO, r'''
/-- **`prop:wnet` (4), the values of the proof**: among the primes `17 ≤ p ≤ 61` the least `δ N^{1/3}` is at `p = 47`,
`1.0009 < δ N^{1/3} < 1.0010`; among the primes `53 ≤ p ≤ 89` it is at `p = 89`, `1.0257 < δ N^{1/3} < 1.0258`. -/
''', r'''
theorem W_least : (∀ p : ℕ, p.Prime → 17 ≤ p → p ≤ 61 → deltaW 47 ≤ deltaW p) ∧
    1.0009 < deltaW 47 ∧ deltaW 47 < 1.0010 ∧
    (∀ p : ℕ, p.Prime → 53 ≤ p → p ≤ 89 → deltaW 89 ≤ deltaW p) ∧
    1.0257 < deltaW 89 ∧ deltaW 89 < 1.0258 := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_wrap', 'Large', 'lem:wwrap', 'QUNetsM3', _WO, r'''
/-- **`lem:wwrap`** (wraps of a halved digit): let `p ≥ 5` be prime, `u ∈ 𝔽_p³` (Lean: any `u`; the paper `u ≠ 0`),
`ζ(n) = u·n mod p`, and for `E ∈ ℤ³` and `n' = n + E` let `Δζ = ζ(n') − ζ(n)`, `κ = [2ζ(n') ≥ p] − [2ζ(n) ≥ p]`,
`σ = u·E mod p`. As `n` runs over `𝔽_p³`, the pairs `(Δζ, κ)` that occur are exactly those of `WrapAllowed`: `(0, 0)`
if `σ = 0`; if `σ ≠ 0`, for each `Δζ ∈ {σ, σ − p}` the pair `(Δζ, sgn Δζ)`, and also `(Δζ, 0)` if `|Δζ| ≤ h`. -/
''', r'''
theorem W_wrap (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) (E : Fin 3 → ℤ) (d k : ℤ) :
    (∃ n : Fin 3 → ZMod p, dZetaW p u n E = d ∧ kappaW p u n E = k) ↔ WrapAllowed p (sigmaW p u E) d k := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wfam_star', 'Large', 'prop:wfamily', 'QUNetsM3', _WO, r'''
/-- **The balance before `prop:wfamily`**: `q_a(ε*) = q_b(ε*) = μ*²` (`ε* = (13 − 2√31)/90`, `μ*² = (72 − 8√31)/25`),
`0.02071 < ε* < 0.02072`, `1.0480 < μ* < 1.0481`, and `2K = 9 − 162ε* = |q_a'(ε*)|` for `K = (9√31 − 36)/5`. -/
''', r'''
theorem Wfam_star : qaW epsStar = muStarSq ∧ qbW epsStar = muStarSq ∧ 0.02071 < epsStar ∧ epsStar < 0.02072 ∧
    1.0480 < muStar ∧ muStar < 1.0481 ∧ 2 * KW = 9 - 162 * epsStar := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wfam_one', 'Large', 'prop:wfamily', 'QUNetsM3', _WO, r'''
/-- **`prop:wfamily` (1)**: for every prime `p ≥ 5`, every `u ∈ 𝔽_p³` (Lean: also `u = 0`; no net property needed) and
any third rows `T`, the value without the third digits is `F_p(u) = F(u/p)`, and the net `genWfam p u T` has
`|δ N^{1/3} − √F_p(u)| < √3/p`. -/
''', r'''
theorem Wfam_one (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) (T : Fin 3 → Fin 3 → ZMod p) :
    FpW p u = Ffam (tauOf p u) ∧ |deltaG p (genWfam p u T) - Real.sqrt (FpW p u)| < Real.sqrt 3 / p := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wfam_two', 'Large', 'prop:wfamily', 'QUNetsM3', _WO, r'''
/-- **`prop:wfamily` (2)**: for `0 < ε ≤ 3/100`, `F(½ − ε, ½ − ε, 2ε) = min(q_a(ε), q_b(ε))`. -/
''', r'''
theorem Wfam_two (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 3 / 100) :
    Ffam (tauEps ε) = min (qaW ε) (qbW ε) := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wfam_three_tau', 'Large', 'prop:wfamily', 'QUNetsM3', _WO, r'''
/-- **`prop:wfamily` (3), on the torus**: `F(τ) ≤ μ*²` for every `τ ∈ ℝ³`, with equality if and only if
`τ ≡ τ* = (½ − ε*, ½ − ε*, 2ε*) (mod ℤ³)`. -/
''', r'''
theorem Wfam_three_tau (τ : Fin 3 → ℝ) :
    Ffam τ ≤ muStarSq ∧ (Ffam τ = muStarSq ↔ ∃ k : Fin 3 → ℤ, τ = fun c => tauStar c + k c) := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wfam_three', 'Large', 'prop:wfamily', 'QUNetsM3', _WO, r'''
/-- **`prop:wfamily` (3), the nets**: for every prime `p ≥ 5`, every `u` and any third rows `T`, `F_p(u) < μ*²` (as `τ*`
has irrational coordinates) and `δ N^{1/3} < μ* + √3/p`. -/
''', r'''
theorem Wfam_three (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) (T : Fin 3 → Fin 3 → ZMod p) :
    FpW p u < muStarSq ∧ deltaG p (genWfam p u T) < muStar + Real.sqrt 3 / p := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wstar_net', 'Large', 'rem:wstar', 'QUNetsM3', _WO, r'''
/-- **`rem:wstar`, `t = 0`**: `𝒲*_p` (`genWr` at `r = ⌊pε*⌋`) is a `(0,3,3)`-net for every prime `p ≥ 5`. -/
''', r'''
theorem Wstar_net (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : IsDigitalNet033 p (genWstar p) := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wstar_rho', 'Large', 'rem:wstar', 'QUNetsM3', _WO, r'''
/-- **`rem:wstar`, `ρ` and `ε_p`**: for every `p ≥ 1`, `ρ = 2⌊pε*⌋ + 1` is the odd integer nearest to `2pε*`
(`|ρ − 2pε*| < 1`, and no odd integer is nearer), and `|ε_p − ε*| < 1/(2p)` for `ε_p = ρ/(2p)`. -/
''', r'''
theorem Wstar_rho (p : ℕ) (hp : 0 < p) :
    |(2 * (rStar p : ℝ) + 1) - 2 * p * epsStar| < 1 ∧
    (∀ o : ℤ, Odd o → |(2 * (rStar p : ℝ) + 1) - 2 * p * epsStar| ≤ |(o : ℝ) - 2 * p * epsStar|) ∧
    |epsP p - epsStar| < 1 / (2 * p) := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wstar_eps', 'Large', 'rem:wstar', 'QUNetsM3', _WO, r'''
/-- **`rem:wstar`, `ε_p ≤ 3/100`** for every prime `p ≥ 17` (and `ε_p > 0`). -/
''', r'''
theorem Wstar_eps (p : ℕ) (hp : p.Prime) (h17 : 17 ≤ p) : 0 < epsP p ∧ epsP p ≤ 3 / 100 := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wstar_bound', 'Large', 'rem:wstar', 'QUNetsM3', _WO, r'''
/-- **`rem:wstar`, the bound**: for every prime `p ≥ 17`, `δ N^{1/3}(𝒲*_p) > √(μ*² − K/p) − √3/p`,
`K = (9√31 − 36)/5`. -/
''', r'''
theorem Wstar_bound (p : ℕ) (hp : p.Prime) (h17 : 17 ≤ p) :
    Real.sqrt (muStarSq - KW / p) - Real.sqrt 3 / p < deltaG p (genWstar p) := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wstar_limit', 'Large', 'rem:wstar', 'QUNetsM3', _WO, r'''
/-- **`rem:wstar`, the limit**: `δ N^{1/3}(𝒲*_p) → μ*` as the prime `p → ∞` (the optimum of the family is attained in
the limit). -/
''', r'''
theorem Wstar_limit : ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
    |deltaG p (genWstar p) - muStar| < ε := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wstar_thresholds', 'Large', 'rem:wstar', 'QUNetsM3', _WO, r'''
/-- **`rem:wstar`, the thresholds**: the bound `f(p) = √(μ*² − K/p) − √3/p` increases with `p` (`p ≥ 17`); it exceeds
`1` for `p ≥ 67`, `√66/8` for `p ≥ 97`, `√281/16` for `p ≥ 9791`, and the upper bound `√281/16 + 5/(2p)` of
`prop:wnet` (3) for `p ≥ 17737`. -/
''', r'''
theorem Wstar_thresholds :
    (∀ p p' : ℕ, 17 ≤ p → p ≤ p' → fStar p ≤ fStar p') ∧
    (∀ p : ℕ, 67 ≤ p → 1 < fStar p) ∧ (∀ p : ℕ, 97 ≤ p → Real.sqrt 66 / 8 < fStar p) ∧
    (∀ p : ℕ, 9791 ≤ p → Real.sqrt 281 / 16 < fStar p) ∧
    (∀ p : ℕ, 17737 ≤ p → Real.sqrt 281 / 16 + 5 / (2 * p) < fStar p) := by
  sorry
''')

_new('S12′', 'QUNetsM3.Wstar_ahead', 'Large', 'rem:wstar', 'QUNetsM3', _WO, r'''
/-- **`rem:wstar`, `𝒲*_p` provably ahead of `𝒲_p`**: for every prime `p ≥ 17737`, `δ N^{1/3}(𝒲_p) < δ N^{1/3}(𝒲*_p)`. -/
''', r'''
theorem Wstar_ahead (p : ℕ) (hp : p.Prime) (h : 17737 ≤ p) : deltaW p < deltaG p (genWstar p) := by
  sorry
''')

_new('S12′', 'QUNetsM3.W_shift', 'DGS', 'rem:shiftshared', 'QUNetsM3', _WO, r'''
/-- **`rem:shiftshared`, the net `𝒲_p`**: let `p ≥ 53` be prime and shift `𝒲_p` digit by digit by `τ` (`def:dshift`;
any first and third shift digits). If the second shift digits are `τ_{x,2} = τ_{y,2} = a`, `τ_{z,2} = b` with
`a ≡ 2b` or `a ≡ 2b + 1 (mod p)`, the bound of `prop:wnet` (2) holds for the shifted net: every pair of distinct points
and every torus translate have squared distance `≥ (p² c_W(p))²` at integer scale `p³`. -/
''', r'''
theorem W_shift (p : ℕ) (hp : p.Prime) (hp53 : 53 ≤ p) (τ : Fin 3 → Fin 3 → ZMod p) (hxy : τ 0 1 = τ 1 1)
    (hab : τ 0 1 = 2 * τ 2 1 ∨ τ 0 1 = 2 * τ 2 1 + 1) (x x' : ℕ) (hx : x < p ^ 3)
    (hx' : x' < p ^ 3) (hne : x ≠ x') (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * cW p) ^ 2 ≤ (sepSqGS p (genW p) τ x x' t : ℝ) := by
  sorry
''')

# ---------------------------------------------------------------- stage S13′ (`rem:projlines`, `rem:accounting`, the link
# of the S12′ shifted point set `digitalPtS` to `def:dshift`). Statement review: the statement-review notes (research repository). Restatements
# `Z3Net/S13Main.lean` (generated by `scripts/gen_s13main.py` from the texts below).
EXTRA_SOLUTION.append('Z3Net.S13Main')
_LO = ['open Matrix']

_new('S13′', 'QUNetsM3.digitalPtS_eq_dshiftPt', 'DGS', 'rem:shiftshared', 'QUNetsM3', _LO, r'''
/-- **`def:dshift` for the shifted point set of `rem:shiftshared`**: the point set `digitalPtS p C τ` (the digital point
set `digitalPt p C` of `prop:twocoset` and `sec:wnet`, each coordinate's digits `C_c · digits(x)` shifted by `τ_c`) is the
digit-by-digit shift `Z3NetF.dshiftPt p 3 τ` of `def:dshift` applied to `digitalPt p C`, for every `p ≥ 1`. -/
''', r'''
theorem digitalPtS_eq_dshiftPt (p : ℕ) [NeZero p] (C : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p))
    (τ : Fin 3 → Fin 3 → ZMod p) (x : ℕ) :
    digitalPtS p C τ x = Z3NetF.dshiftPt p 3 τ (digitalPt p C x) := by
  sorry
''')

# ---------------------------------------------------------------- stage S13′ (2/4): `rem:projlines` (the middle digits of
# two coordinates of the frame, of `𝒫^F_{k,q}` and of `𝒫_{k,q}`; the remedy that rescales one row). Proof modules
# `Z3Net/ProjLines.lean`, `Z3Net/ProjSep.lean`, `Z3Net/ProjPSep.lean`; definitions `Z3Net/ProjDefs.lean`.
EXTRA_MODS['Frames'] = EXTRA_MODS.get('Frames', []) + ['Z3Net.ProjDefs']
_PL = ('Frames', 'rem:projlines')
_PLF = ['open Matrix Finset']
_PLZ = ['open Matrix']

_new('S13′', 'Z3NetF.projlines_frame', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines`, the frame** (the reversal symmetry of the two-dimensional Hammersley set, transported to every
pair of places). Let `m = 2r + 1`, let the differences of the finite places be units (`PlacesOK`), and let `a ≠ b`.
Digit `r` of the reading `b` of the frame of `s` places (`lem:Ts`) equals `g` times digit `r` of the reading `a` plus a
linear combination of the more significant digits `0, …, r-1` of both readings (`RowRel`) if and only if
`g = projSign inf a b r`, i.e. `+1` if one of the two places is `∞` and `(-1)^r` if both are finite. So the relation
exists and its coefficient is unique. Any `m = 2r + 1`; the paper's `m = sk` is the case used below. -/
''', r'''
theorem projlines_frame {R : Type*} [CommRing R] {s m r : ℕ} (inf : Fin s) (x : Fin s → R)
    (hx : PlacesOK inf x) (hm : m = 2 * r + 1) {a b : Fin s} (hab : a ≠ b) (g : R) :
    RowRel (frameRead m inf x a) (frameRead m inf x b) r g ↔ g = (projSign inf a b r : R) := by
  sorry
''')

_new('S13′', 'Z3NetF.projlines', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines` for `𝒫^F_k`** (`def:Ns`, over the ring `R` of the places and of the residual solution). Let
`m = s k` be odd with `(s, k) ≠ (3, 1)` and `r* = (m - 1)/2`. For any two coordinates `a ≠ b`, digit `r*` of
coordinate `b` equals `g` times digit `r*` of coordinate `a` plus a linear combination of the more significant digits of
both coordinates iff `g = projSign inf a b r*`: `+1` if one of the two places is `∞`, `(-1)^{r*}` otherwise. (The
lower-triangular scrambles of `cor:tsk` keep the frame's relation, as `r* ≥ k + 1`.) Any `β`; no hypothesis on the
diagonal of the design. -/
''', r'''
theorem projlines {R : Type*} [CommRing R] {s k : ℕ} (inf : Fin s) (x : Fin s → R) (hx : PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (Ur β : Fin s → ℕ → ℕ → R)
    (hres : Residual inf x F lam Ur) (hodd : Odd (s * k)) (hsk : (s, k) ≠ (3, 1)) {a b : Fin s}
    (hab : a ≠ b) (g : R) :
    RowRel (PGen k inf x F lam Ur β a) (PGen k inf x F lam Ur β b) ((s * k - 1) / 2) g ↔
      g = (projSign inf a b ((s * k - 1) / 2) : R) := by
  sorry
''')

_new('S13′', 'Z3NetF.projlines_zmod', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines` for the net `𝒫^F_{k,q}` over `ℤ/qℤ`** (the reduction of `𝒫^F_k` along any ring homomorphism
`ψ : R → ℤ/qℤ`, as in `tsk_net`): with `m = s k` odd, `(s, k) ≠ (3, 1)`, `r* = (m-1)/2` and `a ≠ b`, the relation
between digit `r*` of the coordinates `b` and `a` holds over `ℤ/qℤ` exactly for the coefficient `projSign inf a b r*`
(`+1` if one place is `∞`, `(-1)^{r*}` otherwise). -/
''', r'''
theorem projlines_zmod {R : Type*} [CommRing R] {s k q : ℕ} (ψ : R →+* ZMod q) (inf : Fin s) (x : Fin s → R)
    (hx : PlacesOK inf x) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R) (Ur β : Fin s → ℕ → ℕ → R)
    (hres : Residual inf x F lam Ur) (hodd : Odd (s * k)) (hsk : (s, k) ≠ (3, 1)) {a b : Fin s}
    (hab : a ≠ b) (g : ZMod q) :
    RowRel ((PGen k inf x F lam Ur β a).map ψ) ((PGen k inf x F lam Ur β b).map ψ) ((s * k - 1) / 2) g ↔
      g = (projSign inf a b ((s * k - 1) / 2) : ZMod q) := by
  sorry
''')

_new('S13′', 'Z3NetF.projlines_box', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines`, the general lemma behind "up to a sign"**: for any digital point set over a commutative ring
with `m = 2r + 1` and two coordinates `a ≠ b`, if the box with depths `r + 1` at `a`, `r` at `b` (`pairDepth a b r`) and
the box with depths `r` at `a`, `r + 1` at `b` have unit determinants, then digit `r` of coordinate `b` is `g` times
digit `r` of coordinate `a` plus more significant digits of both, for a unique `g`, and `g` is a unit. (For a
`(0,m,s)`-net over `ℤ/qℤ` both boxes are units by `lem:nie`; what is specific to the frame nets is `g = ±1`.) -/
''', r'''
theorem projlines_box {R : Type*} [CommRing R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R) {a b : Fin s}
    (hab : a ≠ b) {r : ℕ} (hm : m = 2 * r + 1) (h1 : IsUnit (boxMatrix C (pairDepth a b r)).det)
    (h2 : IsUnit (boxMatrix C (pairDepth b a r)).det) :
    ∃ g, IsUnit g ∧ RowRel (C a) (C b) r g ∧ ∀ g', RowRel (C a) (C b) r g' → g' = g := by
  sorry
''')

_new('S13′', 'Z3NetF.rowScale_box', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines`, the remedy and `t`** (`eq:scr` for the diagonal scramble that rescales row `r`): rescaling row
`r` of every generator matrix `C_c` by `ρ_c` (`rowScale`) multiplies the box minor with depths `d` (`∑ d = m`) by the
product of the `ρ_c` over the coordinates with `r < d_c`. -/
''', r'''
theorem rowScale_box {R : Type*} [CommRing R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R) (r : ℕ)
    (ρ : Fin s → R) (d : Fin s → ℕ) (hd : ∑ c, d c = m) :
    (boxMatrix (rowScale C r ρ) d).det = (∏ c, if r < d c then ρ c else 1) * (boxMatrix C d).det := by
  sorry
''')

_new('S13′', 'Z3NetF.rowScale_net', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines`, the remedy keeps `t = 0`**: for units `ρ_c` of `ℤ/qℤ`, the digital point set with row `r` of
every generator matrix rescaled by `ρ_c` is a `(0,m,s)`-net iff the original one is (any generator matrices, any `r`). -/
''', r'''
theorem rowScale_net {s q m : ℕ} [NeZero q] (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) (r : ℕ)
    (ρ : Fin s → ZMod q) (hρ : ∀ c, IsUnit (ρ c)) :
    IsNet0 s q m (digPoint q m (rowScale C r ρ)) ↔ IsNet0 s q m (digPoint q m C) := by
  sorry
''')

_new('S13′', 'Z3NetF.tsk_net_rowScale', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines`, the remedy on `𝒫^F_{k,q}`** (with `cor:tsk`): rescaling any row `r` of the generator matrices of
`𝒫^F_{k,q}` by units `ρ_c` of `ℤ/qℤ` gives a digital `(0,sk,s)`-net. -/
''', r'''
theorem tsk_net_rowScale {R : Type*} [CommRing R] {s q : ℕ} [NeZero q] (ψ : R →+* ZMod q) (k : ℕ)
    (inf : Fin s) (x : Fin s → R) (hx : PlacesOK inf x) (F : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur β : Fin s → ℕ → ℕ → R) (hres : Residual inf x F lam Ur) (r : ℕ) (ρ : Fin s → ZMod q)
    (hρ : ∀ c, IsUnit (ρ c)) :
    IsNet0 s q (s * k) (digPoint q (s * k) (rowScale (fun c => (PGen k inf x F lam Ur β c).map ψ) r ρ)) := by
  sorry
''')

_new('S13′', 'Z3NetF.rowScale_rowRel', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines`, the remedy's effect on the relation**: if digit `r` of `C_b` is `g` times digit `r` of `C_a` plus
more significant digits, then after rescaling row `r` by `ρ` (with `ρ_a` a unit) the coefficient is `ρ_b g ρ_a⁻¹`. -/
''', r'''
theorem rowScale_rowRel {R : Type*} [CommRing R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R) (r : ℕ)
    (ρ : Fin s → R) {a b : Fin s} {g : R} (ha : IsUnit (ρ a)) (h : RowRel (C a) (C b) r g) :
    RowRel (rowScale C r ρ a) (rowScale C r ρ b) r (ρ b * g * Ring.inverse (ρ a)) := by
  sorry
''')

_new('S13′', 'Z3NetF.Ss_sep_rowScale', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines`, the remedy and `lem:Ss`**: the statement of `Ss_sep` (every `k ≥ 1`, (H1), (H2), the same bound)
for the graph form with row `r ≥ k + 1` of every generator matrix rescaled by arbitrary `ρ_c` (units are not needed
here; they are needed only for `t = 0`, `rowScale_net`). The rescaled point set is the graph form whose offset row
`r - k ≥ 1` of every block is rescaled, which keeps (H1) and (H2). -/
''', r'''
theorem Ss_sep_rowScale {s q k L : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (h1 : H1 F L Φ) (h2 : H2 Φ) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, IsConfig k e j → B ≤ ∑ i, bval q F L e j i ^ 2) {r : ℕ} (hr : k + 1 ≤ r)
    (ρ : Fin s → ZMod q) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * k))
        (digPoint q (s * k) (rowScale (graphGenK (m := s * k) (fun _ => k) Φ) r ρ) v)
        (digPoint q (s * k) (rowScale (graphGenK (m := s * k) (fun _ => k) Φ) r ρ) w) : ℤ) := by
  sorry
''')

_new('S13′', 'Z3NetF.D_sep_rowScale', _PL[0], _PL[1], 'Z3NetF', _PLF, r'''
/-- **`rem:projlines`, the remedy and `prop:D`**: the statement of `D_sep` (`𝒫^F_{k,q}` of a dominant reachable design,
`q ≥ 5a + 4`, every `k ≥ 1`, the bound `δ ≥ (1 - a/q) N^(-1/s)`) for `𝒫^F_{k,q}` with row `r ≥ k + 1` of every
generator matrix rescaled by arbitrary `ρ_c`. -/
''', r'''
theorem D_sep_rowScale {R : Type*} [CommRing R] {s q a : ℕ} [NeZero q] (hs : 2 ≤ s) (ψ : R →+* ZMod q)
    (k : ℕ) (hk : 1 ≤ k) (inf : Fin s) (x : Fin s → R) (hx : PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : BetaRel inf x (fun n c d => (F n c d : R)) lam β)
    (α : Fin s → ℕ) (h0 : ∀ c, F 0 c c = -(α c : ℤ)) (hdiag : ∀ n c, 1 ≤ n → F n c c = 0)
    (hdom : ∀ c, ∑ d ∈ univ.filter (fun d => d ≠ c),
      (range (s - 1)).sup (fun j => (Msum F j c d).natAbs) ≤ α c)
    (ha : ∀ c, α c ≤ a) (hq : 5 * a + 4 ≤ q) {r : ℕ} (hr : k + 1 ≤ r) (ρ : Fin s → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - a) ^ 2 ≤ (q : ℤ) ^ 2 *
      (torusDist2 (q ^ (s * k))
        (digPoint q (s * k) (rowScale (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) r ρ) v)
        (digPoint q (s * k) (rowScale (fun c => (PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) r ρ) w) :
          ℤ) := by
  sorry
''')

_new('S13′', 'Z3Net.projlines_P', _PL[0], _PL[1], 'Z3Net', _PLZ, r'''
/-- **`rem:projlines` for `𝒫_{k,q}`** (`def:net`; "up to a sign"): for `k` odd, `r* = (3k - 1)/2` and two coordinates
`a ≠ b`, there is an integer sign `g = ±1`, the same for every base `q`, such that over every `ℤ/qℤ` digit `r*` of
coordinate `b` is `g'` times digit `r*` of coordinate `a` plus more significant digits of both iff `g' = g`. (The box
minors `±1` of `thm:t0` and `projlines_box`; the value of `g` is computed, not stated. Any odd `k ≥ 1`.) -/
''', r'''
theorem projlines_P (k : ℕ) (hk : Odd k) {a b : Fin 3} (hab : a ≠ b) :
    ∃ g : ℤ, (g = 1 ∨ g = -1) ∧ ∀ (q : ℕ) (g' : ZMod q),
      Z3NetF.RowRel ((PGen k a).map (Int.cast : ℤ → ZMod q)) ((PGen k b).map (Int.cast : ℤ → ZMod q))
        ((3 * k - 1) / 2) g' ↔ g' = g := by
  sorry
''')

_new('S13′', 'Z3Net.P_net_rowScale', _PL[0], _PL[1], 'Z3Net', _PLZ, r'''
/-- **`rem:projlines`, the remedy on `𝒫_{k,q}`** (with `thm:t0`): rescaling any row `r` of the three generator matrices
of `𝒫_{k,q}` by units `ρ_c` of `ℤ/qℤ` gives a digital `(0,3k,3)`-net (every `k ≥ 1`, every `q ≥ 1`). -/
''', r'''
theorem P_net_rowScale (q : ℕ) [NeZero q] (k : ℕ) (hk : 1 ≤ k) (r : ℕ) (ρ : Fin 3 → ZMod q)
    (hρ : ∀ c, IsUnit (ρ c)) :
    Z3NetF.IsNet0 3 q (3 * k) (Z3NetF.digPoint q (3 * k)
      (Z3NetF.rowScale (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) r ρ)) := by
  sorry
''')

_new('S13′', 'Z3Net.P_sep_rowScale', _PL[0], _PL[1], 'Z3Net', _PLZ, r'''
/-- **`rem:projlines`, the remedy and `thm:sep`**: the statement of `P_sep` (`q ≥ 4`, `k ≥ 2`, exact integer form,
`δ ≥ c(q) N^(-1/3)`) for `𝒫_{k,q}` with row `r ≥ k + 1` of each of the three generator matrices multiplied by an
arbitrary `ρ_c ∈ ℤ/qℤ` (the proof of `thm:sep` uses the digits below the geometric digit only through `prop:cell`(b),
which the rescaling keeps). -/
''', r'''
theorem P_sep_rowScale (q k r : ℕ) (hq : 4 ≤ q) (hk : 2 ≤ k) (hr : k + 1 ≤ r) (ρ : Fin 3 → ZMod q)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) *
        min (((q : ℤ) - 1) ^ 2) (min (((q : ℤ) - 2) ^ 2 + ((q : ℤ) - 4) ^ 2) (3 * ((q : ℤ) - 3) ^ 2))
      ≤ (q : ℤ) ^ 2 * (torusDist2 (q ^ (3 * k))
          (digPoint q (3 * k) (Z3NetF.rowScale (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) r ρ) v)
          (digPoint q (3 * k) (Z3NetF.rowScale (fun c => (PGen k c).map (Int.cast : ℤ → ZMod q)) r ρ) w) :
            ℤ) := by
  sorry
''')

EXTRA_MODS['Frames'] = EXTRA_MODS.get('Frames', []) + ['Z3Net.ThmADefs', 'Z3Net.DGSDefs']

_new('S13′', 'Z3NetA.A_sep_rowScale', _PL[0], _PL[1], 'Z3NetA', ['open Matrix Finset Z3NetF'], r'''
/-- **`rem:projlines`, the remedy and `thm:A`(2)**: the statement of `A_sep` (`q ≥ 5 a*_s + 4` admissible, every
`k ≥ 1`, `δ ≥ (1 - a*_s/q) N^(-1/s)`) for `𝒫^{U*_s}_{k,q}` (generator matrices `AGen`) with row `r ≥ k + 1` of every
generator matrix rescaled by arbitrary `ρ_c` (the bound goes through `prop:D` and `lem:Ss`). -/
''', r'''
theorem A_sep_rowScale (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q) (hqa : 5 * aStar s + 4 ≤ q)
    (hk : 1 ≤ k) {r : ℕ} (hr : k + 1 ≤ r) (ρ : Fin s → ZMod q) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aStar s) ^ 2 ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (s * k)) (digPoint q (s * k) (rowScale (AGen s q k) r ρ) v)
        (digPoint q (s * k) (rowScale (AGen s q k) r ρ) w) : ℤ) := by
  sorry
''')

# ---------------------------------------------------------------- stage S13′ (3/4): `rem:accounting` (first-order accounting
# of the `s = 5` layers at one resolution: `limsup K_eff ≤ dj` under (Λ), `liminf K_eff ≥ dr` for `det F₀ ≠ 0`, the
# exact expansion for `𝒬*_p`, the printed layer without (Λ)). Definitions `Z3Net/AcctDefs.lean`; proofs `Z3Net/AcctUp.lean`,
# `Z3Net/AcctLow.lean`, `Z3Net/AcctCert.lean`, `Z3Net/AcctMain.lean`; restatements `Z3Net/S13Main.lean`.
EXTRA_MODS['Split'] = EXTRA_MODS.get('Split', []) + ['Z3Net.AcctDefs']
_AC = ('Split', 'rem:accounting')

_new('S13′', 'Z3NetHL.sepN_spec', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`δN^{1/5}` as used in `rem:accounting`** (`sepN`, definition in `Z3Net/AcctDefs.lean`): for every `p ≥ 2` and
every point set `X` indexed by `(ℤ/pℤ)⁵` (integer points in `[0, p⁵)⁵`), `sepN p X` is `p` (`= N^{1/5}`) times the
least toroidal distance of two points with distinct indices: it is at most the value of every pair and equal to the
value of some pair. -/
''', r'''
theorem sepN_spec (p : ℕ) (hp : 2 ≤ p) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) :
    (∀ x y : Fin (5 * 1) → ZMod p, x ≠ y → sepN p X ≤ (p : ℝ) * Real.sqrt (∑ c,
      ((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℝ) / (p : ℝ) ^ (5 * 1)) ^ 2)) ∧
    ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧ sepN p X = (p : ℝ) * Real.sqrt (∑ c,
      ((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℝ) / (p : ℝ) ^ (5 * 1)) ^ 2) := by
  sorry
''')

_new('S13′', 'Z3NetHL.ell2_eq_halfEllInf', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`ℓ` of `rem:accounting`** is the `ℓ` of the proof of `prop:half5` as formalized in S11′: `2ℓ_c(E)` (`ell2`, an
integer) is twice `halfEllInf` (`min(|E_c ± ½|)` for `σ_E` odd, `min_κ |E_c − κ|`, `κ ∈ {0, sgn β_c}`, for `σ_E`
even). -/
''', r'''
theorem ell2_eq_halfEllInf (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) :
    (ell2 F2 E c : ℝ) = 2 * halfEllInf F2 E c := by
  sorry
''')

_new('S13′', 'Z3NetHL.acct_upper', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`rem:accounting`, `limsup K_eff ≤ dj`** (the upper bound for `K_eff` of the printed proof, via `lem:R2`): let
`F₀ = F2/2 ∈ (½ + ℤ)^{5×5}` (`F2` odd) satisfy (Λ) (`LamHyp`), and let the deeper rows `D` be arbitrary integer
matrices (`D₁ = D c 1`). Then there are `C` and `P` such that for every prime `p ≥ P` the digital point set over
`𝔽_p` with these rows has `δN^{1/5} ≥ (√5/2)(1 − 2dj(F₀,D₁)/(5p)) − C/p²` (toroidal; `dj2 = 2dj`). (`det F₀ ≠ 0`
is not needed here; `C`, `P` are not explicit, as the paper's `O(p⁻²)`.) -/
''', r'''
theorem acct_upper (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hΛ : LamHyp F2) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      Real.sqrt 5 / 2 * (1 - (dj2 F2 (fun c d => D c 1 d) : ℝ) / (5 * p)) - C / (p : ℝ) ^ 2
        ≤ sepN p (halfNet p F2 D) := by
  sorry
''')

_new('S13′', 'Z3NetHL.acct_lower', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`rem:accounting`, `liminf K_eff ≥ dr`** (the lower bound of the printed proof, by an explicit pair): let
`F₀ = F2/2 ∈ (½ + ℤ)^{5×5}` with `det F₀ ≠ 0`, deeper rows `D` arbitrary. Then there are `C` and `P` such that for
every prime `p ≥ P`, `δN^{1/5} ≤ (√5/2)(1 − 2dr(F₀)/(5p)) + C/p²` (toroidal; `drift2 = 2dr`). ((Λ) is not needed
here.) -/
''', r'''
theorem acct_lower (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hdet : (Matrix.of F2).det ≠ 0) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      sepN p (halfNet p F2 D) ≤ Real.sqrt 5 / 2 * (1 - (drift2 F2 : ℝ) / (5 * p)) + C / (p : ℝ) ^ 2 := by
  sorry
''')

_new('S13′', 'Z3NetHL.acct_main', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`rem:accounting`** (`dr(F₀) ≤ liminf K_eff ≤ limsup K_eff ≤ dj(F₀, D₁)`, in `ε` form): let
`F₀ = F2/2 ∈ (½ + ℤ)^{5×5}` with `det F₀ ≠ 0` satisfy (Λ), and let `D` be arbitrary integer deeper rows. For every
`ε > 0` there is `P` such that for every prime `p ≥ P`, `K_eff(p) = (5p/2)(1 − δN^{1/5}/(√5/2))` of the digital point
set with these rows lies in `[dr(F₀) − ε, dj(F₀, D₁) + ε]` (`drift2 = 2dr`, `dj2 = 2dj`). The `liminf`/`limsup` form
is `acct_liminf`. -/
''', r'''
theorem acct_main (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hdet : (Matrix.of F2).det ≠ 0) (hΛ : LamHyp F2) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      (drift2 F2 : ℝ) / 2 - ε ≤ Keff p (halfNet p F2 D) ∧
        Keff p (halfNet p F2 D) ≤ (dj2 F2 (fun c d => D c 1 d) : ℝ) / 2 + ε := by
  sorry
''')

_new('S13′', 'Z3NetHL.acct_liminf', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`rem:accounting`, as printed**: under the hypotheses of `acct_main`,
`dr(F₀) ≤ liminf_{p→∞} K_eff(p) ≤ limsup_{p→∞} K_eff(p) ≤ dj(F₀, D₁)`, the limits taken along the primes (the
filter `atTop ⊓ 𝓟 {p | p prime}`; `K_eff` is bounded along it, so these are genuine `liminf`/`limsup` in `ℝ`). -/
''', r'''
theorem acct_liminf (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hdet : (Matrix.of F2).det ≠ 0) (hΛ : LamHyp F2) :
    (drift2 F2 : ℝ) / 2 ≤
        Filter.liminf (fun p => Keff p (halfNet p F2 D)) (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) ∧
      Filter.liminf (fun p => Keff p (halfNet p F2 D)) (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) ≤
        Filter.limsup (fun p => Keff p (halfNet p F2 D)) (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) ∧
      Filter.limsup (fun p => Keff p (halfNet p F2 D)) (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) ≤
        (dj2 F2 (fun c d => D c 1 d) : ℝ) / 2 := by
  sorry
''')

_new('S13′', 'Z3NetHL.acct_exact', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`rem:accounting`, "in particular"**: under the hypotheses of `acct_main`, if moreover `dj(F₀, D₁) = dr(F₀)`, then
`δN^{1/5} = (√5/2)(1 − 2dr(F₀)/(5p)) + O(p⁻²)` along the primes: `|δN^{1/5} − (√5/2)(1 − 2dr/(5p))| ≤ C/p²` for
every prime `p ≥ P`. -/
''', r'''
theorem acct_exact (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hdet : (Matrix.of F2).det ≠ 0) (hΛ : LamHyp F2) (heq : dj2 F2 (fun c d => D c 1 d) = drift2 F2) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      |sepN p (halfNet p F2 D) - Real.sqrt 5 / 2 * (1 - (drift2 F2 : ℝ) / (5 * p))| ≤ C / (p : ℝ) ^ 2 := by
  sorry
''')

_new('S13′', 'Z3NetHL.acct_qstar', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`rem:accounting` for `𝒬*_p`**: `dr(F₀*) = dj(F₀*, D₁) = 17/2`, `det 2F₀* = −880`, `|ℓ(E)|² ≥ 2` (i.e.
`∑_c (2ℓ_c(E))² ≥ 8`) on every non-binding step, hence (Λ), and `δN^{1/5} = (√5/2)(1 − 17/(5p)) + O(p⁻²)` (toroidal)
along the primes (`Qstar p = halfNet p F2star Dstar` by definition). -/
''', r'''
theorem acct_qstar : drift2 F2star = 17 ∧ dj2 F2star D1star = 17 ∧ (Matrix.of F2star).det = -880 ∧
    (∀ E ∈ halfSteps 5, E ∉ bind5 → 8 ≤ ∑ c, ell2 F2star E c ^ 2) ∧ LamHyp F2star ∧
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      |sepN p (Qstar p) - Real.sqrt 5 / 2 * (1 - 17 / (5 * p))| ≤ C / (p : ℝ) ^ 2 := by
  sorry
''')

_new('S13′', 'Z3NetHL.acct_counterexample', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **"(Λ) is a genuine hypothesis"** (`rem:accounting`): the printed layer `2F₀ = F2cex` has odd entries, satisfies
(B2) and (MIN) (`DisjMinors`) and has `det 2F₀ = 560`, but the even step `E = (1, −1, −2, −1, −1)` (in
`{-2, …, 2}⁵ \ {0}`, not binding) has `2β = (4, −6, −2, −2, −2)` and `∑_c (2ℓ_c(E))² = 4`, i.e. `|ℓ(E)| = 1`; so (Λ)
fails. -/
''', r'''
theorem acct_counterexample : (∀ c d, Odd (F2cex c d)) ∧ B2D F2cex ∧ DisjMinors F2cex ∧
    (Matrix.of F2cex).det = 560 ∧ ![1, -1, -2, -1, -1] ∈ halfSteps 5 ∧ ![1, -1, -2, -1, -1] ∉ bind5 ∧
    (fun c => dotR F2cex ![1, -1, -2, -1, -1] c) = ![4, -6, -2, -2, -2] ∧
    ∑ c, ell2 F2cex ![1, -1, -2, -1, -1] c ^ 2 = 4 ∧ ¬ LamHyp F2cex := by
  sorry
''')


# ---------------------------------------------------------------- stage S14′ (`sec:base23`: `def:lift`, `lem:lift`,
# `lem:liftsep`, `lem:shiftcert` (with the fixes F1–F4 of the research notes), `thm:base23` with part (3)).
# Statement review: the statement-review notes (research repository). Restatements `Z3Net/B23Restate.lean` (generated by
# `scripts/gen_s14main.py` from the texts below).
EXTRA_SOLUTION.append('Z3Net.B23Restate')
EXTRA_MODS['Base23'] = EXTRA_MODS.get('Base23', []) + ['Z3Net.B23Fam', 'Z3Net.B23Consts']
_B23 = ['open Matrix']

_new('S14′', 'Z3NetB23.lift_net', 'Base23', 'lem:lift', 'Z3NetB23', _B23, r'''
/-- **`lem:lift`(A)**: if `P` (generator matrices `C`, digital shift `σ`) is a digitally shifted digital `(0,M,3)`-net
over `F_b` and `s_A, s_B` are admissible (`def:lift`), the lift `L_D(P)` (generator matrices `liftGen C s_A s_B`, shift
`liftShift σ`) is a digitally shifted digital `(0, M+3, 3)`-net. -/
''', r'''
theorem lift_net {b M : ℕ} [Fact b.Prime] (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (σ sA sB : Fin 3 → Fin M → ZMod b)
    (hP : Z3NetF.IsNet0 3 b M (Z3NetF.digPointShift b M C σ)) (hadm : Admissible C sA sB) :
    Z3NetF.IsNet0 3 b (M + 3) (Z3NetF.digPointShift b (M + 3) (liftGen C sA sB) (liftShift σ)) := by
  sorry
''')

_new('S14′', 'Z3NetB23.lift_exists', 'Base23', 'lem:lift', 'Z3NetB23', _B23, r'''
/-- **`lem:lift`(B)**: if `P` is a digitally shifted digital `(0,M,3)`-net over `F_b` and `2D ≤ M`, there are
admissible `s_A, s_B` vanishing on the first `D` digits of each coordinate. -/
''', r'''
theorem lift_exists {b M : ℕ} [Fact b.Prime] (C : Fin 3 → Matrix (Fin M) (Fin M) (ZMod b)) (σ : Fin 3 → Fin M → ZMod b)
    (hP : Z3NetF.IsNet0 3 b M (Z3NetF.digPointShift b M C σ)) (D : ℕ) (hD : 2 * D ≤ M) :
    ∃ sA sB : Fin 3 → Fin M → ZMod b, VanishTop D sA ∧ VanishTop D sB ∧ Admissible C sA sB := by
  sorry
''')

_new('S14′', 'Z3NetB23.liftsep', 'Base23', 'lem:liftsep', 'Z3NetB23', _B23, r'''
/-- **`lem:liftsep`**: let `P_L → P_{L+3} → ⋯` be lifts (a deep-shift chain from `P_L`, generator matrices `C₀`, shift
`σ₀`) whose depth parameters satisfy `D_{L+3j'} ≥ ⌊L/2⌋ + j'`. Then for every level `m = L + 3j` and any two distinct
indices `v, w` of `P_m` (with its own shift), the toroidal distance of the points is at least
`min(g_L, b^{L/3} − W b^{-2L/3}) · N^{-1/3}`, `N = b^m`, `W = b^(L − ⌊L/2⌋)`, `g_L = W √(v*_L) b^{-2L/3}`; i.e.
`δ N^{1/3} ≥ min(g_L, b^{L/3} − W b^{-2L/3})`. -/
''', r'''
theorem liftsep {b : ℕ} [Fact b.Prime] {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)}
    {σ₀ : Fin 3 → Fin L → ZMod b} {D : ℕ → ℕ} (hD : ∀ ℓ, L ≤ ℓ → L / 2 + (ℓ - L) / 3 ≤ D ℓ) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b L C₀ σ₀ D m C σ) (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    min (gL b L (vstar b L C₀ σ₀)) (((b : ℝ) ^ L) ^ (1 / 3 : ℝ) - (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ))) *
        ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C σ v c : ℤ) -
        Z3NetF.digPointShift b m C σ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  sorry
''')

_new('S14′', 'Z3NetB23.shiftcert_a', 'Base23', 'lem:shiftcert', 'Z3NetB23', _B23, r'''
/-- **`lem:shiftcert`(a)** (with the fix F1 of the research notes: distinct points, `Δ = 0` allowed): under the hypothesis of `lem:liftsep`, for every level `m` of the
chain, **every digital shift** `τ` of depth `m` and any two distinct indices,
`δ(P_m ⊕ τ) N^{1/3} ≥ min(W √(v°_L) b^{-2L/3}, b^{L/3} − W b^{-2L/3})`, with `v°_L = vcirc b L C₀` (the minimum over
distinct points of `P_L` of `∑_c max(0, μ_{⌊L/2⌋}(Δ_c) − 1)²`, `Δ` the difference of their top `⌊L/2⌋` digits). -/
''', r'''
theorem shiftcert_a {b : ℕ} [Fact b.Prime] {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)}
    {σ₀ : Fin 3 → Fin L → ZMod b} {D : ℕ → ℕ} (hD : ∀ ℓ, L ≤ ℓ → L / 2 + (ℓ - L) / 3 ≤ D ℓ) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b L C₀ σ₀ D m C σ) (τ : Fin 3 → Fin m → ZMod b) (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    min (gL b L (vcirc b L C₀)) (((b : ℝ) ^ L) ^ (1 / 3 : ℝ) - (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ))) *
        ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  sorry
''')

_new('S14′', 'Z3NetB23.vcirc_eq_iInf', 'Base23', 'lem:shiftcert', 'Z3NetB23', _B23, r'''
/-- **`lem:shiftcert`(a), `v°_L` as a minimum over shifts**: `v°_L = min_{τ'} v*_L(P_L ⊕ τ')`, the minimum over all
digital shifts `τ'` of `P_L` of the certificate `v*_L` of `lem:liftsep` (`L ≥ 1`). -/
''', r'''
theorem vcirc_eq_iInf {b : ℕ} [Fact b.Prime] (L : ℕ) (hL : 1 ≤ L) (C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) :
    vcirc b L C₀ = ⨅ τ' : Fin 3 → Fin L → ZMod b, vstar b L C₀ τ' := by
  sorry
''')

_new('S14′', 'Z3NetB23.shiftcert_b', 'Base23', 'lem:shiftcert', 'Z3NetB23', _B23, r'''
/-- **`lem:shiftcert`(b)**: for every digital net over `F_b` (generator matrices `C`): (i) for every digital shift `τ`
and any two indices `v, w`, `∑_c μ_m(Δ_c)² ≤ |X − X'|²` (squared toroidal distance at scale `b^m`), `Δ = C(w − v)` the
digit difference; (ii) for every `d` some shift attains it with the pair `(0, d)`. Hence
`min_τ δ(P ⊕ τ)² = b^{-2m} min_{Δ ≠ 0} ∑_c μ_m(Δ_c)²` over the nonzero digit differences of two points. -/
''', r'''
theorem shiftcert_b {b : ℕ} [Fact b.Prime] {m : ℕ} (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)) :
    (∀ (τ : Fin 3 → Fin m → ZMod b) (v w : Fin m → ZMod b),
      ∑ c : Fin 3, muD b (C c *ᵥ (w - v)) ^ 2 ≤
        Z3NetF.torusDist2 (b ^ m) (Z3NetF.digPointShift b m C τ v) (Z3NetF.digPointShift b m C τ w)) ∧
    (∀ d : Fin m → ZMod b, ∃ τ : Fin 3 → Fin m → ZMod b,
      Z3NetF.torusDist2 (b ^ m) (Z3NetF.digPointShift b m C τ 0) (Z3NetF.digPointShift b m C τ d) =
        ∑ c : Fin 3, muD b (C c *ᵥ d) ^ 2) := by
  sorry
''')

_new('S14′', 'Z3NetB23.b23_seed', 'Base23', 'thm:base23', 'Z3NetB23', _B23, r'''
/-- **`thm:base23`, the seeds** (`tab:b23seeds`): for `b ∈ {2, 3}` and every residue class `r`, the chain level `0`
has the generator matrices `(I, A_y, A_z)`, where row `d` of `A_y` (resp. `A_z`) is the digit vector of the printed
integer `b23RowsY b r` (resp. `b23RowsZ b r`) at position `d`. -/
''', r'''
theorem b23_seed (b r : ℕ) (hb : b = 2 ∨ b = 3) :
    b23Gen b r 0 = ![1, rowMat b (b23SeedM b r) (b23RowsY b r), rowMat b (b23SeedM b r) (b23RowsZ b r)] := by
  sorry
''')

_new('S14′', 'Z3NetB23.b23_lift', 'Base23', 'thm:base23', 'Z3NetB23', _B23, r'''
/-- **`thm:base23`, the fixed chains**: for `b ∈ {2, 3}`, every residue class `r` and every lift `k` up to the
certificate level, the chain level `k + 1` is the lift (`def:lift`) of level `k` with the parameters `b23Lifts b r`,
and these parameters are admissible. -/
''', r'''
theorem b23_lift (b r k : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) (hr : r < 3) (hk : k < b23NL b r) :
    b23Gen b r (k + 1) = liftGen (b23Gen b r k) (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).1)
      (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).2) ∧
    Admissible (b23Gen b r k) (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).1)
      (shOf b (b23Lev b r k) ((b23Lifts b r).getD k ([], [])).2) := by
  sorry
''')

_new('S14′', 'Z3NetB23.b23_vcirc', 'Base23', 'thm:base23', 'Z3NetB23', _B23, r'''
/-- **`thm:base23`, the every-shift certificates**: at the certificate level `L` of each residue class,
`v°_L ≥ b23Vcert b r` (`168, 110, 3` for `b = 2`, `8, 86, 9` for `b = 3`; kernel-checked). -/
''', r'''
theorem b23_vcirc (b r : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) (hr : r < 3) :
    b23Vcert b r ≤ vcirc b (b23Lev b r (b23NL b r)) (b23Gen b r (b23NL b r)) := by
  sorry
''')

_new('S14′', 'Z3NetB23.base23_net', 'Base23', 'thm:base23', 'Z3NetB23', _B23, r'''
/-- **`thm:base23`, the nets**: for `b ∈ {2, 3}` every net of the theorem (`IsB23Gen`: an explicit witness below the
seed level, a level of the fixed chain, or any continuation by admissible lifts with `D_ℓ = ⌊ℓ/2⌋` beyond the
certificate level) is a `(0,m,3)`-net over `F_b`, with any digital shift. -/
''', r'''
theorem base23_net (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    (h : IsB23Gen b m C) (σ : Fin 3 → Fin m → ZMod b) : Z3NetF.IsNet0 3 b m (Z3NetF.digPointShift b m C σ) := by
  sorry
''')

_new('S14′', 'Z3NetB23.base23_exists', 'Base23', 'thm:base23', 'Z3NetB23', _B23, r'''
/-- **`thm:base23`, every `m ≥ 1`**: for `b ∈ {2, 3}` and every `m ≥ 1` there is a net of the theorem at level `m`. -/
''', r'''
theorem base23_exists (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b), IsB23Gen b m C := by
  sorry
''')

_new('S14′', 'Z3NetB23.base23_everyshift', 'Base23', 'thm:base23', 'Z3NetB23', _B23, r'''
/-- **`thm:base23`(3), every digital shift**: for `b ∈ {2, 3}`, every net of the theorem at level `m`, every digital
shift `τ` of depth `m` and any two distinct indices, `δ(P_m ⊕ τ) N^{1/3} ≥ b23C b (m mod 3)` (toroidal distance), the
constants `.4050, .4129, .1718` (`b = 2`) and `.1047, .1651, .0770` (`b = 3`) for `m ≡ 0, 1, 2 (mod 3)`. -/
''', r'''
theorem base23_everyshift (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} (h : IsB23Gen b m C) (τ : Fin 3 → Fin m → ZMod b)
    (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    b23C b (m % 3) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  sorry
''')

_new('S14′', 'Z3NetB23.base23_everyshift_base', 'Base23', 'thm:base23', 'Z3NetB23', _B23, r'''
/-- **`thm:base23`(3) per base, and (2)** (`τ = 0`): `δ(P_m ⊕ τ) N^{1/3} ≥ 0.1718` for `b = 2` and `≥ 0.0770` for
`b = 3`, for every `m ≥ 1`, every net of the theorem and every digital shift (including no shift). -/
''', r'''
theorem base23_everyshift_base (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} (h : IsB23Gen b m C) (τ : Fin 3 → Fin m → ZMod b)
    (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    (if b = 2 then (0.1718 : ℝ) else 0.0770) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  sorry
''')

_new('S14′', 'Z3NetB23.base23_witcur', 'Base23', 'thm:base23', 'Z3NetB23', _B23, r'''
/-- **The current witnesses** `b = 2`, `m = 6, 7` (`base23_audit/witness_smallm`, not used by `IsB23Gen`, which takes
the replacement witnesses of the research notes): `(0,m,3)`-nets with every-shift constants `.2165`, `.3100`. -/
''', r'''
theorem base23_witcur (m : ℕ) (hm : m = 6 ∨ m = 7) :
    (∀ σ, Z3NetF.IsNet0 3 2 m (Z3NetF.digPointShift 2 m (colMat 2 m (b23WitCur m)) σ)) ∧
    ∀ (τ : Fin 3 → Fin m → ZMod 2) (v w : Fin m → ZMod 2), v ≠ w →
      (if m = 6 then (0.2165 : ℝ) else 0.3100) * ((2 : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
        Real.sqrt (∑ c, ((Z3NetF.cres (2 ^ m) ((Z3NetF.digPointShift 2 m (colMat 2 m (b23WitCur m)) τ v c : ℤ) -
          Z3NetF.digPointShift 2 m (colMat 2 m (b23WitCur m)) τ w c) : ℝ) / (2 : ℝ) ^ m) ^ 2) := by
  sorry
''')

_new('S14′', 'Z3NetB23.base23_shifted', 'Base23', 'thm:base23', 'Z3NetB23', _B23, r'''
/-- **`thm:base23`(1) beyond the certificate level, given the certificate** (a decidable finite check, not run in
the kernel; see the statement-review notes (research repository)): if every pair of distinct points of `P_L` with its explicit shift has weight
`≥ v₁` in `v*_L`, then along every deep-shift chain from `P_L` with its explicit shift and `D_ℓ = ⌊ℓ/2⌋`,
`δ N^{1/3} ≥ min(g_L(v₁), b^{L/3} − W b^{-2L/3})`. -/
''', r'''
theorem base23_shifted (b r : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) (hr : r < 3) (v₁ : ℕ)
    (hcert : ∀ n n' : Fin (b23Lev b r (b23NL b r)) → ZMod b, n ≠ n' →
      v₁ ≤ ∑ c : Fin 3, hW (Z3NetF.cres (b ^ (b23Lev b r (b23NL b r) / 2))
        (((Z3NetF.digPointShift b _ (b23Gen b r (b23NL b r)) (b23Shift b r (b23NL b r)) n c /
            b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2) : ℕ) : ℤ) -
          ((Z3NetF.digPointShift b _ (b23Gen b r (b23NL b r)) (b23Shift b r (b23NL b r)) n' c /
            b ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2) : ℕ) : ℤ))))
    {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b (b23Lev b r (b23NL b r)) (b23Gen b r (b23NL b r)) (b23Shift b r (b23NL b r))
      (fun ℓ => ℓ / 2) m C σ) (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    min (gL b (b23Lev b r (b23NL b r)) v₁) (((b : ℝ) ^ b23Lev b r (b23NL b r)) ^ (1 / 3 : ℝ) -
        (b : ℝ) ^ (b23Lev b r (b23NL b r) - b23Lev b r (b23NL b r) / 2) *
          ((b : ℝ) ^ b23Lev b r (b23NL b r)) ^ (-(2 / 3 : ℝ))) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C σ v c : ℤ) -
        Z3NetF.digPointShift b m C σ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  sorry
''')


# ---------------------------------------------------------------- stage S15′ (`rem:ppshift`; `rem:dgsfinite` in every prime
# base under every digital shift; `prop:k1designs`: the `t = 0` completions of the frameless layers and the `s = 5` frame
# layer). Statement review: the statement-review notes (research repository). Restatements `Z3Net/S15Restate.lean` (generated by
# `scripts/gen_s15main.py` from the texts below).
EXTRA_SOLUTION.append('Z3Net.S15Restate')
EXTRA_MODS['Appendix'] = EXTRA_MODS.get('Appendix', []) + ['Z3Net.DShiftDefs']
EXTRA_MODS['Deficit'].append('Z3Net.K1ComplDefs')

_new('S15′', 'Z3NetKN.ppsep_shift', 'Appendix', 'rem:ppshift', 'Z3NetKN', _KO, r'''
/-- **`rem:ppshift`** (general form): `prop:ppsep` holds verbatim, with the same certificate `(T, Rg)`
(`def:pprelax`), for every digital shift `τ` (`def:dshift`) of every graph form `C` carrying the design `R` (net or not):
the points of `P ⊕ τ` satisfy `‖X(w) − X(v)‖²_torus ≥ T u²` for all indices `v ≠ w` (integer coordinates on the torus
of side `N = p^(3k+r)`, `u = p^(m−k−2)`). Here `p` is any prime (the unshifted `ppsep_general` assumes `p` odd). -/
''', r'''
theorem ppsep_shift (p r k T : ℕ) (hp : p.Prime) (hk : (r = 1 ∧ 3 ≤ k) ∨ (r = 2 ∧ 2 ≤ k)) (R : Rows)
    (Rg : Fin 3 → ℕ) (hcert : IsPPCert p r Rg R T)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (τ : Fin 3 → Fin (3 * k + r) → ZMod p) (v w : Fin (3 * k + r) → ZMod p) (hvw : v ≠ w) :
    T * (p ^ (3 * k + r - (k + 2))) ^ 2 ≤
      torusDist2 (p ^ (3 * k + r)) (Z3NetF.digPointShift p (3 * k + r) C τ v)
        (Z3NetF.digPointShift p (3 * k + r) C τ w) := by
  sorry
''')

_new('S15′', 'Z3NetKN.KN1_sep_shift', 'Appendix', 'rem:ppshift', 'Z3NetKN', _KO, r'''
/-- **`rem:ppshift`**, the per-prime designs with `m ≡ 1` (`table1`, `tab:perprime`): for each design `(p, T_p, R)`,
every `k ≥ 3`, every graph form `C` with these rows, every digital shift `τ` and distinct indices `v ≠ w`, with
`N = p^(3k+1)`: `T_p · p^(4k-2) ≤ N² δ²` for the points of `P ⊕ τ`, i.e. `δ ≥ √T_p · p^(-5/3) · N^(-1/3)`. -/
''', r'''
theorem KN1_sep_shift (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table1) (k : ℕ) (hk : 3 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (hC : IsKN 1 p k R C)
    (τ : Fin 3 → Fin (3 * k + 1) → ZMod p) (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    T * p ^ (4 * k - 2) ≤
      torusDist2 (p ^ (3 * k + 1)) (Z3NetF.digPointShift p (3 * k + 1) C τ v)
        (Z3NetF.digPointShift p (3 * k + 1) C τ w) := by
  sorry
''')

_new('S15′', 'Z3NetKN.KN2_sep_shift', 'Appendix', 'rem:ppshift', 'Z3NetKN', _KO, r'''
/-- **`rem:ppshift`**, the per-prime designs with `m ≡ 2` (`table2`, `tab:perprime`): for each design `(p, T_p, R)`,
every `k ≥ 2`, every graph form `C` with these rows, every digital shift `τ` and `v ≠ w`, with `N = p^(3k+2)`:
`T_p · p^(4k) ≤ N² δ²` for the points of `P ⊕ τ`, i.e. `δ ≥ √T_p · p^(-4/3) · N^(-1/3)`. -/
''', r'''
theorem KN2_sep_shift (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table2) (k : ℕ) (hk : 2 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p)) (hC : IsKN 2 p k R C)
    (τ : Fin 3 → Fin (3 * k + 2) → ZMod p) (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    T * p ^ (4 * k) ≤
      torusDist2 (p ^ (3 * k + 2)) (Z3NetF.digPointShift p (3 * k + 2) C τ v)
        (Z3NetF.digPointShift p (3 * k + 2) C τ w) := by
  sorry
''')

_new('S15′', 'Z3NetDGS.dgs_pp', 'DGS', 'rem:dgsfinite', 'Z3NetDGS', _DO, r'''
/-- **`rem:dgsfinite`, the per-prime range**: for every prime `5 ≤ p ≤ 31` and every `m ≥ 10` there are generator
matrices (in the proof: `thm:main` for `m ≡ 0`, the per-prime designs of `app:perprime` for `m ≡ 1, 2`, with
`rem:ppshift`) such that every digital shift of the net is a `(0,m,3)`-net in base `p` and `(⌊m/3⌋ + 3)`-separated and
toroidally `(⌊m/3⌋ + 3)`-separated. -/
''', r'''
theorem dgs_pp (p m : ℕ) [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hp31 : p ≤ 31) (hm : 10 ≤ m) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : Fin 3 → Fin m → ZMod p,
      IsTMSNet p 0 m (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSep p (m / 3 + 3) (ptSet p (Z3NetF.digPointShift p m C τ)) ∧
      IsKSepTor p (m / 3 + 3) (ptSet p (Z3NetF.digPointShift p m C τ)) := by
  sorry
''')

_new('S15′', 'Z3NetDGS.dgs_family_pp', 'DGS', 'rem:dgsfinite', 'Z3NetDGS', _DO, r'''
/-- **`rem:dgsfinite`, `5 ≤ p ≤ 31`**: there are digital `(0,m,3)`-nets over `𝔽_p` for every `m ∈ ℕ` (the frame of the
places `∞, 0, 1` for `m ≤ 9`, the nets of `dgs_pp` for `m ≥ 10`) such that for every choice of digital shifts `τ_m` the
family `(P_m ⊕ τ_m)_{m ∈ ℕ}` is well separated and toroidally well separated on all of `ℕ` in the sense of
`[DGS2, Def. 3.8]`. -/
''', r'''
theorem dgs_family_pp (p : ℕ) [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hp31 : p ≤ 31) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p,
      WellSepFamily p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      WellSepFamilyTor p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) := by
  sorry
''')

_new('S15′', 'Z3NetDGS.dgs_family_b23', 'DGS', 'rem:dgsfinite', 'Z3NetDGS', _DO, r'''
/-- **`rem:dgsfinite`, `b ∈ {2, 3}`**: there are digital `(0,m,3)`-nets over `𝔽_b` for every `m ∈ ℕ` (the frame of the
places `∞, 0, 1` for `m = 0`, the nets of `thm:base23` for `m ≥ 1`) such that for every choice of digital shifts `τ_m`
the family `(P_m ⊕ τ_m)_{m ∈ ℕ}` is well separated and toroidally well separated on all of `ℕ` in the sense of
`[DGS2, Def. 3.8]` (`thm:base23`(3) and `cor:dgs`). -/
''', r'''
theorem dgs_family_b23 (b : ℕ) [Fact b.Prime] (hb : b = 2 ∨ b = 3) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod b,
      WellSepFamily b 0 3 Set.univ (fun m => ptSet b (Z3NetF.digPointShift b m (C m) (τ m))) ∧
      WellSepFamilyTor b 0 3 Set.univ (fun m => ptSet b (Z3NetF.digPointShift b m (C m) (τ m))) := by
  sorry
''')

_new('S15′', 'Z3NetDGS.dgs_family_all', 'DGS', 'rem:dgsfinite', 'Z3NetDGS', _DO, r'''
/-- **`rem:dgsfinite`, every prime base, every digital shift** (the abstract: "In prime bases these families are well
separated in the sense of Dick, Goda and Suzuki, and they stay so under every digital shift"): for every prime `p` there
are digital `(0,m,3)`-nets over `𝔽_p`, one for every `m ∈ ℕ`, such that for every choice of digital shifts `τ_m` the
family `(P_m ⊕ τ_m)_{m ∈ ℕ}` is well separated and toroidally well separated on all of `ℕ` in the sense of
`[DGS2, Def. 3.8]`. (Proof: `dgs_family_b23` for `p ≤ 3`, `dgs_family_pp` for `5 ≤ p ≤ 31`, `dgs_family` for
`p ≥ 37`.) -/
''', r'''
theorem dgs_family_all (p : ℕ) [NeZero p] (hp : p.Prime) :
    ∃ C : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod p), ∀ τ : (m : ℕ) → Fin 3 → Fin m → ZMod p,
      WellSepFamily p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) ∧
      WellSepFamilyTor p 0 3 Set.univ (fun m => ptSet p (Z3NetF.digPointShift p m (C m) (τ m))) := by
  sorry
''')

_new('S15′', 'Z3NetF.k1designs_free5_net', 'Deficit', 'prop:k1designs', 'Z3NetF', _FO, r'''
/-- **`prop:k1designs`(2), `s = 5`**: for every `q` with `gcd(q, 30) = 1` the frameless layer `k1Free5` (`K₁ = 2`) has a
`t = 0` completion: there is a digital `(0,5,5)`-net over `ℤ/qℤ` in graph form with depths `(1, …, 1)` whose first
offset rows are `k1Free5` (diagonal included, reduced modulo `q`) and whose deeper rows vanish in their own column
((H2)); so `prop:k1`(1) (`k1_sep`) applies to it. -/
''', r'''
theorem k1designs_free5_net (q : ℕ) [NeZero q] (hq : Nat.Coprime q 30) :
    ∃ Φ : Fin 5 → Fin 5 → Matrix (Fin (5 * 1 - 1)) (Fin 1) (ZMod q),
      (∀ c d (r : Fin (5 * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (k1Free5 c d : ZMod q)) ∧ H2 Φ ∧
      IsNet0 5 q (5 * 1) (digPoint q (5 * 1) (graphGenK (m := 5 * 1) (fun _ => 1) Φ)) := by
  sorry
''')

_new('S15′', 'Z3NetF.k1designs_free6a_net', 'Deficit', 'prop:k1designs', 'Z3NetF', _FO, r'''
/-- **`prop:k1designs`(2), `s = 6`, `K₁ = 3`**: for every `q` with no prime factor in
`𝓔₆ = {2, 3, 5, 7, 11, 13, 17, 23, 31}` the frameless layer `k1Free6a` has a `t = 0` completion: a digital
`(0,6,6)`-net over `ℤ/qℤ` in graph form with depths `(1, …, 1)`, first offset rows `k1Free6a`, (H2). -/
''', r'''
theorem k1designs_free6a_net (q : ℕ) [NeZero q]
    (hq : ∀ p ∈ ({2, 3, 5, 7, 11, 13, 17, 23, 31} : Finset ℕ), ¬ p ∣ q) :
    ∃ Φ : Fin 6 → Fin 6 → Matrix (Fin (6 * 1 - 1)) (Fin 1) (ZMod q),
      (∀ c d (r : Fin (6 * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (k1Free6a c d : ZMod q)) ∧ H2 Φ ∧
      IsNet0 6 q (6 * 1) (digPoint q (6 * 1) (graphGenK (m := 6 * 1) (fun _ => 1) Φ)) := by
  sorry
''')

_new('S15′', 'Z3NetF.k1designs_free6b_net', 'Deficit', 'prop:k1designs', 'Z3NetF', _FO, r'''
/-- **`prop:k1designs`(2), `s = 6`, `K₁ = 5`** (the second frameless `s = 6` layer of `tab:practical`): for every `q`
with `gcd(q, 210) = 1` the frameless layer `k1Free6b` has a `t = 0` completion: a digital `(0,6,6)`-net over `ℤ/qℤ` in
graph form with depths `(1, …, 1)`, first offset rows `k1Free6b`, (H2). -/
''', r'''
theorem k1designs_free6b_net (q : ℕ) [NeZero q] (hq : Nat.Coprime q 210) :
    ∃ Φ : Fin 6 → Fin 6 → Matrix (Fin (6 * 1 - 1)) (Fin 1) (ZMod q),
      (∀ c d (r : Fin (6 * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (k1Free6b c d : ZMod q)) ∧ H2 Φ ∧
      IsNet0 6 q (6 * 1) (digPoint q (6 * 1) (graphGenK (m := 6 * 1) (fun _ => 1) Φ)) := by
  sorry
''')

_new('S15′', 'Z3NetF.k1designs_frame5_cauchy', 'Deficit', 'prop:k1designs', 'Z3NetF', _FO, r'''
/-- **`prop:k1designs`(1), `s = 5`**: off the diagonal, the `s = 5` frame layer `k1Frame5` of `tab:practical` is the
geometric layer `F₀` of the `s = 5` design of `tab:Kdesigns` (`kdes5F0`, as printed in `app:designs`), and it is the
Cauchy layer `λ'_c μ_d w_cd` (`w_cd` of `prop:Ns`) on the admissible places `∞, 0, 1, 2, 3` with the row scalars
`λ' = (1/2, 1, 1, 1, 1)` of that design and the column scalars `μ = (-1, -6, 2, -2, 6)`. -/
''', r'''
theorem k1designs_frame5_cauchy :
    PlacesOK (0 : Fin 5) kdes5Places ∧
      ∀ c d : Fin 5, c ≠ d → k1Frame5 c d = kdes5F0 c d ∧
        (k1Frame5 c d : ℚ) = kdes5Lam c * kdes5Mu d * wN (0 : Fin 5) kdes5Places c d := by
  sorry
''')

# ---------------------------------------------------------------- stage S16′ (`cor:skelreach`, rev 15.9). Statement review:
# the statement-review notes (research repository). Restatements `Z3Net/S16Restate.lean` (generated by `scripts/gen_s16main.py` from the texts
# below).
EXTRA_SOLUTION.append('Z3Net.S16Restate')
_SK = ['open Matrix Finset']

_new('S16′', 'Z3NetF.skelreach_iff', 'Skeleton', 'cor:skelreach', 'Z3NetF', _SK, r'''
/-- **`cor:skelreach`** (`ℓ = 2`, `s = r + 2`): skeleton digits of the form of `prop:skelcomp`(iii),
`S_{z_i} = ∑_d A_id x_{d,k} + ∑_d β_id x_{d,k-1} + g_i z_{j,k-1} + o_i z_{i,k-1}` (`sk2Coef`), with coefficients that do
not depend on `k`, are reachable from the frame for every `k ≥ 1` for a suitable choice of the places (the moves of
`lem:box`: `Φ_cd = L_c Φ^F_cd U_d` off the diagonal with `L_c`, `U_d` lower triangular with unit diagonal, own blocks
arbitrary) if and only if they satisfy (N1)–(N3) of `lem:skelnec`, which for skeleton digits of this form read: every
entry and every `2 × 2` minor of `A` is nonzero (N1), `g_1, g_2 ≠ 0` (N2), and `det[A_{·d}, β_{·d}] ≠ 0` for every full
coordinate `x_d` (N3). -/
''', r'''
theorem skelreach_iff (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 1 ≤ r) (A β : Fin 2 → ℕ → ZMod p)
    (g o : Fin 2 → ZMod p) :
    (∃ (inf : Fin (r + 2)) (x : Fin (r + 2) → ZMod p), PlacesOK inf x ∧ ∀ k, 1 ≤ k →
      ∃ (L : (c : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - skDepth r k c))
          (Fin ((r + 2) * k + r - skDepth r k c)) (ZMod p))
        (U : (d : Fin (r + 2)) → Matrix (Fin (skDepth r k d)) (Fin (skDepth r k d)) (ZMod p))
        (Φ : (c d : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - skDepth r k c))
          (Fin (skDepth r k d)) (ZMod p)),
        (∀ c, IsLTU (L c)) ∧ (∀ d, IsLTU (U d)) ∧
        (∀ c d, c ≠ d → Φ c d =
          L c * frameGraphK (ZMod p) ((r + 2) * k + r) (skDepth r k) inf x c d * U d) ∧
        ∀ i : Fin 2, ∀ d : Fin (r + 2), ∀ l : Fin (skDepth r k d),
          ent (Φ (Fin.natAdd r i) d) 0 l = sk2Coef r k A β g o i (d : ℕ) (l : ℕ)) ↔
      (∀ i d, d < r → A i d ≠ 0) ∧
        (∀ d d', d < r → d' < r → d ≠ d' → A 0 d * A 1 d' - A 0 d' * A 1 d ≠ 0) ∧
        (∀ i, g i ≠ 0) ∧ (∀ d, d < r → A 0 d * β 1 d - β 0 d * A 1 d ≠ 0) := by
  sorry
''')

_new('S16′', 'Z3NetF.skelreach_nec', 'Skeleton', 'cor:skelreach', 'Z3NetF', _SK, r'''
/-- **`cor:skelreach`, necessity for each single `k ≥ 1`**: every graph form with the skeleton depths
`(k+1, …, k+1, k, k)` whose two skeleton digits are those of `prop:skelcomp`(iii) (`sk2Coef`) and which is a digital
`(0, sk+s-2, s)`-net over `𝔽_p` (`s = r + 2`) satisfies (N1)–(N3): every entry and every `2 × 2` minor of `A` is nonzero,
`g_1, g_2 ≠ 0`, and `det[A_{·d}, β_{·d}] ≠ 0` for every full coordinate `x_d`. -/
''', r'''
theorem skelreach_nec (p : ℕ) [Fact p.Prime] (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (A β : Fin 2 → ℕ → ZMod p) (g o : Fin 2 → ZMod p)
    (Φ : (c d : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - skDepth r k c)) (Fin (skDepth r k d)) (ZMod p))
    (hΦ : ∀ (i : Fin 2) (d : Fin (r + 2)) (l : Fin (skDepth r k d)),
      ent (Φ (Fin.natAdd r i) d) 0 l = sk2Coef r k A β g o i (d : ℕ) (l : ℕ))
    (hnet : IsNet0 (r + 2) p ((r + 2) * k + r)
      (digPoint p ((r + 2) * k + r) (graphGenK (m := (r + 2) * k + r) (skDepth r k) Φ))) :
    (∀ i d, d < r → A i d ≠ 0) ∧
      (∀ d d', d < r → d' < r → d ≠ d' → A 0 d * A 1 d' - A 0 d' * A 1 d ≠ 0) ∧
      (∀ i, g i ≠ 0) ∧ (∀ d, d < r → A 0 d * β 1 d - β 0 d * A 1 d ≠ 0) := by
  sorry
''')

# `rem:wshift` (rev 15.10): the two-coset net `𝒯_p` under digital shifts with equal second digits on `y` and `z`
# (`QUNetsM3/TCShift.lean`), and the wraps of the digit `2ζ + 1` for the shift `t ≡ 2t′ + 1` of `𝒲_p`
# (`QUNetsM3/WWrapOne.lean`). `rem:wshift` sits in `sec:wnet`, so both go to `Large` (with `W_wrap`, `TC_sep`).

_new('S16′', 'QUNetsM3.TC_shift', 'Large', 'rem:wshift', 'QUNetsM3', _WO, r'''
/-- **`rem:wshift`, the net `𝒯_p`**: let `p ≥ 41` be prime and shift `𝒯_p` (`prop:twocoset`) digit by digit by `τ`
(`def:dshift`; any first and third shift digits, any second shift digit of `x`). If the second shift digits agree on the
digit shared by `y` and `z`, `τ_{y,2} = τ_{z,2}`, the bound of `prop:twocoset` (2) holds for the shifted net: every pair
of distinct points and every torus translate have squared distance `≥ (p²(√(33/32 − 41/(16p)) − √3/p))²` at integer
scale `p³`. -/
''', r'''
theorem TC_shift (p : ℕ) (hp : p.Prime) (hp41 : 41 ≤ p) (τ : Fin 3 → Fin 3 → ZMod p) (hyz : τ 1 1 = τ 2 1)
    (x x' : ℕ) (hx : x < p ^ 3) (hx' : x' < p ^ 3) (hne : x ≠ x') (t : Fin 3 → ℤ) :
    ((p : ℝ) ^ 2 * (Real.sqrt (33 / 32 - 41 / (16 * (p : ℝ))) - Real.sqrt 3 / p)) ^ 2 ≤
      (sepSqGS p (genTC p) τ x x' t : ℝ) := by
  sorry
''')

_new('S16′', 'QUNetsM3.W_wrap_one', 'Large', 'rem:wshift', 'QUNetsM3', _WO, r'''
/-- **`rem:wshift`, the digit `2ζ + 1`** (the shift `t ≡ 2t′ + 1` of `𝒲_p`): let `p ≥ 5` be prime, `u ∈ 𝔽_p³` (Lean:
any `u`), `ζ(n) = u·n mod p`, and for `E ∈ ℤ³` and `n' = n + E` let `Δζ = ζ(n') − ζ(n)`, `σ = u·E mod p`. The digit
`2ζ + 1` wraps (`2ζ + 1 ≥ p`) if and only if `ζ ≥ h`, and with `ω = [2ζ(n') + 1 ≥ p] − [2ζ(n) + 1 ≥ p]`, as `n` runs
over `𝔽_p³` the pairs `(Δζ, ω)` that occur are exactly those of `lem:wwrap` (`WrapAllowed`): `(0, 0)` if `σ = 0`; if
`σ ≠ 0`, for each `Δζ ∈ {σ, σ − p}` the pair `(Δζ, sgn Δζ)`, and also `(Δζ, 0)` if `|Δζ| ≤ h`. -/
''', r'''
theorem W_wrap_one (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (u : Fin 3 → ZMod p) (E : Fin 3 → ℤ) (d k : ℤ) :
    (∀ z : ℕ, z < p → (p ≤ 2 * z + 1 ↔ hW p ≤ z)) ∧
    ((∃ n : Fin 3 → ZMod p, dZetaW p u n E = d ∧
        (if p ≤ 2 * zetaW p u (n + fun c => (E c : ZMod p)) + 1 then (1 : ℤ) else 0) -
          (if p ≤ 2 * zetaW p u n + 1 then (1 : ℤ) else 0) = k) ↔
      WrapAllowed p (sigmaW p u E) d k) := by
  sorry
''')

# S16′ (2/2): printed claims found missing by the read-only audit of rev 15.10: `thm:col`(1) (the integer box minors of
# the boxes with depth 3), `lem:drift`(2) (the excesses of a cycle), `cor:dgs`(4) (`ρ = ⌊p^{1/s}⌋`), `rem:accounting`
# (the two-sided expansion of `LB₂(p)` under (Gap)). Proofs `Z3Net/ColZMinor.lean`, `Z3Net/DGSRho.lean`,
# `Z3Net/AcctTwo.lean`.

_new('S16′', 'Z3NetC.col_boxMinor_int', 'Dim3', 'thm:col', 'Z3NetC', _CO, r'''
/-- **`thm:col`(1)**, the parenthetical "as integers the minors of the boxes with depth `3` are `a_x + a_y` and `±a_z`":
the integer generator matrices of `𝒞_q` (rows `e_c`, `a = (q𝟏 + w)/3`, `b = (-1, 1, 0)`, `def:col`) reduce to
`colGen q` modulo `q`, and the box with depth `3` on `c` (all three rows of coordinate `c`) has the integer determinant
`a_x + a_y` for `c = z` and `-a_z` for `c = x, y` (up to the sign of the cofactor expansion along `e_c`, the `2 × 2` minor
of the rows `a`, `b` on the two columns other than `c`: `-a_z`, `a_z`, `a_x + a_y` for `c = x, y, z`). Every `q`. -/
''', r'''
theorem col_boxMinor_int (q : ℕ) :
    (∀ c : Fin 3, (Matrix.of ![(Pi.single c 1 : Fin 3 → ℤ), fun d => colA q (wCol q) d, ellCol]).map
        (Int.cast : ℤ → ZMod q) = colGen q c) ∧
    ∀ c : Fin 3, (boxMatrix (fun c : Fin 3 =>
        Matrix.of ![(Pi.single c 1 : Fin 3 → ℤ), fun d => colA q (wCol q) d, ellCol]) (Pi.single c 3)).det =
      if c = 2 then colA q (wCol q) 0 + colA q (wCol q) 1 else -colA q (wCol q) 2 := by
  sorry
''')

_new('S16′', 'Z3NetC.drift_excess', 'Deficit', 'lem:drift', 'Z3NetC', _CO, r'''
/-- **`lem:drift`(2)**, "the excesses of the cycle are `ε_i` and `ε_i − q`": for the digital column net with the digits
`n_c`, `a·n`, `ℓ·n` (`a = (q𝟏 + w)/3`), if `|ε_i| < ½q²` and `|ε_i − q| < ½q²` (in thirds: `2|q w_i + 3 r_i| < 3q²` and
`2|q w_i + 3 r_i − 3q| < 3q²`), or for instance `|w_i| ≤ 2` and `q ≥ 4`, then the excess of the step at every cell `n`
along `e_i` is `ε_i` if the third digit does not wrap (`j(n) + r_i < q`) and `ε_i − q` if it wraps (Lean: three times
the excess, `excess3`, is `q w_i + 3 r_i` resp. `q w_i + 3 r_i − 3q`; `r_i` the residue of `ℓ_i`). -/
''', r'''
theorem drift_excess {q : ℕ} [NeZero q] (w ℓ : Fin 3 → ℤ) (hw3 : ∀ c, (3 : ℤ) ∣ q + w c) (i : Fin 3)
    (hR : (2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val| < 3 * (q : ℤ) ^ 2 ∧
      2 * |(q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val - 3 * q| < 3 * (q : ℤ) ^ 2) ∨
      (|w i| ≤ 2 ∧ 4 ≤ q))
    (n : Fin 3 → ZMod q) :
    excess3 q (colStep q (colPhi q w ℓ) i n) =
      (q : ℤ) * w i + 3 * (((ℓ i : ℤ) : ZMod q)).val -
        (if (colJ q ℓ n).val + (((ℓ i : ℤ) : ZMod q)).val < q then (0 : ℤ) else 3 * q) := by
  sorry
''')

_new('S16′', 'Z3NetDGS.dgs_S1_floor', 'DGS', 'cor:dgs', 'Z3NetDGS', _DO, r'''
/-- **`cor:dgs`(4)**, the parenthetical "for `ρ = ⌊p^{1/s}⌋` this holds when `p > (⌈√s⌉+1)^s`": for `s ≥ 3`, a prime
`p > (⌈√s⌉ + 1)^s` and `ρ = ⌊p^{1/s}⌋`, one has `ρ ≥ ⌈√s⌉ + 1 ≥ 2`, `ρ^s < p` (the hypotheses of `thm:S1`) and
`(ρ − 1)² ≥ s`; hence the nets `𝒮¹_{k,p,ρ}` (`m = sk + s − 1`) are `(k+1)`-separated and toroidally `(k+1)`-separated,
for every digital shift. -/
''', r'''
theorem dgs_S1_floor (s p k ρ : ℕ) [NeZero p] (hs : 3 ≤ s) (hp : p.Prime)
    (hρ : ρ = ⌊(p : ℝ) ^ ((1 : ℝ) / s)⌋₊) (hps : (⌈Real.sqrt s⌉₊ + 1) ^ s < p)
    (τ : Fin s → Fin (s * k + (s - 1)) → ZMod p) :
    ⌈Real.sqrt s⌉₊ + 1 ≤ ρ ∧ 2 ≤ ρ ∧ ρ ^ s < p ∧ s ≤ (ρ - 1) ^ 2 ∧
      IsKSep p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) ∧
      IsKSepTor p (k + 1) (ptSet p (Z3NetF.digPointShift p (s * k + (s - 1)) (Z3NetS1.S1gen s p k ρ) τ)) := by
  sorry
''')

_new('S16′', 'Z3NetHL.acct_LB2', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`rem:accounting`, the two-sided expansion of the printed proof**: let `F₀ = F2/2 ∈ (½ + ℤ)^{5×5}` (`F2` odd)
satisfy (Gap) (`LamHyp`), and let `D₁` be any integer matrix. Then `LB₂(p)` of `lem:R2` (`LB2R`) satisfies
`LB₂(p) = (√5/2)(1 − 2dj(F₀, D₁)/(5p)) + O(p⁻²)`: there are `C` and `P` with
`|LB₂(p) − (√5/2)(1 − 2dj/(5p))| ≤ C/p²` for every `p ≥ P` (`dj2 = 2dj`; `det F₀ ≠ 0` is not needed). -/
''', r'''
theorem acct_LB2 (F2 D1 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (hΛ : LamHyp F2) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, P ≤ p →
      |LB2R p F2 D1 - Real.sqrt 5 / 2 * (1 - (dj2 F2 D1 : ℝ) / (5 * p))| ≤ C / (p : ℝ) ^ 2 := by
  sorry
''')

# S16′ (3/n): `rem:shiftparity` (sec:base23), parts (i)–(iii); the counts of resolutions where `v°_L` vanishes stay
# script-checked, (iv) is `b23_vcirc` + `base23_everyshift`. Definitions `Z3Net/B23ParityDefs.lean`, proofs
# `Z3Net/B23Parity.lean`.
EXTRA_MODS['Base23'] = EXTRA_MODS.get('Base23', []) + ['Z3Net.B23ParityDefs']

_new('S16′', 'Z3NetB23.shiftparity_parity', 'Base23', 'rem:shiftparity', 'Z3NetB23', _B23, r'''
/-- **`rem:shiftparity`(i), parity**: if the resolution `L ≥ 1` is even and the every-shift certificate vanishes,
`v°_L = 0`, then `v°_{L+3} = 0` for every lift `P_{L+3}` of `P_L` (`def:lift`; generator matrices `liftGen C s_A s_B`,
for any `s_A, s_B`, admissible or not; `v°` does not depend on the shift). -/
''', r'''
theorem shiftparity_parity {b : ℕ} [Fact b.Prime] {L : ℕ} (hL : 1 ≤ L) (hev : Even L)
    (C : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) (h0 : vcirc b L C = 0) (sA sB : Fin 3 → Fin L → ZMod b) :
    vcirc b (L + 3) (liftGen C sA sB) = 0 := by
  sorry
''')

_new('S16′', 'Z3NetB23.shiftparity_first_even', 'Base23', 'rem:shiftparity', 'Z3NetB23', _B23, r'''
/-- **`rem:shiftparity`(i), contrapositive form**: a certificate can first become positive only at an even
resolution: if `v°_L = 0` (`L ≥ 1`) and `v°_{L+3} > 0` for a lift `P_{L+3}` of `P_L` (any `s_A, s_B`), then `L + 3` is
even. -/
''', r'''
theorem shiftparity_first_even {b : ℕ} [Fact b.Prime] {L : ℕ} (hL : 1 ≤ L)
    (C : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) (h0 : vcirc b L C = 0) (sA sB : Fin 3 → Fin L → ZMod b)
    (hpos : 0 < vcirc b (L + 3) (liftGen C sA sB)) : Even (L + 3) := by
  sorry
''')

_new('S16′', 'Z3NetB23.shiftparity_dichotomy', 'Base23', 'rem:shiftparity', 'Z3NetB23', _B23, r'''
/-- **`rem:shiftparity`(ii), dichotomy**: if `v°_L = 0` (`L ≥ 1`), then along every lift chain from `P_L` (generator
matrices `C₀`, any shift `σ₀`, any depth parameters `D`, any shifts `s_A, s_B`), every level `m` of the chain
(`m = L + 3j`, the resolutions `m ≥ L` of the class) has `min_τ δ(P_m ⊕ τ) N^{1/3} < 2√3 b^{⌈L/2⌉ − 2L/3}`: there are a
digital shift `τ` of depth `m` and two distinct indices whose toroidal distance is at most their Euclidean distance,
which is `< 2√3 · b^(L − ⌊L/2⌋) · (b^L)^{−2/3} · N^{−1/3}`, `N = b^m` (real form; distances in `[0,1)³`). -/
''', r'''
theorem shiftparity_dichotomy {b : ℕ} [Fact b.Prime] {L : ℕ} (hL : 1 ≤ L) {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)}
    {σ₀ : Fin 3 → Fin L → ZMod b} {D : ℕ → ℕ} {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    {σ : Fin 3 → Fin m → ZMod b} (h0 : vcirc b L C₀ = 0) (h : LiftChain b L C₀ σ₀ D m C σ) :
    ∃ τ : Fin 3 → Fin m → ZMod b, ∃ v w : Fin m → ZMod b, v ≠ w ∧
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) ≤
        Real.sqrt (∑ c, (((Z3NetF.digPointShift b m C τ v c : ℝ) - Z3NetF.digPointShift b m C τ w c) /
          (b : ℝ) ^ m) ^ 2) ∧
      Real.sqrt (∑ c, (((Z3NetF.digPointShift b m C τ v c : ℝ) - Z3NetF.digPointShift b m C τ w c) /
          (b : ℝ) ^ m) ^ 2) <
        2 * Real.sqrt 3 * (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ)) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) := by
  sorry
''')

_new('S16′', 'Z3NetB23.shiftparity_floor_iff', 'Base23', 'rem:shiftparity', 'Z3NetB23', _B23, r'''
/-- **`rem:shiftparity`(iii), a floor for every shift exists iff a certificate is positive**: for an infinite chain of
lifts from a resolution `m₀ ≥ 1` (`IsLiftSeq`: generator matrices `G m`, shifts `S m` at the levels `m = m₀ + 3k`)
that is frozen from every resolution (`FrozenFromEvery`: the hypothesis of `lem:liftsep` from every level), there is a
floor `κ > 0` with `δ(P_m ⊕ τ) N^{1/3} ≥ κ` (toroidal) for every digital shift `τ` and every level `m` of the chain
from some level `M` on, if and only if `v°_L > 0` at some level `L` of the chain. -/
''', r'''
theorem shiftparity_floor_iff {b : ℕ} [Fact b.Prime] {m₀ : ℕ} (hm₀ : 1 ≤ m₀) {D : ℕ → ℕ}
    {G : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {S : (m : ℕ) → Fin 3 → Fin m → ZMod b}
    (hseq : IsLiftSeq b m₀ D G S) (hfz : FrozenFromEvery m₀ D) :
    (∃ κ : ℝ, 0 < κ ∧ ∃ M, ∀ m, M ≤ m → m₀ ≤ m → m % 3 = m₀ % 3 → ∀ (τ : Fin 3 → Fin m → ZMod b)
      (v w : Fin m → ZMod b), v ≠ w →
        κ * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤ Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m)
          ((Z3NetF.digPointShift b m (G m) τ v c : ℤ) - Z3NetF.digPointShift b m (G m) τ w c) : ℝ) /
            (b : ℝ) ^ m) ^ 2)) ↔
      ∃ L, m₀ ≤ L ∧ L % 3 = m₀ % 3 ∧ 0 < vcirc b L (G L) := by
  sorry
''')

_new('S16′', 'Z3NetB23.shiftparity_tendsto', 'Base23', 'rem:shiftparity', 'Z3NetB23', _B23, r'''
/-- **`rem:shiftparity`(iii), vanishing at infinitely many resolutions**: for an infinite chain of lifts from
`m₀ ≥ 1` (any depth parameters), if `v°_L = 0` at arbitrarily large levels `L` of the chain, the every-shift
separation tends to `0`: for every `ε > 0` there is `M` such that every level `m ≥ M` of the chain has a digital shift
`τ` and two distinct indices at toroidal distance `≤` Euclidean distance `< ε N^{−1/3}`, `N = b^m`; i.e.
`min_τ δ(P_m ⊕ τ) N^{1/3} → 0`. -/
''', r'''
theorem shiftparity_tendsto {b : ℕ} [Fact b.Prime] {m₀ : ℕ} (hm₀ : 1 ≤ m₀) {D : ℕ → ℕ}
    {G : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {S : (m : ℕ) → Fin 3 → Fin m → ZMod b}
    (hseq : IsLiftSeq b m₀ D G S)
    (hinf : ∀ M, ∃ L, M ≤ L ∧ m₀ ≤ L ∧ L % 3 = m₀ % 3 ∧ vcirc b L (G L) = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ M, ∀ m, M ≤ m → m₀ ≤ m → m % 3 = m₀ % 3 → ∃ τ : Fin 3 → Fin m → ZMod b, ∃ v w : Fin m → ZMod b, v ≠ w ∧
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m (G m) τ v c : ℤ) -
        Z3NetF.digPointShift b m (G m) τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) ≤
        Real.sqrt (∑ c, (((Z3NetF.digPointShift b m (G m) τ v c : ℝ) - Z3NetF.digPointShift b m (G m) τ w c) /
          (b : ℝ) ^ m) ^ 2) ∧
      Real.sqrt (∑ c, (((Z3NetF.digPointShift b m (G m) τ v c : ℝ) - Z3NetF.digPointShift b m (G m) τ w c) /
          (b : ℝ) ^ m) ^ 2) < ε * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) := by
  sorry
''')

# S16′ (3/n): `rem:accounting`, the sentence "In the same way Proposition prop:Hk(1) has LB = …" of the printed proof.
# Proof `Z3Net/AcctHk.lean`.
_new('S16′', 'Z3NetHL.acct_LBHk', _AC[0], _AC[1], 'Z3NetHL', _HO, r'''
/-- **`rem:accounting`, the expansion of `LB` of `prop:Hk`(1)** ("in the same way `prop:Hk`(1) has
`LB = (√5/2)(1 − 2(dr + 5)/(5p)) + O(p⁻²)`"): let `F₀ = F2/2 ∈ (½ + ℤ)^{5×5}` (`F2` odd) satisfy (Gap) (`LamHyp`).
Then `LB(p)` of `prop:Hk`(1) at `s = 5`, `k = 1` (`L = 1`, no carries: `min(2, min_{0 ≠ E ∈ {-2,…,2}⁵} |b|/p)` with
`2b_c = bOpt2 p F₀ E 0 c`) satisfies `|LB(p) − (√5/2)(1 − 2(dr(F₀) + 5)/(5p))| ≤ C/p²` for every `p ≥ P`, for some
`C`, `P` (`drift2 = 2dr`, so `2(dr + 5) = drift2 + 10`; `p` any integer `≥ P`; `det F₀ ≠ 0` is not needed). -/
''', r'''
theorem acct_LBHk (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (hΛ : LamHyp F2) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, P ≤ p →
      |min 2 (⨅ E : halfSteps 5,
          Real.sqrt (∑ c, ((bOpt2 p (fun _ => F2) (E : Fin 5 → ℤ) (fun _ => 0) c : ℤ) : ℝ) ^ 2) / (2 * p)) -
        Real.sqrt 5 / 2 * (1 - ((drift2 F2 + 10 : ℤ) : ℝ) / (5 * p))| ≤ C / (p : ℝ) ^ 2 := by
  sorry
''')

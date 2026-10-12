/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.FSepShift
public import Z3Net.FDsep

@[expose] public section

/-!
# V14 stage S10′: `prop:shift` for `lem:Ss` and `prop:D`

`lem:shift` for the depths `(k, …, k)`: re-indexed by the cells `n = v + T` (`T = TcK τ`, the index
whose cells are the cell digits of `τ`), the shifted graph form is the affine graph form with the
constant `γ = gammaK Φ τ` on the offset digits, which vanishes on the cell digits (`gammaK_cell`). So
`lem:Ss` holds verbatim, with the same bound, for every digitally shifted net (`Ss_coord_shift_core`,
`Ss_sep_shift_core`), and with it `prop:D` applied to `𝒫^F_{k,q}` (`D_sep_shift_core`).
-/

namespace Z3NetF.Proofs

open Finset Matrix

noncomputable section

section shift

variable {s q k : ℕ} [NeZero q]

/-- The index whose cell digits are those of the shift `τ` (level `l` of the cell of coordinate `c` is
digit `l` of `τ_c`). -/
def TcK (τ : Fin s → Fin (s * k) → ZMod q) : Fin (s * k) → ZMod q := fun j =>
  τ ⟨(j : ℕ) / k, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm s k))⟩
    ⟨(j : ℕ) % k, lt_of_le_of_lt (Nat.mod_le _ _) j.isLt⟩

omit [NeZero q] in
lemma TcK_ix (τ : Fin s → Fin (s * k) → ZMod q) (c : Fin s) (l : Fin k) :
    TcK τ (Z3NetU.Proofs.ix k c l) = τ c ⟨l, lt_of_lt_of_le l.isLt (Z3NetU.Proofs.k_le_sk k c)⟩ := by
  unfold TcK
  congr 1
  · ext; simp [Z3NetU.Proofs.ix_div]
  · ext; simp [Z3NetU.Proofs.ix_mod]

/-- The constant of the affine graph form: `γ_c = τ_c - G_c T`. -/
def gammaK (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (τ : Fin s → Fin (s * k) → ZMod q) : Fin s → Fin (s * k) → ZMod q :=
  fun c => τ c - Z3NetU.graphGen s k Φ c *ᵥ TcK τ

omit [NeZero q] in
lemma gammaK_cell (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (τ : Fin s → Fin (s * k) → ZMod q) : ∀ c (i : Fin (s * k)), (i : ℕ) < k → gammaK Φ τ c i = 0 := by
  intro c i hi
  obtain ⟨i, hi'⟩ := i
  unfold gammaK
  rw [Pi.sub_apply, Z3NetU.Proofs.graphGen_cell k Φ c (TcK τ) i hi, TcK_ix, sub_self]

/-- **`lem:shift`** for the depths `(k, …, k)`: the shifted graph form is the affine graph form with the
constant `gammaK Φ τ`, re-indexed by `v ↦ v + TcK τ`. -/
lemma shift_affine (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (τ : Fin s → Fin (s * k) → ZMod q) (v : Fin (s * k) → ZMod q) :
    Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) τ v =
      Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) (gammaK Φ τ)
        (v + TcK τ) := by
  rw [digPointShift_reindex _ τ (TcK τ) v, graphGenK_const]
  rfl

/-- **`prop:shift`**, `lem:Ss` (the coordinate bounds) for every digitally shifted net. -/
theorem Ss_coord_shift_core {L : ℕ} (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (F : ℕ → Fin s → Fin s → ℤ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ) (he : ∀ d, -1 ≤ e d ∧ e d ≤ 1)
    (hcell : ∀ d, ((Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) τ w d /
        q ^ (s * k - k) : ℕ) : ℤ) = ((Z3NetF.digPointShift q (s * k)
          (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) τ v d / q ^ (s * k - k) : ℕ) + e d) % (q ^ k : ℕ))
    (i : Fin s) :
    Z3NetF.bval q F L e (fun d => Z3NetF.carryLen q k (Z3NetF.digPointShift q (s * k)
        (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) τ v d / q ^ (s * k - k)) (e d)) i *
          (q ^ (s * k - k) : ℕ) ≤
      (q : ℤ) * |e i * (q ^ (s * k - k) : ℕ) +
        ((Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) τ w i %
          q ^ (s * k - k) : ℕ) : ℤ) -
        ((Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) τ v i %
          q ^ (s * k - k) : ℕ) : ℤ)| := by
  simp only [shift_affine Φ τ] at hcell ⊢
  exact Ss_coord_coreA s q k Φ (gammaK Φ τ) (gammaK_cell Φ τ) F L hs hq hk hL hLk h1 h2
    (v + TcK τ) (w + TcK τ) e he hcell i

/-- **`prop:shift`**, `lem:Ss` (the separation) verbatim, with the same bound, for every digitally
shifted net. -/
theorem Ss_sep_shift_core {L : ℕ} (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (F : ℕ → Fin s → Fin s → ℤ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, Z3NetF.IsConfig k e j → B ≤ ∑ i, Z3NetF.bval q F L e j i ^ 2)
    (τ : Fin s → Fin (s * k) → ZMod q) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ 2 *
      (Z3NetF.torusDist2 (q ^ (s * k))
        (Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) τ v)
        (Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) τ w) : ℤ) := by
  rw [shift_affine Φ τ v, shift_affine Φ τ w]
  exact Ss_sep_coreA s q k Φ (gammaK Φ τ) (gammaK_cell Φ τ) F L hs hq hk hL hLk h1 h2 B hBq hB
    (v + TcK τ) (w + TcK τ) (fun h => hvw (add_right_cancel h))

/-- **`prop:shift`**, `prop:D` applied to `𝒫^F_{k,q}`, for every digital shift. -/
theorem D_sep_shift_core {R : Type*} [CommRing R] {a : ℕ} (hs : 2 ≤ s) (ψ : R →+* ZMod q)
    (hk : 1 ≤ k) (inf : Fin s) (x : Fin s → R) (hx : Z3NetF.PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : Z3NetF.BetaRel inf x (fun n c d => (F n c d : R)) lam β)
    (α : Fin s → ℕ) (h0 : ∀ c, F 0 c c = -(α c : ℤ)) (hdiag : ∀ n c, 1 ≤ n → F n c c = 0)
    (hdom : ∀ c, ∑ d ∈ univ.filter (fun d => d ≠ c),
      (range (s - 1)).sup (fun j => (Z3NetF.Msum F j c d).natAbs) ≤ α c)
    (ha : ∀ c, α c ≤ a) (hq : 5 * a + 4 ≤ q) (τ : Fin s → Fin (s * k) → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - a) ^ 2 ≤ (q : ℤ) ^ 2 *
      (Z3NetF.torusDist2 (q ^ (s * k))
        (Z3NetF.digPointShift q (s * k)
          (fun c => (Z3NetF.PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) τ v)
        (Z3NetF.digPointShift q (s * k)
          (fun c => (Z3NetF.PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) τ w) : ℤ) := by
  rw [PGen_map_eq]
  obtain ⟨h1, h2⟩ := PGen_H1H2 ψ k inf x hx F lam Ur β hres hβ
  set L := min k (s - 1) with hLdef
  have hL : 1 ≤ L := by omega
  have hLk : L ≤ k := min_le_left _ _
  have hLs : L ≤ s - 1 := min_le_right _ _
  obtain ⟨hBq, hB⟩ := D_LB_core F L α a hL hLs h0 hdiag hdom ha q k hq
  exact Ss_sep_shift_core hs (by omega) hk hL hLk F _ h1 h2 _ hBq hB τ v w hvw

end shift

end

end Z3NetF.Proofs

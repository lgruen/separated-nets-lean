/-
`rem:projlines`, the remedy for `lem:Ss` and `prop:D`: the separation bounds hold verbatim after rescaling an offset row
`r ≥ k + 1` (the rescaled point set is a graph form with the same (H1), (H2)). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ProjLines
public import Z3Net.FDsep
public import Z3Net.ThmAShift

@[expose] public section

/-!
# `rem:projlines`: `lem:Ss` and `prop:D` after rescaling one row (V14 stage S13′)

Rescaling row `r ≥ k + 1` of every generator matrix of a graph form with depths `(k, …, k)` gives the graph form whose
offset row `r - k ≥ 1` of every block `Φ_cd` is rescaled by `ρ_c` (`rowScale_graphGenK`). That keeps (H1) (row `0`) and
(H2) (the rescaled diagonal rows stay `0`), so `lem:Ss` (`Ss_sep_core`) and `prop:D` (`D_LB_core`) apply unchanged;
`A_sep_rowScale_core` is the lower bound of `thm:A`(2) for the rescaled net (through `prop:D`, as `A_sep_core`).
-/

namespace Z3NetF.Proofs

open Finset Matrix

noncomputable section

/-- The blocks with offset row `r - k` rescaled by `ρ_c`. -/
def PhiScale {R : Type*} [Mul R] {s k : ℕ} (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) R) (r : ℕ)
    (ρ : Fin s → R) : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) R :=
  fun c d i l => if k + (i : ℕ) = r then ρ c * Φ c d i l else Φ c d i l

lemma H1_scale {s q k L : ℕ} (F : ℕ → Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q)) {r : ℕ} (hr : k + 1 ≤ r) (ρ : Fin s → ZMod q)
    (h1 : Z3NetF.H1 F L Φ) : Z3NetF.H1 F L (PhiScale Φ r ρ) := by
  intro c d i hi j
  simp only [PhiScale]
  rw [if_neg (by omega)]
  exact h1 c d i hi j

lemma H2_scale {s q k : ℕ} (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q)) (r : ℕ)
    (ρ : Fin s → ZMod q) (h2 : Z3NetF.H2 Φ) : Z3NetF.H2 (PhiScale Φ r ρ) := by
  intro c i hi j
  simp only [PhiScale]
  rw [h2 c i hi j]
  split_ifs <;> simp

/-- **`lem:Ss` after rescaling** row `r ≥ k + 1` by arbitrary `ρ_c`: the conclusion of `Ss_sep` holds verbatim. -/
theorem Ss_sep_rowScale_core {s q k L : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hLk : L ≤ k) (F : ℕ → Fin s → Fin s → ℤ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, Z3NetF.IsConfig k e j → B ≤ ∑ i, Z3NetF.bval q F L e j i ^ 2) {r : ℕ} (hr : k + 1 ≤ r)
    (ρ : Fin s → ZMod q) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ 2 *
      (Z3NetF.torusDist2 (q ^ (s * k))
        (Z3NetF.digPoint q (s * k) (Z3NetF.rowScale (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) r ρ) v)
        (Z3NetF.digPoint q (s * k) (Z3NetF.rowScale (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) r ρ) w) :
          ℤ) := by
  rw [rowScale_graphGenK Φ (by omega) ρ]
  exact Ss_sep_core s q k (PhiScale Φ r ρ) F L hs hq hk hL hLk (H1_scale F Φ hr ρ h1) (H2_scale Φ r ρ h2)
    B hBq hB v w hvw

/-- **`prop:D` for `𝒫^F_{k,q}` after rescaling** row `r ≥ k + 1` by arbitrary `ρ_c`: the conclusion of `D_sep`. -/
theorem D_sep_rowScale_core {R : Type*} [CommRing R] {s q a : ℕ} [NeZero q] (hs : 2 ≤ s) (ψ : R →+* ZMod q)
    (k : ℕ) (hk : 1 ≤ k) (inf : Fin s) (x : Fin s → R) (hx : Z3NetF.PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : Z3NetF.BetaRel inf x (fun n c d => (F n c d : R)) lam β)
    (α : Fin s → ℕ) (h0 : ∀ c, F 0 c c = -(α c : ℤ)) (hdiag : ∀ n c, 1 ≤ n → F n c c = 0)
    (hdom : ∀ c, ∑ d ∈ univ.filter (fun d => d ≠ c),
      (range (s - 1)).sup (fun j => (Z3NetF.Msum F j c d).natAbs) ≤ α c)
    (ha : ∀ c, α c ≤ a) (hq : 5 * a + 4 ≤ q) {r : ℕ} (hr : k + 1 ≤ r) (ρ : Fin s → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - a) ^ 2 ≤ (q : ℤ) ^ 2 *
      (Z3NetF.torusDist2 (q ^ (s * k))
        (Z3NetF.digPoint q (s * k) (Z3NetF.rowScale
          (fun c => (Z3NetF.PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) r ρ) v)
        (Z3NetF.digPoint q (s * k) (Z3NetF.rowScale
          (fun c => (Z3NetF.PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) r ρ) w) : ℤ) := by
  rw [PGen_map_eq, rowScale_graphGenK _ (by omega) ρ]
  obtain ⟨h1, h2⟩ := PGen_H1H2 ψ k inf x hx F lam Ur β hres hβ
  set L := min k (s - 1) with hLdef
  have hL : 1 ≤ L := by omega
  have hLk : L ≤ k := min_le_left _ _
  have hLs : L ≤ s - 1 := min_le_right _ _
  obtain ⟨hBq, hB⟩ := D_LB_core F L α a hL hLs h0 hdiag hdom ha q k hq
  exact Ss_sep_core s q k (PhiScale _ r ρ) F L hs (by omega) hk hL hLk (H1_scale F _ hr ρ h1)
    (H2_scale _ r ρ h2) _ hBq hB v w hvw

end

end Z3NetF.Proofs

namespace Z3NetA.Proofs

open Finset Z3NetF Z3NetA

/-- **`thm:A`(2) after rescaling** row `r ≥ k + 1` of the generator matrices of `𝒫^{U*_s}_{k,q}` by arbitrary `ρ_c`. -/
theorem A_sep_rowScale_core (s q k : ℕ) [NeZero s] (hs : 3 ≤ s) (hq : AdmBase s q)
    (hqa : 5 * aStar s + 4 ≤ q) (hk : 1 ≤ k) {r : ℕ} (hr : k + 1 ≤ r) (ρ : Fin s → ZMod q)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - aStar s) ^ 2 ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (s * k)) (digPoint q (s * k) (rowScale (AGen s q k) r ρ) v)
        (digPoint q (s * k) (rowScale (AGen s q k) r ρ) w) : ℤ) := by
  have : NeZero q := ⟨by have := hq.1; omega⟩
  obtain ⟨ψ⟩ := (A_hom_core hs hq).1
  rw [AGen_eq k ψ]
  exact Z3NetF.Proofs.D_sep_rowScale_core (by omega) ψ k hk (0 : Fin s) placeA (placesOK (by omega))
    (UstarF s) 1 (UrS s) (betaS s) (Ustar_data_core hs).1 (Ustar_data_core hs).2 alphaS
    (fun c => (Ustar_diag_core c).1) (fun n c hn => (Ustar_diag_core c).2 n hn)
    (fun c => (Ustar_dominant_core hs c).1.le) (fun c => (Ustar_dominant_core hs c).2) hqa hr ρ v w hvw

end Z3NetA.Proofs

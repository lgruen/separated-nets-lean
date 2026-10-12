module
public import Z3Net.FSep

@[expose] public section

/-!
# Entry F, part 14: `prop:D` applied to `𝒫^F_{k,q}` (the step of `thm:U` for an arbitrary
dominant reachable design)

(H1) holds by `prop:Gs` and `def:Ns` with `L = min(k, s-1)` levels, (H2) by `def:Ns`; then
`lem:Ss` and `prop:D`. Every `k ≥ 1` (V14 stage S2: `lem:Ss` at `k = 1`; at `k = 1`, `L = 1`).
-/

namespace Z3NetF.Proofs

open Finset Matrix

noncomputable section

lemma graphGenK_map {R S : Type*} [CommRing R] [CommRing S] {s m : ℕ} (f : R →+* S) (K : Fin s → ℕ)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R) (c : Fin s) :
    (Z3NetF.graphGenK K Φ c).map f = Z3NetF.graphGenK K (fun c d => (Φ c d).map f) c := by
  ext i j
  simp only [Matrix.map_apply, Z3NetF.graphGenK]
  split_ifs <;> simp

/-- (H1) with `L = min(k, s-1)` levels and (H2) for the graph form of `𝒫^F_{k,q}` (`prop:Gs`,
`def:Ns`), every `k`. -/
theorem PGen_H1H2 {R : Type*} [CommRing R] {s q : ℕ} (ψ : R →+* ZMod q)
    (k : ℕ) (inf : Fin s) (x : Fin s → R) (hx : Z3NetF.PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : Z3NetF.BetaRel inf x (fun n c d => (F n c d : R)) lam β) :
    Z3NetF.H1 F (min k (s - 1))
      (fun c d => (Z3NetF.PPhi k inf x (fun n c d => (F n c d : R)) lam Ur β c d).map ψ) ∧
    Z3NetF.H2 (fun c d => (Z3NetF.PPhi k inf x (fun n c d => (F n c d : R)) lam Ur β c d).map ψ) := by
  set FR : ℕ → Fin s → Fin s → R := fun n c d => (F n c d : R)
  set Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q) :=
    fun c d => (Z3NetF.PPhi k inf x FR lam Ur β c d).map ψ with hΦ
  set L := min k (s - 1) with hLdef
  have hcond : ∀ j : Fin k, (k - 1 - (j : ℕ) < s - 1 ↔ k - 1 - (j : ℕ) < L) := by
    intro j; have := j.isLt; omega
  have h1 : Z3NetF.H1 F L Φ := by
    intro c d r hr j
    simp only [hΦ, Matrix.map_apply]
    by_cases hcd : c = d
    · subst hcd
      have e1 : Z3NetF.PPhi k inf x FR lam Ur β c c r j =
          if (r : ℕ) = 0 ∧ k - 1 - (j : ℕ) < s - 1 then FR (k - 1 - (j : ℕ)) c c else 0 := by
        simp [Z3NetF.PPhi]
      rw [e1]
      by_cases hj : k - 1 - (j : ℕ) < s - 1
      · have c1 : (r : ℕ) = 0 ∧ k - 1 - (j : ℕ) < s - 1 := ⟨hr, hj⟩
        have c2 : k - 1 - (j : ℕ) < L := (hcond j).mp hj
        rw [if_pos c1, if_pos c2, map_intCast]
      · have c1 : ¬ ((r : ℕ) = 0 ∧ k - 1 - (j : ℕ) < s - 1) := fun h => hj h.2
        have c2 : ¬ k - 1 - (j : ℕ) < L := fun h => hj ((hcond j).mpr h)
        rw [if_neg c1, if_neg c2, map_zero]
    · have e1 : Z3NetF.PPhi k inf x FR lam Ur β c d =
          Z3NetF.Lmat k inf x lam c * Z3NetF.frameGraph R k inf x c d * Z3NetF.Ugauge k inf x Ur β d := by
        simp [Z3NetF.PPhi, hcd]
      rw [e1, Gs_row0_core k inf x FR lam Ur β hx hres hβ c d hcd r hr j]
      by_cases hj : k - 1 - (j : ℕ) < s - 1
      · have c2 : k - 1 - (j : ℕ) < L := (hcond j).mp hj
        rw [if_pos hj, if_pos c2, map_intCast]
      · have c2 : ¬ k - 1 - (j : ℕ) < L := fun h => hj ((hcond j).mpr h)
        rw [if_neg hj, if_neg c2, map_zero]
  have h2 : Z3NetF.H2 Φ := by
    intro c r hr j
    have e1 : Z3NetF.PPhi k inf x FR lam Ur β c c r j =
        if (r : ℕ) = 0 ∧ k - 1 - (j : ℕ) < s - 1 then FR (k - 1 - (j : ℕ)) c c else 0 := by
      simp [Z3NetF.PPhi]
    simp only [hΦ, Matrix.map_apply]
    rw [e1, if_neg (fun h => hr h.1), map_zero]
  exact ⟨h1, h2⟩

/-- The generator matrices of `𝒫^F_{k,q}` over `ℤ/qℤ` are those of its graph form. -/
lemma PGen_map_eq {R : Type*} [CommRing R] {s q : ℕ} (ψ : R →+* ZMod q)
    (k : ℕ) (inf : Fin s) (x : Fin s → R) (FR : ℕ → Fin s → Fin s → R) (lam : Fin s → R)
    (Ur : Fin s → ℕ → ℕ → R) (β : Fin s → ℕ → ℕ → R) :
    (fun c => (Z3NetF.PGen k inf x FR lam Ur β c).map ψ) =
      Z3NetF.graphGenK (m := s * k) (fun _ => k)
        (fun c d => (Z3NetF.PPhi k inf x FR lam Ur β c d).map ψ) := by
  funext c
  exact graphGenK_map ψ (m := s * k) (fun _ => k) _ c

theorem D_sep_core {R : Type*} [CommRing R] {s q a : ℕ} [NeZero q] (hs : 2 ≤ s) (ψ : R →+* ZMod q)
    (k : ℕ) (hk : 1 ≤ k) (inf : Fin s) (x : Fin s → R) (hx : Z3NetF.PlacesOK inf x)
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → R) (Ur : Fin s → ℕ → ℕ → R)
    (β : Fin s → ℕ → ℕ → R) (hres : Z3NetF.Residual inf x (fun n c d => (F n c d : R)) lam Ur)
    (hβ : Z3NetF.BetaRel inf x (fun n c d => (F n c d : R)) lam β)
    (α : Fin s → ℕ) (h0 : ∀ c, F 0 c c = -(α c : ℤ)) (hdiag : ∀ n c, 1 ≤ n → F n c c = 0)
    (hdom : ∀ c, ∑ d ∈ univ.filter (fun d => d ≠ c),
      (range (s - 1)).sup (fun j => (Z3NetF.Msum F j c d).natAbs) ≤ α c)
    (ha : ∀ c, α c ≤ a) (hq : 5 * a + 4 ≤ q) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * ((q : ℤ) - a) ^ 2 ≤ (q : ℤ) ^ 2 *
      (Z3NetF.torusDist2 (q ^ (s * k))
        (Z3NetF.digPoint q (s * k) (fun c => (Z3NetF.PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) v)
        (Z3NetF.digPoint q (s * k) (fun c => (Z3NetF.PGen k inf x (fun n c d => (F n c d : R)) lam Ur β c).map ψ) w) : ℤ) := by
  rw [PGen_map_eq]
  obtain ⟨h1, h2⟩ := PGen_H1H2 ψ k inf x hx F lam Ur β hres hβ
  set L := min k (s - 1) with hLdef
  have hL : 1 ≤ L := by omega
  have hLk : L ≤ k := min_le_left _ _
  have hLs : L ≤ s - 1 := min_le_right _ _
  obtain ⟨hBq, hB⟩ := D_LB_core F L α a hL hLs h0 hdiag hdom ha q k hq
  exact Ss_sep_core s q k _ F L hs (by omega) hk hL hLk h1 h2 _ hBq hB v w hvw

end

end Z3NetF.Proofs

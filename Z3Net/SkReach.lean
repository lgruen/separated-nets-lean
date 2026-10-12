/-
Proof module (V14 stage S16′): `cor:skelreach` (reachable skeletons with two skeleton coordinates).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkNec
public import Z3Net.SkNecBridge
public import Z3Net.SkCompIII

@[expose] public section

/-!
# `cor:skelreach`: reachable skeletons with two skeleton coordinates

`ℓ = 2`, `s = r + 2`, skeleton digits of the form of `prop:skelcomp`(iii) (`sk2Coef`) with coefficients
`A, β, g, o` that do not depend on `k`.

* `skelreach_nec_core` (necessity at a single `k ≥ 1`): a graph form with depths `skDepth r k` carrying these
  skeleton digits that is a digital `(0,m,s)`-net over `𝔽_p` satisfies (N1)–(N3) in coefficient form; by
  `lem:skelnec` (`skelnec_N1` with one and two coordinates, `skelnec_N2`, `skelnec_N3_full` with two
  coordinates) through `skel_graphGen`.
* `skelreach_iff_core`: reachable from the frame for every `k ≥ 1` (for some places) iff (N1)–(N3). *If*:
  `prop:skelcomp`(iii). *Only if*: at `k = 1`, the moves of `lem:box` applied to the frame give a net
  (`SkComp.frame_gauge_net`: `lem:Ts`, `lem:box`, `lem:nie`), and the necessity applies.
-/

namespace Z3NetF.Proofs

namespace SkReach

open Matrix Finset

/-- The coefficient of `S_{z_i}` on level `l` of block `d`, read from the generator matrix of the graph form. -/
lemma coef_read (p : ℕ) (r k : ℕ)
    (Φ : (c d : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - skDepth r k c)) (Fin (skDepth r k d)) (ZMod p))
    (A β : Fin 2 → ℕ → ZMod p) (g o : Fin 2 → ZMod p)
    (hΦ : ∀ (i : Fin 2) (d : Fin (r + 2)) (l : Fin (skDepth r k d)),
      ent (Φ (Fin.natAdd r i) d) 0 l = sk2Coef r k A β g o i (d : ℕ) (l : ℕ))
    (i : Fin 2) (d : Fin (r + 2)) (l : ℕ) (hl : l < skDepth r k d) :
    ent (graphGenK (m := (r + 2) * k + r) (skDepth r k) Φ (Fin.natAdd r i)) k (skOff r k (d : ℕ) + l) =
      sk2Coef r k A β g o i (d : ℕ) l := by
  have h := (skel_graphGen (r + 2) r p k (by omega) Φ).2 (Fin.natAdd r i) d (by simp) ⟨l, hl⟩
  rw [h, hΦ i d ⟨l, hl⟩]

/-- The two skeleton coordinates as an embedding `Fin 2 ↪ Fin (r + 2)`. -/
def skEmb (r : ℕ) : Fin 2 ↪ Fin (r + 2) := ⟨Fin.natAdd r, fun a b h => by simpa using h⟩

/-- Two distinct full coordinates as an embedding `Fin 2 ↪ Fin (r + 2)`. -/
def fullEmb (r d d' : ℕ) (hd : d < r) (hd' : d' < r) (hdd : d ≠ d') : Fin 2 ↪ Fin (r + 2) :=
  ⟨![⟨d, by omega⟩, ⟨d', by omega⟩], fun a b h => by
    fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff]⟩

/-- Necessity at a single `k ≥ 1` (`cor:skelreach`, last sentence). -/
theorem skelreach_nec_core (p : ℕ) [Fact p.Prime] (r k : ℕ) (_hr : 1 ≤ r) (hk : 1 ≤ k)
    (A β : Fin 2 → ℕ → ZMod p) (g o : Fin 2 → ZMod p)
    (Φ : (c d : Fin (r + 2)) → Matrix (Fin ((r + 2) * k + r - skDepth r k c)) (Fin (skDepth r k d)) (ZMod p))
    (hΦ : ∀ (i : Fin 2) (d : Fin (r + 2)) (l : Fin (skDepth r k d)),
      ent (Φ (Fin.natAdd r i) d) 0 l = sk2Coef r k A β g o i (d : ℕ) (l : ℕ))
    (hnet : IsNet0 (r + 2) p ((r + 2) * k + r)
      (digPoint p ((r + 2) * k + r) (graphGenK (m := (r + 2) * k + r) (skDepth r k) Φ))) :
    (∀ i d, d < r → A i d ≠ 0) ∧
      (∀ d d', d < r → d' < r → d ≠ d' → A 0 d * A 1 d' - A 0 d' * A 1 d ≠ 0) ∧
      (∀ i, g i ≠ 0) ∧ (∀ d, d < r → A 0 d * β 1 d - β 0 d * A 1 d ≠ 0) := by
  set C := graphGenK (m := (r + 2) * k + r) (skDepth r k) Φ with hCdef
  have hC : IsSkGF (r + 2) r p k C := (skel_graphGen (r + 2) r p k (by omega) Φ).1
  have hfull : ∀ (d : ℕ) (hd : d < r), skDepth (s := r + 2) r k ⟨d, by omega⟩ = k + 1 := by
    intro d hd; simp [skDepth, hd]
  have hskel : ∀ j : Fin 2, skDepth (s := r + 2) r k (Fin.natAdd r j) = k := by
    intro j; simp [skDepth]
  -- entries of the skeleton rows on a full block
  have hA_ent : ∀ (i : Fin 2) (d : ℕ) (hd : d < r),
      ent (C (Fin.natAdd r i)) k (skOff r k d + k) = A i d := by
    intro i d hd
    have h := coef_read p r k Φ A β g o hΦ i ⟨d, by omega⟩ k (by rw [hfull d hd]; omega)
    simpa [sk2Coef, hd] using h
  have hβ_ent : ∀ (i : Fin 2) (d : ℕ) (hd : d < r),
      ent (C (Fin.natAdd r i)) k (skOff r k d + (k - 1)) = β i d := by
    intro i d hd
    have h := coef_read p r k Φ A β g o hΦ i ⟨d, by omega⟩ (k - 1) (by rw [hfull d hd]; omega)
    rw [h]
    simp only [sk2Coef, hd, ite_true]
    rw [if_neg (by omega), if_pos (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (N1) with one coordinate: the entries of `A`
    intro i d hd
    let I : Fin 1 ↪ Fin (r + 2) := ⟨fun _ => Fin.natAdd r i, fun a b _ => Subsingleton.elim a b⟩
    let J : Fin 1 ↪ Fin (r + 2) := ⟨fun _ => ⟨d, by omega⟩, fun a b _ => Subsingleton.elim a b⟩
    have h := skelnec_N1 (r + 2) r p k (by omega) C hC hnet 1 I J
      (fun _ => show r ≤ ((Fin.natAdd r i : Fin (r + 2)) : ℕ) by simp)
      (fun _ => show d < r from hd)
    rw [Matrix.det_unique] at h
    have h' : ent (C (Fin.natAdd r i)) k (skOff r k d + k) ≠ 0 := h
    rwa [hA_ent i d hd] at h'
  · -- (N1) with two coordinates: the `2 × 2` minors of `A`
    intro d d' hd hd' hdd
    have h := skelnec_N1 (r + 2) r p k (by omega) C hC hnet 2 (skEmb r) (fullEmb r d d' hd hd' hdd)
      (fun a => show r ≤ ((Fin.natAdd r a : Fin (r + 2)) : ℕ) by simp)
      (fun b => by fin_cases b; exacts [show d < r from hd, show d' < r from hd'])
    rw [Matrix.det_fin_two] at h
    have h' : ent (C (Fin.natAdd r 0)) k (skOff r k d + k) * ent (C (Fin.natAdd r 1)) k (skOff r k d' + k) -
        ent (C (Fin.natAdd r 0)) k (skOff r k d' + k) * ent (C (Fin.natAdd r 1)) k (skOff r k d + k) ≠ 0 := h
    rwa [hA_ent _ d hd, hA_ent _ d' hd', hA_ent _ d hd, hA_ent _ d' hd'] at h'
  · -- (N2): the faults
    intro i
    have hij : Fin.natAdd r i ≠ Fin.natAdd r (1 - i) := by
      fin_cases i <;> simp [Fin.ext_iff]
    have h := skelnec_N2 (r + 2) r p k (by omega) hk C hC hnet (Fin.natAdd r i) (Fin.natAdd r (1 - i))
      (by simp) (by simp) hij
    have hrd := coef_read p r k Φ A β g o hΦ i (Fin.natAdd r (1 - i)) (k - 1)
      (by rw [hskel]; omega)
    rw [hrd] at h
    have hne : ¬ ((Fin.natAdd r (1 - i) : Fin (r + 2)) : ℕ) = r + (i : ℕ) := by
      fin_cases i <;> simp
    have h1i : ((1 - i : Fin 2) : ℕ) ≠ (i : ℕ) := by fin_cases i <;> decide
    simpa [sk2Coef, hne, h1i, show k - 1 + 1 = k by omega] using h
  · -- (N3) with two skeleton coordinates on a full coordinate
    intro d hd
    have h := skelnec_N3_full (r + 2) r p k (by omega) C hC hnet 2 (by omega) (skEmb r)
      (fun a => show r ≤ ((Fin.natAdd r a : Fin (r + 2)) : ℕ) by simp) ⟨d, by omega⟩ (show d < r from hd)
    rw [Matrix.det_fin_two] at h
    have h' : ent (C (Fin.natAdd r 0)) k (skOff r k d + (k - 0)) *
          ent (C (Fin.natAdd r 1)) k (skOff r k d + (k - 1)) -
        ent (C (Fin.natAdd r 0)) k (skOff r k d + (k - 1)) *
          ent (C (Fin.natAdd r 1)) k (skOff r k d + (k - 0)) ≠ 0 := h
    rw [Nat.sub_zero, hA_ent _ d hd, hA_ent _ d hd, hβ_ent _ d hd, hβ_ent _ d hd] at h'
    exact h'

/-- `cor:skelreach`: reachable from the frame for every `k ≥ 1` iff (N1)–(N3). -/
theorem skelreach_iff_core (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 1 ≤ r) (A β : Fin 2 → ℕ → ZMod p)
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
  constructor
  · rintro ⟨inf, x, hx, H⟩
    obtain ⟨L, U, Φ, hL, hU, hΦF, hΦ⟩ := H 1 le_rfl
    have hnet := SkComp.frame_gauge_net p _ (SkComp.sum_skDepth' r 1 (by omega)) inf x hx L U hL hU Φ hΦF
    exact skelreach_nec_core p r 1 hr le_rfl A β g o Φ hΦ hnet
  · rintro ⟨hA, hA2, hg, hβ⟩
    obtain ⟨inf, x, hx, H⟩ := skelcomp_iii p r hr A β g o hA hA2 hg hβ
    refine ⟨inf, x, hx, fun k hk => ?_⟩
    obtain ⟨L, U, Φ, hL, hU, hΦF, hΦ, -⟩ := H k hk
    exact ⟨L, U, Φ, hL, hU, hΦF, hΦ⟩

end SkReach

end Z3NetF.Proofs

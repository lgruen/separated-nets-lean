/-
Proof module of entry Skel (`prop:skelcomp`(ii): one skeleton coordinate).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkCompG

@[expose] public section

/-!
# Entry Skel: `prop:skelcomp`(ii) (`ℓ = 1`)

* `SkComp.frame_gauge_net`: every graph form obtained from the frame's graph form (any depths `K`,
  any places) by the moves (a), (c) of `lem:box` is a digital `(0,m,s)`-net over `ℤ/qℤ` (the box
  minors of `frameGraphK` are those of the frame divided by its `K`-minor, `lem:Ts`; then
  `lem:box` and `lem:nie`).
* `SkComp.sum_skDepth'`: the skeleton depths sum to `s k + r`.
* `skelcomp_ii`: `prop:skelcomp`(ii) via `skel_Gs` with the single row `S = {z}`.
-/

namespace Z3NetF.Proofs

namespace SkComp

open Polynomial Finset Matrix

noncomputable section

/-- The moves of `lem:box` applied to the frame's graph form give nets. -/
lemma frame_gauge_net (q : ℕ) [NeZero q] {s m : ℕ} (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (inf : Fin s) (x : Fin s → ZMod q) (hx : Z3NetF.PlacesOK inf x)
    (L : (c : Fin s) → Matrix (Fin (m - K c)) (Fin (m - K c)) (ZMod q))
    (U : (d : Fin s) → Matrix (Fin (K d)) (Fin (K d)) (ZMod q))
    (hL : ∀ c, Z3NetF.IsLTU (L c)) (hU : ∀ d, Z3NetF.IsLTU (U d))
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) (ZMod q))
    (hΦ : ∀ c d, c ≠ d → Φ c d = L c * Z3NetF.frameGraphK (ZMod q) m K inf x c d * U d) :
    Z3NetF.IsNet0 s q m (Z3NetF.digPoint q m (Z3NetF.graphGenK (m := m) K Φ)) := by
  rw [nie_zmod]
  intro d hd
  obtain ⟨u, hu, h⟩ := gauge_LU K hK L U (fun c => (hL c).1) (fun c => (hL c).2)
    (fun d => (hU d).1) (fun d => (hU d).2) d hd
  rw [h (Z3NetF.frameGraphK (ZMod q) m K inf x) Φ hΦ]
  refine hu.mul ?_
  have hspec := (frameGraphK_spec_core K hK inf x hx).2
  have hfr : Z3NetF.frameRead m inf x = fun c => Z3NetF.graphGenK (m := m) K
      (Z3NetF.frameGraphK (ZMod q) m K inf x) c * Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) K := by
    funext c; exact (hspec c).symm
  have hd' := GK_unit d hd inf x hx
  have e : Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) d =
      Z3NetF.boxMatrix (Z3NetF.graphGenK (m := m) K (Z3NetF.frameGraphK (ZMod q) m K inf x)) d *
        Z3NetF.boxMatrix (Z3NetF.frameRead m inf x) K := by
    conv_lhs => rw [hfr]
    exact box_mul_right _ _ d
  rw [e, det_mul] at hd'
  exact isUnit_of_mul_isUnit_left hd'

lemma sum_skDepth' {s : ℕ} (r k : ℕ) (hr : r ≤ s) : ∑ c : Fin s, Z3NetF.skDepth r k c = s * k + r := by
  unfold Z3NetF.skDepth
  rw [Fin.sum_univ_eq_sum_range (fun c => if c < r then k + 1 else k) s]
  have : ∀ c, (if c < r then k + 1 else k) = k + (if c < r then 1 else 0) := by
    intro c; split_ifs <;> rfl
  simp only [this, Finset.sum_add_distrib, sum_const, card_range, smul_eq_mul, Finset.sum_boole]
  have hf : (range s).filter (fun c => c < r) = range r := by
    ext c; simp only [mem_filter, mem_range]; omega
  rw [hf, card_range, Nat.cast_id, mul_comm]

lemma ent_zero {R : Type*} [Zero R] {a b : ℕ} (i j : ℕ) :
    Z3NetF.ent (0 : Matrix (Fin a) (Fin b) R) i j = 0 := by
  unfold Z3NetF.ent; split_ifs <;> rfl

lemma Lgauge_LTU {R : Type*} [CommRing R] (n : ℕ) (sc : R) (h : IsUnit sc) :
    Z3NetF.IsLTU (Z3NetF.Lgauge n sc) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp only [Z3NetF.Lgauge]; rw [diagonal_apply_ne _ (ne_of_lt hij)]
  · simp only [Z3NetF.Lgauge, diagonal_apply_eq]
    split_ifs
    · exact h
    · exact isUnit_one

lemma unit_of_ne {p : ℕ} [Fact p.Prime] {a : ZMod p} (h : a ≠ 0) : IsUnit a :=
  isUnit_iff_ne_zero.mpr h

end

end SkComp

open SkComp Finset Matrix in
/-- **`prop:skelcomp`(ii)** (`ℓ = 1`). -/
theorem skelcomp_ii (p : ℕ) [Fact p.Prime] (s k : ℕ) (hs : 2 ≤ s) (inf : Fin s)
    (x : Fin s → ZMod p) (hx : PlacesOK inf x) (κ : ℕ → ZMod p) (hκ : ∀ d, d + 1 < s → κ d ≠ 0) :
    ∃ (L : (c : Fin s) → Matrix (Fin (s * k + (s - 1) - skDepth (s - 1) k c))
        (Fin (s * k + (s - 1) - skDepth (s - 1) k c)) (ZMod p))
      (U : (d : Fin s) → Matrix (Fin (skDepth (s - 1) k d)) (Fin (skDepth (s - 1) k d)) (ZMod p))
      (Φ : (c d : Fin s) → Matrix (Fin (s * k + (s - 1) - skDepth (s - 1) k c))
        (Fin (skDepth (s - 1) k d)) (ZMod p)),
      (∀ c, IsLTU (L c)) ∧ (∀ d, IsLTU (U d)) ∧
      (∀ c d, c ≠ d → Φ c d =
        L c * frameGraphK (ZMod p) (s * k + (s - 1)) (skDepth (s - 1) k) inf x c d * U d) ∧
      (∀ z d : Fin s, (z : ℕ) + 1 = s → ∀ l : Fin (skDepth (s - 1) k d),
        ent (Φ z d) 0 l = if (d : ℕ) + 1 < s ∧ (l : ℕ) = k then κ d else 0) ∧
      IsNet0 s p (s * k + (s - 1))
        (digPoint p (s * k + (s - 1)) (graphGenK (m := s * k + (s - 1)) (skDepth (s - 1) k) Φ)) := by
  classical
  set K : Fin s → ℕ := skDepth (s - 1) k with hKdef
  have hK : ∑ c, K c = s * k + (s - 1) := sum_skDepth' (s - 1) k (by omega)
  set z : Fin s := ⟨s - 1, by omega⟩ with hz
  set S : Finset (Fin s) := {z}
  have hcard : ∀ d, d ≠ z → (S.erase d).card = 1 := by
    intro d hd
    rw [Finset.erase_eq_of_notMem (by simp [S, hd])]; rfl
  have hcard0 : (S.erase z).card = 0 := by simp [S]
  have hdz : ∀ d : Fin s, d ≠ z → (d : ℕ) + 1 < s := by
    intro d hd
    have : (d : ℕ) ≠ s - 1 := fun h => hd (Fin.ext h)
    omega
  set F : ℕ → Fin s → Fin s → ZMod p := fun _ _ d => κ d
  set lam : Fin s → ZMod p := fun _ => 1
  set Ur : Fin s → ℕ → ℕ → ZMod p := fun d _ _ => κ d * Ring.inverse (wN inf x z d)
  have hres : ResidualSk inf x S F lam Ur := by
    refine ⟨fun _ _ => isUnit_one, ?_, ?_, ?_⟩
    · intro d n' n h1 h2
      by_cases hd : d = z
      · rw [hd, hcard0] at h2; omega
      · rw [hcard d hd] at h2; omega
    · intro d n hn
      by_cases hd : d = z
      · rw [hd, hcard0] at hn; omega
      · exact (unit_of_ne (hκ d (hdz d hd))).mul
          (wN_unit inf x hx z d (Ne.symm hd)).ringInverse
    · intro c hc d hcd n hn
      have hcz : c = z := Finset.mem_singleton.mp hc
      have hd : d ≠ z := fun h => hcd (hcz.trans h.symm)
      rw [hcard d hd] at hn
      obtain rfl : n = 0 := by omega
      subst hcz
      simp only [F, lam, Ur, zero_add, Finset.sum_range_one, pow_zero, mul_one, one_mul]
      rw [mul_comm, mul_assoc, Ring.inverse_mul_cancel _ (wN_unit inf x hx z d (Ne.symm hd)), mul_one]
  obtain ⟨U, hU, hrow⟩ := skel_Gs K hK inf x hx S F lam Ur hres
  set L : (c : Fin s) → Matrix (Fin (s * k + (s - 1) - K c)) (Fin (s * k + (s - 1) - K c)) (ZMod p) :=
    fun c => Lgauge (s * k + (s - 1) - K c) (lam c * Ring.inverse (QfK K inf x c))
  set Φ : (c d : Fin s) → Matrix (Fin (s * k + (s - 1) - K c)) (Fin (K d)) (ZMod p) :=
    fun c d => if c = d then 0 else L c * frameGraphK (ZMod p) (s * k + (s - 1)) K inf x c d * U d
  have hL : ∀ c, IsLTU (L c) := fun c =>
    Lgauge_LTU _ _ (isUnit_one.mul (QfK_unit K inf x hx c).ringInverse)
  have hΦ : ∀ c d, c ≠ d → Φ c d = L c * frameGraphK (ZMod p) (s * k + (s - 1)) K inf x c d * U d :=
    fun c d hcd => by simp only [Φ, if_neg hcd]
  refine ⟨L, U, Φ, hL, hU, hΦ, ?_, frame_gauge_net p K hK inf x hx L U hL hU Φ hΦ⟩
  intro z' d hz' l
  have hzz : z' = z := Fin.ext (by simp [hz]; omega)
  subst hzz
  by_cases hd : d = z
  · subst hd
    simp only [Φ, if_pos rfl, ent_zero]
    rw [if_neg]; simp only [hz]; omega
  · rw [hΦ z d (Ne.symm hd), hrow z (Finset.mem_singleton_self z) d (Ne.symm hd) l, hcard d hd]
    have hKd : K d = k + 1 := by
      simp only [hKdef, skDepth]; rw [if_pos (by have := hdz d hd; omega)]
    have hl := l.isLt
    simp only [F]
    by_cases hlk : (l : ℕ) = k
    · rw [if_pos (by omega), if_pos ⟨hdz d hd, hlk⟩]
    · rw [if_neg (by omega), if_neg (fun h => hlk h.2)]

end Z3NetF.Proofs

module
public import Mathlib
public import Z3Net.D4Thm1

@[expose] public section

/-!
# 4D entry, part 10: Theorem 4D(1), box minors `±2^j` over `ℚ`

All definitions are polynomial in `h`. Over `ℤ[X]` with `h = X` a box minor is a polynomial
`Δ ∈ ℤ[X]`; evaluating at `1/2 ∈ ℚ` gives the box minor over `ℚ`, evaluating at `2⁻¹ ∈ 𝔽_p` the
box minor over `𝔽_p`, which is nonzero for every odd prime `p` (`box_injective_zmod`). Hence the
integer `z = 2^(deg Δ) Δ(1/2)` is nonzero modulo every odd prime, `z = ±2^a`, and the minor over
`ℚ` is `±2^(a - deg Δ)`.
-/

namespace Z3NetD4.Proofs

open Polynomial Finset Matrix Z3NetD4

noncomputable section

section map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (h : R)

lemma map_Ures (d : Fin 4) (a b : Fin 3) : f (Ures h d a b) = Ures (f h) d a b := by
  fin_cases d <;> fin_cases a <;> fin_cases b <;> simp [Ures, map_ofNat]

lemma map_alpha (d : Fin 4) (n : ℕ) : f (alpha h d n) = alpha (f h) d n := by
  unfold alpha; split_ifs <;> simp [map_ofNat]

lemma map_beta (d : Fin 4) (n : ℕ) : f (beta h d n) = beta (f h) d n := by
  unfold beta; split_ifs <;> simp [map_ofNat]

lemma map_Ux (d : Fin 4) (n' n : ℕ) : f (Ux h d n' n) = Ux (f h) d n' n := by
  unfold Ux
  split_ifs <;> simp [map_Ures, map_alpha, map_beta]

lemma map_Qinv (k : ℕ) (c : Fin 4) : f (Qinv h k c) = Qinv (f h) k c := by
  fin_cases c <;> simp [Qinv]

lemma map_D4Phi (k : ℕ) (c d : Fin 4) : (D4Phi R h k c d).map f = D4Phi S (f h) k c d := by
  ext r j
  simp only [map_apply, D4Phi]
  split_ifs <;> simp [map_sum, map_Qinv, Uk, map_Ux]

lemma map_graphGen (k : ℕ) (Φ : Fin 4 → Fin 4 → Matrix (Fin (3 * k)) (Fin k) R) (c : Fin 4) :
    (graphGen k Φ c).map f = graphGen k (fun c d => (Φ c d).map f) c := by
  ext i j
  simp only [map_apply, graphGen]
  split_ifs <;> simp

lemma map_boxMatrix {m : ℕ} (C : Fin 4 → Matrix (Fin m) (Fin m) R) (d : Fin 4 → ℕ) :
    (boxMatrix C d).map f = boxMatrix (fun c => (C c).map f) d := by
  ext r j
  simp only [map_apply, boxMatrix]
  split_ifs <;> rfl

lemma box_map (k : ℕ) (d : Fin 4 → ℕ) :
    (boxMatrix (graphGen k (D4Phi R h k)) d).map f = boxMatrix (graphGen k (D4Phi S (f h) k)) d := by
  rw [map_boxMatrix]
  congr 1
  funext c
  rw [map_graphGen]
  congr 1
  funext c' d'
  exact map_D4Phi f h k c' d'

end map

/-- `2^D · Δ(u) = ∑_{i ≤ D} Δ_i 2^(D-i)` whenever `2 u = 1`. -/
lemma scaled_eval {S : Type*} [CommRing S] (u : S) (hu : 2 * u = 1) (Δ : ℤ[X]) :
    (((∑ i ∈ range (Δ.natDegree + 1), Δ.coeff i * 2 ^ (Δ.natDegree - i) : ℤ)) : S) =
      2 ^ Δ.natDegree * Δ.eval₂ (Int.castRingHom S) u := by
  rw [eval₂_eq_sum_range, Finset.mul_sum]
  push_cast
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  have : (2 : S) ^ Δ.natDegree * u ^ i = 2 ^ (Δ.natDegree - i) := by
    rw [show Δ.natDegree = (Δ.natDegree - i) + i by omega, pow_add, mul_assoc, ← mul_pow, hu,
      one_pow, mul_one, Nat.add_sub_cancel]
  rw [eq_intCast, ← this]; ring

lemma int_eq_pm_two_pow' (z : ℤ) (h : ∀ p : ℕ, p.Prime → p ≠ 2 → (z : ZMod p) ≠ 0) :
    ∃ a : ℕ, z = 2 ^ a ∨ z = -2 ^ a := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact h 3 Nat.prime_three (by norm_num) (by simp)
  obtain ⟨a, hn⟩ : ∃ a : ℕ, z.natAbs = 2 ^ a := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Int.natAbs_ne_zero.mpr hz0) ?_⟩
    intro d hd hdz
    by_contra hd2
    exact h d hd hd2 ((ZMod.intCast_zmod_eq_zero_iff_dvd z d).mpr (Int.ofNat_dvd_left.mpr hdz))
  refine ⟨a, ?_⟩
  rcases Int.natAbs_eq z with h1 | h1
  · left; rw [h1, hn]; push_cast; ring
  · right; rw [h1, hn]; push_cast; ring

/-- **Theorem 4D(1), box minors.** -/
theorem D4_boxMinor (k : ℕ) (hk : 2 ≤ k) (d : Fin 4 → ℕ) (hd : d 0 + d 1 + d 2 + d 3 = 4 * k) :
    ∃ j : ℤ, (boxMatrix (graphGen k (D4Phi ℚ (1 / 2) k)) d).det = 2 ^ j ∨
      (boxMatrix (graphGen k (D4Phi ℚ (1 / 2) k)) d).det = -2 ^ j := by
  set Δ : ℤ[X] := (boxMatrix (graphGen k (D4Phi ℤ[X] X k)) d).det with hΔ
  set D := Δ.natDegree
  set z : ℤ := ∑ i ∈ range (D + 1), Δ.coeff i * 2 ^ (D - i) with hz
  -- the minor over a ring `S` with `2 u = 1` is `Δ(u)`
  have hdet : ∀ (S : Type) [CommRing S] (u : S),
      (boxMatrix (graphGen k (D4Phi S u k)) d).det = Δ.eval₂ (Int.castRingHom S) u := by
    intro S _ u
    have := box_map (eval₂RingHom (Int.castRingHom S) u) X k d
    rw [show (eval₂RingHom (Int.castRingHom S) u) X = u by simp] at this
    rw [← this]
    exact (RingHom.map_det (eval₂RingHom (Int.castRingHom S) u) _).symm
  -- nonzero modulo every odd prime
  have hp : ∀ p : ℕ, p.Prime → p ≠ 2 → (z : ZMod p) ≠ 0 := by
    intro p hp hp2
    have := Fact.mk hp
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hu := two_mul_inv_two p hodd
    rw [hz, scaled_eval _ hu Δ, ← hdet]
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · intro h0; rw [h0, zero_mul] at hu; exact zero_ne_one hu
    · intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0
      exact box_injective_zmod p k hodd (by omega) d hd (by rw [mulVec_zero]; exact hv)
  obtain ⟨a, ha⟩ := int_eq_pm_two_pow' z hp
  have hq := scaled_eval (1 / 2 : ℚ) (by norm_num) Δ
  rw [← hz, ← hdet] at hq
  refine ⟨(a : ℤ) - D, ?_⟩
  have h2D : (2 : ℚ) ^ D ≠ 0 := by positivity
  have key : (boxMatrix (graphGen k (D4Phi ℚ (1 / 2) k)) d).det = (z : ℚ) / 2 ^ D := by
    rw [hq]; field_simp; rfl
  rw [key, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_natCast]
  rcases ha with ha | ha
  · left; rw [ha]; push_cast; ring
  · right; rw [ha]; push_cast; ring

end

end Z3NetD4.Proofs

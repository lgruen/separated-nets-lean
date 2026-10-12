module
public import Z3Net.NetQ

@[expose] public section

/-!
# The net property of `𝒬_{k,q}` over `ℤ/qℤ` for every odd `q` (Theorem `thm:two`, net part)

The prime case `Q_net` (`Z3Net/NetQ.lean`) shows, via the gauge lemma over the field `𝔽_p`,
that every box matrix of `QGen k` reduced mod an odd prime `p` has trivial kernel.  Hence the
*integer* box minor `Δ_d = det (boxMatrix (QGen k) d)` is nonzero modulo every odd prime:

* `Δ_d = ±2^a` (`Q_boxMinor_pow_two`), and
* `Δ_d` is coprime to every odd `q`, i.e. a unit in `ℤ/qℤ`; the ring form of Niederreiter's
  lemma (`isNet0_of_box_injective`, valid over `ZMod q` for any `q ≠ 0`) then gives the net
  property over `ℤ/qℤ` (`Q_net_odd`), composite `q` included.

No new gauge computation is needed: primality enters only through the field-level kernel
argument at the odd prime divisors of `q`.
-/

namespace Z3Net.Proofs

open Matrix

/-- The box matrices of `𝒬_{k,p}` over `𝔽_p` (`p` an odd prime) have trivial kernel
(the body of `Q_net`, in kernel form). -/
lemma Q_box_kernel_prime (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hk : 2 ≤ k)
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    ∀ n, boxMatrix (fun c => (QGen k c).map (Int.cast : ℤ → ZMod p)) d *ᵥ n = 0 → n = 0 := by
  have hgen : (fun c => (QGen k c).map (Int.cast : ℤ → ZMod p)) =
      graphGen k (fun c e => (QPhiOf k (frameB k) (frameC k) c e).map (Int.cast : ℤ → ZMod p)) := by
    funext c
    exact graphGen_map_int k _ c
  rw [hgen]
  obtain ⟨lam, s, hlam, hs, hfac⟩ := muQ_factor (F := ZMod p) k d hd
  exact gauge_transfer k (by omega) _
    (fun c e => (graphBlock k (frameGen k) c e).map (Int.cast : ℤ → ZMod p))
    ((Rmat k).map Int.cast) (map_lower _ (Rmat_lower k)) (isUnit_map_diag _ (Rmat_diag k))
    ((Ustar k).map Int.cast) (map_lower _ (Ustar_lower k))
    (fun i => by rw [map_apply]; exact isUnit_intCast_of_dvd_four p hp2 _ (Ustar_diag_dvd k i))
    muQ (fun c e hce => QPhi_gauge k (by omega) c e hce) d hd lam s hlam hs hfac
    (fun n' hn' => frameGraph_box_kernel k (by omega) d hd n' hn')

/-- Every integer box minor of `QGen k` is nonzero modulo every odd prime. -/
lemma Q_boxMinor_ne_zero_mod (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k)
    (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    (((boxMatrix (QGen k) d).det : ℤ) : ZMod p) ≠ 0 := by
  have := Fact.mk hp
  intro hzero
  have hmap := boxMatrix_map (Int.castRingHom (ZMod p)) (QGen k) d
  have hdet : ((boxMatrix (QGen k) d).map (Int.castRingHom (ZMod p))).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; simpa using hzero
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply Q_box_kernel_prime p k hp2 hk d hd v
  rw [← hv, ← hmap]
  rfl

/-- An integer that is nonzero modulo every odd prime is a unit modulo every odd `q`. -/
lemma isUnit_intCast_of_odd (z : ℤ) (h : ∀ p : ℕ, p.Prime → p ≠ 2 → (z : ZMod p) ≠ 0)
    (q : ℕ) (hq : Odd q) : IsUnit (z : ZMod q) := by
  have hcop : Nat.Coprime z.natAbs q := by
    apply Nat.coprime_of_dvd
    intro r hr hrz hrq
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr hrq)
    apply h r hr hr2
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.ofNat_dvd_left.mpr hrz
  have hu : IsUnit ((z.natAbs : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  rcases Int.natAbs_eq z with hz | hz
  · rw [hz, Int.cast_natCast]
    exact hu
  · rw [hz, Int.cast_neg, Int.cast_natCast]
    exact hu.neg

/-- An integer that is nonzero modulo every odd prime is `±2^a`. -/
lemma int_eq_pm_two_pow (z : ℤ) (h : ∀ p : ℕ, p.Prime → p ≠ 2 → (z : ZMod p) ≠ 0) :
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
  · left
    rw [h1, hn]
    push_cast
    ring
  · right
    rw [h1, hn]
    push_cast
    ring

/-- **Box minors of `𝒬_{k,·}` over `ℤ`.** For `k ≥ 2`, every box minor of the integer generator
matrices `QGen k` is `±2^a` for some `a`. -/
theorem Q_boxMinor_pow_two (k : ℕ) (hk : 2 ≤ k) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    ∃ a : ℕ, (boxMatrix (QGen k) d).det = 2 ^ a ∨ (boxMatrix (QGen k) d).det = -2 ^ a :=
  int_eq_pm_two_pow _ fun p hp hp2 => Q_boxMinor_ne_zero_mod p k hp hp2 hk d hd

/-- **Theorem `thm:two`, net part, every odd modulus.** For every odd `q` (composite allowed)
and `k ≥ 2`, `𝒬_{k,q}` is a `(0,3k,3)`-net over `ℤ/qℤ`. -/
theorem Q_net_odd (q k : ℕ) (hq : Odd q) (hk : 2 ≤ k) : IsNet0 q (3 * k) (Qpoint q k) := by
  have : NeZero q := ⟨by rintro rfl; exact absurd hq (by decide)⟩
  apply isNet0_of_box_injective
  intro d hd
  apply mulVec_injective_of_isUnit_det
  have hmap0 := boxMatrix_map (Int.castRingHom (ZMod q)) (QGen k) d
  have hmap : boxMatrix (fun c => (QGen k c).map (Int.cast : ℤ → ZMod q)) d =
      (boxMatrix (QGen k) d).map (Int.castRingHom (ZMod q)) := hmap0
  rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact isUnit_intCast_of_odd _ (fun p hp hp2 => Q_boxMinor_ne_zero_mod p k hp hp2 hk d hd) q hq

end Z3Net.Proofs

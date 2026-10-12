module
public import Mathlib
public import Z3Net.HL8Lev
public import Z3Net.HLB5

@[expose] public section

/-!
# Entry HL8, part 3: `prop:HL5` per level

The point differences, `λ'` and the leading coefficients of the column polynomials `f_{d,n}` of
`B₅` at the levels `n ≤ 2` divide `N₁ = 2^10 3^10 5^10 7^10` (`decide +kernel`); the primes `97`
and `101` occur only in the leading coefficients at level `3` (which divide `N₀`, entry HL). So
for `k ≤ 3` only `2, 3, 5, 7` are excluded (`HL_net_lev` with `L = min(k, 4) ≤ 3`), and for
`k ≥ 4` the admissibility of entry HL applies.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-- `N₁ = 2^10 3^10 5^10 7^10`. -/
def N1 : ℕ := 2 ^ 10 * 3 ^ 10 * 5 ^ 10 * 7 ^ 10

lemma N1_dvd_N0 : N1 ∣ N0 := ⟨97 * 101, by unfold N1 N0; ring⟩

lemma prime_dvd_N1 (q : ℕ) (hq : q.Prime) (h : q ∣ N1) : q ∈ ({2, 3, 5, 7} : Finset ℕ) := by
  have hp : ∀ p : ℕ, p.Prime → q ∣ p → q = p := fun p hp h' => (Nat.prime_dvd_prime_iff_eq hq hp).mp h'
  unfold N1 at h
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · left; exact hp 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
      · right; left; exact hp 3 Nat.prime_three (hq.dvd_of_dvd_pow h)
    · right; right; left; exact hp 5 (by norm_num) (hq.dvd_of_dvd_pow h)
  · right; right; right; exact hp 7 (by norm_num) (hq.dvd_of_dvd_pow h)

lemma gcd_one_of_dvd_N1 (q : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7} : Finset ℕ))
    (z : ℤ) (hz : z ∣ (N1 : ℤ)) : Int.gcd z q = 1 := by
  have hd : Int.gcd z q ∣ q := by
    have := Int.gcd_dvd_right (a := z) (b := (q : ℤ))
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr this |>.trans (by simp)
  rcases (Nat.dvd_prime hq).mp hd with h | h
  · exact h
  · exfalso
    have h1 : (q : ℤ) ∣ z := by
      have := Int.gcd_dvd_left (a := z) (b := (q : ℤ)); rw [h] at this; exact this
    have h2 : q ∣ N1 := by exact_mod_cast h1.trans hz
    exact hbad (prime_dvd_N1 q hq h2)

lemma coprime_of_dvd_N1 (q : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7} : Finset ℕ))
    (n : ℕ) (hn : n ∣ N1) : Nat.Coprime n q := by
  have := gcd_one_of_dvd_N1 q hq hbad (n : ℤ) (by exact_mod_cast hn)
  rw [Int.gcd_natCast_natCast] at this
  exact this

lemma B5_pts_dvd1 : ∀ c : Fin 5, ∀ e : Fin 2, ∀ c' : Fin 5, ∀ e' : Fin 2, (c, e) ≠ (c', e') →
    (splitPt uB5 vB5 c e - splitPt uB5 vB5 c' e') ∣ (N1 : ℤ) := by
  decide +kernel

lemma B5_lam_dvd1 : ∀ c : Fin 5, (lamB5 c).num ∣ (N1 : ℤ) ∧ (lamB5 c).den ∣ N1 := by
  decide +kernel

lemma B5_lead_dvd1 : ∀ d : Fin 5, ∀ n : Fin 3,
    (gcoB5 d n n).num ∣ (N1 : ℤ) ∧ (gcoB5 d n n).den ∣ N1 := by
  decide +kernel

theorem B5_net_lev (q k : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7} : Finset ℕ))
    (h4 : 4 ≤ k → q ∉ ({97, 101} : Finset ℕ)) (hk : 1 ≤ k) :
    Z3NetHL.IsNet0 5 q (5 * k) (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5) := by
  by_cases hk4 : 4 ≤ k
  · have hbad' : q ∉ ({2, 3, 5, 7, 97, 101} : Finset ℕ) := by
      have := h4 hk4
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbad this ⊢
      tauto
    exact B5_net q k hq hbad' hk
  · refine HL_net_lev 5 q k uB5 vB5 lamB5 gcoB5 dgB5 (by norm_num) ⟨hq.two_le,
      fun c e c' e' h => gcd_one_of_dvd_N1 q hq hbad _ (B5_pts_dvd1 c e c' e' h),
      fun c => ⟨gcd_one_of_dvd_N1 q hq hbad _ (B5_lam_dvd1 c).1,
        coprime_of_dvd_N1 q hq hbad _ (B5_lam_dvd1 c).2⟩, fun d n hn => ?_⟩ hk
    have := B5_lead_dvd1 d ⟨n, by omega⟩
    exact ⟨gcd_one_of_dvd_N1 q hq hbad _ this.1, coprime_of_dvd_N1 q hq hbad _ this.2⟩

end

end Z3NetHL.Proofs

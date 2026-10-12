module
public import Mathlib
public import Z3Net.HLMainH

@[expose] public section

/-!
# Entry HL, part 10: the `s = 5` design `B₅`

* `B5_design`: `2 F_x[c][d] = F2[x][c][d]` (the witness matrix), by `decide +kernel` on the 100
  entries `x < 4` (all rational arithmetic is exact).
* Bad primes: every point difference, `λ'_c` (numerator and denominator) and every coefficient of
  the `f_{d,n}` used divides `N₀ = 2^10 3^10 5^10 7^10 · 97 · 101` (`decide +kernel`); a prime
  `q ∉ {2, 3, 5, 7, 97, 101}` does not divide `N₀`, so all of them are units mod `q`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-! ## The witness identity -/

lemma B5_design_lt : ∀ x : Fin 4, ∀ c d : Fin 5,
    2 * HLdes uB5 vB5 lamB5 gcoB5 dgB5 x c d = F2B5 x c d := by
  decide +kernel

theorem B5_design (x : ℕ) (c d : Fin 5) :
    2 * HLdes uB5 vB5 lamB5 gcoB5 dgB5 x c d = F2B5 x c d := by
  by_cases hx : x < 4
  · exact B5_design_lt ⟨x, hx⟩ c d
  · have h1 : HLdes uB5 vB5 lamB5 gcoB5 dgB5 x c d = 0 := by
      simp [HLdes, show 5 - 1 ≤ x by omega]
    have h2 : F2B5 x c d = 0 := by
      unfold F2B5
      have : F2TabB5.getD x [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [F2TabB5]; omega)]; rfl
      rw [this]; simp
    rw [h1, h2]; simp

/-! ## Bad primes -/

/-- `N₀ = 2^10 3^10 5^10 7^10 · 97 · 101`. -/
def N0 : ℕ := 2 ^ 10 * 3 ^ 10 * 5 ^ 10 * 7 ^ 10 * 97 * 101

lemma prime_dvd_N0 (q : ℕ) (hq : q.Prime) (h : q ∣ N0) : q ∈ ({2, 3, 5, 7, 97, 101} : Finset ℕ) := by
  have hp : ∀ p : ℕ, p.Prime → q ∣ p → q = p := fun p hp h' => (Nat.prime_dvd_prime_iff_eq hq hp).mp h'
  unfold N0 at h
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · left; exact hp 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
          · right; left; exact hp 3 Nat.prime_three (hq.dvd_of_dvd_pow h)
        · right; right; left; exact hp 5 (by norm_num) (hq.dvd_of_dvd_pow h)
      · right; right; right; left; exact hp 7 (by norm_num) (hq.dvd_of_dvd_pow h)
    · right; right; right; right; left; exact hp 97 (by norm_num) h
  · right; right; right; right; right; exact hp 101 (by norm_num) h

lemma gcd_one_of_dvd_N0 (q : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7, 97, 101} : Finset ℕ))
    (z : ℤ) (hz : z ∣ (N0 : ℤ)) : Int.gcd z q = 1 := by
  have hd : Int.gcd z q ∣ q := by
    have := Int.gcd_dvd_right (a := z) (b := (q : ℤ))
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr this |>.trans (by simp)
  rcases (Nat.dvd_prime hq).mp hd with h | h
  · exact h
  · exfalso
    have h1 : (q : ℤ) ∣ z := by
      have := Int.gcd_dvd_left (a := z) (b := (q : ℤ)); rw [h] at this; exact this
    have h2 : q ∣ N0 := by exact_mod_cast h1.trans hz
    exact hbad (prime_dvd_N0 q hq h2)

lemma coprime_of_dvd_N0 (q : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7, 97, 101} : Finset ℕ))
    (n : ℕ) (hn : n ∣ N0) : Nat.Coprime n q := by
  have := gcd_one_of_dvd_N0 q hq hbad (n : ℤ) (by exact_mod_cast hn)
  rw [Int.gcd_natCast_natCast] at this
  exact this

lemma B5_pts_dvd : ∀ c : Fin 5, ∀ e : Fin 2, ∀ c' : Fin 5, ∀ e' : Fin 2, (c, e) ≠ (c', e') →
    (splitPt uB5 vB5 c e - splitPt uB5 vB5 c' e') ∣ (N0 : ℤ) := by
  decide +kernel

lemma B5_lam_dvd : ∀ c : Fin 5, (lamB5 c).num ∣ (N0 : ℤ) ∧ (lamB5 c).den ∣ N0 := by
  decide +kernel

lemma B5_lead_dvd : ∀ d : Fin 5, ∀ n : Fin 4,
    (gcoB5 d n n).num ∣ (N0 : ℤ) ∧ (gcoB5 d n n).den ∣ N0 := by
  decide +kernel

lemma B5_den_dvd : ∀ d : Fin 5, ∀ n : Fin 4, ∀ n' : Fin 4, (gcoB5 d n n').den ∣ N0 := by
  decide +kernel

lemma B5_dg_dvd : ∀ c : Fin 5, ∀ n : Fin 4, (dgB5 c n).den ∣ N0 := by
  decide +kernel

lemma adm_B5 (q : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7, 97, 101} : Finset ℕ)) :
    HLAdm 5 q uB5 vB5 lamB5 gcoB5 := by
  refine ⟨hq.two_le, fun c e c' e' h => gcd_one_of_dvd_N0 q hq hbad _ (B5_pts_dvd c e c' e' h),
    fun c => ⟨gcd_one_of_dvd_N0 q hq hbad _ (B5_lam_dvd c).1,
      coprime_of_dvd_N0 q hq hbad _ (B5_lam_dvd c).2⟩, fun d n hn => ?_⟩
  have := B5_lead_dvd d ⟨n, by omega⟩
  exact ⟨gcd_one_of_dvd_N0 q hq hbad _ this.1, coprime_of_dvd_N0 q hq hbad _ this.2⟩

lemma den_B5 (q : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7, 97, 101} : Finset ℕ)) :
    HLDen 5 q gcoB5 dgB5 :=
  ⟨fun d n hn n' hn' => coprime_of_dvd_N0 q hq hbad _ (B5_den_dvd d ⟨n, by omega⟩ ⟨n', by omega⟩),
    fun c n hn => coprime_of_dvd_N0 q hq hbad _ (B5_dg_dvd c ⟨n, by omega⟩)⟩

theorem B5_net (q k : ℕ) (hq : q.Prime) (hbad : q ∉ ({2, 3, 5, 7, 97, 101} : Finset ℕ))
    (hk : 1 ≤ k) : Z3NetHL.IsNet0 5 q (5 * k) (HLpoint 5 q k uB5 vB5 lamB5 gcoB5 dgB5) :=
  HL_net 5 q k uB5 vB5 lamB5 gcoB5 dgB5 (by norm_num) (adm_B5 q hq hbad) hk

end

end Z3NetHL.Proofs

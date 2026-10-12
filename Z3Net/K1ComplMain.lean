/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.K1ComplData
public import Z3Net.K1ComplDefs
public import Z3Net.DeficitMain

@[expose] public section

/-!
# V14 stage S15′: `prop:k1designs`, the remainder

* (2) the `t = 0` completions of the frameless layers for every admissible `q` (`free5_net`, `free6a_net`,
  `free6b_net`), with the bound `LB₁(q)` of `prop:k1`(1) for the resulting nets. Proof route: an integer completion
  whose box minors have only the excluded primes works modulo every admissible prime (`k1Free5`, `k1Free6a`); for
  `k1Free6b` the integer completion has the further primes `11, 13, 17, 19`, which the audited per-prime completions
  cover; then the integer lift and the Chinese remainder theorem (`net_of_compl`). The paper uses the
  Schwartz–Zippel lemma for the primes above `SZ(s)` and per-prime completions below it; the statement is the same.
* (1) the `s = 5` frame layer is, off the diagonal, the geometric layer `F₀` of the `s = 5` design of `tab:Kdesigns`
  (as printed in `app:designs`), and a Cauchy layer `λ'_c μ_d w_cd` on the places `∞, 0, 1, 2, 3` with the row
  scalars `λ' = (1/2, 1, 1, 1, 1)` of that design (`frame5_cauchy`).
-/

namespace Z3NetF.Proofs.K1Compl

open Matrix Finset Z3NetF

lemma not_dvd_of_strip {s : ℕ} (F0 : Fin s → Fin s → ℤ) (A : Fin s → Fin (s - 2) → Fin s → ℤ) (S : List ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hchk : (compList s s).all (fun d => strip S (boxDetM F0 A d).natAbs = 1) = true)
    (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) : ∀ d ∈ compList s s, ¬ (p : ℤ) ∣ boxDetM F0 A d := by
  intro d hd hdvd
  have h1 := of_decide_eq_true (List.all_eq_true.mp hchk d hd)
  exact hpS (strip_spec S hS _ h1 p hp (Int.natCast_dvd.mp hdvd))

lemma not_dvd_of_mod {s : ℕ} (F0 : Fin s → Fin s → ℤ) (A : Fin s → Fin (s - 2) → Fin s → ℤ) (p : ℕ)
    (hchk : (compList s s).all (fun d => boxDetM F0 A d % (p : ℤ) ≠ 0) = true) :
    ∀ d ∈ compList s s, ¬ (p : ℤ) ∣ boxDetM F0 A d := by
  intro d hd hdvd
  have h1 := of_decide_eq_true (List.all_eq_true.mp hchk d hd)
  exact h1 (Int.emod_eq_zero_of_dvd hdvd)

/-- **`prop:k1designs`(2), `s = 5`**: for every `q` with `gcd(q, 30) = 1` the frameless layer `k1Free5` has a `t = 0`
completion over `ℤ/qℤ`. -/
theorem free5_net (q : ℕ) [NeZero q] (hq : Nat.Coprime q 30) :
    ∃ Φ : Fin 5 → Fin 5 → Matrix (Fin (5 * 1 - 1)) (Fin 1) (ZMod q),
      (∀ c d (r : Fin (5 * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (k1Free5 c d : ZMod q)) ∧ H2 Φ ∧
      IsNet0 5 q (5 * 1) (digPoint q (5 * 1) (graphGenK (m := 5 * 1) (fun _ => 1) Φ)) := by
  refine net_of_compl q k1Free5 (fun _ => A5) fun p hp hpq => ?_
  refine not_dvd_of_strip k1Free5 A5 [2, 3, 5] (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num)
    chk5 p hp ?_
  intro hmem
  have h30 : p ∣ 30 := by simp at hmem; rcases hmem with rfl | rfl | rfl <;> norm_num
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpq hq) h30)

/-- **`prop:k1designs`(2), `s = 6`, `K₁ = 3`**: for every `q` with no prime factor in
`𝓔₆ = {2, 3, 5, 7, 11, 13, 17, 23, 31}` the frameless layer `k1Free6a` has a `t = 0` completion over `ℤ/qℤ`. -/
theorem free6a_net (q : ℕ) [NeZero q]
    (hq : ∀ p ∈ ({2, 3, 5, 7, 11, 13, 17, 23, 31} : Finset ℕ), ¬ p ∣ q) :
    ∃ Φ : Fin 6 → Fin 6 → Matrix (Fin (6 * 1 - 1)) (Fin 1) (ZMod q),
      (∀ c d (r : Fin (6 * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (k1Free6a c d : ZMod q)) ∧ H2 Φ ∧
      IsNet0 6 q (6 * 1) (digPoint q (6 * 1) (graphGenK (m := 6 * 1) (fun _ => 1) Φ)) := by
  refine net_of_compl q k1Free6a (fun _ => A6a) fun p hp hpq => ?_
  refine not_dvd_of_strip k1Free6a A6a [2, 3, 5, 7, 11, 13, 17, 23, 31]
    (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    chk6a p hp ?_
  intro hmem
  exact hq p (by simpa using hmem) hpq

/-- **`prop:k1designs`(2), `s = 6`, `K₁ = 5`** (`tab:practical`): for every `q` with `gcd(q, 210) = 1` the frameless
layer `k1Free6b` has a `t = 0` completion over `ℤ/qℤ`. -/
theorem free6b_net (q : ℕ) [NeZero q] (hq : Nat.Coprime q 210) :
    ∃ Φ : Fin 6 → Fin 6 → Matrix (Fin (6 * 1 - 1)) (Fin 1) (ZMod q),
      (∀ c d (r : Fin (6 * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (k1Free6b c d : ZMod q)) ∧ H2 Φ ∧
      IsNet0 6 q (6 * 1) (digPoint q (6 * 1) (graphGenK (m := 6 * 1) (fun _ => 1) Φ)) := by
  refine net_of_compl q k1Free6b
    (fun p => if p = 11 then E6b11 else if p = 13 then E6b13 else if p = 17 then E6b17 else if p = 19 then E6b19
      else A6b) fun p hp hpq => ?_
  by_cases h11 : p = 11
  · subst h11; simpa using not_dvd_of_mod k1Free6b E6b11 11 (by simpa using chk6b11)
  by_cases h13 : p = 13
  · subst h13; simpa using not_dvd_of_mod k1Free6b E6b13 13 (by simpa using chk6b13)
  by_cases h17 : p = 17
  · subst h17; simpa using not_dvd_of_mod k1Free6b E6b17 17 (by simpa using chk6b17)
  by_cases h19 : p = 19
  · subst h19; simpa using not_dvd_of_mod k1Free6b E6b19 19 (by simpa using chk6b19)
  simp only [h11, h13, h17, h19, if_false]
  refine not_dvd_of_strip k1Free6b A6b [2, 3, 5, 7, 11, 13, 17, 19]
    (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    chk6b p hp ?_
  intro hmem
  have h210 : p ∣ 210 := by
    simp at hmem
    rcases hmem with rfl | rfl | rfl | rfl | h | h | h | h <;> first | (exfalso; omega) | norm_num
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpq hq) h210)

/-- The frameless nets with the bound of `prop:k1`(1): any `Φ` as in `free5_net` etc. satisfies `δ N^{1/s} ≥ LB₁(q)`. -/
theorem free_sep {s q : ℕ} [NeZero q] (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : H2 Φ) (v w : Fin (s * 1) → ZMod q) (hvw : v ≠ w) :
    LBval q (layer1 F₀) 1 1 * ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) ≤
      Real.sqrt (∑ c, ((cres (q ^ (s * 1))
        ((digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) v c : ℤ) -
         (digPoint q (s * 1) (graphGenK (m := s * 1) (fun _ => 1) Φ) w c : ℤ)) : ℝ) /
          (q : ℝ) ^ (s * 1)) ^ 2) :=
  Z3NetF.k1_sep hs hq F₀ Φ h1 h2 v w hvw

/-- **`prop:k1designs`(1), `s = 5`**: off the diagonal the frame layer `k1Frame5` is the geometric layer of the `s = 5`
design of `tab:Kdesigns`, and the Cauchy layer `λ'_c μ_d w_cd` on the places `∞, 0, 1, 2, 3`. -/
theorem frame5_cauchy (c d : Fin 5) (hcd : c ≠ d) :
    k1Frame5 c d = kdes5F0 c d ∧
      (k1Frame5 c d : ℚ) = kdes5Lam c * kdes5Mu d * wN (0 : Fin 5) kdes5Places c d := by
  fin_cases c <;> fin_cases d <;> simp_all [k1Frame5, kdes5F0, kdes5Lam, kdes5Mu, wN, kdes5Places] <;> norm_num

theorem places5_ok : PlacesOK (0 : Fin 5) kdes5Places := by
  intro c d hc hd hcd
  rw [isUnit_iff_ne_zero, sub_ne_zero]
  fin_cases c <;> fin_cases d <;> simp_all [kdes5Places]

end Z3NetF.Proofs.K1Compl

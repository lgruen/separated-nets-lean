module
public import Z3Net.HalfDefs

@[expose] public section

/-!
# Entry Half: integer form of `ℓ` and soundness of the kernel certificates

With `b = ∑_d M2_cd E_d` (`= 2β_c`), `2p · ℓ_c(E) = hLc p (σ_E odd) E_c b` where
`hLc p odd E b = max(0, p · min(|2E+1|, |2E-1|) - |b| - 2)` for `σ_E` odd and
`max(0, min(|2pE + b|, |2pE - 2p·sgn b + b|) - 2)` for `σ_E` even (`halfEll_eq`). Hence
`n / 10⁴ ≤ |ℓ(E)|` as soon as `(2pn)² ≤ 10⁸ ∑_c hLc²` (`le_sqrt_of_cert`). Likewise
`2 ℓ^∞_c(E) = hLinf (σ_E odd) E_c b` (`halfEllInf_eq`).
-/

namespace Z3NetHL.Proofs

open Finset

/-- `2p ℓ_c(E)` as an integer (`b = 2β_c`). -/
def hLc (p : ℤ) (odd : Bool) (E b : ℤ) : ℤ :=
  if odd then max 0 (p * min |2 * E + 1| |2 * E - 1| - |b| - 2)
  else max 0 (min |2 * p * E + b| |2 * p * E - 2 * p * b.sign + b| - 2)

/-- `2 ℓ^∞_c(E)` as an integer (`b = 2β_c`). -/
def hLinf (odd : Bool) (E b : ℤ) : ℤ :=
  if odd then min |2 * E + 1| |2 * E - 1| else 2 * min |E| |E - b.sign|

/-- Parity bit of `σ_E` as used by `halfEll`. -/
def oddB {s : ℕ} (E : Fin s → ℤ) : Bool := decide ((∑ d, E d) % 2 = 1)

lemma abs_half_aux (x k : ℝ) (hk : 0 < k) : |x| = |k * x| / k := by
  rw [abs_mul, abs_of_pos hk]; field_simp

lemma max0_div_eq {X Y k : ℝ} (hk : 0 < k) (h : X = Y / k) : max 0 X = max 0 Y / k := by
  rw [h, ← max_div_div_right hk.le, zero_div]

lemma halfEll_eq {s : ℕ} (p : ℕ) (hp : 0 < p) (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ)
    (c : Fin s) :
    halfEll p M2 E c = (hLc p (oddB E) (E c) (∑ d, M2 c d * E d) : ℝ) / (2 * p) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2p : (0 : ℝ) < 2 * p := by positivity
  unfold halfEll halfBeta hLc oddB
  set b : ℤ := ∑ d, M2 c d * E d with hb
  by_cases h : (∑ d, E d) % 2 = 1
  · simp only [h, ite_true, decide_true]
    push_cast
    apply max0_div_eq h2p
    have e1 : |(E c : ℝ) + 1 / 2| = |2 * (E c : ℝ) + 1| / 2 := by
      rw [abs_half_aux _ 2 (by norm_num)]; ring_nf
    have e2 : |(E c : ℝ) - 1 / 2| = |2 * (E c : ℝ) - 1| / 2 := by
      rw [abs_half_aux _ 2 (by norm_num)]; ring_nf
    have e3 : |(b : ℝ) / 2| = |(b : ℝ)| / 2 := by rw [abs_div]; norm_num
    rw [e1, e2, e3, min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    ring
  · simp only [h, ite_false, decide_false, Bool.false_eq_true]
    push_cast
    apply max0_div_eq h2p
    have e1 : |(E c : ℝ) + (b : ℝ) / 2 / p| = |2 * p * (E c : ℝ) + b| / (2 * p) := by
      rw [abs_half_aux _ (2 * p) h2p]; congr 2; field_simp
    have e2 : |(E c : ℝ) - ((b.sign : ℤ) : ℝ) + (b : ℝ) / 2 / p|
        = |2 * p * (E c : ℝ) - 2 * p * ((b.sign : ℤ) : ℝ) + b| / (2 * p) := by
      rw [abs_half_aux _ (2 * p) h2p]; congr 2; field_simp
    rw [e1, e2, min_div_div_right h2p.le]
    field_simp

lemma sum_halfEll_sq {s : ℕ} (p : ℕ) (hp : 0 < p) (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) :
    ∑ c, halfEll p M2 E c ^ 2
      = ((∑ c, hLc p (oddB E) (E c) (∑ d, M2 c d * E d) ^ 2 : ℤ) : ℝ) / (2 * p) ^ 2 := by
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [halfEll_eq p hp, div_pow]

/-- **Soundness of one certificate entry**: `(2pn)² ≤ 10⁸ ∑ hLc²` gives `n/10⁴ ≤ |ℓ(E)|`. -/
lemma le_sqrt_of_cert {s : ℕ} (p : ℕ) (hp : 0 < p) (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ)
    (n : ℕ) (T : ℤ) (hT : T = (2 * (p : ℤ) * n) ^ 2)
    (h : T ≤ 100000000 * ∑ c, hLc p (oddB E) (E c) (∑ d, M2 c d * E d) ^ 2) :
    (n : ℝ) / 10 ^ 4 ≤ Real.sqrt (∑ c, halfEll p M2 E c ^ 2) := by
  subst hT
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  apply Real.le_sqrt_of_sq_le
  rw [sum_halfEll_sq p hp, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have h' := (Int.cast_le (R := ℝ)).2 h
  push_cast at h' ⊢
  nlinarith [h']

/-- Upper bound: `∑ hLc² < (2p)²` gives `|ℓ(E)| < 1`. -/
lemma sqrt_lt_one_of_cert {s : ℕ} (p : ℕ) (hp : 0 < p) (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ)
    (h : ∑ c, hLc p (oddB E) (E c) (∑ d, M2 c d * E d) ^ 2 < (2 * (p : ℤ)) ^ 2) :
    Real.sqrt (∑ c, halfEll p M2 E c ^ 2) < 1 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Real.sqrt_lt' one_pos, sum_halfEll_sq p hp, one_pow, div_lt_one (by positivity)]
  exact_mod_cast h

lemma halfEllInf_eq {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (c : Fin s) :
    halfEllInf M2 E c = (hLinf (oddB E) (E c) (∑ d, M2 c d * E d) : ℝ) / 2 := by
  unfold halfEllInf hLinf oddB
  by_cases h : (∑ d, E d) % 2 = 1
  · simp only [h, ite_true, decide_true]
    push_cast
    have e1 : |(E c : ℝ) + 1 / 2| = |2 * (E c : ℝ) + 1| / 2 := by
      rw [abs_half_aux _ 2 (by norm_num)]; ring_nf
    have e2 : |(E c : ℝ) - 1 / 2| = |2 * (E c : ℝ) - 1| / 2 := by
      rw [abs_half_aux _ 2 (by norm_num)]; ring_nf
    rw [e1, e2, min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
  · simp only [h, ite_false, decide_false, Bool.false_eq_true]
    push_cast
    ring

lemma sum_halfEllInf_sq {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) :
    ∑ c, halfEllInf M2 E c ^ 2
      = ((∑ c, hLinf (oddB E) (E c) (∑ d, M2 c d * E d) ^ 2 : ℤ) : ℝ) / 4 := by
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [halfEllInf_eq, div_pow]
  norm_num

/-- Soundness for `λ`: `n ≤ ∑ (2ℓ^∞)²` gives `√n / 2 ≤ |ℓ^∞(E)|`. -/
lemma le_sqrt_inf_of_cert {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (n : ℕ)
    (h : (n : ℤ) ≤ ∑ c, hLinf (oddB E) (E c) (∑ d, M2 c d * E d) ^ 2) :
    Real.sqrt n / 2 ≤ Real.sqrt (∑ c, halfEllInf M2 E c ^ 2) := by
  rw [sum_halfEllInf_sq, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  gcongr
  exact_mod_cast h

/-! ## Enumeration ranges -/

def vals5 : List ℤ := [-2, -1, 0, 1, 2]
def vals3 : List ℤ := [-1, 0, 1]

lemma mem_vals5 (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ vals5 := by
  unfold vals5; interval_cases x <;> simp

lemma mem_vals3 (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ vals3 := by
  unfold vals3; interval_cases x <;> simp

lemma forall_vals5 {P : ℤ → Prop} (a : P (-2)) (b : P (-1)) (c : P 0) (d : P 1) (e : P 2) :
    ∀ x ∈ vals5, P x := by
  intro x hx; simp only [vals5, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h <;> subst h <;> assumption

lemma forall_vals3 {P : ℤ → Prop} (b : P (-1)) (c : P 0) (d : P 1) : ∀ x ∈ vals3, P x := by
  intro x hx; simp only [vals3, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h <;> subst h <;> assumption

lemma halfSteps_mem {s : ℕ} {E : Fin s → ℤ} (hE : E ∈ halfSteps s) :
    E ≠ 0 ∧ ∀ c, -2 ≤ E c ∧ E c ≤ 2 := by
  simp only [halfSteps, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hE
  exact ⟨hE.2, hE.1⟩

end Z3NetHL.Proofs

module
public import Mathlib
public import Z3Net.S1Defs

@[expose] public section

/-!
# Entry S1, part 1: Lemma L2_s

`Λ = {(x, z) : z ≡ ∑_i ρ^(i+1) x_i (mod p)}`; if `ρ^s < p` every nonzero vector has sup-norm `≥ ρ`.
Proof (note §3.1): if all entries are `< ρ` in absolute value, the relation is exact
(`|z - ∑| ≤ ρ^s - 1 < p`), and peeling `ρ`-divisibility from the left gives `0`.
-/

namespace Z3NetS1.Proofs

open Finset

/-- Exact relation with small entries forces zero (induction on the number of `x`'s). -/
lemma peel (ρ : ℤ) : ∀ (n : ℕ) (x : Fin n → ℤ) (z : ℤ), (∀ i, |x i| < ρ) → |z| < ρ →
    z = ∑ i : Fin n, ρ ^ ((i : ℕ) + 1) * x i → z = 0 ∧ ∀ i, x i = 0 := by
  intro n
  induction n with
  | zero => intro x z _ _ h; simp at h; exact ⟨h, fun i => i.elim0⟩
  | succ n ih =>
    intro x z hx hz h
    rw [Fin.sum_univ_succ] at h
    have hS : ∑ i : Fin n, ρ ^ ((i.succ : ℕ) + 1) * x i.succ =
        ρ * ∑ i : Fin n, ρ ^ ((i : ℕ) + 1) * x i.succ := by
      rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; simp [pow_succ]; ring
    rw [hS] at h
    have hρ : 0 < ρ := lt_of_le_of_lt (abs_nonneg z) hz
    have hdvd : ρ ∣ z := ⟨x 0 + ∑ i : Fin n, ρ ^ ((i : ℕ) + 1) * x i.succ, by rw [h]; simp; ring⟩
    have z0 : z = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hz
    have h2 : -x 0 = ∑ i : Fin n, ρ ^ ((i : ℕ) + 1) * x i.succ := by
      rw [z0] at h
      simp at h
      have : ρ * (x 0 + ∑ i : Fin n, ρ ^ ((i : ℕ) + 1) * x i.succ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · omega
      · linarith
    obtain ⟨h0, hs⟩ := ih (fun i => x i.succ) (-x 0) (fun i => hx _) (by rw [abs_neg]; exact hx 0) h2
    refine ⟨z0, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => hs j) i
    linarith

/-- `|∑_{i<n} ρ^(i+1) x_i| ≤ ρ^(n+1) - ρ` when every `|x_i| ≤ ρ - 1`. -/
lemma sum_bound (ρ : ℤ) (hρ : 1 ≤ ρ) (n : ℕ) (x : Fin n → ℤ) (hx : ∀ i, |x i| ≤ ρ - 1) :
    |∑ i : Fin n, ρ ^ ((i : ℕ) + 1) * x i| ≤ ρ ^ (n + 1) - ρ := by
  calc |∑ i : Fin n, ρ ^ ((i : ℕ) + 1) * x i| ≤ ∑ i : Fin n, |ρ ^ ((i : ℕ) + 1) * x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ρ ^ ((i : ℕ) + 1) * (ρ - 1) := by
        refine sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hx i) (by positivity)
    _ = ρ * ((∑ i ∈ range n, ρ ^ i) * (ρ - 1)) := by
        rw [Fin.sum_univ_eq_sum_range (fun i => ρ ^ (i + 1) * (ρ - 1)), sum_mul, mul_sum]
        refine sum_congr rfl fun i _ => by ring
    _ = ρ ^ (n + 1) - ρ := by rw [geom_sum_mul]; ring

/-- **Lemma L2_s, lower bound.** -/
theorem L2s_min (s p ρ : ℕ) (hs : 1 ≤ s) (hρp : ρ ^ s < p) (x : Fin (s - 1) → ℤ) (z : ℤ)
    (hdiv : (p : ℤ) ∣ z - ∑ i : Fin (s - 1), (ρ : ℤ) ^ ((i : ℕ) + 1) * x i) (hne : ¬(x = 0 ∧ z = 0)) :
    (ρ : ℤ) ≤ |z| ∨ ∃ i : Fin (s - 1), (ρ : ℤ) ≤ |x i| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hz, hx⟩ := hcon
  have hz0' := abs_nonneg z
  have hρ1 : (1 : ℤ) ≤ ρ := by omega
  have hx' : ∀ i, |x i| ≤ (ρ : ℤ) - 1 := fun i => by
    have := hx i
    omega
  have hb := sum_bound (ρ : ℤ) hρ1 (s - 1) x hx'
  have hpow : (ρ : ℤ) ^ (s - 1 + 1) < p := by
    rw [Nat.sub_add_cancel hs]; exact_mod_cast hρp
  have hlt : |z - ∑ i : Fin (s - 1), (ρ : ℤ) ^ ((i : ℕ) + 1) * x i| < p := by
    have := abs_sub z (∑ i : Fin (s - 1), (ρ : ℤ) ^ ((i : ℕ) + 1) * x i)
    linarith
  have h0 := Int.eq_zero_of_abs_lt_dvd hdiv hlt
  obtain ⟨hz0, hx0⟩ := peel (ρ : ℤ) (s - 1) x z hx hz (by linarith)
  exact hne ⟨funext hx0, hz0⟩

/-- **Lemma L2_s, attained.** -/
theorem L2s_attained (s p ρ : ℕ) (hs : 2 ≤ s) (hρ : 1 ≤ ρ) :
    ∃ x : Fin (s - 1) → ℤ, ∃ z : ℤ,
      (p : ℤ) ∣ z - ∑ i : Fin (s - 1), (ρ : ℤ) ^ ((i : ℕ) + 1) * x i ∧
      ¬(x = 0 ∧ z = 0) ∧ |z| ≤ ρ ∧ ∀ i : Fin (s - 1), |x i| ≤ ρ := by
  have h0 : 0 < s - 1 := by omega
  refine ⟨fun i => if (i : ℕ) = 0 then 1 else 0, ρ, ?_, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single ⟨0, h0⟩]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  · rintro ⟨hx, -⟩
    have := congrFun hx ⟨0, h0⟩
    simp at this
  · simp
  · intro i
    show |(if (i : ℕ) = 0 then (1 : ℤ) else 0)| ≤ ρ
    split_ifs <;> simp <;> omega
end Z3NetS1.Proofs

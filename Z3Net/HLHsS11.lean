/-
Proof module (stage 11, entry HLHL8): `lem:Hs` (half-integer designs) as compared statements.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.HLMainH

@[expose] public section

/-!
# Stage 11 additions to entry HLHL8

* `HL_halfDesign` (`lem:Hs`, general part): for even `u_c`, odd `v_d`, `λ'_c = Λ_c/2` and
  `g_{d,j} = 1 + 2y^j`, the partial sums `M^(j)[c][d]` (`c ≠ d`, `j ≤ s-2`) equal
  `Λ_c/(2ϑ_cd) + [j ≥ 1] Λ_c/ϑ_cd^(j+1)`, lie in `½ + ℤ`, and `F_j[c][d] ∈ ℤ` for `j ≥ 1`;
* `HL_Hs` (`lem:Hs` for `H_s`): every prime `q ≥ 2s` is admissible (`HLAdm`, `HLDen`), and the
  completed design is half-integer (`2F_0` odd, `2F_x` even for `x ≥ 1`), from `HLMainH`.
-/

namespace Z3NetHL.Proofs

open Finset

noncomputable section

/-- The inner sum `∑_{n' ≤ n} f_{d,n,n'} y^(n'+1)` for `gcoH`. -/
lemma gcoH_inner {s : ℕ} (d : Fin s) (y : ℚ) (n : ℕ) :
    ∑ n' ∈ range (n + 1), gcoH d n n' * y ^ (n' + 1) =
      if n = 0 then y else if n = 1 then 2 * y ^ 2 else 2 * y ^ (n + 1) - 2 * y ^ n := by
  rcases n with _ | m
  · simp [gcoH]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : ∑ n' ∈ range m, gcoH d (m + 1) n' * y ^ (n' + 1) = 0 := by
    refine Finset.sum_eq_zero fun n' hn' => ?_
    rw [mem_range] at hn'
    have h1 : m + 1 ≠ 0 := by omega
    have h2 : n' ≠ m + 1 := by omega
    have h3 : ¬ (n' + 1 = m + 1 ∧ 2 ≤ m + 1) := by omega
    simp [gcoH, h1, h2]
    intro h; exact absurd h (by omega)
  rw [h0]
  rcases m with _ | m
  · simp [gcoH]
  · have h1 : m + 1 + 1 ≠ 0 := by omega
    have h2 : m + 1 ≠ m + 1 + 1 := by omega
    have h3 : (m + 1 + 1 = m + 1 + 1 ∧ 2 ≤ m + 1 + 1) := ⟨rfl, by omega⟩
    have h4 : m + 1 + 1 ≠ 1 := by omega
    simp only [gcoH, h1, h2, h3, h4, if_false, if_true, and_self]
    ring

/-- Telescoping: `∑_{n ≤ j} ∑_{n' ≤ n} f_{d,n,n'} y^(n'+1) = y + [j ≥ 1] 2y^(j+1)`. -/
lemma gcoH_partial {s : ℕ} (d : Fin s) (y : ℚ) (j : ℕ) :
    ∑ n ∈ range (j + 1), ∑ n' ∈ range (n + 1), gcoH d n n' * y ^ (n' + 1) =
      y + (if j = 0 then 0 else 2 * y ^ (j + 1)) := by
  induction j with
  | zero => simp [gcoH]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, gcoH_inner]
    rcases j with _ | j
    · simp
    · have h1 : j + 1 + 1 ≠ 0 := by omega
      have h2 : j + 1 + 1 ≠ 1 := by omega
      have h3 : j + 1 ≠ 0 := by omega
      simp only [h1, h2, h3, if_false]
      ring

theorem HL_halfDesign (s : ℕ) (u v : Fin s → ℤ) (hu : ∀ c, Even (u c)) (hv : ∀ d, Odd (v d))
    (dg : Fin s → ℕ → ℚ) (c d : Fin s) (hcd : c ≠ d) (j : ℕ) (hj : j ≤ s - 2) :
    let Λ : Fin s → ℚ := fun c' => ∏ d' ∈ univ.erase c', ((u c' - v d' : ℤ) : ℚ) ^ (s - 1)
    let θ : ℚ := ((u c - v d : ℤ) : ℚ)
    let M := ∑ n ∈ range (j + 1), HLdes u v (fun c' => Λ c' / 2) gcoH dg n c d
    M = Λ c / (2 * θ) + (if j = 0 then 0 else Λ c / θ ^ (j + 1)) ∧ (∃ z : ℤ, M = z + 1 / 2) ∧
      (1 ≤ j → ∃ z : ℤ, HLdes u v (fun c' => Λ c' / 2) gcoH dg j c d = z) := by
  intro Λ θ M
  have hs : 2 ≤ s := by
    have := c.isLt; have := d.isLt
    have : (c : ℕ) ≠ d := fun h => hcd (Fin.ext h)
    omega
  have hodd : ∀ d', Odd (u c - v d') := fun d' => by
    obtain ⟨a, ha⟩ := hu c; obtain ⟨b, hb⟩ := hv d'
    exact ⟨a - b - 1, by rw [ha, hb]; ring⟩
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = u c - v d := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = ∏ d' ∈ (univ.erase c).erase d, (u c - v d') ^ (s - 1) := ⟨_, rfl⟩
  have hQodd : Odd Q := by
    rw [hQ]
    exact Finset.prod_induction _ (fun z => Odd z) (fun a b ha hb => ha.mul hb) odd_one
      fun d' _ => (hodd d').pow
  have heodd : Odd e := he ▸ hodd d
  have he0 : (e : ℚ) ≠ 0 := by
    have : e ≠ 0 := fun h => by rw [h] at heodd; exact absurd heodd (by decide)
    exact_mod_cast this
  have hθ : θ = (e : ℚ) := by simp only [θ, he]
  have hΛ : Λ c = (e : ℚ) ^ (s - 1) * (Q : ℚ) := by
    simp only [Λ, hQ, he]
    rw [← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨Ne.symm hcd, mem_univ d⟩)]
    push_cast; rfl
  have hpow : ∀ i, i ≤ s - 1 → Λ c / θ ^ i = ((Q * e ^ (s - 1 - i) : ℤ) : ℚ) := fun i hi => by
    rw [hΛ, hθ]
    have : (e : ℚ) ^ (s - 1) = (e : ℚ) ^ (s - 1 - i) * (e : ℚ) ^ i := by
      rw [← pow_add]; congr 1; omega
    rw [this]; push_cast
    field_simp
  have hdes : ∀ n, n < s - 1 → HLdes u v (fun c' => Λ c' / 2) gcoH dg n c d =
      Λ c / 2 * ∑ n' ∈ range (n + 1), gcoH d n n' * θ⁻¹ ^ (n' + 1) := fun n hn => by
    simp only [HLdes, if_neg (show ¬ s - 1 ≤ n by omega), if_neg hcd, yQ, θ]
  have hM : M = Λ c / (2 * θ) + (if j = 0 then 0 else Λ c / θ ^ (j + 1)) := by
    simp only [M]
    rw [Finset.sum_congr rfl fun n hn => hdes n (by rw [mem_range] at hn; omega), ← Finset.mul_sum,
      gcoH_partial]
    rw [hθ]
    split_ifs
    · field_simp; ring
    · simp only [inv_pow]; field_simp
  refine ⟨hM, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hQodd.mul (heodd.pow (n := s - 1 - 1))
    have h1 : Λ c / (2 * θ) = (t : ℚ) + 1 / 2 := by
      have := hpow 1 (by omega)
      rw [pow_one] at this
      rw [div_mul_eq_div_div_swap, this, ht]
      push_cast; ring
    rw [hM, h1]
    split_ifs
    · exact ⟨t, by ring⟩
    · refine ⟨t + Q * e ^ (s - 1 - (j + 1)), ?_⟩
      rw [hpow (j + 1) (by omega)]
      push_cast; ring
  · intro hj1
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hdes _ (by omega), gcoH_inner]
    rcases j' with _ | j''
    · refine ⟨Q * e ^ (s - 1 - 2), ?_⟩
      rw [← hpow 2 (by omega), hθ]
      simp only [show (0 + 1 : ℕ) ≠ 0 by omega, if_false, if_true]
      field_simp
    · refine ⟨Q * e ^ (s - 1 - (j'' + 1 + 1 + 1)) - Q * e ^ (s - 1 - (j'' + 1 + 1)), ?_⟩
      have h1 := hpow (j'' + 1 + 1 + 1) (by omega)
      have h2 := hpow (j'' + 1 + 1) (by omega)
      push_cast at h1 h2 ⊢
      rw [← h1, ← h2, hθ]
      simp only [inv_pow, div_eq_mul_inv]; ring

theorem HL_Hs (s q : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q) :
    HLAdm s q uH vH (lamH s) gcoH ∧ HLDen s q gcoH (dgH s) ∧ ∀ x c d, ∃ z : ℤ,
      2 * HLdes uH vH (lamH s) gcoH (dgH s) x c d = z ∧ (x = 0 → Odd z) ∧ (1 ≤ x → Even z) :=
  ⟨adm_H hs q hq hqs, den_H q hq (by omega), fun x c d => ⟨F2Hf s x c d, hF2_H x c d,
    fun hx => hx ▸ F2Hf_half0 hs c d, fun hx => F2Hf_half x c d hx⟩⟩

end

end Z3NetHL.Proofs

namespace Z3NetHL

open Finset

/-- **`lem:Hs`** (half-integer designs): `u_c` even, `v_d` odd, `λ'_c = Λ_c/2`, `g_{d,j} = 1 + 2y^j`
(`gcoH`), `c ≠ d`, `j ≤ s-2`: `M^(j)[c][d] = Λ_c/(2ϑ_cd) + [j ≥ 1] Λ_c/ϑ_cd^(j+1) ∈ ½ + ℤ`, `F_j ∈ ℤ` (`j ≥ 1`). -/
theorem HL_halfDesign (s : ℕ) (u v : Fin s → ℤ) (hu : ∀ c, Even (u c)) (hv : ∀ d, Odd (v d))
    (dg : Fin s → ℕ → ℚ) (c d : Fin s) (hcd : c ≠ d) (j : ℕ) (hj : j ≤ s - 2) :
    let Λ : Fin s → ℚ := fun c' => ∏ d' ∈ univ.erase c', ((u c' - v d' : ℤ) : ℚ) ^ (s - 1)
    let θ : ℚ := ((u c - v d : ℤ) : ℚ)
    let M := ∑ n ∈ range (j + 1), HLdes u v (fun c' => Λ c' / 2) gcoH dg n c d
    M = Λ c / (2 * θ) + (if j = 0 then 0 else Λ c / θ ^ (j + 1)) ∧ (∃ z : ℤ, M = z + 1 / 2) ∧
      (1 ≤ j → ∃ z : ℤ, HLdes u v (fun c' => Λ c' / 2) gcoH dg j c d = z) :=
  Proofs.HL_halfDesign s u v hu hv dg c d hcd j hj

/-- **`lem:Hs`** for `H_s` (`s ≥ 2`): every prime `q ≥ 2s` is admissible (the primes of `DD'` are
`≤ 2s - 1`), and the completed design is half-integer: `2F_x` integral, odd at `x = 0`, even at `x ≥ 1`. -/
theorem HL_Hs (s q : ℕ) (hs : 2 ≤ s) (hq : q.Prime) (hqs : 2 * s ≤ q) :
    HLAdm s q uH vH (lamH s) gcoH ∧ HLDen s q gcoH (dgH s) ∧ ∀ x c d, ∃ z : ℤ,
      2 * HLdes uH vH (lamH s) gcoH (dgH s) x c d = z ∧ (x = 0 → Odd z) ∧ (1 ≤ x → Even z) :=
  Proofs.HL_Hs s q hs hq hqs

end Z3NetHL

module
public import Mathlib
public import Z3Net.HalfLam
public import Z3Net.HLGFDom
public import Z3Net.HLGFUp

@[expose] public section

/-!
# Entry Half, part 2: separation, upper bound and limit (`prop:half`(1), `prop:Hk`(3) at `k = 1`)

* `halfPhi_row` — `halfPhi` has row `0` equal to the layer (`2 · (p+1)/2 = p + 1 ≡ 1`).
* `half_sep` — `GF_relax_core` at `k = 1`, `F2 = fun _ => M2`: the carry lengths are `0`, so
  `sig2 = ∑_d M2_cd E_d = 2β_c`, and each per-option bound dominates `2p ℓ_c(E)`
  (`opt_bound_odd`, `opt_bound_even`).
* `half_upper` — `GF_upper_core` at `k = 1`.
* `half_limit` — from `half_sep`, `half_LB2_ge` and `half_upper`.
-/

namespace Z3NetHL.Proofs

open Finset Matrix

noncomputable section

/-! ## Row `0` -/

theorem halfPhi_row (s p : ℕ) (hs : 2 ≤ s) (hp : Odd p) (M2 : Fin s → Fin s → ℤ)
    (D : Fin s → ℕ → Fin s → ℤ) :
    RowDesign s p 1 (halfPhi s p M2 D) (fun _ => M2) := by
  intro c d r hr j
  have hj : (j : ℕ) = 0 := by omega
  simp only [halfPhi, hr, ↓reduceIte]
  rw [if_pos (by omega : 1 - 1 - (j : ℕ) < s - 1)]
  obtain ⟨t, ht⟩ := hp
  have h2 : (p + 1) / 2 = t + 1 := by omega
  rw [h2]
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  calc (2 : ZMod p) * ((M2 c d : ZMod p) * ((t + 1 : ℕ) : ZMod p))
      = (M2 c d : ZMod p) * ((2 * t + 1 : ℕ) : ZMod p) + M2 c d := by push_cast; ring
    _ = M2 c d := by rw [← ht, hp0, mul_zero, zero_add]

/-! ## The per-option bounds -/

lemma sig2_half {s : ℕ} (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ) (J : Fin s → ℕ)
    (hJ : ∀ d, J d = 0) (c : Fin s) : sig2 (fun _ => M2) E J c = ∑ d, M2 c d * E d := by
  unfold sig2
  refine sum_congr rfl fun d _ => ?_
  rw [hJ d, Finset.Icc_eq_empty_of_lt (by norm_num), sum_empty, mul_zero, add_zero, mul_comm]

lemma opt_bound_odd (P e σ : ℝ) (hP : 0 < P) :
    2 * P * (min |e + 1 / 2| |e - 1 / 2| - (|σ / 2| + 1) / P) ≤
      min (max 0 (|2 * P * e + σ + P| - 2)) (max 0 (|2 * P * e + σ - P| - 2)) := by
  have hm : 2 * P * (min |e + 1 / 2| |e - 1 / 2| - (|σ / 2| + 1) / P) =
      2 * P * min |e + 1 / 2| |e - 1 / 2| - |σ| - 2 := by
    rw [abs_div, abs_two]; field_simp; ring
  rw [hm]
  have hP2 : 0 < 2 * P := by linarith
  have e1 : 2 * P * |e + 1 / 2| = |2 * P * e + P| := by
    rw [show 2 * P * e + P = (2 * P) * (e + 1 / 2) by ring, abs_mul, abs_of_pos hP2]
  have e2 : 2 * P * |e - 1 / 2| = |2 * P * e - P| := by
    rw [show 2 * P * e - P = (2 * P) * (e - 1 / 2) by ring, abs_mul, abs_of_pos hP2]
  have t1 : |2 * P * e + P| - |σ| ≤ |2 * P * e + σ + P| := by
    have := abs_add_le (2 * P * e + σ + P) (-σ)
    rw [show 2 * P * e + σ + P + -σ = 2 * P * e + P by ring, abs_neg] at this
    linarith
  have t2 : |2 * P * e - P| - |σ| ≤ |2 * P * e + σ - P| := by
    have := abs_add_le (2 * P * e + σ - P) (-σ)
    rw [show 2 * P * e + σ - P + -σ = 2 * P * e - P by ring, abs_neg] at this
    linarith
  have m1 := mul_le_mul_of_nonneg_left (min_le_left |e + 1 / 2| |e - 1 / 2|) hP2.le
  have m2 := mul_le_mul_of_nonneg_left (min_le_right |e + 1 / 2| |e - 1 / 2|) hP2.le
  refine le_min (le_trans ?_ (le_max_right _ _)) (le_trans ?_ (le_max_right _ _)) <;> linarith

lemma opt_bound_even (P e σ κ : ℝ) (hP : 0 < P) :
    2 * P * (min |e + σ / 2 / P| |e - κ + σ / 2 / P| - 1 / P) ≤
      min (max 0 (|2 * P * e + σ| - 2)) (max 0 (|2 * P * e + σ - 2 * P * κ| - 2)) := by
  have hP2 : 0 < 2 * P := by linarith
  have hm : 2 * P * (min |e + σ / 2 / P| |e - κ + σ / 2 / P| - 1 / P) =
      2 * P * min |e + σ / 2 / P| |e - κ + σ / 2 / P| - 2 := by
    field_simp
  rw [hm]
  have e1 : 2 * P * |e + σ / 2 / P| = |2 * P * e + σ| := by
    rw [show 2 * P * e + σ = (2 * P) * (e + σ / 2 / P) by field_simp, abs_mul, abs_of_pos hP2]
  have e2 : 2 * P * |e - κ + σ / 2 / P| = |2 * P * e + σ - 2 * P * κ| := by
    rw [show 2 * P * e + σ - 2 * P * κ = (2 * P) * (e - κ + σ / 2 / P) by field_simp; ring,
      abs_mul, abs_of_pos hP2]
  have m1 := mul_le_mul_of_nonneg_left (min_le_left |e + σ / 2 / P| |e - κ + σ / 2 / P|) hP2.le
  have m2 := mul_le_mul_of_nonneg_left (min_le_right |e + σ / 2 / P| |e - κ + σ / 2 / P|) hP2.le
  refine le_min (le_trans ?_ (le_max_right _ _)) (le_trans ?_ (le_max_right _ _)) <;> linarith

/-- `2p ℓ_c(E) ≤ b_c` for carry lengths `0`. -/
lemma two_p_ell_le_bOpt2 {s : ℕ} (p : ℕ) (hp : 0 < p) (M2 : Fin s → Fin s → ℤ) (E : Fin s → ℤ)
    (J : Fin s → ℕ) (hJ : ∀ d, J d = 0) (c : Fin s) :
    2 * (p : ℝ) * halfEll p M2 E c ≤ ((bOpt2 p (fun _ => M2) E J c : ℤ) : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hb0 : (0 : ℝ) ≤ ((bOpt2 p (fun _ => M2) E J c : ℤ) : ℝ) := by
    exact_mod_cast bOpt2_nonneg p _ E J c
  unfold halfEll
  rw [mul_max_of_nonneg _ _ (by positivity), mul_zero]
  refine max_le hb0 ?_
  unfold bOpt2 halfBeta
  rw [sig2_half M2 E J hJ c]
  generalize (∑ d, M2 c d * E d) = σ2
  generalize Int.sign σ2 = κ
  split_ifs with h
  · have := opt_bound_odd p (E c) σ2 hp0
    push_cast
    exact this
  · have := opt_bound_even p (E c) σ2 κ hp0
    push_cast
    exact this

/-! ## `prop:half`(1): separation -/

theorem half_sep (s p : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hp2 : p ≠ 2)
    (M2 : Fin s → Fin s → ℤ) (hodd : ∀ c d, Odd (M2 c d)) (hpA : 2 * halfA2 M2 + 2 < p)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod p))
    (hrow : RowDesign s p 1 Φ (fun _ => M2)) (x y : Fin (s * 1) → ZMod p) (hxy : x ≠ y) :
    halfLB2 p M2 * ((p : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * 1))
          ((GFpoint s p 1 Φ x c : ℤ) - (GFpoint s p 1 Φ y c : ℤ)) : ℝ) / (p : ℝ) ^ (s * 1)) ^ 2) := by
  have hqodd : Odd p := hp.odd_of_ne_two hp2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine GF_relax_core s p 1 Φ (fun _ => M2) hs hqodd le_rfl hrow (fun c d => hodd c d)
    (fun x c d h1 h2 => by omega) ?_ (halfLB2 p M2) ?_ x y hxy
  · intro E J c hE hJ
    rw [sig2_half M2 E J (fun d => by have := hJ d; omega) c]
    have h1 := abs_beta2_le M2 E hE c
    have h2 : (2 * halfA2 M2 + 2 : ℤ) < p := by exact_mod_cast hpA
    linarith
  · intro E J hE hne hJ
    have hJ0 : ∀ d, J d = 0 := fun d => by have := hJ d; omega
    have hmem : E ∈ halfSteps s := by
      refine mem_halfSteps.mpr ⟨hE, fun h => ?_⟩
      obtain ⟨d, hd⟩ := hne
      exact hd (by rw [h]; rfl)
    refine le_min (min_le_left _ _) ((halfLB2_le_of p M2 E hmem).trans ?_)
    rw [le_div_iff₀ (by positivity)]
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt (sum_nonneg fun c _ => sq_nonneg _), sum_mul]
    refine sum_le_sum fun c _ => ?_
    have h := two_p_ell_le_bOpt2 p hp.pos M2 E J hJ0 c
    have h0 : 0 ≤ 2 * (p : ℝ) * halfEll p M2 E c := by
      have := ell_nonneg p M2 E c; positivity
    calc halfEll p M2 E c ^ 2 * (2 * (p : ℝ)) ^ 2 = (2 * (p : ℝ) * halfEll p M2 E c) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ h0 h 2

/-! ## The matching upper bound and the limit -/

theorem half_upper (s p : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (M2 : Fin s → Fin s → ℤ)
    (hodd : ∀ c d, Odd (M2 c d)) (hpC : 2 * s * C2max s (fun _ => M2) + 2 < p)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod p))
    (hrow : RowDesign s p 1 Φ (fun _ => M2)) :
    ∃ x y : Fin (s * 1) → ZMod p, x ≠ y ∧
      Real.sqrt (∑ c, (((GFpoint s p 1 Φ x c : ℝ) - (GFpoint s p 1 Φ y c : ℝ)) / (p : ℝ) ^ (s * 1)) ^ 2)
        ≤ (min (Real.sqrt s / 2) (Real.sqrt 2) + Real.sqrt s * ((C2max s (fun _ => M2) : ℝ) + 1) / p) *
          ((p : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) :=
  GF_upper_core s p 1 Φ (fun _ => M2) hs hp le_rfl hrow (fun c d => hodd c d) hpC

theorem half_limit (s : ℕ) (hs : 3 ≤ s) (M2 : Fin s → Fin s → ℤ) (hodd : ∀ c d, Odd (M2 c d))
    (hlam : halfLam M2 = min (Real.sqrt s / 2) (Real.sqrt 2)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      ∀ Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod p),
        RowDesign s p 1 Φ (fun _ => M2) →
        (∀ x y : Fin (s * 1) → ZMod p, x ≠ y →
          (min (Real.sqrt s / 2) (Real.sqrt 2) - ε) * ((p : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ)))
            ≤ Real.sqrt (∑ c, ((cres (p ^ (s * 1))
                ((GFpoint s p 1 Φ x c : ℤ) - (GFpoint s p 1 Φ y c : ℤ)) : ℝ) / (p : ℝ) ^ (s * 1)) ^ 2)) ∧
        ∃ x y : Fin (s * 1) → ZMod p, x ≠ y ∧
          Real.sqrt (∑ c, (((GFpoint s p 1 Φ x c : ℝ) - (GFpoint s p 1 Φ y c : ℝ)) / (p : ℝ) ^ (s * 1)) ^ 2)
            ≤ (min (Real.sqrt s / 2) (Real.sqrt 2) + ε) * ((p : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) := by
  set A : ℕ := halfA2 M2 with hA
  set C : ℕ := C2max s (fun _ => M2) with hC
  set T : ℕ := 2 * s * C with hT
  set K : ℝ := Real.sqrt s * ((A : ℝ) + 1 + (C : ℝ) + 1) / ε with hK
  refine ⟨⌈K⌉₊ + 2 * A + T + 3, fun p hp hP Φ hrow => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hKp : K ≤ p := by
    have := Nat.le_ceil K
    have : (⌈K⌉₊ : ℝ) ≤ p := by exact_mod_cast (show ⌈K⌉₊ ≤ p by omega)
    linarith
  have hKe : Real.sqrt s * ((A : ℝ) + 1 + (C : ℝ) + 1) ≤ ε * p := by
    have := mul_le_mul_of_nonneg_left hKp hε.le
    rw [hK, mul_div_cancel₀ _ hε.ne'] at this
    exact this
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hNp : (0 : ℝ) < ((p : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) := by positivity
  constructor
  · intro x y hxy
    have h := half_sep s p hs hp (by omega) M2 hodd (by omega) Φ hrow x y hxy
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hNp.le) h
    have h2 := half_LB2_ge s p (by omega) (by omega) M2
    rw [hlam] at h2
    have h3 : Real.sqrt s * ((A : ℝ) + 1) / p ≤ ε := by
      rw [div_le_iff₀ hp0]
      nlinarith [mul_nonneg hsq hC0]
    linarith
  · obtain ⟨x, y, hxy, h⟩ := half_upper s p hs hp M2 hodd
      (by have : 2 * s * C2max s (fun _ => M2) = T := rfl; omega) Φ hrow
    refine ⟨x, y, hxy, h.trans (mul_le_mul_of_nonneg_right ?_ hNp.le)⟩
    have h3 : Real.sqrt s * ((C : ℝ) + 1) / p ≤ ε := by
      rw [div_le_iff₀ hp0]
      nlinarith [mul_nonneg hsq hA0]
    linarith

end

end Z3NetHL.Proofs

module
public import Mathlib
public import Z3Net.Defs
public import Z3Net.Two

@[expose] public section

/-!
# Theorem 2 (`thm:two`), separation part, for every integer base `q ≥ 11`

The separation proof of `Z3Net/Two.lean` uses the primality of `p` only through `1 < p`
(`main_bound`: `have hp1 : 1 < p := hp.one_lt`); every other ingredient (graph-form cells,
the first two offset rows `cor:rows` as integer identities reduced mod `p`, the carry lemma,
the kernel-checked case analysis `key_ineq`, valid for all integers `p ≥ 11`) works over
`ℤ/qℤ` for any `q`.  This file restates `main_bound` with the hypothesis `11 ≤ q` only
(proof verbatim, `hp.one_lt` replaced by `omega`) and derives `Q_sep_ge11`, `Q_sep_real_ge11`
(every `q ≥ 11`, even `q` included) and the odd-`q` forms `Q_sep_odd`, `Q_sep_real_odd`.
For even `q` the point set is in general not a net (`k ≥ 3`); the separation bound still holds.
-/

namespace Z3Net.Two

open Finset

noncomputable section

variable (p : ℕ) [NeZero p]

theorem main_bound_ge11 (hp11 : 11 ≤ p) (k : ℕ) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod p) (hvw : v ≠ w) :
    (p : ℤ) ^ (4 * k) * ((p : ℤ) ^ 2 * ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 2) ^ 2)
      ≤ (p : ℤ) ^ 4 * ∑ c : Fin 3,
          ((cres (p ^ (3 * k)) ((Qpoint p k w c : ℤ) - (Qpoint p k v c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  have hp1 : 1 < p := by omega
  have hpz : (11 : ℤ) ≤ p := by exact_mod_cast hp11
  set u : ℤ := (p : ℤ) ^ (2 * k - 2) with hu_def
  have hu : 0 < u := by positivity
  have hpow : (p : ℤ) ^ (2 * k) = u * (p : ℤ) ^ 2 := by rw [hu_def, ← pow_add]; congr 1; omega
  have hN : ((p ^ (3 * k) : ℕ) : ℤ) = (p : ℤ) ^ (2 * k) * (p : ℤ) ^ k := by
    push_cast; rw [← pow_add]; congr 1; omega
  have hX : ∀ c, (Qpoint p k w c : ℤ) - Qpoint p k v c =
      (p : ℤ) ^ (2 * k) * ((cellN p k w c : ℤ) - cellN p k v c) +
      (u * ((p : ℤ) * ((o0 p k w c : ℤ) - o0 p k v c) + ((o1 p k w c : ℤ) - o1 p k v c)) +
        ((tl p k w c : ℤ) - tl p k v c)) := by
    intro c; rw [X_decomp p k hk, X_decomp p k hk]; ring
  have htl : ∀ c, |(tl p k w c : ℤ) - tl p k v c| < u := by
    intro c
    have h1 := tail_lt p k (by omega) (Dg p k c w); have h2 := tail_lt p k (by omega) (Dg p k c v)
    have h1' : ((tl p k w c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast h1
    have h2' : ((tl p k v c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast h2
    rw [abs_lt]; constructor <;> omega
  have hT4 : (p : ℤ) ^ 2 * ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 2) ^ 2 ≤ (p : ℤ) ^ 4 := by
    nlinarith
  have hsum_nonneg : ∀ c ∈ (univ : Finset (Fin 3)), (0 : ℤ) ≤
      ((cres (p ^ (3 * k)) ((Qpoint p k w c : ℤ) - (Qpoint p k v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
    fun c _ => sq_nonneg _
  by_cases hfar : ∃ c, Far p k v w c
  · obtain ⟨c, hc⟩ := hfar
    obtain ⟨ho0, ho1⟩ := o_bound p k v w c
    have hR : |u * ((p : ℤ) * ((o0 p k w c : ℤ) - o0 p k v c) + ((o1 p k w c : ℤ) - o1 p k v c)) +
        ((tl p k w c : ℤ) - tl p k v c)| < (p : ℤ) ^ (2 * k) := by
      have a1 : |(p : ℤ) * ((o0 p k w c : ℤ) - o0 p k v c) + ((o1 p k w c : ℤ) - o1 p k v c)| ≤
          (p : ℤ) ^ 2 - 1 := by
        have := abs_add_le ((p : ℤ) * ((o0 p k w c : ℤ) - o0 p k v c)) ((o1 p k w c : ℤ) - o1 p k v c)
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < p)] at this
        have b1 : |(o0 p k w c : ℤ) - o0 p k v c| ≤ p - 1 := by omega
        have b2 : |(o1 p k w c : ℤ) - o1 p k v c| ≤ p - 1 := by omega
        nlinarith
      have a2 := abs_add_le (u * ((p : ℤ) * ((o0 p k w c : ℤ) - o0 p k v c) +
        ((o1 p k w c : ℤ) - o1 p k v c))) ((tl p k w c : ℤ) - tl p k v c)
      rw [abs_mul, abs_of_pos hu] at a2
      have := htl c
      rw [hpow]; nlinarith
    have hf := far_gen (p ^ (3 * k)) ((p : ℤ) ^ (2 * k)) ((p : ℤ) ^ k) (by positivity) (by positivity)
      hN _ _ hR hc
    rw [← hX c] at hf
    have hsq : ((p : ℤ) ^ (2 * k)) ^ 2 ≤
        ((cres (p ^ (3 * k)) ((Qpoint p k w c : ℤ) - (Qpoint p k v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hf 2
    have hsingle := Finset.single_le_sum hsum_nonneg (mem_univ c)
    calc (p : ℤ) ^ (4 * k) * ((p : ℤ) ^ 2 * ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 2) ^ 2)
        ≤ (p : ℤ) ^ (4 * k) * (p : ℤ) ^ 4 := by gcongr
      _ = (p : ℤ) ^ 4 * ((p : ℤ) ^ (2 * k)) ^ 2 := by ring
      _ ≤ _ := by gcongr; exact hsq.trans hsingle
  · push_neg at hfar
    choose e J he hJ3 hJk hstep hz he0 using fun c => axis_classify p hp1 k hk v w c (hfar c)
    by_cases hall : ∀ c, e c = 0
    · exact absurd (eq_of_cellN p hp1 k v w (fun d => he0 d (hall d))).symm hvw
    push_neg at hall
    have hσ : ∀ c, ((o0 p k w c : ℤ) - o0 p k v c) ≡ sigR (e c) (e (c + 1)) (e (c + 2)) (J (c + 1))
        [ZMOD p] := by
      intro c
      have h := Dg_off_sub p k c v w ⟨0, by omega⟩ tab0 (fun d l => QPhi_row0' k hk c d l)
        tab0_vanish e J hJk hstep
      rw [← o0_cast p k (by omega) w c, ← o0_cast p k (by omega) v c] at h
      rw [← ZMod.intCast_eq_intCast_iff, ← sig_closed e J hJ3 c]
      simp only [P0]
      push_cast at h ⊢
      exact h
    have hτ : ∀ c, ((o1 p k w c : ℤ) - o1 p k v c) ≡
        tauR (e (c + 1)) (e (c + 2)) (J (c + 1)) (J (c + 2)) [ZMOD p] := by
      intro c
      have h := Dg_off_sub p k c v w ⟨1, by omega⟩ tab1 (fun d l => QPhi_row1' k hk c d l)
        tab1_vanish e J hJk hstep
      rw [← o1_cast p k (by omega) w c, ← o1_cast p k (by omega) v c] at h
      rw [← ZMod.intCast_eq_intCast_iff, ← tau_closed e J hJ3 c]
      simp only [P1]
      push_cast at h ⊢
      exact h
    set V : Fin 3 → ℤ := fun c => e c * (p : ℤ) ^ 2 + ((o0 p k w c : ℤ) - o0 p k v c) * p +
      ((o1 p k w c : ℤ) - o1 p k v c) with hV
    have hVb : ∀ c, |V c| ≤ 2 * (p : ℤ) ^ 2 - 1 := by
      intro c
      obtain ⟨ho0, ho1⟩ := o_bound p k v w c
      have b1 : |(o0 p k w c : ℤ) - o0 p k v c| ≤ p - 1 := by omega
      have b2 : |(o1 p k w c : ℤ) - o1 p k v c| ≤ p - 1 := by omega
      have b0 : |e c| ≤ 1 := abs_le.mpr ⟨(he c).1, (he c).2⟩
      have := abs_add_le (e c * (p : ℤ) ^ 2 + ((o0 p k w c : ℤ) - o0 p k v c) * p)
        ((o1 p k w c : ℤ) - o1 p k v c)
      have := abs_add_le (e c * (p : ℤ) ^ 2) (((o0 p k w c : ℤ) - o0 p k v c) * p)
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (p : ℤ) ^ 2),
        abs_of_pos (by positivity : (0 : ℤ) < p)] at this
      simp only [hV]
      nlinarith
    have hXV : ∀ c, ∃ z : ℤ, (Qpoint p k w c : ℤ) - Qpoint p k v c =
        u * V c + ((tl p k w c : ℤ) - tl p k v c) + z * ((p ^ (3 * k) : ℕ) : ℤ) := by
      intro c
      obtain ⟨z, hzc⟩ := hz c
      refine ⟨z, ?_⟩
      rw [hX c, hzc, hN, hpow]; simp only [hV]; ring
    have hpk : (4 : ℤ) ≤ (p : ℤ) ^ k := by
      calc (4 : ℤ) ≤ p := by omega
        _ = (p : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (p : ℤ) ^ k := pow_le_pow_right₀ (by omega) (by omega)
    set x : Fin 3 → ℤ := fun c =>
      ((cres (p ^ (3 * k)) ((Qpoint p k w c : ℤ) - (Qpoint p k v c : ℤ)) : ℕ) : ℤ) / u with hx_def
    have hnear : ∀ c, 0 ≤ x c ∧ |V c| - 1 ≤ x c ∧
        ((tl p k w c : ℤ) - tl p k v c = 0 → |V c| ≤ x c) ∧
        u * x c ≤ ((cres (p ^ (3 * k)) ((Qpoint p k w c : ℤ) - (Qpoint p k v c : ℤ)) : ℕ) : ℤ) := by
      intro c
      obtain ⟨z, hzc⟩ := hXV c
      simp only [hx_def]
      rw [hzc]
      refine near_gen (p ^ (3 * k)) u (V c) _ z hu (htl c) ?_
      rw [hN, hpow]
      have := abs_add_le (u * V c) ((tl p k w c : ℤ) - tl p k v c)
      rw [abs_mul, abs_of_pos hu] at this
      have := hVb c; have := htl c
      have h4 : 4 * (u * (p : ℤ) ^ 2) ≤ u * (p : ℤ) ^ 2 * (p : ℤ) ^ k := by
        have : 0 < u * (p : ℤ) ^ 2 := by positivity
        nlinarith
      nlinarith
    have hkey := key_ineq checkAll_eq (p : ℤ) hpz e he hall J hJ3
      (fun c => (o0 p k w c : ℤ) - o0 p k v c) (fun c => (o1 p k w c : ℤ) - o1 p k v c) x
      (fun c => ⟨hσ c, (o_bound p k v w c).1⟩) (fun c => ⟨hτ c, (o_bound p k v w c).2⟩)
      (fun c => (hnear c).1) (by
        intro c
        split_ifs with honly
        · apply (hnear c).2.2.1
          have := tl_eq_of_only p hp1 k (by omega) c v w (by
            intro d hd
            apply he0
            have : d = c + 1 ∨ d = c + 2 := by fin_cases c <;> fin_cases d <;> simp_all
            rcases this with rfl | rfl
            · exact honly.2.1
            · exact honly.2.2)
          rw [this]; ring
        · exact (hnear c).2.1)
    have hsq : ∀ c, (u * x c) ^ 2 ≤
        ((cres (p ^ (3 * k)) ((Qpoint p k w c : ℤ) - (Qpoint p k v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      fun c => pow_le_pow_left₀ (mul_nonneg hu.le (hnear c).1) (hnear c).2.2.2 2
    have hu4 : (p : ℤ) ^ (4 * k) = (p : ℤ) ^ 4 * u ^ 2 := by
      rw [hu_def, ← pow_mul, ← pow_add]; congr 1; omega
    rw [Fin.sum_univ_three]
    calc (p : ℤ) ^ (4 * k) * ((p : ℤ) ^ 2 * ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 2) ^ 2)
        ≤ (p : ℤ) ^ (4 * k) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by gcongr
      _ = (p : ℤ) ^ 4 * ((u * x 0) ^ 2 + (u * x 1) ^ 2 + (u * x 2) ^ 2) := by rw [hu4]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hsq 0) (hsq 1)) (hsq 2))
          (by positivity)


end

end Z3Net.Two

namespace Z3Net.Proofs

open Z3Net

/-- **Separation part of `thm:two`, exact integer form, every integer `q ≥ 11`.** -/
theorem Q_sep_ge11 (q k : ℕ) (hq11 : 11 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * ((q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 2 + ((q : ℤ) - 1) ^ 2 + ((q : ℤ) - 2) ^ 2)
      ≤ (q : ℤ) ^ 4 * (torusDist2 (q ^ (3 * k)) (Qpoint q k v) (Qpoint q k w) : ℤ) := by
  have : NeZero q := ⟨by omega⟩
  have h := Two.main_bound_ge11 q hq11 k hk w v (Ne.symm hvw)
  unfold torusDist2
  push_cast
  exact h


/-- **Theorem 2, real form, every integer `q ≥ 11`.** -/
theorem Q_sep_real_ge11 (p k : ℕ) (hp11 : 11 ≤ p) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod p) (hvw : v ≠ w) :
    cQ p * ((p : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k)) ((Qpoint p k v c : ℤ) - (Qpoint p k w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k)) ^ 2) := by
  have hZ := Q_sep_ge11 p k hp11 hk v w hvw
  unfold torusDist2 at hZ
  have hR : ((p : ℝ) ^ (4 * k) * ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2 + ((p : ℝ) - 1) ^ 2 + ((p : ℝ) - 2) ^ 2))
      ≤ (p : ℝ) ^ 4 * ∑ c, ((cres (p ^ (3 * k)) ((Qpoint p k v c : ℤ) - (Qpoint p k w c : ℤ)) : ℝ)) ^ 2 := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this
    exact this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set S : ℝ := ∑ c, ((cres (p ^ (3 * k)) ((Qpoint p k v c : ℤ) - (Qpoint p k w c : ℤ)) : ℝ)) ^ 2
    with hS
  set T : ℝ := (p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2 + ((p : ℝ) - 1) ^ 2 + ((p : ℝ) - 2) ^ 2 with hT
  have hcQ : cQ p ^ 2 = T / (p : ℝ) ^ 4 := by
    unfold cQ
    rw [Real.sq_sqrt (by positivity), hT]
    field_simp
    ring
  have hrp : ((p : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ)) = 1 / (p : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, show ((3 * k : ℕ) : ℝ) * (-(1 / 3 : ℝ)) =
      -(k : ℝ) by push_cast; ring, Real.rpow_neg hp0.le, Real.rpow_natCast, one_div]
  have hsum : ∑ c, ((cres (p ^ (3 * k)) ((Qpoint p k v c : ℤ) - (Qpoint p k w c : ℤ)) : ℝ)
      / (p : ℝ) ^ (3 * k)) ^ 2 = S / ((p : ℝ) ^ (3 * k)) ^ 2 := by
    rw [hS, Finset.sum_div]; refine Finset.sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum, hrp]
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, hcQ, div_pow, one_pow]
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : ((p : ℝ) ^ (3 * k)) ^ 2 = (p : ℝ) ^ (4 * k) * ((p : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  rw [e1]
  nlinarith [hR, sq_nonneg ((p : ℝ) ^ k)]


/-- **Separation part of `thm:two` for odd `q ≥ 11`** (exact integer form). -/
theorem Q_sep_odd (q k : ℕ) (_hq : Odd q) (hq11 : 11 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (4 * k) * ((q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 2 + ((q : ℤ) - 1) ^ 2 + ((q : ℤ) - 2) ^ 2)
      ≤ (q : ℤ) ^ 4 * (torusDist2 (q ^ (3 * k)) (Qpoint q k v) (Qpoint q k w) : ℤ) :=
  Q_sep_ge11 q k hq11 hk v w hvw

/-- **Theorem 2, real form, odd `q ≥ 11`.** -/
theorem Q_sep_real_odd (q k : ℕ) (_hq : Odd q) (hq11 : 11 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod q) (hvw : v ≠ w) :
    cQ q * ((q : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (3 * k)) ((Qpoint q k v c : ℤ) - (Qpoint q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (3 * k)) ^ 2) :=
  Q_sep_real_ge11 q k hq11 hk v w hvw

end Z3Net.Proofs

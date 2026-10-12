module
public import Mathlib
public import Z3Net.Defs
public import Z3Net.TwoCase
public import Z3Net.TwoGeom

@[expose] public section

/-!
# Theorem 2 (`thm:two`): separation of the two-digit nets `𝒬_{k,p}`

## Architecture
* `Z3Net/TwoPoly.lean` — `τ` as a polynomial map (`tauL`), multiplicativity, `T³ = 1`; the explicit
  inverse `Wmat` of the `(k,k,k)` box matrix of the frame `(T², I, T)` (so Mathlib's `⁻¹` over `ℤ`
  in `graphBlock` is identified for **all** `k`); `frameB`, `frameC` are digits `k + r` of `T² Y_l`,
  `T Y_l` with `Y_l = (t-1)^k (t^l (t-1)^(-k) mod t^k)`.
* `Z3Net/TwoRows.lean` — `prop:rows` (generating functions `E1^k`, `-t E1^k`, `-E1^(k+1)`, `E1^(k+2)`)
  and `cor:rows` (`QPhi_row0`, `QPhi_row1`, `QPhi_self_row`), all `k ≥ 2`.
* `Z3Net/TwoCase.lean` — the case analysis of the proof of `thm:two` as one kernel-checked
  enumeration (`checkAll_eq`, `decide +kernel`) + soundness (`key_ineq`), valid for all `p ≥ 11`.
* `Z3Net/TwoGeom.lean` — digits of `Qpoint`, cell/offset decomposition, carry lemma, change of the
  first two offset digits, toroidal residues.
* this file — assembly: `Z3Net.Proofs.Q_sep`, `Z3Net.Proofs.Q_sep_real`.
-/

namespace Z3Net.Two

open Finset

noncomputable section

variable (p : ℕ) [NeZero p]

/-- First and second offset digits and the tail of coordinate `c`. -/
def o0 (k : ℕ) (v : Fin (3 * k) → ZMod p) (c : Fin 3) : ℕ := dv p k (Dg p k c v) k
def o1 (k : ℕ) (v : Fin (3 * k) → ZMod p) (c : Fin 3) : ℕ := dv p k (Dg p k c v) (k + 1)
def tl (k : ℕ) (v : Fin (3 * k) → ZMod p) (c : Fin 3) : ℕ := tail p k (Dg p k c v)

lemma X_decomp (k : ℕ) (hk : 2 ≤ k) (v : Fin (3 * k) → ZMod p) (c : Fin 3) :
    (Qpoint p k v c : ℤ) = (p : ℤ) ^ (2 * k) * cellN p k v c +
      (p : ℤ) ^ (2 * k - 2) * (p * o0 p k v c + o1 p k v c) + tl p k v c := by
  rw [Qpoint_eq, coord_split p k (by omega), cell_part]
  push_cast
  rw [show 2 * k - 1 = (2 * k - 2) + 1 by omega, pow_succ]
  simp only [o0, o1, tl]; ring

lemma o0_cast (k : ℕ) (hk : 1 ≤ k) (v : Fin (3 * k) → ZMod p) (c : Fin 3) :
    ((o0 p k v c : ℕ) : ZMod p) = Dg p k c v ⟨k + (⟨0, by omega⟩ : Fin (2 * k)), by simp; omega⟩ := by
  simp only [o0, dv, dif_pos (show k < 3 * k by omega), ZMod.natCast_zmod_val, add_zero]

lemma o1_cast (k : ℕ) (hk : 1 ≤ k) (v : Fin (3 * k) → ZMod p) (c : Fin 3) :
    ((o1 p k v c : ℕ) : ZMod p) = Dg p k c v ⟨k + (⟨1, by omega⟩ : Fin (2 * k)), by simp; omega⟩ := by
  simp only [o1, dv, dif_pos (show k + 1 < 3 * k by omega), ZMod.natCast_zmod_val]

lemma sum_rot3 {M : Type*} [AddCommMonoid M] (c : Fin 3) (f : Fin 3 → M) :
    ∑ d, f d = f c + f (c + 1) + f (c + 2) := by
  fin_cases c <;> simp [Fin.sum_univ_three] <;> abel

lemma P0_closed (J : ℕ) (hJ : J ≤ 3) : P0 0 J = -1 ∧ P0 1 J = p0n J ∧ P0 2 J = -1 := by
  interval_cases J <;> decide

lemma P1_closed (J : ℕ) (hJ : J ≤ 3) : P1 0 J = 0 ∧ P1 1 J = p1n J ∧ P1 2 J = p1f J := by
  interval_cases J <;> decide

lemma sig_closed (e : Fin 3 → ℤ) (J : Fin 3 → ℕ) (hJ : ∀ d, J d ≤ 3) (c : Fin 3) :
    ∑ d, e d * P0 (d - c) (J d) = sigR (e c) (e (c + 1)) (e (c + 2)) (J (c + 1)) := by
  rw [sum_rot3 c, sub_self, add_sub_cancel_left, add_sub_cancel_left, (P0_closed _ (hJ c)).1,
    (P0_closed _ (hJ (c + 1))).2.1, (P0_closed _ (hJ (c + 2))).2.2, sigR]
  ring

lemma tau_closed (e : Fin 3 → ℤ) (J : Fin 3 → ℕ) (hJ : ∀ d, J d ≤ 3) (c : Fin 3) :
    ∑ d, e d * P1 (d - c) (J d) = tauR (e (c + 1)) (e (c + 2)) (J (c + 1)) (J (c + 2)) := by
  rw [sum_rot3 c, sub_self, add_sub_cancel_left, add_sub_cancel_left, (P1_closed _ (hJ c)).1,
    (P1_closed _ (hJ (c + 1))).2.1, (P1_closed _ (hJ (c + 2))).2.2, tauR]
  ring

/-- Equal cells on all three axes force equal indices (graph form: the index is the cells). -/
lemma eq_of_cellN (hp : 1 < p) (k : ℕ) (v w : Fin (3 * k) → ZMod p)
    (h : ∀ d, cellN p k w d = cellN p k v d) : w = v := by
  funext j
  have hk : 0 < k := by have := j.isLt; omega
  have := digits_eq_of_cellN_eq p hp k v w ⟨(j : ℕ) / k, Nat.div_lt_of_lt_mul (by have := j.isLt; omega)⟩
    (h _) ⟨(j : ℕ) % k, Nat.mod_lt _ hk⟩
  convert this using 2 <;> (ext; simp [ix, Nat.div_add_mod'])

/-! ## One coordinate: far steps and near steps -/

omit [NeZero p] in
lemma far_gen (N : ℕ) (G P : ℤ) (hG : 0 < G) (hP : 0 < P) (hN : (N : ℤ) = G * P) (Δn R : ℤ)
    (hR : |R| < G) (hfar : ∀ z : ℤ, 2 ≤ |Δn - z * P|) : G ≤ cres N (G * Δn + R) := by
  have hN0 : 0 < N := by
    have : (0 : ℤ) < N := by rw [hN]; positivity
    exact_mod_cast this
  obtain ⟨z, hz⟩ := cres_eq_abs_sub N hN0 (G * Δn + R)
  rw [hz, hN]
  have h2 := hfar z
  have e : G * Δn + R - z * (G * P) = G * (Δn - z * P) + R := by ring
  rw [e]
  have h3 : |G * (Δn - z * P)| = G * |Δn - z * P| := by rw [abs_mul, abs_of_pos hG]
  have h4 := abs_add_le (G * (Δn - z * P) + R) (-R)
  rw [add_neg_cancel_right, abs_neg, h3] at h4
  nlinarith

omit [NeZero p] in
lemma near_gen (N : ℕ) (u V Δt z : ℤ) (hu : 0 < u) (ht : |Δt| < u)
    (hsmall : 2 * |u * V + Δt| ≤ N) :
    0 ≤ (cres N (u * V + Δt + z * N) : ℤ) / u ∧
    |V| - 1 ≤ (cres N (u * V + Δt + z * N) : ℤ) / u ∧
    (Δt = 0 → |V| ≤ (cres N (u * V + Δt + z * N) : ℤ) / u) ∧
    u * ((cres N (u * V + Δt + z * N) : ℤ) / u) ≤ cres N (u * V + Δt + z * N) := by
  rw [cres_add_mul, cres_eq_abs N _ hsmall]
  refine ⟨Int.ediv_nonneg (abs_nonneg _) hu.le, ?_, ?_, ?_⟩
  · apply Int.le_ediv_of_mul_le hu
    have h1 := abs_add_le (u * V + Δt) (-Δt)
    rw [add_neg_cancel_right, abs_neg, abs_mul, abs_of_pos hu] at h1
    nlinarith
  · intro h0; subst h0
    apply Int.le_ediv_of_mul_le hu
    rw [add_zero, abs_mul, abs_of_pos hu]; linarith
  · rw [mul_comm]; exact Int.ediv_mul_le _ hu.ne'

/-- The step of axis `d` is "far" (toroidal cell difference outside `{-1,0,1}`). -/
def Far (k : ℕ) (v w : Fin (3 * k) → ZMod p) (d : Fin 3) : Prop :=
  ∀ z : ℤ, 2 ≤ |(cellN p k w d : ℤ) - cellN p k v d - z * (p : ℤ) ^ k|

lemma axis_classify (hp : 1 < p) (k : ℕ) (hk : 2 ≤ k) (v w : Fin (3 * k) → ZMod p) (d : Fin 3)
    (hnf : ¬ Far p k v w d) :
    ∃ e : ℤ, ∃ J : ℕ, (-1 ≤ e ∧ e ≤ 1) ∧ J ≤ 3 ∧ J < k ∧ AxisStep p k v w d e J ∧
      (∃ z : ℤ, (cellN p k w d : ℤ) - cellN p k v d = e + z * (p : ℤ) ^ k) ∧
      (e = 0 → cellN p k w d = cellN p k v d) := by
  have hP : 3 ≤ p ^ k := by
    calc 3 ≤ p ^ 2 := by nlinarith
      _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  rcases step_cases (p ^ k) (cellN p k v d) (cellN p k w d) hP (cellN_lt p k v d)
    (cellN_lt p k w d) with h | h | h | h
  · exact ⟨0, 0, by norm_num, by norm_num, by omega, axisStep_zero p hp k v w d h,
      ⟨0, by rw [h]; ring⟩, fun _ => h⟩
  · refine ⟨1, Jof p k (cellN p k v d), by norm_num, Jof_le p k _, Jof_lt p k _ (by omega),
      axisStep_plus p hp k (by omega) v w d h, ⟨-(((cellN p k v d + 1) / p ^ k : ℕ) : ℤ), ?_⟩,
      fun h1 => absurd h1 (by norm_num)⟩
    have := Nat.mod_add_div (cellN p k v d + 1) (p ^ k)
    rw [← h] at this
    have h' : ((cellN p k w d : ℕ) : ℤ) + ((p ^ k : ℕ) : ℤ) * (((cellN p k v d + 1) / p ^ k : ℕ) : ℤ)
        = (cellN p k v d : ℤ) + 1 := by exact_mod_cast this
    push_cast at h' ⊢; linarith
  · refine ⟨-1, Jof p k (cellN p k w d), by norm_num, Jof_le p k _, Jof_lt p k _ (by omega),
      axisStep_minus p hp k (by omega) v w d h, ⟨(((cellN p k w d + 1) / p ^ k : ℕ) : ℤ), ?_⟩,
      fun h1 => absurd h1 (by norm_num)⟩
    have := Nat.mod_add_div (cellN p k w d + 1) (p ^ k)
    rw [← h] at this
    have h' : ((cellN p k v d : ℕ) : ℤ) + ((p ^ k : ℕ) : ℤ) * (((cellN p k w d + 1) / p ^ k : ℕ) : ℤ)
        = (cellN p k w d : ℤ) + 1 := by exact_mod_cast this
    push_cast at h' ⊢; linarith
  · exact absurd h hnf

/-! ## Assembly -/

lemma tl_eq_of_only (hp : 1 < p) (k : ℕ) (hk : 1 ≤ k) (c : Fin 3) (v w : Fin (3 * k) → ZMod p)
    (hother : ∀ d, d ≠ c → cellN p k w d = cellN p k v d) : tl p k w c = tl p k v c := by
  unfold tl tail
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_Ico] at hj
  congr 1
  unfold dv
  rw [dif_pos hj.2, dif_pos hj.2]
  have e := Dg_off_eq_of_only p hp k c v w hother ⟨j - k, by omega⟩ (by simp; omega)
  have hj' : (⟨j, hj.2⟩ : Fin (3 * k)) = ⟨k + ((⟨j - k, by omega⟩ : Fin (2 * k)) : ℕ), by simp; omega⟩ := by
    ext; simp; omega
  rw [hj', e]

lemma o_bound (k : ℕ) (v w : Fin (3 * k) → ZMod p) (c : Fin 3) :
    |(o0 p k w c : ℤ) - o0 p k v c| < p ∧ |(o1 p k w c : ℤ) - o1 p k v c| < p := by
  have h1 := dv_lt p k (Dg p k c w) k; have h2 := dv_lt p k (Dg p k c v) k
  have h3 := dv_lt p k (Dg p k c w) (k + 1); have h4 := dv_lt p k (Dg p k c v) (k + 1)
  simp only [o0, o1]
  constructor <;> rw [abs_lt] <;> constructor <;> omega

theorem main_bound (hp : p.Prime) (hp11 : 11 ≤ p) (k : ℕ) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod p) (hvw : v ≠ w) :
    (p : ℤ) ^ (4 * k) * ((p : ℤ) ^ 2 * ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 2) ^ 2)
      ≤ (p : ℤ) ^ 4 * ∑ c : Fin 3,
          ((cres (p ^ (3 * k)) ((Qpoint p k w c : ℤ) - (Qpoint p k v c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  have hp1 : 1 < p := hp.one_lt
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

/-- **Separation part of `thm:two`, exact integer form.** For primes `p ≥ 11`, `k ≥ 2`, distinct
`v ≠ w`, with `N = p^(3k)`:
`p⁴ D² ≥ p^(4k) · (p²(p-1)² + (p-1)² + (p-2)²)`, i.e. `δ ≥ c*(p) N^(-1/3)` with
`c*(p)² = (1-1/p)² + ((p-1)² + (p-2)²)/p⁴`. -/
theorem Q_sep (p k : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod p) (hvw : v ≠ w) :
    (p : ℤ) ^ (4 * k) * ((p : ℤ) ^ 2 * ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 1) ^ 2 + ((p : ℤ) - 2) ^ 2)
      ≤ (p : ℤ) ^ 4 * (torusDist2 (p ^ (3 * k)) (Qpoint p k v) (Qpoint p k w) : ℤ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h := Two.main_bound p hp hp11 k hk w v (Ne.symm hvw)
  unfold torusDist2
  push_cast
  exact h

/-- **Theorem 2, real form.** The toroidal distance between distinct points of `𝒬_{k,p}` is at
least `c*(p) · N^(-1/3)`. -/
theorem Q_sep_real (p k : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (hk : 2 ≤ k)
    (v w : Fin (3 * k) → ZMod p) (hvw : v ≠ w) :
    cQ p * ((p : ℝ) ^ (3 * k)) ^ (-(1 / 3 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (3 * k)) ((Qpoint p k v c : ℤ) - (Qpoint p k w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (3 * k)) ^ 2) := by
  have hZ := Q_sep p k hp hp11 hk v w hvw
  unfold torusDist2 at hZ
  have hR : ((p : ℝ) ^ (4 * k) * ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2 + ((p : ℝ) - 1) ^ 2 + ((p : ℝ) - 2) ^ 2))
      ≤ (p : ℝ) ^ 4 * ∑ c, ((cres (p ^ (3 * k)) ((Qpoint p k v c : ℤ) - (Qpoint p k w c : ℤ)) : ℝ)) ^ 2 := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this
    exact this
  have hp0 : (0 : ℝ) < p := by have := hp.pos; exact_mod_cast this
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

end Z3Net.Proofs

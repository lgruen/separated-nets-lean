module
public import Mathlib
public import Z3Net.HLGeom

@[expose] public section

/-!
# Entry HL, part 6: Prop H_k(a), the carry relaxation (`HL_relax`)

For distinct indices `x ≠ y`: every axis `d` makes a cell step `E_d ∈ {-2,…,2}` (with carry
length `J_d`) or is *far* (toroidal cell difference `≥ 3`, distance `≥ 2` cells). Row `0` of every
block is the design (`HL_row0`), so the first offset digit of coordinate `c` changes by
`Δ_c ≡ ∑_d (E_d F_0[c][d] + sgn(E_d) ∑_{t=1}^{J_d} F_t[c][d])` (mod `q`), i.e.
`2Δ_c ≡ sig2 (mod q)`; the deeper offset digits are a jitter of less than one first-offset
unit. Hence `cres_c ≥ q^(sk-k-1) (|q E_c + Δ_c| - 1)`.
-/

namespace Z3NetHL.Proofs

open Finset Matrix

noncomputable section

/-! ## Good design entries -/

lemma HLdes_good {s q : ℕ} {u v : Fin s → ℤ} {lam : Fin s → ℚ} {gco : Fin s → ℕ → ℕ → ℚ}
    {dg : Fin s → ℕ → ℚ} (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg)
    (n : ℕ) (c d : Fin s) : Good q (HLdes u v lam gco dg n c d) := by
  obtain ⟨hpts, _, _⟩ := adm_units hq
  unfold HLdes
  split_ifs with h1 h2
  · simpa using good_int (q := q) 0
  · exact isUnit_nat_of_coprime (hden.2 c n (by omega))
  · have hP : IsUnit (((u c - v d : ℤ)) : ZMod q) := by
      have := hpts c 1 d 0 (by simp)
      simpa [splitPt] using this
    have hy := (good_inv_int (q := q) _ hP).1
    have hl : Good q (lam c) := isUnit_nat_of_coprime (hq.2.2.1 c).2
    refine (good_mul hl (good_sum _ _ fun n' hn' => ?_).1).1
    rw [mem_range] at hn'
    exact (good_mul (isUnit_nat_of_coprime (hden.1 d n (by omega) n' (by omega)))
      (good_pow hy (n' + 1)).1).1

lemma two_qr_des {s q : ℕ} {u v : Fin s → ℤ} {lam : Fin s → ℚ} {gco : Fin s → ℕ → ℕ → ℚ}
    {dg : Fin s → ℕ → ℚ} (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg)
    (F2 : ℕ → Fin s → Fin s → ℤ) (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d)
    (n : ℕ) (c d : Fin s) : 2 * qr q (HLdes u v lam gco dg n c d) = (F2 n c d : ZMod q) := by
  have h2 : Good q (2 : ℚ) := by simpa using good_int (q := q) 2
  have := (good_mul h2 (HLdes_good hq hden n c d)).2
  rw [hF2, qr_int] at this
  rw [this, show (2 : ℚ) = ((2 : ℤ) : ℚ) by simp, qr_int]; simp

/-! ## Torus residues -/

lemma far_gen3 (N : ℕ) (G P : ℤ) (hG : 0 < G) (hP : 0 < P) (hN : (N : ℤ) = G * P) (Δn R : ℤ)
    (hR : |R| < G) (hfar : ∀ z : ℤ, 3 ≤ |Δn - z * P|) : 2 * G ≤ Z3NetU.cres N (G * Δn + R) := by
  have hN0 : 0 < N := by
    have : (0 : ℤ) < N := by rw [hN]; positivity
    exact_mod_cast this
  obtain ⟨z, hz⟩ := Z3NetU.Proofs.cres_eq_abs_sub N hN0 (G * Δn + R)
  rw [hz, hN]
  have h2 := hfar z
  have e : G * Δn + R - z * (G * P) = G * (Δn - z * P) + R := by ring
  rw [e]
  have h3 : |G * (Δn - z * P)| = G * |Δn - z * P| := by rw [abs_mul, abs_of_pos hG]
  have h4 := abs_add_le (G * (Δn - z * P) + R) (-R)
  rw [add_neg_cancel_right, abs_neg, h3] at h4
  nlinarith

/-- Cell-step classification on `ℤ/Pℤ` (`P ≥ 5`): equal, `±1`, `±2`, or far (`≥ 3`). -/
lemma step_cases2 (P a b : ℕ) (hP : 5 ≤ P) (ha : a < P) (hb : b < P) :
    b = a ∨ b = (a + 1) % P ∨ b = (a + 2) % P ∨ a = (b + 1) % P ∨ a = (b + 2) % P ∨
      ∀ z : ℤ, 3 ≤ |(b : ℤ) - a - z * P| := by
  by_cases h0 : b = a; · exact Or.inl h0
  by_cases h1 : b = a + 1; · right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h1
  by_cases h2 : b = a + 2; · right; right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h2
  by_cases h3 : a = b + 1; · right; right; right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h3
  by_cases h4 : a = b + 2; · right; right; right; right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h4
  by_cases h5 : a + 1 = b + P
  · right; left; rw [h5, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  by_cases h6 : a + 2 = b + P
  · right; right; left; rw [h6, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  by_cases h7 : b + 1 = a + P
  · right; right; right; left; rw [h7, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  by_cases h8 : b + 2 = a + P
  · right; right; right; right; left; rw [h8, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  right; right; right; right; right
  intro z
  rw [le_abs]
  rcases lt_trichotomy z 0 with hz | hz | hz
  · rcases eq_or_lt_of_le (show z ≤ -1 by omega) with hz1 | hz1
    · subst hz1; left; omega
    · left; nlinarith
  · subst hz; simp only [zero_mul, sub_zero]; omega
  · rcases eq_or_lt_of_le (show 1 ≤ z by omega) with hz1 | hz1
    · subst hz1; right; omega
    · right; nlinarith

/-! ## Axis classification and the first offset digit -/

section main

variable (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
  (dg : Fin s → ℕ → ℚ)

open Z3NetU.Proofs (ix ix_surj sk_sub_add)

variable [NeZero q]

/-- The step of axis `d` is far: toroidal cell difference outside `{-2, …, 2}`. -/
def Far3 (x y : Fin (s * k) → ZMod q) (d : Fin s) : Prop :=
  ∀ z : ℤ, 3 ≤ |(cellN s q k y d : ℤ) - cellN s q k x d - z * (q : ℤ) ^ k|

lemma axis_classify2 (hq : 7 ≤ q) (hk : 1 ≤ k) (x y : Fin (s * k) → ZMod q) (d : Fin s)
    (hnf : ¬ Far3 s q k x y d) :
    ∃ E : ℤ, ∃ J : ℕ, |E| ≤ 2 ∧ J ≤ s - 2 ∧ J < k ∧ AxisStep2 s q k x y d E J ∧
      (∃ z : ℤ, (cellN s q k y d : ℤ) - cellN s q k x d = E + z * (q : ℤ) ^ k) ∧
      (E = 0 → cellN s q k y d = cellN s q k x d) := by
  have hq2 : 2 < q := by omega
  have hP : 5 ≤ q ^ k := by
    calc 5 ≤ q := by omega
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  have hJ1 : ∀ e n, Jof2 s q k e n ≤ s - 2 := fun e n => (Jof2_le s q k e n).trans (min_le_left _ _)
  have hJ2 : ∀ e n, Jof2 s q k e n < k := fun e n => by
    have := (Jof2_le s q k e n).trans (min_le_right _ _); omega
  have hplus : ∀ e : ℕ, 1 ≤ e → e ≤ 2 →
      cellN s q k y d = (cellN s q k x d + e) % q ^ k →
      ∃ E : ℤ, ∃ J : ℕ, |E| ≤ 2 ∧ J ≤ s - 2 ∧ J < k ∧ AxisStep2 s q k x y d E J ∧
        (∃ z : ℤ, (cellN s q k y d : ℤ) - cellN s q k x d = E + z * (q : ℤ) ^ k) ∧
        (E = 0 → cellN s q k y d = cellN s q k x d) := by
    intro e he1 he2 h
    refine ⟨e, Jof2 s q k e (cellN s q k x d), by rw [abs_le]; constructor <;> omega, hJ1 _ _,
      hJ2 _ _, axisStep2_plus s q k hq2 x y d e he1 he2 h,
      ⟨-(((cellN s q k x d + e) / q ^ k : ℕ) : ℤ), ?_⟩, fun h1 => by omega⟩
    have := Nat.mod_add_div (cellN s q k x d + e) (q ^ k)
    rw [← h] at this
    have h' : ((cellN s q k y d : ℕ) : ℤ) + ((q ^ k : ℕ) : ℤ) * (((cellN s q k x d + e) / q ^ k : ℕ) : ℤ)
        = (cellN s q k x d : ℤ) + e := by exact_mod_cast this
    push_cast at h' ⊢; linarith
  have hminus : ∀ e : ℕ, 1 ≤ e → e ≤ 2 →
      cellN s q k x d = (cellN s q k y d + e) % q ^ k →
      ∃ E : ℤ, ∃ J : ℕ, |E| ≤ 2 ∧ J ≤ s - 2 ∧ J < k ∧ AxisStep2 s q k x y d E J ∧
        (∃ z : ℤ, (cellN s q k y d : ℤ) - cellN s q k x d = E + z * (q : ℤ) ^ k) ∧
        (E = 0 → cellN s q k y d = cellN s q k x d) := by
    intro e he1 he2 h
    refine ⟨-(e : ℤ), Jof2 s q k e (cellN s q k y d), by rw [abs_le]; constructor <;> omega,
      hJ1 _ _, hJ2 _ _, axisStep2_minus s q k hq2 x y d e he1 he2 h,
      ⟨(((cellN s q k y d + e) / q ^ k : ℕ) : ℤ), ?_⟩, fun h1 => by omega⟩
    have := Nat.mod_add_div (cellN s q k y d + e) (q ^ k)
    rw [← h] at this
    have h' : ((cellN s q k x d : ℕ) : ℤ) + ((q ^ k : ℕ) : ℤ) * (((cellN s q k y d + e) / q ^ k : ℕ) : ℤ)
        = (cellN s q k y d : ℤ) + e := by exact_mod_cast this
    push_cast at h' ⊢; linarith
  rcases step_cases2 (q ^ k) (cellN s q k x d) (cellN s q k y d) hP (cellN_lt s q k x d)
    (cellN_lt s q k y d) with h | h | h | h | h | h
  · exact ⟨0, 0, by simp, by omega, by omega, axisStep2_zero s q k (by omega) x y d h,
      ⟨0, by rw [h]; ring⟩, fun _ => h⟩
  · exact hplus 1 le_rfl (by norm_num) h
  · exact hplus 2 (by norm_num) le_rfl h
  · exact hminus 1 le_rfl (by norm_num) h
  · exact hminus 2 (by norm_num) le_rfl h
  · exact absurd h hnf

lemma sum_steps (k J : ℕ) (hJ : J < k) (f : ℕ → ZMod q) (E : ℤ) :
    ∑ t ∈ range k, f t * (if t = 0 then (E : ZMod q) else (E.sign : ZMod q) * (if t ≤ J then 1 else 0)) =
      (E : ZMod q) * f 0 + (E.sign : ZMod q) * ∑ t ∈ Icc 1 J, f t := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', if_pos rfl]
  simp only [Nat.succ_ne_zero, if_false]
  rw [add_comm, mul_comm (f 0)]
  congr 1
  rw [Finset.mul_sum]
  have : Icc 1 J = Finset.map ⟨(· + 1), add_left_injective 1⟩ ((range k').filter (fun t => t + 1 ≤ J)) := by
    ext t; simp only [mem_Icc, mem_map, mem_filter, mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨t - 1, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩; omega
  rw [this, Finset.sum_map, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  split_ifs <;> ring

/-- Change of the first offset digit (digit `k`) of coordinate `c`. -/
lemma Dg_off_sub2 (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg) (hs : 2 ≤ s) (hk : 1 ≤ k)
    (c : Fin s) (x y : Fin (s * k) → ZMod q) (E : Fin s → ℤ) (J : Fin s → ℕ)
    (hJk : ∀ d, J d < k) (hJs : ∀ d, J d ≤ s - 2)
    (hstep : ∀ d, AxisStep2 s q k x y d (E d) (J d)) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) :
    Dg s q k u v lam gco dg c y ⟨k + r, sk_sub_add r⟩ - Dg s q k u v lam gco dg c x ⟨k + r, sk_sub_add r⟩ =
      ∑ d : Fin s, ((E d : ZMod q) * qr q (HLdes u v lam gco dg 0 c d) +
        ((E d).sign : ZMod q) * ∑ t ∈ Icc 1 (J d), qr q (HLdes u v lam gco dg t c d)) := by
  rw [Dg_off, Dg_off, ← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_sub_distrib]
  have hrow : ∀ l : Fin k, HLPhi s q k u v lam gco dg c d r l =
      qr q (HLdes u v lam gco dg (k - 1 - (l : ℕ)) c d) :=
    fun l => HL_row0 s q k u v lam gco dg hs hq hden hk c d r hr l
  set f : ℕ → ZMod q := fun t => qr q (HLdes u v lam gco dg t c d) with hf
  have hf0 : ∀ t, s - 1 ≤ t → f t = 0 := by
    intro t ht
    simp only [hf, HLdes, if_pos ht]
    simpa using qr_int (q := q) 0
  have e1 : ∀ l : Fin k, HLPhi s q k u v lam gco dg c d r l * y (ix k d l) -
      HLPhi s q k u v lam gco dg c d r l * x (ix k d l) =
      f (k - 1 - (l : ℕ)) * (if k - 1 - (l : ℕ) = 0 then (E d : ZMod q)
        else ((E d).sign : ZMod q) * (if k - 1 - (l : ℕ) ≤ J d then 1 else 0)) := by
    intro l
    rw [← mul_sub, hrow l]
    by_cases hl : k - 1 - (l : ℕ) ≤ s - 2
    · rw [hstep d l hl]
    · rw [show qr q (HLdes u v lam gco dg (k - 1 - (l : ℕ)) c d) = f (k - 1 - (l : ℕ)) from rfl,
        hf0 _ (by omega), zero_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun l _ => e1 l)]
  rw [Fin.sum_univ_eq_sum_range (fun l => f (k - 1 - l) * (if k - 1 - l = 0 then (E d : ZMod q)
        else ((E d).sign : ZMod q) * (if k - 1 - l ≤ J d then 1 else 0))) k,
    Finset.sum_range_reflect (fun t => f t * (if t = 0 then (E d : ZMod q)
        else ((E d).sign : ZMod q) * (if t ≤ J d then 1 else 0))) k,
    sum_steps q k (J d) (hJk d) f (E d)]

/-! ## Assembly -/

/-- First offset digit and tail of coordinate `c`. -/
def o0 (x : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := dv s q k (Dg s q k u v lam gco dg c x) k
def tl (x : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := tail s q k (Dg s q k u v lam gco dg c x)

lemma X_decomp (hsk : k + 1 ≤ s * k) (x : Fin (s * k) → ZMod q) (c : Fin s) :
    (HLpoint s q k u v lam gco dg x c : ℤ) = (q : ℤ) ^ (s * k - k) * cellN s q k x c +
      (q : ℤ) ^ (s * k - k - 1) * o0 s q k u v lam gco dg x c + tl s q k u v lam gco dg x c := by
  rw [HLpoint_eq, coord_split s q k hsk, cell_part]
  push_cast
  simp only [o0, tl]

lemma o0_cast (x : Fin (s * k) → ZMod q) (c : Fin s) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) :
    ((o0 s q k u v lam gco dg x c : ℕ) : ZMod q) = Dg s q k u v lam gco dg c x ⟨k + r, sk_sub_add r⟩ := by
  have hk : k < s * k := by have := sk_sub_add r; omega
  simp only [o0, dv, dif_pos hk, ZMod.natCast_zmod_val, hr, add_zero]

lemma eq_of_cellN (hq : 1 < q) (x y : Fin (s * k) → ZMod q)
    (h : ∀ d, cellN s q k y d = cellN s q k x d) : y = x := by
  funext j
  obtain ⟨d, l, rfl⟩ := ix_surj k j
  exact digits_eq_of_cellN_eq s q k hq x y d (h d) l

lemma o_bound (x y : Fin (s * k) → ZMod q) (c : Fin s) :
    |(o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c| < q := by
  have h1 := dv_lt s q k (Dg s q k u v lam gco dg c x) k
  have h2 := dv_lt s q k (Dg s q k u v lam gco dg c y) k
  simp only [o0]
  rw [abs_lt]; constructor <;> omega

/-- **Prop H_k(a)**, with `cres` of entry U. -/
theorem relax_core (hs : 2 ≤ s) (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg)
    (hq7 : 7 ≤ q) (F2 : ℕ → Fin s → Fin s → ℤ)
    (hF2 : ∀ x c d, 2 * HLdes u v lam gco dg x c d = F2 x c d) (hk : 1 ≤ k)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤ ∑ c : Fin s,
        ((Z3NetU.cres (q ^ (s * k)) ((HLpoint s q k u v lam gco dg x c : ℤ) -
          (HLpoint s q k u v lam gco dg y c : ℤ)) : ℕ) : ℤ) ^ 2 ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          ∑ c : Fin s, ((Z3NetU.cres (q ^ (s * k)) ((HLpoint s q k u v lam gco dg x c : ℤ) -
            (HLpoint s q k u v lam gco dg y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  have hq1 : 1 < q := by omega
  have h2k : 2 * k ≤ s * k := Nat.mul_le_mul_right k hs
  have hsk : k + 1 ≤ s * k := by omega
  set M := s * k - k with hM
  have hM1 : 1 ≤ M := by omega
  set U : ℤ := (q : ℤ) ^ (M - 1) with hU_def
  have hU : 0 < U := by positivity
  have hpow : (q : ℤ) ^ M = U * q := by rw [hU_def, ← pow_succ]; congr 1; omega
  have hN : ((q ^ (s * k) : ℕ) : ℤ) = (q : ℤ) ^ M * (q : ℤ) ^ k := by
    push_cast; rw [← pow_add]; congr 1; omega
  set X := HLpoint s q k u v lam gco dg with hXdef
  have hX : ∀ c, (X x c : ℤ) - X y c =
      (q : ℤ) ^ M * ((cellN s q k x c : ℤ) - cellN s q k y c) +
      (U * ((o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c) +
        ((tl s q k u v lam gco dg x c : ℤ) - tl s q k u v lam gco dg y c)) := by
    intro c; rw [hXdef, X_decomp s q k u v lam gco dg hsk, X_decomp s q k u v lam gco dg hsk]; ring
  have htl : ∀ c, |(tl s q k u v lam gco dg x c : ℤ) - tl s q k u v lam gco dg y c| < U := by
    intro c
    have h1 := tail_lt s q k hsk (Dg s q k u v lam gco dg c x)
    have h2 := tail_lt s q k hsk (Dg s q k u v lam gco dg c y)
    have h1' : ((tl s q k u v lam gco dg x c : ℕ) : ℤ) < U := by rw [hU_def]; exact_mod_cast h1
    have h2' : ((tl s q k u v lam gco dg y c : ℕ) : ℤ) < U := by rw [hU_def]; exact_mod_cast h2
    rw [abs_lt]; constructor <;> omega
  have hsum_nonneg : ∀ c ∈ (univ : Finset (Fin s)), (0 : ℤ) ≤
      ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 :=
    fun c _ => sq_nonneg _
  by_cases hfar : ∃ c, Far3 s q k y x c
  · left
    obtain ⟨c, hc⟩ := hfar
    have ho0 := o_bound s q k u v lam gco dg x y c
    have hR : |U * ((o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c) +
        ((tl s q k u v lam gco dg x c : ℤ) - tl s q k u v lam gco dg y c)| < (q : ℤ) ^ M := by
      have a2 := abs_add_le (U * ((o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c))
        ((tl s q k u v lam gco dg x c : ℤ) - tl s q k u v lam gco dg y c)
      rw [abs_mul, abs_of_pos hU] at a2
      have := htl c
      have b1 : |(o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c| ≤ q - 1 := by omega
      rw [hpow]; nlinarith
    have hf := far_gen3 (q ^ (s * k)) ((q : ℤ) ^ M) ((q : ℤ) ^ k) (by positivity) (by positivity)
      hN _ _ hR hc
    rw [← hX c] at hf
    have hsq : (2 * (q : ℤ) ^ M) ^ 2 ≤
        ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hf 2
    have hsingle := Finset.single_le_sum hsum_nonneg (mem_univ c)
    calc 4 * (q : ℤ) ^ (2 * M) = (2 * (q : ℤ) ^ M) ^ 2 := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ _ := hsq.trans hsingle
  · right
    push_neg at hfar
    choose E J hE hJs hJk hstep hz hE0 using fun c => axis_classify2 s q k hq7 hk y x c (hfar c)
    have hne : ∃ c, E c ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hxy (eq_of_cellN s q k hq1 y x (fun d => hE0 d (hall d)))
    refine ⟨E, J, fun c => (o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c,
      hE, hne, fun c => lt_min (hJk c) (by have := hJs c; omega), ?_,
      fun c => o_bound s q k u v lam gco dg x y c, ?_⟩
    · -- the congruence `2Δ ≡ sig2`
      intro c
      have h := Dg_off_sub2 s q k u v lam gco dg hq hden hs hk c y x E J hJk hJs hstep
        ⟨0, by omega⟩ rfl
      rw [← o0_cast s q k u v lam gco dg x c ⟨0, by omega⟩ rfl,
        ← o0_cast s q k u v lam gco dg y c ⟨0, by omega⟩ rfl] at h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h]
      unfold sig2
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intro d _
      have h0 := two_qr_des hq hden F2 hF2 0 c d
      have hsum : ∑ t ∈ Icc 1 (J d), (F2 t c d : ZMod q) =
          2 * ∑ t ∈ Icc 1 (J d), qr q (HLdes u v lam gco dg t c d) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => (two_qr_des hq hden F2 hF2 t c d).symm
      rw [hsum, ← h0]
      ring
    · -- the distance bound
      set V : Fin s → ℤ := fun c => (q : ℤ) * E c +
        ((o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c) with hV
      have hVb : ∀ c, |V c| ≤ 3 * (q : ℤ) - 1 := by
        intro c
        have ho := o_bound s q k u v lam gco dg x y c
        have b1 : |(o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c| ≤ q - 1 := by omega
        have b0 : |E c| ≤ 2 := hE c
        have := abs_add_le ((q : ℤ) * E c) ((o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c)
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < q)] at this
        simp only [hV]
        nlinarith
      have hXV : ∀ c, ∃ z : ℤ, (X x c : ℤ) - X y c =
          U * V c + ((tl s q k u v lam gco dg x c : ℤ) - tl s q k u v lam gco dg y c) +
            z * ((q ^ (s * k) : ℕ) : ℤ) := by
        intro c
        obtain ⟨z, hzc⟩ := hz c
        refine ⟨z, ?_⟩
        rw [hX c, hzc, hN, hpow]; simp only [hV]; ring
      have hqk : (7 : ℤ) ≤ (q : ℤ) ^ k := by
        calc (7 : ℤ) ≤ q := by exact_mod_cast hq7
          _ = (q : ℤ) ^ 1 := (pow_one _).symm
          _ ≤ (q : ℤ) ^ k := pow_le_pow_right₀ (by omega) hk
      set xc : Fin s → ℤ := fun c =>
        ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) / U with hxc_def
      have hnear : ∀ c, 0 ≤ xc c ∧ |V c| - 1 ≤ xc c ∧
          U * xc c ≤ ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) := by
        intro c
        obtain ⟨z, hzc⟩ := hXV c
        simp only [hxc_def]
        rw [hzc]
        have := Z3NetU.Proofs.near_gen (q ^ (s * k)) U (V c) _ z hU (htl c) (by
          rw [hN, hpow]
          have := abs_add_le (U * V c) ((tl s q k u v lam gco dg x c : ℤ) - tl s q k u v lam gco dg y c)
          rw [abs_mul, abs_of_pos hU] at this
          have := hVb c; have := htl c
          have h7 : 7 * (U * q) ≤ U * q * (q : ℤ) ^ k := by
            have : 0 < U * q := by positivity
            nlinarith
          nlinarith)
        exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hsq : ∀ c, (U * max 0 (|V c| - 1)) ^ 2 ≤
          ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
        intro c
        obtain ⟨h1, h2, h3⟩ := hnear c
        have hm : max 0 (|V c| - 1) ≤ xc c := max_le h1 h2
        have hm0 : 0 ≤ max 0 (|V c| - 1) := le_max_left _ _
        exact pow_le_pow_left₀ (mul_nonneg hU.le hm0) ((mul_le_mul_of_nonneg_left hm hU.le).trans h3) 2
      have hU2 : (q : ℤ) ^ (2 * (M - 1)) = U ^ 2 := by rw [hU_def, ← pow_mul]; ring_nf
      calc (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c +
            ((o0 s q k u v lam gco dg x c : ℤ) - o0 s q k u v lam gco dg y c)| - 1)) ^ 2
          = ∑ c, (U * max 0 (|V c| - 1)) ^ 2 := by
            rw [← hM, hU2, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by simp only [hV]; ring
        _ ≤ _ := Finset.sum_le_sum fun c _ => hsq c

end main


end

end Z3NetHL.Proofs

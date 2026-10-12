module
public import Mathlib
public import Z3Net.D4Geom
public import Z3Net.D4Case
public import Z3Net.D4CaseCheck

@[expose] public section

/-!
# 4D entry, part 8: Theorem 4D(3) — separation

Assembly of Lemma S (soundness of the relaxation: carries, residue representatives, jitter) and
Proposition C (`key_ineq`, kernel-checked). The toroidal residue lemmas are copied from the 3D
entry (`Z3Net/TwoGeom.lean`, `Z3Net/Two.lean`) for the 4D `cres`.
-/

namespace Z3NetD4.Proofs

open Finset Z3NetD4

noncomputable section

/-! ## Toroidal residues (copied from the 3D entry) -/

lemma cres_add_mul (N : ℕ) (u z : ℤ) : cres N (u + z * N) = cres N u := by
  unfold cres; rw [Int.add_mul_emod_self_right]

lemma cres_eq_abs (N : ℕ) (u : ℤ) (h : 2 * |u| ≤ N) : (cres N u : ℤ) = |u| := by
  unfold cres
  rcases lt_trichotomy u 0 with hu | hu | hu
  · rw [abs_of_neg hu] at h ⊢
    have hm : u % (N : ℤ) = u + N := by
      rw [show u = (u + N) + (-1) * N by ring, Int.add_mul_emod_self_right,
        Int.emod_eq_of_lt (by omega) (by omega)]; ring
    rw [hm]
    have : N - (u + N).toNat ≤ (u + N).toNat := by omega
    rw [min_eq_right this]; omega
  · subst hu; simp
  · rw [abs_of_pos hu] at h ⊢
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    have : u.toNat ≤ N - u.toNat := by omega
    rw [min_eq_left this]; omega

lemma cres_eq_abs_sub (N : ℕ) (hN : 0 < N) (u : ℤ) : ∃ z : ℤ, (cres N u : ℤ) = |u - z * N| := by
  have h0 := Int.emod_nonneg u (show (N : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos u (show (0 : ℤ) < N by omega)
  have hd := Int.mul_ediv_add_emod u (N : ℤ)
  unfold cres
  rcases le_total (u % (N : ℤ)).toNat (N - (u % (N : ℤ)).toNat) with h | h
  · refine ⟨u / N, ?_⟩
    rw [min_eq_left h, abs_of_nonneg (by nlinarith)]
    have : ((u % (N : ℤ)).toNat : ℤ) = u % N := Int.toNat_of_nonneg h0
    rw [this]; linarith
  · refine ⟨u / N + 1, ?_⟩
    rw [min_eq_right h, abs_of_nonpos (by nlinarith)]
    have : ((u % (N : ℤ)).toNat : ℤ) = u % N := Int.toNat_of_nonneg h0
    push_cast [Nat.cast_sub (show (u % (N : ℤ)).toNat ≤ N by omega), this]
    linarith

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

/-- Cell-step trichotomy on `ℤ/Pℤ` (`P ≥ 3`). -/
lemma step_cases (P a b : ℕ) (hP : 3 ≤ P) (ha : a < P) (hb : b < P) :
    b = a ∨ b = (a + 1) % P ∨ a = (b + 1) % P ∨ ∀ z : ℤ, 2 ≤ |(b : ℤ) - a - z * P| := by
  by_cases h0 : b = a; · exact Or.inl h0
  by_cases h1 : b = a + 1; · right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h1
  by_cases h2 : a = b + 1; · right; right; left; rw [Nat.mod_eq_of_lt (by omega)]; exact h2
  by_cases h3 : b = 0 ∧ a = P - 1
  · right; left; rw [h3.1, h3.2, Nat.sub_add_cancel (by omega), Nat.mod_self]
  by_cases h4 : a = 0 ∧ b = P - 1
  · right; right; left; rw [h4.1, h4.2, Nat.sub_add_cancel (by omega), Nat.mod_self]
  right; right; right
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

/-! ## One coordinate -/

variable (q : ℕ) [NeZero q]

/-- First offset digit and tail of coordinate `c`. -/
def o0 (k : ℕ) (v : Fin (4 * k) → ZMod q) (c : Fin 4) : ℕ := dv q k (Dg q k c v) k
def tl (k : ℕ) (v : Fin (4 * k) → ZMod q) (c : Fin 4) : ℕ := tail q k (Dg q k c v)

lemma X_decomp (k : ℕ) (hk : 2 ≤ k) (v : Fin (4 * k) → ZMod q) (c : Fin 4) :
    (D4point q k v c : ℤ) = (q : ℤ) ^ (3 * k) * cellN q k v c +
      (q : ℤ) ^ (3 * k - 1) * o0 q k v c + tl q k v c := by
  rw [D4point_eq, coord_split q k (by omega), cell_part]
  push_cast
  simp only [o0, tl]

lemma o0_cast (k : ℕ) (hk : 1 ≤ k) (v : Fin (4 * k) → ZMod q) (c : Fin 4) :
    ((o0 q k v c : ℕ) : ZMod q) = Dg q k c v ⟨k + 0, by omega⟩ := by
  simp only [o0, dv, dif_pos (show k < 4 * k by omega), ZMod.natCast_zmod_val, add_zero]

/-- Equal cells on all four axes force equal indices (graph form: the index is the cells). -/
lemma eq_of_cellN (hq : 1 < q) (k : ℕ) (v w : Fin (4 * k) → ZMod q)
    (h : ∀ d, cellN q k w d = cellN q k v d) : w = v := by
  funext j
  have hk : 0 < k := by have := j.isLt; omega
  have hc : (j : ℕ) / k < 4 := Nat.div_lt_of_lt_mul (by have := j.isLt; omega)
  have := digits_eq_of_cellN_eq q hq k v w ⟨(j : ℕ) / k, hc⟩ (h _) ⟨(j : ℕ) % k, Nat.mod_lt _ hk⟩
  convert this using 2 <;> (ext; simp [ix]; exact (Nat.div_add_mod' (j : ℕ) k).symm)

/-- The step of axis `d` is "far" (toroidal cell difference outside `{-1,0,1}`). -/
def Far (k : ℕ) (v w : Fin (4 * k) → ZMod q) (d : Fin 4) : Prop :=
  ∀ z : ℤ, 2 ≤ |(cellN q k w d : ℤ) - cellN q k v d - z * (q : ℤ) ^ k|

lemma axis_classify (hq : 1 < q) (k : ℕ) (hk : 2 ≤ k) (v w : Fin (4 * k) → ZMod q) (d : Fin 4)
    (hnf : ¬ Far q k v w d) :
    ∃ e : ℤ, ∃ J : ℕ, (-1 ≤ e ∧ e ≤ 1) ∧ J ≤ 2 ∧ J < k ∧ AxisStep q k v w d e J ∧
      (∃ z : ℤ, (cellN q k w d : ℤ) - cellN q k v d = e + z * (q : ℤ) ^ k) ∧
      (e = 0 → cellN q k w d = cellN q k v d) := by
  have hP : 3 ≤ q ^ k := by
    calc 3 ≤ q ^ 2 := by nlinarith
      _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  rcases step_cases (q ^ k) (cellN q k v d) (cellN q k w d) hP (cellN_lt q k v d)
    (cellN_lt q k w d) with h | h | h | h
  · exact ⟨0, 0, by norm_num, by norm_num, by omega, axisStep_zero q hq k v w d h,
      ⟨0, by rw [h]; ring⟩, fun _ => h⟩
  · refine ⟨1, Jof q k (cellN q k v d), by norm_num, Jof_le q k _, Jof_lt q k _ (by omega),
      axisStep_plus q hq k (by omega) v w d h, ⟨-(((cellN q k v d + 1) / q ^ k : ℕ) : ℤ), ?_⟩,
      fun h1 => absurd h1 (by norm_num)⟩
    have := Nat.mod_add_div (cellN q k v d + 1) (q ^ k)
    rw [← h] at this
    have h' : ((cellN q k w d : ℕ) : ℤ) + ((q ^ k : ℕ) : ℤ) * (((cellN q k v d + 1) / q ^ k : ℕ) : ℤ)
        = (cellN q k v d : ℤ) + 1 := by exact_mod_cast this
    push_cast at h' ⊢; linarith
  · refine ⟨-1, Jof q k (cellN q k w d), by norm_num, Jof_le q k _, Jof_lt q k _ (by omega),
      axisStep_minus q hq k (by omega) v w d h, ⟨(((cellN q k w d + 1) / q ^ k : ℕ) : ℤ), ?_⟩,
      fun h1 => absurd h1 (by norm_num)⟩
    have := Nat.mod_add_div (cellN q k w d + 1) (q ^ k)
    rw [← h] at this
    have h' : ((cellN q k v d : ℕ) : ℤ) + ((q ^ k : ℕ) : ℤ) * (((cellN q k w d + 1) / q ^ k : ℕ) : ℤ)
        = (cellN q k w d : ℤ) + 1 := by exact_mod_cast this
    push_cast at h' ⊢; linarith
  · exact absurd h hnf

lemma tl_eq_of_only (hq : 1 < q) (k : ℕ) (hk : 1 ≤ k) (c : Fin 4) (v w : Fin (4 * k) → ZMod q)
    (hother : ∀ d, d ≠ c → cellN q k w d = cellN q k v d) : tl q k w c = tl q k v c := by
  unfold tl tail
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_Ico] at hj
  congr 1
  unfold dv
  rw [dif_pos hj.2, dif_pos hj.2]
  have e := Dg_off_eq_of_only q hq k c v w hother ⟨j - k, by omega⟩ (by simp; omega)
  have hj' : (⟨j, hj.2⟩ : Fin (4 * k)) = ⟨k + ((⟨j - k, by omega⟩ : Fin (3 * k)) : ℕ), by simp; omega⟩ := by
    ext; simp; omega
  rw [hj', e]

lemma o_bound (k : ℕ) (v w : Fin (4 * k) → ZMod q) (c : Fin 4) :
    |(o0 q k w c : ℤ) - o0 q k v c| < q := by
  have h1 := dv_lt q k (Dg q k c w) k; have h2 := dv_lt q k (Dg q k c v) k
  simp only [o0]
  rw [abs_lt]; constructor <;> omega

lemma K4_eq (q : ℕ) : K4 q = K4i (q : ℤ) := by
  unfold K4 K4i
  by_cases h5 : q = 5
  · subst h5; simp
  · by_cases h7 : q = 7
    · subst h7; simp
    · rw [if_neg h5, if_neg h7, if_neg (by omega), if_neg (by omega)]

/-- **Theorem 4D(3), integer form.** -/
theorem main_bound (hq : Odd q) (hq5 : 5 ≤ q) (k : ℕ) (hk : 2 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (6 * k) * K4 q ≤ (q : ℤ) ^ 2 * ∑ c : Fin 4,
          ((cres (q ^ (4 * k)) ((D4point q k w c : ℤ) - (D4point q k v c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  have hq1 : 1 < q := by omega
  have hqz : (5 : ℤ) ≤ q := by exact_mod_cast hq5
  set u : ℤ := (q : ℤ) ^ (3 * k - 1) with hu_def
  have hu : 0 < u := by positivity
  have hpow : (q : ℤ) ^ (3 * k) = u * q := by rw [hu_def, ← pow_succ]; congr 1; omega
  have hN : ((q ^ (4 * k) : ℕ) : ℤ) = (q : ℤ) ^ (3 * k) * (q : ℤ) ^ k := by
    push_cast; rw [← pow_add]; congr 1; omega
  have hX : ∀ c, (D4point q k w c : ℤ) - D4point q k v c =
      (q : ℤ) ^ (3 * k) * ((cellN q k w c : ℤ) - cellN q k v c) +
      (u * ((o0 q k w c : ℤ) - o0 q k v c) + ((tl q k w c : ℤ) - tl q k v c)) := by
    intro c; rw [X_decomp q k hk, X_decomp q k hk]; ring
  have htl : ∀ c, |(tl q k w c : ℤ) - tl q k v c| < u := by
    intro c
    have h1 := tail_lt q k (by omega) (Dg q k c w); have h2 := tail_lt q k (by omega) (Dg q k c v)
    have h1' : ((tl q k w c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast h1
    have h2' : ((tl q k v c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast h2
    rw [abs_lt]; constructor <;> omega
  have hK : K4 q ≤ (q : ℤ) ^ 2 := by
    rw [K4_eq]; unfold K4i
    split_ifs <;> nlinarith
  have hK0 : 0 ≤ K4 q := by rw [K4_eq]; unfold K4i; split_ifs <;> positivity
  have hsum_nonneg : ∀ c ∈ (univ : Finset (Fin 4)), (0 : ℤ) ≤
      ((cres (q ^ (4 * k)) ((D4point q k w c : ℤ) - (D4point q k v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
    fun c _ => sq_nonneg _
  by_cases hfar : ∃ c, Far q k v w c
  · obtain ⟨c, hc⟩ := hfar
    have ho0 := o_bound q k v w c
    have hR : |u * ((o0 q k w c : ℤ) - o0 q k v c) + ((tl q k w c : ℤ) - tl q k v c)| <
        (q : ℤ) ^ (3 * k) := by
      have a2 := abs_add_le (u * ((o0 q k w c : ℤ) - o0 q k v c)) ((tl q k w c : ℤ) - tl q k v c)
      rw [abs_mul, abs_of_pos hu] at a2
      have := htl c
      have b1 : |(o0 q k w c : ℤ) - o0 q k v c| ≤ q - 1 := by omega
      rw [hpow]; nlinarith
    have hf := far_gen (q ^ (4 * k)) ((q : ℤ) ^ (3 * k)) ((q : ℤ) ^ k) (by positivity) (by positivity)
      hN _ _ hR hc
    rw [← hX c] at hf
    have hsq : ((q : ℤ) ^ (3 * k)) ^ 2 ≤
        ((cres (q ^ (4 * k)) ((D4point q k w c : ℤ) - (D4point q k v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hf 2
    have hsingle := Finset.single_le_sum hsum_nonneg (mem_univ c)
    calc (q : ℤ) ^ (6 * k) * K4 q ≤ (q : ℤ) ^ (6 * k) * (q : ℤ) ^ 2 := by gcongr
      _ = (q : ℤ) ^ 2 * ((q : ℤ) ^ (3 * k)) ^ 2 := by rw [← pow_mul]; ring_nf
      _ ≤ _ := by gcongr; exact hsq.trans hsingle
  · push_neg at hfar
    choose e J he hJ2 hJk hstep hz he0 using fun c => axis_classify q hq1 k hk v w c (hfar c)
    by_cases hall : ∀ c, e c = 0
    · exact absurd (eq_of_cellN q hq1 k v w (fun d => he0 d (hall d))).symm hvw
    push_neg at hall
    have hσ : ∀ c, ((o0 q k w c : ℤ) - o0 q k v c) ≡ ∑ d, e d * PJ c d (J d) [ZMOD q] := by
      intro c
      have h := Dg_off_sub q hq k hk c v w e J hJk hstep
      rw [← o0_cast q k (by omega) w c, ← o0_cast q k (by omega) v c] at h
      rw [← ZMod.intCast_eq_intCast_iff]
      simp only [PJ]
      push_cast at h ⊢
      exact h
    set V : Fin 4 → ℤ := fun c => e c * q + ((o0 q k w c : ℤ) - o0 q k v c) with hV
    have hVb : ∀ c, |V c| ≤ 2 * (q : ℤ) - 1 := by
      intro c
      have ho := o_bound q k v w c
      have b1 : |(o0 q k w c : ℤ) - o0 q k v c| ≤ q - 1 := by omega
      have b0 : |e c| ≤ 1 := abs_le.mpr ⟨(he c).1, (he c).2⟩
      have := abs_add_le (e c * q) ((o0 q k w c : ℤ) - o0 q k v c)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < q)] at this
      simp only [hV]
      nlinarith
    have hXV : ∀ c, ∃ z : ℤ, (D4point q k w c : ℤ) - D4point q k v c =
        u * V c + ((tl q k w c : ℤ) - tl q k v c) + z * ((q ^ (4 * k) : ℕ) : ℤ) := by
      intro c
      obtain ⟨z, hzc⟩ := hz c
      refine ⟨z, ?_⟩
      rw [hX c, hzc, hN, hpow]; simp only [hV]; ring
    have hqk : (4 : ℤ) ≤ (q : ℤ) ^ k := by
      calc (4 : ℤ) ≤ q := by omega
        _ = (q : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℤ) ^ k := pow_le_pow_right₀ (by omega) (by omega)
    set x : Fin 4 → ℤ := fun c =>
      ((cres (q ^ (4 * k)) ((D4point q k w c : ℤ) - (D4point q k v c : ℤ)) : ℕ) : ℤ) / u with hx_def
    have hnear : ∀ c, 0 ≤ x c ∧ |V c| - 1 ≤ x c ∧
        ((tl q k w c : ℤ) - tl q k v c = 0 → |V c| ≤ x c) ∧
        u * x c ≤ ((cres (q ^ (4 * k)) ((D4point q k w c : ℤ) - (D4point q k v c : ℤ)) : ℕ) : ℤ) := by
      intro c
      obtain ⟨z, hzc⟩ := hXV c
      simp only [hx_def]
      rw [hzc]
      refine near_gen (q ^ (4 * k)) u (V c) _ z hu (htl c) ?_
      rw [hN, hpow]
      have := abs_add_le (u * V c) ((tl q k w c : ℤ) - tl q k v c)
      rw [abs_mul, abs_of_pos hu] at this
      have := hVb c; have := htl c
      have h4 : 4 * (u * q) ≤ u * q * (q : ℤ) ^ k := by
        have : 0 < u * q := by positivity
        nlinarith
      nlinarith
    have hqcase : (q : ℤ) = 5 ∨ (q : ℤ) = 7 ∨ (q : ℤ) = 9 ∨ 11 ≤ (q : ℤ) := by
      obtain ⟨t, ht⟩ := hq
      have : q = 5 ∨ q = 7 ∨ q = 9 ∨ 11 ≤ q := by omega
      rcases this with h | h | h | h
      · left; exact_mod_cast h
      · right; left; exact_mod_cast h
      · right; right; left; exact_mod_cast h
      · right; right; right; exact_mod_cast h
    have hkey := key_ineq checkPoly_eq checkSmall5 checkSmall7 checkSmall9 checkSigBound_eq
      (q : ℤ) hqcase e he hall J hJ2 (fun c => (o0 q k w c : ℤ) - o0 q k v c) x
      (fun c => ⟨hσ c, o_bound q k v w c⟩) (fun c => (hnear c).1) (by
        intro c
        split_ifs with honly
        · apply (hnear c).2.2.1
          have := tl_eq_of_only q hq1 k (by omega) c v w (fun d hd => he0 d (honly.2 d hd))
          rw [this]; ring
        · exact (hnear c).2.1)
    rw [← K4_eq] at hkey
    have hsq : ∀ c, (u * x c) ^ 2 ≤
        ((cres (q ^ (4 * k)) ((D4point q k w c : ℤ) - (D4point q k v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      fun c => pow_le_pow_left₀ (mul_nonneg hu.le (hnear c).1) (hnear c).2.2.2 2
    have hu6 : (q : ℤ) ^ (6 * k) = (q : ℤ) ^ 2 * u ^ 2 := by
      rw [hu_def, ← pow_mul, ← pow_add]; congr 1; omega
    rw [Fin.sum_univ_four]
    calc (q : ℤ) ^ (6 * k) * K4 q ≤ (q : ℤ) ^ (6 * k) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) := by
          gcongr
      _ = (q : ℤ) ^ 2 * ((u * x 0) ^ 2 + (u * x 1) ^ 2 + (u * x 2) ^ 2 + (u * x 3) ^ 2) := by
          rw [hu6]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add (add_le_add (hsq 0) (hsq 1)) (hsq 2)) (hsq 3)) (by positivity)

end

/-- **Theorem 4D(3), exact integer form.** -/
theorem D4_sep (q k : ℕ) (hq : Odd q) (hq5 : 5 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (6 * k) * K4 q ≤
      (q : ℤ) ^ 2 * (torusDist2 (q ^ (4 * k)) (D4point q k v) (D4point q k w) : ℤ) := by
  haveI : NeZero q := ⟨by omega⟩
  have h := main_bound q hq hq5 k hk w v (Ne.symm hvw)
  unfold torusDist2
  push_cast
  exact h

/-- **Theorem 4D(3), real form.** -/
theorem D4_sep_real (q k : ℕ) (hq : Odd q) (hq5 : 5 ≤ q) (hk : 2 ≤ k)
    (v w : Fin (4 * k) → ZMod q) (hvw : v ≠ w) :
    c4 q * ((q : ℝ) ^ (4 * k)) ^ (-(1 / 4 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (4 * k)) ((D4point q k v c : ℤ) - (D4point q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (4 * k)) ^ 2) := by
  have hZ := D4_sep q k hq hq5 hk v w hvw
  unfold torusDist2 at hZ
  have hR : (q : ℝ) ^ (6 * k) * (K4 q : ℝ)
      ≤ (q : ℝ) ^ 2 * ∑ c, ((cres (q ^ (4 * k)) ((D4point q k v c : ℤ) - (D4point q k w c : ℤ)) : ℝ)) ^ 2 := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this
    exact this
  have hq0 : (0 : ℝ) < q := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hK0 : (0 : ℝ) ≤ (K4 q : ℝ) := by
    have : 0 ≤ K4 q := by unfold K4; split_ifs <;> positivity
    exact_mod_cast this
  set S : ℝ := ∑ c, ((cres (q ^ (4 * k)) ((D4point q k v c : ℤ) - (D4point q k w c : ℤ)) : ℝ)) ^ 2
    with hS
  have hc4 : c4 q ^ 2 = (K4 q : ℝ) / (q : ℝ) ^ 2 := by
    unfold c4
    rw [div_pow, Real.sq_sqrt hK0]
  have hrp : ((q : ℝ) ^ (4 * k)) ^ (-(1 / 4 : ℝ)) = 1 / (q : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, show ((4 * k : ℕ) : ℝ) * (-(1 / 4 : ℝ)) =
      -(k : ℝ) by push_cast; ring, Real.rpow_neg hq0.le, Real.rpow_natCast, one_div]
  have hsum : ∑ c, ((cres (q ^ (4 * k)) ((D4point q k v c : ℤ) - (D4point q k w c : ℤ)) : ℝ)
      / (q : ℝ) ^ (4 * k)) ^ 2 = S / ((q : ℝ) ^ (4 * k)) ^ 2 := by
    rw [hS, Finset.sum_div]; refine Finset.sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum, hrp]
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, hc4, div_pow, one_pow]
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : ((q : ℝ) ^ (4 * k)) ^ 2 = (q : ℝ) ^ (6 * k) * ((q : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  rw [e1]
  nlinarith [hR, sq_nonneg ((q : ℝ) ^ k)]

end Z3NetD4.Proofs

module
public import Mathlib
public import Z3Net.KNSep
public import Z3Net.KNBnet1

@[expose] public section

/-!
# `B1_sep`, `B2_sep`: separation of the all-`p` families (the research notes, §3, §4)

Fine positions `P_c = ` the first `k + 1` digits of coordinate `c` (`P_c = n_c` for a full
coordinate, `p n_c + S_c` for a skeleton coordinate); `a_c` the centred difference of `P_c` mod
`p^(k+1)`.  Lemma T (`prefix_bound`): `cres_c ≥ |a_c| f - (f - 1)`, `f = p^(m-k-1)`.  The skeleton
rows put `a` (resp. a carry-corrected `u`) into an index-`p` (resp. index-`p²`) lattice whose
nonzero vectors are long (`latL2`, `latL1`).
-/

namespace Z3NetKN.Geom

open Finset Matrix Z3NetKN.Relax

variable {p r k : ℕ}

/-! ## Generic: prefix bound, fine positions -/

/-- **Lemma T** for an arbitrary prefix length `a`. -/
lemma prefix_bound [NeZero p] {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p)
    (a : ℕ) (ha : a ≤ m) :
    |cen (p ^ a) ((pre p (dg A v) a : ℤ) - pre p (dg A w) a)| * ((p ^ (m - a) : ℕ) : ℤ)
        - (((p ^ (m - a) : ℕ) : ℤ) - 1) ≤
      (cres (p ^ m) ((coord p m A v : ℤ) - coord p m A w) : ℤ) := by
  have hp0 : 0 < p := Nat.pos_of_neZero p
  set U := p ^ (m - a) with hU
  rw [coord_split A v a ha, coord_split A w a ha]
  obtain ⟨z, hz⟩ := cen_spec (p ^ a) ((pre p (dg A v) a : ℤ) - pre p (dg A w) a)
  have hN : p ^ m = p ^ a * U := by rw [hU, ← pow_add]; congr 1; omega
  have key : ((pre p (dg A v) a * U + low A v a : ℕ) : ℤ) - ((pre p (dg A w) a * U + low A w a : ℕ) : ℤ) =
      cen (p ^ a) ((pre p (dg A v) a : ℤ) - pre p (dg A w) a) * U +
        ((low A v a : ℤ) - low A w a) + z * ((p ^ a * U : ℕ) : ℤ) := by
    push_cast
    have : (pre p (dg A v) a : ℤ) - pre p (dg A w) a - (cen (p ^ a) ((pre p (dg A v) a : ℤ) -
        pre p (dg A w) a) + z * ((p ^ a : ℕ) : ℤ)) = 0 := by rw [← hz]; ring
    push_cast at this
    linear_combination (U : ℤ) * this
  rw [hN, key]
  exact cres_lower (p ^ a) U (pow_pos hp0 _) (pow_pos hp0 _) _ _ z _
    (cen_abs _ (pow_pos hp0 _) _) (low_diff A v w a)

lemma eq_of_cen_zero (K x y : ℕ) (hx : x < K) (hy : y < K) (h : cen K ((x : ℤ) - y) = 0) : x = y := by
  obtain ⟨z, hz⟩ := cen_spec K ((x : ℤ) - y)
  rw [h, zero_add] at hz
  exact eq_of_sub_eq_mul _ _ _ hx hy z hz

lemma cen_cast_mod (K x y : ℕ) (hK : 1 ≤ K) :
    ((cen (p ^ K) ((x : ℤ) - y) : ℤ) : ZMod p) = ((x % p : ℕ) : ZMod p) - ((y % p : ℕ) : ZMod p) := by
  obtain ⟨z, hz⟩ := cen_spec (p ^ K) ((x : ℤ) - y)
  have h2 : (((x : ℤ) - y : ℤ) : ZMod p) = ((cen (p ^ K) ((x : ℤ) - y) + z * ((p ^ K : ℕ) : ℤ) : ℤ) : ZMod p) := by
    rw [← hz]
  push_cast at h2
  rw [ZMod.natCast_mod, ZMod.natCast_mod]
  have h1' : ((p : ZMod p)) ^ K = 0 := by
    rw [ZMod.natCast_self]; exact zero_pow (by omega)
  rw [h1', mul_zero, add_zero] at h2
  exact h2.symm

/-- Fine position: the first `k + 1` digits. -/
def Pf {m : ℕ} (k : ℕ) (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) : ℕ :=
  pre p (dg A v) (k + 1)

lemma Pf_lt [NeZero p] {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) :
    Pf k A v < p ^ (k + 1) :=
  pre_lt p (Nat.pos_of_neZero p) _ _ (fun j _ => dg_lt A v _)

section Graph

variable {sk : Fin 3 → Fin 3 → Fin 4 → ℤ}
  {C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)}

lemma Pf_full (hr : r = 1 ∨ r = 2) (hC : IsKNskel r p k sk C) (v : Fin (3 * k + r) → ZMod p)
    (c : Fin 3) (hc : (c : ℕ) < r) : Pf k (C c) v = nC r k v c := by
  have hd : depth r k c = k + 1 := by unfold depth; rw [if_pos hc]
  have := pre_dg_depth sk C hr hC v c
  rw [hd] at this
  exact this

lemma Pf_skel (hr : r = 1 ∨ r = 2) (hC : IsKNskel r p k sk C) (v : Fin (3 * k + r) → ZMod p)
    (c : Fin 3) (hc : r ≤ (c : ℕ)) : Pf k (C c) v = nC r k v c * p + dg (C c) v k := by
  have hd : depth r k c = k := by unfold depth; rw [if_neg (by omega)]
  have := pre_dg_depth sk C hr hC v c
  rw [hd] at this
  unfold Pf
  rw [pre_succ, this]

lemma Pf_mod_full [NeZero p] (hr : r = 1 ∨ r = 2) (hC : IsKNskel r p k sk C)
    (v : Fin (3 * k + r) → ZMod p) (c : Fin 3) (hc : (c : ℕ) < r) :
    ((Pf k (C c) v % p : ℕ) : ZMod p) = vz v (off r k c + k) := by
  have hd : depth r k c = k + 1 := by unfold depth; rw [if_pos hc]
  rw [Pf_full hr hC v c hc]
  have := nC_digit v c 0 (by omega)
  rw [pow_zero, Nat.div_one, hd, show k + 1 - 1 - 0 = k by omega] at this
  rw [this, vv_cast]

lemma Pf_mod_skel [NeZero p] (hr : r = 1 ∨ r = 2) (hC : IsKNskel r p k sk C)
    (v : Fin (3 * k + r) → ZMod p) (c : Fin 3) (hc : r ≤ (c : ℕ)) :
    ((Pf k (C c) v % p : ℕ) : ZMod p) = vz (C c *ᵥ v) k := by
  rw [Pf_skel hr hC v c hc, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (dg_lt _ _ _)]
  simp [dg, ZMod.natCast_zmod_val]

lemma Pf_div [NeZero p] (hr : r = 1 ∨ r = 2) (hC : IsKNskel r p k sk C) (hk : 1 ≤ k)
    (v : Fin (3 * k + r) → ZMod p) (c : Fin 3) :
    ((Pf k (C c) v / p % p : ℕ) : ZMod p) = vz v (off r k c + (k - 1)) := by
  by_cases hc : (c : ℕ) < r
  · have hd : depth r k c = k + 1 := by unfold depth; rw [if_pos hc]
    rw [Pf_full hr hC v c hc]
    have := nC_digit v c 1 (by omega)
    rw [pow_one, hd, show k + 1 - 1 - 1 = k - 1 by omega] at this
    rw [this, vv_cast]
  · have hd : depth r k c = k := by unfold depth; rw [if_neg hc]
    have hp0 : 0 < p := Nat.pos_of_neZero p
    rw [Pf_skel hr hC v c (by omega), Nat.mul_comm, Nat.mul_add_div hp0,
      Nat.div_eq_of_lt (dg_lt _ _ _), add_zero]
    have := nC_digit v c 0 (by omega)
    rw [pow_zero, Nat.div_one, hd, show k - 1 - 0 = k - 1 by omega] at this
    rw [this, vv_cast]

lemma eq_of_Pf_eq [NeZero p] (hr : r = 1 ∨ r = 2) (hC : IsKNskel r p k sk C)
    (v w : Fin (3 * k + r) → ZMod p) (h : ∀ c, Pf k (C c) v = Pf k (C c) w) : v = w := by
  refine eq_of_nC_eq hr v w fun c => ?_
  by_cases hc : (c : ℕ) < r
  · rw [← Pf_full hr hC v c hc, ← Pf_full hr hC w c hc, h c]
  · have hp0 : 0 < p := Nat.pos_of_neZero p
    have e := h c
    rw [Pf_skel hr hC v c (by omega), Pf_skel hr hC w c (by omega)] at e
    have e2 := congrArg (· / p) e
    rwa [Nat.mul_comm, Nat.mul_add_div hp0, Nat.div_eq_of_lt (dg_lt _ _ _), add_zero,
      Nat.mul_comm, Nat.mul_add_div hp0, Nat.div_eq_of_lt (dg_lt _ _ _), add_zero] at e2

/-- Change of a skeleton digit through the designed rows. -/
lemma skel_diff (hr : r = 1 ∨ r = 2) (hC : IsKNskel r p k sk C) (v w : Fin (3 * k + r) → ZMod p)
    (c : Fin 3) (hc : r ≤ (c : ℕ)) :
    vz (C c *ᵥ v) k - vz (C c *ᵥ w) k = ∑ d : Fin 3, ∑ l ∈ range (depth r k d),
      ((winEntry (sk c d) (win r d) (depth r k d) l : ℤ) : ZMod p) *
        (vz v (off r k d + l) - vz w (off r k d + l)) := by
  have hd : depth r k c = k := by unfold depth; rw [if_neg (by omega)]
  rw [row_diff hr (C c) v w k (by omega)]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l hl => ?_
  simp only [mem_range] at hl
  have := hC.2 c d hc l hl
  rw [hd] at this
  rw [this]

end Graph

/-! ## Window sums of one- and two-entry rows -/

lemma win_sum_single (x : ℤ) (L K : ℕ) (hL : 1 ≤ L) (hK : 1 ≤ K) (D : ℕ → ZMod p) :
    ∑ l ∈ range K, ((winEntry ![x, 0, 0, 0] L K l : ℤ) : ZMod p) * D l = (x : ZMod p) * D (K - 1) := by
  rw [Finset.sum_eq_single (K - 1)]
  · rw [Z3NetKN.Frame.winEntry_single x L K (K - 1) hL (by omega), if_pos (by omega)]
  · intro l hl hne
    simp only [mem_range] at hl
    rw [Z3NetKN.Frame.winEntry_single x L K l hL hl, if_neg (by omega)]; simp
  · intro h; simp at h; omega

lemma win_sum_two (x y : ℤ) (L K : ℕ) (hL : 2 ≤ L) (hK : 2 ≤ K) (D : ℕ → ZMod p) :
    ∑ l ∈ range K, ((winEntry ![x, y, 0, 0] L K l : ℤ) : ZMod p) * D l =
      (x : ZMod p) * D (K - 1) + (y : ZMod p) * D (K - 2) := by
  have e : ∀ l ∈ range K, ((winEntry ![x, y, 0, 0] L K l : ℤ) : ZMod p) * D l =
      (if l = K - 1 then (x : ZMod p) * D l else 0) + (if l = K - 2 then (y : ZMod p) * D l else 0) := by
    intro l hl
    simp only [mem_range] at hl
    rw [Z3NetKN.Frame.winEntry_two x y L K l hL hl]
    by_cases h1 : l = K - 1
    · rw [if_pos (by omega), if_pos h1, if_neg (by omega)]; simp
    · by_cases h2 : l = K - 2
      · rw [if_neg (by omega), if_pos (by omega), if_neg h1, if_pos h2]; simp
      · rw [if_neg (by omega), if_neg (by omega), if_neg h1, if_neg h2]; simp
  rw [sum_congr rfl e, sum_add_distrib, sum_ite_eq', sum_ite_eq', if_pos (by simp; omega),
    if_pos (by simp; omega)]

lemma win_sum_zero (L K : ℕ) (D : ℕ → ZMod p) :
    ∑ l ∈ range K, ((winEntry (0 : Fin 4 → ℤ) L K l : ℤ) : ZMod p) * D l = 0 := by
  refine sum_eq_zero fun l _ => ?_
  unfold winEntry; split_ifs <;> simp

/-! ## Lattice lemmas -/

/-- **L2.** -/
lemma latL2 (p ρ : ℕ) (hρ : 1 ≤ ρ) (hρp : ρ * (1 + ρ + ρ ^ 2) ≤ p) (a0 a1 a2 : ℤ)
    (hdiv : (p : ℤ) ∣ a2 - ρ * a0 - ρ ^ 2 * a1) (hne : ¬(a0 = 0 ∧ a1 = 0 ∧ a2 = 0)) :
    (ρ : ℤ) ≤ |a0| ∨ (ρ : ℤ) ≤ |a1| ∨ (ρ : ℤ) ≤ |a2| := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h1, h2⟩ := hcon
  have hρ' : (1 : ℤ) ≤ ρ := by exact_mod_cast hρ
  have hp' : (ρ : ℤ) * (1 + ρ + ρ ^ 2) ≤ p := by exact_mod_cast hρp
  have b0 : |(ρ : ℤ) * a0| ≤ ρ * (ρ - 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have b1 : |(ρ : ℤ) ^ 2 * a1| ≤ ρ ^ 2 * (ρ - 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have hlt : |a2 - ρ * a0 - ρ ^ 2 * a1| < p := by
    have t1 := abs_sub (a2 - ρ * a0) (ρ ^ 2 * a1)
    have t2 := abs_sub a2 (ρ * a0)
    have : (ρ : ℤ) - 1 + ρ * (ρ - 1) + ρ ^ 2 * (ρ - 1) < p := by nlinarith
    have : |a2| ≤ ρ - 1 := by omega
    linarith
  have hz := Int.eq_zero_of_abs_lt_dvd hdiv hlt
  have ha2 : a2 = ρ * (a0 + ρ * a1) := by linear_combination hz
  have hd2 : (ρ : ℤ) ∣ a2 := ⟨_, ha2⟩
  have a2z : a2 = 0 := Int.eq_zero_of_abs_lt_dvd hd2 h2
  rw [a2z] at ha2
  have hs : a0 + ρ * a1 = 0 := by
    rcases mul_eq_zero.mp ha2.symm with h | h
    · omega
    · exact h
  have hd1 : (ρ : ℤ) ∣ a0 := ⟨-a1, by linear_combination hs⟩
  have a0z : a0 = 0 := Int.eq_zero_of_abs_lt_dvd hd1 h0
  have a1z : a1 = 0 := by
    rw [a0z, zero_add] at hs
    rcases mul_eq_zero.mp hs with h | h
    · omega
    · exact h
  exact hne ⟨a0z, a1z, a2z⟩

/-- **L1.** -/
lemma latL1 (p ρ : ℕ) (hρ : 1 ≤ ρ) (hρp : ρ ^ 2 * (ρ + 1) ≤ p) (u0 u1 u2 B : ℤ)
    (h1 : (p : ℤ) ∣ u1 - ρ * u0) (h2 : (p : ℤ) ∣ u2 - ρ ^ 2 * u0)
    (hb0 : |u0| ≤ B) (hb1 : |u1| ≤ B) (hb2 : |u2| ≤ B) (hne : ¬(u0 = 0 ∧ u1 = 0 ∧ u2 = 0)) :
    (ρ : ℤ) ^ 2 ≤ B := by
  have hρ' : (1 : ℤ) ≤ ρ := by exact_mod_cast hρ
  have hp' : (ρ : ℤ) ^ 2 * (ρ + 1) ≤ p := by exact_mod_cast hρp
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hb0
  by_cases hbig : (p : ℤ) ≤ B * (ρ + 1)
  · have : (ρ : ℤ) ^ 2 * (ρ + 1) ≤ B * (ρ + 1) := le_trans hp' hbig
    exact le_of_mul_le_mul_right this (by positivity)
  · push_neg at hbig
    have e1 : |u1 - ρ * u0| < p := by
      have t := abs_sub u1 (ρ * u0)
      have : |(ρ : ℤ) * u0| ≤ ρ * B := by
        rw [abs_mul, abs_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left hb0 (by positivity)
      nlinarith
    have z1 := Int.eq_zero_of_abs_lt_dvd h1 e1
    have h3 : (p : ℤ) ∣ u2 - ρ * u1 := by
      have : u2 - ρ * u1 = (u2 - ρ ^ 2 * u0) - ρ * (u1 - ρ * u0) := by ring
      rw [this]; exact dvd_sub h2 (dvd_mul_of_dvd_right h1 _)
    have e3 : |u2 - ρ * u1| < p := by
      have t := abs_sub u2 (ρ * u1)
      have : |(ρ : ℤ) * u1| ≤ ρ * B := by
        rw [abs_mul, abs_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left hb1 (by positivity)
      nlinarith
    have z3 := Int.eq_zero_of_abs_lt_dvd h3 e3
    have hu1 : u1 = ρ * u0 := by linear_combination z1
    have hu2 : u2 = ρ ^ 2 * u0 := by linear_combination z3 + ρ * z1
    have hu0 : u0 ≠ 0 := by
      intro h0; apply hne
      refine ⟨h0, ?_, ?_⟩
      · rw [hu1, h0, mul_zero]
      · rw [hu2, h0, mul_zero]
    have : (ρ : ℤ) ^ 2 ≤ |u2| := by
      rw [hu2, abs_mul, abs_of_nonneg (by positivity)]
      have : 1 ≤ |u0| := Int.one_le_abs hu0
      nlinarith
    linarith

end Z3NetKN.Geom

namespace Z3NetKN.Proofs

open Finset Matrix Z3NetKN.Relax Z3NetKN.Geom

/-- **`m ≡ 2`, all primes, separation** (`B2_sep` of `ChallengeKN.lean`). -/
theorem B2_sep (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 1 ≤ ρ)
    (hρp : ρ * (1 + ρ + ρ ^ 2) ≤ p)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p))
    (hC : IsKNskel 2 p k (skB2 ρ) C) (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    (ρ - 1) ^ 2 * p ^ (4 * k + 2) ≤
      torusDist2 (p ^ (3 * k + 2)) (digPoint p (3 * k + 2) C v) (digPoint p (3 * k + 2) C w) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hr : (2 = 1 ∨ 2 = 2) := Or.inr rfl
  set a : Fin 3 → ℤ := fun c => cen (p ^ (k + 1)) ((Pf k (C c) v : ℤ) - Pf k (C c) w) with ha
  have hcast : ∀ c, ((a c : ℤ) : ZMod p) =
      ((Pf k (C c) v % p : ℕ) : ZMod p) - ((Pf k (C c) w % p : ℕ) : ZMod p) :=
    fun c => cen_cast_mod (k + 1) _ _ (by omega)
  have hrel : ((a 2 : ℤ) : ZMod p) =
      (ρ : ZMod p) * ((a 0 : ℤ) : ZMod p) + (ρ : ZMod p) ^ 2 * ((a 1 : ℤ) : ZMod p) := by
    rw [hcast 2, hcast 0, hcast 1, Pf_mod_skel hr hC v 2 (by simp), Pf_mod_skel hr hC w 2 (by simp),
      Pf_mod_full hr hC v 0 (by simp), Pf_mod_full hr hC w 0 (by simp),
      Pf_mod_full hr hC v 1 (by simp), Pf_mod_full hr hC w 1 (by simp),
      skel_diff hr hC v w 2 (by simp), Fin.sum_univ_three]
    have h0 : skB2 ρ 2 0 = ![(ρ : ℤ), 0, 0, 0] := rfl
    have h1 : skB2 ρ 2 1 = ![(ρ : ℤ) ^ 2, 0, 0, 0] := rfl
    have h2 : skB2 ρ 2 2 = 0 := rfl
    rw [h0, h1, h2, win_sum_single _ _ _ (by simp [win]) (by simp [depth]),
      win_sum_single _ _ _ (by simp [win]) (by simp [depth]), win_sum_zero]
    have d0 : depth 2 k 0 - 1 = k := by simp [depth]
    have d1 : depth 2 k 1 - 1 = k := by simp [depth]
    rw [d0, d1]
    push_cast; ring
  have hdiv : (p : ℤ) ∣ a 2 - ρ * a 0 - ρ ^ 2 * a 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hrel]; ring
  have hne : ¬(a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hvw
    refine eq_of_Pf_eq hr hC v w fun c => eq_of_cen_zero _ _ _ (Pf_lt _ v) (Pf_lt _ w) ?_
    fin_cases c
    exacts [h0, h1, h2]
  obtain ⟨c, hc⟩ : ∃ c, (ρ : ℤ) ≤ |a c| := by
    rcases latL2 p ρ hρ hρp _ _ _ hdiv hne with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hb : |a c| * ((p ^ (3 * k + 2 - (k + 1)) : ℕ) : ℤ) - (((p ^ (3 * k + 2 - (k + 1)) : ℕ) : ℤ) - 1) ≤
      (cres (p ^ (3 * k + 2)) ((coord p (3 * k + 2) (C c) v : ℤ) - coord p (3 * k + 2) (C c) w) : ℤ) :=
    prefix_bound (C c) v w (k + 1) (by omega)
  set f := p ^ (3 * k + 2 - (k + 1)) with hf
  set cr := cres (p ^ (3 * k + 2)) ((coord p (3 * k + 2) (C c) v : ℤ) - coord p (3 * k + 2) (C c) w)
  have h1 : (((ρ - 1) * f : ℕ) : ℤ) ≤ cr := by
    push_cast [Nat.cast_sub hρ]
    have hf0 : (0 : ℤ) ≤ f := by positivity
    have := mul_le_mul_of_nonneg_right hc hf0
    linarith
  have h1' : (ρ - 1) * f ≤ cr := by exact_mod_cast h1
  calc (ρ - 1) ^ 2 * p ^ (4 * k + 2) = ((ρ - 1) * f) ^ 2 := by
        rw [hf, mul_pow, ← pow_mul]; congr 2; omega
    _ ≤ cr ^ 2 := Nat.pow_le_pow_left h1' 2
    _ ≤ _ := cres_le_torus _ (digPoint p (3 * k + 2) C v) (digPoint p (3 * k + 2) C w) c

lemma pat1_spec (δ : ℤ) (ch : ℕ) (h0 : δ = 0 → ch = 0) :
    pat δ ch 1 = 0 ∨ (pat δ ch 1 = 1 ∧ 0 < δ) ∨ (pat δ ch 1 = -1 ∧ δ < 0) := by
  unfold pat sgn
  rcases lt_trichotomy δ 0 with h | h | h
  · split_ifs <;> simp_all
  · simp [h0 h]
  · split_ifs <;> simp_all

/-- **`m ≡ 1`, all primes, separation** (`B1_sep` of `ChallengeKN.lean`). -/
theorem B1_sep (p k ρ : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hρ : 2 ≤ ρ)
    (hρp : ρ ^ 2 * (ρ + 1) ≤ p)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p))
    (hC : IsKNskel 1 p k (skB1 ρ) C) (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    (ρ ^ 2 - 4) ^ 2 * p ^ (4 * k) ≤
      torusDist2 (p ^ (3 * k + 1)) (digPoint p (3 * k + 1) C v) (digPoint p (3 * k + 1) C w) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hr : (1 = 1 ∨ 1 = 2) := Or.inl rfl
  have hp2 := hp.two_le
  set a : Fin 3 → ℤ := fun c => cen (p ^ (k + 1)) ((Pf k (C c) v : ℤ) - Pf k (C c) w) with ha
  have hρ' : (2 : ℤ) ≤ ρ := by exact_mod_cast hρ
  have hρp' : (ρ : ℤ) ^ 2 * (ρ + 1) ≤ p := by exact_mod_cast hρp
  have hρ2p : (ρ : ℤ) ^ 2 + 2 ≤ p := by nlinarith
  have key : ∃ c, (ρ : ℤ) ^ 2 - 3 ≤ |a c| := by
    by_contra hcon
    push_neg at hcon
    have hsmall : ∀ c, |a c| < p := fun c => by have := hcon c; omega
    have hcar : ∀ c : Fin 3, ∃ ch, ch < min (k + 1) 2 ∧ (a c = 0 → ch = 0) ∧ ∀ i < min (k + 1) 2,
        ((Pf k (C c) v / p ^ i % p : ℕ) : ZMod p) - ((Pf k (C c) w / p ^ i % p : ℕ) : ZMod p) =
          ((pat (a c) ch i : ℤ) : ZMod p) := by
      intro c
      obtain ⟨z, hz⟩ := cen_spec (p ^ (k + 1)) ((Pf k (C c) v : ℤ) - Pf k (C c) w)
      exact carry p (k + 1) 2 (by omega) (by omega) (by norm_num) (by norm_num) _ _
        (Pf_lt _ v) (Pf_lt _ w) (a c) z (hsmall c) hz
    choose ch hch1 hch0 hchD using hcar
    set ξ : Fin 3 → ℤ := fun c => pat (a c) (ch c) 1 with hξ
    have d0 : ∀ c, ((a c : ℤ) : ZMod p) =
        ((Pf k (C c) v % p : ℕ) : ZMod p) - ((Pf k (C c) w % p : ℕ) : ZMod p) :=
      fun c => cen_cast_mod (k + 1) _ _ (by omega)
    have d1 : ∀ c, ((ξ c : ℤ) : ZMod p) = vz v (off 1 k c + (k - 1)) - vz w (off 1 k c + (k - 1)) := by
      intro c
      have := hchD c 1 (by omega)
      rw [pow_one, Pf_div hr hC hk v c, Pf_div hr hC hk w c] at this
      exact this.symm
    have hY : ((a 1 : ℤ) : ZMod p) = (ρ : ZMod p) * ((a 0 : ℤ) : ZMod p) + ((ξ 2 : ℤ) : ZMod p) := by
      rw [d0 1, d0 0, d1 2, Pf_mod_skel hr hC v 1 (by simp), Pf_mod_skel hr hC w 1 (by simp),
        Pf_mod_full hr hC v 0 (by simp), Pf_mod_full hr hC w 0 (by simp),
        skel_diff hr hC v w 1 (by simp), Fin.sum_univ_three]
      have h0 : skB1 ρ 1 0 = ![(ρ : ℤ), 0, 0, 0] := rfl
      have h1 : skB1 ρ 1 1 = 0 := rfl
      have h2 : skB1 ρ 1 2 = ![(1 : ℤ), 0, 0, 0] := rfl
      rw [h0, h1, h2, win_sum_single _ _ _ (by simp [win]) (by simp [depth]), win_sum_zero,
        win_sum_single _ _ _ (by simp [win]) (by simp [depth]; omega)]
      have e0 : depth 1 k 0 - 1 = k := by simp [depth]
      have e2 : depth 1 k 2 - 1 = k - 1 := by simp [depth]
      rw [e0, e2]
      push_cast; ring
    have hZ : ((a 2 : ℤ) : ZMod p) = (ρ : ZMod p) ^ 2 * ((a 0 : ℤ) : ZMod p) + ((ξ 0 : ℤ) : ZMod p) +
        ((ξ 1 : ℤ) : ZMod p) - ((ξ 2 : ℤ) : ZMod p) := by
      rw [d0 2, d0 0, d1 0, d1 1, d1 2, Pf_mod_skel hr hC v 2 (by simp), Pf_mod_skel hr hC w 2 (by simp),
        Pf_mod_full hr hC v 0 (by simp), Pf_mod_full hr hC w 0 (by simp),
        skel_diff hr hC v w 2 (by simp), Fin.sum_univ_three]
      have h0 : skB1 ρ 2 0 = ![(ρ : ℤ) ^ 2, 1, 0, 0] := rfl
      have h1 : skB1 ρ 2 1 = ![(1 : ℤ), 0, 0, 0] := rfl
      have h2 : skB1 ρ 2 2 = ![(-1 : ℤ), 0, 0, 0] := rfl
      rw [h0, h1, h2, win_sum_two _ _ _ _ (by simp [win]) (by simp [depth]; omega),
        win_sum_single _ _ _ (by simp [win]) (by simp [depth]; omega),
        win_sum_single _ _ _ (by simp [win]) (by simp [depth]; omega)]
      have e0 : depth 1 k 0 - 1 = k := by simp [depth]
      have e0' : depth 1 k 0 - 2 = k - 1 := by simp [depth]
      have e1 : depth 1 k 1 - 1 = k - 1 := by simp [depth]
      have e2 : depth 1 k 2 - 1 = k - 1 := by simp [depth]
      rw [e0, e0', e1, e2]
      push_cast; ring
    have hdiv1 : (p : ℤ) ∣ (a 1 - ξ 2) - ρ * a 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hY]; ring
    have hdiv2 : (p : ℤ) ∣ (a 2 - ξ 0 - ξ 1 + ξ 2) - ρ ^ 2 * a 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hZ]; ring
    have hspec := fun c => pat1_spec (a c) (ch c) (hch0 c)
    have hξb : ∀ c, |ξ c| ≤ 1 := by
      intro c
      rcases hspec c with h | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [hξ, h] <;> norm_num
    have hab : ∀ c, |a c| ≤ (ρ : ℤ) ^ 2 - 4 := fun c => by have := hcon c; omega
    have hu0 : a 0 = 0 ∧ a 1 - ξ 2 = 0 ∧ a 2 - ξ 0 - ξ 1 + ξ 2 = 0 := by
      by_contra hne
      have := latL1 p ρ (by omega) hρp (a 0) (a 1 - ξ 2) (a 2 - ξ 0 - ξ 1 + ξ 2) ((ρ : ℤ) ^ 2 - 1)
        hdiv1 hdiv2
        (by have := hab 0; omega)
        (by have := hab 1; have := hξb 2
            have := abs_sub (a 1) (ξ 2); linarith)
        (by have := hab 2; have := hξb 0; have := hξb 1; have := hξb 2
            have t1 := abs_add_le (a 2 - ξ 0 - ξ 1) (ξ 2)
            have t2 := abs_sub (a 2 - ξ 0) (ξ 1)
            have t3 := abs_sub (a 2) (ξ 0)
            linarith) hne
      linarith
    obtain ⟨u0, u1, u2⟩ := hu0
    have ξ0 : ξ 0 = 0 := by simp only [hξ, pat]; rw [hch0 0 u0]; simp
    rw [ξ0] at u2
    have hall : a 1 = 0 ∧ a 2 = 0 := by
      rcases hspec 2 with h | ⟨h, hpos⟩ | ⟨h, hneg⟩
      · have h' : ξ 2 = 0 := h
        have a1 : a 1 = 0 := by linarith
        have ξ1 : ξ 1 = 0 := by simp only [hξ, pat]; rw [hch0 1 a1]; simp
        exact ⟨a1, by linarith⟩
      · exfalso
        have h' : ξ 2 = 1 := h
        rcases hspec 1 with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · have : ξ 1 = 0 := h1; linarith
        · have : ξ 1 = 1 := h1; linarith
        · have : ξ 1 = -1 := h1; linarith
      · exfalso
        have h' : ξ 2 = -1 := h
        rcases hspec 1 with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · have : ξ 1 = 0 := h1; linarith
        · have : ξ 1 = 1 := h1; linarith
        · have : ξ 1 = -1 := h1; linarith
    apply hvw
    refine eq_of_Pf_eq hr hC v w fun c => eq_of_cen_zero _ _ _ (Pf_lt _ v) (Pf_lt _ w) ?_
    fin_cases c
    exacts [u0, hall.1, hall.2]
  obtain ⟨c, hc⟩ := key
  have hb : |a c| * ((p ^ (3 * k + 1 - (k + 1)) : ℕ) : ℤ) - (((p ^ (3 * k + 1 - (k + 1)) : ℕ) : ℤ) - 1) ≤
      (cres (p ^ (3 * k + 1)) ((coord p (3 * k + 1) (C c) v : ℤ) - coord p (3 * k + 1) (C c) w) : ℤ) :=
    prefix_bound (C c) v w (k + 1) (by omega)
  set f := p ^ (3 * k + 1 - (k + 1)) with hf
  set cr := cres (p ^ (3 * k + 1)) ((coord p (3 * k + 1) (C c) v : ℤ) - coord p (3 * k + 1) (C c) w)
  have h4 : 4 ≤ ρ ^ 2 := by nlinarith
  have h1 : (((ρ ^ 2 - 4) * f : ℕ) : ℤ) ≤ cr := by
    push_cast [Nat.cast_sub h4]
    have hf0 : (0 : ℤ) ≤ f := by positivity
    have := mul_le_mul_of_nonneg_right hc hf0
    linarith
  have h1' : (ρ ^ 2 - 4) * f ≤ cr := by exact_mod_cast h1
  calc (ρ ^ 2 - 4) ^ 2 * p ^ (4 * k) = ((ρ ^ 2 - 4) * f) ^ 2 := by
        rw [hf, mul_pow, ← pow_mul]; congr 2; omega
    _ ≤ cr ^ 2 := Nat.pow_le_pow_left h1' 2
    _ ≤ _ := cres_le_torus _ (digPoint p (3 * k + 1) C v) (digPoint p (3 * k + 1) C w) c

end Z3NetKN.Proofs

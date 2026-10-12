/-
Proof module of entry Obs: `prop:P2` (the pair ceiling).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsCeil

@[expose] public section

/-!
# Entry Obs: `prop:P2`

The proof of the paper (`app:proofs`): a cell where the last digits of `n_a`, `n_b` cause no
carry along `e_a + ε e_b`, the first offset digit of `a` wraps, that of `b` does not, the second
offset digit of `b` is `q - 1` (`ε = 1`) or `0` (`ε = -1`) so that it cannot move against `ε`, and
the first offset digits of the still coordinates do not wrap. The boxes have depths `sk - 2k - 3`
on `a` (only the levels `k-1`, `k` are prescribed), `k + 2` on `b` and `k + 1` on one still `u`
(`exists_good`). For the second statement, the first offset digit of `b` wraps too.
-/

namespace Z3NetF.Proofs

open Matrix Finset ObsCount ObsStep ObsCeil

noncomputable section

namespace ObsP2

lemma val_add_one_ne {q : ℕ} [NeZero q] (x : ZMod q) (h : x ≠ -1) :
    ((x + 1).val : ℤ) = x.val + 1 := by
  have h1 := ZMod.val_lt x
  have h2 : x.val ≠ q - 1 := by
    intro h3; apply h
    rw [← ZMod.natCast_zmod_val x, h3]
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    have h4 : ((p + 1 : ℕ) : ZMod (p + 1)) = 0 := ZMod.natCast_self _
    simp only [Nat.add_sub_cancel]
    push_cast at h4
    linear_combination h4
  have := val_add_int x 1
  push_cast at this
  rw [this, Int.emod_eq_of_lt (by positivity) (by omega)]

lemma val_sub_one_ne {q : ℕ} [NeZero q] (x : ZMod q) (h : x ≠ 0) :
    ((x + -1).val : ℤ) = x.val - 1 := by
  have h2 : x.val ≠ 0 := fun h3 => h ((ZMod.val_eq_zero x).mp h3)
  have := val_add_int x (-1)
  push_cast at this
  have h1 := ZMod.val_lt x
  rw [this, Int.emod_eq_of_lt (by omega) (by omega)]
  ring

variable {s q k : ℕ} [NeZero q]

/-- The common core of `prop:P2`. `t = 1` adds the condition on the second offset digit of `b`. -/
theorem p2_core (hs : 3 ≤ s) (hq : 2 ≤ q) (t : ℕ) (ht : t ≤ 1) (h3k : 3 * k + 3 + t ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a b : Fin s) (hab : a ≠ b)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (Wa Wb Rb : Finset (ZMod q)) (hWa : Wa.Nonempty)
    (hWb : Wb.Nonempty) (hRb : Rb.Nonempty)
    (hsum : ∑ c, |Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| < q) :
    ∃ v : Fin (s * k) → ZMod q,
      dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ a) v k ∈ Wa ∧
      dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ b) v k ∈ Wb ∧
      (t = 1 → dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ b) v (k + 1) ∈ Rb) ∧
      ∃ w : Fin (s * k) → ZMod q, v ≠ w ∧
      (∀ c, ((dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) w k).val : ℤ) -
          (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v k).val =
        ((dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v k +
          ((Z3NetF.sig (Z3NetF.Mt Φ) a b ε c : ℤ) : ZMod q)).val : ℤ) -
          (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v k).val) ∧
      (∀ c, ∃ τ : ZMod q, dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) w (k + 1) =
        dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v (k + 1) + τ) ∧
      (Z3NetU.Proofs.cellN s q k w a : ℤ) - Z3NetU.Proofs.cellN s q k v a = 1 ∧
      (Z3NetU.Proofs.cellN s q k w b : ℤ) - Z3NetU.Proofs.cellN s q k v b = ε ∧
      (∀ u, u ≠ a → u ≠ b → Z3NetU.Proofs.cellN s q k w u = Z3NetU.Proofs.cellN s q k v u ∧
        NoWrap (Z3NetF.sig (Z3NetF.Mt Φ) a b ε u)
          (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ u) v k)) := by
  classical
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · exact h
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  set C := Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ with hC
  have hunit := unit_of_net C hnet
  set σ := Z3NetF.sig (Z3NetF.Mt Φ) a b ε with hσ
  set cb : ZMod q := if ε = 1 then -1 else 0 with hcb
  set A : Fin s → ℕ → Finset (ZMod q) := fun c j =>
    if c = a then (if j = k - 1 then univ.filter (· ≠ -1) else if j = k then Wa else univ)
    else if c = b then (if j = k - 1 then univ.filter (· ≠ cb) else if j = k then Wb
      else if j = k + 1 then Rb else univ)
    else univ with hA
  set dB : Fin s → ℕ := fun c =>
    if c = a then s * k - 2 * k - 2 - t else if c = b then k + 1 + t else 0 with hdB
  have hneq : ∀ y : ZMod q, (univ.filter (· ≠ y)).Nonempty := by
    intro y
    by_cases hy : y = 0
    · exact ⟨1, by simp [hy]⟩
    · exact ⟨0, by simp [Ne.symm hy]⟩
  have hU : (univ.filter fun u : Fin s => u ≠ a ∧ u ≠ b).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    have : (univ : Finset (Fin s)) ⊆ {a, b} := by
      intro u _
      by_cases hua : u = a
      · simp [hua]
      · have := h (mem_univ u); simp only [not_and, not_not] at this; simp [this hua]
    have := card_le_card this
    simp only [card_univ, Fintype.card_fin] at this
    have := card_le_two (a := a) (b := b)
    omega
  obtain ⟨v, hvA, hvB⟩ := exists_good C k hunit dB A
    (fun c j _ => by
      simp only [hA]
      split_ifs
      · exact hneq _
      · exact hWa
      · exact univ_nonempty
      · exact hneq _
      · exact hWb
      · exact hRb
      · exact univ_nonempty
      · exact univ_nonempty)
    (univ.filter fun u => u ≠ a ∧ u ≠ b) hU
    (fun u hu => by
      simp only [mem_filter, mem_univ, true_and] at hu
      simp [hdB, hu.1, hu.2])
    (by
      have e1 : ∀ c, dB c = (if c = a then s * k - 2 * k - 2 - t else 0) +
          (if c = b then k + 1 + t else 0) := by
        intro c
        by_cases hca : c = a
        · subst hca; simp [hdB, hab]
        · simp [hdB, hca]
      simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, if_true]
      omega)
    (fun u => univ.filter fun x => ¬ NoWrap (σ u) x)
    (by
      calc ∑ u ∈ univ.filter (fun u => u ≠ a ∧ u ≠ b),
            (univ.filter fun x => ¬ NoWrap (σ u) x).card
          ≤ ∑ u ∈ univ.filter (fun u => u ≠ a ∧ u ≠ b), (σ u).natAbs :=
            Finset.sum_le_sum fun u _ => card_wrap_le _
        _ ≤ ∑ u, (σ u).natAbs := Finset.sum_le_sum_of_subset (filter_subset _ _)
        _ < q := by
          have : ((∑ u, (σ u).natAbs : ℕ) : ℤ) = ∑ u, |σ u| := by
            rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun u _ => Int.natCast_natAbs _
          omega)
  have hdBa : dB a = s * k - 2 * k - 2 - t := by simp [hdB]
  have hdBb : dB b = k + 1 + t := by simp [hdB, Ne.symm hab]
  have hva : ∀ j < s * k - 2 * k - 2 - t, dig (C a) v j ∈
      (if j = k - 1 then univ.filter (· ≠ -1) else if j = k then Wa else univ) := by
    intro j hj
    have := hvA a j (by rw [hdBa]; exact hj)
    simpa [hA] using this
  have hvb : ∀ j < k + 1 + t, dig (C b) v j ∈
      (if j = k - 1 then univ.filter (· ≠ cb) else if j = k then Wb
        else if j = k + 1 then Rb else univ) := by
    intro j hj
    have := hvA b j (by rw [hdBb]; exact hj)
    simpa [hA, Ne.symm hab] using this
  have hka : k < s * k - 2 * k - 2 - t := by
    have : 3 * k + 3 + t ≤ s * k := h3k
    omega
  -- the step
  set e : Fin s → ZMod q := Pi.single a 1 + Pi.single b (ε : ZMod q) with he
  set w := v + stepVec hk0 e with hw
  have hsum_e : ∀ c (r : ℕ), ∑ d : Fin s, e d * Z3NetF.ent (Φ c d) r (k - 1) =
      Z3NetF.ent (Φ c a) r (k - 1) + (ε : ZMod q) * Z3NetF.ent (Φ c b) r (k - 1) := by
    intro c r
    simp only [he, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single a]
      · simp
      · intro d _ hd; simp [hd]
      · simp
    · rw [Finset.sum_eq_single b]
      · simp
      · intro d _ hd; simp [hd]
      · simp
  have hstepk : ∀ c, dig (C c) w k = dig (C c) v k + ((σ c : ℤ) : ZMod q) := by
    intro c
    have h0 := dig_step_off Φ hk0 e c 0 (by omega)
    simp only [add_zero] at h0
    rw [hw, dig_add, h0, hsum_e]
    congr 1
    simp [hσ, Z3NetF.sig, Z3NetF.Mt, ZMod.coe_valMinAbs]
  have hea : e a = 1 := by simp [he, hab]
  have heb : e b = (ε : ZMod q) := by simp [he, Ne.symm hab]
  have heu : ∀ u, u ≠ a → u ≠ b → e u = 0 := by intro u h1 h2; simp [he, h1, h2]
  have hla : dig (C a) v (k - 1) ≠ -1 := by
    have := hva (k - 1) (by omega)
    rw [if_pos rfl] at this
    simpa using this
  have hlb : dig (C b) v (k - 1) ≠ cb := by
    have := hvb (k - 1) (by omega)
    rw [if_pos rfl] at this
    simpa using this
  refine ⟨v, ?_, ?_, ?_, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hva k hka
    rwa [if_neg (by omega), if_pos rfl] at this
  · have := hvb k (by omega)
    rwa [if_neg (by omega), if_pos rfl] at this
  · intro ht1
    have := hvb (k + 1) (by omega)
    rwa [if_neg (by omega), if_neg (by omega), if_pos rfl] at this
  · intro h
    have h1 := congrFun h (Z3NetU.Proofs.ix k a ⟨k - 1, by omega⟩)
    rw [hw, Pi.add_apply, stepVec_apply, if_pos rfl, hea] at h1
    exact one_ne_zero (by linear_combination -h1)
  · intro c
    rw [hstepk]
  · intro c
    refine ⟨∑ d : Fin s, e d * Z3NetF.ent (Φ c d) 1 (k - 1), ?_⟩
    rw [hw, dig_add, dig_step_off Φ hk0 e c 1 (by omega)]
  · have hcl := cellN_step hk0 v e a
    have hla' : v (Z3NetU.Proofs.ix k a ⟨k - 1, by omega⟩) ≠ -1 := by
      have := dig_cell Φ a v (k - 1) (by omega)
      rw [← this]; exact hla
    rw [hea] at hcl
    rw [hcl, val_add_one_ne _ hla']
    ring
  · have hcl := cellN_step hk0 v e b
    rw [heb] at hcl
    rw [hcl]
    have hlb' : v (Z3NetU.Proofs.ix k b ⟨k - 1, by omega⟩) ≠ cb := by
      have := dig_cell Φ b v (k - 1) (by omega)
      rw [← this]; exact hlb
    rcases hε with rfl | rfl
    · simp only [hcb, if_pos rfl] at hlb'
      push_cast
      rw [val_add_one_ne _ hlb']; ring
    · simp only [hcb, if_neg (show (-1 : ℤ) ≠ 1 by norm_num)] at hlb'
      push_cast
      rw [val_sub_one_ne _ hlb']; ring
  · intro u hua hub
    constructor
    · have hcl := cellN_step hk0 v e u
      rw [heu u hua hub, add_zero, sub_self] at hcl
      have := sub_eq_zero.mp hcl
      exact_mod_cast this
    · have := hvB u (by simp [hua, hub])
      simpa using this

/-- The coordinate difference in terms of cell, first offset digit and tail. -/
lemma dX (hsk : k + 1 ≤ s * k) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (v w : Fin (s * k) → ZMod q) (c : Fin s) :
    (Z3NetF.gfPoint q k Φ w c : ℤ) - Z3NetF.gfPoint q k Φ v c =
      (q : ℤ) ^ (s * k - k) * ((Z3NetU.Proofs.cellN s q k w c : ℤ) - Z3NetU.Proofs.cellN s q k v c) +
      (q : ℤ) ^ (s * k - k - 1) *
        (((dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) w k).val : ℤ) -
          (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v k).val) +
      ((tl Φ w c : ℤ) - tl Φ v c) := by
  rw [X_eq Φ hsk w c, X_eq Φ hsk v c]; ring

lemma tl_split (hsk : k + 2 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (v : Fin (s * k) → ZMod q) (c : Fin s) :
    ∃ r : ℕ, r < q ^ (s * k - k - 2) ∧ tl Φ v c =
      (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v (k + 1)).val *
        q ^ (s * k - k - 2) + r := by
  refine ⟨TS q (fun j => (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v j).val)
    (k + 2) (s * k), ?_, ?_⟩
  · exact TS_lt (Nat.pos_of_neZero q) _ (fun j => ZMod.val_lt _) _ _ _ (by omega)
  · unfold tl
    rw [TS_succ q _ (show k + 1 < s * k by omega), show s * k - 1 - (k + 1) = s * k - k - 2 by omega]

lemma tl_diff (hsk : k + 1 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (v w : Fin (s * k) → ZMod q) (c : Fin s) :
    |(tl Φ w c : ℝ) - tl Φ v c| < (q : ℝ) ^ (s * k - k - 1) := by
  have h1 := tl_lt Φ hsk v c
  have h2 := tl_lt Φ hsk w c
  have h1' : (tl Φ v c : ℝ) < (q : ℝ) ^ (s * k - k - 1) := by exact_mod_cast h1
  have h2' : (tl Φ w c : ℝ) < (q : ℝ) ^ (s * k - k - 1) := by exact_mod_cast h2
  have : (0 : ℝ) ≤ tl Φ v c := by positivity
  have : (0 : ℝ) ≤ tl Φ w c := by positivity
  rw [abs_lt]; constructor <;> linarith

lemma b_bound (q P σ ε D dd r : ℤ) (hq : 2 ≤ q) (hP : 0 < P) (hε : ε = 1 ∨ ε = -1)
    (hσ : |σ| ≤ q - 1) (hD : ε * D = P * q * q - P * q * |σ| + dd * P + r)
    (hdd1 : -(q - 1) ≤ dd) (hdd2 : dd ≤ 0) (hr : |r| < P) :
    0 < ε * D ∧ ε * D < P * q * q - P * q * |σ| + P := by
  have h1 : dd * P ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hdd2 hP.le
  have h2 : -(q - 1) * P ≤ dd * P := mul_le_mul_of_nonneg_right hdd1 hP.le
  have h3 : 0 ≤ P * q * (q - |σ| - 1) := mul_nonneg (mul_nonneg hP.le (by linarith)) (by linarith)
  have h4 := (abs_lt.mp hr).1
  have h5 := (abs_lt.mp hr).2
  constructor
  · nlinarith
  · linarith

theorem P2_ceiling (hs : 4 ≤ s) (h3k : 3 * k + 4 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a b : Fin s) (hab : a ≠ b) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (ha : 0 < Z3NetF.sig (Z3NetF.Mt Φ) a b ε a)
    (hb : ε * Z3NetF.sig (Z3NetF.Mt Φ) a b ε b < 0)
    (hsum : ∑ c, |Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| < q) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      ((1 - ((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε b| : ℤ) : ℝ) / q + 1 / (q : ℝ) ^ 2) ^ 2 +
        ((((Z3NetF.sig (Z3NetF.Mt Φ) a b ε a + 1 : ℤ)) : ℝ) ^ 2 +
          ∑ u ∈ (univ.erase a).erase b, (((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε u| : ℤ) : ℝ) + 1) ^ 2) /
          (q : ℝ) ^ 2) := by
  classical
  set σ := Z3NetF.sig (Z3NetF.Mt Φ) a b ε with hσ
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · exact h
  have hsle : ∀ c, |σ c| ≤ ∑ c, |σ c| := fun c =>
    Finset.single_le_sum (f := fun c => |σ c|) (fun _ _ => abs_nonneg _) (mem_univ c)
  have hσa := hsle a
  have hσb := hsle b
  have ha1 := le_abs_self (σ a); have ha2 := neg_abs_le (σ a)
  have hb1 := le_abs_self (σ b); have hb2 := neg_abs_le (σ b)
  have hq2 : 2 ≤ q := by
    have : (0 : ℤ) < |σ a| := abs_pos.mpr (by omega)
    have : (2 : ℤ) ≤ q := by omega
    exact_mod_cast this
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  have hbne : σ b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  set cb' : ZMod q := if ε = 1 then -1 else 0 with hcb'
  obtain ⟨v, hWa, hWb, hRb, w, hvw, hdig, hτ, hca, hcb, hu⟩ := p2_core (by omega) hq2 1 le_rfl
    (by omega) Φ hnet a b hab ε hε
    (univ.filter fun x : ZMod q => (q : ℤ) ≤ x.val + σ a)
    (univ.filter fun x : ZMod q => NoWrap (σ b) x) {cb'}
    ⟨-1, by simp only [mem_filter, mem_univ, true_and]; rw [val_m1]; push_cast; omega⟩
    (by
      rcases le_or_gt 0 (σ b) with h0 | h0
      · refine ⟨0, ?_⟩
        simp only [mem_filter, mem_univ, true_and]
        rw [noWrap_iff, ZMod.val_zero]; push_cast; omega
      · refine ⟨-1, ?_⟩
        simp only [mem_filter, mem_univ, true_and]
        rw [noWrap_iff, val_m1]; push_cast; omega)
    (singleton_nonempty _) hsum
  simp only [mem_filter, mem_univ, true_and] at hWa hWb
  have hRb' := hRb rfl
  rw [mem_singleton] at hRb'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set g : ℝ := (q : ℝ) ^ (s * k - k - 1) with hg
  have hgpos : 0 < g := by positivity
  have hG : (q : ℝ) ^ (s * k - k) = g * q := by
    rw [hg, ← pow_succ]; congr 1; omega
  have hG2 : (q : ℝ) ^ (s * k - k) = (q : ℝ) ^ (s * k - k - 2) * (q : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  set C := Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ with hCdef
  set b' : Fin s → ℝ := fun c => if c = a then (((σ a + 1 : ℤ)) : ℝ) / q
    else if c = b then 1 - ((|σ b| : ℤ) : ℝ) / q + 1 / (q : ℝ) ^ 2
    else (((|σ c| : ℤ) : ℝ) + 1) / q with hb'
  have key := ObsCount.pair_of_bounds (X := Z3NetF.gfPoint q k Φ) (k := k) (by omega)
    (by omega) v w hvw b' (fun c => by
      have hd := dX (by omega) Φ v w c
      have htl := tl_diff (by omega) Φ v w c
      by_cases hc : c = a
      · subst hc
        simp only [hb', if_pos rfl]
        have ho : ((dig (C c) w k).val : ℤ) - (dig (C c) v k).val = σ c - q := by
          have := ZMod.val_lt (dig (C c) v k)
          rw [hdig c, val_wrap_up _ _ hWa (by omega)]; ring
        have hX : ((Z3NetF.gfPoint q k Φ w c : ℕ) : ℝ) - Z3NetF.gfPoint q k Φ v c =
            g * (σ c : ℝ) + ((((tl Φ w c : ℤ) - tl Φ v c : ℤ)) : ℝ) := by
          have := congrArg (fun z : ℤ => (z : ℝ)) hd
          simp only at this
          rw [hca, ho] at this
          push_cast at this ⊢
          rw [this, hG]; ring
        rw [hG]
        have := trans_bound (q := q) (by omega) hgpos (σ c) ((tl Φ w c : ℤ) - tl Φ v c) _ hX
          (by push_cast; exact htl)
        rw [abs_of_pos ha] at this
        push_cast at this ⊢; exact this
      · by_cases hcb2 : c = b
        · subst hcb2
          simp only [hb', if_neg hc, ite_true]
          have ho : ((dig (C c) w k).val : ℤ) - (dig (C c) v k).val = σ c := by
            rw [hdig c]; unfold NoWrap at hWb; rw [hWb]; ring
          obtain ⟨τ, hτc⟩ := hτ c
          obtain ⟨rv, hrv, htv⟩ := tl_split (by omega) Φ v c
          obtain ⟨rw', hrw, htw⟩ := tl_split (by omega) Φ w c
          have hRb2 : dig (C c) v (k + 1) = cb' := hRb'
          -- `ε (d'_w - d'_v) ≤ 0` for the second offset digit
          have hmono : ε * (((dig (C c) w (k + 1)).val : ℤ) - (dig (C c) v (k + 1)).val) ≤ 0 := by
            rw [hRb2]
            have hl := ZMod.val_lt (dig (C c) w (k + 1))
            rcases hε with rfl | rfl
            · rw [hcb', if_pos rfl, val_m1, Nat.cast_sub (by omega), Nat.cast_one]
              have : ((dig (C c) w (k + 1)).val : ℤ) < q := by exact_mod_cast hl
              linarith
            · rw [hcb', if_neg (show (-1 : ℤ) ≠ 1 by norm_num), ZMod.val_zero]
              push_cast
              have : (0 : ℤ) ≤ ((dig (C c) w (k + 1)).val : ℤ) := by positivity
              linarith
          have hX : ε * (((Z3NetF.gfPoint q k Φ w c : ℕ) : ℤ) - Z3NetF.gfPoint q k Φ v c) =
              (q : ℤ) ^ (s * k - k) + (q : ℤ) ^ (s * k - k - 1) * (ε * σ c) +
                ε * (((dig (C c) w (k + 1)).val : ℤ) - (dig (C c) v (k + 1)).val) *
                  (q : ℤ) ^ (s * k - k - 2) + ε * ((rw' : ℤ) - rv) := by
            rw [hd, hcb, ho, htv, htw]
            push_cast
            have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
            linear_combination ((q : ℤ) ^ (s * k - k)) * hε2
          have hεσ : ε * σ c = -|σ c| := by
            have h1 : |ε * σ c| = |σ c| := by
              rw [abs_mul]; rcases hε with rfl | rfl <;> simp
            have h2 := abs_of_neg hb
            linarith
          set D : ℤ := ((Z3NetF.gfPoint q k Φ w c : ℕ) : ℤ) - Z3NetF.gfPoint q k Φ v c with hD
          set P : ℤ := (q : ℤ) ^ (s * k - k - 2) with hP
          have hPpos : 0 < P := by positivity
          have hgP : (q : ℤ) ^ (s * k - k - 1) = P * q := by
            rw [hP, ← pow_succ]; congr 1; omega
          have hGP : (q : ℤ) ^ (s * k - k) = P * q * q := by
            rw [hP, ← pow_succ, ← pow_succ]; congr 1; omega
          have hrv' : (rv : ℤ) < P := by rw [hP]; exact_mod_cast hrv
          have hrw' : (rw' : ℤ) < P := by rw [hP]; exact_mod_cast hrw
          have hrv0 : (0 : ℤ) ≤ rv := by positivity
          have hrw0 : (0 : ℤ) ≤ rw' := by positivity
          have hdlo : -((q : ℤ) - 1) ≤ ε * (((dig (C c) w (k + 1)).val : ℤ) -
              (dig (C c) v (k + 1)).val) := by
            have h1 := ZMod.val_lt (dig (C c) w (k + 1))
            have h2 := ZMod.val_lt (dig (C c) v (k + 1))
            have h1' : ((dig (C c) w (k + 1)).val : ℤ) < q := by exact_mod_cast h1
            have h2' : ((dig (C c) v (k + 1)).val : ℤ) < q := by exact_mod_cast h2
            have : (0 : ℤ) ≤ ((dig (C c) w (k + 1)).val : ℤ) := by positivity
            have : (0 : ℤ) ≤ ((dig (C c) v (k + 1)).val : ℤ) := by positivity
            rcases hε with rfl | rfl <;> linarith
          have hεr : |ε * ((rw' : ℤ) - rv)| < P := by
            rw [abs_mul, show |ε| = 1 by rcases hε with rfl | rfl <;> simp, one_mul, abs_lt]
            constructor <;> linarith
          have hσq : |σ c| ≤ q - 1 := by omega
          obtain ⟨hlo, hup⟩ := b_bound (q : ℤ) P (σ c) ε D
            (ε * (((dig (C c) w (k + 1)).val : ℤ) - (dig (C c) v (k + 1)).val))
            (ε * ((rw' : ℤ) - rv)) (by exact_mod_cast hq2) hPpos hε hσq
            (by rw [hX, hεσ, hGP, hgP]; ring) hdlo hmono hεr
          have hDabs : |D| = ε * D := by
            rw [← abs_of_pos hlo, abs_mul, show |ε| = 1 by rcases hε with rfl | rfl <;> simp,
              one_mul]
          have hreal : |(D : ℝ)| < (1 - ((|σ c| : ℤ) : ℝ) / q + 1 / (q : ℝ) ^ 2) *
              (q : ℝ) ^ (s * k - k) := by
            have h1 : ((|D| : ℤ) : ℝ) < ((P * q * q - P * q * |σ c| + P : ℤ) : ℝ) := by
              rw [hDabs]; exact_mod_cast hup
            rw [Int.cast_abs] at h1
            refine lt_of_lt_of_eq h1 ?_
            have hPr : ((P : ℤ) : ℝ) = (q : ℝ) ^ (s * k - k - 2) := by rw [hP]; push_cast; rfl
            rw [hG2]
            push_cast
            rw [hPr]
            field_simp
          rw [hD] at hreal
          push_cast at hreal ⊢
          exact hreal
        · simp only [hb', if_neg hc, if_neg hcb2]
          obtain ⟨hcell, hnw⟩ := hu c hc hcb2
          have ho : ((dig (C c) w k).val : ℤ) - (dig (C c) v k).val = σ c := by
            rw [hdig c]; unfold NoWrap at hnw; rw [hnw]; ring
          have hX : ((Z3NetF.gfPoint q k Φ w c : ℕ) : ℝ) - Z3NetF.gfPoint q k Φ v c =
              g * (σ c : ℝ) + ((((tl Φ w c : ℤ) - tl Φ v c : ℤ)) : ℝ) := by
            have := congrArg (fun z : ℤ => (z : ℝ)) hd
            simp only at this
            rw [hcell, sub_self, mul_zero, zero_add, ho] at this
            push_cast at this ⊢
            rw [this]
          rw [hG]
          exact trans_bound (q := q) (by omega) hgpos (σ c) ((tl Φ w c : ℤ) - tl Φ v c) _ hX
            (by push_cast; exact htl))
  convert key using 1
  rw [← Finset.add_sum_erase _ _ (mem_univ a),
    ← Finset.add_sum_erase _ _ (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩)]
  simp only [hb', if_pos rfl, if_neg (Ne.symm hab)]
  rw [add_div, Finset.sum_div, div_pow]
  have hs : ∑ u ∈ (univ.erase a).erase b, (((|σ u| : ℤ) : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 =
      ∑ u ∈ (univ.erase a).erase b, (if u = a then (((σ a + 1 : ℤ)) : ℝ) / q
        else if u = b then 1 - ((|σ b| : ℤ) : ℝ) / q + 1 / (q : ℝ) ^ 2
        else (((|σ u| : ℤ) : ℝ) + 1) / q) ^ 2 := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have h1 := (mem_erase.mp hu).1
    have h2 := (mem_erase.mp (mem_erase.mp hu).2).1
    rw [if_neg h2, if_neg h1, div_pow]
  rw [hs]
  simp only [ite_true]
  ring

theorem P2_forward (hs : 4 ≤ s) (h3k : 3 * k + 3 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a b : Fin s) (hab : a ≠ b) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (ha : 0 < Z3NetF.sig (Z3NetF.Mt Φ) a b ε a)
    (hb : 0 < ε * Z3NetF.sig (Z3NetF.Mt Φ) a b ε b)
    (hsum : ∑ c, |Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| < q) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      (∑ c, (((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| : ℤ) : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) := by
  classical
  set σ := Z3NetF.sig (Z3NetF.Mt Φ) a b ε with hσ
  have hsle : ∀ c, |σ c| ≤ ∑ c, |σ c| := fun c =>
    Finset.single_le_sum (f := fun c => |σ c|) (fun _ _ => abs_nonneg _) (mem_univ c)
  have hσa := hsle a
  have hσb := hsle b
  have ha1 := le_abs_self (σ a); have ha2 := neg_abs_le (σ a)
  have hb1 := le_abs_self (σ b); have hb2 := neg_abs_le (σ b)
  have hq2 : 2 ≤ q := by
    have : (0 : ℤ) < |σ a| := abs_pos.mpr (by omega)
    have : (2 : ℤ) ≤ q := by omega
    exact_mod_cast this
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  set Wb : Finset (ZMod q) := if ε = 1 then univ.filter fun x : ZMod q => (q : ℤ) ≤ x.val + σ b
    else univ.filter fun x : ZMod q => (x.val : ℤ) + σ b < 0 with hWbdef
  obtain ⟨v, hWa, hWb, -, w, hvw, hdig, -, hca, hcb, hu⟩ := p2_core (by omega) hq2 0 (by omega)
    (by omega) Φ hnet a b hab ε hε
    (univ.filter fun x : ZMod q => (q : ℤ) ≤ x.val + σ a) Wb univ
    ⟨-1, by simp only [mem_filter, mem_univ, true_and]; rw [val_m1]; push_cast; omega⟩
    (by
      rcases hε with rfl | rfl
      · refine ⟨-1, ?_⟩
        rw [hWbdef, if_pos rfl]
        simp only [mem_filter, mem_univ, true_and]
        rw [val_m1]; push_cast; simp at hb; omega
      · refine ⟨0, ?_⟩
        simp only [hWbdef, if_neg (show (-1 : ℤ) ≠ 1 by norm_num), mem_filter, mem_univ,
          true_and]
        rw [ZMod.val_zero]; push_cast; simp at hb; omega)
    univ_nonempty hsum
  simp only [mem_filter, mem_univ, true_and] at hWa
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set g : ℝ := (q : ℝ) ^ (s * k - k - 1) with hg
  have hgpos : 0 < g := by positivity
  have hG : (q : ℝ) ^ (s * k - k) = g * q := by
    rw [hg, ← pow_succ]; congr 1; omega
  set C := Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ with hCdef
  set b' : Fin s → ℝ := fun c => (((|σ c| : ℤ) : ℝ) + 1) / q with hb'
  have key := ObsCount.pair_of_bounds (X := Z3NetF.gfPoint q k Φ) (k := k) (by omega)
    (by omega) v w hvw b' (fun c => by
      have hd := dX (by omega) Φ v w c
      have htl := tl_diff (by omega) Φ v w c
      simp only [hb']
      rw [hG]
      -- the three kinds of coordinates: `X_c(w) - X_c(v) = g σ_c + Δ`
      have hform : ((Z3NetF.gfPoint q k Φ w c : ℕ) : ℝ) - Z3NetF.gfPoint q k Φ v c =
          g * (σ c : ℝ) + ((((tl Φ w c : ℤ) - tl Φ v c : ℤ)) : ℝ) := by
        have hint : (Z3NetF.gfPoint q k Φ w c : ℤ) - Z3NetF.gfPoint q k Φ v c =
            (q : ℤ) ^ (s * k - k - 1) * σ c + ((tl Φ w c : ℤ) - tl Φ v c) := by
          rw [hd]
          have hGq : (q : ℤ) ^ (s * k - k) = (q : ℤ) ^ (s * k - k - 1) * q := by
            rw [← pow_succ]; congr 1; omega
          by_cases hc : c = a
          · subst hc
            have := ZMod.val_lt (dig (C c) v k)
            rw [hca, hdig c, val_wrap_up _ _ hWa (by omega), hGq]; ring
          · by_cases hcb2 : c = b
            · subst hcb2
              have := ZMod.val_lt (dig (C c) v k)
              rw [hcb, hdig c, hGq]
              rcases hε with rfl | rfl
              · rw [hWbdef, if_pos rfl] at hWb
                simp only [mem_filter, mem_univ, true_and] at hWb
                simp at hb
                rw [val_wrap_up _ _ hWb (by omega)]; ring
              · simp only [hWbdef, if_neg (show (-1 : ℤ) ≠ 1 by norm_num), mem_filter, mem_univ,
                  true_and] at hWb
                simp at hb
                rw [val_wrap_down _ _ (by omega) hWb]; ring
            · obtain ⟨hcell, hnw⟩ := hu c hc hcb2
              unfold NoWrap at hnw
              rw [hcell, hdig c, hnw]; ring
        have := congrArg (fun z : ℤ => (z : ℝ)) hint
        push_cast at this ⊢
        rw [this]
      exact trans_bound (q := q) (by omega) hgpos (σ c) ((tl Φ w c : ℤ) - tl Φ v c) _ hform
        (by push_cast; exact htl))
  convert key using 1
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hb', div_pow]

theorem P2_forward_C {C : ℕ} (hs : 4 ≤ s) (h3k : 3 * k + 3 ≤ s * k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a b : Fin s) (hab : a ≠ b) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (ha : 0 < Z3NetF.sig (Z3NetF.Mt Φ) a b ε a)
    (hb : 0 < ε * Z3NetF.sig (Z3NetF.Mt Φ) a b ε b)
    (hsum : ∑ c, |Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| < q) (hC : ∀ c d, |Z3NetF.Mt Φ c d| ≤ C) :
    Z3NetF.PairBelow q (s * k) k (Z3NetF.gfPoint q k Φ)
      (s * (2 * (C : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) := by
  refine PairBelow_mono ?_ (P2_forward hs h3k Φ hnet a b hab ε hε ha hb hsum)
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hb' : ∀ c, (((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| : ℤ) : ℝ) + 1) ^ 2 ≤
      (2 * (C : ℝ) + 1) ^ 2 := by
    intro c
    have h1 : |Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| ≤ 2 * C := by
      unfold Z3NetF.sig
      calc |Z3NetF.Mt Φ c a + ε * Z3NetF.Mt Φ c b| ≤ |Z3NetF.Mt Φ c a| + |ε * Z3NetF.Mt Φ c b| :=
            abs_add_le _ _
        _ = |Z3NetF.Mt Φ c a| + |Z3NetF.Mt Φ c b| := by
            rw [abs_mul, show |ε| = 1 by rcases hε with rfl | rfl <;> simp, one_mul]
        _ ≤ 2 * C := by have := hC c a; have := hC c b; omega
    have : ((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| : ℤ) : ℝ) ≤ 2 * C := by exact_mod_cast h1
    have : (0 : ℝ) ≤ ((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| : ℤ) : ℝ) := by positivity
    nlinarith
  calc ∑ c, (((|Z3NetF.sig (Z3NetF.Mt Φ) a b ε c| : ℤ) : ℝ) + 1) ^ 2
      ≤ ∑ _c : Fin s, (2 * (C : ℝ) + 1) ^ 2 := Finset.sum_le_sum fun c _ => hb' c
    _ = s * (2 * (C : ℝ) + 1) ^ 2 := by simp

end ObsP2


end

end Z3NetF.Proofs

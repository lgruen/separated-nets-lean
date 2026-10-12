module
public import Mathlib
public import Z3Net.HLGFDom

@[expose] public section

/-!
# Entry HL, stage 1, part 3: Prop H_k(3), the upper bound (arbitrary graph form over `𝔽_q`)

Witnesses: indices `xOf w` supported on the last cell digits (level `k-1`) of the `s` axes, with
values `w : Fin s → 𝔽_q`. Then the cell of axis `d` is `val(w_d)` and the first offset digit of
coordinate `c` is `val(∑_d f_cd w_d)` with `2 f_cd = 2F_0[c][d]` (`RowDesign`).

* step `E = e_a` (`a = 0`, free digit on `g = 1`): choose `w_g` so that `r_a = q - 1`; then
  `r_a` wraps and every coordinate moves by at most `½ + (C+1)/q` cells;
* step `E = e_a - e_b` (`a = 0`, `b = 1`, free digit on `g = 2`): a counting argument over the
  `q` values of `w_g` (every `f_cg` is a unit, `∑_c |β_c| ≤ 2sC < q`) gives a choice without
  wraps, so `|D_c - E_c| ≤ (2C + 1)/q` cells.
-/

namespace Z3NetHL.Proofs

open Finset Matrix

noncomputable section

open Z3NetU.Proofs (ix ix_surj sk_sub_add graphGen_cell graphGen_off)

/-! ## Arithmetic of half-integral residues -/

lemma two_val_eq (q : ℕ) [NeZero q] (hqodd : Odd q) (f : ZMod q) (F : ℤ) (hF : Odd F)
    (hFq : |F| < q) (h2 : 2 * f = (F : ZMod q)) : 2 * (f.val : ℤ) = F + q := by
  have hv := ZMod.val_lt f
  have hdvd : (q : ℤ) ∣ 2 * (f.val : ℤ) - F := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, h2, sub_self]
  obtain ⟨m, hm⟩ := hdvd
  have hmodd : Odd m := by
    by_contra h
    rw [Int.not_odd_iff_even] at h
    obtain ⟨r, hr⟩ := h
    obtain ⟨w, hw⟩ := hF
    have : 2 * (f.val : ℤ) - F = 2 * (q * r) := by rw [hm, hr]; ring
    omega
  rw [abs_lt] at hFq
  have hq0 : (0 : ℤ) < q := by have := NeZero.pos q; exact_mod_cast this
  have hv' : (f.val : ℤ) < q := by exact_mod_cast hv
  have h1 : -1 < m := by
    by_contra h; push_neg at h; nlinarith
  have h2 : m < 3 := by
    by_contra h; push_neg at h; nlinarith
  obtain ⟨t, ht⟩ := hmodd
  have : m = 1 := by omega
  subst this; linarith

lemma val_add_cases (q : ℕ) [NeZero q] (a b : ZMod q) :
    ((a + b).val : ℤ) = a.val + b.val ∨ ((a + b).val : ℤ) = a.val + b.val - q := by
  rw [ZMod.val_add]
  have ha := ZMod.val_lt a; have hb := ZMod.val_lt b
  rcases Nat.lt_or_ge (a.val + b.val) q with h | h
  · left; rw [Nat.mod_eq_of_lt h]; push_cast; ring
  · right
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    push_cast [h]; ring

lemma val_add_int (q : ℕ) [NeZero q] (r : ZMod q) (β : ℤ) (h0 : 0 ≤ (r.val : ℤ) + β)
    (h1 : (r.val : ℤ) + β < q) : ((r + (β : ZMod q)).val : ℤ) = r.val + β := by
  set m : ℕ := ((r.val : ℤ) + β).toNat with hm
  have hmz : (m : ℤ) = r.val + β := Int.toNat_of_nonneg h0
  have hc : ((m : ℕ) : ZMod q) = r + (β : ZMod q) := by
    have : ((m : ℤ) : ZMod q) = (((r.val : ℤ) + β : ℤ) : ZMod q) := by rw [hmz]
    push_cast at this
    rw [this, ZMod.natCast_zmod_val]
  rw [← hc, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), hmz]

lemma two_abs_le (z B : ℤ) (h1 : -B ≤ 2 * z) (h2 : 2 * z ≤ B) : 2 * |z| ≤ B := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-! ## Counting: a common good value of the free digit -/

lemma card_bad_res (q : ℕ) [NeZero q] (β : ℤ) :
    (univ.filter (fun r : ZMod q => ¬ (0 ≤ (r.val : ℤ) + β ∧ (r.val : ℤ) + β < q))).card ≤ β.natAbs := by
  have hinj : Set.InjOn (fun r : ZMod q => r.val)
      (univ.filter (fun r : ZMod q => ¬ (0 ≤ (r.val : ℤ) + β ∧ (r.val : ℤ) + β < q)) : Set (ZMod q)) :=
    fun a _ b _ h => ZMod.val_injective q h
  rw [← Finset.card_image_of_injOn hinj]
  calc _ ≤ (Ico (q - β.toNat) q ∪ range (-β).toNat).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [mem_image, mem_filter, mem_univ, true_and] at hn
        obtain ⟨r, hr, rfl⟩ := hn
        have hv := ZMod.val_lt r
        simp only [mem_union, mem_Ico, mem_range]
        rw [not_and_or] at hr
        rcases hr with h | h
        · right; push_neg at h; omega
        · left; push_neg at h; omega
    _ ≤ (Ico (q - β.toNat) q).card + (range (-β).toNat).card := Finset.card_union_le _ _
    _ ≤ β.natAbs := by simp; omega

lemma exists_good (q : ℕ) [Fact q.Prime] {s : ℕ} (A B : Fin s → ZMod q) (β : Fin s → ℤ)
    (hA : ∀ c, A c ≠ 0) (hsum : ∑ c, (β c).natAbs < q) :
    ∃ t : ZMod q, ∀ c, 0 ≤ ((A c * t + B c).val : ℤ) + β c ∧ ((A c * t + B c).val : ℤ) + β c < q := by
  by_contra hno
  push_neg at hno
  set bad : Fin s → Finset (ZMod q) := fun c =>
    univ.filter (fun t => ¬ (0 ≤ ((A c * t + B c).val : ℤ) + β c ∧ ((A c * t + B c).val : ℤ) + β c < q))
  have hcov : (univ : Finset (ZMod q)) ⊆ univ.biUnion bad := by
    intro t _
    obtain ⟨c, hc⟩ := hno t
    simp only [mem_biUnion, mem_univ, true_and, bad, mem_filter]
    exact ⟨c, by
      intro h; exact absurd h.2 (not_lt.mpr (hc h.1))⟩
  have hcard : ∀ c, (bad c).card ≤ (β c).natAbs := by
    intro c
    have hinj : Set.InjOn (fun t => A c * t + B c) (bad c : Set (ZMod q)) := by
      intro a _ b _ h
      simp only at h
      exact mul_left_cancel₀ (hA c) (add_right_cancel h)
    rw [← Finset.card_image_of_injOn hinj]
    refine le_trans (Finset.card_le_card ?_) (card_bad_res q (β c))
    intro r hr
    simp only [mem_image, bad, mem_filter, mem_univ, true_and] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    simp only [mem_filter, mem_univ, true_and]
    exact ht
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_biUnion_le (s := univ) (t := bad)
  rw [Finset.card_univ, ZMod.card] at h1
  have h3 : ∑ c, (bad c).card ≤ ∑ c, (β c).natAbs := Finset.sum_le_sum fun c _ => hcard c
  omega

/-! ## The witness indices -/

section wit

variable (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))

/-- The index supported on the last cell digits: digit `ix k d (k-1)` is `w_d`, all others `0`. -/
def xOf (w : Fin s → ZMod q) : Fin (s * k) → ZMod q := fun j =>
  if (j : ℕ) % k = k - 1 then
    w ⟨(j : ℕ) / k, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm s k))⟩
  else 0

lemma xOf_ix (w : Fin s → ZMod q) (d : Fin s) (l : Fin k) :
    xOf s q k w (ix k d l) = if (l : ℕ) = k - 1 then w d else 0 := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact l.elim0)
  have h1 : ((d : ℕ) * k + l) % k = l := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt l.isLt]
  have h2 : ((d : ℕ) * k + l) / k = d := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk0, Nat.div_eq_of_lt l.isLt, zero_add]
  simp only [xOf, ix, h1]
  split_ifs <;> first | rfl | (congr 1; exact Fin.ext h2)

variable [NeZero q]

lemma cellN_xOf (hk : 1 ≤ k) (w : Fin s → ZMod q) (d : Fin s) :
    cellN s q k (xOf s q k w) d = (w d).val := by
  unfold cellN
  rw [Finset.sum_eq_single (k - 1)]
  · simp only [ad, dif_pos (show k - 1 < k by omega), Nat.sub_self, pow_zero, mul_one]
    rw [xOf_ix]; simp
  · intro i hi hne
    have hi' := mem_range.mp hi
    simp only [ad, dif_pos hi', xOf_ix, if_neg hne, ZMod.val_zero, zero_mul]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

/-- The entry `f_cd = Φ_cd[0, k-1]` (the coefficient of the last cell digit of `d` in the first
offset digit of `c`). -/
def fE (hs : 2 ≤ s) (hk : 1 ≤ k) (c d : Fin s) : ZMod q :=
  Φ c d ⟨0, by have := Nat.mul_le_mul_right k hs; omega⟩ ⟨k - 1, by omega⟩

lemma o0G_xOf (hs : 2 ≤ s) (hk : 1 ≤ k) (w : Fin s → ZMod q) (c : Fin s) :
    o0G s q k Φ (xOf s q k w) c = (∑ d, fE s q k Φ hs hk c d * w d).val := by
  have hsk : k < s * k := by have := Nat.mul_le_mul_right k hs; omega
  set r0 : Fin (s * k - k) := ⟨0, by omega⟩
  have e := DgG_off s q k Φ c (xOf s q k w) r0
  have e2 : DgG s q k Φ c (xOf s q k w) ⟨k + (r0 : ℕ), sk_sub_add r0⟩ =
      DgG s q k Φ c (xOf s q k w) ⟨k, hsk⟩ := rfl
  unfold o0G dv
  rw [dif_pos hsk, ← e2, e]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [xOf_ix, if_pos rfl]; rfl
  · intro l _ hl
    rw [xOf_ix, if_neg (fun h => hl (Fin.ext h)), mul_zero]
  · intro h; exact absurd (mem_univ _) h

lemma two_fE (hs : 2 ≤ s) (hk : 1 ≤ k) (F2 : ℕ → Fin s → Fin s → ℤ)
    (hrow : RowDesign s q k Φ F2) (c d : Fin s) : 2 * fE s q k Φ hs hk c d = (F2 0 c d : ZMod q) := by
  unfold fE
  rw [hrow c d _ rfl, if_pos (by simp; omega)]
  simp

/-- Coordinate differences of two witness indices. -/
lemma Xdiff_xOf (hs : 2 ≤ s) (hk : 1 ≤ k) (w w' : Fin s → ZMod q) (c : Fin s) :
    ∃ τ : ℤ, |τ| < (q : ℤ) ^ (s * k - k - 1) ∧
      (GFpoint s q k Φ (xOf s q k w') c : ℤ) - GFpoint s q k Φ (xOf s q k w) c =
        (q : ℤ) ^ (s * k - k) * (((w' c).val : ℤ) - (w c).val) +
        (q : ℤ) ^ (s * k - k - 1) * (((∑ d, fE s q k Φ hs hk c d * w' d).val : ℤ) -
          (∑ d, fE s q k Φ hs hk c d * w d).val) + τ := by
  have hsk : k + 1 ≤ s * k := by have := Nat.mul_le_mul_right k hs; omega
  refine ⟨(tlG s q k Φ (xOf s q k w') c : ℤ) - tlG s q k Φ (xOf s q k w) c, ?_, ?_⟩
  · have h1 := tlG_lt s q k Φ hsk (xOf s q k w') c
    have h2 := tlG_lt s q k Φ hsk (xOf s q k w) c
    have h1' : ((tlG s q k Φ (xOf s q k w') c : ℕ) : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by
      exact_mod_cast h1
    have h2' : ((tlG s q k Φ (xOf s q k w) c : ℕ) : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by
      exact_mod_cast h2
    rw [abs_lt]; constructor <;> omega
  · rw [XG_decomp s q k Φ hsk, XG_decomp s q k Φ hsk, cellN_xOf s q k hk, cellN_xOf s q k hk,
      o0G_xOf s q k Φ hs hk, o0G_xOf s q k Φ hs hk]
    ring

lemma xOf_ne (hk : 1 ≤ k) (w w' : Fin s → ZMod q) (a : Fin s) (h : w a ≠ w' a) :
    xOf s q k w' ≠ xOf s q k w := by
  intro he
  have := congrFun he (ix k a ⟨k - 1, by omega⟩)
  rw [xOf_ix, xOf_ix, if_pos rfl, if_pos rfl] at this
  exact h this.symm

end wit

/-! ## Real bookkeeping -/

lemma sqrt_sum_le_of_abs {s : ℕ} (D : Fin s → ℝ) (b : ℝ) (hb : 0 ≤ b) (h : ∀ c, |D c| ≤ b) :
    Real.sqrt (∑ c, D c ^ 2) ≤ Real.sqrt s * b := by
  rw [show Real.sqrt s * b = Real.sqrt ((s : ℝ) * b ^ 2) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb]]
  apply Real.sqrt_le_sqrt
  calc ∑ c, D c ^ 2 ≤ ∑ _c : Fin s, b ^ 2 := Finset.sum_le_sum fun c _ => by
        have := h c
        have h0 := abs_nonneg (D c)
        rw [← sq_abs]; nlinarith
    _ = (s : ℝ) * b ^ 2 := by simp

lemma sqrt_sum_le_two {s : ℕ} (hs : 2 ≤ s) (D : Fin s → ℝ) (P T : ℝ) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (a b : Fin s) (hab : a ≠ b) (ha : |D a| ≤ P + T) (hb : |D b| ≤ P + T)
    (hc : ∀ c, c ≠ a → c ≠ b → |D c| ≤ T) :
    Real.sqrt (∑ c, D c ^ 2) ≤ Real.sqrt 2 * P + Real.sqrt s * T := by
  have hsq : ∀ c, D c ^ 2 ≤ T ^ 2 + (if c = a then (P + T) ^ 2 - T ^ 2 else 0) +
      (if c = b then (P + T) ^ 2 - T ^ 2 else 0) := by
    intro c
    by_cases h1 : c = a
    · subst h1
      rw [if_pos rfl, if_neg hab]
      have := abs_nonneg (D c); rw [← sq_abs]; nlinarith
    · by_cases h2 : c = b
      · subst h2
        rw [if_neg h1, if_pos rfl]
        have := abs_nonneg (D c); rw [← sq_abs]; nlinarith
      · rw [if_neg h1, if_neg h2]
        have := hc c h1 h2
        have := abs_nonneg (D c); rw [← sq_abs]; nlinarith
  have hsum : ∑ c, D c ^ 2 ≤ (s : ℝ) * T ^ 2 + 2 * ((P + T) ^ 2 - T ^ 2) := by
    calc ∑ c, D c ^ 2 ≤ ∑ c, (T ^ 2 + (if c = a then (P + T) ^ 2 - T ^ 2 else 0) +
          (if c = b then (P + T) ^ 2 - T ^ 2 else 0)) := Finset.sum_le_sum fun c _ => hsq c
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp; ring
  have h2s : (2 : ℝ) ≤ Real.sqrt 2 * Real.sqrt s := by
    have hr0 : 0 ≤ Real.sqrt 2 * Real.sqrt s := by positivity
    have hr2 : (Real.sqrt 2 * Real.sqrt s) ^ 2 = 2 * s := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  rw [Real.sqrt_le_left (by positivity)]
  have e2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have es : Real.sqrt s ^ 2 = s := Real.sq_sqrt (by positivity)
  calc ∑ c, D c ^ 2 ≤ (s : ℝ) * T ^ 2 + 2 * ((P + T) ^ 2 - T ^ 2) := hsum
    _ ≤ (Real.sqrt 2 * P + Real.sqrt s * T) ^ 2 := by
        have : 0 ≤ P * T := mul_nonneg hP hT
        nlinarith

lemma Npow_eq (s q k : ℕ) (hs : 1 ≤ s) (hq : 1 ≤ q) :
    ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) = 1 / (q : ℝ) ^ k := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : (s : ℝ) ≠ 0 := by
    have h0 : (0 : ℝ) < s := by exact_mod_cast hs
    exact h0.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, show ((s * k : ℕ) : ℝ) * (-(1 / (s : ℝ))) =
    -(k : ℝ) by push_cast; field_simp, Real.rpow_neg hq0.le, Real.rpow_natCast, one_div]

/-! ## Prop H_k(3) -/

theorem GF_upper_core (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (F2 : ℕ → Fin s → Fin s → ℤ) (hs : 3 ≤ s) (hq : q.Prime) (hk : 1 ≤ k)
    (hrow : RowDesign s q k Φ F2) (hhalf0 : ∀ c d, Odd (F2 0 c d))
    (hqC : 2 * s * C2max s F2 + 2 < q) :
    ∃ x y : Fin (s * k) → ZMod q, x ≠ y ∧
      Real.sqrt (∑ c, (((GFpoint s q k Φ x c : ℝ) - (GFpoint s q k Φ y c : ℝ)) / (q : ℝ) ^ (s * k)) ^ 2)
        ≤ (min (Real.sqrt s / 2) (Real.sqrt 2) + Real.sqrt s * ((C2max s F2 : ℝ) + 1) / q) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (1 < q) := ⟨hq.one_lt⟩
  have hs2 : 2 ≤ s := by omega
  set C2 := C2max s F2 with hC2def
  have hC : ∀ c d, |F2 0 c d| ≤ (C2 : ℤ) := by
    intro c d
    have h1 := Finset.le_sup (f := fun d : Fin s => (F2 0 c d).natAbs) (mem_univ d)
    have h2 := Finset.le_sup (f := fun c : Fin s => univ.sup fun d : Fin s => (F2 0 c d).natAbs)
      (mem_univ c)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1.trans h2
  have hqC' : (2 * s * C2 + 2 : ℤ) < q := by exact_mod_cast hqC
  have hs' : (3 : ℤ) ≤ s := by exact_mod_cast hs
  have hC0 : (0 : ℤ) ≤ C2 := by positivity
  have hCq : (C2 : ℤ) < q := by nlinarith
  have hq2 : q ≠ 2 := by
    intro h; rw [h] at hqC'; push_cast at hqC'; nlinarith
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hq1 : 1 ≤ q := hq.one_lt.le
  set f := fE s q k Φ hs2 hk with hfdef
  have h2f : ∀ c d, 2 * f c d = (F2 0 c d : ZMod q) := two_fE s q k Φ hs2 hk F2 hrow
  have hFq : ∀ c d, |F2 0 c d| < q := fun c d => lt_of_le_of_lt (hC c d) hCq
  have hfval : ∀ c d, 2 * ((f c d).val : ℤ) = F2 0 c d + q := fun c d =>
    two_val_eq q hqodd (f c d) (F2 0 c d) (hhalf0 c d) (hFq c d) (h2f c d)
  have hf0 : ∀ c d, f c d ≠ 0 := by
    intro c d h
    have := hfval c d
    rw [h, ZMod.val_zero] at this
    have := hFq c d
    rw [abs_lt] at this; push_cast at *; linarith
  -- common real quantities
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hsk : k + 1 ≤ s * k := by have := Nat.mul_le_mul_right k hs2; omega
  set U : ℝ := (q : ℝ) ^ (s * k - k - 1) with hU
  set N : ℝ := (q : ℝ) ^ (s * k) with hN
  have hU0 : 0 < U := by positivity
  have hPU : (q : ℝ) ^ (s * k - k) = U * q := by rw [hU, ← pow_succ]; congr 1; omega
  have hNU : N = U * q * (q : ℝ) ^ k := by rw [hN, ← hPU, ← pow_add]; congr 1; omega
  have hNp : ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) = 1 / (q : ℝ) ^ k := Npow_eq s q k (by omega) hq1
  set a : Fin s := ⟨0, by omega⟩
  set b : Fin s := ⟨1, by omega⟩
  set g : Fin s := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hag : a ≠ g := by simp [a, g, Fin.ext_iff]
  have hbg : b ≠ g := by simp [b, g, Fin.ext_iff]
  have hCr : (0 : ℝ) ≤ C2 := by positivity
  rcases le_total (Real.sqrt s / 2) (Real.sqrt 2) with hmin | hmin
  · -- step `E = e_a` with a wrap of `r_a`
    rw [min_eq_left hmin]
    set t : ZMod q := (f a b)⁻¹ * ((q - 1 : ℕ) : ZMod q)
    set w : Fin s → ZMod q := Pi.single b t
    set w' : Fin s → ZMod q := w + Pi.single a 1
    have hwa : w a = 0 := by simp [w, Pi.single_apply, hab]
    have hw'a : w' a = 1 := by simp [w', w, Pi.single_apply, hab]
    have hw'c : ∀ c, c ≠ a → w' c = w c := by
      intro c hc; simp [w', Pi.single_apply, hc]
    have hS : ∀ c, ∑ d, f c d * w d = f c b * t := by
      intro c; simp [w, Pi.single_apply, mul_comm]
    have hS' : ∀ c, ∑ d, f c d * w' d = f c b * t + f c a := by
      intro c
      simp only [w', Pi.add_apply, mul_add, Finset.sum_add_distrib, hS]
      simp [Pi.single_apply]
    refine ⟨xOf s q k w', xOf s q k w, xOf_ne s q k hk w w' a (by rw [hwa, hw'a]; exact zero_ne_one),
      ?_⟩
    have hbound : ∀ c, |((GFpoint s q k Φ (xOf s q k w') c : ℝ) - (GFpoint s q k Φ (xOf s q k w) c : ℝ)) / N|
        ≤ (1 / 2 + ((C2 : ℝ) + 1) / q) * (1 / (q : ℝ) ^ k) := by
      intro c
      obtain ⟨τ, hτ, hX⟩ := Xdiff_xOf s q k Φ hs2 hk w w' c
      -- integer bound `2 |X' - X| ≤ U (q + C2 + 2)`
      have hint : 2 * |(GFpoint s q k Φ (xOf s q k w') c : ℤ) - GFpoint s q k Φ (xOf s q k w) c| ≤
          (q : ℤ) ^ (s * k - k - 1) * (q + C2 + 2) := by
        have hUq : (q : ℤ) ^ (s * k - k) = (q : ℤ) ^ (s * k - k - 1) * q := by
          rw [← pow_succ]; congr 1; omega
        have hUz : (0 : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by positivity
        rw [hX, hS', hS]
        have hτ' := abs_lt.mp hτ
        by_cases hca : c = a
        · rw [hca, hw'a, hwa]
          have hval1 : ((1 : ZMod q).val : ℤ) = 1 := by rw [ZMod.val_one]; rfl
          have ht : f a b * t = ((q - 1 : ℕ) : ZMod q) := by
            simp only [t]; rw [← mul_assoc, mul_inv_cancel₀ (hf0 a b), one_mul]
          have hvt : ((f a b * t).val : ℤ) = q - 1 := by
            rw [ht, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; push_cast [hq1]; ring
          have hvc := hfval a a
          have hFc := abs_le.mp (hC a a)
          have hv1 : 1 ≤ ((f a a).val : ℤ) := by omega
          have hvlt : ((f a a).val : ℤ) < q := by exact_mod_cast ZMod.val_lt _
          have hlt : (((f a b * t + f a a).val : ℤ)) < q := by exact_mod_cast ZMod.val_lt _
          have hsum : (((f a b * t + f a a).val : ℤ)) = (f a a).val - 1 := by
            rcases val_add_cases q (f a b * t) (f a a) with h | h <;> rw [h] at hlt ⊢ <;>
              rw [hvt] at hlt ⊢ <;> omega
          rw [hsum, hvt, hval1, ZMod.val_zero, hUq]
          apply two_abs_le <;> push_cast <;> clear * - hUz hτ' hvc hFc hvlt hv1 <;> nlinarith
        · rw [hw'c c hca]
          have hvlt : ((f c a).val : ℤ) < q := by exact_mod_cast ZMod.val_lt _
          have hvc := hfval c a
          have hFc := abs_le.mp (hC c a)
          rw [sub_self, mul_zero, zero_add]
          rcases val_add_cases q (f c b * t) (f c a) with h | h <;> rw [h] <;>
            apply two_abs_le <;> clear * - hUz hτ' hvc hFc hvlt <;> nlinarith
      have hreal := (Int.cast_le (R := ℝ)).mpr hint
      push_cast at hreal
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < N), div_le_iff₀ (by positivity), hNU]
      rw [← hU] at hreal
      have : (1 / 2 + ((C2 : ℝ) + 1) / q) * (1 / (q : ℝ) ^ k) * (U * q * (q : ℝ) ^ k) =
          U * ((q : ℝ) / 2 + C2 + 1) := by field_simp; ring
      rw [this]
      have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
      nlinarith
    calc Real.sqrt (∑ c, (((GFpoint s q k Φ (xOf s q k w') c : ℝ) -
          (GFpoint s q k Φ (xOf s q k w) c : ℝ)) / N) ^ 2)
        ≤ Real.sqrt s * ((1 / 2 + ((C2 : ℝ) + 1) / q) * (1 / (q : ℝ) ^ k)) :=
          sqrt_sum_le_of_abs _ _ (by positivity) hbound
      _ = _ := by rw [hNp]; ring
  · -- step `E = e_a - e_b` without wraps
    rw [min_eq_right hmin]
    -- `β_c = F_0[c][a] - F_0[c][b]`
    have hβex : ∀ c, ∃ β : ℤ, F2 0 c a - F2 0 c b = 2 * β := by
      intro c
      obtain ⟨u1, hu1⟩ := hhalf0 c a; obtain ⟨u2, hu2⟩ := hhalf0 c b
      exact ⟨u1 - u2, by rw [hu1, hu2]; ring⟩
    choose β hβ using hβex
    have hβC : ∀ c, |β c| ≤ C2 := by
      intro c
      have h1 := hC c a; have h2 := hC c b
      rw [abs_le] at h1 h2 ⊢
      have := hβ c
      constructor <;> omega
    have hfab : ∀ c, f c a = f c b + (β c : ZMod q) := by
      intro c
      have h2 : (2 : ZMod q) * (f c a - f c b - (β c : ZMod q)) = 0 := by
        rw [mul_sub, mul_sub, h2f, h2f]
        have : ((F2 0 c a - F2 0 c b : ℤ) : ZMod q) = ((2 * β c : ℤ) : ZMod q) := by rw [hβ c]
        push_cast at this
        rw [this]; ring
      have h2ne : (2 : ZMod q) ≠ 0 := by
        intro h
        have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at this
        have := Nat.le_of_dvd (by norm_num) this
        have : q = 2 := le_antisymm this hq.two_le
        exact hq2 this
      have := (mul_eq_zero.mp h2).resolve_left h2ne
      linear_combination this
    have hsumβ : ∑ c, (β c).natAbs < q := by
      have : ∑ c, (β c).natAbs ≤ ∑ _c : Fin s, C2 := Finset.sum_le_sum fun c _ => by
        have := hβC c; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
      have h2 : ∑ _c : Fin s, C2 = s * C2 := by simp
      have : s * C2 < q := by
        have : s * C2 ≤ 2 * s * C2 := by nlinarith
        omega
      omega
    obtain ⟨t, ht⟩ := exists_good q (fun c => f c g) (fun c => f c b) β (fun c => hf0 c g) hsumβ
    set w : Fin s → ZMod q := Pi.single g t + Pi.single b 1
    set w' : Fin s → ZMod q := Pi.single g t + Pi.single a 1
    have hS : ∀ c, ∑ d, f c d * w d = f c g * t + f c b := by
      intro c
      simp only [w, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      simp [Pi.single_apply]
    have hS' : ∀ c, ∑ d, f c d * w' d = f c g * t + f c b + (β c : ZMod q) := by
      intro c
      simp only [w', Pi.add_apply, mul_add, Finset.sum_add_distrib]
      simp [Pi.single_apply, hfab, add_assoc]
    have hwa : w a = 0 := by simp [w, Pi.single_apply, hab, hag]
    have hw'a : w' a = 1 := by simp [w', Pi.single_apply, hag]
    have hwb : w b = 1 := by simp [w, Pi.single_apply, hbg]
    have hw'b : w' b = 0 := by simp [w', Pi.single_apply, hbg, hab.symm]
    have hwc : ∀ c, c ≠ a → c ≠ b → w' c = w c := by
      intro c h1 h2; simp [w, w', Pi.single_apply, h1, h2]
    refine ⟨xOf s q k w', xOf s q k w, xOf_ne s q k hk w w' a (by rw [hwa, hw'a]; exact zero_ne_one),
      ?_⟩
    have hval1 : ((1 : ZMod q).val : ℤ) = 1 := by rw [ZMod.val_one]; rfl
    -- per coordinate: `|X' - X - q^(sk-k) E_c| ≤ U (C2 + 1)` (integers)
    have hint : ∀ c, |(GFpoint s q k Φ (xOf s q k w') c : ℤ) - GFpoint s q k Φ (xOf s q k w) c -
        (q : ℤ) ^ (s * k - k) * (((w' c).val : ℤ) - (w c).val)| ≤
        (q : ℤ) ^ (s * k - k - 1) * (C2 + 1) := by
      intro c
      obtain ⟨τ, hτ, hX⟩ := Xdiff_xOf s q k Φ hs2 hk w w' c
      rw [hX, hS', hS, val_add_int q _ (β c) (ht c).1 (ht c).2]
      have e : (q : ℤ) ^ (s * k - k) * (((w' c).val : ℤ) - (w c).val) +
          (q : ℤ) ^ (s * k - k - 1) * (((f c g * t + f c b).val : ℤ) + β c - (f c g * t + f c b).val) + τ -
          (q : ℤ) ^ (s * k - k) * (((w' c).val : ℤ) - (w c).val) =
          (q : ℤ) ^ (s * k - k - 1) * β c + τ := by ring
      rw [e]
      have hUz : (0 : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by positivity
      have hτ' := abs_lt.mp hτ
      have hb := abs_le.mp (hβC c)
      rw [abs_le]; constructor <;> nlinarith
    set P : ℝ := (q : ℝ) ^ (s * k - k) with hP
    set T : ℝ := U * ((C2 : ℝ) + 1) with hT
    set D : Fin s → ℝ := fun c => ((GFpoint s q k Φ (xOf s q k w') c : ℝ) -
      (GFpoint s q k Φ (xOf s q k w) c : ℝ)) with hD
    have hreal : ∀ c, |D c - P * (((w' c).val : ℝ) - (w c).val)| ≤ T := by
      intro c
      have := (Int.cast_le (R := ℝ)).mpr (hint c)
      push_cast at this
      simpa [hD, hP, hT, hU] using this
    have hDa : |D a| ≤ P + T := by
      have := hreal a
      rw [hw'a, hwa, ZMod.val_zero] at this
      have h1 : ((1 : ZMod q).val : ℝ) = 1 := by exact_mod_cast hval1
      rw [h1] at this
      have := abs_sub_abs_le_abs_sub (D a) (P * (1 - ((0 : ℕ) : ℝ)))
      simp at *
      have hP0 : 0 ≤ P := by positivity
      rw [abs_of_nonneg hP0] at *
      linarith
    have hDb : |D b| ≤ P + T := by
      have := hreal b
      rw [hw'b, hwb, ZMod.val_zero] at this
      have h1 : ((1 : ZMod q).val : ℝ) = 1 := by exact_mod_cast hval1
      rw [h1] at this
      have := abs_sub_abs_le_abs_sub (D b) (P * (((0 : ℕ) : ℝ) - 1))
      have hP0 : 0 ≤ P := by positivity
      simp at *
      rw [abs_of_nonneg hP0] at *
      linarith
    have hDc : ∀ c, c ≠ a → c ≠ b → |D c| ≤ T := by
      intro c h1 h2
      have := hreal c
      rw [hwc c h1 h2, sub_self, mul_zero, sub_zero] at this
      exact this
    have hmain := sqrt_sum_le_two hs2 D P T (by positivity) (by positivity) a b hab hDa hDb hDc
    have hrw : ∑ c, (((GFpoint s q k Φ (xOf s q k w') c : ℝ) - (GFpoint s q k Φ (xOf s q k w) c : ℝ)) / N) ^ 2 =
        (∑ c, D c ^ 2) / N ^ 2 := sum_div_sq N D
    rw [hrw, Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ N ^ 2), Real.sqrt_sq (by positivity), hNp,
      div_le_iff₀ (by positivity)]
    have e : (Real.sqrt 2 + Real.sqrt s * ((C2 : ℝ) + 1) / q) * (1 / (q : ℝ) ^ k) * N =
        Real.sqrt 2 * P + Real.sqrt s * T := by
      rw [hNU, hT, hPU]; field_simp
    rw [e]; exact hmain

end

end Z3NetHL.Proofs

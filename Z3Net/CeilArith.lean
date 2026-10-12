/-
Proofs for Proposition `prop:ceil` (first-order ceiling): base-`q` digit arithmetic.
-/
module
public import Z3Net.Defs

@[expose] public section

/-!
# Base-`q` digit strings, most significant digit first

`bval q x n = ∑_{j<n} x_j q^(n-1-j)` (natural digits) and its integer analogue `zval`.
-/

namespace Z3Net.Proofs

open Finset

/-- Base-`q` value of the digit string `x_0 … x_{n-1}` (`x_0` most significant). -/
def bval (q : ℕ) (x : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ range n, x j * q ^ (n - 1 - j)

theorem bval_zero (q : ℕ) (x : ℕ → ℕ) : bval q x 0 = 0 := by simp [bval]

theorem bval_succ (q : ℕ) (x : ℕ → ℕ) (n : ℕ) : bval q x (n + 1) = q * bval q x n + x n := by
  unfold bval
  rw [sum_range_succ, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have hj := mem_range.mp hj
    have : n + 1 - 1 - j = (n - 1 - j) + 1 := by omega
    rw [this, pow_succ]; ring
  · simp

theorem bval_lt {q : ℕ} {x : ℕ → ℕ} {n : ℕ} (hx : ∀ j < n, x j < q) : bval q x n < q ^ n := by
  induction n with
  | zero => simp [bval]
  | succ n ih =>
    rw [bval_succ, pow_succ]
    have h1 := ih (fun j hj => hx j (by omega))
    have h2 := hx n (by omega)
    have : q * bval q x n + x n < q * (bval q x n + 1) := by nlinarith
    calc q * bval q x n + x n < q * (bval q x n + 1) := this
      _ ≤ q * q ^ n := Nat.mul_le_mul_left _ h1
      _ = q ^ n * q := by ring

theorem bval_add (q : ℕ) (x : ℕ → ℕ) (d e : ℕ) :
    bval q x (d + e) = q ^ e * bval q x d + bval q (fun j => x (d + j)) e := by
  induction e with
  | zero => simp [bval_zero]
  | succ e ih =>
    rw [← add_assoc, bval_succ, ih, bval_succ, pow_succ]; ring

theorem bval_div {q : ℕ} {x : ℕ → ℕ} {d e : ℕ} (hx : ∀ j < d + e, x j < q) :
    bval q x (d + e) / q ^ e = bval q x d := by
  have hpos : 0 < q ^ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · simp [h]
    · exact pow_pos (lt_of_le_of_lt (Nat.zero_le _) (hx d (by omega))) _
  have hlt : bval q (fun j => x (d + j)) e < q ^ e := bval_lt (fun j hj => hx _ (by omega))
  rw [bval_add, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, add_zero]

theorem bval_inj {q : ℕ} {x y : ℕ → ℕ} {n : ℕ} (hx : ∀ j < n, x j < q) (hy : ∀ j < n, y j < q)
    (h : bval q x n = bval q y n) : ∀ j < n, x j = y j := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    rw [bval_succ, bval_succ] at h
    have hxn := hx n (by omega)
    have hyn := hy n (by omega)
    have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hxn
    have hmod : x n = y n := by
      have h1 := congrArg (· % q) h
      simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hxn, Nat.mod_eq_of_lt hyn] at h1
      exact h1
    have hdiv : bval q x n = bval q y n := by
      have h1 : (q * bval q x n + x n) / q = (q * bval q y n + y n) / q := by rw [h]
      rwa [Nat.mul_add_div hq, Nat.mul_add_div hq, Nat.div_eq_of_lt hxn, Nat.div_eq_of_lt hyn,
        add_zero, add_zero] at h1
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact ih (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega)) hdiv j hj
    · subst hj; exact hmod

/-- Integer base-`q` value of the signed digit string `e_0 … e_{n-1}` (`e_0` most significant). -/
def zval (q : ℤ) (e : ℕ → ℤ) (n : ℕ) : ℤ := ∑ j ∈ range n, e j * q ^ (n - 1 - j)

theorem zval_zero (q : ℤ) (e : ℕ → ℤ) : zval q e 0 = 0 := by simp [zval]

theorem zval_succ (q : ℤ) (e : ℕ → ℤ) (n : ℕ) : zval q e (n + 1) = q * zval q e n + e n := by
  unfold zval
  rw [sum_range_succ, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have hj := mem_range.mp hj
    have : n + 1 - 1 - j = (n - 1 - j) + 1 := by omega
    rw [this, pow_succ]; ring
  · simp

theorem zval_add (q : ℤ) (e : ℕ → ℤ) (d n : ℕ) :
    zval q e (d + n) = q ^ n * zval q e d + zval q (fun j => e (d + j)) n := by
  induction n with
  | zero => simp [zval_zero]
  | succ n ih =>
    rw [← add_assoc, zval_succ, ih, zval_succ, pow_succ]; ring

theorem zval_sub (q : ℤ) (e f : ℕ → ℤ) (n : ℕ) :
    zval q e n - zval q f n = zval q (fun j => e j - f j) n := by
  unfold zval; rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; ring

theorem zval_eq_zero (q : ℤ) {e : ℕ → ℤ} {n : ℕ} (h : ∀ j < n, e j = 0) : zval q e n = 0 := by
  unfold zval; apply sum_eq_zero; intro j hj; rw [h j (mem_range.mp hj)]; ring

theorem zval_nonpos {q : ℤ} (hq : 0 ≤ q) {e : ℕ → ℤ} {n : ℕ} (h : ∀ j < n, e j ≤ 0) :
    zval q e n ≤ 0 := by
  unfold zval; apply sum_nonpos; intro j hj
  exact mul_nonpos_of_nonpos_of_nonneg (h j (mem_range.mp hj)) (pow_nonneg hq _)

theorem zval_le {q : ℤ} (hq : 1 ≤ q) {e : ℕ → ℤ} {n : ℕ} (h : ∀ j < n, e j ≤ q - 1) :
    zval q e n ≤ q ^ n - 1 := by
  induction n with
  | zero => simp [zval_zero]
  | succ n ih =>
    rw [zval_succ, pow_succ]
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    nlinarith

theorem zval_ge {q : ℤ} (hq : 1 ≤ q) {e : ℕ → ℤ} {n : ℕ} (h : ∀ j < n, -(q - 1) ≤ e j) :
    -(q ^ n - 1) ≤ zval q e n := by
  induction n with
  | zero => simp [zval_zero]
  | succ n ih =>
    rw [zval_succ, pow_succ]
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    nlinarith

theorem bval_cast (q : ℕ) (x : ℕ → ℕ) (n : ℕ) :
    ((bval q x n : ℕ) : ℤ) = zval (q : ℤ) (fun j => (x j : ℤ)) n := by
  unfold bval zval; push_cast; rfl

/-! ## Wrap sets of a constant digit change -/

/-- Adding `M` to the digit `x` does not wrap: the value changes by exactly the centred
representative of `M`. -/
def good {p : ℕ} (M x : ZMod p) : Prop := ((x + M).val : ℤ) = (x.val : ℤ) + M.valMinAbs

instance good.decidable {p : ℕ} (M x : ZMod p) : Decidable (good M x) :=
  inferInstanceAs (Decidable (((x + M).val : ℤ) = (x.val : ℤ) + M.valMinAbs))

theorem card_bad_le {p : ℕ} [NeZero p] (M : ZMod p) :
    (univ.filter (fun x : ZMod p => ¬ good M x)).card ≤ M.valMinAbs.natAbs := by
  set s := M.valMinAbs with hs
  have hMs : M = (s : ZMod p) := (ZMod.coe_valMinAbs M).symm
  have hsle : s.natAbs ≤ p / 2 := ZMod.natAbs_valMinAbs_le M
  rcases le_or_gt 0 s with h0 | h0
  · -- `s = n ≥ 0`: bad digits are `x ≥ p - n`, i.e. `x = p - 1 - i`, `i < n`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, (Int.toNat_of_nonneg h0).symm⟩
    have hnp : n < p := by
      have : s.natAbs = n := by rw [hn]; simp
      have : p / 2 < p := Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne p)) (by norm_num)
      omega
    have hsub : univ.filter (fun x : ZMod p => ¬ good M x) ⊆
        (range n).image (fun i => ((p - 1 - i : ℕ) : ZMod p)) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [mem_image]
      have hxl := ZMod.val_lt x
      have hge : p ≤ x.val + n := by
        by_contra hlt
        apply hx
        unfold good
        rw [← hs, hn, hMs, hn]
        push_cast
        rw [ZMod.val_add, ZMod.val_natCast_of_lt hnp, Nat.mod_eq_of_lt (by omega)]
        push_cast; ring
      refine ⟨p - 1 - x.val, mem_range.mpr (by omega), ?_⟩
      rw [show p - 1 - (p - 1 - x.val) = x.val by omega, ZMod.natCast_zmod_val]
    calc _ ≤ ((range n).image (fun i => ((p - 1 - i : ℕ) : ZMod p))).card := card_le_card hsub
      _ ≤ (range n).card := card_image_le
      _ = s.natAbs := by rw [card_range, hn]; simp
  · -- `s = -n < 0`: bad digits are `x < n`
    obtain ⟨n, hn⟩ : ∃ n : ℕ, s = -(n : ℤ) := ⟨(-s).toNat, by omega⟩
    have hnp : n < p := by
      have : s.natAbs = n := by rw [hn]; simp
      have : p / 2 < p := Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne p)) (by norm_num)
      omega
    have hsub : univ.filter (fun x : ZMod p => ¬ good M x) ⊆
        (range n).image (fun i => ((i : ℕ) : ZMod p)) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [mem_image]
      have hlt : x.val < n := by
        by_contra hge
        push Not at hge
        apply hx
        unfold good
        rw [← hs, hn, hMs, hn]
        push_cast
        rw [← sub_eq_add_neg, ZMod.val_sub (by rwa [ZMod.val_natCast_of_lt hnp]),
          ZMod.val_natCast_of_lt hnp]
        push_cast [hge]; ring
      exact ⟨x.val, mem_range.mpr hlt, ZMod.natCast_zmod_val x⟩
    calc _ ≤ ((range n).image (fun i => ((i : ℕ) : ZMod p))).card := card_le_card hsub
      _ ≤ (range n).card := card_image_le
      _ = s.natAbs := by rw [card_range, hn]; simp

/-- On an affine line `t ↦ (β₀ + t β₁, γ₀ + t γ₁)` with `β₁, γ₁ ≠ 0` some point avoids both
wrap sets (union bound: `|M̃_b| + |M̃_c| ≤ p - 1 < p`). -/
theorem exists_good_line {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (Mb Mc β₀ β₁ γ₀ γ₁ : ZMod p)
    (hβ : β₁ ≠ 0) (hγ : γ₁ ≠ 0) : ∃ t : ZMod p, good Mb (β₀ + t * β₁) ∧ good Mc (γ₀ + t * γ₁) := by
  have := Fact.mk hp
  set Sb := univ.filter (fun t : ZMod p => ¬ good Mb (β₀ + t * β₁))
  set Sc := univ.filter (fun t : ZMod p => ¬ good Mc (γ₀ + t * γ₁))
  have hb : Sb.card ≤ Mb.valMinAbs.natAbs := by
    refine le_trans (card_le_card_of_injOn (t := univ.filter (fun x : ZMod p => ¬ good Mb x))
      (fun t => β₀ + t * β₁) ?_ ?_) (card_bad_le Mb)
    · intro t ht
      simp only [Sb, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht
      simpa using ht
    · intro t _ t' _ h
      simp only [add_right_inj] at h
      exact mul_right_cancel₀ hβ h
  have hc : Sc.card ≤ Mc.valMinAbs.natAbs := by
    refine le_trans (card_le_card_of_injOn (t := univ.filter (fun x : ZMod p => ¬ good Mc x))
      (fun t => γ₀ + t * γ₁) ?_ ?_) (card_bad_le Mc)
    · intro t ht
      simp only [Sc, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht
      simpa using ht
    · intro t _ t' _ h
      simp only [add_right_inj] at h
      exact mul_right_cancel₀ hγ h
  have h1 := ZMod.natAbs_valMinAbs_le Mb
  have h2 := ZMod.natAbs_valMinAbs_le Mc
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hlt : (Sb ∪ Sc).card < (univ : Finset (ZMod p)).card := by
    rw [card_univ, ZMod.card]
    have := card_union_le Sb Sc
    omega
  obtain ⟨t, -, ht⟩ := exists_mem_notMem_of_card_lt_card hlt
  simp only [mem_union, Sb, Sc, mem_filter, mem_univ, true_and, not_or, not_not] at ht
  exact ⟨t, ht⟩

end Z3Net.Proofs

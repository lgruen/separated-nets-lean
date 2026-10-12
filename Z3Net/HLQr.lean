module
public import Mathlib
public import Z3Net.HLDefs

@[expose] public section

/-!
# Entry HL, part 2: rational numbers modulo `q`

`qr q x = num(x) · den(x)⁻¹ ∈ ℤ/qℤ` is additive and multiplicative on the rationals whose
denominator is a unit mod `q` (`Good q`). The basic tool is `qr_of_mul`: if `z · b = a` with
`a ∈ ℤ` and `b ∈ ℕ` a unit mod `q`, then `z` is good and `qr q z = a · b⁻¹`.
-/

namespace Z3NetHL.Proofs

open Finset

/-- The denominator of `x` is a unit mod `q`. -/
def Good (q : ℕ) (x : ℚ) : Prop := IsUnit (((x.den : ℕ) : ZMod q))

variable {q : ℕ}

lemma isUnit_of_dvd_nat {a b : ℕ} (h : a ∣ b) (hb : IsUnit ((b : ℕ) : ZMod q)) :
    IsUnit ((a : ℕ) : ZMod q) :=
  isUnit_of_dvd_unit (Nat.cast_dvd_cast h) hb

lemma isUnit_int_of_gcd {z : ℤ} (h : Int.gcd z q = 1) : IsUnit ((z : ℤ) : ZMod q) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  exact h

lemma isUnit_nat_of_coprime {n : ℕ} (h : Nat.Coprime n q) : IsUnit ((n : ℕ) : ZMod q) :=
  (ZMod.isUnit_iff_coprime n q).mpr h

lemma num_mul_eq (z : ℚ) (a : ℤ) (b : ℕ) (h : z * b = a) : z.num * b = a * z.den := by
  have e1 : (z.num : ℚ) = z * z.den := (Rat.mul_den_eq_num z).symm
  have : (z.num : ℚ) * b = a * z.den := by rw [e1, ← h]; ring
  exact_mod_cast this

lemma den_dvd_of_mul (z : ℚ) (a : ℤ) (b : ℕ) (h : z * b = a) : z.den ∣ b := by
  have e := num_mul_eq z a b h
  have h1 : (z.den : ℤ) ∣ z.num * b := ⟨a, by rw [e]; ring⟩
  have hc : IsCoprime (z.den : ℤ) z.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact z.reduced
  exact Int.natCast_dvd_natCast.mp (hc.dvd_of_dvd_mul_left h1)

/-- **The basic tool.** -/
lemma qr_of_mul (z : ℚ) (a : ℤ) (b : ℕ) (hb : IsUnit ((b : ℕ) : ZMod q)) (h : z * b = a) :
    Good q z ∧ qr q z = (a : ZMod q) * ((b : ℕ) : ZMod q)⁻¹ := by
  have hg : Good q z := isUnit_of_dvd_nat (den_dvd_of_mul z a b h) hb
  refine ⟨hg, ?_⟩
  have e := num_mul_eq z a b h
  have e' : (z.num : ZMod q) * (b : ZMod q) = (a : ZMod q) * (z.den : ZMod q) := by
    exact_mod_cast congrArg (fun t : ℤ => (t : ZMod q)) e
  unfold qr
  calc (z.num : ZMod q) * ((z.den : ℕ) : ZMod q)⁻¹
      = (z.num : ZMod q) * ((z.den : ℕ) : ZMod q)⁻¹ * ((b : ZMod q) * (b : ZMod q)⁻¹) := by
        rw [ZMod.mul_inv_of_unit _ hb, mul_one]
    _ = ((z.num : ZMod q) * (b : ZMod q)) * ((b : ZMod q)⁻¹ * ((z.den : ℕ) : ZMod q)⁻¹) := by ring
    _ = (a : ZMod q) * ((z.den : ZMod q) * ((z.den : ℕ) : ZMod q)⁻¹) * (b : ZMod q)⁻¹ := by
        rw [e']; ring
    _ = (a : ZMod q) * ((b : ℕ) : ZMod q)⁻¹ := by rw [ZMod.mul_inv_of_unit _ hg, mul_one]

lemma qr_spec (x : ℚ) : x * (x.den : ℕ) = x.num := by
  have := Rat.mul_den_eq_num x
  exact_mod_cast this

lemma qr_def' (x : ℚ) : qr q x = (x.num : ZMod q) * ((x.den : ℕ) : ZMod q)⁻¹ := rfl

lemma good_int (z : ℤ) : Good q (z : ℚ) := by simp [Good]

lemma qr_int (z : ℤ) : qr q (z : ℚ) = (z : ZMod q) := by
  simp [qr]

lemma qr_nat (n : ℕ) : qr q (n : ℚ) = (n : ZMod q) := by
  have := qr_int (q := q) (n : ℤ); simpa using this

lemma zinv_mul {a b : ZMod q} (ha : IsUnit a) (hb : IsUnit b) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one
  calc a * b * (a⁻¹ * b⁻¹) = (a * a⁻¹) * (b * b⁻¹) := by ring
    _ = 1 := by rw [ZMod.mul_inv_of_unit _ ha, ZMod.mul_inv_of_unit _ hb, one_mul]

lemma good_add {x y : ℚ} (hx : Good q x) (hy : Good q y) :
    Good q (x + y) ∧ qr q (x + y) = qr q x + qr q y := by
  have hb : IsUnit (((x.den * y.den : ℕ) : ℕ) : ZMod q) := by push_cast; exact hx.mul hy
  have h : (x + y) * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.den + y.num * x.den : ℤ) : ℚ) := by
    have h1 := qr_spec x; have h2 := qr_spec y
    push_cast
    rw [← h1, ← h2]; ring
  obtain ⟨hg, he⟩ := qr_of_mul (q := q) _ _ _ hb h
  refine ⟨hg, ?_⟩
  rw [he, qr_def', qr_def']
  push_cast
  rw [zinv_mul hx hy]
  have hxu := ZMod.mul_inv_of_unit _ hx
  have hyu := ZMod.mul_inv_of_unit _ hy
  linear_combination ((x.num : ZMod q) * ((x.den : ℕ) : ZMod q)⁻¹) * hyu +
    ((y.num : ZMod q) * ((y.den : ℕ) : ZMod q)⁻¹) * hxu

lemma good_mul {x y : ℚ} (hx : Good q x) (hy : Good q y) :
    Good q (x * y) ∧ qr q (x * y) = qr q x * qr q y := by
  have hb : IsUnit (((x.den * y.den : ℕ) : ℕ) : ZMod q) := by push_cast; exact hx.mul hy
  have h : (x * y) * ((x.den * y.den : ℕ) : ℚ) = ((x.num * y.num : ℤ) : ℚ) := by
    have h1 := qr_spec x; have h2 := qr_spec y
    push_cast
    rw [← h1, ← h2]; ring
  obtain ⟨hg, he⟩ := qr_of_mul (q := q) _ _ _ hb h
  refine ⟨hg, ?_⟩
  rw [he, qr_def', qr_def']
  push_cast
  rw [zinv_mul hx hy]; ring

lemma good_neg {x : ℚ} (hx : Good q x) : Good q (-x) ∧ qr q (-x) = -qr q x := by
  unfold Good at hx ⊢
  refine ⟨by rw [Rat.den_neg_eq_den]; exact hx, ?_⟩
  simp [qr, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den]

lemma good_sub {x y : ℚ} (hx : Good q x) (hy : Good q y) :
    Good q (x - y) ∧ qr q (x - y) = qr q x - qr q y := by
  rw [sub_eq_add_neg]
  obtain ⟨h1, h2⟩ := good_neg hy
  obtain ⟨h3, h4⟩ := good_add hx h1
  exact ⟨h3, by rw [h4, h2, ← sub_eq_add_neg]⟩

lemma good_pow {x : ℚ} (hx : Good q x) : ∀ n : ℕ, Good q (x ^ n) ∧ qr q (x ^ n) = qr q x ^ n
  | 0 => by
    refine ⟨?_, ?_⟩
    · simpa using good_int (q := q) 1
    · simpa using qr_int (q := q) 1
  | n + 1 => by
    obtain ⟨h1, h2⟩ := good_pow hx n
    obtain ⟨h3, h4⟩ := good_mul h1 hx
    exact ⟨by rw [pow_succ]; exact h3, by rw [pow_succ, h4, h2, pow_succ]⟩

lemma good_sum {ι : Type*} (S : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ S, Good q (f i)) :
    Good q (∑ i ∈ S, f i) ∧ qr q (∑ i ∈ S, f i) = ∑ i ∈ S, qr q (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · simpa using good_int (q := q) 0
    · simpa using qr_int (q := q) 0
  | insert a S ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (mem_insert_of_mem hi))
    obtain ⟨h3, h4⟩ := good_add (hf a (mem_insert_self a S)) h1
    rw [sum_insert ha, sum_insert ha]
    exact ⟨h3, by rw [h4, h2]⟩

lemma good_prod {ι : Type*} (S : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ S, Good q (f i)) :
    Good q (∏ i ∈ S, f i) ∧ qr q (∏ i ∈ S, f i) = ∏ i ∈ S, qr q (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · simpa using good_int (q := q) 1
    · simpa using qr_int (q := q) 1
  | insert a S ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (mem_insert_of_mem hi))
    obtain ⟨h3, h4⟩ := good_mul (hf a (mem_insert_self a S)) h1
    rw [prod_insert ha, prod_insert ha]
    exact ⟨h3, by rw [h4, h2]⟩

/-- Inverse of an integer that is a unit mod `q`. -/
lemma good_inv_int (z : ℤ) (hz : IsUnit ((z : ℤ) : ZMod q)) :
    Good q ((z : ℚ)⁻¹) ∧ qr q ((z : ℚ)⁻¹) = ((z : ℤ) : ZMod q)⁻¹ := by
  rcases eq_or_ne z 0 with h0 | h0
  · subst h0
    simp only [Int.cast_zero, inv_zero]
    refine ⟨by simpa using good_int (q := q) 0, ?_⟩
    rw [show ((0 : ℚ)) = ((0 : ℤ) : ℚ) by simp, qr_int]; simp [ZMod.inv_zero]
  · have hz' : (z : ZMod q) = (z.sign : ZMod q) * ((z.natAbs : ℕ) : ZMod q) := by
      have := congrArg (Int.cast : ℤ → ZMod q) (Int.sign_mul_natAbs z)
      rw [Int.cast_mul, Int.cast_natCast] at this; exact this.symm
    have hb : IsUnit (((z.natAbs : ℕ) : ℕ) : ZMod q) := by
      rw [hz'] at hz; exact isUnit_of_mul_isUnit_right hz
    have hsg : z.sign = 1 ∨ z.sign = -1 := by
      rcases lt_or_gt_of_ne h0 with hn | hp
      · exact Or.inr (Int.sign_eq_neg_one_of_neg hn)
      · exact Or.inl (Int.sign_eq_one_of_pos hp)
    have hs2 : (z.sign : ZMod q) * (z.sign : ZMod q) = 1 := by
      rcases hsg with h | h <;> rw [h] <;> simp
    have h : ((z : ℚ)⁻¹) * ((z.natAbs : ℕ) : ℚ) = ((z.sign : ℤ) : ℚ) := by
      have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast h0
      have e : ((z.natAbs : ℕ) : ℚ) = (z.sign : ℚ) * z := by
        have := congrArg (Int.cast : ℤ → ℚ) (Int.sign_mul_natAbs z)
        rw [Int.cast_mul, Int.cast_natCast] at this
        have hs : (z.sign : ℚ) * z.sign = 1 := by
          rcases hsg with h | h <;> rw [h] <;> simp
        calc ((z.natAbs : ℕ) : ℚ) = ((z.sign : ℚ) * z.sign) * z.natAbs := by rw [hs, one_mul]
          _ = (z.sign : ℚ) * (z.sign * z.natAbs) := by ring
          _ = (z.sign : ℚ) * z := by rw [this]
      rw [e]; field_simp
    obtain ⟨hg, he⟩ := qr_of_mul (q := q) _ _ _ hb h
    refine ⟨hg, ?_⟩
    rw [he]
    symm
    apply ZMod.inv_eq_of_mul_eq_one
    have hu := ZMod.mul_inv_of_unit _ hb
    rw [hz']
    linear_combination ((z.sign : ZMod q) * (z.sign : ZMod q)) * hu + hs2

lemma isUnit_qr {x : ℚ} (hx : Good q x) (hn : IsUnit ((x.num : ℤ) : ZMod q)) : IsUnit (qr q x) := by
  unfold qr
  exact hn.mul (isUnit_iff_exists.mpr ⟨_, ZMod.inv_mul_of_unit _ hx, ZMod.mul_inv_of_unit _ hx⟩)

end Z3NetHL.Proofs

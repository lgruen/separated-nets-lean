module
public import Mathlib
public import Z3Net.KNSepCoord
public import Z3Net.KNSepCheck

@[expose] public section

/-!
# KN separation, part 6: the near bound `term(c) · u ≤ cres_c`

Given the coarse steps `δ` (centred) inside the step box and the carry chains `ch` of every block,
the relaxed term of `Relax.term` times the sub-fine unit `u = p^(m-k-2)` is a lower bound for
the toroidal coordinate distance.
-/

namespace Z3NetKN.Geom

open Finset Matrix Z3NetKN.Relax

variable {p r k : ℕ}

lemma isOwn_spec (dl : Fin 3 → ℤ) (c : Fin 3) (h : isOwn dl c = true) (d : Fin 3) (hd : d ≠ c) :
    dl d = 0 := by
  fin_cases d <;> fin_cases c <;> simp_all [isOwn]

lemma tv_mul_le (B sl : ℤ) (hsl : sl = 0 ∨ sl = 1) (u : ℕ) (cr : ℤ)
    (h : |B| * u - sl * ((u : ℤ) - 1) ≤ cr) (h0 : 0 ≤ cr) : ((tv B sl : ℕ) : ℤ) * u ≤ cr := by
  unfold tv
  rcases le_or_gt (|B| - sl) 0 with h1 | h1
  · rw [Int.toNat_of_nonpos h1]; simpa using h0
  · rw [Int.toNat_of_nonneg h1.le]
    rcases hsl with rfl | rfl
    · simpa using h
    · nlinarith

lemma natCast_dg_sub [NeZero p] {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p)
    (j : ℕ) : ((((dg A v j : ℤ) - dg A w j : ℤ)) : ZMod p) = vz (A *ᵥ v) j - vz (A *ᵥ w) j := by
  push_cast
  simp [dg, ZMod.natCast_zmod_val]

lemma dg_sub_abs [NeZero p] {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p)
    (j : ℕ) : |(dg A v j : ℤ) - dg A w j| < p := by
  have h1 := dg_lt A v j
  have h2 := dg_lt A w j
  rw [abs_lt]; constructor <;> omega

/-- Own case: the tail digits agree. -/
lemma low_eq_of_own [NeZero p] (hr : r = 1 ∨ r = 2) (R : Rows)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (v w : Fin (3 * k + r) → ZMod p) (c : Fin 3) (hother : ∀ d, d ≠ c → nC r k v d = nC r k w d) :
    low (C c) v (k + 2) = low (C c) w (k + 2) := by
  unfold low
  refine pre_congr p _ _ _ fun j hj => ?_
  have hi : k + 2 + j < 3 * k + r := by omega
  unfold dg
  congr 1
  rw [← sub_eq_zero, row_diff hr _ v w _ hi]
  refine sum_eq_zero fun d _ => sum_eq_zero fun l hl => ?_
  simp only [mem_range] at hl
  by_cases hd : d = c
  · subst hd
    rw [hC.2.2 d (k + 2 + j) l (by rw [jrow_eq]; omega) hi hl, zero_mul]
  · rw [vz_eq_of_nC_eq v w d (hother d hd) l hl, sub_self, mul_zero]

lemma nC_eq_of_cen_zero [NeZero p] (v w : Fin (3 * k + r) → ZMod p) (d : Fin 3)
    (h : cen (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d) = 0) : nC r k v d = nC r k w d := by
  obtain ⟨z, hz⟩ := cen_spec (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d)
  rw [h, zero_add] at hz
  exact eq_of_sub_eq_mul _ _ _ (nC_lt v d) (nC_lt w d) z (by exact_mod_cast hz)

/-- **Near bound** for one coordinate. -/
theorem near_term (hr : r = 1 ∨ r = 2) (hk : 2 ≤ k) (hp : 2 ≤ p) (R : Rows) (Rg : Fin 3 → ℕ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (v w : Fin (3 * k + r) → ZMod p) (δ : Fin 3 → ℤ)
    (hδ : ∀ d, δ d = cen (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d))
    (hbox : ∀ d, |δ d| ≤ Rg d) (hRp : ∀ d, Rg d < p) (hRs : ∀ d : Fin 3, r ≤ (d : ℕ) → Rg d = 1)
    (ch : Fin 3 → ℕ) (hch : ∀ d, ch d < min (depth r k d) (win r d))
    (hD : ∀ d : Fin 3, ∀ l < depth r k d, depth r k d - 1 - l < win r d →
      vz v (off r k d + l) - vz w (off r k d + l) = ((pat (δ d) (ch d) (depth r k d - 1 - l) : ℤ) : ZMod p))
    (c : Fin 3) :
    haveI : NeZero p := ⟨by omega⟩
    ((term ⟨p, r, Rg, R⟩ δ ch c : ℕ) : ℤ) * ((p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) ≤
      (cres (p ^ (3 * k + r)) ((coord p (3 * k + r) (C c) v : ℤ) - coord p (3 * k + r) (C c) w) : ℤ) := by
  haveI : NeZero p := ⟨by omega⟩
  set u := p ^ (3 * k + r - (k + 2)) with hu
  have hu0 : 0 < u := by positivity
  have hN : p ^ (3 * k + r) = p ^ (k + 2) * u := by rw [hu, ← pow_add]; congr 1; omega
  have hP4 : 4 * p ^ 2 ≤ p ^ (k + 2) := by
    rw [pow_add]
    have : 4 ≤ p ^ k := by
      calc 4 ≤ 2 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
        _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
    exact Nat.mul_le_mul_right _ this
  have hP4' : (4 : ℤ) * (p : ℤ) ^ 2 ≤ ((p ^ (k + 2) : ℕ) : ℤ) := by exact_mod_cast hP4
  -- slack
  set sl : ℤ := if isOwn δ c then 0 else 1 with hsl
  have hsl01 : sl = 0 ∨ sl = 1 := by rw [hsl]; split_ifs <;> simp
  set e : ℤ := (low (C c) v (k + 2) : ℤ) - low (C c) w (k + 2) with he
  have heE : |e| ≤ sl * ((u : ℤ) - 1) := by
    by_cases hown : isOwn δ c = true
    · have : sl = 0 := by rw [hsl, if_pos hown]
      rw [this, zero_mul, he, low_eq_of_own hr R C hC v w c (fun d hd => nC_eq_of_cen_zero v w d
        (by rw [← hδ d]; exact isOwn_spec δ c hown d hd))]
      simp
    · have : sl = 1 := by rw [hsl, if_neg hown]
      rw [this, one_mul]
      exact low_diff (C c) v w (k + 2)
  have hcr0 : (0 : ℤ) ≤ (cres (p ^ (3 * k + r)) ((coord p (3 * k + r) (C c) v : ℤ) -
      coord p (3 * k + r) (C c) w) : ℤ) := by positivity
  -- jitter row
  set x : ℤ := (dg (C c) v (k + 1) : ℤ) - dg (C c) w (k + 1) with hx
  have hxa : |x| < p := dg_sub_abs _ v w _
  have hxm : (x : ZMod p) = ((linC (R.jt c) δ ch : ℤ) : ZMod p) := by
    rw [hx, natCast_dg_sub]
    refine designed_row_diff hr (C c) (R.jt c) v w (k + 1) (by omega) (fun d l hl => ?_) δ ch hch hD
    have := hC.2.1 c d l hl
    rwa [jrow_eq] at this
  have hδc : |δ c| ≤ (p : ℤ) - 1 := by have := hbox c; have := hRp c; omega
  have hxa' := abs_lt.mp hxa
  have hfin : ∀ B : ℤ, ∀ z : ℤ, 2 * |B| ≤ ((p ^ (k + 2) : ℕ) : ℤ) →
      ((coord p (3 * k + r) (C c) v : ℤ) - coord p (3 * k + r) (C c) w) =
        B * (u : ℤ) + e + z * ((p ^ (k + 2) * u : ℕ) : ℤ) →
      term ⟨p, r, Rg, R⟩ δ ch c ≤ tv B sl →
      ((term ⟨p, r, Rg, R⟩ δ ch c : ℕ) : ℤ) * u ≤
        (cres (p ^ (3 * k + r)) ((coord p (3 * k + r) (C c) v : ℤ) -
          coord p (3 * k + r) (C c) w) : ℤ) := by
    intro B z hB2 hz hterm
    have hcl := cres_lower (p ^ (k + 2)) u (by positivity) hu0 B e z _ hB2 heE
    rw [← hz, ← hN] at hcl
    have h1 : ((term ⟨p, r, Rg, R⟩ δ ch c : ℕ) : ℤ) ≤ ((tv B sl : ℕ) : ℤ) := by
      exact_mod_cast hterm
    exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) (tv_mul_le B sl hsl01 u _ hcl hcr0)
  by_cases hc : (c : ℕ) < r
  · -- full coordinate
    obtain ⟨z, hz⟩ := near_full hr R.sk C hC.1 v w c hc (by omega)
    rw [← hδ c] at hz
    refine hfin (δ c * p + x) z ?_ hz ?_
    · have h1 : |δ c * p + x| ≤ |δ c| * p + |x| := by
        calc |δ c * p + x| ≤ |δ c * p| + |x| := abs_add_le _ _
          _ = |δ c| * p + |x| := by rw [abs_mul, Nat.abs_cast]
      nlinarith [abs_nonneg (δ c), abs_nonneg x]
    · have hf : (⟨p, r, Rg, R⟩ : Design).full c = true := by simp [Design.full, hc]
      have := term_full_le ⟨p, r, Rg, R⟩ (by simp; omega) δ ch c hf x hxa hxm
      rw [show (p : ℤ) * δ c + x = δ c * p + x by ring] at this
      exact this
  · -- skeleton coordinate
    have hc' : r ≤ (c : ℕ) := by omega
    have hdk : depth r k c = k := by unfold depth; rw [if_neg hc]
    obtain ⟨z, hz⟩ := near_skel hr R.sk C hC.1 v w c hc' (by omega)
    rw [← hδ c] at hz
    have hya : |(dg (C c) v k : ℤ) - dg (C c) w k| < p := dg_sub_abs _ v w _
    have hym : (((dg (C c) v k : ℤ) - dg (C c) w k : ℤ) : ZMod p) =
        ((linC (R.sk c) δ ch : ℤ) : ZMod p) := by
      rw [natCast_dg_sub]
      refine designed_row_diff hr (C c) (R.sk c) v w k (by omega) (fun d l hl => ?_) δ ch hch hD
      have := hC.1.2 c d hc' l hl
      rwa [hdk] at this
    have hδ1 : |δ c| ≤ 1 := by have := hbox c; rw [hRs c hc'] at this; exact_mod_cast this
    refine hfin ((δ c * p + ((dg (C c) v k : ℤ) - dg (C c) w k)) * p + x) z ?_ hz ?_
    · generalize hy : (dg (C c) v k : ℤ) - dg (C c) w k = y at hya
      have hya' := abs_lt.mp hya
      have h1 : |(δ c * p + y) * p + x| ≤ (|δ c| * p + |y|) * p + |x| := by
        calc |(δ c * p + y) * p + x| ≤ |(δ c * p + y) * p| + |x| := abs_add_le _ _
          _ = |δ c * p + y| * p + |x| := by rw [abs_mul, Nat.abs_cast]
          _ ≤ (|δ c * p| + |y|) * p + |x| := by
              have := abs_add_le (δ c * p) y
              have hp0 : (0 : ℤ) ≤ p := by positivity
              have := mul_le_mul_of_nonneg_right this hp0
              linarith
          _ = (|δ c| * p + |y|) * p + |x| := by rw [abs_mul, Nat.abs_cast]
      have hya2 : |y| ≤ (p : ℤ) - 1 := by omega
      have hxa2 : |x| ≤ (p : ℤ) - 1 := by omega
      have h2 : (|δ c| * p + |y|) * p ≤ (2 * (p : ℤ) - 1) * p := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hp0 : (0 : ℤ) ≤ p := by positivity
        have := mul_le_mul_of_nonneg_right hδ1 hp0
        linarith
      have h3 : (2 * (p : ℤ) - 1) * p = 2 * (p : ℤ) ^ 2 - p := by ring
      linarith
    · have hf : (⟨p, r, Rg, R⟩ : Design).full c = false := by simp [Design.full, hc]
      have := term_skel_le ⟨p, r, Rg, R⟩ (by simp; omega) δ ch c hf x _ hxa hxm hya hym
      rw [show (p : ℤ) * ((p : ℤ) * δ c + ((dg (C c) v k : ℤ) - dg (C c) w k)) + x =
        (δ c * p + ((dg (C c) v k : ℤ) - dg (C c) w k)) * p + x by ring] at this
      exact this

end Z3NetKN.Geom

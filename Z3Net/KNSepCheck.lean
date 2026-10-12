module
public import Mathlib
public import Z3Net.KNRelax

@[expose] public section

/-!
# KN separation, part 4: soundness of the finite enumeration `checkAll` and of `sideOK`,
and the elementary wrap-option lemmas for `tvJ` / `term`.
-/

namespace Z3NetKN.Relax

lemma mem_steps (R : ℕ) (x : ℤ) (h1 : -(R : ℤ) ≤ x) (h2 : x ≤ R) : x ∈ steps R := by
  simp [steps]
  exact ⟨(x + R).toNat, by omega, by omega⟩

lemma mem_chains (L : ℕ) (d : ℤ) (ch : ℕ) (h0 : d = 0 → ch = 0) (h1 : ch < L) : ch ∈ chains L d := by
  unfold chains
  split_ifs with h
  · simp [h0 h]
  · exact List.mem_range.mpr h1

lemma vec3_eq {α : Type*} (f : Fin 3 → α) : f = ![f 0, f 1, f 2] := by
  ext i; fin_cases i <;> rfl

/-- Soundness of the enumeration. -/
theorem checkAll_sound (D : Design) (T : ℕ) (h : checkAll D T = true) (dl : Fin 3 → ℤ)
    (ch : Fin 3 → ℕ) (hdl : ∀ c, -(D.R c : ℤ) ≤ dl c ∧ dl c ≤ D.R c)
    (hch : ∀ c, ch c ∈ chains (D.L c) (dl c)) (hne : ¬(dl 0 = 0 ∧ dl 1 = 0 ∧ dl 2 = 0)) :
    T ≤ total D dl ch := by
  unfold checkAll at h
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  have := h (dl 0) (mem_steps _ _ (hdl 0).1 (hdl 0).2) (dl 1) (mem_steps _ _ (hdl 1).1 (hdl 1).2)
    (dl 2) (mem_steps _ _ (hdl 2).1 (hdl 2).2)
  rcases this with h0 | h0
  · exact absurd ⟨h0.1.1, h0.1.2, h0.2⟩ hne
  · have := h0 (ch 0) (hch 0) (ch 1) (hch 1) (ch 2) (hch 2)
    rwa [← vec3_eq dl, ← vec3_eq ch] at this

/-- Soundness of the side conditions. -/
theorem sideOK_sound (D : Design) (T : ℕ) (h : sideOK D T = true) (c : Fin 3) :
    D.R c < D.p ∧ 1 ≤ D.L c ∧ D.L c ≤ 4 ∧ (D.full c = true → T ≤ (D.p * D.R c) ^ 2) ∧
      (D.full c = false → D.R c = 1 ∧ T ≤ (D.p * D.p) ^ 2) := by
  unfold sideOK at h
  rw [List.all_eq_true] at h
  have := h c (List.mem_finRange c)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
  refine ⟨h1, h2, h3, fun hf => ?_, fun hf => ?_⟩
  · rcases h4 with h4 | h4
    · rw [hf] at h4; exact absurd h4 (by decide)
    · exact h4
  · rcases h5 with h5 | h5
    · rw [hf] at h5; exact absurd h5 (by decide)
    · exact h5

/-! ## Wrap options -/

/-- A residue `x ∈ (-p, p)` with `x ≡ lin (mod p)` is `lin % p` or `lin % p - p`
(and `0` when `lin % p = 0`). -/
lemma wrap_cases (p : ℕ) (hp : 0 < p) (x lin : ℤ) (hx : |x| < p)
    (hmod : (x : ZMod p) = (lin : ZMod p)) :
    (lin % p = 0 → x = 0) ∧ (x = lin % p ∨ x = lin % p - p) := by
  have h0 := Int.emod_nonneg lin (show (p : ℤ) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos lin (show (0 : ℤ) < p by omega)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hmod
  obtain ⟨t, ht⟩ := hmod
  have hd := Int.mul_ediv_add_emod lin (p : ℤ)
  -- x = lin % p + p * s
  have e : x = lin % p + p * (lin / p - t) := by linarith
  have hx1 := abs_lt.mp hx
  have hs : lin / p - t = 0 ∨ lin / p - t = -1 := by
    rcases lt_trichotomy (lin / p - t) 0 with hs | hs | hs
    · right
      by_contra hne
      have : lin / p - t ≤ -2 := by omega
      have : (p : ℤ) * (lin / p - t) ≤ -2 * p := by nlinarith
      omega
    · left; exact hs
    · exfalso
      have : (p : ℤ) * 1 ≤ p * (lin / p - t) := by nlinarith
      omega
  constructor
  · intro hz
    rcases hs with hs | hs
    · rw [e, hs, hz]; ring
    · exfalso; rw [hs, hz] at e; omega
  · rcases hs with hs | hs
    · left; rw [e, hs]; ring
    · right; rw [e, hs]; ring

lemma tvJ_le (p : ℕ) (hp : 0 < p) (b x lin sl : ℤ) (hx : |x| < p)
    (hmod : (x : ZMod p) = (lin : ZMod p)) : tvJ p b (lin % p) sl ≤ tv (b + x) sl := by
  obtain ⟨hz, hc⟩ := wrap_cases p hp x lin hx hmod
  unfold tvJ
  split_ifs with h
  · rw [hz h, add_zero]
  · rcases hc with hc | hc
    · rw [hc]; exact min_le_left _ _
    · rw [hc, ← add_sub_assoc]; exact min_le_right _ _

/-- `term` of a full coordinate is at most the actual relaxed distance. -/
lemma term_full_le (D : Design) (hp : 0 < D.p) (dl : Fin 3 → ℤ) (ch : Fin 3 → ℕ) (c : Fin 3)
    (hf : D.full c = true) (x : ℤ) (hx : |x| < D.p)
    (hxm : (x : ZMod D.p) = ((linC (D.rows.jt c) dl ch : ℤ) : ZMod D.p)) :
    term D dl ch c ≤ tv (D.p * dl c + x) (if isOwn dl c then 0 else 1) := by
  unfold term
  simp only [hf, if_true]
  exact tvJ_le D.p hp _ x _ _ hx hxm

/-- `term` of a skeleton coordinate is at most the actual relaxed distance. -/
lemma term_skel_le (D : Design) (hp : 0 < D.p) (dl : Fin 3 → ℤ) (ch : Fin 3 → ℕ) (c : Fin 3)
    (hf : D.full c = false) (x y : ℤ) (hx : |x| < D.p)
    (hxm : (x : ZMod D.p) = ((linC (D.rows.jt c) dl ch : ℤ) : ZMod D.p)) (hy : |y| < D.p)
    (hym : (y : ZMod D.p) = ((linC (D.rows.sk c) dl ch : ℤ) : ZMod D.p)) :
    term D dl ch c ≤ tv (D.p * (D.p * dl c + y) + x) (if isOwn dl c then 0 else 1) := by
  obtain ⟨hz0, hcases⟩ := wrap_cases D.p hp y _ hy hym
  have key := tvJ_le D.p hp (D.p * (D.p * dl c + y)) x _ (if isOwn dl c then 0 else 1) hx hxm
  unfold term
  simp only [hf, Bool.false_eq_true, if_false]
  by_cases h0 : linC (D.rows.sk c) dl ch % (D.p : ℤ) = 0
  · rw [if_pos h0]; rw [hz0 h0, add_zero] at key ⊢; exact key
  · rw [if_neg h0]
    rcases hcases with h | h
    · rw [h] at key ⊢; exact le_trans (min_le_left _ _) key
    · rw [h, ← add_sub_assoc] at key ⊢; exact le_trans (min_le_right _ _) key

end Z3NetKN.Relax

/-
Proof module of entry T3S4 (`prop:t3s4`, `tab:t3s4`): the kernel-evaluable checks and their soundness.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.T3S4Defs

@[expose] public section

/-!
# Entry T3S4: the checks

* `chk D`: the relaxation of the proof of `prop:t3s4`, enumerated exhaustively: all `a_x ∈ [0, p/2)`
  (the case `a_x < 0` follows by the symmetry `(a, ξ) ↦ (-a, -ξ)`), all prefix patterns of `x` with
  `σ_x ≥ 0` and all patterns of the `z_i`, the centred `a_{z_i}`; every consistent nonzero solution
  must have `|a|_∞ ≥ M_p`. `chk_sound`: then every nonzero solution of `T3Rel` has `|a|_∞ ≥ M_p`.
* `latchk D`: every `x ∈ [1, p/2)` has `max(|x|, |cen(κ_i x)|) ≥ λ_∞`; `latchk_sound`.
* `wchk D W`: the frame-orbit conditions of the reachability proof, as integer congruences modulo
  `p` (row scalars `lam`, column gauges `ux` (column `x`, `x`-indices `0, 1, 2`) and `uz j` (column
  `z_j`, `x`-indices `0, 1`)); `smallOK D W`: `wchk`, the attaining relaxation solution and lattice
  vector, `latchk`, `2 M_p ≤ p + 1`, `2 λ_∞ ≤ p + 1`, and the integer forms of the printed
  truncations of `tab:t3s4` (`tab⁴ p³ ≤ (M_p - 1)⁴ 10¹² < (tab + 1)⁴ p³`).
-/

namespace Z3NetF.Proofs.T3

open Finset

/-- Witness data of a design (see `Z3Net/T3Wit.lean`). -/
structure Wit where
  lam : Fin 3 → ℤ
  ux : Fin 3 → Fin 3 → ℤ
  uz : Fin 3 → Fin 2 → Fin 2 → ℤ
  a : Fin 4 → ℤ
  ξ1 : Fin 4 → ℤ
  ξ2 : Fin 4 → ℤ
  u : Fin 4 → ℤ

/-- Centred residue modulo `p` (representative in `(-p/2, p/2]`). -/
def cen (p : ℕ) (v : ℤ) : ℤ := if 2 * (v % (p : ℤ)) < p then v % (p : ℤ) else v % (p : ℤ) - p

/-- Sign-consistent prefix pattern `(ξ1, ξ2) ∈ {(0,0), (σ,0), (σ,σ)}`, `σ = sgn a`. -/
def patOK (a x1 x2 : ℤ) : Bool :=
  (x1 == 0 || x1 == a.sign) && (x2 == 0 || x2 == a.sign) && (x2 == 0 || x1 != 0)

/-- Contribution of `z_j` to the congruence of `a_{z_i}`. -/
def zt (D : T3Design) (i j : Fin 3) (z1 z2 : ℤ) : ℤ :=
  if j = i then D.o i * z1 else D.g i j * z1 + D.H i j * z2

/-- Right-hand side of the congruence of `a_{z_i}`. -/
def rhsZ (D : T3Design) (i : Fin 3) (ax : ℤ) (xp z0 z1 z2 : ℤ × ℤ) : ℤ :=
  D.κ i * ax + D.β i * xp.1 + D.η i * xp.2 + zt D i 0 z0.1 z0.2 + zt D i 1 z1.1 z1.2 +
    zt D i 2 z2.1 z2.2

/-- One case of the enumeration. -/
def caseOK (D : T3Design) (ax : ℤ) (xp z0 z1 z2 : ℤ × ℤ) : Bool :=
  let b0 := cen D.p (rhsZ D 0 ax xp z0 z1 z2)
  let b1 := cen D.p (rhsZ D 1 ax xp z0 z1 z2)
  let b2 := cen D.p (rhsZ D 2 ax xp z0 z1 z2)
  !(patOK ax xp.1 xp.2 && patOK b0 z0.1 z0.2 && patOK b1 z1.1 z1.2 && patOK b2 z2.1 z2.2) ||
    (ax == 0 && b0 == 0 && b1 == 0 && b2 == 0) ||
    decide ((D.M : ℤ) ≤ max (max |ax| |b0|) (max |b1| |b2|))

/-- All five prefix patterns. -/
def pats5 : List (ℤ × ℤ) := [(0, 0), (1, 0), (1, 1), (-1, 0), (-1, -1)]

/-- The prefix patterns with `σ ≥ 0`. -/
def pats3 : List (ℤ × ℤ) := [(0, 0), (1, 0), (1, 1)]

/-- The relaxation certificate. -/
def chk (D : T3Design) : Bool :=
  (List.range ((D.p + 1) / 2)).all fun n => pats3.all fun xp => pats5.all fun z0 =>
    pats5.all fun z1 => pats5.all fun z2 => caseOK D (n : ℤ) xp z0 z1 z2

/-- The Korobov lattice certificate. -/
def latchk (D : T3Design) : Bool :=
  (List.range ((D.p + 1) / 2)).all fun n => n == 0 ||
    decide ((D.lat : ℤ) ≤ max (max |(n : ℤ)| |cen D.p (D.κ 0 * n)|)
      (max |cen D.p (D.κ 1 * n)| |cen D.p (D.κ 2 * n)|))

/-- The places `(0, 1, a3)` of `z` as integers. -/
def plZ (D : T3Design) (i : Fin 3) : ℤ := ![0, 1, (D.a3 : ℤ)] i

/-- `F_n` on the column `x` (`x`-index `n`): `κ, β, η`. -/
def fxZ (D : T3Design) (n : Fin 3) (i : Fin 3) : ℤ := ![D.κ i, D.β i, D.η i] n

/-- `F_n` on the column `z_j` (`x`-index `n`): `g, H`. -/
def fzZ (D : T3Design) (n : Fin 2) (i j : Fin 3) : ℤ := ![D.g i j, D.H i j] n

/-- The frame-orbit conditions, modulo `p`. -/
def wchk (D : T3Design) (W : Wit) : Bool :=
  let p : ℤ := D.p
  (D.a3 : ℤ) % p != 0 && ((D.a3 : ℤ) - 1) % p != 0 &&
  (List.finRange 3).all (fun i => W.lam i % p != 0) &&
  (List.finRange 3).all (fun n => W.ux n n % p != 0) &&
  (List.finRange 3).all (fun j => (List.finRange 2).all fun n => W.uz j n n % p != 0) &&
  (List.finRange 3).all (fun i => (List.finRange 3).all fun n =>
    (fxZ D n i - W.lam i * ∑ n' ∈ univ.filter (fun n' : Fin 3 => n' ≤ n),
      plZ D i ^ (n' : ℕ) * W.ux n' n) % p == 0) &&
  (List.finRange 3).all (fun i => (List.finRange 3).all fun j => i == j ||
    (List.finRange 2).all fun n =>
      (fzZ D n i j * (plZ D i - plZ D j) ^ ((n : ℕ) + 1) - W.lam i *
        ∑ n' ∈ univ.filter (fun n' : Fin 2 => n' ≤ n),
          (plZ D i - plZ D j) ^ ((n : ℕ) - (n' : ℕ)) * W.uz j n' n) % p == 0)

/-- The relaxation, as a Boolean (for the attaining witness). -/
def relB (D : T3Design) (a ξ1 ξ2 : Fin 4 → ℤ) : Bool :=
  (List.finRange 4).all (fun c => decide (2 * |a c| < D.p) && patOK (a c) (ξ1 c) (ξ2 c)) &&
  (List.finRange 3).all fun i =>
    (a i.succ - rhsZ D i (a 0) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1) (ξ1 2, ξ2 2) (ξ1 3, ξ2 3)) % (D.p : ℤ) == 0

/-- The Korobov lattice, as a Boolean. -/
def latB (D : T3Design) (u : Fin 4 → ℤ) : Bool :=
  (List.finRange 3).all fun i => (u i.succ - D.κ i * u 0) % (D.p : ℤ) == 0

/-- All cheap checks of a design. -/
def smallOK (D : T3Design) (W : Wit) : Bool :=
  wchk D W && relB D W.a W.ξ1 W.ξ2 && decide (W.a ≠ 0) && decide (t3MaxAbs W.a = D.M) &&
    latB D W.u && decide (W.u ≠ 0) && decide (t3MaxAbs W.u = D.lat) && latchk D &&
    decide (2 * D.M ≤ D.p + 1) && decide (2 * D.lat ≤ D.p + 1) && decide (0 < D.p) &&
    decide (D.tab ^ 4 * D.p ^ 3 ≤ (D.M - 1) ^ 4 * 10 ^ 12) &&
    decide ((D.M - 1) ^ 4 * 10 ^ 12 < (D.tab + 1) ^ 4 * D.p ^ 3) && decide (D.lat ≤ D.M + 2) &&
    decide (1 ≤ D.M) && decide (7 ≤ D.p → 2 ≤ D.M) && decide (23 ≤ D.p → 180 ≤ D.tab)

/-! ## Soundness -/

lemma cen_eq (p : ℕ) (hp : 0 < p) (a v : ℤ) (ha : 2 * |a| < p) (hd : (p : ℤ) ∣ a - v) :
    cen p v = a := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hmod : v % (p : ℤ) = a % (p : ℤ) := (Int.modEq_iff_dvd.mpr hd).eq
  unfold cen
  rw [hmod]
  rcases abs_cases a with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at ha
    rw [Int.emod_eq_of_lt h2 (by omega), if_pos (by omega)]
  · rw [h1] at ha
    have e : a % (p : ℤ) = a + p := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [e, if_neg (by omega)]
    ring

lemma cen_zero (p : ℕ) (_hp : 0 < p) : cen p 0 = 0 := by
  unfold cen; simp

lemma patOK_iff (a x1 x2 : ℤ) : patOK a x1 x2 = true ↔
    (x1 = 0 ∨ x1 = a.sign) ∧ (x2 = 0 ∨ x2 = a.sign) ∧ (x2 ≠ 0 → x1 ≠ 0) := by
  simp only [patOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  tauto

lemma sign_cases' (a : ℤ) : a.sign = -1 ∧ a < 0 ∨ a.sign = 0 ∧ a = 0 ∨ a.sign = 1 ∧ 0 < a := by
  rcases lt_trichotomy a 0 with h | h | h
  · exact Or.inl ⟨Int.sign_eq_neg_one_of_neg h, h⟩
  · exact Or.inr (Or.inl ⟨by simp [h], h⟩)
  · exact Or.inr (Or.inr ⟨Int.sign_eq_one_of_pos h, h⟩)

lemma mem_pats5 (a x1 x2 : ℤ) (h1 : x1 = 0 ∨ x1 = a.sign) (h2 : x2 = 0 ∨ x2 = a.sign)
    (h3 : x2 ≠ 0 → x1 ≠ 0) : (x1, x2) ∈ pats5 := by
  have hs := sign_cases' a
  simp only [pats5, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

lemma mem_pats3 (a x1 x2 : ℤ) (ha : 0 ≤ a) (h1 : x1 = 0 ∨ x1 = a.sign) (h2 : x2 = 0 ∨ x2 = a.sign)
    (h3 : x2 ≠ 0 → x1 ≠ 0) : (x1, x2) ∈ pats3 := by
  have hs := sign_cases' a
  simp only [pats3, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

lemma le_maxAbs (u : Fin 4 → ℤ) (c : Fin 4) : |u c| ≤ t3MaxAbs u := by
  unfold t3MaxAbs
  fin_cases c <;> simp

lemma maxAbs_neg (u : Fin 4 → ℤ) : t3MaxAbs (-u) = t3MaxAbs u := by
  simp [t3MaxAbs, abs_neg]

lemma rhs_eq (D : T3Design) (a ξ1 ξ2 : Fin 4 → ℤ) (i : Fin 3) :
    rhsZ D i (a 0) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1) (ξ1 2, ξ2 2) (ξ1 3, ξ2 3) =
      D.κ i * a 0 + D.β i * ξ1 0 + D.η i * ξ2 0 +
        ∑ j : Fin 3, (if j = i then D.o i * ξ1 j.succ else D.g i j * ξ1 j.succ + D.H i j * ξ2 j.succ) := by
  rw [Fin.sum_univ_three]
  have e3 : (2 : Fin 3).succ = 3 := rfl
  simp only [rhsZ, zt, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, e3]
  ring

lemma rel_neg (D : T3Design) (a ξ1 ξ2 : Fin 4 → ℤ) (h : T3Rel D a ξ1 ξ2) :
    T3Rel D (-a) (-ξ1) (-ξ2) := by
  obtain ⟨hA, hP, hE⟩ := h
  refine ⟨fun c => by simpa [abs_neg] using hA c, fun c => ?_, fun i => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hP c
    simp only [Pi.neg_apply, Int.sign_neg, neg_eq_zero, neg_inj, ne_eq]
    exact ⟨h1, h2, h3⟩
  · have key : ∀ j : Fin 3, (if j = i then D.o i * (-ξ1) j.succ
        else D.g i j * (-ξ1) j.succ + D.H i j * (-ξ2) j.succ) =
        -(if j = i then D.o i * ξ1 j.succ else D.g i j * ξ1 j.succ + D.H i j * ξ2 j.succ) := by
      intro j; simp only [Pi.neg_apply]; split_ifs <;> ring
    simp only [key, Finset.sum_neg_distrib]
    have := (hE i).neg_right
    convert this using 1
    simp only [Pi.neg_apply]
    ring

/-- `chk` bounds every nonzero relaxation solution with `a_x ≥ 0`. -/
lemma chk_sound_pos (D : T3Design) (hp : 0 < D.p) (h : chk D = true) (a ξ1 ξ2 : Fin 4 → ℤ)
    (hR : T3Rel D a ξ1 ξ2) (ha : a ≠ 0) (h0 : 0 ≤ a 0) : (D.M : ℤ) ≤ t3MaxAbs a := by
  obtain ⟨hA, hP, hE⟩ := hR
  set n := (a 0).toNat with hndef
  have hn : (n : ℤ) = a 0 := Int.toNat_of_nonneg h0
  have hnr : n ∈ List.range ((D.p + 1) / 2) := by
    rw [List.mem_range]
    have := hA 0
    rw [abs_of_nonneg h0] at this
    omega
  have hx : (ξ1 0, ξ2 0) ∈ pats3 := mem_pats3 (a 0) _ _ h0 (hP 0).1 (hP 0).2.1 (hP 0).2.2
  have hz : ∀ c, (ξ1 c, ξ2 c) ∈ pats5 := fun c => mem_pats5 (a c) _ _ (hP c).1 (hP c).2.1 (hP c).2.2
  have hc : caseOK D (n : ℤ) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1) (ξ1 2, ξ2 2) (ξ1 3, ξ2 3) = true := by
    simp only [chk, List.all_eq_true] at h
    exact h n hnr _ hx _ (hz 1) _ (hz 2) _ (hz 3)
  have hb : ∀ i : Fin 3, cen D.p (rhsZ D i (n : ℤ) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1) (ξ1 2, ξ2 2)
      (ξ1 3, ξ2 3)) = a i.succ := by
    intro i
    rw [hn, rhs_eq]
    exact cen_eq D.p hp _ _ (hA i.succ) (hE i)
  have hpat : ∀ c, patOK (a c) (ξ1 c) (ξ2 c) = true := fun c => (patOK_iff _ _ _).mpr (hP c)
  simp only [caseOK, hb 0, hb 1, hb 2] at hc
  have e1 : (0 : Fin 3).succ = 1 := rfl
  have e2 : (1 : Fin 3).succ = 2 := rfl
  have e3 : (2 : Fin 3).succ = 3 := rfl
  rw [e1, e2, e3, hn, hpat 0, hpat 1, hpat 2, hpat 3] at hc
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨h0', h1⟩, h2⟩, h3⟩ | hc
  · exfalso; apply ha
    funext c; fin_cases c
    · exact h0'
    · exact h1
    · exact h2
    · exact h3
  · exact hc

/-- **Soundness of `chk`**: every nonzero solution of the relaxation has `|a|_∞ ≥ M_p`. -/
theorem chk_sound (D : T3Design) (hp : 0 < D.p) (h : chk D = true) (a ξ1 ξ2 : Fin 4 → ℤ)
    (hR : T3Rel D a ξ1 ξ2) (ha : a ≠ 0) : (D.M : ℤ) ≤ t3MaxAbs a := by
  rcases le_or_gt 0 (a 0) with h0 | h0
  · exact chk_sound_pos D hp h a ξ1 ξ2 hR ha h0
  · have := chk_sound_pos D hp h (-a) (-ξ1) (-ξ2) (rel_neg D a ξ1 ξ2 hR) (neg_ne_zero.mpr ha)
      (by simp only [Pi.neg_apply]; omega)
    rwa [maxAbs_neg] at this

lemma lat_neg (D : T3Design) (u : Fin 4 → ℤ) (h : ∀ i : Fin 3, (D.p : ℤ) ∣ u i.succ - D.κ i * u 0) :
    ∀ i : Fin 3, (D.p : ℤ) ∣ (-u) i.succ - D.κ i * (-u) 0 := by
  intro i
  have := (h i).neg_right
  convert this using 1
  simp only [Pi.neg_apply]; ring

lemma latchk_sound_pos (D : T3Design) (hp : 0 < D.p) (h : latchk D = true) (u : Fin 4 → ℤ)
    (hu : u ≠ 0) (hL : ∀ i : Fin 3, (D.p : ℤ) ∣ u i.succ - D.κ i * u 0)
    (hs : ∀ c, 2 * |u c| < D.p) (h0 : 0 ≤ u 0) : (D.lat : ℤ) ≤ t3MaxAbs u := by
  set n := (u 0).toNat with hndef
  have hn : (n : ℤ) = u 0 := Int.toNat_of_nonneg h0
  have hb : ∀ i : Fin 3, cen D.p (D.κ i * n) = u i.succ := fun i => by
    rw [hn]; exact cen_eq D.p hp _ _ (hs i.succ) (hL i)
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hu
    have hz : ∀ i : Fin 3, u i.succ = 0 := by
      intro i
      have := hb i
      rw [hn0] at this
      simp only [Nat.cast_zero, mul_zero] at this
      rw [← this, cen_zero D.p hp]
    have hu0 : u 0 = 0 := by rw [← hn, hn0]; rfl
    funext c; fin_cases c
    · exact hu0
    · exact hz 0
    · exact hz 1
    · exact hz 2
  have hnr : n ∈ List.range ((D.p + 1) / 2) := by
    rw [List.mem_range]
    have := hs 0
    rw [abs_of_nonneg h0] at this
    omega
  simp only [latchk, List.all_eq_true] at h
  have := h n hnr
  simp only [Bool.or_eq_true, beq_iff_eq, hn0, false_or, decide_eq_true_eq, hb 0, hb 1, hb 2] at this
  rw [hn] at this
  exact this

/-- **Soundness of `latchk`**: every nonzero vector of the Korobov lattice has `|u|_∞ ≥ λ_∞`. -/
theorem latchk_sound (D : T3Design) (hp : 0 < D.p) (h : latchk D = true)
    (h2 : 2 * D.lat ≤ D.p + 1) (u : Fin 4 → ℤ) (hu : u ≠ 0)
    (hL : ∀ i : Fin 3, (D.p : ℤ) ∣ u i.succ - D.κ i * u 0) : (D.lat : ℤ) ≤ t3MaxAbs u := by
  by_cases hbig : ∃ c, (D.p : ℤ) ≤ 2 * |u c|
  · obtain ⟨c, hc⟩ := hbig
    have := le_maxAbs u c
    have h2' : 2 * (D.lat : ℤ) ≤ D.p + 1 := by exact_mod_cast h2
    omega
  push Not at hbig
  rcases le_or_gt 0 (u 0) with h0 | h0
  · exact latchk_sound_pos D hp h u hu hL hbig h0
  · have := latchk_sound_pos D hp h (-u) (neg_ne_zero.mpr hu) (lat_neg D u hL)
      (fun c => by simpa [abs_neg] using hbig c) (by simp only [Pi.neg_apply]; omega)
    rwa [maxAbs_neg] at this

lemma relB_sound (D : T3Design) (a ξ1 ξ2 : Fin 4 → ℤ) (h : relB D a ξ1 ξ2 = true) :
    T3Rel D a ξ1 ξ2 := by
  simp only [relB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun c => (h1 c).1, fun c => (patOK_iff _ _ _).mp (h1 c).2, fun i => ?_⟩
  rw [← rhs_eq]
  exact Int.dvd_of_emod_eq_zero (h2 i)

lemma small_sound (D : T3Design) (W : Wit) (h : smallOK D W = true) :
    wchk D W = true ∧ relB D W.a W.ξ1 W.ξ2 = true ∧ W.a ≠ 0 ∧ t3MaxAbs W.a = D.M ∧
      latB D W.u = true ∧ W.u ≠ 0 ∧ t3MaxAbs W.u = D.lat ∧ latchk D = true ∧
      2 * D.M ≤ D.p + 1 ∧ 2 * D.lat ≤ D.p + 1 ∧ 0 < D.p ∧
      D.tab ^ 4 * D.p ^ 3 ≤ (D.M - 1) ^ 4 * 10 ^ 12 ∧
      (D.M - 1) ^ 4 * 10 ^ 12 < (D.tab + 1) ^ 4 * D.p ^ 3 ∧ D.lat ≤ D.M + 2 ∧ 1 ≤ D.M ∧
      (7 ≤ D.p → 2 ≤ D.M) ∧ (23 ≤ D.p → 180 ≤ D.tab) := by
  simp only [smallOK, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

lemma latB_sound (D : T3Design) (u : Fin 4 → ℤ) (h : latB D u = true) :
    ∀ i : Fin 3, (D.p : ℤ) ∣ u i.succ - D.κ i * u 0 := by
  simp only [latB, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact fun i => Int.dvd_of_emod_eq_zero (h i)

end Z3NetF.Proofs.T3

/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.TDBal

@[expose] public section

/-!
# V14 stage S11′: `thm:D`, the skew layers (hand proof)

Doubled (`G = 2F₀`), with the diagonal lowered to `m` (`G_cc = −m_c`).
* `drift_skew`: for a skew off-diagonal part the cross terms cancel, `2 dr(E) = ∑_{E_c ≠ 0} m_c + ∑_{E_c = 0} |2β_c|`.
* `pair_bound` (the pair `{x, y}` of the printed proof, `S` the other three coordinates): the binding step with
  `E_x = E_y = 0` and `E_S = sgn G[y, S]` has `2 dr(E) ≥ ∑_S m + ‖G[y, S]‖₁ + 1` (`|2β_x| ≥ 1`, being odd).
* `graph_lemma` (kernel `decide` over the `2¹⁰` graphs `G` of the entries `±3`): either two rows have no edge
  outside themselves (which (MIN) excludes: `two_rows`; this covers two light rows and a perfect matching on the
  heavy rows), or some pair has `∑_S m + 2 deg_S(y) ≥ 13` (cases (i), (ii) of the printed proof).
* `skew_drift`: every skew layer with (Half), the minimal diagonal and (MIN) has a binding step with
  `2 dr(E) ≥ 17`; an entry `≥ 5/2` gives `∑ m ≥ 17` directly (with the minor tax).
-/

namespace Z3NetHL.Proofs.TD

open Finset

/-- The off-diagonal part is skew. -/
def SkewOff (G : Fin 5 → Fin 5 → ℤ) : Prop := ∀ c d, c ≠ d → G c d + G d c = 0

lemma dotR_split (G : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) :
    dotR G E c = G c c * E c + ∑ d, (if d = c then 0 else G c d * E d) := by
  have : ∀ d, G c d * E d = (if d = c then G c c * E c else 0) + (if d = c then 0 else G c d * E d) := by
    intro d; split_ifs with h
    · subst h; ring
    · ring
  simp only [dotR]
  rw [sum_congr rfl fun d _ => this d, sum_add_distrib, sum_ite_eq' univ c, if_pos (mem_univ c)]

lemma cross_skew (G : Fin 5 → Fin 5 → ℤ) (hs : SkewOff G) (E : Fin 5 → ℤ) :
    ∑ c, ∑ d, (if d = c then 0 else E c * G c d * E d) = 0 := by
  have h1 := Finset.sum_comm (s := (univ : Finset (Fin 5))) (t := univ)
    (f := fun c d => if d = c then (0 : ℤ) else E c * G c d * E d)
  have h2 : ∑ d, ∑ c, (if d = c then (0 : ℤ) else E c * G c d * E d) =
      -∑ c, ∑ d, (if d = c then 0 else E c * G c d * E d) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun c _ => ?_
    by_cases h : d = c
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
      have := hs d c h
      have e : G c d = -G d c := by linarith
      rw [e]; ring
  linarith

/-- For a skew off-diagonal part and the minimal diagonal, the cross terms cancel. -/
lemma drift_skew (G : Fin 5 → Fin 5 → ℤ) (hs : SkewOff G) (hdiag : ∀ c, G c c = -mrow G c)
    (E : Fin 5 → ℤ) (hE : ∀ c, E c = -1 ∨ E c = 0 ∨ E c = 1) :
    drift2E G E = ∑ c, (if E c = 0 then |dotR G E c| else mrow G c) := by
  have key : ∀ c, drc2 G E c = (if E c = 0 then |dotR G E c| else mrow G c) -
      ∑ d, (if d = c then 0 else E c * G c d * E d) := by
    intro c
    unfold drc2
    split_ifs with h0
    · rw [h0]; simp
    · rw [dotR_split, hdiag c]
      have hsq : E c * E c = 1 := by rcases hE c with h | h | h <;> simp_all
      have : E c * ∑ d, (if d = c then (0 : ℤ) else G c d * E d) =
          ∑ d, (if d = c then 0 else E c * G c d * E d) := by
        rw [mul_sum]; refine sum_congr rfl fun d _ => ?_; split_ifs <;> ring
      rw [← this]
      linear_combination (mrow G c) * hsq
  rw [drift2E, sum_congr rfl fun c _ => key c, sum_sub_distrib, cross_skew G hs E, sub_zero]

/-- The coordinates other than `x`, `y`. -/
def Sxy (x y : Fin 5) : Finset (Fin 5) := univ.filter fun c => c ≠ x ∧ c ≠ y

lemma card_Sxy : ∀ x y : Fin 5, x ≠ y → (Sxy x y).card = 3 := by decide

lemma sum_xyS (f : Fin 5 → ℤ) (x y : Fin 5) (hxy : x ≠ y) :
    ∑ c, f c = f x + f y + ∑ c ∈ Sxy x y, f c := by
  rw [← sum_filter_add_sum_filter_not univ (fun c => c = x ∨ c = y)]
  have e1 : univ.filter (fun c => c = x ∨ c = y) = {x, y} := by
    ext c; simp
  have e2 : univ.filter (fun c => ¬(c = x ∨ c = y)) = Sxy x y := by
    ext c; simp [Sxy, not_or]
  rw [e1, e2, sum_pair hxy]

lemma odd_sum_three (S : Finset (Fin 5)) (hS : S.card = 3) (t : Fin 5 → ℤ) (ht : ∀ d ∈ S, Odd (t d)) :
    Odd (∑ d ∈ S, t d) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  rw [sum_insert (by simp [hab, hac]), sum_pair hbc, ← add_assoc]
  have ha := ht a (by simp); have hb := ht b (by simp); have hc := ht c (by simp)
  exact (ha.add_odd hb).add_odd hc

lemma sign_odd {z : ℤ} (h : Odd z) : z.sign = 1 ∨ z.sign = -1 := by
  rcases lt_trichotomy z 0 with h' | h' | h'
  · exact Or.inr (Int.sign_eq_neg_one_of_neg h')
  · subst h'; exact absurd h (by decide)
  · exact Or.inl (Int.sign_eq_one_of_pos h')

/-- The step of the pair `{x, y}`: `E_x = E_y = 0`, `E_d = sgn G[y][d]` on the other coordinates. -/
def Ep (G : Fin 5 → Fin 5 → ℤ) (x y : Fin 5) (i : Fin 5) : ℤ :=
  if i = x ∨ i = y then 0 else Int.sign (G y i)

/-- **The pair bound** (skew case of `thm:D`). -/
lemma pair_bound (G : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (G c d)) (hs : SkewOff G)
    (hdiag : ∀ c, G c c = -mrow G c) (x y : Fin 5) (hxy : x ≠ y) :
    ∃ E ∈ bind5, ∑ c ∈ Sxy x y, mrow G c + ∑ d ∈ Sxy x y, |G y d| + 1 ≤ drift2E G E := by
  set E := Ep G x y with hEdef
  have hEx : E x = 0 := by simp [hEdef, Ep]
  have hEy : E y = 0 := by simp [hEdef, Ep]
  have hES : ∀ d ∈ Sxy x y, E d = Int.sign (G y d) := by
    intro d hd; simp only [Sxy, mem_filter] at hd; simp [hEdef, Ep, hd.2.1, hd.2.2]
  have hE3 : ∀ c, E c = -1 ∨ E c = 0 ∨ E c = 1 := by
    intro c; simp only [hEdef, Ep]; split_ifs
    · exact Or.inr (Or.inl rfl)
    · rcases sign_odd (hodd y c) with h | h <;> simp [h]
  have hS3 := card_Sxy x y hxy
  -- the sum of `E` is odd
  have hsumE : (∑ d, E d) % 2 = 1 := by
    rw [sum_xyS _ x y hxy, hEx, hEy, zero_add, zero_add]
    have : Odd (∑ d ∈ Sxy x y, E d) := odd_sum_three _ hS3 _ fun d hd => by
      rw [hES d hd]; rcases sign_odd (hodd y d) with h | h <;> rw [h] <;> decide
    obtain ⟨k, hk⟩ := this; omega
  have hEb : E ∈ bind5 := by
    rw [mem_bind5]
    refine ⟨fun d => by rcases hE3 d with h | h | h <;> omega, ?_⟩
    rw [Fin.sum_univ_five] at hsumE; exact hsumE
  refine ⟨E, hEb, ?_⟩
  rw [drift_skew G hs hdiag E hE3, sum_xyS _ x y hxy, if_pos hEx, if_pos hEy]
  have hSm : ∑ c ∈ Sxy x y, (if E c = 0 then |dotR G E c| else mrow G c) = ∑ c ∈ Sxy x y, mrow G c := by
    refine sum_congr rfl fun c hc => ?_
    rw [if_neg]; rw [hES c hc]; rcases sign_odd (hodd y c) with h | h <;> rw [h] <;> decide
  have hy : dotR G E y = ∑ d ∈ Sxy x y, |G y d| := by
    rw [dotR, sum_xyS _ x y hxy, hEx, hEy, mul_zero, mul_zero, zero_add, zero_add]
    refine sum_congr rfl fun d hd => ?_
    rw [hES d hd, Int.mul_sign_self, Int.abs_eq_natAbs]
  have hx : 1 ≤ |dotR G E x| := by
    have : Odd (dotR G E x) := by
      rw [dotR, sum_xyS _ x y hxy, hEx, hEy, mul_zero, mul_zero, zero_add, zero_add]
      refine odd_sum_three _ hS3 _ fun d hd => ?_
      rw [hES d hd]
      rcases sign_odd (hodd y d) with h | h <;> rw [h]
      · simpa using hodd x d
      · simpa using (hodd x d).neg
    exact Int.one_le_abs (by obtain ⟨k, hk⟩ := this; omega)
  have hy0 : 0 ≤ ∑ d ∈ Sxy x y, |G y d| := sum_nonneg fun d _ => abs_nonneg _
  rw [hSm, hy, abs_of_nonneg hy0]
  linarith

/-! ## The graph lemma -/

/-- The graph on five vertices with the edges `b_cd` (symmetric, no loops). -/
def adjB (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) (c d : Fin 5) : Bool :=
  match (c : ℕ), (d : ℕ) with
  | 0, 1 => b01 | 1, 0 => b01 | 0, 2 => b02 | 2, 0 => b02 | 0, 3 => b03 | 3, 0 => b03
  | 0, 4 => b04 | 4, 0 => b04 | 1, 2 => b12 | 2, 1 => b12 | 1, 3 => b13 | 3, 1 => b13
  | 1, 4 => b14 | 4, 1 => b14 | 2, 3 => b23 | 3, 2 => b23 | 2, 4 => b24 | 4, 2 => b24
  | 3, 4 => b34 | 4, 3 => b34 | _, _ => false

/-- `m_c` from the graph: `3/2` (doubled `3`) at a vertex with an edge, `½` at an isolated vertex. -/
def mB (A : Fin 5 → Fin 5 → Bool) (c : Fin 5) : ℤ := if ∃ d, A c d = true then 3 else 1

set_option maxRecDepth 100000 in
/-- **The graph lemma** (cases (i), (ii) of the skew case of `thm:D`; kernel `decide` over all `2¹⁰` graphs). -/
theorem graph_lemma : ∀ b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool,
    (∃ a b : Fin 5, a ≠ b ∧ ∀ d, d ≠ a → d ≠ b →
      adjB b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 a d = false ∧
      adjB b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 b d = false) ∨
    (∃ x y : Fin 5, x ≠ y ∧ 13 ≤ ∑ c ∈ Sxy x y, mB (adjB b01 b02 b03 b04 b12 b13 b14 b23 b24 b34) c +
      2 * (((Sxy x y).filter fun d => adjB b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 y d = true).card : ℤ)) := by
  decide +kernel

/-! ## The skew case -/

lemma abs13 {z : ℤ} (ho : Odd z) (h : |z| < 5) : |z| = 1 ∨ |z| = 3 := by
  obtain ⟨k, hk⟩ := ho
  rcases abs_cases z with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

lemma sum_ge17 (m : Fin 5 → ℤ) (hp : ∀ c, 1 ≤ m c) (ho : ∀ c, m c % 2 = 1)
    (ht : ∀ a b, a ≠ b → m a ≠ 1 ∨ m b ≠ 1) (c d : Fin 5) (hcd : c ≠ d) (hc : 5 ≤ m c) (hd : 5 ≤ m d) :
    17 ≤ ∑ i, m i := by
  rw [Fin.sum_univ_five]
  have p0 := hp 0; have p1 := hp 1; have p2 := hp 2; have p3 := hp 3; have p4 := hp 4
  have o0 := ho 0; have o1 := ho 1; have o2 := ho 2; have o3 := ho 3; have o4 := ho 4
  have t01 := ht 0 1 (by decide); have t02 := ht 0 2 (by decide); have t03 := ht 0 3 (by decide)
  have t04 := ht 0 4 (by decide); have t12 := ht 1 2 (by decide); have t13 := ht 1 3 (by decide)
  have t14 := ht 1 4 (by decide); have t23 := ht 2 3 (by decide); have t24 := ht 2 4 (by decide)
  have t34 := ht 3 4 (by decide)
  fin_cases c <;> fin_cases d <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at * <;>
    first | exact absurd rfl hcd | omega

/-- **The skew case of `thm:D`** (hand proof): a skew layer with (Half), the minimal diagonal and (MIN) has a binding
step with `2 dr(E) ≥ 17`. -/
theorem skew_drift (G : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (G c d)) (hs : SkewOff G)
    (hdiag : ∀ c, G c c = -mrow G c) (hmin : Min2 G) : ∃ E ∈ bind5, 17 ≤ drift2E G E := by
  have habs : ∀ c d, c ≠ d → |G d c| = |G c d| := fun c d h => by
    have := hs c d h; rw [show G d c = -G c d by linarith, abs_neg]
  by_cases hbig : ∃ c d, c ≠ d ∧ 5 ≤ |G c d|
  · -- an entry `≥ 5/2`: `∑ m ≥ 17`, attained on the full step `𝟙`
    obtain ⟨c, d, hcd, h5⟩ := hbig
    have hm : 17 ≤ ∑ i, mrow G i := by
      refine sum_ge17 (mrow G) (mrow_pos G hodd) (fun c => by obtain ⟨k, hk⟩ := mrow_odd G hodd c; omega)
        (fun a b hab => by
          by_contra hc; push Not at hc; exact minor_tax G hodd hmin a b hab hc.1 hc.2) c d hcd
        (h5.trans (le_mrow G c d (Ne.symm hcd))) ?_
      rw [← habs c d hcd] at h5; exact h5.trans (le_mrow G d c hcd)
    refine ⟨fun _ => 1, by rw [mem_bind5]; decide, ?_⟩
    rw [drift_skew G hs hdiag _ (fun _ => Or.inr (Or.inr rfl))]
    simpa using hm
  push Not at hbig
  have h13 : ∀ c d, c ≠ d → |G c d| = 1 ∨ |G c d| = 3 := fun c d h =>
    abs13 (hodd c d) (hbig c d h)
  -- the graph of the entries `±3`
  set A := adjB (decide (|G 0 1| = 3)) (decide (|G 0 2| = 3)) (decide (|G 0 3| = 3)) (decide (|G 0 4| = 3))
    (decide (|G 1 2| = 3)) (decide (|G 1 3| = 3)) (decide (|G 1 4| = 3)) (decide (|G 2 3| = 3))
    (decide (|G 2 4| = 3)) (decide (|G 3 4| = 3)) with hA
  have hAe : ∀ c d, c ≠ d → (A c d = true ↔ |G c d| = 3) := by
    intro c d hcd
    have h10 := habs 0 1 (by decide); have h20 := habs 0 2 (by decide); have h30 := habs 0 3 (by decide)
    have h40 := habs 0 4 (by decide); have h21 := habs 1 2 (by decide); have h31 := habs 1 3 (by decide)
    have h41 := habs 1 4 (by decide); have h32 := habs 2 3 (by decide); have h42 := habs 2 4 (by decide)
    have h43 := habs 3 4 (by decide)
    fin_cases c <;> fin_cases d <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at * <;>
      first | exact absurd rfl hcd | simp [hA, adjB, h10, h20, h30, h40, h21, h31, h41, h32, h42, h43]
  have hAc : ∀ c, A c c = false := by
    intro c; fin_cases c <;> simp [hA, adjB]
  have hmB : ∀ c, mB A c = mrow G c := by
    intro c
    obtain ⟨d0, hd0, he⟩ := mrow_attained G c
    unfold mB
    split_ifs with h
    · obtain ⟨d, hd⟩ := h
      have hdc : d ≠ c := fun e => by rw [e, hAc] at hd; exact absurd hd (by decide)
      have h3 := (hAe c d (Ne.symm hdc)).mp hd
      have := le_mrow G c d hdc
      rcases h13 c d0 (Ne.symm hd0) with h' | h' <;> omega
    · push Not at h
      rcases h13 c d0 (Ne.symm hd0) with h' | h'
      · omega
      · exact absurd ((hAe c d0 (Ne.symm hd0)).mpr h') (h d0)
  rcases graph_lemma (decide (|G 0 1| = 3)) (decide (|G 0 2| = 3)) (decide (|G 0 3| = 3))
      (decide (|G 0 4| = 3)) (decide (|G 1 2| = 3)) (decide (|G 1 3| = 3)) (decide (|G 1 4| = 3))
      (decide (|G 2 3| = 3)) (decide (|G 2 4| = 3)) (decide (|G 3 4| = 3)) with
    ⟨a, b, hab, hno⟩ | ⟨x, y, hxy, h13'⟩
  · -- two rows without an edge outside them: (MIN) fails
    exfalso
    refine two_rows G hmin a b hab fun d hda hdb => ?_
    obtain ⟨ha, hb⟩ := hno d hda hdb
    rw [← hA] at ha hb
    constructor
    · rcases h13 a d (Ne.symm hda) with h | h
      · exact h
      · rw [(hAe a d (Ne.symm hda)).mpr h] at ha; exact absurd ha (by decide)
    · rcases h13 b d (Ne.symm hdb) with h | h
      · exact h
      · rw [(hAe b d (Ne.symm hdb)).mpr h] at hb; exact absurd hb (by decide)
  · obtain ⟨E, hE, hle⟩ := pair_bound G hodd hs hdiag x y hxy
    refine ⟨E, hE, ?_⟩
    rw [← hA] at h13'
    have hm : ∑ c ∈ Sxy x y, mB A c = ∑ c ∈ Sxy x y, mrow G c := sum_congr rfl fun c _ => hmB c
    have hcol : ∑ d ∈ Sxy x y, |G y d| =
        3 + 2 * (((Sxy x y).filter fun d => A y d = true).card : ℤ) := by
      have : ∀ d ∈ Sxy x y, |G y d| = 1 + 2 * (if A y d = true then 1 else 0) := by
        intro d hd
        simp only [Sxy, mem_filter] at hd
        have hdy : y ≠ d := Ne.symm hd.2.2
        by_cases h : A y d = true
        · rw [if_pos h]; have := (hAe y d hdy).mp h; omega
        · rw [if_neg h]
          rcases h13 y d hdy with h' | h'
          · omega
          · exact absurd ((hAe y d hdy).mpr h') h
      rw [sum_congr rfl this, sum_add_distrib, ← mul_sum, sum_boole]
      simp [card_Sxy x y hxy]
    rw [hm] at h13'
    linarith

end Z3NetHL.Proofs.TD

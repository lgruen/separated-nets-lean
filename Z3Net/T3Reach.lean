/-
Proof module of entry T3S4 (`prop:t3s4`, "Reachability").
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.T3Cert
public import Z3Net.SkCompII
public import Z3Net.SkNecBridge

@[expose] public section

/-!
# Entry T3S4: reachability from the frame (`prop:t3s4`)

`reach_of`: if the frame-orbit conditions `wchk D W` hold (places `x = ∞`, `z = (0, 1, a3)`
distinct; row scalars `λ_i`; on the column `x` an upper triangular `3 × 3` gauge `ux` with
`F_n[z_i][x] = λ_i ∑_{n' ≤ n} a_i^(n') ux[n', n]` for the `x`-indices `n = 0, 1, 2` (`F_0 = κ`,
`F_1 = β`, `F_2 = η`); on the column `z_j` an upper triangular `2 × 2` gauge `uz j` with
`F_n[z_i][z_j] (a_i - a_j)^(n+1) = λ_i ∑_{n' ≤ n} (a_i - a_j)^(n - n') uz j [n', n]` for `n = 0, 1`
(`F_0 = g`, `F_1 = H`); all diagonal entries units), then the residual problem of
`prop:skelcomp`(i) on the rows `S = {z_1, z_2, z_3}` is solved (`w = 1`, `y = a_i` on the column
`∞`; `w = y = 1/(a_i - a_j)` on the column `z_j`), and `skel_Gs` (`prop:Gs` on the skeleton rows)
gives the column gauges for every `k ≥ 1`; move (a) sets the own blocks, and
`SkComp.frame_gauge_net` (`lem:box`, `lem:nie`) the net. This is the paper's reachability
argument with the constraints made explicit per design; the witnesses come from
`scripts/t3s4_data.py`.
-/

namespace Z3NetF.Proofs.T3

open Finset Matrix

lemma zcast_eq_zero (p : ℕ) (x : ℤ) (h : x % (p : ℤ) = 0) : (x : ZMod p) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mpr (Int.dvd_of_emod_eq_zero h)

lemma zcast_ne_zero (p : ℕ) (x : ℤ) (h : x % (p : ℤ) ≠ 0) : (x : ZMod p) ≠ 0 := fun h' =>
  h (Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h'))

/-- The frame-orbit conditions in `ZMod p`. -/
structure WOK (D : T3Design) (W : Wit) : Prop where
  a3 : (D.a3 : ZMod D.p) ≠ 0
  a31 : (D.a3 : ZMod D.p) - 1 ≠ 0
  lam : ∀ i, ((W.lam i : ℤ) : ZMod D.p) ≠ 0
  ux : ∀ n, ((W.ux n n : ℤ) : ZMod D.p) ≠ 0
  uz : ∀ j n, ((W.uz j n n : ℤ) : ZMod D.p) ≠ 0
  fx : ∀ i n, ((fxZ D n i : ℤ) : ZMod D.p) = (W.lam i : ZMod D.p) *
    ∑ n' ∈ univ.filter (fun n' : Fin 3 => n' ≤ n), (plZ D i : ZMod D.p) ^ (n' : ℕ) * (W.ux n' n : ZMod D.p)
  fz : ∀ i j, i ≠ j → ∀ n, ((fzZ D n i j : ℤ) : ZMod D.p) *
      ((plZ D i : ZMod D.p) - plZ D j) ^ ((n : ℕ) + 1) = (W.lam i : ZMod D.p) *
    ∑ n' ∈ univ.filter (fun n' : Fin 2 => n' ≤ n),
      ((plZ D i : ZMod D.p) - plZ D j) ^ ((n : ℕ) - (n' : ℕ)) * (W.uz j n' n : ZMod D.p)

lemma wchk_sound (D : T3Design) (W : Wit) (h : wchk D W = true) : WOK D W := by
  simp only [wchk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, bne_iff_ne,
    ne_eq, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨?_, ?_, fun i => zcast_ne_zero _ _ (h3 i),
    fun n => zcast_ne_zero _ _ (h4 n), fun j n => zcast_ne_zero _ _ (h5 j n), fun i n => ?_,
    fun i j hij n => ?_⟩
  · have := zcast_ne_zero _ _ h1; push_cast at this; exact this
  · have := zcast_ne_zero _ _ h2; push_cast at this; exact this
  · have := zcast_eq_zero _ _ (h6 i n)
    push_cast at this
    exact sub_eq_zero.mp this
  · rcases h7 i j with h | h
    · exact absurd h hij
    · have := zcast_eq_zero _ _ (h n)
      push_cast at this
      exact sub_eq_zero.mp this

lemma plZ_cast (D : T3Design) (i : Fin 3) : ((plZ D i : ℤ) : ZMod D.p) = t3Places D i.succ := by
  fin_cases i <;> simp [plZ, t3Places]

lemma places_ne (D : T3Design) (W : Wit) (hp : D.p.Prime) (hw : WOK D W) (i j : Fin 3)
    (hij : i ≠ j) : t3Places D i.succ - t3Places D j.succ ≠ 0 := by
  have : Fact (1 < D.p) := ⟨hp.one_lt⟩
  have h1 : (1 : ZMod D.p) ≠ 0 := one_ne_zero
  have ha := hw.a3
  have ha1 := hw.a31
  have ha1' : (1 : ZMod D.p) - D.a3 ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.mpr ha1
  have h1' : (0 : ZMod D.p) - 1 ≠ 0 := by rw [zero_sub]; exact neg_ne_zero.mpr h1
  have ha' : (0 : ZMod D.p) - D.a3 ≠ 0 := by rw [zero_sub]; exact neg_ne_zero.mpr ha
  have h10 : (1 : ZMod D.p) - 0 ≠ 0 := by rw [sub_zero]; exact h1
  have ha0 : (D.a3 : ZMod D.p) - 0 ≠ 0 := by rw [sub_zero]; exact ha
  have e1 : t3Places D (Fin.succ 0) = 0 := rfl
  have e2 : t3Places D (Fin.succ 1) = 1 := rfl
  have e3 : t3Places D (Fin.succ 2) = D.a3 := rfl
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, e1, e2, e3]; assumption)

lemma placesOK (D : T3Design) (W : Wit) (hp : D.p.Prime) (hw : WOK D W) :
    PlacesOK 0 (t3Places D) := by
  intro c d hc hd hcd
  have : Fact D.p.Prime := ⟨hp⟩
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hc
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hd
  exact isUnit_iff_ne_zero.mpr (places_ne D W hp hw i j (fun h => hcd (by rw [h])))

/-- **Reachability** (`prop:t3s4`) from the frame-orbit conditions. -/
theorem reach_of (D : T3Design) (W : Wit) (hp : D.p.Prime) (hw : WOK D W) :
    PlacesOK 0 (t3Places D) ∧ ∀ k, 1 ≤ k →
      ∃ (L : (c : Fin 4) → Matrix (Fin (4 * k + 1 - skDepth 1 k c))
          (Fin (4 * k + 1 - skDepth 1 k c)) (ZMod D.p))
        (U : (d : Fin 4) → Matrix (Fin (skDepth 1 k d)) (Fin (skDepth 1 k d)) (ZMod D.p))
        (Φ : (c d : Fin 4) → Matrix (Fin (4 * k + 1 - skDepth 1 k c)) (Fin (skDepth 1 k d))
          (ZMod D.p)),
        (∀ c, IsLTU (L c)) ∧ (∀ d, IsLTU (U d)) ∧
        (∀ c d, c ≠ d → Φ c d =
          L c * frameGraphK (ZMod D.p) (4 * k + 1) (skDepth 1 k) 0 (t3Places D) c d * U d) ∧
        (∀ (i : Fin 3) (l : Fin (skDepth 1 k (0 : Fin 4))),
          ent (Φ i.succ 0) 0 l = ((t3xCoef D k i l : ℤ) : ZMod D.p)) ∧
        (∀ (i j : Fin 3) (l : Fin (skDepth 1 k j.succ)),
          ent (Φ i.succ j.succ) 0 l = ((t3zCoef D k i j l : ℤ) : ZMod D.p)) ∧
        IsNet0 4 D.p (4 * k + 1)
          (digPoint D.p (4 * k + 1) (graphGenK (m := 4 * k + 1) (skDepth 1 k) Φ)) := by
  have : Fact D.p.Prime := ⟨hp⟩
  have : NeZero D.p := ⟨hp.ne_zero⟩
  have hx := placesOK D W hp hw
  refine ⟨hx, fun k hk => ?_⟩
  set K : Fin 4 → ℕ := skDepth 1 k with hKdef
  have hK : ∑ c, K c = 4 * k + 1 := SkComp.sum_skDepth' 1 k (by omega)
  have hK0 : K 0 = k + 1 := by simp [hKdef, skDepth]
  have hKs : ∀ j : Fin 3, K j.succ = k := by intro j; simp [hKdef, skDepth]
  set S : Finset (Fin 4) := univ.erase 0 with hSdef
  have hS : ∀ c, c ∈ S ↔ c ≠ 0 := by simp [hSdef]
  have hcard0 : (S.erase 0).card = 3 := by simp [hSdef]
  have hcardj : ∀ j : Fin 3, (S.erase j.succ).card = 2 := by
    intro j
    rw [card_erase_of_mem ((hS _).mpr (Fin.succ_ne_zero j))]
    simp [hSdef]
  set lamR : Fin 4 → ZMod D.p := Fin.cases 1 (fun i => (W.lam i : ZMod D.p)) with hlamdef
  have hlamU : ∀ c, IsUnit (lamR c) := by
    intro c
    cases c using Fin.cases with
    | zero => simp [hlamdef]
    | succ i => simp only [hlamdef, Fin.cases_succ]; exact isUnit_iff_ne_zero.mpr (hw.lam i)
  set Ur : Fin 4 → ℕ → ℕ → ZMod D.p := fun d n' n => Fin.cases (motive := fun _ => ZMod D.p)
      (if h : n' < 3 ∧ n < 3 ∧ n' ≤ n then (W.ux ⟨n', h.1⟩ ⟨n, h.2.1⟩ : ZMod D.p) else 0)
      (fun j => if h : n' < 2 ∧ n < 2 ∧ n' ≤ n then (W.uz j ⟨n', h.1⟩ ⟨n, h.2.1⟩ : ZMod D.p)
        else 0) d with hUrdef
  set F : ℕ → Fin 4 → Fin 4 → ZMod D.p := fun n c d => Fin.cases (motive := fun _ => ZMod D.p) 0
      (fun i => Fin.cases (motive := fun _ => ZMod D.p)
        (if h : n < 3 then (fxZ D ⟨n, h⟩ i : ZMod D.p) else 0)
        (fun j => if h : n < 2 then (fzZ D ⟨n, h⟩ i j : ZMod D.p) else 0) d) c with hFdef
  have hres : ResidualSk 0 (t3Places D) S F lamR Ur := by
    refine ⟨fun c _ => hlamU c, ?_, ?_, ?_⟩
    · intro d n' n h1 h2
      cases d using Fin.cases with
      | zero => simp only [hUrdef, Fin.cases_zero]; rw [dif_neg (by omega)]
      | succ j => simp only [hUrdef, Fin.cases_succ]; rw [dif_neg (by omega)]
    · intro d n hn
      cases d using Fin.cases with
      | zero =>
        rw [hcard0] at hn
        simp only [hUrdef, Fin.cases_zero]
        rw [dif_pos ⟨hn, hn, le_rfl⟩]
        exact isUnit_iff_ne_zero.mpr (hw.ux ⟨n, hn⟩)
      | succ j =>
        rw [hcardj] at hn
        simp only [hUrdef, Fin.cases_succ]
        rw [dif_pos ⟨hn, hn, le_rfl⟩]
        exact isUnit_iff_ne_zero.mpr (hw.uz j ⟨n, hn⟩)
    · intro c hc d hcd n hn
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr ((hS c).mp hc)
      cases d using Fin.cases with
      | zero =>
        rw [hcard0] at hn
        have hw1 : wN 0 (t3Places D) i.succ 0 = 1 := by simp [wN]
        have hy1 : yN 0 (t3Places D) i.succ 0 = t3Places D i.succ := by simp [yN, Fin.succ_ne_zero]
        have hf := hw.fx i ⟨n, hn⟩
        rw [plZ_cast] at hf
        simp only [hw1, hy1, one_mul, hFdef, hlamdef, Fin.cases_succ, Fin.cases_zero, hUrdef]
        rw [dif_pos hn, hf]
        rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl <;>
          simp [Finset.sum_filter, Fin.sum_univ_three, Finset.sum_range_succ]
      | succ j =>
        have hij : i ≠ j := fun h => hcd (by rw [h])
        rw [hcardj] at hn
        have ht : t3Places D i.succ - t3Places D j.succ ≠ 0 := places_ne D W hp hw i j hij
        have hwz : wN 0 (t3Places D) i.succ j.succ = (t3Places D i.succ - t3Places D j.succ)⁻¹ := by
          simp [wN, Fin.succ_ne_zero, Ring.inverse_eq_inv']
        have hyz : yN 0 (t3Places D) i.succ j.succ = (t3Places D i.succ - t3Places D j.succ)⁻¹ := by
          simp [yN, Fin.succ_ne_zero, Ring.inverse_eq_inv']
        have hf := hw.fz i j hij ⟨n, hn⟩
        rw [plZ_cast, plZ_cast] at hf
        simp only [hwz, hyz, hFdef, hlamdef, Fin.cases_succ, hUrdef]
        rw [dif_pos hn]
        set t := t3Places D i.succ - t3Places D j.succ with htdef
        rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
        · simp [Finset.sum_filter, Fin.sum_univ_two, Finset.sum_range_succ] at hf ⊢
          field_simp
          linear_combination hf
        · simp [Finset.sum_filter, Fin.sum_univ_two, Finset.sum_range_succ] at hf ⊢
          field_simp
          linear_combination hf
  obtain ⟨U, hU, hrow⟩ := skel_Gs K hK 0 (t3Places D) hx S F lamR Ur hres
  set L : (c : Fin 4) → Matrix (Fin (4 * k + 1 - K c)) (Fin (4 * k + 1 - K c)) (ZMod D.p) :=
    fun c => Lgauge (4 * k + 1 - K c) (lamR c * Ring.inverse (QfK K 0 (t3Places D) c)) with hLdef
  set Dg : (c d : Fin 4) → Matrix (Fin (4 * k + 1 - K c)) (Fin (K d)) (ZMod D.p) :=
    fun c _ a l => if (a : ℕ) = 0 ∧ (l : ℕ) + 1 = k then
      Fin.cases (motive := fun _ => ZMod D.p) 0 (fun i => (D.o i : ZMod D.p)) c else 0 with hDgdef
  set Φ : (c d : Fin 4) → Matrix (Fin (4 * k + 1 - K c)) (Fin (K d)) (ZMod D.p) :=
    fun c d => if c = d then Dg c d
      else L c * frameGraphK (ZMod D.p) (4 * k + 1) K 0 (t3Places D) c d * U d with hΦdef
  have hL : ∀ c, IsLTU (L c) := fun c =>
    SkComp.Lgauge_LTU _ _ ((hlamU c).mul (SkComp.QfK_unit K 0 (t3Places D) hx c).ringInverse)
  have hΦ : ∀ c d, c ≠ d → Φ c d = L c * frameGraphK (ZMod D.p) (4 * k + 1) K 0 (t3Places D) c d * U d :=
    fun c d hcd => by simp only [hΦdef, if_neg hcd]
  refine ⟨L, U, Φ, hL, hU, hΦ, ?_, ?_,
    SkComp.frame_gauge_net D.p K hK 0 (t3Places D) hx L U hL hU Φ hΦ⟩
  · intro i l
    have hl : (l : ℕ) < k + 1 := hK0 ▸ l.isLt
    rw [hΦ i.succ 0 (Fin.succ_ne_zero i), hrow i.succ ((hS _).mpr (Fin.succ_ne_zero i)) 0
      (Fin.succ_ne_zero i) l, hcard0]
    have e : K 0 - 1 - (l : ℕ) = k - l := by omega
    simp only [e, hFdef, Fin.cases_succ, Fin.cases_zero]
    rcases (show (l : ℕ) = k ∨ (l : ℕ) + 1 = k ∨ (l : ℕ) + 2 = k ∨ (l : ℕ) + 3 ≤ k by omega)
      with h | h | h | h
    · have h0 : k - (l : ℕ) = 0 := by omega
      simp [t3xCoef, h, h0, fxZ]
    · have h0 : k - (l : ℕ) = 1 := by omega
      have h1 : (l : ℕ) ≠ k := by omega
      simp [t3xCoef, h, h0, h1, fxZ]
    · have h0 : k - (l : ℕ) = 2 := by omega
      have h1 : (l : ℕ) ≠ k := by omega
      have h2 : (l : ℕ) + 1 ≠ k := by omega
      simp [t3xCoef, h, h0, h1, h2, fxZ]
    · have h0 : ¬ (k - (l : ℕ) < 3) := by omega
      have h1 : (l : ℕ) ≠ k := by omega
      have h2 : (l : ℕ) + 1 ≠ k := by omega
      have h3 : (l : ℕ) + 2 ≠ k := by omega
      simp [t3xCoef, h0, h1, h2, h3]
  · intro i j l
    have hl : (l : ℕ) < k := hKs j ▸ l.isLt
    by_cases hij : i = j
    · subst hij
      have h0 : 0 < 4 * k + 1 - K i.succ := by rw [hKs i]; omega
      have hent : ent (Φ i.succ i.succ) 0 l = if (l : ℕ) + 1 = k then (D.o i : ZMod D.p) else 0 := by
        unfold ent
        rw [dif_pos ⟨h0, l.isLt⟩]
        simp [hΦdef, hDgdef]
      rw [hent]
      unfold t3zCoef
      rw [if_pos rfl]
      split_ifs <;> simp
    · have hne : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective _ h)
      rw [hΦ i.succ j.succ hne, hrow i.succ ((hS _).mpr (Fin.succ_ne_zero i)) j.succ hne l,
        hcardj]
      have e : K j.succ - 1 - (l : ℕ) = k - 1 - l := by have := hKs j; omega
      simp only [e, hFdef, Fin.cases_succ]
      rcases (show (l : ℕ) + 1 = k ∨ (l : ℕ) + 2 = k ∨ (l : ℕ) + 3 ≤ k by omega) with h | h | h
      · have h0 : k - 1 - (l : ℕ) = 0 := by omega
        simp [t3zCoef, hij, h, h0, fzZ]
      · have h0 : k - 1 - (l : ℕ) = 1 := by omega
        have h1 : (l : ℕ) + 1 ≠ k := by omega
        simp [t3zCoef, hij, h, h0, h1, fzZ]
      · have h0 : ¬ (k - 1 - (l : ℕ) < 2) := by omega
        have h1 : (l : ℕ) + 1 ≠ k := by omega
        have h2 : (l : ℕ) + 2 ≠ k := by omega
        simp [t3zCoef, hij, h0, h1, h2]

end Z3NetF.Proofs.T3

/-
Proof module of entry S5R2 (`prop:s5r2`, "Reachability").
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.S5Cert
public import Z3Net.SkCompII
public import Z3Net.SkNecBridge

@[expose] public section

/-!
# Entry S5R2: reachability from the frame (`prop:s5r2`)

`reach_of`: if the frame-orbit conditions `wchk D W` hold (the paper's places `b_1, b_2, a_1, a_2,
a_3` distinct; the Möbius places `P_c ≡ 1/(c - b_1)` of `s5Places`, distinct; row scalars `λ_i`; on
the column `x_1` (at `∞`) an upper triangular `3 × 3` gauge `U0` with
`F_n[z_i][x_1] = λ_i ∑_{n' ≤ n} P_{z_i}^(n') U0[n', n]` (`F_0 = κ`, `F_1 = β`, `F_2 = η`); on the
finite columns `x_2` (`3 × 3` gauge `U1`) and `z_j` (`2 × 2` gauge `Uz j`, `F_0 = g`, `F_1 = H`) with
`t = P_{z_i} - P_d`: `F_n[z_i][d] t^(n+1) = λ_i ∑_{n' ≤ n} t^(n - n') U_d[n', n]`; all diagonal entries
units), then the residual problem of `prop:skelcomp`(i) on the rows `S = {z_1, z_2, z_3}` is solved
(`w = 1`, `y = P_{z_i}` on the column `∞`; `w = y = 1/(P_{z_i} - P_d)` on a finite column `d`), and
`skel_Gs` (`prop:Gs` on the skeleton rows) gives the column gauges for every `k ≥ 1`; move (a) sets
the own blocks, and `SkComp.frame_gauge_net` (`lem:box`, `lem:nie`) the net. This is the paper's
reachability argument, on the Möbius image of the paper's frame (with `x_1` at `∞`), with the
constraints made explicit per design; the witnesses come from `scripts/s5r2_data.py`.
-/

namespace Z3NetF.Proofs.S5

open Finset Matrix

lemma zcast_eq_zero (p : ℕ) (x : ℤ) (h : x % (p : ℤ) = 0) : (x : ZMod p) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mpr (Int.dvd_of_emod_eq_zero h)

lemma zcast_ne_zero (p : ℕ) (x : ℤ) (h : x % (p : ℤ) ≠ 0) : (x : ZMod p) ≠ 0 := fun h' =>
  h (Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h'))

/-- The frame-orbit conditions in `ZMod p`. -/
structure WOK (D : S5Design) (W : Wit) : Prop where
  pl : ∀ c d : Fin 5, c ≠ d → (D.pl c : ZMod D.p) - (D.pl d : ZMod D.p) ≠ 0
  mob : ∀ c : Fin 5, c ≠ 0 → ((D.pl c : ZMod D.p) - (D.pl 0 : ZMod D.p)) * (W.P c : ZMod D.p) = 1
  P : ∀ c d : Fin 5, c ≠ 0 → d ≠ 0 → c ≠ d → (W.P c : ZMod D.p) - (W.P d : ZMod D.p) ≠ 0
  lam : ∀ i, ((W.lam i : ℤ) : ZMod D.p) ≠ 0
  u0 : ∀ n, ((W.U0 n n : ℤ) : ZMod D.p) ≠ 0
  u1 : ∀ n, ((W.U1 n n : ℤ) : ZMod D.p) ≠ 0
  uz : ∀ j n, ((W.Uz j n n : ℤ) : ZMod D.p) ≠ 0
  f0 : ∀ i n, ((fxZ D n i 0 : ℤ) : ZMod D.p) = (W.lam i : ZMod D.p) *
    ∑ n' ∈ univ.filter (fun n' : Fin 3 => n' ≤ n), (W.P (s5z i) : ZMod D.p) ^ (n' : ℕ) *
      (W.U0 n' n : ZMod D.p)
  f1 : ∀ i n, ((fxZ D n i 1 : ℤ) : ZMod D.p) * ((W.P (s5z i) : ZMod D.p) - W.P 1) ^ ((n : ℕ) + 1) =
    (W.lam i : ZMod D.p) * ∑ n' ∈ univ.filter (fun n' : Fin 3 => n' ≤ n),
      ((W.P (s5z i) : ZMod D.p) - W.P 1) ^ ((n : ℕ) - (n' : ℕ)) * (W.U1 n' n : ZMod D.p)
  fz : ∀ i j, i ≠ j → ∀ n, ((fzZ D n i j : ℤ) : ZMod D.p) *
      ((W.P (s5z i) : ZMod D.p) - W.P (s5z j)) ^ ((n : ℕ) + 1) = (W.lam i : ZMod D.p) *
    ∑ n' ∈ univ.filter (fun n' : Fin 2 => n' ≤ n),
      ((W.P (s5z i) : ZMod D.p) - W.P (s5z j)) ^ ((n : ℕ) - (n' : ℕ)) * (W.Uz j n' n : ZMod D.p)

lemma wchk_sound (D : S5Design) (W : Wit) (h : wchk D W = true) : WOK D W := by
  simp only [wchk, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, bne_iff_ne,
    ne_eq, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨fun c d hcd => ?_, fun c hc => ?_, fun c d hc hd hcd => ?_,
    fun i => zcast_ne_zero _ _ (h4 i), fun n => zcast_ne_zero _ _ (h5 n).1,
    fun n => zcast_ne_zero _ _ (h5 n).2, fun j n => zcast_ne_zero _ _ (h6 j n), fun i n => ?_,
    fun i n => ?_, fun i j hij n => ?_⟩
  · rcases h1 c d with h | h
    · exact absurd h hcd
    · have := zcast_ne_zero _ _ h; push_cast at this; exact this
  · rcases h2 c with h | h
    · exact absurd h hc
    · have := zcast_eq_zero _ _ h; push_cast at this; exact sub_eq_zero.mp this
  · rcases h3 c d with (h | h) | h
    · rcases h with h | h
      · exact absurd h hc
      · exact absurd h hd
    · exact absurd h hcd
    · have := zcast_ne_zero _ _ h; push_cast at this; exact this
  · have := zcast_eq_zero _ _ (h7 i n)
    push_cast at this
    exact sub_eq_zero.mp this
  · have := zcast_eq_zero _ _ (h8 i n)
    push_cast at this
    exact sub_eq_zero.mp this
  · rcases h9 i j with h | h
    · exact absurd h hij
    · have := zcast_eq_zero _ _ (h n)
      push_cast at this
      exact sub_eq_zero.mp this

lemma places_eq (D : S5Design) (W : Wit) (hp : D.p.Prime) (hw : WOK D W) (c : Fin 5)
    (hc : c ≠ 0) : s5Places D c = (W.P c : ZMod D.p) := by
  have : Fact D.p.Prime := ⟨hp⟩
  unfold s5Places
  exact inv_eq_of_mul_eq_one_right (hw.mob c hc)

lemma placesOK (D : S5Design) (W : Wit) (hp : D.p.Prime) (hw : WOK D W) :
    PlacesOK 0 (s5Places D) := by
  intro c d hc hd hcd
  have : Fact D.p.Prime := ⟨hp⟩
  rw [places_eq D W hp hw c hc, places_eq D W hp hw d hd]
  exact isUnit_iff_ne_zero.mpr (hw.P c d hc hd hcd)

lemma fin5_cases : ∀ d : Fin 5, d = 0 ∨ d = 1 ∨ ∃ j : Fin 3, d = s5z j := by decide

lemma s5z_ne_zero (i : Fin 3) : s5z i ≠ 0 := by fin_cases i <;> decide

lemma s5z_ne_one (i : Fin 3) : s5z i ≠ 1 := by fin_cases i <;> decide

lemma s5z_inj {i j : Fin 3} (h : s5z i = s5z j) : i = j := by
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)

/-- **Reachability** (`prop:s5r2`) from the frame-orbit conditions. -/
theorem reach_of (D : S5Design) (W : Wit) (hp : D.p.Prime) (hw : WOK D W) :
    (∀ c d : Fin 5, c ≠ d → (D.pl c : ZMod D.p) ≠ (D.pl d : ZMod D.p)) ∧
    PlacesOK 0 (s5Places D) ∧ ∀ k, 1 ≤ k →
      ∃ (L : (c : Fin 5) → Matrix (Fin (5 * k + 2 - skDepth 2 k c))
          (Fin (5 * k + 2 - skDepth 2 k c)) (ZMod D.p))
        (U : (d : Fin 5) → Matrix (Fin (skDepth 2 k d)) (Fin (skDepth 2 k d)) (ZMod D.p))
        (Φ : (c d : Fin 5) → Matrix (Fin (5 * k + 2 - skDepth 2 k c)) (Fin (skDepth 2 k d))
          (ZMod D.p)),
        (∀ c, IsLTU (L c)) ∧ (∀ d, IsLTU (U d)) ∧
        (∀ c d, c ≠ d → Φ c d =
          L c * frameGraphK (ZMod D.p) (5 * k + 2) (skDepth 2 k) 0 (s5Places D) c d * U d) ∧
        (∀ (i : Fin 3) (d : Fin 2) (l : Fin (skDepth 2 k (s5x d))),
          ent (Φ (s5z i) (s5x d)) 0 l = ((s5xCoef D k i d l : ℤ) : ZMod D.p)) ∧
        (∀ (i j : Fin 3) (l : Fin (skDepth 2 k (s5z j))),
          ent (Φ (s5z i) (s5z j)) 0 l = ((s5zCoef D k i j l : ℤ) : ZMod D.p)) ∧
        IsNet0 5 D.p (5 * k + 2)
          (digPoint D.p (5 * k + 2) (graphGenK (m := 5 * k + 2) (skDepth 2 k) Φ)) := by
  have : Fact D.p.Prime := ⟨hp⟩
  have : NeZero D.p := ⟨hp.ne_zero⟩
  have hx := placesOK D W hp hw
  refine ⟨fun c d hcd => sub_ne_zero.mp (hw.pl c d hcd), hx, fun k hk => ?_⟩
  set K : Fin 5 → ℕ := skDepth 2 k with hKdef
  have hK : ∑ c, K c = 5 * k + 2 := SkComp.sum_skDepth' 2 k (by omega)
  have hKx : ∀ d : Fin 2, K (s5x d) = k + 1 := by intro d; fin_cases d <;> simp [hKdef, skDepth]
  have hKz : ∀ j : Fin 3, K (s5z j) = k := by intro j; fin_cases j <;> simp [hKdef, skDepth]
  set S : Finset (Fin 5) := univ.filter (fun c : Fin 5 => 2 ≤ (c : ℕ)) with hSdef
  have hSz : ∀ i : Fin 3, s5z i ∈ S := by intro i; fin_cases i <;> decide
  have hS : ∀ c ∈ S, ∃ i : Fin 3, c = s5z i := by
    intro c hc
    rcases fin5_cases c with rfl | rfl | h
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · exact h
  have hcard0 : (S.erase 0).card = 3 := by decide
  have hcard1 : (S.erase 1).card = 3 := by decide
  have hcardx : ∀ d : Fin 2, (S.erase (s5x d)).card = 3 := by
    intro d; fin_cases d
    · exact hcard0
    · exact hcard1
  have hcardz : ∀ j : Fin 3, (S.erase (s5z j)).card = 2 := by intro j; fin_cases j <;> decide
  -- the data of the residual problem
  set lamR : Fin 5 → ZMod D.p :=
    Fin.cases 1 (Fin.cases 1 (fun i => (W.lam i : ZMod D.p))) with hlamdef
  have hlamz : ∀ i, lamR (s5z i) = (W.lam i : ZMod D.p) := fun i => rfl
  set fx : ℕ → Fin 3 → Fin 2 → ZMod D.p := fun n i d =>
    if h : n < 3 then (fxZ D ⟨n, h⟩ i d : ZMod D.p) else 0 with hfxdef
  set fz : ℕ → Fin 3 → Fin 3 → ZMod D.p := fun n i j =>
    if h : n < 2 then (fzZ D ⟨n, h⟩ i j : ZMod D.p) else 0 with hfzdef
  set F : ℕ → Fin 5 → Fin 5 → ZMod D.p := fun n c d => Fin.cases (motive := fun _ => ZMod D.p) 0
      (Fin.cases (motive := fun _ => ZMod D.p) 0 (fun i => Fin.cases (motive := fun _ => ZMod D.p)
        (fx n i 0) (Fin.cases (motive := fun _ => ZMod D.p) (fx n i 1) (fun j => fz n i j)) d)) c
    with hFdef
  have hFx : ∀ n i (d : Fin 2), F n (s5z i) (s5x d) = fx n i d := by
    intro n i d; fin_cases d <;> rfl
  have hFz : ∀ n i j, F n (s5z i) (s5z j) = fz n i j := fun _ _ _ => rfl
  set u0 : ℕ → ℕ → ZMod D.p := fun n' n =>
    if h : n' < 3 ∧ n < 3 then (W.U0 ⟨n', h.1⟩ ⟨n, h.2⟩ : ZMod D.p) else 0 with hu0def
  set u1 : ℕ → ℕ → ZMod D.p := fun n' n =>
    if h : n' < 3 ∧ n < 3 then (W.U1 ⟨n', h.1⟩ ⟨n, h.2⟩ : ZMod D.p) else 0 with hu1def
  set uz : Fin 3 → ℕ → ℕ → ZMod D.p := fun j n' n =>
    if h : n' < 2 ∧ n < 2 then (W.Uz j ⟨n', h.1⟩ ⟨n, h.2⟩ : ZMod D.p) else 0 with huzdef
  set Ur : Fin 5 → ℕ → ℕ → ZMod D.p := fun d n' n =>
    if n' ≤ n then Fin.cases (motive := fun _ => ZMod D.p) (u0 n' n)
      (Fin.cases (motive := fun _ => ZMod D.p) (u1 n' n) (fun j => uz j n' n)) d else 0 with hUrdef
  have hU0 : ∀ n' n, n' ≤ n → Ur 0 n' n = u0 n' n := fun n' n h => by simp [hUrdef, h]
  have hU1 : ∀ n' n, n' ≤ n → Ur 1 n' n = u1 n' n := fun n' n h => by
    simp only [hUrdef, if_pos h]; rfl
  have hUz : ∀ j n' n, n' ≤ n → Ur (s5z j) n' n = uz j n' n := fun j n' n h => by
    simp only [hUrdef, if_pos h]; rfl
  -- the places
  have hPz : ∀ i, s5Places D (s5z i) = (W.P (s5z i) : ZMod D.p) := fun i =>
    places_eq D W hp hw _ (s5z_ne_zero i)
  have hP1 : s5Places D 1 = (W.P 1 : ZMod D.p) := places_eq D W hp hw 1 (by decide)
  have hres : ResidualSk 0 (s5Places D) S F lamR Ur := by
    refine ⟨fun c hc => ?_, ?_, ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := hS c hc
      rw [hlamz]; exact isUnit_iff_ne_zero.mpr (hw.lam i)
    · intro d n' n h1 _
      simp only [hUrdef, if_neg (show ¬ n' ≤ n by omega)]
    · intro d n hn
      rcases fin5_cases d with rfl | rfl | ⟨j, rfl⟩
      · rw [hcard0] at hn
        rw [hU0 n n le_rfl]
        simp only [hu0def, dif_pos (And.intro hn hn)]
        exact isUnit_iff_ne_zero.mpr (hw.u0 ⟨n, hn⟩)
      · rw [hcard1] at hn
        rw [hU1 n n le_rfl]
        simp only [hu1def, dif_pos (And.intro hn hn)]
        exact isUnit_iff_ne_zero.mpr (hw.u1 ⟨n, hn⟩)
      · rw [hcardz] at hn
        rw [hUz j n n le_rfl]
        simp only [huzdef, dif_pos (And.intro hn hn)]
        exact isUnit_iff_ne_zero.mpr (hw.uz j ⟨n, hn⟩)
    · intro c hc d hcd n hn
      obtain ⟨i, rfl⟩ := hS c hc
      rcases fin5_cases d with rfl | rfl | ⟨j, rfl⟩
      · -- the column `x_1` at `∞`
        rw [hcard0] at hn
        have hw1 : wN 0 (s5Places D) (s5z i) 0 = 1 := by simp [wN]
        have hy1 : yN 0 (s5Places D) (s5z i) 0 = (W.P (s5z i) : ZMod D.p) := by
          simp [yN, s5z_ne_zero i, hPz]
        have hf := hw.f0 i ⟨n, hn⟩
        rw [hw1, hy1, hlamz, show F n (s5z i) 0 = fx n i 0 from hFx n i 0]
        rw [Finset.sum_congr rfl (fun n' hn' => by
          rw [hU0 n' n (by simp only [mem_range] at hn'; omega)])]
        simp only [hfxdef, dif_pos hn, hf, hu0def]
        rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl <;>
          simp [Finset.sum_filter, Fin.sum_univ_three, Finset.sum_range_succ]
      · -- the finite full column `x_2`
        rw [hcard1] at hn
        have ht : (W.P (s5z i) : ZMod D.p) - W.P 1 ≠ 0 :=
          hw.P _ _ (s5z_ne_zero i) (by decide) (s5z_ne_one i)
        have hw1 : wN 0 (s5Places D) (s5z i) 1 = ((W.P (s5z i) : ZMod D.p) - W.P 1)⁻¹ := by
          simp [wN, s5z_ne_zero i, hPz, hP1, Ring.inverse_eq_inv']
        have hy1 : yN 0 (s5Places D) (s5z i) 1 = ((W.P (s5z i) : ZMod D.p) - W.P 1)⁻¹ := by
          simp [yN, s5z_ne_zero i, hPz, hP1, Ring.inverse_eq_inv']
        have hf := hw.f1 i ⟨n, hn⟩
        rw [hw1, hy1, hlamz, show F n (s5z i) 1 = fx n i 1 from hFx n i 1]
        rw [Finset.sum_congr rfl (fun n' hn' => by
          rw [hU1 n' n (by simp only [mem_range] at hn'; omega)])]
        simp only [hfxdef, dif_pos hn, hu1def]
        set t := (W.P (s5z i) : ZMod D.p) - W.P 1 with htdef
        rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
        · simp [Finset.sum_filter, Fin.sum_univ_three, Finset.sum_range_succ] at hf ⊢
          field_simp
          linear_combination hf
        · simp [Finset.sum_filter, Fin.sum_univ_three, Finset.sum_range_succ] at hf ⊢
          field_simp
          linear_combination hf
        · simp [Finset.sum_filter, Fin.sum_univ_three, Finset.sum_range_succ] at hf ⊢
          field_simp
          linear_combination hf
      · -- a skeleton column `z_j`
        have hij : i ≠ j := fun h => hcd (by rw [h])
        rw [hcardz] at hn
        have ht : (W.P (s5z i) : ZMod D.p) - W.P (s5z j) ≠ 0 :=
          hw.P _ _ (s5z_ne_zero i) (s5z_ne_zero j) hcd
        have hw1 : wN 0 (s5Places D) (s5z i) (s5z j) =
            ((W.P (s5z i) : ZMod D.p) - W.P (s5z j))⁻¹ := by
          simp [wN, s5z_ne_zero i, s5z_ne_zero j, hPz, Ring.inverse_eq_inv']
        have hy1 : yN 0 (s5Places D) (s5z i) (s5z j) =
            ((W.P (s5z i) : ZMod D.p) - W.P (s5z j))⁻¹ := by
          simp [yN, s5z_ne_zero i, s5z_ne_zero j, hPz, Ring.inverse_eq_inv']
        have hf := hw.fz i j hij ⟨n, hn⟩
        rw [hw1, hy1, hlamz, hFz]
        rw [Finset.sum_congr rfl (fun n' hn' => by
          rw [hUz j n' n (by simp only [mem_range] at hn'; omega)])]
        simp only [hfzdef, dif_pos hn, huzdef]
        set t := (W.P (s5z i) : ZMod D.p) - W.P (s5z j) with htdef
        rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
        · simp [Finset.sum_filter, Fin.sum_univ_two, Finset.sum_range_succ] at hf ⊢
          field_simp
          linear_combination hf
        · simp [Finset.sum_filter, Fin.sum_univ_two, Finset.sum_range_succ] at hf ⊢
          field_simp
          linear_combination hf
  obtain ⟨U, hU, hrow⟩ := skel_Gs K hK 0 (s5Places D) hx S F lamR Ur hres
  set L : (c : Fin 5) → Matrix (Fin (5 * k + 2 - K c)) (Fin (5 * k + 2 - K c)) (ZMod D.p) :=
    fun c => Lgauge (5 * k + 2 - K c) (lamR c * Ring.inverse (QfK K 0 (s5Places D) c)) with hLdef
  set oR : Fin 5 → ZMod D.p :=
    Fin.cases 0 (Fin.cases 0 (fun i => (D.o i : ZMod D.p))) with hoRdef
  set Dg : (c d : Fin 5) → Matrix (Fin (5 * k + 2 - K c)) (Fin (K d)) (ZMod D.p) :=
    fun c _ a l => if (a : ℕ) = 0 ∧ (l : ℕ) + 1 = k then oR c else 0 with hDgdef
  set Φ : (c d : Fin 5) → Matrix (Fin (5 * k + 2 - K c)) (Fin (K d)) (ZMod D.p) :=
    fun c d => if c = d then Dg c d
      else L c * frameGraphK (ZMod D.p) (5 * k + 2) K 0 (s5Places D) c d * U d with hΦdef
  have hlamU : ∀ c, IsUnit (lamR c) := by
    intro c
    rcases fin5_cases c with rfl | rfl | ⟨i, rfl⟩
    · exact isUnit_one
    · exact isUnit_one
    · rw [hlamz]; exact isUnit_iff_ne_zero.mpr (hw.lam i)
  have hL : ∀ c, IsLTU (L c) := fun c =>
    SkComp.Lgauge_LTU _ _ ((hlamU c).mul (SkComp.QfK_unit K 0 (s5Places D) hx c).ringInverse)
  have hΦ : ∀ c d, c ≠ d →
      Φ c d = L c * frameGraphK (ZMod D.p) (5 * k + 2) K 0 (s5Places D) c d * U d :=
    fun c d hcd => by simp only [hΦdef, if_neg hcd]
  refine ⟨L, U, Φ, hL, hU, hΦ, ?_, ?_,
    SkComp.frame_gauge_net D.p K hK 0 (s5Places D) hx L U hL hU Φ hΦ⟩
  · intro i d l
    have hl : (l : ℕ) < k + 1 := hKx d ▸ l.isLt
    have hne : s5z i ≠ s5x d := by fin_cases i <;> fin_cases d <;> decide
    rw [hΦ _ _ hne, hrow (s5z i) (hSz i) (s5x d) hne l, hcardx d]
    have e : K (s5x d) - 1 - (l : ℕ) = k - l := by have := hKx d; omega
    simp only [e, hFx, hfxdef]
    rcases (show (l : ℕ) = k ∨ (l : ℕ) + 1 = k ∨ (l : ℕ) + 2 = k ∨ (l : ℕ) + 3 ≤ k by omega)
      with h | h | h | h
    · have h0 : k - (l : ℕ) = 0 := by omega
      simp [s5xCoef, h, h0, fxZ]
    · have h0 : k - (l : ℕ) = 1 := by omega
      have h1 : (l : ℕ) ≠ k := by omega
      simp [s5xCoef, h, h0, h1, fxZ]
    · have h0 : k - (l : ℕ) = 2 := by omega
      have h1 : (l : ℕ) ≠ k := by omega
      have h2 : (l : ℕ) + 1 ≠ k := by omega
      simp [s5xCoef, h, h0, h1, h2, fxZ]
    · have h0 : ¬ (k - (l : ℕ) < 3) := by omega
      have h1 : (l : ℕ) ≠ k := by omega
      have h2 : (l : ℕ) + 1 ≠ k := by omega
      have h3 : (l : ℕ) + 2 ≠ k := by omega
      simp [s5xCoef, h0, h1, h2, h3]
  · intro i j l
    have hl : (l : ℕ) < k := hKz j ▸ l.isLt
    by_cases hij : i = j
    · subst hij
      have h0 : 0 < 5 * k + 2 - K (s5z i) := by rw [hKz i]; omega
      have hent : ent (Φ (s5z i) (s5z i)) 0 l =
          if (l : ℕ) + 1 = k then (D.o i : ZMod D.p) else 0 := by
        unfold ent
        rw [dif_pos ⟨h0, l.isLt⟩]
        have hoR : oR (s5z i) = (D.o i : ZMod D.p) := rfl
        simp [hΦdef, hDgdef, hoR]
      rw [hent]
      unfold s5zCoef
      rw [if_pos rfl]
      split_ifs <;> simp
    · have hne : s5z i ≠ s5z j := fun h => hij (s5z_inj h)
      rw [hΦ _ _ hne, hrow (s5z i) (hSz i) (s5z j) hne l, hcardz]
      have e : K (s5z j) - 1 - (l : ℕ) = k - 1 - l := by have := hKz j; omega
      simp only [e, hFz, hfzdef]
      rcases (show (l : ℕ) + 1 = k ∨ (l : ℕ) + 2 = k ∨ (l : ℕ) + 3 ≤ k by omega) with h | h | h
      · have h0 : k - 1 - (l : ℕ) = 0 := by omega
        simp [s5zCoef, hij, h, h0, fzZ]
      · have h0 : k - 1 - (l : ℕ) = 1 := by omega
        have h1 : (l : ℕ) + 1 ≠ k := by omega
        simp [s5zCoef, hij, h, h0, h1, fzZ]
      · have h0 : ¬ (k - 1 - (l : ℕ) < 2) := by omega
        have h1 : (l : ℕ) + 1 ≠ k := by omega
        have h2 : (l : ℕ) + 2 ≠ k := by omega
        simp [s5zCoef, hij, h0, h1, h2]

end Z3NetF.Proofs.S5

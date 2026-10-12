/-
Proof module of entry Skel (bridge between `IsSkGF` and `graphGenK (skDepth r k)`).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkelDefs
public import Z3Net.FBox

@[expose] public section

/-!
# Entry Skel: graph forms in the skeleton depths

* `SkNec.pre_skDepth`, `SkNec.offL_skDepth`, `SkNec.sum_skDepth`: the block offsets of the depths
  `skDepth r k` are `skOff r k d`, and the depths sum to `s k + r` (for `r ≤ s`).
* `SkNec.boxLoc_skDepth`: column `skOff r k d + l` (`l < K_d`) is level `l` of block `d`.
* `SkNec.ent_graphGen`: the entries of `graphGenK K Φ` through the total accessor `ent`.
* `skel_graphGen` (Challenge): `graphGenK (skDepth r k) Φ` is in skeleton graph form, and row `k` of
  a skeleton coordinate is row `0` of its offset blocks.
* `SkNec.eq_graphGen_of_IsSkGF` (converse): a skeleton graph form `C` is `graphGenK (skDepth r k)`
  of `SkNec.phiOf C`, `phiOf C c d r' l = ent (C c) (K_c + r') (skOff r k d + l)`.
-/

namespace Z3NetF.Proofs

open Matrix Finset

namespace SkNec

variable {s : ℕ}

lemma skOff_zero (r k : ℕ) : Z3NetF.skOff r k 0 = 0 := by simp [Z3NetF.skOff]

lemma skOff_succ (r k c : ℕ) :
    Z3NetF.skOff r k (c + 1) = Z3NetF.skOff r k c + (if c < r then k + 1 else k) := by
  unfold Z3NetF.skOff
  rw [Nat.succ_mul]
  generalize c * k = t
  split_ifs with h <;> omega

/-- Prefix sums of the skeleton depths are the skeleton offsets. -/
lemma pre_skDepth (r k : ℕ) : ∀ c ≤ s, pre (Z3NetF.skDepth (s := s) r k) c = Z3NetF.skOff r k c
  | 0, _ => by rw [skOff_zero]; exact Z3NetU.Proofs.pre_zero _
  | c + 1, hc => by
    have h1 := Z3NetU.Proofs.pre_succ (Z3NetF.skDepth (s := s) r k) ⟨c, by omega⟩
    have ih := pre_skDepth r k c (by omega)
    simp only [pre] at ih h1 ⊢
    rw [h1, ih, skOff_succ]
    simp [Z3NetF.skDepth]

lemma offL_skDepth (r k : ℕ) (d : Fin s) :
    Z3NetF.offL (Z3NetF.skDepth r k) d = Z3NetF.skOff r k d := by
  rw [← pre_skDepth r k d d.isLt.le, pre, Z3NetU.Proofs.pre_eq_sum]
  rfl

lemma sum_skDepth {r : ℕ} (k : ℕ) (hr : r ≤ s) :
    ∑ c, Z3NetF.skDepth (s := s) r k c = s * k + r := by
  have h := Z3NetU.Proofs.pre_eq_sum (Z3NetF.skDepth (s := s) r k) s
  have hf : univ.filter (fun t : Fin s => (t : ℕ) < s) = univ := by
    ext t; simp
  rw [hf] at h
  rw [← h]
  have := pre_skDepth (s := s) r k s le_rfl
  simp only [pre] at this
  rw [this, Z3NetF.skOff, Nat.min_eq_right hr]

lemma skDepth_le (r k : ℕ) (c : Fin s) : Z3NetF.skDepth r k c ≤ k + 1 := by
  unfold Z3NetF.skDepth; split_ifs <;> omega

lemma boxLoc_skDepth (r k : ℕ) (d : Fin s) (l : ℕ) (hl : l < Z3NetF.skDepth r k d) :
    Z3NetF.boxLoc (List.ofFn (Z3NetF.skDepth (s := s) r k)) 0 (Z3NetF.skOff r k d + l) = ((d : ℕ), l) := by
  rw [← pre_skDepth r k d d.isLt.le]
  exact boxLoc_pre _ d l hl

/-- Entries of a graph form, through the total accessor `ent`. -/
lemma ent_graphGen {R : Type*} [Zero R] [One R] {m : ℕ} (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R) (c : Fin s) (i : ℕ) (hi : i < m)
    (e : Fin s) (l : ℕ) (hl : l < K e) :
    Z3NetF.ent (Z3NetF.graphGenK K Φ c) i (pre K e + l) =
      if i < K c then (if e = c ∧ l = i then 1 else 0) else Z3NetF.ent (Φ c e) (i - K c) l := by
  have hcol := pre_add_lt K hK e l hl
  unfold Z3NetF.ent
  rw [dif_pos ⟨hi, hcol⟩]
  have := graphGenK_apply K hK Φ c ⟨i, hi⟩ e l hl
  rw [this]
  by_cases h : i < K c
  · rw [dif_pos h, if_pos h]
  · rw [dif_neg h, if_neg h, dif_pos ⟨by omega, hl⟩]

lemma pre_inj (K : Fin s → ℕ) (c e : Fin s) (i l : ℕ) (hi : i < K c) (hl : l < K e) :
    pre K e + l = pre K c + i ↔ e = c ∧ l = i := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := pos_inj K c e i l hi hl h.symm
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The graph-form blocks read off a matrix tuple in skeleton graph form. -/
def phiOf {p : ℕ} (r k : ℕ) (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p))
    (c d : Fin s) :
    Matrix (Fin (s * k + r - Z3NetF.skDepth r k c)) (Fin (Z3NetF.skDepth r k d)) (ZMod p) :=
  fun r' l => Z3NetF.ent (C c) (Z3NetF.skDepth r k c + (r' : ℕ)) (Z3NetF.skOff r k d + (l : ℕ))

/-- Converse of `skel_graphGen`: a skeleton graph form is the graph form of `phiOf C`. -/
theorem eq_graphGen_of_IsSkGF {p r k : ℕ} (hr : r ≤ s)
    (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p))
    (hC : Z3NetF.IsSkGF s r p k C) :
    C = Z3NetF.graphGenK (m := s * k + r) (Z3NetF.skDepth r k) (phiOf r k C) := by
  have hK := sum_skDepth (s := s) (r := r) k hr
  funext c i j
  obtain ⟨e, l, hl, rfl⟩ := col_cover _ hK j
  rw [graphGenK_apply _ hK _ c i e l hl]
  have hpre := pre_skDepth (s := s) r k e e.isLt.le
  have hcol := pre_add_lt _ hK e l hl
  have hentC : ∀ i' : ℕ, (hi' : i' < s * k + r) →
      Z3NetF.ent (C c) i' (pre (Z3NetF.skDepth (s := s) r k) e + l) = C c ⟨i', hi'⟩ ⟨_, hcol⟩ := by
    intro i' hi'
    unfold Z3NetF.ent; rw [dif_pos ⟨hi', hcol⟩]
  by_cases hi : (i : ℕ) < Z3NetF.skDepth r k c
  · rw [dif_pos hi, ← hentC i i.isLt, hC c i hi _ hcol]
    have hpc := pre_skDepth (s := s) r k c c.isLt.le
    simp only [pre] at hpre hpc
    rw [← hpc]
    have := pre_inj (Z3NetF.skDepth r k) c e i l hi hl
    simp only [pre] at this
    by_cases h : e = c ∧ l = (i : ℕ)
    · rw [if_pos (this.2 h), if_pos h]
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
  · rw [dif_neg hi]
    simp only [phiOf]
    rw [← hpre]
    have : Z3NetF.skDepth r k c + ((i : ℕ) - Z3NetF.skDepth r k c) = i := by omega
    rw [this, hentC i i.isLt]

end SkNec

open SkNec in
/-- **Graph forms in the skeleton depths** (Challenge `skel_graphGen`). -/
theorem skel_graphGen (s r p k : ℕ) (hr : r ≤ s)
    (Φ : (c d : Fin s) → Matrix (Fin (s * k + r - skDepth r k c)) (Fin (skDepth r k d)) (ZMod p)) :
    IsSkGF s r p k (graphGenK (m := s * k + r) (skDepth r k) Φ) ∧
      ∀ z d : Fin s, r ≤ (z : ℕ) → ∀ l : Fin (skDepth r k d),
        ent (graphGenK (m := s * k + r) (skDepth r k) Φ z) k (skOff r k (d : ℕ) + l) =
          ent (Φ z d) 0 l := by
  have hK := sum_skDepth (s := s) (r := r) k hr
  refine ⟨?_, ?_⟩
  · intro c j hj col hcol
    obtain ⟨e, l, hl, hcol'⟩ := col_cover _ hK ⟨col, hcol⟩
    have hcolv : col = pre (skDepth r k) e + l := congrArg Fin.val hcol'
    have hjm : j < s * k + r := by
      have := le_of_sum _ hK c; omega
    rw [hcolv, ent_graphGen _ hK Φ c j hjm e l hl, if_pos hj]
    have hpc := pre_skDepth (s := s) r k c c.isLt.le
    rw [← hpc]
    by_cases h : e = c ∧ l = j
    · rw [if_pos h, if_pos ((pre_inj _ c e j l hj hl).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((pre_inj _ c e j l hj hl).1 h'))]
  · intro z d hz l
    have hKz : skDepth r k z = k := by
      unfold skDepth; rw [if_neg (by omega)]
    have hpd := pre_skDepth (s := s) r k d d.isLt.le
    by_cases hkm : k < s * k + r
    · rw [← hpd, ent_graphGen _ hK Φ z k hkm d l l.isLt, if_neg (by rw [hKz]; exact lt_irrefl k),
        show k - skDepth r k z = 0 by rw [hKz, Nat.sub_self]]
    · have h1 : ent (graphGenK (m := s * k + r) (skDepth r k) Φ z) k
          (skOff r k (d : ℕ) + l) = 0 := by
        unfold ent; rw [dif_neg (fun h => hkm h.1)]
      have h2 : ent (Φ z d) 0 l = 0 := by
        unfold ent; rw [dif_neg]; rw [hKz]; omega
      rw [h1, h2]

end Z3NetF.Proofs

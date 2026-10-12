/-
Proof module of entry Obs: `def:Ktrue` (the sentence after it), `thm:L` and the `±1` statement
after it.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsP2
public import Z3Net.SkNec

@[expose] public section

/-!
# Entry Obs: `thm:L`

* Box minors (`lem:nie`, `lem:box`): for a net in graph form with depths `(k, …, k)`, the box with
  depths `k + 1` on the rows `I`, `k - 1` on the columns `J` (disjoint, `|I| = |J|`) and `k`
  elsewhere has the minor `± det (M_{I,J})` of the level-`(k-1)` entries; so the off-diagonal
  entries of the layer and its `2 × 2` minors on disjoint row and column pairs are units, hence
  nonzero integers (`Mt_ne_zero`, `Mt_minor_ne_zero`).
* `L_core`: the combinatorial core of `thm:L` (small entries, orientation, convexity count,
  direction pigeonhole) for an integer matrix with these properties.
-/

namespace Z3NetF.Proofs

open Matrix Finset ObsCount ObsStep ObsCeil SkNec

noncomputable section

namespace ObsL

variable {s q k : ℕ} [NeZero q]

/-- `lem:nie` and `lem:box` for depths `(k, …, k)`: rows `I`, columns `J`. -/
theorem unit_IJ (hk : 1 ≤ k) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (n : ℕ) (I J : Fin n ↪ Fin s)
    (hIJ : ∀ a b, I a ≠ J b) :
    IsUnit (Matrix.of fun a b : Fin n => Z3NetF.ent (Φ (I a) (J b)) 0 (k - 1)).det := by
  classical
  set K : Fin s → ℕ := fun _ => k with hKdef
  have hK : ∑ c, K c = s * k := by simp [hKdef]
  let S := univ.map I
  let T := univ.map J
  have hS : ∀ c, c ∈ S ↔ ∃ a, I a = c := by intro c; simp [S]
  have hT : ∀ c, c ∈ T ↔ ∃ b, J b = c := by intro c; simp [T]
  let up : Fin s → ℕ := fun c => if c ∈ S then 1 else 0
  let down : Fin s → ℕ := fun c => if c ∈ T then 1 else 0
  let dv := dvec K up down
  have hdv : ∑ c, dv c = s * k := by
    refine sum_dvec K up down hK (fun c => ?_) ?_
    · simp only [down]; split_ifs
      · simp [hKdef]; omega
      · exact Nat.zero_le _
    · simp only [up, down]
      rw [sum_ind, sum_ind, card_map, card_map]
  have hupI : ∀ a, up (I a) = 1 := by
    intro a; simp only [up]; rw [if_pos ((hS _).2 ⟨a, rfl⟩)]
  have hdownI : ∀ a, down (I a) = 0 := by
    intro a; simp only [down]; rw [if_neg]; rw [hT]; rintro ⟨b, hb⟩; exact hIJ a b hb.symm
  have hupJ : ∀ b, up (J b) = 0 := by
    intro b; simp only [up]; rw [if_neg]; rw [hS]; rintro ⟨a, ha⟩; exact hIJ a b ha
  have hdownJ : ∀ b, down (J b) = 1 := by
    intro b; simp only [down]; rw [if_pos ((hT _).2 ⟨b, rfl⟩)]
  have hdvI : ∀ a, dv (I a) = K (I a) + 1 := by
    intro a; simp only [dv, dvec, hupI, hdownI]; omega
  have hdvJ : ∀ b, dv (J b) + 1 = K (J b) := by
    intro b; simp only [dv, dvec, hupJ, hdownJ, hKdef]; omega
  have hcovO : ∀ c, K c < dv c → ∃ a, I a = c := by
    intro c hc
    have := up_ne_zero hc
    simp only [up] at this
    split_ifs at this with h
    · exact (hS c).1 h
    · exact absurd rfl this
  have hcovU : ∀ c, dv c < K c → ∃ b, J b = c := by
    intro c hc
    have := down_ne_zero hc
    simp only [down] at this
    split_ifs at this with h
    · exact (hT c).1 h
    · exact absurd rfl this
  set eU := underEquivJ K dv J hdvJ hcovU
  set eO := overEquiv K dv I hdvI hcovO
  have hu := (nie_zmod q _).1 hnet dv hdv
  obtain ⟨-, hbm⟩ := box_minor (R := ZMod q) K dv hK hdv
  obtain ⟨ε, -, hdet⟩ := hbm (eU.symm.trans eO)
  have hu2 : IsUnit (Z3NetF.boxMatrix (Z3NetF.graphGenK (m := s * k) K Φ) dv).det := hu
  rw [hdet Φ] at hu2
  have hne := isUnit_of_mul_isUnit_right hu2
  rw [← Matrix.det_submatrix_equiv_self eU] at hne
  convert hne using 2
  ext a b
  simp only [Matrix.of_apply, Matrix.submatrix_apply, Z3NetF.redBox]
  have h1 : (eU.symm.trans eO) (eU a) = eO a := by simp
  rw [h1]
  have hOc : (eO a).1.1 = I a := overEquiv_c K dv I hdvI hcovO a
  have hOl : ((eO a).2 : ℕ) = 0 := overEquiv_l K dv I hdvI hcovO a
  have hUc : (eU b).1.1 = J b := underEquivJ_c K dv J hdvJ hcovU b
  have hUl : ((eU b).2 : ℕ) = 0 := underEquivJ_l K dv J hdvJ hcovU b
  have hdJ : dv (J b) = k - 1 := by have := hdvJ b; simp only [hKdef] at this; omega
  have hsk : 0 < s * k - k := by
    have := (I a).isLt; have := (J b).isLt
    have : (I a : ℕ) ≠ J b := fun h => hIJ a b (Fin.ext h)
    have : 2 ≤ s := by omega
    have : 2 * k ≤ s * k := Nat.mul_le_mul_right k this
    omega
  rw [dif_pos (by rw [hOl]; simpa [hKdef] using hsk)]
  unfold Z3NetF.ent
  rw [dif_pos ⟨by simpa [hKdef] using hsk, by omega⟩]
  congr 1
  all_goals first
    | (ext; simp only [hUl, hUc, hdJ, add_zero])
    | exact Fin.ext hOl
    | rw [hOc, hUc]

lemma Mt_ne_zero (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (c d : Fin s) (hcd : c ≠ d) :
    Z3NetF.Mt Φ c d ≠ 0 := by
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  let I : Fin 1 ↪ Fin s := ⟨fun _ => c, fun i j _ => Subsingleton.elim i j⟩
  let J : Fin 1 ↪ Fin s := ⟨fun _ => d, fun i j _ => Subsingleton.elim i j⟩
  have hu := unit_IJ hk Φ hnet 1 I J (fun _ _ => hcd)
  rw [Matrix.det_unique] at hu
  simp only [Matrix.of_apply] at hu
  intro h0
  unfold Z3NetF.Mt at h0
  rw [ZMod.valMinAbs_eq_zero] at h0
  exact hu.ne_zero h0

lemma Mt_minor_ne_zero (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (c c' d d' : Fin s) (hcc : c ≠ c')
    (hdd : d ≠ d') (h1 : c ≠ d) (h2 : c ≠ d') (h3 : c' ≠ d) (h4 : c' ≠ d') :
    Z3NetF.Mt Φ c d * Z3NetF.Mt Φ c' d' - Z3NetF.Mt Φ c d' * Z3NetF.Mt Φ c' d ≠ 0 := by
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  let I : Fin 2 ↪ Fin s := ⟨![c, c'], by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  let J : Fin 2 ↪ Fin s := ⟨![d, d'], by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  have hu := unit_IJ hk Φ hnet 2 I J (by
    intro a b; fin_cases a <;> fin_cases b <;> simp [I, J] <;> assumption)
  rw [Matrix.det_fin_two] at hu
  simp only [Matrix.of_apply, I, J, Function.Embedding.coeFn_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hu
  intro h0
  have : ((Z3NetF.Mt Φ c d * Z3NetF.Mt Φ c' d' - Z3NetF.Mt Φ c d' * Z3NetF.Mt Φ c' d : ℤ) :
      ZMod q) = 0 := by rw [h0]; simp
  push_cast at this
  simp only [Z3NetF.Mt, ZMod.coe_valMinAbs] at this
  exact hu.ne_zero this

/-! ## The combinatorial core -/

section core

variable {s : ℕ} (M : Fin s → Fin s → ℤ)

lemma diag_le (a : Fin s) : (M a a).natAbs ≤ Z3NetF.pairVal M :=
  le_trans (Finset.le_sup (f := fun a => (M a a).natAbs) (mem_univ a)) (le_max_left _ _)

lemma config_le (a b : Fin s) (hab : a ≠ b) (ε : ℤ) (hε : ε ∈ ({1, -1} : Finset ℤ))
    (ha : 0 < Z3NetF.sig M a b ε a) (hb : ε * Z3NetF.sig M a b ε b < 0) :
    (Z3NetF.sig M a b ε b).natAbs ≤ Z3NetF.pairVal M := by
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (Finset.le_sup (f := fun a => univ.sup fun b =>
    ({1, -1} : Finset ℤ).sup fun ε => if a ≠ b ∧ 0 < Z3NetF.sig M a b ε a ∧
      ε * Z3NetF.sig M a b ε b < 0 then (Z3NetF.sig M a b ε b).natAbs else 0) (mem_univ a))
  refine le_trans ?_ (Finset.le_sup (f := fun b =>
    ({1, -1} : Finset ℤ).sup fun ε => if a ≠ b ∧ 0 < Z3NetF.sig M a b ε a ∧
      ε * Z3NetF.sig M a b ε b < 0 then (Z3NetF.sig M a b ε b).natAbs else 0) (mem_univ b))
  refine le_trans ?_ (Finset.le_sup (f := fun ε => if a ≠ b ∧ 0 < Z3NetF.sig M a b ε a ∧
      ε * Z3NetF.sig M a b ε b < 0 then (Z3NetF.sig M a b ε b).natAbs else 0) hε)
  rw [if_pos ⟨hab, ha, hb⟩]

/-- Every pair has a small entry (`thm:L`, first step of the proof). -/
lemma small_pair (hdiag : ∀ a, M a a ≠ 0) (hfin : ¬ Z3NetF.PairInf M) (a b : Fin s)
    (hab : a ≠ b) : |M a b| ≤ Z3NetF.pairVal M ∨ |M b a| ≤ Z3NetF.pairVal M := by
  set K := Z3NetF.pairVal M
  have hneg : ∀ c, M c c ≤ -1 := by
    intro c
    have h1 : ¬ 0 < M c c := fun h => hfin (Or.inl ⟨c, h⟩)
    have := hdiag c; omega
  have hdK : ∀ c, -M c c ≤ K := by
    intro c; have := diag_le M c; have := hneg c; omega
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hy⟩ := hcon
  have hnf : ∀ ε ∈ ({1, -1} : Finset ℤ), 0 < Z3NetF.sig M a b ε a →
      ¬ 0 < ε * Z3NetF.sig M a b ε b := fun ε hε h1 h2 => hfin (Or.inr ⟨a, b, hab, ε, hε, h1, h2⟩)
  have hda := hdK a
  have hdb := hdK b
  have hna := hneg a
  have hnb := hneg b
  have hy' : K < M b a ∨ M b a < -(K : ℤ) := by
    rcases le_or_gt 0 (M b a) with h | h
    · rw [abs_of_nonneg h] at hy; left; exact hy
    · rw [abs_of_neg h] at hy; right; omega
  rcases le_or_gt 0 (M a b) with hx0 | hx0
  · -- `ε = 1`
    rw [abs_of_nonneg hx0] at hx
    have hσa : 0 < Z3NetF.sig M a b 1 a := by unfold Z3NetF.sig; omega
    have h1 := hnf 1 (by simp) hσa
    by_cases hlt : 1 * Z3NetF.sig M a b 1 b < 0
    · have h2 := config_le M a b hab 1 (by simp) hσa hlt
      simp only [Z3NetF.sig] at hlt h2 h1
      omega
    · simp only [Z3NetF.sig] at hlt h1
      omega
  · -- `ε = -1`
    rw [abs_of_neg hx0] at hx
    have hσa : 0 < Z3NetF.sig M a b (-1) a := by unfold Z3NetF.sig; omega
    have h1 := hnf (-1) (by simp) hσa
    by_cases hlt : (-1) * Z3NetF.sig M a b (-1) b < 0
    · have h2 := config_le M a b hab (-1) (by simp) hσa hlt
      simp only [Z3NetF.sig] at hlt h2 h1
      omega
    · simp only [Z3NetF.sig] at hlt h1
      omega

/-- Direction pigeonhole: rows with small nonzero entries on two columns, pairwise
non-proportional, number at most `2K²`. -/
lemma common_le (K : ℕ) (d d' : Fin s) (hdd : d ≠ d') (S : Finset (Fin s))
    (hS : ∀ c ∈ S, c ≠ d ∧ c ≠ d' ∧ M c d ≠ 0 ∧ M c d' ≠ 0 ∧ |M c d| ≤ K ∧ |M c d'| ≤ K)
    (hmin : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → M c d * M c' d' - M c d' * M c' d ≠ 0) :
    S.card ≤ 2 * K ^ 2 := by
  classical
  let f : Fin s → ℤ × ℤ := fun c => (|M c d|, (if 0 < M c d then 1 else -1) * M c d')
  let T : Finset (ℤ × ℤ) := (Icc (1 : ℤ) K) ×ˢ ((Icc (-(K : ℤ)) K).erase 0)
  have hT : T.card = 2 * K ^ 2 := by
    have c1 : (Icc (1 : ℤ) K).card = K := by simp
    have c2 : ((Icc (-(K : ℤ)) K).erase 0).card = 2 * K := by
      rw [card_erase_of_mem (mem_Icc.mpr ⟨by omega, by omega⟩), Int.card_Icc]
      omega
    simp only [T, card_product, c1, c2]; ring
  rw [← hT]
  refine card_le_card_of_injOn f ?_ ?_
  · intro c hc
    obtain ⟨-, -, h1, h2, h3, h4⟩ := hS c hc
    simp only [T, coe_product, coe_erase, coe_Icc, Set.mem_prod, Set.mem_sdiff, Set.mem_Icc,
      Set.mem_singleton_iff, f]
    refine ⟨⟨abs_pos.mpr h1, h3⟩, ⟨?_, ?_⟩, ?_⟩
    · split_ifs <;> rw [abs_le] at h4 <;> linarith [h4.1, h4.2]
    · split_ifs <;> rw [abs_le] at h4 <;> linarith [h4.1, h4.2]
    · split_ifs <;> simp [h2]
  · intro c hc c' hc' hf
    by_contra hcc
    apply hmin c hc c' hc' hcc
    simp only [f, Prod.mk.injEq] at hf
    obtain ⟨e1, e2⟩ := hf
    have hd := (hS c hc).2.2.1
    have hd' := (hS c' hc').2.2.1
    rcases lt_or_gt_of_ne hd with h | h <;> rcases lt_or_gt_of_ne hd' with h' | h'
    · rw [abs_of_neg h, abs_of_neg h'] at e1
      simp only [if_neg (not_lt.mpr h.le), if_neg (not_lt.mpr h'.le)] at e2
      have : M c d = M c' d := by linarith
      have : M c d' = M c' d' := by linarith
      rw [‹M c d = M c' d›, ‹M c d' = M c' d'›]; ring
    · rw [abs_of_neg h, abs_of_pos h'] at e1
      simp only [if_neg (not_lt.mpr h.le), if_pos h'] at e2
      have : M c d = -M c' d := by linarith
      have : M c d' = -M c' d' := by linarith
      rw [‹M c d = -M c' d›, ‹M c d' = -M c' d'›]; ring
    · rw [abs_of_pos h, abs_of_neg h'] at e1
      simp only [if_pos h, if_neg (not_lt.mpr h'.le)] at e2
      have : M c d = -M c' d := by linarith
      have : M c d' = -M c' d' := by linarith
      rw [‹M c d = -M c' d›, ‹M c d' = -M c' d'›]; ring
    · rw [abs_of_pos h, abs_of_pos h'] at e1
      simp only [if_pos h, if_pos h'] at e2
      have : M c d = M c' d := by linarith
      have : M c d' = M c' d' := by linarith
      rw [‹M c d = M c' d›, ‹M c d' = M c' d'›]; ring

/-- **The combinatorial core of `thm:L`.** -/
theorem L_core (hs : 4 ≤ s) (hoff : ∀ c d, c ≠ d → M c d ≠ 0)
    (hmin : ∀ c c' d d', c ≠ c' → d ≠ d' → c ≠ d → c ≠ d' → c' ≠ d → c' ≠ d' →
      M c d * M c' d' - M c d' * M c' d ≠ 0)
    (hdiag : ∀ a, M a a ≠ 0) (hfin : ¬ Z3NetF.PairInf M) :
    (s : ℤ) - 3 ≤ 8 * (Z3NetF.pairVal M : ℤ) ^ 2 := by
  classical
  set K := Z3NetF.pairVal M with hKdef
  let sm : Fin s → Fin s → Prop := fun c d => c ≠ d ∧ |M c d| ≤ K
  let D : Fin s → Finset (Fin s) := fun c => univ.filter (sm c)
  -- (1) every pair carries an arc
  have h1 : (s : ℤ) * (s - 1) ≤ 2 * ∑ c, ((D c).card : ℤ) := by
    have e : ∀ c, ((D c).card : ℤ) = ∑ d, (if sm c d then 1 else 0 : ℤ) := by
      intro c; simp only [D, card_filter]; push_cast; rfl
    simp only [e]
    have hsw : ∑ c, ∑ d, (if sm c d then 1 else 0 : ℤ) = ∑ c, ∑ d, (if sm d c then 1 else 0 : ℤ) :=
      Finset.sum_comm
    have : 2 * ∑ c, ∑ d, (if sm c d then 1 else 0 : ℤ) =
        ∑ c, ∑ d, ((if sm c d then 1 else 0 : ℤ) + (if sm d c then 1 else 0)) := by
      rw [two_mul]; nth_rewrite 2 [hsw]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => (Finset.sum_add_distrib).symm
    rw [this]
    have hle : ∀ c d, (if c ≠ d then 1 else 0 : ℤ) ≤
        (if sm c d then 1 else 0 : ℤ) + (if sm d c then 1 else 0) := by
      intro c d
      by_cases hcd : c = d
      · simp only [hcd, ne_eq, not_true_eq_false, if_false]
        split_ifs <;> norm_num
      · have hsm : sm c d ∨ sm d c := by
          rcases small_pair M hdiag hfin c d hcd with h | h
          · exact Or.inl ⟨hcd, h⟩
          · exact Or.inr ⟨Ne.symm hcd, h⟩
        rw [if_pos (show c ≠ d from hcd)]
        rcases hsm with h | h
        · rw [if_pos h]; split_ifs <;> norm_num
        · rw [if_pos h]; split_ifs <;> norm_num
    calc (s : ℤ) * (s - 1) = ∑ c : Fin s, ∑ d : Fin s, (if c ≠ d then 1 else 0 : ℤ) := by
          have : ∀ c : Fin s, ∑ d : Fin s, (if c ≠ d then 1 else 0 : ℤ) = s - 1 := by
            intro c
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
              mul_one]
            have : (univ.filter fun d : Fin s => c ≠ d) = univ.erase c := by
              ext d; simp [eq_comm]
            rw [this, card_erase_of_mem (mem_univ c), card_univ, Fintype.card_fin]
            push_cast [Nat.cast_sub (show 1 ≤ s by omega)]; ring
          simp only [this, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => hle c d
  -- (2) the pairs of columns
  have h2 : ∑ c, (((D c).card : ℤ) ^ 2 - (D c).card) ≤ 2 * (K : ℤ) ^ 2 * ((s : ℤ) * (s - 1)) := by
    have e1 : ∀ c, ((D c).card : ℤ) ^ 2 - (D c).card = ((D c).offDiag.card : ℤ) := by
      intro c
      rw [offDiag_card, Nat.cast_sub (Nat.le_mul_self _)]; push_cast; ring
    simp only [e1]
    have e2 : ∀ c, ((D c).offDiag.card : ℤ) =
        ∑ p ∈ (univ : Finset (Fin s)).offDiag, (if sm c p.1 ∧ sm c p.2 then 1 else 0 : ℤ) := by
      intro c
      rw [Finset.sum_boole]
      congr 2
      ext p
      simp only [D, mem_offDiag, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h3, h1, h2⟩
      · rintro ⟨h3, h1, h2⟩; exact ⟨h1, h2, h3⟩
    simp only [e2]
    rw [Finset.sum_comm]
    have hb : ∀ p ∈ (univ : Finset (Fin s)).offDiag,
        ∑ c, (if sm c p.1 ∧ sm c p.2 then 1 else 0 : ℤ) ≤ 2 * (K : ℤ) ^ 2 := by
      intro p hp
      rw [mem_offDiag] at hp
      rw [Finset.sum_boole]
      have := common_le M K p.1 p.2 hp.2.2 (univ.filter fun c => sm c p.1 ∧ sm c p.2)
        (fun c hc => by
          simp only [mem_filter, mem_univ, true_and, sm] at hc
          exact ⟨hc.1.1, hc.2.1, hoff c p.1 hc.1.1, hoff c p.2 hc.2.1, hc.1.2, hc.2.2⟩)
        (fun c hc c' hc' hcc => by
          simp only [mem_filter, mem_univ, true_and, sm] at hc hc'
          exact hmin c c' p.1 p.2 hcc hp.2.2 hc.1.1 hc.2.1 hc'.1.1 hc'.2.1)
      exact_mod_cast this
    calc ∑ p ∈ (univ : Finset (Fin s)).offDiag, ∑ c, (if sm c p.1 ∧ sm c p.2 then 1 else 0 : ℤ)
        ≤ ∑ p ∈ (univ : Finset (Fin s)).offDiag, 2 * (K : ℤ) ^ 2 := Finset.sum_le_sum hb
      _ = 2 * (K : ℤ) ^ 2 * ((s : ℤ) * (s - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, offDiag_card, card_univ, Fintype.card_fin,
          Nat.cast_sub (Nat.le_mul_self _)]
        push_cast; ring
  -- (3) Cauchy–Schwarz
  have h3 : (∑ c, ((D c).card : ℤ)) ^ 2 ≤ (s : ℤ) * ∑ c, ((D c).card : ℤ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin s)))
      (f := fun c => ((D c).card : ℤ))
    simpa using this
  set T := ∑ c, ((D c).card : ℤ)
  set Q := ∑ c, ((D c).card : ℤ) ^ 2
  have h2' : Q - T ≤ 2 * (K : ℤ) ^ 2 * ((s : ℤ) * (s - 1)) := by
    have : ∑ c, (((D c).card : ℤ) ^ 2 - (D c).card) = Q - T := by
      rw [Finset.sum_sub_distrib]
    rw [← this]; exact h2
  have hs' : (4 : ℤ) ≤ s := by exact_mod_cast hs
  have hA : 0 ≤ 2 * T - s * (s - 1) := by linarith
  have hB : 0 ≤ 2 * T + s * (s - 1) - 2 * s := by nlinarith
  have hprod := mul_nonneg hA hB
  have hmain : (s : ℤ) ^ 2 * (s - 1) * (s - 3) ≤ 8 * (K : ℤ) ^ 2 * ((s : ℤ) ^ 2 * (s - 1)) := by
    nlinarith
  have hpos : (0 : ℤ) < (s : ℤ) ^ 2 * (s - 1) := by
    have : (0 : ℤ) < s - 1 := by linarith
    positivity
  by_contra hcon
  push Not at hcon
  nlinarith

lemma pairVal_attained (hs : 0 < s) :
    (∃ a, Z3NetF.pairVal M = (M a a).natAbs) ∨
      ∃ a b, a ≠ b ∧ ∃ ε ∈ ({1, -1} : Finset ℤ), 0 < Z3NetF.sig M a b ε a ∧
        ε * Z3NetF.sig M a b ε b < 0 ∧ Z3NetF.pairVal M = (Z3NetF.sig M a b ε b).natAbs := by
  classical
  have hne : (univ : Finset (Fin s)).Nonempty := ⟨⟨0, hs⟩, mem_univ _⟩
  unfold Z3NetF.pairVal
  set A := univ.sup fun a => (M a a).natAbs
  set B := univ.sup fun a => univ.sup fun b => ({1, -1} : Finset ℤ).sup fun ε =>
    if a ≠ b ∧ 0 < Z3NetF.sig M a b ε a ∧ ε * Z3NetF.sig M a b ε b < 0 then
      (Z3NetF.sig M a b ε b).natAbs else 0
  rcases le_total B A with h | h
  · left
    rw [max_eq_left h]
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup univ hne (fun a => (M a a).natAbs)
    exact ⟨a, ha⟩
  · rcases Nat.eq_zero_or_pos B with hB | hB
    · left
      have : A = 0 := by omega
      rw [max_eq_right h, hB]
      obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup univ hne (fun a => (M a a).natAbs)
      exact ⟨a, by rw [← ha]; exact this.symm⟩
    · right
      rw [max_eq_right h]
      obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup univ hne (fun a => univ.sup fun b =>
        ({1, -1} : Finset ℤ).sup fun ε => if a ≠ b ∧ 0 < Z3NetF.sig M a b ε a ∧
          ε * Z3NetF.sig M a b ε b < 0 then (Z3NetF.sig M a b ε b).natAbs else 0)
      obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup univ hne (fun b =>
        ({1, -1} : Finset ℤ).sup fun ε => if a ≠ b ∧ 0 < Z3NetF.sig M a b ε a ∧
          ε * Z3NetF.sig M a b ε b < 0 then (Z3NetF.sig M a b ε b).natAbs else 0)
      obtain ⟨ε, hε, he⟩ := Finset.exists_mem_eq_sup ({1, -1} : Finset ℤ) (by simp) (fun ε =>
        if a ≠ b ∧ 0 < Z3NetF.sig M a b ε a ∧ ε * Z3NetF.sig M a b ε b < 0 then
          (Z3NetF.sig M a b ε b).natAbs else 0)
      have hBv : B = if a ≠ b ∧ 0 < Z3NetF.sig M a b ε a ∧ ε * Z3NetF.sig M a b ε b < 0 then
          (Z3NetF.sig M a b ε b).natAbs else 0 := by simp only [B]; rw [ha, hb, he]
      split_ifs at hBv with hc
      · exact ⟨a, b, hc.1, ε, hε, hc.2.1, hc.2.2, hBv⟩
      · omega

lemma pairVal_le (C : ℕ) (hC : ∀ c d, |M c d| ≤ C) : Z3NetF.pairVal M ≤ 2 * C := by
  unfold Z3NetF.pairVal
  apply max_le
  · refine Finset.sup_le fun a _ => ?_
    have h1 := hC a a
    have : (((M a a).natAbs : ℕ) : ℤ) ≤ 2 * C := by rw [← Int.abs_eq_natAbs]; linarith
    exact_mod_cast this
  · refine Finset.sup_le fun a _ => Finset.sup_le fun b _ => Finset.sup_le fun ε hε => ?_
    split_ifs
    · have h1 := hC b a; have h2 := hC b b
      simp only [mem_insert, mem_singleton] at hε
      have h3 : |Z3NetF.sig M a b ε b| ≤ 2 * C := by
        unfold Z3NetF.sig
        calc |M b a + ε * M b b| ≤ |M b a| + |ε * M b b| := abs_add_le _ _
          _ = |M b a| + |M b b| := by
              rw [abs_mul, show |ε| = 1 by rcases hε with rfl | rfl <;> simp, one_mul]
          _ ≤ 2 * C := by linarith
      have : (((Z3NetF.sig M a b ε b).natAbs : ℕ) : ℤ) ≤ 2 * C := by
        rw [← Int.abs_eq_natAbs]; exact h3
      exact_mod_cast this
    · omega

lemma Kpair_top (h : Z3NetF.PairInf M) : Z3NetF.Kpair M = ⊤ := by
  unfold Z3NetF.Kpair; rw [if_pos h]

lemma Kpair_fin (h : ¬ Z3NetF.PairInf M) : Z3NetF.Kpair M = (Z3NetF.pairVal M : ℕ∞) := by
  unfold Z3NetF.Kpair; rw [if_neg h]

lemma Kpair_eq_top_iff : Z3NetF.Kpair M = ⊤ ↔ Z3NetF.PairInf M := by
  constructor
  · intro h; by_contra h'; rw [Kpair_fin M h'] at h; exact ENat.coe_ne_top _ h
  · exact Kpair_top M

end core

theorem L_Kpair (hs : 4 ≤ s) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (hdiag : ∀ a, Z3NetF.Mt Φ a a ≠ 0) :
    Z3NetF.Kpair (Z3NetF.Mt Φ) = ⊤ ∨ ∃ K : ℕ, Z3NetF.Kpair (Z3NetF.Mt Φ) = K ∧
      Real.sqrt (((s : ℝ) - 3) / 8) ≤ K := by
  by_cases hP : Z3NetF.PairInf (Z3NetF.Mt Φ)
  · exact Or.inl (Kpair_top _ hP)
  · right
    refine ⟨Z3NetF.pairVal (Z3NetF.Mt Φ), Kpair_fin _ hP, ?_⟩
    have h := L_core (Z3NetF.Mt Φ) hs (fun c d hcd => Mt_ne_zero hq hk Φ hnet c d hcd)
      (fun c c' d d' h1 h2 h3 h4 h5 h6 => Mt_minor_ne_zero hq hk Φ hnet c c' d d' h1 h2 h3 h4 h5 h6)
      hdiag hP
    rw [Real.sqrt_le_left (by positivity)]
    have : ((s : ℤ) - 3 : ℝ) ≤ ((8 * (Z3NetF.pairVal (Z3NetF.Mt Φ) : ℤ) ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    linarith

theorem L_pm1 (hs : 5 ≤ s) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) :
    ¬ ∀ c d, c ≠ d → Z3NetF.Mt Φ c d = 1 ∨ Z3NetF.Mt Φ c d = -1 := by
  classical
  intro hall
  let d : Fin s := ⟨0, by omega⟩
  let d' : Fin s := ⟨1, by omega⟩
  have hdd : d ≠ d' := by simp [d, d', Fin.ext_iff]
  set S := univ.filter fun c : Fin s => c ≠ d ∧ c ≠ d'
  have hS : 3 ≤ S.card := by
    have : S = (univ.erase d).erase d' := by
      ext c; simp [S, and_comm]
    rw [this, card_erase_of_mem (by simp [Ne.symm hdd]), card_erase_of_mem (mem_univ _),
      card_univ, Fintype.card_fin]
    omega
  have hab : ∀ c, c ≠ d → c ≠ d' → ∀ e, e = d ∨ e = d' →
      Z3NetF.Mt Φ c e ≠ 0 ∧ |Z3NetF.Mt Φ c e| ≤ (1 : ℕ) := by
    intro c h1 h2 e he
    have hce : c ≠ e := by rcases he with rfl | rfl <;> assumption
    rcases hall c e hce with h | h <;> rw [h] <;> simp
  have := common_le (Z3NetF.Mt Φ) 1 d d' hdd S
    (fun c hc => by
      simp only [S, mem_filter, mem_univ, true_and] at hc
      obtain ⟨a1, a2⟩ := hab c hc.1 hc.2 d (Or.inl rfl)
      obtain ⟨b1, b2⟩ := hab c hc.1 hc.2 d' (Or.inr rfl)
      exact ⟨hc.1, hc.2, a1, b1, a2, b2⟩)
    (fun c hc c' hc' hcc => by
      simp only [S, mem_filter, mem_univ, true_and] at hc hc'
      exact Mt_minor_ne_zero hq hk Φ hnet c c' d d' hcc hdd hc.1 hc.2 hc'.1 hc'.2)
  omega

end ObsL

end

end Z3NetF.Proofs

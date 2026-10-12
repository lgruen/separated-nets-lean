/-
Proof module of entry Skel: `lem:skelnec` (pure-skeleton conditions (N1)-(N3)).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkNecBridge
public import Z3Net.FNie

@[expose] public section

/-!
# Entry Skel: `lem:skelnec`

The proof of the paper: a net has unit box minors (`lem:nie`), a skeleton graph form is a graph form
with depths `K = skDepth r k` (`SkNec.eq_graphGen_of_IsSkGF`), and by `lem:box` (`box_minor`) the
box minor for a depth vector `d` is `±` the determinant of the reduced box matrix.

* `SkNec.det_ne_zero_of_box`: for any depth vector `d` with `∑ d = m` and any enumerations of the
  under columns and over rows by `Fin n`, the matrix of offset entries is invertible.
* `SkNec.dvec K up down = K + up - down`: the depth vectors of the proofs.
* `SkNec.overEquiv`, `SkNec.underEquivJ`, `SkNec.underEquivE`: the enumerations used.
* `SkNec.single_under`: depth `k+1` on a set `I` of skeleton coordinates and `K_e - n` on one
  coordinate `e ∉ I`; gives (N2) and both halves of (N3).
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

namespace SkNec

variable {s : ℕ}

/-- The key consequence of `lem:nie` and `lem:box` for skeleton graph forms. -/
theorem det_ne_zero_of_box {p r k : ℕ} [Fact p.Prime] (hr : r ≤ s)
    (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p))
    (hC : Z3NetF.IsSkGF s r p k C)
    (hnet : Z3NetF.IsNet0 s p (s * k + r) (Z3NetF.digPoint p (s * k + r) C))
    (dv : Fin s → ℕ) (hdv : ∑ c, dv c = s * k + r) {n : ℕ}
    (eU : Fin n ≃ Z3NetF.UnderCols (Z3NetF.skDepth r k) dv)
    (eO : Fin n ≃ Z3NetF.OverRows (Z3NetF.skDepth r k) dv) :
    (Matrix.of fun a b : Fin n =>
      Z3NetF.ent (C (eO a).1.1) (Z3NetF.skDepth r k (eO a).1.1 + ((eO a).2 : ℕ))
        (Z3NetF.skOff r k (eU b).1.1 + (dv (eU b).1.1 + ((eU b).2 : ℕ)))).det ≠ 0 := by
  have hK := sum_skDepth (s := s) (r := r) k hr
  have hu := (nie_zmod p C).1 hnet dv hdv
  rw [eq_graphGen_of_IsSkGF hr C hC] at hu
  obtain ⟨-, hbm⟩ := box_minor (R := ZMod p) (Z3NetF.skDepth r k) dv hK hdv
  obtain ⟨ε, -, hdet⟩ := hbm (eU.symm.trans eO)
  rw [hdet] at hu
  have hne := (isUnit_of_mul_isUnit_right hu).ne_zero
  rw [← Matrix.det_submatrix_equiv_self eU] at hne
  set σ := eU.symm.trans eO with hσdef
  have hent : ∀ x y, Z3NetF.redBox (Z3NetF.skDepth r k) dv (phiOf r k C) σ x y =
      Z3NetF.ent (C (σ x).1.1) (Z3NetF.skDepth r k (σ x).1.1 + ((σ x).2 : ℕ))
        (Z3NetF.skOff r k y.1.1 + (dv y.1.1 + (y.2 : ℕ))) := by
    intro x y
    unfold Z3NetF.redBox
    rw [dif_pos (by
      have h1 := (σ x).2.isLt
      have h2 := le_of_sum dv hdv (σ x).1.1
      omega)]
    rfl
  have hσ : ∀ a, σ (eU a) = eO a := by intro a; simp [hσdef]
  convert hne using 2
  ext a b
  rw [Matrix.of_apply, Matrix.submatrix_apply, hent, hσ]

/-- The depth vectors of the proofs: `K + up - down`. -/
def dvec (K up down : Fin s → ℕ) (c : Fin s) : ℕ := K c + up c - down c

lemma sum_dvec {m : ℕ} (K up down : Fin s → ℕ) (hK : ∑ c, K c = m) (hdown : ∀ c, down c ≤ K c)
    (hsum : ∑ c, up c = ∑ c, down c) : ∑ c, dvec K up down c = m := by
  have h : ∀ c, dvec K up down c + down c = K c + up c := by
    intro c; have := hdown c; unfold dvec; omega
  have h2 : ∑ c, dvec K up down c + ∑ c, down c = ∑ c, K c + ∑ c, up c := by
    rw [← sum_add_distrib, ← sum_add_distrib]; exact sum_congr rfl (fun c _ => h c)
  omega

lemma up_ne_zero {K up down : Fin s → ℕ} {c : Fin s} (h : K c < dvec K up down c) : up c ≠ 0 := by
  unfold dvec at h; omega

lemma down_ne_zero {K up down : Fin s → ℕ} {c : Fin s} (h : dvec K up down c < K c) :
    down c ≠ 0 := by
  unfold dvec at h; omega

lemma sum_ind (S : Finset (Fin s)) : ∑ c, (if c ∈ S then 1 else 0 : ℕ) = S.card := by
  rw [Finset.sum_ite_mem, univ_inter, sum_const, smul_eq_mul, mul_one]

/-- Enumeration of the over rows when they are the single offset rows of the coordinates `I a`. -/
def overEquiv (K dv : Fin s → ℕ) {n : ℕ} (I : Fin n ↪ Fin s) (hI : ∀ a, dv (I a) = K (I a) + 1)
    (hcov : ∀ c, K c < dv c → ∃ a, I a = c) : Fin n ≃ Z3NetF.OverRows K dv :=
  Equiv.ofBijective
    (fun a => ⟨⟨I a, by have := hI a; omega⟩, ⟨0, show 0 < dv (I a) - K (I a) by
      have := hI a; omega⟩⟩)
    ⟨fun a a' h => I.injective (congrArg (fun x : Z3NetF.OverRows K dv => x.1.1) h), by
      rintro ⟨⟨c, hc⟩, l⟩
      obtain ⟨a, rfl⟩ := hcov c hc
      refine ⟨a, Sigma.ext rfl (heq_of_eq (Fin.ext ?_))⟩
      have h1 := l.isLt
      have h2 := hI a
      simp only at h1 ⊢
      omega⟩

lemma overEquiv_c (K dv : Fin s → ℕ) {n : ℕ} (I : Fin n ↪ Fin s) (hI) (hcov) (a : Fin n) :
    (overEquiv K dv I hI hcov a).1.1 = I a := rfl

lemma overEquiv_l (K dv : Fin s → ℕ) {n : ℕ} (I : Fin n ↪ Fin s) (hI) (hcov) (a : Fin n) :
    ((overEquiv K dv I hI hcov a).2 : ℕ) = 0 := rfl

/-- Enumeration of the under columns when they are the last levels of the coordinates `J b`. -/
def underEquivJ (K dv : Fin s → ℕ) {n : ℕ} (J : Fin n ↪ Fin s) (hJ : ∀ b, dv (J b) + 1 = K (J b))
    (hcov : ∀ c, dv c < K c → ∃ b, J b = c) : Fin n ≃ Z3NetF.UnderCols K dv :=
  Equiv.ofBijective
    (fun b => ⟨⟨J b, by have := hJ b; omega⟩, ⟨0, show 0 < K (J b) - dv (J b) by
      have := hJ b; omega⟩⟩)
    ⟨fun b b' h => J.injective (congrArg (fun x : Z3NetF.UnderCols K dv => x.1.1) h), by
      rintro ⟨⟨c, hc⟩, l⟩
      obtain ⟨b, rfl⟩ := hcov c hc
      refine ⟨b, Sigma.ext rfl (heq_of_eq (Fin.ext ?_))⟩
      have h1 := l.isLt
      have h2 := hJ b
      simp only at h1 ⊢
      omega⟩

lemma underEquivJ_c (K dv : Fin s → ℕ) {n : ℕ} (J : Fin n ↪ Fin s) (hJ) (hcov) (b : Fin n) :
    (underEquivJ K dv J hJ hcov b).1.1 = J b := rfl

lemma underEquivJ_l (K dv : Fin s → ℕ) {n : ℕ} (J : Fin n ↪ Fin s) (hJ) (hcov) (b : Fin n) :
    ((underEquivJ K dv J hJ hcov b).2 : ℕ) = 0 := rfl

/-- Enumeration of the under columns when they are the last `n` levels of one coordinate `e`,
in reverse order. -/
def underEquivE (K dv : Fin s → ℕ) {n : ℕ} (e : Fin s) (hE : dv e + n = K e) (hn : 0 < n)
    (hcov : ∀ c, dv c < K c → c = e) : Fin n ≃ Z3NetF.UnderCols K dv :=
  Equiv.ofBijective
    (fun b => ⟨⟨e, by omega⟩, ⟨n - 1 - (b : ℕ), show n - 1 - (b : ℕ) < K e - dv e by omega⟩⟩)
    ⟨fun b b' h => by
      have h1 := congrArg (fun x : Z3NetF.UnderCols K dv => (x.2 : ℕ)) h
      simp only at h1
      have := b.isLt; have := b'.isLt
      exact Fin.ext (by omega), by
      rintro ⟨⟨c, hc⟩, l⟩
      obtain rfl := hcov c hc
      have h1 := l.isLt
      refine ⟨⟨n - 1 - (l : ℕ), by simp only at h1; omega⟩, Sigma.ext rfl (heq_of_eq (Fin.ext ?_))⟩
      simp only at h1 ⊢
      omega⟩

lemma underEquivE_c (K dv : Fin s → ℕ) {n : ℕ} (e : Fin s) (hE) (hn) (hcov) (b : Fin n) :
    (underEquivE K dv e hE hn hcov b).1.1 = e := rfl

lemma underEquivE_l (K dv : Fin s → ℕ) {n : ℕ} (e : Fin s) (hE) (hn) (hcov) (b : Fin n) :
    ((underEquivE K dv e hE hn hcov b).2 : ℕ) = n - 1 - (b : ℕ) := rfl

lemma skDepth_skel {r k : ℕ} {c : Fin s} (h : r ≤ (c : ℕ)) : Z3NetF.skDepth r k c = k := by
  unfold Z3NetF.skDepth; rw [if_neg (by omega)]

lemma skDepth_full {r k : ℕ} {c : Fin s} (h : (c : ℕ) < r) : Z3NetF.skDepth r k c = k + 1 := by
  unfold Z3NetF.skDepth; rw [if_pos h]

/-- Depth `k + 1` on the skeleton coordinates `I a`, depth `K_e - n` on a coordinate `e ∉ I`:
the offsets of the skeleton digits on the last `n` levels of `e` form an invertible matrix. -/
theorem single_under {p r k : ℕ} [Fact p.Prime] (hr : r ≤ s)
    (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p))
    (hC : Z3NetF.IsSkGF s r p k C)
    (hnet : Z3NetF.IsNet0 s p (s * k + r) (Z3NetF.digPoint p (s * k + r) C)) (n : ℕ)
    (I : Fin n ↪ Fin s) (hI : ∀ a, r ≤ (I a : ℕ)) (e : Fin s) (heI : ∀ a, I a ≠ e)
    (hn : n ≤ Z3NetF.skDepth r k e) :
    (Matrix.of fun a b : Fin n =>
      Z3NetF.ent (C (I a)) k (Z3NetF.skOff r k (e : ℕ) + (Z3NetF.skDepth r k e - 1 - (b : ℕ)))).det
      ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [Matrix.det_isEmpty]; exact one_ne_zero
  set K := Z3NetF.skDepth (s := s) r k with hKdef
  let S := univ.map I
  have hS : ∀ c, c ∈ S ↔ ∃ a, I a = c := by intro c; simp [S]
  let up : Fin s → ℕ := fun c => if c ∈ S then 1 else 0
  let down : Fin s → ℕ := fun c => if c = e then n else 0
  let dv := dvec K up down
  have hK := sum_skDepth (s := s) (r := r) k hr
  have hdv : ∑ c, dv c = s * k + r := by
    refine sum_dvec K up down hK (fun c => ?_) ?_
    · simp only [down]; split_ifs with h
      · subst h; exact hn
      · exact Nat.zero_le _
    · simp only [up, down]
      rw [sum_ind, Finset.sum_ite_eq' univ e, if_pos (mem_univ _), card_map, card_univ,
        Fintype.card_fin]
  have hdvI : ∀ a, dv (I a) = K (I a) + 1 := by
    intro a
    have h1 : up (I a) = 1 := by simp only [up]; rw [if_pos ((hS _).2 ⟨a, rfl⟩)]
    have h2 : down (I a) = 0 := by simp only [down]; rw [if_neg (heI a)]
    simp only [dv, dvec, h1, h2]; omega
  have hdvE : dv e + n = K e := by
    have h1 : up e = 0 := by
      simp only [up]; rw [if_neg]; rw [hS]; rintro ⟨a, ha⟩; exact heI a ha
    have h2 : down e = n := by simp [down]
    simp only [dv, dvec, h1, h2]; omega
  have hcovO : ∀ c, K c < dv c → ∃ a, I a = c := by
    intro c hc
    have := up_ne_zero hc
    simp only [up] at this
    split_ifs at this with h
    · exact (hS c).1 h
    · exact absurd rfl this
  have hcovU : ∀ c, dv c < K c → c = e := by
    intro c hc
    have := down_ne_zero hc
    simp only [down] at this
    split_ifs at this with h
    · exact h
    · exact absurd rfl this
  have key := det_ne_zero_of_box hr C hC hnet dv hdv (underEquivE K dv e hdvE hn0 hcovU)
    (overEquiv K dv I hdvI hcovO)
  convert key using 2
  ext a b
  simp only [Matrix.of_apply, overEquiv_c, overEquiv_l, underEquivE_c, underEquivE_l]
  rw [skDepth_skel (hI a), Nat.add_zero]
  congr 2
  have := b.isLt
  omega

/-- **`lem:skelnec`(N1)** in the form used: depth `k + 1` on the skeleton coordinates `I a`,
depth `k` on the full coordinates `J b`. -/
theorem N1_aux {p r k : ℕ} [Fact p.Prime] (hr : r ≤ s)
    (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p))
    (hC : Z3NetF.IsSkGF s r p k C)
    (hnet : Z3NetF.IsNet0 s p (s * k + r) (Z3NetF.digPoint p (s * k + r) C)) (n : ℕ)
    (I J : Fin n ↪ Fin s) (hI : ∀ a, r ≤ (I a : ℕ)) (hJ : ∀ b, (J b : ℕ) < r) :
    (Matrix.of fun a b => Z3NetF.ent (C (I a)) k (Z3NetF.skOff r k (J b : ℕ) + k)).det ≠ 0 := by
  set K := Z3NetF.skDepth (s := s) r k with hKdef
  let S := univ.map I
  let T := univ.map J
  have hS : ∀ c, c ∈ S ↔ ∃ a, I a = c := by intro c; simp [S]
  have hT : ∀ c, c ∈ T ↔ ∃ b, J b = c := by intro c; simp [T]
  have hIJ : ∀ a b, I a ≠ J b := by
    intro a b h; have := hI a; have := hJ b; rw [h] at *; omega
  let up : Fin s → ℕ := fun c => if c ∈ S then 1 else 0
  let down : Fin s → ℕ := fun c => if c ∈ T then 1 else 0
  let dv := dvec K up down
  have hK := sum_skDepth (s := s) (r := r) k hr
  have hdv : ∑ c, dv c = s * k + r := by
    refine sum_dvec K up down hK (fun c => ?_) ?_
    · simp only [down]; split_ifs with h
      · obtain ⟨b, rfl⟩ := (hT c).1 h
        rw [hKdef, skDepth_full (hJ b)]; omega
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
    intro b
    have : K (J b) = k + 1 := by rw [hKdef]; exact skDepth_full (hJ b)
    simp only [dv, dvec, hupJ, hdownJ]; omega
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
  have key := det_ne_zero_of_box hr C hC hnet dv hdv (underEquivJ K dv J hdvJ hcovU)
    (overEquiv K dv I hdvI hcovO)
  convert key using 2
  ext a b
  simp only [Matrix.of_apply, overEquiv_c, overEquiv_l, underEquivJ_c, underEquivJ_l]
  rw [skDepth_skel (hI a), Nat.add_zero, Nat.add_zero]
  have := hdvJ b
  rw [hKdef, skDepth_full (hJ b)] at this
  congr 2
  omega

end SkNec

open SkNec

/-- **`lem:skelnec`(N1)**. -/
theorem skelnec_N1 (s r p k : ℕ) [Fact p.Prime] (hr : r ≤ s)
    (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p)) (hC : IsSkGF s r p k C)
    (hnet : IsNet0 s p (s * k + r) (digPoint p (s * k + r) C)) (n : ℕ) (I J : Fin n ↪ Fin s)
    (hI : ∀ a, r ≤ (I a : ℕ)) (hJ : ∀ b, (J b : ℕ) < r) :
    (Matrix.of fun a b => ent (C (I a)) k (skOff r k (J b : ℕ) + k)).det ≠ 0 :=
  N1_aux hr C hC hnet n I J hI hJ

/-- **`lem:skelnec`(N2)** (forced faults). -/
theorem skelnec_N2 (s r p k : ℕ) [Fact p.Prime] (hr : r ≤ s) (hk : 1 ≤ k)
    (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p)) (hC : IsSkGF s r p k C)
    (hnet : IsNet0 s p (s * k + r) (digPoint p (s * k + r) C)) (i j : Fin s) (hi : r ≤ (i : ℕ))
    (hj : r ≤ (j : ℕ)) (hij : i ≠ j) :
    ent (C i) k (skOff r k (j : ℕ) + (k - 1)) ≠ 0 := by
  let I : Fin 1 ↪ Fin s := ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩
  have h := single_under hr C hC hnet 1 I (fun _ => hi) j (fun _ => hij)
    (by rw [skDepth_skel hj]; exact hk)
  rw [Matrix.det_unique, skDepth_skel hj] at h
  exact h

/-- **`lem:skelnec`(N3)**, full coordinate. -/
theorem skelnec_N3_full (s r p k : ℕ) [Fact p.Prime] (hr : r ≤ s)
    (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p)) (hC : IsSkGF s r p k C)
    (hnet : IsNet0 s p (s * k + r) (digPoint p (s * k + r) C)) (n : ℕ) (hn : n ≤ k + 1)
    (I : Fin n ↪ Fin s) (hI : ∀ a, r ≤ (I a : ℕ)) (d : Fin s) (hd : (d : ℕ) < r) :
    (Matrix.of fun a b : Fin n => ent (C (I a)) k (skOff r k (d : ℕ) + (k - (b : ℕ)))).det ≠ 0 := by
  have h := single_under hr C hC hnet n I hI d
    (fun a h => by have := hI a; rw [h] at this; omega) (by rw [skDepth_full hd]; exact hn)
  simpa [skDepth_full hd] using h

/-- **`lem:skelnec`(N3)**, skeleton coordinate. -/
theorem skelnec_N3_skel (s r p k : ℕ) [Fact p.Prime] (hr : r ≤ s)
    (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p)) (hC : IsSkGF s r p k C)
    (hnet : IsNet0 s p (s * k + r) (digPoint p (s * k + r) C)) (n : ℕ) (hn : n ≤ k)
    (I : Fin n ↪ Fin s) (hI : ∀ a, r ≤ (I a : ℕ)) (e : Fin s) (he : r ≤ (e : ℕ))
    (heI : ∀ a, I a ≠ e) :
    (Matrix.of fun a b : Fin n => ent (C (I a)) k (skOff r k (e : ℕ) + (k - 1 - (b : ℕ)))).det ≠ 0 := by
  have h := single_under hr C hC hnet n I hI e heI (by rw [skDepth_skel he]; exact hn)
  simpa [skDepth_skel he] using h

end

end Z3NetF.Proofs

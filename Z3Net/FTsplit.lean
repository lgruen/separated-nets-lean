module
public import Z3Net.FTs

@[expose] public section

/-!
# Entry F, part 15: `lem:Tsplit` (box minors of the split frame)

The split box matrix is literally the Hermite matrix of the `2s` points `v_0, u_0, v_1, u_1, …`
with multiplicities `min(d_c, k)`, `(d_c - k)_+` (the row blocks line up because the prefix sums
agree, `pre_split2`); the converse of the net criterion uses the boxes `(k, …, k)`, one coordinate
`k+1` and one `k-1`, and two `k+1`, two `k-1` (`s ≥ 4`).
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s : ℕ}

/-- Multiplicities of the Hermite matrix of the split frame (with the empty `∞`-jet last). -/
abbrev splitD (k : ℕ) (d : Fin s → ℕ) : Fin (2 * s + 1) → ℕ := hα (Z3NetF.splitMult k d) 0

lemma splitD_even (k : ℕ) (d : Fin s → ℕ) (c : ℕ) (hc : c < s) :
    splitD k d ⟨2 * c, by omega⟩ = min (d ⟨c, hc⟩) k := by
  simp only [splitD, hα, Z3NetF.splitMult]
  rw [dif_pos (by omega)]
  simp only [Nat.mul_mod_right, if_true]
  congr 3
  simp

lemma splitD_odd (k : ℕ) (d : Fin s → ℕ) (c : ℕ) (hc : c < s) :
    splitD k d ⟨2 * c + 1, by omega⟩ = d ⟨c, hc⟩ - k := by
  simp only [splitD, hα, Z3NetF.splitMult]
  rw [dif_pos (by omega)]
  have h1 : (2 * c + 1) % 2 = 1 := by omega
  have h2 : (2 * c + 1) / 2 = c := by omega
  simp only [h1, h2]
  simp

lemma pre_split2 (k : ℕ) (d : Fin s → ℕ) : ∀ c, c ≤ s → pre (splitD k d) (2 * c) = pre d c
  | 0, _ => by simp [pre, Z3NetU.Proofs.pre]
  | c + 1, hc => by
    have ih := pre_split2 k d c (by omega)
    have e1 := Z3NetU.Proofs.pre_succ (splitD k d) ⟨2 * c, by omega⟩
    have e2 := Z3NetU.Proofs.pre_succ (splitD k d) ⟨2 * c + 1, by omega⟩
    have e3 := Z3NetU.Proofs.pre_succ d ⟨c, by omega⟩
    simp only at e1 e2 e3
    rw [splitD_even k d c (by omega)] at e1
    rw [splitD_odd k d c (by omega)] at e2
    show Z3NetU.Proofs.pre (splitD k d) (2 * (c + 1)) = Z3NetU.Proofs.pre d (c + 1)
    rw [show 2 * (c + 1) = 2 * c + 1 + 1 by ring, e2, e1, e3]
    simp only [pre] at ih
    rw [ih]
    have := min_le_left (d ⟨c, by omega⟩) k
    have := min_le_right (d ⟨c, by omega⟩) k
    rcases le_total (d ⟨c, by omega⟩) k with h | h
    · rw [min_eq_left h, Nat.sub_eq_zero_of_le h]; ring
    · rw [min_eq_right h]; omega

lemma splitD_sum (k : ℕ) (d : Fin s → ℕ) (hd : ∑ c, d c = s * k) :
    ∑ P, Z3NetF.splitMult k d P + 0 = s * k := by
  rw [← hα_sum (Z3NetF.splitMult k d) 0]
  have h1 := Z3NetU.Proofs.pre_eq_sum (splitD k d) (2 * s + 1)
  have h2 : univ.filter (fun t : Fin (2 * s + 1) => (t : ℕ) < 2 * s + 1) = univ := by
    ext t; have := t.isLt; simp only [mem_filter, mem_univ, true_and, iff_true]; omega
  rw [h2] at h1
  rw [← h1]
  have e := Z3NetU.Proofs.pre_succ (splitD k d) ⟨2 * s, by omega⟩
  simp only at e
  rw [e]
  have hz : splitD k d ⟨2 * s, by omega⟩ = 0 := by
    simp [splitD, hα]
  rw [hz, add_zero]
  have := pre_split2 k d s le_rfl
  simp only [pre] at this
  rw [this, ← hd]
  have h3 := Z3NetU.Proofs.pre_eq_sum d s
  have h4 : univ.filter (fun t : Fin s => (t : ℕ) < s) = univ := by
    ext t; have := t.isLt; simp only [mem_filter, mem_univ, true_and, iff_true]; omega
  rw [h4] at h3
  exact h3

theorem split_box_eq (k : ℕ) (u v : Fin s → R) (d : Fin s → ℕ) (hd : ∑ c, d c = s * k) :
    Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) d =
      Z3NetF.hermiteMat (s * k) (Z3NetF.splitPts u v) (Z3NetF.splitMult k d) 0 := by
  rw [hermite_eq_frame]
  have hD : ∑ P, splitD k d P = s * k := by rw [hα_sum]; exact splitD_sum k d hd
  ext r l
  obtain ⟨c, i, hi, hr, -⟩ := box_row_cover d hd r
  have hr' : r = ⟨pre d c + i, pre_add_lt d hd c i hi⟩ := Fin.ext hr
  rw [hr', box_row_pre _ d hd c i hi]
  have hpre := pre_split2 k d c (le_of_lt c.isLt)
  by_cases hik : i < k
  · have hm : i < splitD k d ⟨2 * c, by omega⟩ := by
      rw [splitD_even k d c c.isLt]; exact lt_min hi hik
    have hpos : pre d c + i = pre (splitD k d) (⟨2 * c, by omega⟩ : Fin (2 * s + 1)) + i := by
      rw [show ((⟨2 * c, by omega⟩ : Fin (2 * s + 1)) : ℕ) = 2 * (c : ℕ) from rfl, hpre]
    have e := box_row_pre (Z3NetF.frameRead (s * k) (Fin.last (2 * s)) (hx (Z3NetF.splitPts u v)))
      (splitD k d) hD ⟨2 * c, by omega⟩ i hm
    have hrr : (⟨pre d c + i, pre_add_lt d hd c i hi⟩ : Fin (s * k)) =
        ⟨pre (splitD k d) (⟨2 * c, by omega⟩ : Fin (2 * s + 1)) + i, pre_add_lt _ hD _ i hm⟩ :=
      Fin.ext hpos
    rw [hrr, e]
    have hne : (⟨2 * (c : ℕ), by omega⟩ : Fin (2 * s + 1)) ≠ Fin.last (2 * s) := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp only [Z3NetF.frameRead, Z3NetF.splitRead, Z3NetF.readAt, hne, if_false, Fin.val_mk, hik,
      if_true]
    simp [hx, Z3NetF.splitPts]
  · have hdk : k < d c := by omega
    have hm : i - k < splitD k d ⟨2 * c + 1, by omega⟩ := by
      rw [splitD_odd k d c c.isLt, Fin.eta]; omega
    have e1 := Z3NetU.Proofs.pre_succ (splitD k d) ⟨2 * c, by omega⟩
    simp only at e1
    rw [splitD_even k d c c.isLt, Fin.eta] at e1
    have hpos : pre d c + i = pre (splitD k d) (⟨2 * c + 1, by omega⟩ : Fin (2 * s + 1)) + (i - k) := by
      show pre d c + i = Z3NetU.Proofs.pre (splitD k d) (2 * c + 1) + (i - k)
      rw [e1]
      simp only [pre] at hpre
      rw [hpre, min_eq_right (le_of_lt hdk)]
      simp only [pre]; omega
    have e := box_row_pre (Z3NetF.frameRead (s * k) (Fin.last (2 * s)) (hx (Z3NetF.splitPts u v)))
      (splitD k d) hD ⟨2 * c + 1, by omega⟩ (i - k) hm
    have hrr : (⟨pre d c + i, pre_add_lt d hd c i hi⟩ : Fin (s * k)) =
        ⟨pre (splitD k d) (⟨2 * c + 1, by omega⟩ : Fin (2 * s + 1)) + (i - k), pre_add_lt _ hD _ _ hm⟩ :=
      Fin.ext hpos
    rw [hrr, e]
    have hne : (⟨2 * (c : ℕ) + 1, by omega⟩ : Fin (2 * s + 1)) ≠ Fin.last (2 * s) := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp only [Z3NetF.frameRead, Z3NetF.splitRead, Z3NetF.readAt, hne, if_false, Fin.val_mk, hik]
    have h1 : (2 * (c : ℕ) + 1) % 2 = 1 := by omega
    have h2 : (2 * (c : ℕ) + 1) / 2 = c := by omega
    have h3 : ¬ (2 * s ≤ 2 * (c : ℕ) + 1) := by have := c.isLt; omega
    simp [hx, Z3NetF.splitPts, h1, h2, h3]

theorem Tsplit_minor_core (k : ℕ) (u v : Fin s → R) (d : Fin s → ℕ) (hd : ∑ c, d c = s * k) :
    Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) d =
        Z3NetF.hermiteMat (s * k) (Z3NetF.splitPts u v) (Z3NetF.splitMult k d) 0 ∧
      ((Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) d).det = ∏ Q : Fin (2 * s), ∏ P : Fin (2 * s),
          (if P < Q then (Z3NetF.splitPts u v Q - Z3NetF.splitPts u v P) ^
            (Z3NetF.splitMult k d P * Z3NetF.splitMult k d Q) else 1) ∨
        (Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) d).det = -∏ Q : Fin (2 * s), ∏ P : Fin (2 * s),
          (if P < Q then (Z3NetF.splitPts u v Q - Z3NetF.splitPts u v P) ^
            (Z3NetF.splitMult k d P * Z3NetF.splitMult k d Q) else 1)) := by
  refine ⟨split_box_eq k u v d hd, ?_⟩
  rw [split_box_eq k u v d hd]
  exact hermite_det_core _ _ _ (splitD_sum k d hd)

/-! ## The net criterion -/

lemma splitMult_even (k : ℕ) (d : Fin s → ℕ) (c : Fin s) :
    Z3NetF.splitMult k d ⟨2 * c, by omega⟩ = min (d c) k := by
  simp [Z3NetF.splitMult]

lemma splitMult_odd (k : ℕ) (d : Fin s → ℕ) (c : Fin s) :
    Z3NetF.splitMult k d ⟨2 * c + 1, by omega⟩ = d c - k := by
  have h1 : (2 * (c : ℕ) + 1) % 2 = 1 := by omega
  have h2 : (2 * (c : ℕ) + 1) / 2 = c := by omega
  simp [Z3NetF.splitMult, h1, h2]

lemma fin2_decomp (P : Fin (2 * s)) :
    ∃ c : Fin s, (P = ⟨2 * c, by omega⟩ ∨ P = ⟨2 * c + 1, by omega⟩) := by
  refine ⟨⟨(P : ℕ) / 2, Nat.div_lt_of_lt_mul P.isLt⟩, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one P with h | h
  · left; ext; simp; omega
  · right; ext; simp; omega

/-- Sum of a depth vector `k + [t ∈ A] - [t ∈ B]`. -/
lemma sum_adjust (k : ℕ) (hk : 1 ≤ k) (A B : Finset (Fin s)) (hAB : Disjoint A B) (hcard : A.card = B.card) :
    ∑ t, (if t ∈ A then k + 1 else if t ∈ B then k - 1 else k) = s * k := by
  have hz : ∀ t, ((if t ∈ A then k + 1 else if t ∈ B then k - 1 else k : ℕ) : ℤ) =
      (k : ℤ) + (if t ∈ A then 1 else 0) - (if t ∈ B then 1 else 0) := by
    intro t
    by_cases ha : t ∈ A
    · have hb : t ∉ B := Finset.disjoint_left.mp hAB ha
      simp [ha, hb]
    · by_cases hb : t ∈ B
      · simp [ha, hb]; omega
      · simp [ha, hb]
  have : ((∑ t, (if t ∈ A then k + 1 else if t ∈ B then k - 1 else k) : ℕ) : ℤ) = ((s * k : ℕ) : ℤ) := by
    rw [Nat.cast_sum, Nat.cast_mul, Finset.sum_congr rfl (fun t _ => hz t), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, card_univ, Fintype.card_fin, Finset.sum_boole, Finset.sum_boole]
    have e1 : (univ.filter (fun t : Fin s => t ∈ A)) = A := by ext; simp
    have e2 : (univ.filter (fun t : Fin s => t ∈ B)) = B := by ext; simp
    rw [e1, e2, hcard, nsmul_eq_mul]
    ring
  exact_mod_cast this

lemma exists_box (hs : 4 ≤ s) (k : ℕ) (hk : 1 ≤ k) (P Q : Fin (2 * s)) (hPQ : P ≠ Q) :
    ∃ d : Fin s → ℕ, ∑ c, d c = s * k ∧ 1 ≤ Z3NetF.splitMult k d P ∧ 1 ≤ Z3NetF.splitMult k d Q := by
  classical
  -- a coordinate outside a given pair, and two outside a pair
  have hout : ∀ a b : Fin s, ∃ e e' : Fin s, e ≠ e' ∧ e ≠ a ∧ e ≠ b ∧ e' ≠ a ∧ e' ≠ b := by
    intro a b
    have hc : 2 ≤ ((univ.erase a).erase b).card := by
      have h1 := Finset.card_erase_le (s := univ.erase a) (a := b)
      have h2 : (univ.erase a).card = s - 1 := by rw [card_erase_of_mem (mem_univ _)]; simp
      have h3 := Finset.pred_card_le_card_erase (s := univ.erase a) (a := b)
      omega
    obtain ⟨e, he, e', he', hee'⟩ := Finset.one_lt_card.mp (by omega : 1 < ((univ.erase a).erase b).card)
    simp only [mem_erase, mem_univ, and_true] at he he'
    exact ⟨e, e', hee', he.2, he.1, he'.2, he'.1⟩
  obtain ⟨c0, hP⟩ := fin2_decomp P
  obtain ⟨c1, hQ⟩ := fin2_decomp Q
  -- the depth vectors
  let dA : Fin s → Finset (Fin s) → Finset (Fin s) → ℕ := fun t A B =>
    if t ∈ A then k + 1 else if t ∈ B then k - 1 else k
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · -- `v_c0 ≡ v_c1`: the box `(k, …, k)`
    refine ⟨fun _ => k, by simp, ?_, ?_⟩ <;> rw [splitMult_even] <;> simp <;> omega
  · -- `v_c0 ≡ u_c1`
    obtain ⟨e, -, -, he0, he1, -, -⟩ := hout c0 c1
    refine ⟨fun t => dA t {c1} {e}, sum_adjust k hk _ _ (by simp [Ne.symm he1]) (by simp), ?_, ?_⟩
    · rw [splitMult_even]; simp only [dA, mem_singleton]; split_ifs <;> omega
    · rw [splitMult_odd]; simp only [dA, mem_singleton, if_true]; omega
  · -- `u_c0 ≡ v_c1`
    obtain ⟨e, -, -, he0, he1, -, -⟩ := hout c0 c1
    refine ⟨fun t => dA t {c0} {e}, sum_adjust k hk _ _ (by simp [Ne.symm he0]) (by simp), ?_, ?_⟩
    · rw [splitMult_odd]; simp only [dA, mem_singleton, if_true]; omega
    · rw [splitMult_even]; simp only [dA, mem_singleton]; split_ifs <;> omega
  · -- `u_c0 ≡ u_c1`, `c0 ≠ c1`
    have hc : c0 ≠ c1 := by
      intro h; apply hPQ; subst h; rfl
    obtain ⟨e, e', hee', he0, he1, he0', he1'⟩ := hout c0 c1
    refine ⟨fun t => dA t {c0, c1} {e, e'}, sum_adjust k hk _ _ ?_ ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro t ht ht'
      simp only [mem_insert, mem_singleton] at ht ht'
      rcases ht with rfl | rfl <;> rcases ht' with h | h <;> simp_all
    · rw [card_pair hc, card_pair hee']
    · rw [splitMult_odd]; simp only [dA, mem_insert, mem_singleton, true_or, if_true]; omega
    · rw [splitMult_odd]; simp only [dA, mem_insert, mem_singleton, or_true, if_true]; omega

lemma split_reduce (q : ℕ) (u v : Fin s → ℚ) (P : Fin (2 * s)) :
    Z3NetF.splitPts (fun c => Z3NetF.ratRed q (u c)) (fun c => Z3NetF.ratRed q (v c)) P =
      Z3NetF.ratRed q (Z3NetF.splitPts u v P) := by
  unfold Z3NetF.splitPts; split_ifs <;> rfl

theorem Tsplit_net_iff_core {q k : ℕ} (hs : 4 ≤ s) (hk : 1 ≤ k) (hq : 2 ≤ q) (u v : Fin s → ℚ)
    (hden : ∀ c, Nat.Coprime (u c).den q ∧ Nat.Coprime (v c).den q) :
    Z3NetF.IsNet0 s q (s * k) (Z3NetF.digPoint q (s * k)
        (Z3NetF.splitRead (s * k) k (fun c => Z3NetF.ratRed q (u c)) (fun c => Z3NetF.ratRed q (v c)))) ↔
      ∀ p : ℕ, p.Prime → p ∣ q → Function.Injective (fun P => Z3NetF.ratRed p (Z3NetF.splitPts u v P)) := by
  haveI : NeZero q := ⟨by omega⟩
  rw [nie_zmod]
  set xq := Z3NetF.splitPts (fun c => Z3NetF.ratRed q (u c)) (fun c => Z3NetF.ratRed q (v c)) with hxq
  have hden' : ∀ P, Nat.Coprime (Z3NetF.splitPts u v P).den q := by
    intro P; unfold Z3NetF.splitPts; split_ifs
    · exact (hden _).2
    · exact (hden _).1
  have himg : ∀ p (hp : p.Prime) (hpq : p ∣ q) P, ZMod.castHom hpq (ZMod p) (xq P) =
      Z3NetF.ratRed p (Z3NetF.splitPts u v P) := by
    intro p hp hpq P
    rw [hxq, split_reduce]
    exact castHom_ratRed q p hp hpq _ (hden' P)
  constructor
  · intro H p hp hpq P Q heq
    by_contra hPQ
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    obtain ⟨d, hd, hαP, hαQ⟩ := exists_box hs k hk P Q hPQ
    have hu := H d hd
    set f := ZMod.castHom hpq (ZMod p)
    have hfu : IsUnit (f (Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k (fun c => Z3NetF.ratRed q (u c))
        (fun c => Z3NetF.ratRed q (v c))) d).det) := hu.map f
    have heq' : f (xq P) = f (xq Q) := by rw [himg p hp hpq, himg p hp hpq]; exact heq
    have hz : f (∏ Q' : Fin (2 * s), ∏ P' : Fin (2 * s), (if P' < Q' then (xq Q' - xq P') ^
        (Z3NetF.splitMult k d P' * Z3NetF.splitMult k d Q') else 1)) = 0 := by
      rw [map_prod]
      rcases lt_or_gt_of_ne hPQ with hlt | hgt
      · apply Finset.prod_eq_zero (mem_univ Q)
        rw [map_prod]
        apply Finset.prod_eq_zero (mem_univ P)
        rw [if_pos hlt, map_pow, map_sub, heq', sub_self]
        apply zero_pow
        exact Nat.pos_iff_ne_zero.mp (Nat.mul_pos hαP hαQ)
      · apply Finset.prod_eq_zero (mem_univ P)
        rw [map_prod]
        apply Finset.prod_eq_zero (mem_univ Q)
        rw [if_pos hgt, map_pow, map_sub, heq', sub_self]
        apply zero_pow
        exact Nat.pos_iff_ne_zero.mp (Nat.mul_pos hαQ hαP)
    rcases (Tsplit_minor_core (R := ZMod q) k (fun c => Z3NetF.ratRed q (u c))
      (fun c => Z3NetF.ratRed q (v c)) d hd).2 with h | h <;> rw [h] at hfu
    · rw [hz] at hfu; exact not_isUnit_zero hfu
    · rw [map_neg, hz, neg_zero] at hfu; exact not_isUnit_zero hfu
  · intro H d hd
    have hfac : ∀ P Q : Fin (2 * s), P ≠ Q → IsUnit (xq Q - xq P) := by
      intro P Q hPQ
      apply zmod_isUnit_of_primes
      intro p hp hpq
      rw [map_sub, himg p hp hpq, himg p hp hpq, sub_ne_zero]
      exact fun h => hPQ (H p hp hpq h.symm)
    have hprod : IsUnit (∏ Q' : Fin (2 * s), ∏ P' : Fin (2 * s), (if P' < Q' then (xq Q' - xq P') ^
        (Z3NetF.splitMult k d P' * Z3NetF.splitMult k d Q') else 1)) := by
      rw [IsUnit.prod_univ_iff]; intro Q'
      rw [IsUnit.prod_univ_iff]; intro P'
      split_ifs with h
      · exact (hfac P' Q' (ne_of_lt h)).pow _
      · exact isUnit_one
    rcases (Tsplit_minor_core (R := ZMod q) k (fun c => Z3NetF.ratRed q (u c))
      (fun c => Z3NetF.ratRed q (v c)) d hd).2 with h | h <;> rw [h]
    · exact hprod
    · exact hprod.neg

theorem Tsplit_prime_bound_core {p : ℕ} (u v : Fin s → ℚ)
    (h : Function.Injective (fun P => Z3NetF.ratRed p (Z3NetF.splitPts u v P))) (hp : p.Prime) :
    2 * s ≤ p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have := Fintype.card_le_of_injective _ h
  simpa [ZMod.card] using this

end

end Z3NetF.Proofs

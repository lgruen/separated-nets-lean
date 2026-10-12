/-
Proof module of entry Skel: `rem:codes` (Construction A facts).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.SkelDefs

@[expose] public section

/-!
# Entry Skel: `rem:codes`

* `codes_linf`, `codes_l2`: `Λ_A = C_A + p ℤ^s` (Construction A). The centred lift
  (`ZMod.valMinAbs`) of a residue is its shortest lift (`ZMod.natAbs_min_of_le_div_two`), and a
  nonzero multiple of `p` has absolute value at least `p`.
* `codes_mds`: every square submatrix of `A` is invertible iff `C_A = {(x, A x)}` is MDS
  (MacWilliams–Sloane, Ch. 11, Thm. 8), by linear algebra over the field `ZMod p`.
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

namespace SkCodes

variable {p : ℕ}

lemma lift_le [NeZero p] (a : ℤ) : ((a : ZMod p).valMinAbs).natAbs ≤ a.natAbs :=
  ZMod.natAbs_min_of_le_div_two p _ a (ZMod.coe_valMinAbs _) (ZMod.natAbs_valMinAbs_le _)

lemma ge_of_zero (a : ℤ) (h : (a : ZMod p) = 0) (ha : a ≠ 0) : p ≤ a.natAbs := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h1 : p ∣ a.natAbs := Int.natCast_dvd.mp h
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha) h1

lemma mulVec_cast {ℓ r : ℕ} (A : Matrix (Fin ℓ) (Fin r) (ZMod p)) (x : Fin r → ℤ) (z : Fin ℓ → ℤ)
    (hz : ∀ i, (z i : ZMod p) = ∑ d, A i d * (x d : ZMod p)) (i : Fin ℓ) :
    (A *ᵥ (fun d => (x d : ZMod p))) i = (z i : ZMod p) := by
  rw [hz i]; rfl

lemma ne_zero_lift {r : ℕ} (y : Fin r → ZMod p) (hy : y ≠ 0) :
    (fun d => (y d).valMinAbs) ≠ 0 := by
  intro h
  apply hy
  funext d
  have := congrFun h d
  simpa [ZMod.valMinAbs_eq_zero] using this

/-- If the residues of `x` vanish, then so do those of `z`, and some entry is a nonzero multiple
of `p`. -/
lemma big_entry {ℓ r : ℕ} (A : Matrix (Fin ℓ) (Fin r) (ZMod p)) (x : Fin r → ℤ) (z : Fin ℓ → ℤ)
    (hz : ∀ i, (z i : ZMod p) = ∑ d, A i d * (x d : ZMod p)) (hne : ¬(x = 0 ∧ z = 0))
    (hy : (fun d => (x d : ZMod p)) = 0) :
    (∃ d, x d ≠ 0 ∧ p ≤ (x d).natAbs) ∨ (∃ i, z i ≠ 0 ∧ p ≤ (z i).natAbs) := by
  have hx0 : ∀ d, (x d : ZMod p) = 0 := fun d => congrFun hy d
  have hz0 : ∀ i, (z i : ZMod p) = 0 := by
    intro i; rw [hz i]; simp [hx0]
  by_cases hx : x = 0
  · have hz' : z ≠ 0 := fun h => hne ⟨hx, h⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz'
    exact Or.inr ⟨i, hi, ge_of_zero _ (hz0 i) hi⟩
  · obtain ⟨d, hd⟩ := Function.ne_iff.mp hx
    exact Or.inl ⟨d, hd, ge_of_zero _ (hx0 d) hd⟩

end SkCodes

open SkCodes

/-- **`rem:codes`**, maximum norm. -/
theorem codes_linf {ℓ r : ℕ} (p : ℕ) [Fact p.Prime] (hr : 1 ≤ r)
    (A : Matrix (Fin ℓ) (Fin r) (ZMod p)) :
    (∀ (x : Fin r → ℤ) (z : Fin ℓ → ℤ), (∀ i, (z i : ZMod p) = ∑ d, A i d * (x d : ZMod p)) →
        ¬(x = 0 ∧ z = 0) → ∃ y : Fin r → ZMod p, y ≠ 0 ∧
          cwInf p A y ≤ max (univ.sup fun d => (x d).natAbs) (univ.sup fun i => (z i).natAbs)) ∧
      ∀ y : Fin r → ZMod p, y ≠ 0 → (∀ y' : Fin r → ZMod p, y' ≠ 0 → cwInf p A y ≤ cwInf p A y') →
        ∃ (x : Fin r → ℤ) (z : Fin ℓ → ℤ), (∀ i, (z i : ZMod p) = ∑ d, A i d * (x d : ZMod p)) ∧
          ¬(x = 0 ∧ z = 0) ∧
          max (univ.sup fun d => (x d).natAbs) (univ.sup fun i => (z i).natAbs) = cwInf p A y := by
  refine ⟨fun x z hz hne => ?_, fun y hy _ => ?_⟩
  · by_cases hy : (fun d => (x d : ZMod p)) = 0
    · -- every entry is `≡ 0`; some entry is at least `p`
      refine ⟨Pi.single ⟨0, hr⟩ 1, by simp, ?_⟩
      have hsmall : cwInf p A (Pi.single ⟨0, hr⟩ 1) ≤ p / 2 := by
        unfold cwInf
        exact max_le (Finset.sup_le fun d _ => ZMod.natAbs_valMinAbs_le _)
          (Finset.sup_le fun i _ => ZMod.natAbs_valMinAbs_le _)
      have hbig : p ≤ max (univ.sup fun d => (x d).natAbs) (univ.sup fun i => (z i).natAbs) := by
        rcases big_entry A x z hz hne hy with ⟨d, -, hd⟩ | ⟨i, -, hi⟩
        · exact le_max_of_le_left (le_trans hd (Finset.le_sup (f := fun d => (x d).natAbs)
            (mem_univ d)))
        · exact le_max_of_le_right (le_trans hi (Finset.le_sup (f := fun i => (z i).natAbs)
            (mem_univ i)))
      have : p / 2 ≤ p := Nat.div_le_self _ _
      omega
    · refine ⟨_, hy, ?_⟩
      unfold cwInf
      refine max_le_max (Finset.sup_mono_fun fun d _ => lift_le _)
        (Finset.sup_mono_fun fun i _ => ?_)
      rw [mulVec_cast A x z hz i]
      exact lift_le _
  · refine ⟨fun d => (y d).valMinAbs, fun i => ((A *ᵥ y) i).valMinAbs, fun i => ?_,
      fun h => ne_zero_lift y hy h.1, rfl⟩
    simp only [ZMod.coe_valMinAbs]
    rfl

/-- **`rem:codes`**, Euclidean norm. -/
theorem codes_l2 {ℓ r : ℕ} (p : ℕ) [Fact p.Prime] (A : Matrix (Fin ℓ) (Fin r) (ZMod p)) :
    (∀ (x : Fin r → ℤ) (z : Fin ℓ → ℤ), (∀ i, (z i : ZMod p) = ∑ d, A i d * (x d : ZMod p)) →
        ¬(x = 0 ∧ z = 0) →
        p ^ 2 ≤ ∑ d, (x d).natAbs ^ 2 + ∑ i, (z i).natAbs ^ 2 ∨
          ∃ y : Fin r → ZMod p, y ≠ 0 ∧ cwEuc p A y ≤ ∑ d, (x d).natAbs ^ 2 + ∑ i, (z i).natAbs ^ 2) ∧
      (1 ≤ ℓ + r → ∃ (x : Fin r → ℤ) (z : Fin ℓ → ℤ),
        (∀ i, (z i : ZMod p) = ∑ d, A i d * (x d : ZMod p)) ∧ ¬(x = 0 ∧ z = 0) ∧
          ∑ d, (x d).natAbs ^ 2 + ∑ i, (z i).natAbs ^ 2 = p ^ 2) ∧
      ∀ y : Fin r → ZMod p, ∃ (x : Fin r → ℤ) (z : Fin ℓ → ℤ),
        (∀ i, (z i : ZMod p) = ∑ d, A i d * (x d : ZMod p)) ∧ (y ≠ 0 → ¬(x = 0 ∧ z = 0)) ∧
          ∑ d, (x d).natAbs ^ 2 + ∑ i, (z i).natAbs ^ 2 = cwEuc p A y := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨fun x z hz hne => ?_, fun hlr => ?_, fun y => ?_⟩
  · by_cases hy : (fun d => (x d : ZMod p)) = 0
    · left
      rcases big_entry A x z hz hne hy with ⟨d, -, hd⟩ | ⟨i, -, hi⟩
      · have h1 : (x d).natAbs ^ 2 ≤ ∑ d, (x d).natAbs ^ 2 :=
          Finset.single_le_sum (f := fun d => (x d).natAbs ^ 2) (fun _ _ => Nat.zero_le _)
            (mem_univ d)
        have h2 : p ^ 2 ≤ (x d).natAbs ^ 2 := Nat.pow_le_pow_left hd 2
        omega
      · have h1 : (z i).natAbs ^ 2 ≤ ∑ i, (z i).natAbs ^ 2 :=
          Finset.single_le_sum (f := fun i => (z i).natAbs ^ 2) (fun _ _ => Nat.zero_le _)
            (mem_univ i)
        have h2 : p ^ 2 ≤ (z i).natAbs ^ 2 := Nat.pow_le_pow_left hi 2
        omega
    · right
      refine ⟨_, hy, ?_⟩
      unfold cwEuc
      refine Nat.add_le_add (Finset.sum_le_sum fun d _ => Nat.pow_le_pow_left (lift_le _) 2)
        (Finset.sum_le_sum fun i _ => ?_)
      rw [mulVec_cast A x z hz i]
      exact Nat.pow_le_pow_left (lift_le _) 2
  · by_cases hr : 0 < r
    · refine ⟨Pi.single ⟨0, hr⟩ (p : ℤ), 0, fun i => ?_, fun h => ?_, ?_⟩
      · have h0 : ∀ d, ((Pi.single (⟨0, hr⟩ : Fin r) (p : ℤ) : Fin r → ℤ) d : ZMod p) = 0 := by
          intro d
          by_cases hd : d = ⟨0, hr⟩
          · subst hd; simp
          · simp [hd]
        simp [h0]
      · have := congrFun h.1 ⟨0, hr⟩
        simp at this
        omega
      · rw [Finset.sum_eq_single (⟨0, hr⟩ : Fin r)]
        · simp
        · intro d _ hd; simp [hd]
        · simp
    · have hl : 0 < ℓ := by omega
      refine ⟨0, Pi.single ⟨0, hl⟩ (p : ℤ), fun i => ?_, fun h => ?_, ?_⟩
      · by_cases hi : i = ⟨0, hl⟩
        · subst hi; simp
        · simp [hi]
      · have := congrFun h.2 ⟨0, hl⟩
        simp at this
        omega
      · rw [Finset.sum_eq_single (⟨0, hl⟩ : Fin ℓ)]
        · simp
        · intro i _ hi; simp [hi]
        · simp
  · refine ⟨fun d => (y d).valMinAbs, fun i => ((A *ᵥ y) i).valMinAbs, fun i => ?_,
      fun hy h => ne_zero_lift y hy h.1, rfl⟩
    simp only [ZMod.coe_valMinAbs]
    rfl

namespace SkCodes

variable {p : ℕ}

lemma sum_orderEmb {β : Type*} [AddCommMonoid β] {r : ℕ} (S : Finset (Fin r)) (f : Fin r → β) :
    ∑ b : Fin S.card, f ((S.orderEmbOfFin rfl).toEmbedding b) = ∑ d ∈ S, f d := by
  rw [← Finset.sum_map univ (S.orderEmbOfFin rfl).toEmbedding f]
  congr 1
  apply Finset.coe_injective
  rw [Finset.coe_map, coe_univ, Set.image_univ]
  exact Finset.range_orderEmbOfFin S rfl

end SkCodes

/-- **`rem:codes`(a)**: (N1) iff `C_A` is MDS. -/
theorem codes_mds {ℓ r : ℕ} (p : ℕ) [Fact p.Prime] (A : Matrix (Fin ℓ) (Fin r) (ZMod p)) :
    (∀ (n : ℕ) (I : Fin n ↪ Fin ℓ) (J : Fin n ↪ Fin r),
        (Matrix.of fun a b => A (I a) (J b)).det ≠ 0) ↔
      ∀ y : Fin r → ZMod p, y ≠ 0 → ℓ + 1 ≤ cwHam p A y := by
  constructor
  · intro h y hy
    by_contra hlt
    replace hlt := Nat.lt_of_not_le hlt
    unfold cwHam at hlt
    set S := univ.filter fun d => y d ≠ 0 with hSdef
    set W := univ.filter fun i => (A *ᵥ y) i ≠ 0 with hWdef
    set Z := univ.filter fun i => (A *ᵥ y) i = 0 with hZdef
    have hZW : Z.card + W.card = ℓ := by
      have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin ℓ)))
        (p := fun i => (A *ᵥ y) i = 0)
      rw [card_univ, Fintype.card_fin] at this
      exact this
    have hSZ : S.card ≤ Z.card := by omega
    obtain ⟨I', hI'Z, hI'card⟩ := Finset.exists_subset_card_eq hSZ
    let J := (S.orderEmbOfFin rfl).toEmbedding
    let I := (I'.orderEmbOfFin hI'card).toEmbedding
    apply h S.card I J
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    obtain ⟨d0, hd0⟩ := Function.ne_iff.mp hy
    have hd0S : d0 ∈ S := by simp only [hSdef, mem_filter, mem_univ, true_and]; exact hd0
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨d0, hd0S⟩
    refine ⟨fun b => y (J b), fun hv => ?_, ?_⟩
    · have hJ0 : J ⟨0, hpos⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl _
      have := congrFun hv ⟨0, hpos⟩
      simp only [Pi.zero_apply] at this
      simp [hSdef, this] at hJ0
    · funext a
      have hIa : I a ∈ Z := hI'Z (Finset.orderEmbOfFin_mem I' hI'card a)
      simp only [hZdef, mem_filter, mem_univ, true_and] at hIa
      rw [Pi.zero_apply, ← hIa]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [sum_orderEmb S (fun d => A (I a) d * y d)]
      exact Finset.sum_filter_of_ne fun d _ h => right_ne_zero_of_mul h
  · intro h n I J hdet
    obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    let y : Fin r → ZMod p := fun d => ∑ b, if J b = d then v b else 0
    have hyJ : ∀ b, y (J b) = v b := by
      intro b
      simp only [y, J.injective.eq_iff]
      rw [Finset.sum_ite_eq' univ b, if_pos (mem_univ _)]
    have hy : y ≠ 0 := by
      obtain ⟨b, hb⟩ := Function.ne_iff.mp hv0
      intro h0; apply hb; rw [← hyJ b, h0]; rfl
    have hAy : ∀ i, (A *ᵥ y) i = ∑ b, A i (J b) * v b := by
      intro i
      simp only [Matrix.mulVec, dotProduct, y, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_ite_eq univ (J b), if_pos (mem_univ _)]
    have hAyI : ∀ a, (A *ᵥ y) (I a) = 0 := by
      intro a; rw [hAy]; exact congrFun hMv a
    have h1 : (univ.filter fun d => y d ≠ 0).card ≤ n := by
      calc (univ.filter fun d => y d ≠ 0).card ≤ (univ.map J).card := by
            apply Finset.card_le_card
            intro d hd
            simp only [mem_filter, mem_univ, true_and] at hd
            simp only [mem_map, mem_univ, true_and]
            by_contra hJ
            replace hJ := not_exists.mp hJ
            apply hd
            simp only [y]
            exact Finset.sum_eq_zero fun b _ => if_neg (hJ b)
        _ = n := by simp
    have h2 : (univ.filter fun i => (A *ᵥ y) i ≠ 0).card ≤ ℓ - n := by
      calc (univ.filter fun i => (A *ᵥ y) i ≠ 0).card ≤ (univ.map I)ᶜ.card := by
            apply Finset.card_le_card
            intro i hi
            simp only [mem_filter, mem_univ, true_and] at hi
            simp only [mem_compl, mem_map, mem_univ, true_and, not_exists]
            intro a ha
            exact hi (ha ▸ hAyI a)
        _ = ℓ - n := by simp [Finset.card_compl]
    have hnl : n ≤ ℓ := by simpa using Fintype.card_le_of_embedding I
    have := h y hy
    unfold cwHam at this
    omega

end

end Z3NetF.Proofs

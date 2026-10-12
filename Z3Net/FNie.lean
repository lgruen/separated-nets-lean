module
public import Z3Net.FBasic

@[expose] public section

/-!
# Entry F, part 2: `lem:nie` (box criterion, both directions)

The map `v ↦ (⌊X_c(v)/q^(m-d_c)⌋)_c` factors as `ψ ∘ (box matrix ·)`, where `ψ` reads the stacked
leading digits as base-`q` numbers; `ψ` is a bijection, so every box holds exactly one point iff
the box matrix is bijective on `R^m`, i.e. (finite ring) iff its determinant is a unit.
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

variable {R : Type*} [CommRing R] {q s m : ℕ}

lemma coordE_eq (e : R ≃ Fin q) (C : Matrix (Fin m) (Fin m) R) (v : Fin m → R) :
    Z3NetF.coordE e C v = Z3Net.Proofs.digSum q m (fun j => ((e ((C *ᵥ v) j) : Fin q) : ℕ)) := rfl

lemma q_pos (e : R ≃ Fin q) : 0 < q := by
  have := (e 0).isLt; omega

/-- Leading `d` digits of a coordinate. -/
lemma coordE_div (e : R ≃ Fin q) (C : Matrix (Fin m) (Fin m) R) (v : Fin m → R) (d : ℕ)
    (hd : d ≤ m) :
    Z3NetF.coordE e C v / q ^ (m - d) =
      Z3Net.Proofs.digSum q d (fun j => ((e ((C *ᵥ v) ⟨j, lt_of_lt_of_le j.isLt hd⟩) : Fin q) : ℕ)) := by
  rw [coordE_eq, digSum_div_prefix q (q_pos e) m _ (fun j => (e _).isLt) d hd]

/-- The reading `ψ` of a stacked digit vector: block `c` (rows `pre d c + i`, `i < d c`) as a
base-`q` number with `d c` digits. -/
def psiE (e : R ≃ Fin q) (d : Fin s → ℕ) (hd : ∑ c, d c = m) (t : Fin m → R) (c : Fin s) : ℕ :=
  Z3Net.Proofs.digSum q (d c) (fun i => ((e (t ⟨pre d c + i, pre_add_lt d hd c i i.isLt⟩) : Fin q) : ℕ))

lemma psiE_lt (e : R ≃ Fin q) (d : Fin s → ℕ) (hd : ∑ c, d c = m) (t : Fin m → R) (c : Fin s) :
    psiE e d hd t c < q ^ d c :=
  Z3Net.Proofs.digSum_lt q _ _ (fun _ => (e _).isLt)

lemma psiE_inj (e : R ≃ Fin q) (d : Fin s → ℕ) (hd : ∑ c, d c = m) (t t' : Fin m → R)
    (h : ∀ c, psiE e d hd t c = psiE e d hd t' c) : t = t' := by
  funext r
  obtain ⟨c, i, hi, hr, -⟩ := box_row_cover d hd r
  have := digSum_inj q (q_pos e) (d c) _ _ (fun _ => (e _).isLt) (fun _ => (e _).isLt) (h c)
  have h2 := congrFun this ⟨i, hi⟩
  have h3 : e (t r) = e (t' r) := by
    have hr' : r = ⟨pre d c + i, pre_add_lt d hd c i hi⟩ := Fin.ext hr
    rw [hr']; exact Fin.ext h2
  exact e.injective h3

/-- The box quotient map `φ` equals `ψ ∘ (box matrix ·)`. -/
lemma phi_eq (e : R ≃ Fin q) (C : Fin s → Matrix (Fin m) (Fin m) R) (d : Fin s → ℕ)
    (hd : ∑ c, d c = m) (v : Fin m → R) (c : Fin s) :
    Z3NetF.coordE e (C c) v / q ^ (m - d c) = psiE e d hd (Z3NetF.boxMatrix C d *ᵥ v) c := by
  rw [coordE_div e (C c) v (d c) (le_of_sum d hd c), psiE]
  congr 1
  funext i
  have h : (Z3NetF.boxMatrix C d *ᵥ v) ⟨pre d c + i, pre_add_lt d hd c i i.isLt⟩ =
      (C c *ᵥ v) ⟨i, lt_of_lt_of_le i.isLt (le_of_sum d hd c)⟩ := by
    change Z3NetF.boxMatrix C d ⟨_, _⟩ ⬝ᵥ v = C c ⟨i, _⟩ ⬝ᵥ v
    rw [box_row_pre C d hd c i i.isLt]
  rw [h]

lemma isUnit_iff_bij [Finite R] (A : Matrix (Fin m) (Fin m) R) :
    IsUnit A.det ↔ Function.Bijective A.mulVec := by
  classical
  constructor
  · intro h
    have hinj := Z3Net.Proofs.mulVec_injective_of_isUnit_det A h
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩
  · intro h
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.mulVec_surjective_iff_isUnit.mp h.2

/-- **`lem:nie`**, one shape. -/
theorem nie_box (e : R ≃ Fin q) (C : Fin s → Matrix (Fin m) (Fin m) R) (d : Fin s → ℕ)
    (hd : ∑ c, d c = m) : Z3NetF.BoxExact e C d ↔ IsUnit (Z3NetF.boxMatrix C d).det := by
  classical
  have : Finite R := Finite.of_equiv (Fin q) e.symm
  rw [isUnit_iff_bij]
  set B := Z3NetF.boxMatrix C d
  -- `ψ` as a map into the boxes
  let Ψ : (Fin m → R) → ((c : Fin s) → Fin (q ^ d c)) := fun t c => ⟨psiE e d hd t c, psiE_lt e d hd t c⟩
  have hΨinj : Function.Injective Ψ := fun t t' h =>
    psiE_inj e d hd t t' fun c => congrArg Fin.val (congrFun h c)
  have hcard : Nat.card (Fin m → R) = Nat.card ((c : Fin s) → Fin (q ^ d c)) := by
    rw [Nat.card_fun, Nat.card_congr e, Nat.card_pi]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum, hd]
  have hΨbij : Function.Bijective Ψ := by
    exact (Function.Injective.bijective_of_nat_card_le hΨinj hcard.ge)
  have hφ : ∀ v c, Z3NetF.coordE e (C c) v / q ^ (m - d c) = (Ψ (B *ᵥ v) c : ℕ) :=
    fun v c => phi_eq e C d hd v c
  constructor
  · intro hBE
    have hsurj : Function.Surjective B.mulVec := by
      intro t
      obtain ⟨v, hv, -⟩ := hBE (fun c => (Ψ t c : ℕ)) (fun c => (Ψ t c).isLt)
      refine ⟨v, hΨinj ?_⟩
      funext c; exact Fin.ext ((hφ v c).symm.trans (hv c))
    exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  · intro hB a ha
    obtain ⟨t, ht⟩ := hΨbij.2 (fun c => ⟨a c, ha c⟩)
    obtain ⟨v, hv⟩ := hB.2 t
    refine ⟨v, fun c => ?_, fun w hw => ?_⟩
    · rw [hφ, hv, ht]
    · apply hB.1
      apply hΨinj
      funext c
      apply Fin.ext
      have h1 := hφ w c
      rw [hw c] at h1
      rw [← h1, hv, ht]

theorem nie_net (e : R ≃ Fin q) (C : Fin s → Matrix (Fin m) (Fin m) R) :
    Z3NetF.IsNet0E e C ↔ ∀ d : Fin s → ℕ, ∑ c, d c = m → IsUnit (Z3NetF.boxMatrix C d).det :=
  forall_congr' fun d => forall_congr' fun hd => nie_box e C d hd

theorem nie_net_field {K : Type*} [Field K] (e : K ≃ Fin q) (C : Fin s → Matrix (Fin m) (Fin m) K) :
    Z3NetF.IsNet0E e C ↔ ∀ d : Fin s → ℕ, ∑ c, d c = m → (Z3NetF.boxMatrix C d).det ≠ 0 := by
  rw [nie_net]
  exact forall_congr' fun d => forall_congr' fun hd => isUnit_iff_ne_zero

/-- The standard digits of `ℤ/qℤ`. -/
def zmodE (q : ℕ) [NeZero q] : ZMod q ≃ Fin q where
  toFun x := ⟨x.val, ZMod.val_lt x⟩
  invFun i := ((i : ℕ) : ZMod q)
  left_inv x := ZMod.natCast_zmod_val x
  right_inv i := Fin.ext (ZMod.val_cast_of_lt i.isLt)

lemma isNet0_iff_E (q : ℕ) [NeZero q] (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) :
    Z3NetF.IsNet0 s q m (Z3NetF.digPoint q m C) ↔ Z3NetF.IsNet0E (zmodE q) C := Iff.rfl

theorem nie_zmod (q : ℕ) [NeZero q] (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) :
    Z3NetF.IsNet0 s q m (Z3NetF.digPoint q m C) ↔
      ∀ d : Fin s → ℕ, ∑ c, d c = m → IsUnit (Z3NetF.boxMatrix C d).det := by
  rw [isNet0_iff_E]; exact nie_net _ C

end

end Z3NetF.Proofs

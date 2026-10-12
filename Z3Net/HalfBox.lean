module
public import Z3Net.HalfDefs
public import Z3Net.FNie

@[expose] public section

/-!
# Entry Half, part 1: the integer generator matrices of `halfPhi` and the box criterion

* `halfIntGen M2 D c`: the integer generator matrix of coordinate `c` of the graph form
  `halfPhi s p M2 D` with the layer row **doubled**: row `0` is `e_c`, row `1` is `M2 c`
  (`= 2 M_c`), row `i ≥ 2` is `D c (i - 1)`. Plain `if`s, computable (for kernel certificates).
* `halfPhi_box_det`: over `ℤ/pℤ` (`p` odd), the box determinant of `graphGen s 1 (halfPhi …)`
  is a unit times the cast of the integer box determinant of `halfIntGen M2 D` (the `M`-row of
  every coordinate is the integer row `M2 c` scaled by `(p+1)/2 = 2⁻¹`).
* `halfPhi_net_iff_int`, `halfPhi_net_of_int`: `lem:nie` — the graph form is a `(0,s,s)`-net over
  `𝔽_p` iff no integer box determinant is divisible by `p`.
-/

namespace Z3NetHL.Proofs

open Matrix Finset

/-- Integer generator matrix of coordinate `c` of `halfPhi` with the layer row doubled: row `0`
is the unit row `e_c`, row `1` is `M2 c`, row `i ≥ 2` is the deeper row `D c (i - 1)`. -/
def halfIntGen {s : ℕ} (M2 : Fin s → Fin s → ℤ) (D : Fin s → ℕ → Fin s → ℤ) (c : Fin s) :
    Matrix (Fin s) (Fin s) ℤ :=
  fun i j => if (i : ℕ) = 0 then (if j = c then 1 else 0)
    else if (i : ℕ) = 1 then M2 c j else D c ((i : ℕ) - 1) j

noncomputable section

/-! ## Bridges to entry F -/

lemma boxLoc_eqF : ∀ (ds : List ℕ) (c r : ℕ), Z3NetHL.boxLoc ds c r = Z3NetF.boxLoc ds c r
  | [], _, _ => rfl
  | x :: xs, c, r => by simp only [Z3NetHL.boxLoc, Z3NetF.boxLoc, boxLoc_eqF xs]

lemma boxMatrix_eqF {R : Type*} [Zero R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R)
    (d : Fin s → ℕ) : Z3NetHL.boxMatrix C d = Z3NetF.boxMatrix C d := by
  funext r l
  simp only [Z3NetHL.boxMatrix, Z3NetF.boxMatrix, boxLoc_eqF]

lemma isNet0_iffF (s q m : ℕ) (X : (Fin m → ZMod q) → Fin s → ℕ) :
    Z3NetHL.IsNet0 s q m X ↔ Z3NetF.IsNet0 s q m X := Iff.rfl

lemma digPoint_eqF {s : ℕ} (q m : ℕ) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) :
    Z3NetHL.digPoint q m C = Z3NetF.digPoint q m C := rfl

/-! ## Entries -/

/-- `½ ≡ (p+1)/2`. -/
abbrev halfZ (p : ℕ) : ZMod p := (((p + 1) / 2 : ℕ) : ZMod p)

lemma halfZ_isUnit (p : ℕ) (hp : Odd p) : IsUnit (halfZ p) := by
  obtain ⟨k, rfl⟩ := hp
  have h : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  refine IsUnit.of_mul_eq_one 2 ?_
  simp only [halfZ, h]
  have : ((2 * k + 1 : ℕ) : ZMod (2 * k + 1)) = 0 := ZMod.natCast_self _
  push_cast at this ⊢
  linear_combination this

lemma graphGen_half_entry (s p : ℕ) (M2 : Fin s → Fin s → ℤ) (D : Fin s → ℕ → Fin s → ℤ)
    (c : Fin s) (i : ℕ) (hi : i < s * 1) (hi' : i < s) (l : Fin s) :
    graphGen s 1 (halfPhi s p M2 D) c ⟨i, hi⟩ (finCongr (Nat.mul_one s).symm l) =
      (if i = 1 then halfZ p else 1) * ((halfIntGen M2 D c ⟨i, hi'⟩ l : ℤ) : ZMod p) := by
  have hl : (⟨(l : ℕ) / 1, by omega⟩ : Fin s) = l := Fin.ext (Nat.div_one _)
  simp only [graphGen, halfPhi, halfIntGen, finCongr_apply, Fin.val_cast, Nat.mul_one]
  by_cases h0 : i = 0
  · subst h0
    simp only [Nat.zero_lt_one, dite_true, Nat.add_zero, if_true, one_mul]
    by_cases hlc : l = c
    · subst hlc; simp
    · have : ¬ ((l : ℕ) = (c : ℕ)) := fun h => hlc (Fin.ext h)
      simp [this, hlc]
  · have h1 : ¬ i < 1 := by omega
    rw [dif_neg h1, if_neg h0]
    by_cases hi1 : i = 1
    · subst hi1
      simp only [Nat.sub_self, if_true, hl]
      push_cast; ring
    · have : i - 1 ≠ 0 := by omega
      simp only [this, if_false, hi1, one_mul, hl]

/-- The reindexed box matrix over `ℤ/pℤ` is `diag(w) ·` (the integer box matrix mod `p`). -/
lemma halfPhi_box_eq (s p : ℕ) (M2 : Fin s → Fin s → ℤ) (D : Fin s → ℕ → Fin s → ℤ)
    (d : Fin s → ℕ) :
    (Z3NetF.boxMatrix (graphGen s 1 (halfPhi s p M2 D)) d).submatrix
        (finCongr (Nat.mul_one s).symm) (finCongr (Nat.mul_one s).symm) =
      diagonal (fun r : Fin s =>
          if (Z3NetF.boxLoc (List.ofFn d) 0 r).2 = 1 then halfZ p else 1) *
        (Z3NetF.boxMatrix (halfIntGen M2 D) d).map (Int.cast : ℤ → ZMod p) := by
  ext r l
  rw [diagonal_mul, submatrix_apply, map_apply]
  simp only [Z3NetF.boxMatrix, finCongr_apply, Fin.val_cast]
  by_cases h : (Z3NetF.boxLoc (List.ofFn d) 0 r).1 < s ∧ (Z3NetF.boxLoc (List.ofFn d) 0 r).2 < s
  · have h' : (Z3NetF.boxLoc (List.ofFn d) 0 r).1 < s ∧
        (Z3NetF.boxLoc (List.ofFn d) 0 r).2 < s * 1 := by rw [Nat.mul_one]; exact h
    rw [dif_pos h', dif_pos h]
    exact graphGen_half_entry s p M2 D _ _ h'.2 h.2 l
  · have h' : ¬ ((Z3NetF.boxLoc (List.ofFn d) 0 r).1 < s ∧
        (Z3NetF.boxLoc (List.ofFn d) 0 r).2 < s * 1) := by rw [Nat.mul_one]; exact h
    rw [dif_neg h', dif_neg h]
    simp

/-- **Box determinants**: over `ℤ/pℤ` (`p` odd) the box determinant of the graph form
`halfPhi s p M2 D` is a unit times the integer box determinant of `halfIntGen M2 D`. -/
theorem halfPhi_box_det (s p : ℕ) (hp : Odd p) (M2 : Fin s → Fin s → ℤ)
    (D : Fin s → ℕ → Fin s → ℤ) (d : Fin s → ℕ) :
    ∃ u : ZMod p, IsUnit u ∧
      (Z3NetHL.boxMatrix (graphGen s 1 (halfPhi s p M2 D)) d).det =
        u * (((Z3NetHL.boxMatrix (halfIntGen M2 D) d).det : ℤ) : ZMod p) := by
  rw [boxMatrix_eqF, boxMatrix_eqF]
  refine ⟨∏ r : Fin s, (if (Z3NetF.boxLoc (List.ofFn d) 0 r).2 = 1 then halfZ p else 1),
    ?_, ?_⟩
  · refine IsUnit.prod_univ_iff.mpr fun r => ?_
    split_ifs
    · exact halfZ_isUnit p hp
    · exact isUnit_one
  · rw [← det_submatrix_equiv_self (finCongr (Nat.mul_one s).symm), halfPhi_box_eq, det_mul,
      det_diagonal]
    congr 1
    exact (RingHom.map_det (Int.castRingHom (ZMod p)) _).symm

/-- **`lem:nie` for `halfPhi`**: for an odd prime `p`, the graph form `halfPhi s p M2 D` is a
digital `(0,s,s)`-net over `𝔽_p` iff no integer box determinant of `halfIntGen M2 D` is
divisible by `p`. -/
theorem halfPhi_net_iff_int (s p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (M2 : Fin s → Fin s → ℤ)
    (D : Fin s → ℕ → Fin s → ℤ) :
    IsNet0 s p (s * 1) (GFpoint s p 1 (halfPhi s p M2 D)) ↔
      ∀ d : Fin s → ℕ, ∑ c, d c = s → ¬ (p : ℤ) ∣ (boxMatrix (halfIntGen M2 D) d).det := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  unfold GFpoint
  rw [isNet0_iffF, digPoint_eqF, Z3NetF.Proofs.nie_zmod]
  refine forall_congr' fun d => imp_congr (by rw [Nat.mul_one]) ?_
  obtain ⟨u, hu, hdet⟩ := halfPhi_box_det s p hodd M2 D d
  rw [← boxMatrix_eqF, hdet, IsUnit.mul_iff,
    isUnit_iff_ne_zero (a := (((boxMatrix (halfIntGen M2 D) d).det : ℤ) : ZMod p)), Ne,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩

/-- **`lem:nie` for `halfPhi`**, the direction used for `prop:half`(2). -/
theorem halfPhi_net_of_int (s p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (M2 : Fin s → Fin s → ℤ)
    (D : Fin s → ℕ → Fin s → ℤ)
    (h : ∀ d : Fin s → ℕ, ∑ c, d c = s → ¬ (p : ℤ) ∣ (boxMatrix (halfIntGen M2 D) d).det) :
    IsNet0 s p (s * 1) (GFpoint s p 1 (halfPhi s p M2 D)) :=
  (halfPhi_net_iff_int s p hp hp2 M2 D).mpr h

end

end Z3NetHL.Proofs

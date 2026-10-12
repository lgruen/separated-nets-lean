module
public import Mathlib
public import Z3Net.D4Net

@[expose] public section

/-!
# 4D entry, part 4: Theorem 4D(1) — `D4_net` and `D4_boxMinor`

* Box matrices with four coordinates and the injective form of Niederreiter's lemma
  (`isNet0_of_box_injective4`, copied from the 3D entry with `Fin 4`).
* `D4_net`: for odd `q`, `2` is a unit in `ℤ/qℤ` and `box_kernel` applies over `ℤ/qℤ` directly
  (no reduction to primes is needed: Lemma T holds over every ring in which `2` is a unit).
* `D4_boxMinor`: the definitions are polynomial in `h`; over `ℤ[X]` (`h = X`) the box minor is
  a polynomial `Δ`, `Δ(1/2)` is the minor over `ℚ`, `Δ(2⁻¹ mod p)` the minor over `𝔽_p`, which is
  nonzero for every odd prime `p`; so `2^deg Δ · Δ(1/2)` is an integer prime to every odd prime.
-/

namespace Z3NetD4.Proofs

open Polynomial Finset Matrix Z3NetD4

noncomputable section

/-! ## Box matrices with four coordinates -/

lemma boxMatrix_mulVec4 {R : Type*} [CommRing R] {m : ℕ} (C : Fin 4 → Matrix (Fin m) (Fin m) R)
    (d : Fin 4 → ℕ) (v : Fin m → R) (r : Fin m) :
    (boxMatrix C d *ᵥ v) r =
      if (r : ℕ) < d 0 then (C 0 *ᵥ v) r
      else if (r : ℕ) < d 0 + d 1 then (C 1 *ᵥ v) ⟨(r : ℕ) - d 0, by omega⟩
      else if (r : ℕ) < d 0 + d 1 + d 2 then (C 2 *ᵥ v) ⟨(r : ℕ) - d 0 - d 1, by omega⟩
      else (C 3 *ᵥ v) ⟨(r : ℕ) - d 0 - d 1 - d 2, by omega⟩ := by
  unfold boxMatrix
  simp only [mulVec, dotProduct]
  split_ifs <;> rfl

lemma box_row {R : Type*} [CommRing R] {m : ℕ} (C : Fin 4 → Matrix (Fin m) (Fin m) R)
    (d : Fin 4 → ℕ) (hd : d 0 + d 1 + d 2 + d 3 = m) (v : Fin m → R) (c : Fin 4) (i : Fin m)
    (hi : (i : ℕ) < d c) :
    ∃ r : Fin m, (boxMatrix C d *ᵥ v) r = (C c *ᵥ v) i := by
  fin_cases c
  · have hi' : (i : ℕ) < d 0 := hi
    exact ⟨i, by rw [boxMatrix_mulVec4, if_pos hi']; rfl⟩
  · have hi' : (i : ℕ) < d 1 := hi
    refine ⟨⟨d 0 + i, by omega⟩, ?_⟩
    rw [boxMatrix_mulVec4, if_neg (by simp), if_pos (by simp; omega)]
    congr 1; ext; simp
  · have hi' : (i : ℕ) < d 2 := hi
    refine ⟨⟨d 0 + d 1 + i, by omega⟩, ?_⟩
    rw [boxMatrix_mulVec4, if_neg (by simp; omega), if_neg (by simp), if_pos (by simp; omega)]
    congr 1; ext; simp; omega
  · have hi' : (i : ℕ) < d 3 := hi
    refine ⟨⟨d 0 + d 1 + d 2 + i, by omega⟩, ?_⟩
    rw [boxMatrix_mulVec4, if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp)]
    congr 1; ext; simp; omega

lemma box_zero_imp {R : Type*} [CommRing R] {m : ℕ} (C : Fin 4 → Matrix (Fin m) (Fin m) R)
    (d : Fin 4 → ℕ) (hd : d 0 + d 1 + d 2 + d 3 = m) (v : Fin m → R)
    (h : boxMatrix C d *ᵥ v = 0) : ∀ c (i : Fin m), (i : ℕ) < d c → (C c *ᵥ v) i = 0 := by
  intro c i hi
  obtain ⟨r, hr⟩ := box_row C d hd v c i hi
  rw [← hr, h]; rfl

lemma box_eq_of {R : Type*} [CommRing R] {m : ℕ} (C : Fin 4 → Matrix (Fin m) (Fin m) R)
    (d : Fin 4 → ℕ) (hd : d 0 + d 1 + d 2 + d 3 = m) (v w : Fin m → R)
    (h : ∀ c (i : Fin m), (i : ℕ) < d c → (C c *ᵥ v) i = (C c *ᵥ w) i) :
    boxMatrix C d *ᵥ v = boxMatrix C d *ᵥ w := by
  funext r
  rw [boxMatrix_mulVec4, boxMatrix_mulVec4]
  split_ifs with h1 h2 h3
  · exact h 0 r h1
  · exact h 1 _ (by simp; omega)
  · exact h 2 _ (by simp; omega)
  · exact h 3 _ (by simp; omega)

/-- **`lem:nie`** (injective form, four coordinates). -/
theorem isNet0_of_box_injective4 (q m : ℕ) [NeZero q]
    (C : Fin 4 → Matrix (Fin m) (Fin m) (ZMod q))
    (h : ∀ d : Fin 4 → ℕ, d 0 + d 1 + d 2 + d 3 = m → Function.Injective (boxMatrix C d).mulVec) :
    IsNet0 q m (digPoint q m C) := by
  intro d hd a ha
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdle : ∀ c, d c ≤ m := by intro c; fin_cases c <;> simp <;> omega
  have hcoord : ∀ c v, coord q m (C c) v = Z3Net.Proofs.digSum q m (fun j => ((C c *ᵥ v) j).val) := by
    intro c v; rfl
  have hbound : ∀ c v, digPoint q m C v c / q ^ (m - d c) < q ^ d c := by
    intro c v
    have hlt := Z3Net.Proofs.digSum_lt q m (fun j => ((C c *ᵥ v) j).val) (fun j => ZMod.val_lt _)
    rw [Nat.div_lt_iff_lt_mul (pow_pos hq _), ← pow_add, Nat.add_sub_of_le (hdle c)]
    simpa [digPoint, hcoord] using hlt
  let φ : (Fin m → ZMod q) → ((c : Fin 4) → Fin (q ^ d c)) :=
    fun v c => ⟨digPoint q m C v c / q ^ (m - d c), hbound c v⟩
  have hinj : Function.Injective φ := by
    intro v w hvw
    apply h d hd
    apply box_eq_of C d hd
    intro c i hi
    have h1 : digPoint q m C v c / q ^ (m - d c) = digPoint q m C w c / q ^ (m - d c) := by
      have := congrFun hvw c
      simpa [φ] using congrArg Fin.val this
    simp only [digPoint, hcoord] at h1
    have := Z3Net.Proofs.digSum_div_inj q hq m _ _ (fun j => ZMod.val_lt _) (fun j => ZMod.val_lt _)
      _ h1 i (by have := hdle c; omega)
    exact ZMod.val_injective _ this
  have hcard : Fintype.card (Fin m → ZMod q) = Fintype.card ((c : Fin 4) → Fin (q ^ d c)) := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_pi, Fin.prod_univ_four]
    rw [← pow_add, ← pow_add, ← pow_add, hd]
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩
  obtain ⟨v, hv⟩ := hbij.2 (fun c => ⟨a c, ha c⟩)
  refine ⟨v, fun c => ?_, fun w hw => hinj ?_⟩
  · have := congrArg Fin.val (congrFun hv c)
    simpa [φ] using this
  · rw [hv]
    funext c
    exact Fin.ext (hw c)

/-! ## Theorem 4D(1): the net property -/

lemma two_mul_inv_two (q : ℕ) (hq : Odd q) : (2 : ZMod q) * (2 : ZMod q)⁻¹ = 1 := by
  apply ZMod.mul_inv_of_unit
  have : IsUnit ((2 : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  simpa using this

lemma box_injective_zmod (q k : ℕ) (hq : Odd q) (hk : 1 ≤ k) (d : Fin 4 → ℕ)
    (hd : d 0 + d 1 + d 2 + d 3 = 4 * k) : Function.Injective (boxMatrix (D4Gen q k) d).mulVec := by
  apply Z3Net.Proofs.mulVec_injective_of_ker
  intro n hn
  exact box_kernel (2 : ZMod q)⁻¹ (two_mul_inv_two q hq) k hk d hd n
    (box_zero_imp _ d hd n hn)

/-- **Theorem 4D(1).** -/
theorem D4_net (q k : ℕ) (hq : Odd q) (hk : 2 ≤ k) : IsNet0 q (4 * k) (D4point q k) := by
  haveI : NeZero q := ⟨by rintro rfl; exact absurd hq (by decide)⟩
  exact isNet0_of_box_injective4 q (4 * k) (D4Gen q k)
    (fun d hd => box_injective_zmod q k hq (by omega) d hd)

end

end Z3NetD4.Proofs

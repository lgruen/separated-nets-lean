module
public import Mathlib
public import Z3Net.SUNet

@[expose] public section

/-!
# Entry U, part 4: Theorem U(1) — `U_net`

* `ivOK_zmod`: for admissible `q` (prime factors `≥ s - 1`), `iv i = i⁻¹` inverts `1, …, s-2` in
  `ℤ/qℤ` (no reduction to primes is needed: Lemma T_s holds over every ring in which the place
  differences are units).
* `isNet0_of_kernel`: Niederreiter's counting argument for `s` coordinates — if a vector whose
  first `d c` digits vanish in every coordinate is zero, the point set is a `(0,m,s)`-net.
-/

namespace Z3NetU.Proofs

open Polynomial Finset Matrix Z3NetU

noncomputable section

lemma natCast_isUnit_zmod (s q : ℕ) (hq : Admissible s q) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ s - 2) :
    IsUnit ((i : ℕ) : ZMod q) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.coprime_of_dvd
  intro p hp hpi hpq
  have := hq.2 p hp hpq
  have := Nat.le_of_dvd (by omega) hpi
  omega

lemma ivOK_zmod (s q : ℕ) (hq : Admissible s q) :
    IvOK (fun i => ((i : ℕ) : ZMod q)⁻¹) (s - 2) := by
  intro i h1 h2
  exact ZMod.mul_inv_of_unit _ (natCast_isUnit_zmod s q hq i h1 h2)

/-- **`lem:nie`** (kernel form, `s` coordinates). -/
theorem isNet0_of_kernel (s q m : ℕ) [NeZero q] (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q))
    (h : ∀ d : Fin s → ℕ, ∑ c, d c = m → ∀ n : Fin m → ZMod q,
      (∀ c (i : Fin m), (i : ℕ) < d c → (C c *ᵥ n) i = 0) → n = 0) :
    IsNet0 s q m (digPoint q m C) := by
  intro d hd a ha
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdle : ∀ c, d c ≤ m := fun c => by
    rw [← hd]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ c)
  have hcoord : ∀ c v, coord q m (C c) v = Z3Net.Proofs.digSum q m (fun j => ((C c *ᵥ v) j).val) := by
    intro c v; rfl
  have hbound : ∀ c v, digPoint q m C v c / q ^ (m - d c) < q ^ d c := by
    intro c v
    have hlt := Z3Net.Proofs.digSum_lt q m (fun j => ((C c *ᵥ v) j).val) (fun j => ZMod.val_lt _)
    rw [Nat.div_lt_iff_lt_mul (pow_pos hq _), ← pow_add, Nat.add_sub_of_le (hdle c)]
    simpa [digPoint, hcoord] using hlt
  let φ : (Fin m → ZMod q) → ((c : Fin s) → Fin (q ^ d c)) :=
    fun v c => ⟨digPoint q m C v c / q ^ (m - d c), hbound c v⟩
  have hinj : Function.Injective φ := by
    intro v w hvw
    have h0 := h d hd (v - w) (by
      intro c i hi
      have h1 : digPoint q m C v c / q ^ (m - d c) = digPoint q m C w c / q ^ (m - d c) := by
        have := congrFun hvw c
        simpa [φ] using congrArg Fin.val this
      simp only [digPoint, hcoord] at h1
      have := Z3Net.Proofs.digSum_div_inj q hq m _ _ (fun j => ZMod.val_lt _)
        (fun j => ZMod.val_lt _) _ h1 i (by have := hdle c; omega)
      rw [mulVec_sub, Pi.sub_apply, ZMod.val_injective _ this, sub_self])
    exact sub_eq_zero.mp h0
  have hcard : Fintype.card (Fin m → ZMod q) = Fintype.card ((c : Fin s) → Fin (q ^ d c)) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum, hd]
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩
  obtain ⟨v, hv⟩ := hbij.2 (fun c => ⟨a c, ha c⟩)
  refine ⟨v, fun c => ?_, fun w hw => hinj ?_⟩
  · have := congrArg Fin.val (congrFun hv c)
    simpa [φ] using this
  · rw [hv]
    funext c
    exact Fin.ext (hw c)

/-- **Theorem U(1).** -/
theorem U_net (s q k : ℕ) (hs : 3 ≤ s) (hq : Admissible s q) (hk : 1 ≤ k) :
    IsNet0 s q (s * k) (Upoint s q k) := by
  haveI : NeZero q := ⟨by have := hq.1; omega⟩
  exact isNet0_of_kernel s q (s * k) (UGen s q k)
    (fun d hd n hn => box_kernel _ hs (ivOK_zmod s q hq) k d hd n hn)

end

end Z3NetU.Proofs

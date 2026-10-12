module
public import Mathlib
public import Z3Net.SUSep
public import Z3Net.NetBasic
public import Z3Net.ThmACover

@[expose] public section

/-!
# Entry U, part 8: covering radius `≤ √s N^(-1/s)` and the real form of Theorem U(2)

In graph form the first `k` digits of coordinate `c` are the index digits of the cell `n_c`, so
`v ↦ (⌊X_c(v) / q^(sk-k)⌋)_c` is injective, hence (counting) bijective onto the `q^(sk)` cells; this
holds in every base `q ≥ 2` (no unit condition is needed). Adapted from the 4D entry. V14 stage S3:
the covering estimate and the real form are the generic `Z3NetA.Proofs.cover_of_cells` and
`Z3NetA.Proofs.sep_real_of_int` (`Z3Net/ThmACover.lean`), shared with Theorem A.
-/

namespace Z3NetU.Proofs

open Finset Matrix Z3NetU

noncomputable section

lemma cells_exist (s q k : ℕ) (hs : 3 ≤ s) (hq : 2 ≤ q) (a : Fin s → ℕ) (ha : ∀ c, a c < q ^ k) :
    ∃ v : Fin (s * k) → ZMod q, ∀ c, Upoint s q k v c / q ^ (s * k - k) = a c := by
  haveI : NeZero q := ⟨by omega⟩
  have hq0 : 0 < q := by omega
  have hcoord : ∀ c v, Upoint s q k v c =
      Z3Net.Proofs.digSum q (s * k) (fun j => ((UGen s q k c *ᵥ v) j).val) := fun c v => rfl
  have hbound : ∀ c v, Upoint s q k v c / q ^ (s * k - k) < q ^ k := by
    intro c v
    have hlt := Z3Net.Proofs.digSum_lt q (s * k) (fun j => ((UGen s q k c *ᵥ v) j).val)
      (fun j => ZMod.val_lt _)
    rw [Nat.div_lt_iff_lt_mul (pow_pos hq0 _), ← pow_add, show k + (s * k - k) = s * k by have := Nat.mul_le_mul_right k (show 1 ≤ s by omega); omega, hcoord]
    exact hlt
  let φ : (Fin (s * k) → ZMod q) → (Fin s → Fin (q ^ k)) :=
    fun v c => ⟨Upoint s q k v c / q ^ (s * k - k), hbound c v⟩
  have hinj : Function.Injective φ := by
    intro v w hvw
    have hdig : ∀ c (i : ℕ) (hi : i < k), v (ix k c ⟨i, hi⟩) = w (ix k c ⟨i, hi⟩) := by
      intro c i hi
      have h1 : Upoint s q k v c / q ^ (s * k - k) = Upoint s q k w c / q ^ (s * k - k) := by
        have := congrFun hvw c
        simpa [φ] using congrArg Fin.val this
      rw [hcoord, hcoord] at h1
      have hik : i < s * k := lt_of_lt_of_le hi (k_le_sk k c)
      have := Z3Net.Proofs.digSum_div_inj q hq0 (s * k) _ _ (fun j => ZMod.val_lt _)
        (fun j => ZMod.val_lt _) _ h1 ⟨i, hik⟩ (by simp; omega)
      have e := ZMod.val_injective _ this
      have ev := Dg_cell s q k c v i hi
      have ew := Dg_cell s q k c w i hi
      simp only [Dg] at ev ew
      rw [← ev, ← ew]; exact e
    funext j
    obtain ⟨d, l, rfl⟩ := ix_surj k j
    exact hdig d l l.isLt
  have hcard : Fintype.card (Fin (s * k) → ZMod q) = Fintype.card (Fin s → Fin (q ^ k)) := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [← pow_mul, mul_comm]
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩
  obtain ⟨v, hv⟩ := hbij.2 (fun c => ⟨a c, ha c⟩)
  refine ⟨v, fun c => ?_⟩
  have := congrArg Fin.val (congrFun hv c)
  simpa [φ] using this

/-- **Theorem U(1), covering radius.** -/
theorem U_covering (s q k : ℕ) (hs : 3 ≤ s) (hq : 2 ≤ q) (hk : 1 ≤ k) (x : Fin s → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (s * k) → ZMod q,
      ∑ c, (x c - (Upoint s q k v c : ℝ) / (q : ℝ) ^ (s * k)) ^ 2 ≤ (s : ℝ) / ((q : ℝ) ^ k) ^ 2 :=
  Z3NetA.Proofs.cover_of_cells (by omega) hq (Upoint s q k) (fun a ha => cells_exist s q k hs hq a ha) x hx

/-- **Theorem U(2), real form.** -/
theorem U_sep_real (s q k : ℕ) (hs : 3 ≤ s) (hq : Admissible s q) (hqa : 5 * aU s + 4 ≤ q)
    (hk : 2 ≤ k) (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (1 - (aU s : ℝ) / q) * ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Upoint s q k v c : ℤ) - (Upoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) := by
  have hZ := U_sep s q k hs hq hqa hk v w hvw
  unfold torusDist2 at hZ
  have hR : (q : ℝ) ^ (2 * (s * k - k)) * ((q : ℝ) - (aU s : ℝ)) ^ 2
      ≤ (q : ℝ) ^ 2 * ∑ c, ((cres (q ^ (s * k)) ((Upoint s q k v c : ℤ) - (Upoint s q k w c : ℤ)) : ℝ)) ^ 2 := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this
    exact this
  have hsum : ∑ c, ((cres (q ^ (s * k)) ((Upoint s q k v c : ℤ) - (Upoint s q k w c : ℤ)) : ℝ)
      / (q : ℝ) ^ (s * k)) ^ 2 = (∑ c, ((cres (q ^ (s * k))
        ((Upoint s q k v c : ℤ) - (Upoint s q k w c : ℤ)) : ℝ)) ^ 2) / ((q : ℝ) ^ (s * k)) ^ 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun c _ => by rw [div_pow]
  rw [hsum]
  exact Z3NetA.Proofs.sep_real_of_int (by omega) (by have := hq.1; omega) _ hR

end

end Z3NetU.Proofs

module
public import Mathlib
public import Z3Net.D4Geom
public import Z3Net.NetBasic

@[expose] public section

/-!
# 4D entry, part 9: Theorem 4D(2) — one point per cell, covering radius `≤ 2 N^(-1/4)`

In graph form the first `k` digits of coordinate `c` are the index digits of the cell `n_c`, so
`v ↦ (⌊X_c(v) / q^(3k)⌋)_c` is injective, hence (counting) bijective onto the `q^(4k)` cells; this
holds in every base `q ≥ 2` (no unit condition is needed).
-/

namespace Z3NetD4.Proofs

open Finset Matrix Z3NetD4

noncomputable section

lemma cells_exist (q k : ℕ) (hq : 2 ≤ q) (a : Fin 4 → ℕ) (ha : ∀ c, a c < q ^ k) :
    ∃ v : Fin (4 * k) → ZMod q, ∀ c, D4point q k v c / q ^ (3 * k) = a c := by
  haveI : NeZero q := ⟨by omega⟩
  have hq0 : 0 < q := by omega
  have hcoord : ∀ c v, D4point q k v c =
      Z3Net.Proofs.digSum q (4 * k) (fun j => ((D4Gen q k c *ᵥ v) j).val) := fun c v => rfl
  have hbound : ∀ c v, D4point q k v c / q ^ (3 * k) < q ^ k := by
    intro c v
    have hlt := Z3Net.Proofs.digSum_lt q (4 * k) (fun j => ((D4Gen q k c *ᵥ v) j).val)
      (fun j => ZMod.val_lt _)
    rw [Nat.div_lt_iff_lt_mul (pow_pos hq0 _), ← pow_add, show k + 3 * k = 4 * k by ring, hcoord]
    exact hlt
  let φ : (Fin (4 * k) → ZMod q) → (Fin 4 → Fin (q ^ k)) :=
    fun v c => ⟨D4point q k v c / q ^ (3 * k), hbound c v⟩
  have hinj : Function.Injective φ := by
    intro v w hvw
    have hdig : ∀ c (i : ℕ) (hi : i < k), v (ix k c ⟨i, hi⟩) = w (ix k c ⟨i, hi⟩) := by
      intro c i hi
      have h1 : D4point q k v c / q ^ (3 * k) = D4point q k w c / q ^ (3 * k) := by
        have := congrFun hvw c
        simpa [φ] using congrArg Fin.val this
      rw [hcoord, hcoord] at h1
      have := Z3Net.Proofs.digSum_div_inj q hq0 (4 * k) _ _ (fun j => ZMod.val_lt _)
        (fun j => ZMod.val_lt _) _ h1 ⟨i, by omega⟩ (by simp; omega)
      have e := ZMod.val_injective _ this
      have ev := Dg_cell q k c v i hi
      have ew := Dg_cell q k c w i hi
      simp only [Dg] at ev ew
      rw [← ev, ← ew]; exact e
    funext j
    have hk : 0 < k := by have := j.isLt; omega
    have hc : (j : ℕ) / k < 4 := Nat.div_lt_of_lt_mul (by have := j.isLt; omega)
    have := hdig ⟨(j : ℕ) / k, hc⟩ ((j : ℕ) % k) (Nat.mod_lt _ hk)
    convert this using 2 <;> (ext; simp [ix]; exact (Nat.div_add_mod' (j : ℕ) k).symm)
  have hcard : Fintype.card (Fin (4 * k) → ZMod q) = Fintype.card (Fin 4 → Fin (q ^ k)) := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [← pow_mul]; ring_nf
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩
  obtain ⟨v, hv⟩ := hbij.2 (fun c => ⟨a c, ha c⟩)
  refine ⟨v, fun c => ?_⟩
  have := congrArg Fin.val (congrFun hv c)
  simpa [φ] using this

/-- **Theorem 4D(2), covering radius.** -/
theorem D4_covering (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) (x : Fin 4 → ℝ)
    (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) :
    ∃ v : Fin (4 * k) → ZMod q,
      ∑ c, (x c - (D4point q k v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2 ≤ 4 / ((q : ℝ) ^ k) ^ 2 := by
  have hG : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  let a : Fin 4 → ℕ := fun c => min ⌊x c * (q : ℝ) ^ k⌋₊ (q ^ k - 1)
  have ha : ∀ c, a c < q ^ k := fun c => lt_of_le_of_lt (min_le_right _ _) (by omega)
  obtain ⟨v, hv⟩ := cells_exist q k hq a ha
  refine ⟨v, ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hGpos : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hqpos k
  have key : ∀ c, (x c - (D4point q k v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2 ≤ 1 / ((q : ℝ) ^ k) ^ 2 := by
    intro c
    set X := D4point q k v c
    have hdiv : X / q ^ (3 * k) = a c := hv c
    set y := x c * (q : ℝ) ^ k
    set z := (X : ℝ) / (q : ℝ) ^ (3 * k)
    have hy0 : 0 ≤ y := mul_nonneg (hx c).1 hGpos.le
    have hay : (a c : ℝ) ≤ y := by
      have : a c ≤ ⌊y⌋₊ := min_le_left _ _
      exact le_trans (by exact_mod_cast this) (Nat.floor_le hy0)
    have hya : y ≤ (a c : ℝ) + 1 := by
      by_cases hfl : ⌊y⌋₊ ≤ q ^ k - 1
      · have : a c = ⌊y⌋₊ := min_eq_left hfl
        rw [this]; exact (Nat.lt_floor_add_one y).le
      · have hfl' : ¬ ⌊x c * (q : ℝ) ^ k⌋₊ ≤ q ^ k - 1 := hfl
        have : a c = q ^ k - 1 := min_eq_right (by omega)
        rw [this, Nat.cast_sub hG]
        have : y ≤ (q : ℝ) ^ k := by
          have := mul_le_mul_of_nonneg_right (hx c).2 hGpos.le
          simpa [y] using this
        push_cast; linarith
    have hQ : (0 : ℝ) < (q : ℝ) ^ (3 * k) := pow_pos hqpos _
    have hXeq : (X : ℝ) = (q : ℝ) ^ (3 * k) * (a c) + (X % q ^ (3 * k) : ℕ) := by
      have := Nat.div_add_mod X (q ^ (3 * k))
      rw [hdiv] at this
      exact_mod_cast this.symm
    have hrem : ((X % q ^ (3 * k) : ℕ) : ℝ) < (q : ℝ) ^ (3 * k) := by
      exact_mod_cast Nat.mod_lt _ (pow_pos (by omega) _)
    have haz : (a c : ℝ) ≤ z := by
      rw [le_div_iff₀ hQ, hXeq]
      have : (0 : ℝ) ≤ ((X % q ^ (3 * k) : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hza : z ≤ (a c : ℝ) + 1 := by
      rw [div_le_iff₀ hQ, hXeq]
      nlinarith
    have hxz : x c - (X : ℝ) / (q : ℝ) ^ (4 * k) = (y - z) / (q : ℝ) ^ k := by
      simp only [y, z]
      rw [show 4 * k = 3 * k + k by ring, pow_add]
      field_simp
    rw [hxz, div_pow, one_div, div_eq_mul_inv]
    have hsq : (y - z) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith
    calc (y - z) ^ 2 * (((q : ℝ) ^ k) ^ 2)⁻¹ ≤ 1 * (((q : ℝ) ^ k) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (by positivity))
      _ = (((q : ℝ) ^ k) ^ 2)⁻¹ := by rw [one_mul]
  calc ∑ c, (x c - (D4point q k v c : ℝ) / (q : ℝ) ^ (4 * k)) ^ 2
      ≤ ∑ _c : Fin 4, 1 / ((q : ℝ) ^ k) ^ 2 := Finset.sum_le_sum fun c _ => key c
    _ = 4 / ((q : ℝ) ^ k) ^ 2 := by simp; ring

end

end Z3NetD4.Proofs

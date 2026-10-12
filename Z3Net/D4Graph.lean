module
public import Mathlib
public import Z3Net.D4Defs

@[expose] public section

/-!
# 4D entry, part 2: graph-form bookkeeping

Index digit `ix k d l = d k + l` is level `l` of the cell of axis `d`; digit `i < k` of coordinate
`c` of a graph-form net is the index digit `ix k c i`, digit `k + r` is `∑_{d,l} Φ_cd[r,l] n_{d,l}`.
-/

namespace Z3NetD4.Proofs

open Finset Matrix Z3NetD4

lemma idx_lt (k : ℕ) (d : Fin 4) (l : Fin k) : (d : ℕ) * k + l < 4 * k := by
  have := d.isLt; have := l.isLt
  calc (d : ℕ) * k + l < (d : ℕ) * k + k := by omega
    _ = ((d : ℕ) + 1) * k := by ring
    _ ≤ 4 * k := Nat.mul_le_mul_right _ (by omega)

/-- The index digit `n_{d k + l}` (level `l` of the cell of axis `d`). -/
def ix (k : ℕ) (d : Fin 4) (l : Fin k) : Fin (4 * k) := ⟨(d : ℕ) * k + l, idx_lt k d l⟩

lemma sum_fin4k {M : Type*} [AddCommMonoid M] (k : ℕ) (f : Fin (4 * k) → M) :
    ∑ j, f j = ∑ d : Fin 4, ∑ l : Fin k, f (ix k d l) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  congr 1; ext; simp [finProdFinEquiv, ix]; ring

lemma ix_div (k : ℕ) (d : Fin 4) (l : Fin k) : ((ix k d l : ℕ)) / k = d := by
  have := l.isLt
  simp only [ix]; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt this]
  simp

lemma ix_mod (k : ℕ) (d : Fin 4) (l : Fin k) : ((ix k d l : ℕ)) % k = l := by
  have := l.isLt
  simp only [ix]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt this]

lemma ix_injective (k : ℕ) (d d' : Fin 4) (l l' : Fin k) (h : ix k d l = ix k d' l') :
    d = d' ∧ l = l' := by
  have h1 := ix_div k d l; have h2 := ix_mod k d l
  rw [h] at h1 h2
  rw [ix_div] at h1; rw [ix_mod] at h2
  exact ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩

variable {R : Type*} [CommRing R]

/-- Cell digits of a graph-form net. -/
lemma graphGen_cell (k : ℕ) (Φ : Fin 4 → Fin 4 → Matrix (Fin (3 * k)) (Fin k) R) (c : Fin 4)
    (n : Fin (4 * k) → R) (i : ℕ) (hi : i < k) :
    (graphGen k Φ c *ᵥ n) ⟨i, by omega⟩ = n (ix k c ⟨i, hi⟩) := by
  simp only [mulVec, dotProduct, graphGen, dif_pos hi]
  rw [Fintype.sum_eq_single (ix k c ⟨i, hi⟩)]
  · simp [ix]
  · intro j hj
    rw [if_neg]; · simp
    intro h; apply hj; ext; simp [ix, h]

/-- Offset digits of a graph-form net. -/
lemma graphGen_off (k : ℕ) (Φ : Fin 4 → Fin 4 → Matrix (Fin (3 * k)) (Fin k) R) (c : Fin 4)
    (n : Fin (4 * k) → R) (r : Fin (3 * k)) :
    (graphGen k Φ c *ᵥ n) ⟨k + r, by omega⟩ = ∑ d : Fin 4, ∑ l : Fin k, Φ c d r l * n (ix k d l) := by
  simp only [mulVec, dotProduct, graphGen, dif_neg (show ¬ (k + (r : ℕ) < k) by omega)]
  rw [sum_fin4k]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  congr 2
  · ext; simp [ix_div]
  · ext; simp
  · ext; simp [ix_mod]

end Z3NetD4.Proofs

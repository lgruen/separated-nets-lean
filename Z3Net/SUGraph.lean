module
public import Mathlib
public import Z3Net.SUDefs

@[expose] public section

/-!
# Entry U, part 2: graph-form bookkeeping (`s` coordinates)

Index digit `ix k d l = d k + l` is level `l` of the cell of axis `d`; digit `i < k` of coordinate
`c` of a graph-form net is the index digit `ix k c i`, digit `k + r` is
`∑_{d,l} Φ_cd[r,l] n_{d,l}`.
-/

namespace Z3NetU.Proofs

open Finset Matrix Z3NetU

lemma idx_lt {s : ℕ} (k : ℕ) (d : Fin s) (l : Fin k) : (d : ℕ) * k + l < s * k := by
  have := d.isLt; have := l.isLt
  calc (d : ℕ) * k + l < (d : ℕ) * k + k := by omega
    _ = ((d : ℕ) + 1) * k := by ring
    _ ≤ s * k := Nat.mul_le_mul_right _ (by omega)

/-- The index digit `n_{d k + l}` (level `l` of the cell of axis `d`). -/
def ix {s : ℕ} (k : ℕ) (d : Fin s) (l : Fin k) : Fin (s * k) := ⟨(d : ℕ) * k + l, idx_lt k d l⟩

lemma sum_fin_sk {M : Type*} [AddCommMonoid M] (s k : ℕ) (f : Fin (s * k) → M) :
    ∑ j, f j = ∑ d : Fin s, ∑ l : Fin k, f (ix k d l) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  congr 1; ext; simp [finProdFinEquiv, ix]; ring

lemma ix_div {s : ℕ} (k : ℕ) (d : Fin s) (l : Fin k) : ((ix k d l : ℕ)) / k = d := by
  have := l.isLt
  simp only [ix]; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt this]
  simp

lemma ix_mod {s : ℕ} (k : ℕ) (d : Fin s) (l : Fin k) : ((ix k d l : ℕ)) % k = l := by
  have := l.isLt
  simp only [ix]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt this]

lemma ix_surj {s : ℕ} (k : ℕ) (j : Fin (s * k)) :
    ∃ (d : Fin s) (l : Fin k), j = ix k d l := by
  have hk : 0 < k := Nat.pos_of_mul_pos_left (Fin.pos j)
  have hc : (j : ℕ) / k < s := Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm s k))
  exact ⟨⟨_, hc⟩, ⟨_, Nat.mod_lt _ hk⟩, by ext; simp [ix]; exact (Nat.div_add_mod' (j : ℕ) k).symm⟩

variable {R : Type*} [CommRing R]

lemma sk_sub_add {s k : ℕ} (r : Fin (s * k - k)) : k + (r : ℕ) < s * k :=
  Nat.add_lt_of_lt_sub' r.isLt

/-- Cell digits of a graph-form net. -/
lemma graphGen_cell {s : ℕ} (k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) R)
    (c : Fin s) (n : Fin (s * k) → R) (i : ℕ) (hi : i < k) :
    (graphGen s k Φ c *ᵥ n) ⟨i, lt_of_le_of_lt (Nat.le_add_left i _) (idx_lt k c ⟨i, hi⟩)⟩ =
      n (ix k c ⟨i, hi⟩) := by
  simp only [mulVec, dotProduct, graphGen, dif_pos hi]
  rw [Fintype.sum_eq_single (ix k c ⟨i, hi⟩)]
  · simp [ix]
  · intro j hj
    rw [if_neg]; · simp
    intro h; apply hj; ext; simp [ix, h]

/-- Offset digits of a graph-form net. -/
lemma graphGen_off {s : ℕ} (k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) R)
    (c : Fin s) (n : Fin (s * k) → R) (r : Fin (s * k - k)) :
    (graphGen s k Φ c *ᵥ n) ⟨k + r, sk_sub_add r⟩ =
      ∑ d : Fin s, ∑ l : Fin k, Φ c d r l * n (ix k d l) := by
  simp only [mulVec, dotProduct, graphGen, dif_neg (show ¬ (k + (r : ℕ) < k) by omega)]
  rw [sum_fin_sk]
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  congr 2
  · ext; simp [ix_div]
  · ext; simp
  · ext; simp [ix_mod]

end Z3NetU.Proofs

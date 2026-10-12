module
public import Mathlib
public import Z3Net.KNGeomDigit

@[expose] public section

/-!
# KN separation, part 5: decomposition of a coordinate, far and near toroidal bounds

`coord = (prefix of a digits) · p^(m-a) + low`, `low < p^(m-a)`.
* far: `cres ≥ |δ_c| U - (U - 1)`, `U = p^(m - K_c)`;
* near: `X_c(v) - X_c(w) = B u + e + z N` with `B = pδ + Δjitter` (full) or
  `p(pδ + Δskeleton) + Δjitter` (skeleton), `u = p^(m-k-2)`, `e` = tail difference.
-/

namespace Z3NetKN.Geom

open Finset Matrix Z3NetKN.Relax

variable {p : ℕ}

/-- The digits below position `a`, as a number in `[0, p^(m-a))`. -/
def low {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) (a : ℕ) : ℕ :=
  pre p (fun j => dg A v (a + j)) (m - a)

lemma coord_split {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) (a : ℕ)
    (ha : a ≤ m) : coord p m A v = pre p (dg A v) a * p ^ (m - a) + low A v a := by
  have h := pre_add p (dg A v) a (m - a)
  rw [Nat.add_sub_cancel' ha] at h
  rw [coord_eq_pre, h, low]

lemma low_lt [NeZero p] {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p)
    (a : ℕ) : low A v a < p ^ (m - a) :=
  pre_lt p (Nat.pos_of_neZero p) _ _ (fun j _ => dg_lt A v _)

lemma low_diff [NeZero p] {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p)
    (a : ℕ) : |(low A v a : ℤ) - low A w a| ≤ ((p ^ (m - a) : ℕ) : ℤ) - 1 := by
  have h1 := low_lt A v a
  have h2 := low_lt A w a
  rw [abs_le]; constructor <;> omega

variable {r k : ℕ}

/-- **Far bound** for coordinate `c`. -/
lemma far_bound [NeZero p] (hr : r = 1 ∨ r = 2) (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKNskel r p k sk C)
    (v w : Fin (3 * k + r) → ZMod p) (c : Fin 3) :
    |cen (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c)| * ((p ^ (3 * k + r - depth r k c) : ℕ) : ℤ)
        - (((p ^ (3 * k + r - depth r k c) : ℕ) : ℤ) - 1) ≤
      (cres (p ^ (3 * k + r)) ((coord p (3 * k + r) (C c) v : ℤ) - coord p (3 * k + r) (C c) w) : ℤ) := by
  have hK : depth r k c ≤ 3 * k + r := by have := off_add_depth r k hr c; omega
  set K := depth r k c with hKdef
  set U := p ^ (3 * k + r - K) with hU
  rw [coord_split _ v K hK, coord_split _ w K hK, pre_dg_depth sk C hr hC v c,
    pre_dg_depth sk C hr hC w c]
  obtain ⟨z, hz⟩ := cen_spec (p ^ K) ((nC r k v c : ℤ) - nC r k w c)
  have hN : p ^ (3 * k + r) = p ^ K * U := by rw [hU, ← pow_add]; congr 1; omega
  have hp0 : 0 < p := Nat.pos_of_neZero p
  have key : ((nC r k v c * U + low (C c) v K : ℕ) : ℤ) - ((nC r k w c * U + low (C c) w K : ℕ) : ℤ) =
      cen (p ^ K) ((nC r k v c : ℤ) - nC r k w c) * U +
        ((low (C c) v K : ℤ) - low (C c) w K) + z * ((p ^ K * U : ℕ) : ℤ) := by
    push_cast
    have : (nC r k v c : ℤ) - nC r k w c - (cen (p ^ K) ((nC r k v c : ℤ) - nC r k w c) +
        z * ((p ^ K : ℕ) : ℤ)) = 0 := by rw [← hz]; ring
    push_cast at this
    linear_combination (U : ℤ) * this
  rw [hN, key]
  exact cres_lower (p ^ K) U (by positivity) (by positivity) _ _ z _
    (cen_abs _ (by positivity) _) (low_diff (C c) v w K)

/-- Near decomposition, full coordinate (`c < r`, depth `k + 1`). -/
lemma near_full [NeZero p] (hr : r = 1 ∨ r = 2) (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKNskel r p k sk C)
    (v w : Fin (3 * k + r) → ZMod p) (c : Fin 3) (hc : (c : ℕ) < r) (hk : 1 ≤ k) :
    ∃ z : ℤ, (coord p (3 * k + r) (C c) v : ℤ) - coord p (3 * k + r) (C c) w =
      (cen (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c) * p +
          ((dg (C c) v (k + 1) : ℤ) - dg (C c) w (k + 1))) * ((p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) +
        ((low (C c) v (k + 2) : ℤ) - low (C c) w (k + 2)) +
        z * ((p ^ (k + 2) * p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) := by
  have hd : depth r k c = k + 1 := by unfold depth; rw [if_pos hc]
  have hK : k + 2 ≤ 3 * k + r := by omega
  rw [coord_split _ v (k + 2) hK, coord_split _ w (k + 2) hK]
  have ev := pre_dg_depth sk C hr hC v c
  have ew := pre_dg_depth sk C hr hC w c
  rw [hd] at ev ew
  have ev2 : pre p (dg (C c) v) (k + 2) = nC r k v c * p + dg (C c) v (k + 1) := by rw [← ev]; rfl
  have ew2 : pre p (dg (C c) w) (k + 2) = nC r k w c * p + dg (C c) w (k + 1) := by rw [← ew]; rfl
  rw [ev2, ew2]
  obtain ⟨z, hz⟩ := cen_spec (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c)
  refine ⟨z, ?_⟩
  rw [hd] at hz ⊢
  set δ := cen (p ^ (k + 1)) ((nC r k v c : ℤ) - nC r k w c)
  push_cast at hz ⊢
  linear_combination ((p : ℤ) * (p : ℤ) ^ (3 * k + r - (k + 2))) * hz

/-- Near decomposition, skeleton coordinate (`r ≤ c`, depth `k`). -/
lemma near_skel [NeZero p] (hr : r = 1 ∨ r = 2) (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKNskel r p k sk C)
    (v w : Fin (3 * k + r) → ZMod p) (c : Fin 3) (hc : r ≤ (c : ℕ)) (hk : 1 ≤ k) :
    ∃ z : ℤ, (coord p (3 * k + r) (C c) v : ℤ) - coord p (3 * k + r) (C c) w =
      ((cen (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c) * p +
          ((dg (C c) v k : ℤ) - dg (C c) w k)) * p +
          ((dg (C c) v (k + 1) : ℤ) - dg (C c) w (k + 1))) * ((p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) +
        ((low (C c) v (k + 2) : ℤ) - low (C c) w (k + 2)) +
        z * ((p ^ (k + 2) * p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) := by
  have hd : depth r k c = k := by unfold depth; rw [if_neg (by omega)]
  have hK : k + 2 ≤ 3 * k + r := by omega
  rw [coord_split _ v (k + 2) hK, coord_split _ w (k + 2) hK]
  have ev := pre_dg_depth sk C hr hC v c
  have ew := pre_dg_depth sk C hr hC w c
  rw [hd] at ev ew
  have ev2 : pre p (dg (C c) v) (k + 2) = (nC r k v c * p + dg (C c) v k) * p + dg (C c) v (k + 1) := by
    rw [← ev]; rfl
  have ew2 : pre p (dg (C c) w) (k + 2) = (nC r k w c * p + dg (C c) w k) * p + dg (C c) w (k + 1) := by
    rw [← ew]; rfl
  rw [ev2, ew2]
  obtain ⟨z, hz⟩ := cen_spec (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c)
  refine ⟨z, ?_⟩
  rw [hd] at hz ⊢
  set δ := cen (p ^ k) ((nC r k v c : ℤ) - nC r k w c)
  push_cast at hz ⊢
  linear_combination ((p : ℤ) * (p : ℤ) * (p : ℤ) ^ (3 * k + r - (k + 2))) * hz

end Z3NetKN.Geom

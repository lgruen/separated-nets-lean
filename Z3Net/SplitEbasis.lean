module
public import Z3Net.SplitDefs
public import Z3Net.FTsplit
public import Z3Net.FEbasis

@[expose] public section

/-!
# Entry Split, part 1: the graph form of the split frame, its `E`-basis, the normal form

* The `2s` points: `v_c - v_b`, `u_c - v_d` (all `c, d`) and `u_c - u_c'` are units.
* `split_spec`: the `(k, …, k)` box `G` of the split frame is invertible and `Φ^S` is its graph
  form; `split_boxMinor`: box minors of `Φ^S` are those of the split frame divided by `det G`.
* The `E`-basis `E_{d,j} = Π_d (t - v_d)^j`, `Π_d = ∏_{b ≠ d} (t - v_b)^k`: its cells vanish off
  `d` and form `Toep(Π_d(v_d + x))` at `d`; its first offset digit at `c` is
  `Π_d(u_c) ϑ_cd^j = P_c^k w_cd y_cd^(k-1-j)`. Hence `Φ^S_cd Toep(Π_d(v_d + x)) = Ψ_cd`, which
  gives the normal form of `prop:Gsplit` (`Gsplit_normal`) and its nodes (`Gsplit_nodes`).
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s : ℕ}

/-! ## The points -/

lemma splitPts_v (u v : Fin s → R) (c : Fin s) :
    Z3NetF.splitPts u v ⟨2 * c, by omega⟩ = v c := by
  simp [Z3NetF.splitPts]

lemma splitPts_u (u v : Fin s → R) (c : Fin s) :
    Z3NetF.splitPts u v ⟨2 * c + 1, by omega⟩ = u c := by
  have h1 : (2 * (c : ℕ) + 1) % 2 = 1 := by omega
  have h2 : (2 * (c : ℕ) + 1) / 2 = c := by omega
  simp [Z3NetF.splitPts, h1, h2]

variable (k : ℕ) {u v : Fin s → R}

lemma split_vv (huv : Z3NetF.SplitOK u v) (b c : Fin s) (h : b ≠ c) : IsUnit (v b - v c) := by
  have := huv ⟨2 * b, by omega⟩ ⟨2 * c, by omega⟩ (by
    intro e; apply h; ext; have := congrArg Fin.val e; simp only [Fin.val_mk] at this; omega)
  rwa [splitPts_v, splitPts_v] at this

lemma split_uv (huv : Z3NetF.SplitOK u v) (c d : Fin s) : IsUnit (u c - v d) := by
  have := huv ⟨2 * c + 1, by omega⟩ ⟨2 * d, by omega⟩ (by
    intro e; have := congrArg Fin.val e; simp only [Fin.val_mk] at this; omega)
  rwa [splitPts_u, splitPts_v] at this

lemma split_uu (huv : Z3NetF.SplitOK u v) (c c' : Fin s) (h : c ≠ c') : IsUnit (u c - u c') := by
  have := huv ⟨2 * c + 1, by omega⟩ ⟨2 * c' + 1, by omega⟩ (by
    intro e; apply h; ext; have := congrArg Fin.val e; simp only [Fin.val_mk] at this; omega)
  rwa [splitPts_u, splitPts_u] at this

lemma Psplit_unit (huv : Z3NetF.SplitOK u v) (c : Fin s) : IsUnit (Z3NetF.Psplit u v c) :=
  IsUnit.prod_univ_iff.mpr fun d => split_uv huv c d

lemma ySplit_unit (huv : Z3NetF.SplitOK u v) (c d : Fin s) : IsUnit (Z3NetF.ySplit u v c d) :=
  (split_uv huv c d).ringInverse

/-! ## Box minors of the split frame are units -/

lemma split_box_unit (huv : Z3NetF.SplitOK u v) (d : Fin s → ℕ) (hd : ∑ c, d c = s * k) :
    IsUnit (Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) d).det := by
  have hprod : IsUnit (∏ Q : Fin (2 * s), ∏ P : Fin (2 * s),
      (if P < Q then (Z3NetF.splitPts u v Q - Z3NetF.splitPts u v P) ^
        (Z3NetF.splitMult k d P * Z3NetF.splitMult k d Q) else 1)) := by
    rw [IsUnit.prod_univ_iff]; intro Q
    rw [IsUnit.prod_univ_iff]; intro P
    split_ifs with h
    · exact (huv Q P (ne_of_gt h)).pow _
    · exact isUnit_one
  rcases (Tsplit_minor_core k u v d hd).2 with h | h <;> rw [h]
  · exact hprod
  · exact hprod.neg

variable (u v)

/-- The `(k, …, k)` box of the split frame. -/
abbrev GkS : Matrix (Fin (s * k)) (Fin (s * k)) R :=
  Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) (fun _ => k)

lemma GkS_unit (huv : Z3NetF.SplitOK u v) : IsUnit (GkS k u v).det :=
  split_box_unit k huv _ (sum_const_k k)

lemma splitGraph_eq_invPhi :
    Z3NetF.splitGraph R k u v = invPhi (m := s * k) (fun _ => k) (sum_const_k k)
      (Z3NetF.splitRead (s * k) k u v) := by
  funext c d r l
  simp only [Z3NetF.splitGraph, invPhi]
  exact mat_congr2 _ _ _ _ _ _ _ _ _ rfl (by rw [pre_const])

theorem split_spec_core (huv : Z3NetF.SplitOK u v) :
    IsUnit (GkS k u v).det ∧
      ∀ c, Z3NetF.graphGenK (m := s * k) (fun _ => k) (Z3NetF.splitGraph R k u v) c * GkS k u v =
        Z3NetF.splitRead (s * k) k u v c := by
  refine ⟨GkS_unit k u v huv, fun c => ?_⟩
  rw [splitGraph_eq_invPhi, graphGenK_inv _ (sum_const_k k) _ (GkS_unit k u v huv) c,
    Matrix.mul_assoc, nonsing_inv_mul _ (GkS_unit k u v huv), Matrix.mul_one]

lemma graphGenK_splitGraph (huv : Z3NetF.SplitOK u v) :
    Z3NetF.graphGenK (m := s * k) (fun _ => k) (Z3NetF.splitGraph R k u v) =
      fun c => Z3NetF.splitRead (s * k) k u v c * (GkS k u v)⁻¹ := by
  rw [splitGraph_eq_invPhi]
  funext c; exact graphGenK_inv _ (sum_const_k k) _ (GkS_unit k u v huv) c

theorem split_boxMinor_core (huv : Z3NetF.SplitOK u v) (d : Fin s → ℕ) :
    (Z3NetF.boxMatrix (Z3NetF.graphGenK (m := s * k) (fun _ => k) (Z3NetF.splitGraph R k u v)) d).det *
        (Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) (fun _ => k)).det =
      (Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) d).det := by
  rw [graphGenK_splitGraph k u v huv, box_mul_right, det_mul, det_nonsing_inv, mul_assoc,
    Ring.inverse_mul_cancel _ (GkS_unit k u v huv), mul_one]

/-! ## The `E`-basis -/

/-- `Π_d = ∏_{b ≠ d} (X - v_b)^k`. -/
def sPpoly (d : Fin s) : R[X] := ∏ b ∈ univ.filter (fun b => b ≠ d), (X - C (v b)) ^ k

/-- The basis polynomial `E_{d,j} = Π_d (X - v_d)^j`. -/
def sEpoly (d : Fin s) (j : ℕ) : R[X] := sPpoly k v d * (X - C (v d)) ^ j

/-- Coefficient vector of `E_{d,j}` in `R[t]_{<sk}`. -/
def sEvec (d : Fin s) (j : ℕ) : Fin (s * k) → R := fun l => (sEpoly k v d j).coeff l

lemma natDegree_sEpoly_le (d : Fin s) (j : ℕ) : (sEpoly k v d j).natDegree ≤ (s - 1) * k + j := by
  have hcard : (univ.filter (fun b : Fin s => b ≠ d)).card = s - 1 := by
    rw [Finset.filter_ne' univ d, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have h1 : (sPpoly k v d).natDegree ≤ (s - 1) * k := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun b _ => natDegree_lin_pow (v b) k)).trans ?_
    rw [sum_const, smul_eq_mul, hcard]
  exact (natDegree_mul_le).trans (Nat.add_le_add h1 (natDegree_lin_pow _ j))

lemma natDegree_sEpoly_lt (d : Fin s) (j : ℕ) (hj : j < k) : (sEpoly k v d j).natDegree < s * k := by
  have hs : 1 ≤ s := by have := d.isLt; omega
  have : (s - 1) * k + k = s * k := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hs]
  have := natDegree_sEpoly_le k v d j
  omega

/-- Readings of the basis: cell digits at `v_c`, offset digits at `u_c`. -/
lemma sread (c d : Fin s) (j : ℕ) (hj : j < k) (i : Fin (s * k)) :
    (Z3NetF.splitRead (s * k) k u v c *ᵥ sEvec k v d j) i =
      if (i : ℕ) < k then (taylor (v c) (sEpoly k v d j)).coeff i
      else (taylor (u c) (sEpoly k v d j)).coeff ((i : ℕ) - k) := by
  have hP := natDegree_sEpoly_lt k v d j hj
  simp only [mulVec, dotProduct, Z3NetF.splitRead, sEvec]
  by_cases h : (i : ℕ) < k
  · simp only [h, if_true]
    exact readAt_mul (s * k) (v c) _ hP i
  · simp only [h, if_false]
    exact readAt_mul (s * k) (u c) _ hP ⟨(i : ℕ) - k, by omega⟩

lemma taylor_sPpoly (d : Fin s) : taylor (v d) (sPpoly k v d) = Z3NetF.piSplit k v d := by
  rw [Z3NetF.piSplit, sPpoly, taylor_apply, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [pow_comp, sub_comp, X_comp, C_comp, C_sub]
  ring

lemma scell (c d : Fin s) (j : ℕ) (hj : j < k) (i : ℕ) (hi : i < k) :
    (Z3NetF.splitRead (s * k) k u v c *ᵥ sEvec k v d j) ⟨i, by have := c.isLt; nlinarith⟩ =
      if c = d then Z3NetF.toep k (Z3NetF.piSplit k v d) ⟨i, hi⟩ ⟨j, hj⟩ else 0 := by
  rw [sread k u v c d j hj, if_pos (show ((⟨i, _⟩ : Fin (s * k)) : ℕ) < k from hi)]
  simp only [Fin.val_mk]
  by_cases hcd : c = d
  · subst hcd
    rw [if_pos rfl]
    simp only [Z3NetF.toep]
    rw [sEpoly, mul_comm, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul, taylor_sPpoly]
    by_cases hji : j ≤ i
    · have h2 : (⟨j, hj⟩ : Fin k) ≤ ⟨i, hi⟩ := hji
      rw [if_pos hji, if_pos h2]
    · have h2 : ¬ (⟨j, hj⟩ : Fin k) ≤ ⟨i, hi⟩ := hji
      rw [if_neg hji, if_neg h2]
  · rw [if_neg hcd]
    have hmem : c ∈ univ.filter (fun b => b ≠ d) := by simp [hcd]
    unfold sEpoly sPpoly
    rw [← Finset.mul_prod_erase _ _ hmem, mul_assoc, Z3NetU.Proofs.coeff_taylor_X_sub_C_pow_mul,
      if_neg (by omega)]

/-- The first offset digit of `E_{d,j}` at `c`: `E_{d,j}(u_c) = P_c^k w_cd y_cd^(k-1-j)`. -/
lemma soff (hs : 2 ≤ s) (huv : Z3NetF.SplitOK u v) (c d : Fin s) (j : ℕ) (hj : j < k) :
    (Z3NetF.splitRead (s * k) k u v c *ᵥ sEvec k v d j) ⟨k, by nlinarith⟩ =
      Z3NetF.Psplit u v c ^ k * (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ (k - 1 - j)) := by
  rw [sread k u v c d j hj, if_neg (show ¬ ((⟨k, _⟩ : Fin (s * k)) : ℕ) < k from lt_irrefl k)]
  simp only [Fin.val_mk, Nat.sub_self, taylor_coeff_zero]
  simp only [sEpoly, sPpoly, eval_mul, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  rw [Finset.prod_pow, Finset.filter_ne' univ d, Z3NetF.Psplit, ← Finset.mul_prod_erase univ _ (mem_univ d),
    mul_pow]
  have hD := Ring.mul_inverse_cancel (u c - v d) (split_uv huv c d)
  rw [show (u c - v d) ^ k * (∏ b ∈ univ.erase d, (u c - v b)) ^ k *
      (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ (k - 1 - j)) =
      (∏ b ∈ univ.erase d, (u c - v b)) ^ k *
      ((u c - v d) ^ k * (Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ (k - 1 - j))) by ring]
  rw [Z3NetF.ySplit, pow_inv_cancel _ _ hD j k hj]

/-! ## `Φ^S_cd · Toep(Π_d(v_d + x)) = Ψ_cd` and the normal form -/

lemma skey_Psi (huv : Z3NetF.SplitOK u v) (c d : Fin s) (j : Fin k) (r : Fin (s * k - k)) :
    (Z3NetF.splitGraph R k u v c d * Z3NetF.toep k (Z3NetF.piSplit k v d)) r j =
      (Z3NetF.splitRead (s * k) k u v c *ᵥ sEvec k v d j) ⟨k + r, by omega⟩ := by
  have hspec := (split_spec_core k u v huv).2 c
  rw [← hspec, ← mulVec_mulVec]
  have := graphGenK_mulVec_off (m := s * k) (fun _ => k) (sum_const_k k)
    (Z3NetF.splitGraph R k u v) c (GkS k u v *ᵥ sEvec k v d j) r
  refine Eq.trans ?_ this.symm
  rw [Finset.sum_eq_single d, mul_apply]
  · refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [box_mulVec_pre _ _ (sum_const_k k) _ d l l.isLt]
    rw [scell k u v d d j j.isLt l l.isLt, if_pos rfl]
  · intro d' _ hd'
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [box_mulVec_pre _ _ (sum_const_k k) _ d' l l.isLt]
    rw [scell k u v d' d j j.isLt l l.isLt, if_neg hd', mul_zero]
  · simp

lemma two_le_of_ne {c d : Fin s} (hcd : c ≠ d) : 2 ≤ s := by
  by_contra h; push_neg at h
  exact hcd (Fin.ext (by have := c.isLt; have := d.isLt; omega))

theorem Gsplit_normal (k : ℕ) (u v : Fin s → R)
    (huv : Z3NetF.SplitOK u v) (c d : Fin s) (hcd : c ≠ d) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0)
    (j : Fin k) :
    (Z3NetF.Lgauge (s * k - k) (Ring.inverse (Z3NetF.Psplit u v c ^ k)) * Z3NetF.splitGraph R k u v c d *
        Z3NetF.toep k (Z3NetF.piSplit k v d)) r j =
      Z3NetF.ySplit u v c d * Z3NetF.ySplit u v c d ^ (k - 1 - (j : ℕ)) := by
  have hs := two_le_of_ne hcd
  rw [Matrix.mul_assoc, Z3NetF.Lgauge, diagonal_mul, if_pos hr, skey_Psi k u v huv c d j r]
  have hidx : (⟨k + (r : ℕ), by omega⟩ : Fin (s * k)) = ⟨k, by have := r.isLt; omega⟩ :=
    Fin.ext (by simp [hr])
  rw [hidx, soff k u v hs huv c d j j.isLt, ← mul_assoc,
    Ring.inverse_mul_cancel _ ((Psplit_unit huv c).pow k), one_mul]

/-! ## The nodes -/

theorem Gsplit_nodes (u v : Fin s → R) (huv : Z3NetF.SplitOK u v)
    (c c' d : Fin s) (hc : c ≠ d) (hc' : c' ≠ d) :
    IsUnit (Z3NetF.ySplit u v c d) ∧
      Z3NetF.ySplit u v c d - Z3NetF.ySplit u v c' d =
        (u c' - u c) * Ring.inverse ((u c - v d) * (u c' - v d)) ∧
      (c ≠ c' → IsUnit (Z3NetF.ySplit u v c d - Z3NetF.ySplit u v c' d)) := by
  have e : Z3NetF.ySplit u v c d - Z3NetF.ySplit u v c' d =
      (u c' - u c) * Ring.inverse ((u c - v d) * (u c' - v d)) := by
    have h1 := Ring.inverse_mul_cancel _ (split_uv huv c d)
    have h2 := Ring.inverse_mul_cancel _ (split_uv huv c' d)
    rw [Z3NetF.ySplit, Z3NetF.ySplit, Ring.mul_inverse_rev]
    linear_combination (Ring.inverse (u c' - v d)) * h1 - (Ring.inverse (u c - v d)) * h2
  refine ⟨ySplit_unit huv c d, e, fun hcc' => ?_⟩
  rw [e]
  exact (split_uu huv c' c (Ne.symm hcc')).mul
    ((split_uv huv c d).mul (split_uv huv c' d)).ringInverse

/-! ## The compared statements `split_spec`, `split_boxMinor` -/

theorem split_spec {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (u v : Fin s → R)
    (huv : Z3NetF.SplitOK u v) :
    IsUnit (Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) (fun _ => k)).det ∧
      ∀ c, Z3NetF.graphGenK (m := s * k) (fun _ => k) (Z3NetF.splitGraph R k u v) c *
        Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) (fun _ => k) =
          Z3NetF.splitRead (s * k) k u v c :=
  split_spec_core k u v huv

theorem split_boxMinor {R : Type*} [CommRing R] {s : ℕ} (k : ℕ) (u v : Fin s → R)
    (huv : Z3NetF.SplitOK u v) (d : Fin s → ℕ) (_hd : ∑ c, d c = s * k) :
    (Z3NetF.boxMatrix (Z3NetF.graphGenK (m := s * k) (fun _ => k) (Z3NetF.splitGraph R k u v)) d).det *
        (Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) (fun _ => k)).det =
      (Z3NetF.boxMatrix (Z3NetF.splitRead (s * k) k u v) d).det :=
  split_boxMinor_core k u v huv d

end

end Z3NetF.Proofs

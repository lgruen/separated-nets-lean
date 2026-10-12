module
public import Mathlib
public import Z3Net.HLNet
public import Z3Net.SURows

@[expose] public section

/-!
# Entry HL, part 4: Prop N′ (Cauchy kernel) and (H1) (row `0` of every block is the design)

* `psi0_eval`: `Ψ_cd[0, j] = E_{d,j}(u_c) = ∏_{d' ≠ d} (u_c - v_{d'})^k (u_c - v_d)^j`.
* `HL_propN` over `ℚ`; over `ℤ/qℤ` the row scaling turns row `0` into `y_cd^(n+1)` at `x`-index `n`.
* The gauge columns `n < s-1` produce `λ'_c ∑_{n' ≤ n} gco d n n' y^(n'+1)` (the design), the
  columns `n ≥ s-1` produce `λ'_c y (y^n - ∑_i γ_{n,i} y^i) = 0` (Lagrange remainder,
  `Z3NetU.Proofs.xpowRem_eval`).
-/

namespace Z3NetHL.Proofs

open Polynomial Finset Matrix

noncomputable section

/-! ## Bridges for the Lagrange remainder -/

lemma rootsPoly_eq {R : Type*} [CommRing R] :
    ∀ (ys : List R) (i : ℕ), Z3NetHL.rootsPoly ys i = Z3NetU.rootsPoly ys i
  | [], _ => rfl
  | y :: ys, i => by simp only [Z3NetHL.rootsPoly, Z3NetU.rootsPoly, rootsPoly_eq ys]

lemma xpowRem_eq {R : Type*} [CommRing R] (p : ℕ → R) (r : ℕ) :
    ∀ (n i : ℕ), Z3NetHL.xpowRem p r n i = Z3NetU.xpowRem p r n i
  | 0, _ => rfl
  | n + 1, i => by simp only [Z3NetHL.xpowRem, Z3NetU.xpowRem, xpowRem_eq p r n]

/-! ## Row `0` of `Ψ` -/

lemma psi0_eval {s : ℕ} (k : ℕ) (u v : Fin s → ℤ) (hs : 1 ≤ s) (c d : Fin s) (r : Fin (s * k - k))
    (hr : (r : ℕ) = 0) (j : Fin k) :
    Psi k u v c d r j = (∏ d' ∈ univ.erase d, (u c - v d') ^ k) * (u c - v d) ^ (j : ℕ) := by
  have hdeg : (Epoly k v d j).natDegree < s * k := by
    have := natDegree_Epoly_le v k d j
    have : (s - 1) * k + j < s * k := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have := j.isLt
      simp only [Nat.add_sub_cancel]; nlinarith
    omega
  simp only [Psi, mulVec, dotProduct]
  rw [split_reading (s * k) k u v c (Epoly k v d j) hdeg]
  rw [if_neg (by simp), show k + (r : ℕ) - k = 0 by omega, taylor_coeff_zero]
  simp [Epoly, eval_prod]

/-! ## Prop N′ over `ℚ` -/

theorem HL_propN (s k : ℕ) (u v : Fin s → ℤ) (c d : Fin s) (hcd : c ≠ d)
    (huv : ∀ d', u c ≠ v d') (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) (j : Fin k) :
    (Psi k u v c d r j : ℚ) =
      (∏ d' : Fin s, ((u c - v d' : ℤ) : ℚ)) ^ k * yQ u v c d ^ (k - (j : ℕ)) := by
  have hs : 1 ≤ s := by have := c.isLt; omega
  rw [psi0_eval k u v hs c d r hr j]
  have hne : ((u c - v d : ℤ) : ℚ) ≠ 0 := by
    have := huv d; exact_mod_cast sub_ne_zero.mpr this
  rw [← Finset.mul_prod_erase _ _ (mem_univ d), mul_pow, yQ]
  push_cast
  have hj := j.isLt
  rw [inv_pow]
  have e : ((u c : ℚ) - v d) ^ k = ((u c : ℚ) - v d) ^ (j : ℕ) * ((u c : ℚ) - v d) ^ (k - (j : ℕ)) := by
    rw [← pow_add]; congr 1; omega
  have hne' : ((u c : ℚ) - v d) ^ (k - (j : ℕ)) ≠ 0 := pow_ne_zero _ (by push_cast at hne; exact hne)
  rw [e, ← Finset.prod_pow]
  field_simp

/-! ## Row `0` over `ℤ/qℤ` -/

section row0

variable {s q : ℕ} (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
  (dg : Fin s → ℕ → ℚ)

/-- The nodes of column `d`. -/
def nodesZ (d : Fin s) : List (ZMod q) :=
  ((List.finRange s).filter (fun c => c ≠ d)).map (fun c => yZ q u v c d)

lemma nodesZ_length (d : Fin s) : (nodesZ (q := q) u v d).length = s - 1 := by
  rw [nodesZ, List.length_map]
  have h1 := List.length_eq_length_filter_add (l := List.finRange s) (fun c => decide (c ≠ d))
  have h2 : ((List.finRange s).filter (fun c => !decide (c ≠ d))).length = 1 := by
    have : (List.finRange s).filter (fun c => !decide (c ≠ d)) =
        (List.finRange s).filter (fun c => c == d) := by
      congr 1; funext c; simp; rfl
    rw [this, ← List.count_eq_length_filter]
    exact List.count_eq_one_of_mem (List.nodup_finRange s) (List.mem_finRange d)
  rw [List.length_finRange] at h1
  omega

lemma nodeZ_root (c d : Fin s) (hcd : c ≠ d) :
    ∑ i ∈ range (s - 1), Z3NetU.rootsPoly (nodesZ (q := q) u v d) i * yZ q u v c d ^ i +
      yZ q u v c d ^ (s - 1) = 0 := by
  have h := Z3NetU.Proofs.rootsPoly_eval (nodesZ (q := q) u v d) (yZ q u v c d)
  rw [nodesZ_length, Finset.sum_range_succ, ← nodesZ_length (q := q) u v d,
    Z3NetU.Proofs.rootsPoly_top, one_mul, nodesZ_length] at h
  rw [h]
  apply List.prod_eq_zero
  rw [List.mem_map]
  refine ⟨yZ q u v c d, ?_, sub_self _⟩
  rw [nodesZ, List.mem_map]
  exact ⟨c, List.mem_filter.mpr ⟨List.mem_finRange c, by simpa using hcd⟩, rfl⟩

/-- **Prop G′** (defining relation of `γ_n`): `y^n = ∑_{i < s-1} γ_{n,i} y^i` at every node. -/
lemma propG' (hs : 2 ≤ s) (c d : Fin s) (hcd : c ≠ d) (n : ℕ) :
    yZ q u v c d ^ n = ∑ i ∈ range (s - 1), gamZ q u v d n i * yZ q u v c d ^ i := by
  have := Z3NetU.Proofs.xpowRem_eval (Z3NetU.rootsPoly (nodesZ (q := q) u v d)) (s - 1) (by omega)
    (yZ q u v c d) (nodeZ_root u v c d hcd) n
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gamZ, xpowRem_eq, nodesZ]
  congr 2
  funext t
  rw [rootsPoly_eq]

lemma sum_reflectZ (k : ℕ) (d : Fin s) (f : ℕ → ZMod q) (j : Fin k) :
    ∑ j' : Fin k, f (k - 1 - (j' : ℕ)) * UkZ q u v gco k d j' j =
      ∑ n' ∈ range k, f n' * UxZ q u v gco d n' (k - 1 - (j : ℕ)) := by
  simp only [UkZ]
  rw [Fin.sum_univ_eq_sum_range (fun i => f (k - 1 - i) * UxZ q u v gco d (k - 1 - i) (k - 1 - (j : ℕ))) k]
  exact Finset.sum_range_reflect (fun n' => f n' * UxZ q u v gco d n' (k - 1 - (j : ℕ))) k

/-- The scaled row `0` of `Ψ`: `P_c^(-k) Ψ_cd[0, j'] = y_cd^(k - j')`. -/
lemma scaled_psi0 (hs : 1 ≤ s) (k : ℕ) (c d : Fin s) (hcd : c ≠ d)
    (hP : ∀ d', IsUnit (((u c - v d' : ℤ)) : ZMod q)) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0)
    (j' : Fin k) :
    PinvZ q u v c ^ k * ((Psi k u v c d r j' : ℤ) : ZMod q) = yZ q u v c d ^ (k - (j' : ℕ)) := by
  rw [psi0_eval k u v hs c d r hr j']
  have hj := j'.isLt
  set e : ZMod q := ((u c - v d : ℤ) : ZMod q) with he
  set Q : ZMod q := ∏ d' ∈ univ.erase d, ((u c - v d' : ℤ) : ZMod q) with hQ
  have hQu : IsUnit Q := by rw [hQ, IsUnit.prod_iff]; intro d' _; exact hP d'
  have heu : IsUnit e := hP d
  have hPinv : PinvZ q u v c = e⁻¹ * Q⁻¹ := by
    unfold PinvZ
    rw [← Finset.mul_prod_erase _ _ (mem_univ d), zinv_mul heu hQu]
  have hy : yZ q u v c d = e⁻¹ := rfl
  push_cast
  rw [show (∏ d' ∈ univ.erase d, ((u c : ZMod q) - v d') ^ k) = Q ^ k by
    rw [hQ, ← Finset.prod_pow]; push_cast; rfl]
  rw [show ((u c : ZMod q) - v d) = e by rw [he]; push_cast; rfl, hPinv, hy]
  have hQ1 := ZMod.inv_mul_of_unit _ hQu
  have he1 := ZMod.inv_mul_of_unit _ heu
  have ek : (e⁻¹) ^ k = (e⁻¹) ^ (k - (j' : ℕ)) * (e⁻¹) ^ (j' : ℕ) := by
    rw [← pow_add]; congr 1; omega
  calc (e⁻¹ * Q⁻¹) ^ k * (Q ^ k * e ^ (j' : ℕ))
      = (e⁻¹) ^ k * e ^ (j' : ℕ) * (Q⁻¹ * Q) ^ k := by ring
    _ = (e⁻¹) ^ (k - (j' : ℕ)) * (e⁻¹ * e) ^ (j' : ℕ) := by rw [hQ1, one_pow, mul_one, ek]; ring
    _ = (e⁻¹) ^ (k - (j' : ℕ)) := by rw [he1, one_pow, mul_one]

theorem HL_row0 (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) (hs : 2 ≤ s) (hq : HLAdm s q u v lam gco) (hden : HLDen s q gco dg)
    (hk : 1 ≤ k) (c d : Fin s) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) (j : Fin k) :
    HLPhi s q k u v lam gco dg c d r j = qr q (HLdes u v lam gco dg (k - 1 - (j : ℕ)) c d) := by
  have hj := j.isLt
  set n := k - 1 - (j : ℕ) with hn
  by_cases hcd : c = d
  · subst hcd
    simp only [HLPhi, HLdes, if_true, hr, true_and]
    by_cases h1 : n < s - 1
    · rw [if_pos h1, if_neg (by omega)]
    · rw [if_neg h1, if_pos (by omega)]
      simpa using (qr_int (q := q) 0).symm
  obtain ⟨hpts, hlam, hlead⟩ := adm_units hq
  have hP : ∀ d', IsUnit (((u c - v d' : ℤ)) : ZMod q) := by
    intro d'
    have := hpts c 1 d' 0 (by simp)
    simpa [splitPt] using this
  have e : HLPhi s q k u v lam gco dg c d r j = qr q (lam c) * ∑ j' : Fin k,
      yZ q u v c d ^ (k - 1 - (j' : ℕ) + 1) * UkZ q u v gco k d j' j := by
    simp only [HLPhi, if_neg hcd, hr, if_true, mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have := scaled_psi0 u v (by omega) k c d hcd hP r hr j'
    have hj' := j'.isLt
    rw [show k - 1 - (j' : ℕ) + 1 = k - (j' : ℕ) by omega, ← this]
    ring
  rw [e, sum_reflectZ u v gco k d (fun n' => yZ q u v c d ^ (n' + 1)) j]
  rw [← hn]
  have hnk : n < k := by omega
  have hyQ : Good q (yQ u v c d) ∧ qr q (yQ u v c d) = yZ q u v c d := good_inv_int _ (hP d)
  by_cases hns : n < s - 1
  · have hdes : HLdes u v lam gco dg n c d =
        lam c * ∑ n' ∈ range (n + 1), gco d n n' * yQ u v c d ^ (n' + 1) := by
      simp only [HLdes, if_neg (show ¬ s - 1 ≤ n by omega), if_neg hcd]
    have hgood : ∀ n' ∈ range (n + 1), Good q (gco d n n' * yQ u v c d ^ (n' + 1)) ∧
        qr q (gco d n n' * yQ u v c d ^ (n' + 1)) = qr q (gco d n n') * yZ q u v c d ^ (n' + 1) := by
      intro n' hn'
      rw [mem_range] at hn'
      have hg : Good q (gco d n n') := isUnit_nat_of_coprime (hden.1 d n hns n' (by omega))
      obtain ⟨h1, h2⟩ := good_pow hyQ.1 (n' + 1)
      obtain ⟨h3, h4⟩ := good_mul hg h1
      exact ⟨h3, by rw [h4, h2, hyQ.2]⟩
    obtain ⟨hs1, hs2⟩ := good_sum _ _ (fun n' hn' => (hgood n' hn').1)
    have hl : Good q (lam c) := isUnit_nat_of_coprime (hq.2.2.1 c).2
    rw [hdes, (good_mul hl hs1).2, hs2, Finset.sum_congr rfl (fun n' hn' => (hgood n' hn').2)]
    congr 1
    rw [← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ k by omega)]
    rw [Finset.sum_eq_zero (s := Ico (n + 1) k), add_zero]
    · refine Finset.sum_congr rfl fun n' hn' => ?_
      rw [mem_range] at hn'
      simp only [UxZ, if_pos hns, if_pos (show n' ≤ n by omega)]
      ring
    · intro n' hn'
      rw [mem_Ico] at hn'
      rw [UxZ_upper u v gco d n' n (by omega), mul_zero]
  · have hdes : HLdes u v lam gco dg n c d = 0 := by
      simp only [HLdes, if_pos (show s - 1 ≤ n by omega)]
    rw [hdes, show (0 : ℚ) = ((0 : ℤ) : ℚ) by simp, qr_int, Int.cast_zero]
    have e2 : ∑ n' ∈ range k, yZ q u v c d ^ (n' + 1) * UxZ q u v gco d n' n =
        yZ q u v c d * (yZ q u v c d ^ n -
          ∑ i ∈ range (s - 1), gamZ q u v d n i * yZ q u v c d ^ i) := by
      have hsplit : ∀ n', yZ q u v c d ^ (n' + 1) * UxZ q u v gco d n' n =
          (if n' = n then yZ q u v c d ^ (n + 1) else 0) -
            (if n' < s - 1 then yZ q u v c d * (gamZ q u v d n n' * yZ q u v c d ^ n') else 0) := by
        intro n'
        simp only [UxZ, if_neg hns]
        by_cases h1 : n' = n
        · rw [if_pos h1, if_pos h1, h1, if_neg hns, mul_one, sub_zero]
        · by_cases h2 : n' < s - 1
          · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]; ring
          · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, mul_zero, sub_zero]
      rw [Finset.sum_congr rfl (fun n' _ => hsplit n'), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' (range k) n, if_pos (mem_range.mpr hnk)]
      rw [← Finset.sum_filter, show (range k).filter (fun n' => n' < s - 1) = range (s - 1) by
        ext x; simp only [mem_filter, mem_range]; omega, ← Finset.mul_sum, pow_succ]
      ring
    rw [e2, ← propG' u v hs c d hcd n, sub_self, mul_zero, mul_zero]

end row0

end

end Z3NetHL.Proofs

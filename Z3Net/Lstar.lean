/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.LstarDefs
public import Z3Net.FDeficit
public import Z3Net.ObsO5
public import Z3Net.ThmAUstar

@[expose] public section

/-!
# V14 stage S7: lower bounds for the deficit of frame designs (`sec:Lstar`)

* `lem:O` (`O_core`): if `K(F) = K < ∞`, then for every pair `a ≠ b` all partial sums
  `M^(j)[a][b]` or all `M^(j)[b][a]` (`j < L`) are at most `K` in absolute value. First the
  one-axis steps (`own_le`: `0 ≤ -M^(j)[x][x] ≤ K`), then the two-axis step of the printed proof.
* `prop:E` (`E_core`): row scalars constant on the finite places of `∞, 0, …, s-2` force
  `K(F) ≥ lcm(1, …, s-3)`; the elementary form `2^(s-3) ≤ (s-2) K(F)` from Mathlib's
  `two_pow_le_mul_lcmUpto`.
* `lem:C` (`C_core`): the cross-ratio count `|C| ≤ 1 + 2Kτ*(n)τ*(nK)²`. The proof gives the
  sharper `1 + 2Kτ*(n)τ*(nK)` (`C_core_sharp`): in the case of two finite places the place is
  determined by `(h, B, β)`, the divisor `A` of the printed proof is not needed.
* The convexity count of `thm:L` with an arbitrary bound `B` per pair of columns (`pair_count`).
* `thm:Lstar` (`Lstar_core`), with `PGL₂(ℚ)`-images of the places (`wN_pgl`: the weights of the
  image frame are `ρ_c ν_d` times those of `∞, 0, …, s-2`).
-/

namespace Z3NetF.Proofs.Lstar

open Finset Matrix Z3NetF Z3NetF.Proofs.RemK Z3NetF.Proofs.Deficit

/-! ## `lem:O` -/

section orient

variable {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ)

/-- One-axis steps: `0 ≤ -M^(j)[x][x] ≤ K`. -/
lemma own_le {K : ℕ} (hK : Kdef F L = (K : WithTop ℕ)) (x : Fin s) (j : ℕ) (hj : j < L) :
    Msum F j x x ≤ 0 ∧ -Msum F j x x ≤ K := by
  have hm := e1_mem (k := L) x j hj
  obtain ⟨h0, h1⟩ := cfg_of_K F L hK hm
  have hσ : sigma F L (e1 x) (fun _ => j) x = Msum F j x x := by
    rw [sigma_e1, show min j (L - 1) = j by omega]
  have hbwd : bwd F L (e1 x) (fun _ => j) ⊆ {x} := by
    intro i hi
    have := (mem_bwd F L _ _ i).1 hi
    by_contra hix
    exact this.1 (by simp [e1, show i ≠ x from fun h => hix (by simp [h])])
  have hne : (bwd F L (e1 x) (fun _ => j)).Nonempty := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
  have heq : bwd F L (e1 x) (fun _ => j) = {x} :=
    Finset.Subset.antisymm hbwd (by
      obtain ⟨i, hi⟩ := hne
      have := hbwd hi
      rw [Finset.mem_singleton] at this
      subst this
      simpa using hi)
  have hx : x ∈ bwd F L (e1 x) (fun _ => j) := by rw [heq]; exact mem_singleton_self x
  have hx' := (mem_bwd F L _ _ x).1 hx
  have hk := h1 x heq
  rw [hσ] at hk hx'
  simp only [e1, ite_true, one_mul] at hx'
  replace hx' := hx'.2
  refine ⟨hx', ?_⟩
  have : ((Msum F j x x).natAbs : ℤ) ≤ K := by
    have : (Msum F j x x).natAbs ≤ K := le_trans (Nat.le_add_right _ _) hk
    exact_mod_cast this
  rw [Int.natCast_natAbs, abs_of_nonpos hx'] at this
  exact this

/-- The two-axis step `e_a + ε e_b`. -/
def e2 (a b : Fin s) (ε : ℤ) : Fin s → ℤ := fun d => if d = a then 1 else if d = b then ε else 0

lemma sigma_e2 (a b : Fin s) (hab : a ≠ b) (ε : ℤ) (j : Fin s → ℕ) (i : Fin s) :
    sigma F L (e2 a b ε) j i =
      Msum F (min (j a) (L - 1)) i a + ε * Msum F (min (j b) (L - 1)) i b := by
  unfold sigma
  rw [Fintype.sum_eq_add a b hab (fun d hd => by simp [e2, hd.1, hd.2])]
  simp [e2, hab.symm]

/-- **`lem:O`.** -/
theorem O_core {K : ℕ} (hK : Kdef F L = (K : WithTop ℕ)) (a b : Fin s) (hab : a ≠ b) :
    (∀ j < L, |Msum F j a b| ≤ K) ∨ ∀ j < L, |Msum F j b a| ≤ K := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨j1, hj1, hu⟩, ⟨j2, hj2, hv⟩⟩ := hcon
  set u := Msum F j1 a b with hudef
  set v := Msum F j2 b a with hvdef
  set ε : ℤ := if 0 < u then 1 else -1 with hε
  have hεu : ε * u = |u| := by
    rw [hε]; split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [abs_of_nonpos (not_lt.1 h)]; ring
  have hε1 : ε = 1 ∨ ε = -1 := by rw [hε]; split_ifs <;> simp
  have hε2 : ε * ε = 1 := by rcases hε1 with h | h <;> rw [h] <;> norm_num
  let j : Fin s → ℕ := fun d => if d = a then j2 else j1
  have hja : min (j a) (L - 1) = j2 := by simp only [j, ite_true]; omega
  have hjb : min (j b) (L - 1) = j1 := by simp only [j, hab.symm, ite_false]; omega
  have hm : (e2 a b ε, j) ∈ cfgs s L := by
    refine (mem_cfgs _ _).2 ⟨fun d => ?_, ⟨a, by simp [e2]⟩, fun d => ?_⟩
    · simp only [e2]; split_ifs <;> rcases hε1 with h | h <;> omega
    · simp only [j]; split_ifs <;> omega
  obtain ⟨h0, h1⟩ := cfg_of_K F L hK hm
  dsimp only at h0 h1
  have hσa : sigma F L (e2 a b ε) j a = Msum F j2 a a + ε * u := by
    rw [sigma_e2 F L a b hab, hja, hjb]
  have hσb : sigma F L (e2 a b ε) j b = v + ε * Msum F j1 b b := by
    rw [sigma_e2 F L a b hab, hja, hjb]
  have hea : e2 a b ε a = 1 := by simp [e2]
  have heb : e2 a b ε b = ε := by simp [e2, hab.symm]
  have hown_a := own_le F L hK a j2 hj2
  have hown_b := own_le F L hK b j1 hj1
  -- `a` is forward
  have hafwd : a ∉ bwd F L (e2 a b ε) j := by
    intro h
    have := ((mem_bwd F L _ _ a).1 h).2
    rw [hea, hσa, hεu, one_mul] at this
    omega
  have hsub : bwd F L (e2 a b ε) j ⊆ {b} := by
    intro i hi
    have hi' := (mem_bwd F L _ _ i).1 hi
    rw [Finset.mem_singleton]
    by_contra hib
    by_cases hia : i = a
    · exact hafwd (hia ▸ hi)
    · exact hi'.1 (by simp [e2, hia, hib])
  have hbσ : ε * sigma F L (e2 a b ε) j b = ε * v + Msum F j1 b b := by
    rw [hσb, mul_add, ← mul_assoc, hε2, one_mul]
  have hεv : ε * v = |v| ∨ ε * v = -|v| := by
    rw [hε]; split_ifs
    · rw [one_mul]; rcases abs_choice v with h | h <;> [left; right] <;> linarith
    · rcases abs_choice v with h | h <;> [right; left] <;> linarith
  rcases hεv with hεv | hεv
  · -- `b` forward too: no backward coordinate
    apply h0
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro i hi
    have := hsub hi
    rw [Finset.mem_singleton] at this
    subst this
    have := ((mem_bwd F L _ _ i).1 hi).2
    rw [heb, hbσ, hεv] at this
    omega
  · -- `b` is the only backward coordinate
    have hbmem : b ∈ bwd F L (e2 a b ε) j := by
      refine (mem_bwd F L _ _ b).2 ⟨?_, ?_⟩
      · rw [heb]; rcases hε1 with h | h <;> omega
      · rw [heb, hbσ, hεv]; omega
    have heq : bwd F L (e2 a b ε) j = {b} :=
      Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.2 hbmem)
    have hk := h1 b heq
    have hjit : jit (e2 a b ε) b = 1 := by
      unfold jit
      split_ifs with h
      · exfalso
        have := h.2 a hab
        rw [hea] at this
        exact one_ne_zero this
      · rfl
    rw [hjit] at hk
    have hk' : (sigma F L (e2 a b ε) j b).natAbs + 1 ≤ (K : ℤ) := by exact_mod_cast hk
    have habs : |sigma F L (e2 a b ε) j b| = |v| - Msum F j1 b b := by
      have h1' : |ε * sigma F L (e2 a b ε) j b| = |sigma F L (e2 a b ε) j b| := by
        rw [abs_mul, show |ε| = 1 by rcases hε1 with h | h <;> rw [h] <;> norm_num, one_mul]
      rw [← h1', hbσ, hεv]
      rw [abs_of_nonpos (by linarith [abs_nonneg v])]
      ring
    have : ((sigma F L (e2 a b ε) j b).natAbs : ℤ) = |v| - Msum F j1 b b := by
      rw [Int.natCast_natAbs]; exact habs
    omega

end orient

/-! ## `prop:E` -/

section constE

/-- Level `0` of a reachable design (`prop:F` at `j = 0`): `F_0[c][d] = λ'_c w_cd κ_d` with
`κ_d = U'_d[0, 0]`; over `ℚ` the scalars are nonzero. -/
lemma res0 {s : ℕ} (hs : 2 ≤ s) {inf : Fin s} {x : Fin s → ℚ} {F : ℕ → Fin s → Fin s → ℤ}
    {lam : Fin s → ℚ} {Ur : Fin s → ℕ → ℕ → ℚ}
    (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur) :
    (∀ c, lam c ≠ 0) ∧ (∀ d, Ur d 0 0 ≠ 0) ∧
      ∀ c d, c ≠ d → (F 0 c d : ℚ) = lam c * wN inf x c d * Ur d 0 0 := by
  obtain ⟨hl, -, hU, hF⟩ := hres
  refine ⟨fun c => (hl c).ne_zero, fun d => (hU d 0 (by omega)).ne_zero, fun c d hcd => ?_⟩
  have := hF c d hcd 0 (by omega)
  simp only at this
  rw [this, Finset.sum_range_one, pow_zero, mul_one]; ring

/-- `lcm(1, …, N) ≤ |M|` if `M ≠ 0` and every `1 ≤ i ≤ N` divides `M`. -/
lemma lcmUpto_le {M : ℤ} (hM : M ≠ 0) (N : ℕ) (h : ∀ i : ℕ, 1 ≤ i → i ≤ N → (i : ℤ) ∣ M) :
    Nat.lcmUpto N ≤ M.natAbs := by
  refine Nat.le_of_dvd (Int.natAbs_pos.2 hM) ?_
  refine Finset.lcm_dvd fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  exact Int.natCast_dvd.1 (h i hi.1 hi.2)

lemma Msum_zero {s : ℕ} (F : ℕ → Fin s → Fin s → ℤ) (a b : Fin s) : Msum F 0 a b = F 0 a b := by
  simp [Msum]

/-- **`prop:E`.** -/
theorem E_core {s L K : ℕ} [NeZero s] (hs : 4 ≤ s) (hL : 1 ≤ L) (inf : Fin s) (x : Fin s → ℚ)
    (π : Fin s ≃ Fin s) (hinf : π inf = 0) (hx : ∀ c, c ≠ inf → x c = Z3NetA.placeA (π c))
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ) (Ur : Fin s → ℕ → ℕ → ℚ)
    (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur)
    (hlam : ∀ c d, c ≠ inf → d ≠ inf → lam c = lam d) (hK : Kdef F L = (K : WithTop ℕ)) :
    Nat.lcmUpto (s - 3) ≤ K := by
  obtain ⟨hl0, hU0, hF0⟩ := res0 (by omega) hres
  -- the coordinate of the place `i`
  let qc : ℕ → Fin s := fun i => π.symm ⟨(i + 1) % s, Nat.mod_lt _ (by omega)⟩
  have hqc : ∀ i (hi : i + 1 < s), π (qc i) = ⟨i + 1, hi⟩ := by
    intro i hi; simp only [qc, Equiv.apply_symm_apply, Nat.mod_eq_of_lt hi]
  have hqinf : ∀ i, i + 1 < s → qc i ≠ inf := by
    intro i hi h
    have := hqc i hi
    rw [h, hinf] at this
    exact absurd (congrArg Fin.val this) (by simp)
  have hxq : ∀ i, i + 1 < s → x (qc i) = (i : ℚ) := by
    intro i hi
    rw [hx _ (hqinf i hi), hqc i hi, Z3NetA.placeA]
    push_cast; ring
  have hqinj : ∀ i i', i + 1 < s → i' + 1 < s → qc i = qc i' → i = i' := by
    intro i i' hi hi' h
    have := congrArg (fun c => ((π c : Fin s) : ℕ)) h
    simp only [hqc i hi, hqc i' hi'] at this
    omega
  have hw : ∀ i i', i + 1 < s → i' + 1 < s → i ≠ i' →
      wN inf x (qc i) (qc i') = ((i : ℚ) - i')⁻¹ := by
    intro i i' hi hi' _
    simp only [wN, hqinf i hi, hqinf i' hi', or_self, ite_false, hxq i hi, hxq i' hi',
      Ring.inverse_eq_inv']
  set c0 := qc 0
  set c1 := qc 1
  have h0s : 0 + 1 < s := by omega
  have h1s : 1 + 1 < s := by omega
  set lm := lam c1
  have hlq : ∀ i, i + 1 < s → lam (qc i) = lm := fun i hi => hlam _ _ (hqinf i hi) (hqinf 1 h1s)
  -- column `c0` (place `0`), rows `qc i`, `1 ≤ i ≤ s-2`
  set M0 := F 0 c1 c0
  have hM0q : (M0 : ℚ) = lm * Ur c0 0 0 := by
    rw [hF0 _ _ (fun h => absurd (hqinj 1 0 h1s h0s h) (by norm_num)), hw 1 0 h1s h0s (by norm_num)]
    simp only [Nat.cast_one, Nat.cast_zero, sub_zero, inv_one, mul_one]; rfl
  have hM0 : M0 ≠ 0 := by
    intro h
    have : (M0 : ℚ) = 0 := by exact_mod_cast h
    rw [hM0q] at this
    exact mul_ne_zero (hl0 c1) (hU0 c0) this
  have hdiv0 : ∀ i : ℕ, 1 ≤ i → i ≤ s - 2 → (i : ℤ) ∣ M0 := by
    intro i hi1 hi2
    have his : i + 1 < s := by omega
    refine ⟨F 0 (qc i) c0, ?_⟩
    have e := hF0 (qc i) c0 (fun h => absurd (hqinj i 0 his h0s h) (by omega))
    rw [hw i 0 his h0s (by omega), hlq i his] at e
    have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
    have : (M0 : ℚ) = (i : ℚ) * (F 0 (qc i) c0 : ℚ) := by
      rw [hM0q, e, Nat.cast_zero, sub_zero]; field_simp
    exact_mod_cast this
  -- column `c1` (place `1`), rows `c0` and `qc i`, `2 ≤ i ≤ s-2`
  set M1 := F 0 c0 c1
  have hM1q : (M1 : ℚ) = -(lam c0 * Ur c1 0 0) := by
    rw [hF0 _ _ (fun h => absurd (hqinj 0 1 h0s h1s h) (by norm_num)), hw 0 1 h0s h1s (by norm_num)]
    norm_num; rfl
  have hM1 : M1 ≠ 0 := by
    intro h
    have : (M1 : ℚ) = 0 := by exact_mod_cast h
    rw [hM1q, neg_eq_zero] at this
    exact mul_ne_zero (hl0 c0) (hU0 c1) this
  have hdiv1 : ∀ i : ℕ, 1 ≤ i → i ≤ s - 3 → (i : ℤ) ∣ M1 := by
    intro i hi1 hi2
    have his : i + 2 < s := by omega
    refine ⟨-F 0 (qc (i + 1)) c1, ?_⟩
    have e := hF0 (qc (i + 1)) c1 (fun h => absurd (hqinj (i + 1) 1 his h1s h) (by omega))
    rw [hw (i + 1) 1 his h1s (by omega), hlq (i + 1) his, ← hlq 0 h0s] at e
    have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
    have hii : ((i + 1 : ℕ) : ℚ) - ((1 : ℕ) : ℚ) = i := by push_cast; ring
    rw [hii] at e
    have : (M1 : ℚ) = (i : ℚ) * -(F 0 (qc (i + 1)) c1 : ℚ) := by
      rw [hM1q, e]; field_simp; show _ = -(Ur c1 0 0 * lam c0); ring
    exact_mod_cast this
  have hl0' : Nat.lcmUpto (s - 3) ≤ M0.natAbs :=
    lcmUpto_le hM0 _ fun i h1 h2 => hdiv0 i h1 (by omega)
  have hl1' : Nat.lcmUpto (s - 3) ≤ M1.natAbs := lcmUpto_le hM1 _ hdiv1
  have hc01 : c0 ≠ c1 := fun h => absurd (hqinj 0 1 h0s h1s h) (by norm_num)
  rcases O_core F L hK c0 c1 hc01 with h | h
  · have := h 0 (by omega)
    rw [Msum_zero, Int.abs_eq_natAbs] at this
    have : M1.natAbs ≤ K := by exact_mod_cast this
    omega
  · have := h 0 (by omega)
    rw [Msum_zero, Int.abs_eq_natAbs] at this
    have : M0.natAbs ≤ K := by exact_mod_cast this
    omega

/-- **`prop:E`**, the elementary form (`W6`): `2^(s-3) ≤ (s-2) K(F)`, from Chebyshev's
`2^n ≤ (n+1) lcm(1, …, n)` (Mathlib's `two_pow_le_mul_lcmUpto`). -/
theorem E_two_pow_core {s L K : ℕ} [NeZero s] (hs : 4 ≤ s) (hL : 1 ≤ L) (inf : Fin s)
    (x : Fin s → ℚ) (π : Fin s ≃ Fin s) (hinf : π inf = 0)
    (hx : ∀ c, c ≠ inf → x c = Z3NetA.placeA (π c))
    (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ) (Ur : Fin s → ℕ → ℕ → ℚ)
    (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur)
    (hlam : ∀ c d, c ≠ inf → d ≠ inf → lam c = lam d) (hK : Kdef F L = (K : WithTop ℕ)) :
    2 ^ (s - 3) ≤ (s - 2) * K := by
  have h1 := E_core hs hL inf x π hinf hx F lam Ur hres hlam hK
  have h2 := Chebyshev.two_pow_le_mul_lcmUpto (s - 3)
  rw [show s - 3 + 1 = s - 2 by omega] at h2
  exact h2.trans (Nat.mul_le_mul_left _ h1)

/-! ## `U*_s` is in the class of `prop:E` -/

/-- `prop:E` applied to `U*_s` (`def:Ustar`, `λ' ≡ 1`, places `∞, 0, …, s-2`): if
`K(U*_s) = K < ∞` (with `L ≥ 1` levels), then `K ≥ lcm(1, …, s-3)`. -/
theorem E_Ustar_core {s L K : ℕ} [NeZero s] (hs : 4 ≤ s) (hL : 1 ≤ L)
    (hK : Kdef (Z3NetA.UstarF s) L = (K : WithTop ℕ)) : Nat.lcmUpto (s - 3) ≤ K := by
  obtain ⟨hx, Ur, hres⟩ := Z3NetA.Proofs.Ustar_reach_core (s := s) (by omega)
  have h := Z3NetF.Proofs.ObsO5.Residual_map (Z3NetA.Proofs.ι s) 0 Z3NetA.placeA hx _ _ _ hres
  have e1 : (fun c : Fin s => Z3NetA.Proofs.ι s (Z3NetA.placeA c)) = Z3NetA.placeA :=
    funext fun c => Z3NetA.Proofs.ι_place c
  have e2 : (fun n (c d : Fin s) => Z3NetA.Proofs.ι s (Z3NetA.UstarR s n c d)) =
      fun n c d => ((Z3NetA.UstarF s n c d : ℤ) : ℚ) :=
    funext fun n => funext fun c => funext fun d => by simp [Z3NetA.UstarR]
  rw [e1, e2] at h
  exact E_core hs hL 0 Z3NetA.placeA (Equiv.refl _) rfl (fun c _ => rfl) (Z3NetA.UstarF s) _ _ h
    (fun _ _ _ _ => rfl) hK

end constE

/-! ## `lem:C` -/

section crossratio

lemma tau_le_tauStar {m x : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ x) : m.divisors.card ≤ tauStar x :=
  Finset.le_sup (f := fun m => m.divisors.card) (Finset.mem_Icc.2 ⟨h1, h2⟩)

lemma one_le_tauStar {x : ℕ} (h : 1 ≤ x) : 1 ≤ tauStar x := by
  have := tau_le_tauStar (le_refl 1) h
  simpa [Nat.divisors_one] using this

/-- If `t ≠ 0` and `t X = Y u`, then `t / gcd(t, Y)` divides `u`. -/
lemma div_gcd_dvd {t X Y u : ℤ} (ht : t ≠ 0) (h : t * X = Y * u) :
    t / (Int.gcd t Y : ℤ) ∣ u := by
  have hg : 0 < Int.gcd t Y := Int.gcd_pos_of_ne_zero_left Y ht
  have hcop := Int.gcd_div_gcd_div_gcd hg
  set g : ℤ := (Int.gcd t Y : ℤ)
  have hg0 : g ≠ 0 := by simp only [g]; exact_mod_cast hg.ne'
  have ht' : t / g * g = t := Int.ediv_mul_cancel (Int.gcd_dvd_left t Y)
  have hY' : Y / g * g = Y := Int.ediv_mul_cancel (Int.gcd_dvd_right t Y)
  have h2 : t / g * X = Y / g * u := by
    apply mul_right_cancel₀ hg0
    calc t / g * X * g = (t / g * g) * X := by ring
      _ = Y * u := by rw [ht', h]
      _ = (Y / g * g) * u := by rw [hY']
      _ = Y / g * u * g := by ring
  exact Int.dvd_of_dvd_mul_right_of_gcd_one ⟨X, h2.symm⟩ hcop

/-- The values `t ≠ 0` with `|t / gcd(t, Y)| ≤ K` number at most `τ(|Y|) · 2K`
(`t = e t'` with `e ∣ Y`, `1 ≤ |t'| ≤ K`). -/
lemma count_div {Y : ℤ} (hY : Y ≠ 0) (K : ℕ) (T : Finset ℤ)
    (hT : ∀ t ∈ T, t ≠ 0 ∧ |t / (Int.gcd t Y : ℤ)| ≤ K) :
    T.card ≤ Y.natAbs.divisors.card * (2 * K) := by
  have hc2 : ((Icc (-(K : ℤ)) K).erase 0).card = 2 * K := by
    rw [card_erase_of_mem (mem_Icc.mpr ⟨by omega, by omega⟩), Int.card_Icc]; omega
  rw [← hc2, ← card_product]
  refine card_le_card_of_injOn (fun t => (Int.gcd t Y, t / (Int.gcd t Y : ℤ))) ?_ ?_
  · intro t ht
    obtain ⟨ht0, htK⟩ := hT t ht
    have hdt : t / (Int.gcd t Y : ℤ) * (Int.gcd t Y : ℤ) = t :=
      Int.ediv_mul_cancel (Int.gcd_dvd_left t Y)
    simp only [coe_product, Set.mem_prod, mem_coe, Nat.mem_divisors, mem_erase, mem_Icc]
    refine ⟨⟨Nat.gcd_dvd_right _ _, Int.natAbs_ne_zero.2 hY⟩, ?_, ?_, ?_⟩
    · intro h0; rw [h0, zero_mul] at hdt; exact ht0 hdt.symm
    · rw [abs_le] at htK; exact htK.1
    · rw [abs_le] at htK; exact htK.2
  · intro t1 _ t2 _ h
    simp only [Prod.mk.injEq] at h
    calc t1 = t1 / (Int.gcd t1 Y : ℤ) * (Int.gcd t1 Y : ℤ) :=
          (Int.ediv_mul_cancel (Int.gcd_dvd_left t1 Y)).symm
      _ = t2 / (Int.gcd t2 Y : ℤ) * (Int.gcd t2 Y : ℤ) := by rw [h.2, h.1]
      _ = t2 := Int.ediv_mul_cancel (Int.gcd_dvd_left t2 Y)

/-- The values `v` with `v ≠ 0`, `v - g ≠ 0` and `|v' / gcd(v', P)| ≤ K`, `v' = v / gcd(v - g, v)`,
number at most `τ(|g|) τ(|P|) · 2K` (`v = h B β` with `h ∣ g`, `B ∣ P`, `1 ≤ |β| ≤ K`). -/
lemma count_div2 {g P : ℤ} (hg : g ≠ 0) (hP : P ≠ 0) (K : ℕ) (V : Finset ℤ)
    (hV : ∀ v ∈ V, v ≠ 0 ∧ |(v / (Int.gcd (v - g) v : ℤ)) /
      (Int.gcd (v / (Int.gcd (v - g) v : ℤ)) P : ℤ)| ≤ K) :
    V.card ≤ g.natAbs.divisors.card * P.natAbs.divisors.card * (2 * K) := by
  have hc2 : ((Icc (-(K : ℤ)) K).erase 0).card = 2 * K := by
    rw [card_erase_of_mem (mem_Icc.mpr ⟨by omega, by omega⟩), Int.card_Icc]; omega
  rw [← hc2, ← card_product, ← card_product]
  let hh : ℤ → ℕ := fun v => Int.gcd (v - g) v
  let v' : ℤ → ℤ := fun v => v / (hh v : ℤ)
  let BB : ℤ → ℕ := fun v => Int.gcd (v' v) P
  have e1 : ∀ v, v' v * (hh v : ℤ) = v := fun v => Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)
  have e2 : ∀ v, v' v / (BB v : ℤ) * (BB v : ℤ) = v' v :=
    fun v => Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)
  refine card_le_card_of_injOn (fun v => ((hh v, BB v), v' v / (BB v : ℤ))) ?_ ?_
  · intro v hv
    obtain ⟨hv0, hvK⟩ := hV v hv
    simp only [coe_product, Set.mem_prod, mem_coe, Nat.mem_divisors, mem_erase, mem_Icc]
    refine ⟨⟨⟨?_, Int.natAbs_ne_zero.2 hg⟩, Nat.gcd_dvd_right _ _, Int.natAbs_ne_zero.2 hP⟩,
      ?_, ?_, ?_⟩
    · have h1 : (hh v : ℤ) ∣ v - g := Int.gcd_dvd_left _ _
      have h2 : (hh v : ℤ) ∣ v := Int.gcd_dvd_right _ _
      have : (hh v : ℤ) ∣ g := by
        have := dvd_sub h2 h1; rwa [sub_sub_cancel] at this
      exact Int.ofNat_dvd_left.1 this
    · intro h0
      have := e2 v; rw [h0, zero_mul] at this
      have h1 := e1 v; rw [← this, zero_mul] at h1
      exact hv0 h1.symm
    · rw [abs_le] at hvK; exact hvK.1
    · rw [abs_le] at hvK; exact hvK.2
  · intro v1 _ v2 _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    calc v1 = v' v1 / (BB v1 : ℤ) * (BB v1 : ℤ) * (hh v1 : ℤ) := by rw [e2, e1]
      _ = v' v2 / (BB v2 : ℤ) * (BB v2 : ℤ) * (hh v2 : ℤ) := by rw [h3, h2, h1]
      _ = v2 := by rw [e2, e1]

/-- The weights of the places `∞, 0, …, n`: finite `c, d`. -/
lemma wstd_fin {n : ℕ} (c d : Fin (n + 2)) (hc : c ≠ 0) (hd : d ≠ 0) :
    wN (0 : Fin (n + 2)) Z3NetA.placeA c d = ((((c : ℕ) : ℤ) - ((d : ℕ) : ℤ) : ℤ) : ℚ)⁻¹ := by
  simp only [wN, hc, hd, or_self, ite_false, Ring.inverse_eq_inv', Z3NetA.placeA]
  push_cast; ring_nf

lemma wstd_inf {n : ℕ} (c d : Fin (n + 2)) (h : c = 0 ∨ d = 0) :
    wN (0 : Fin (n + 2)) (Z3NetA.placeA : Fin (n + 2) → ℚ) c d = 1 := by
  unfold wN; simp only [h, ite_true]

lemma abs_sub_le {n : ℕ} (c d : Fin (n + 2)) (hc : c ≠ 0) (hd : d ≠ 0) :
    |((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)| ≤ n := by
  have hc' : 1 ≤ (c : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hc (Fin.ext h))
  have hd' : 1 ≤ (d : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hd (Fin.ext h))
  have := c.isLt; have := d.isLt
  rw [abs_le]; constructor <;> omega

lemma sub_ne_zero' {n : ℕ} {c d : Fin (n + 2)} (h : c ≠ d) : ((c : ℕ) : ℤ) - ((d : ℕ) : ℤ) ≠ 0 := by
  intro h0; apply h; apply Fin.ext; omega

lemma mem_QK' {K : ℕ} {z : ℚ} (h : z ∈ QK K) :
    ∃ a b : ℤ, a ≠ 0 ∧ |a| ≤ K ∧ b ≠ 0 ∧ |b| ≤ K ∧ z = (a : ℚ) / b := by
  obtain ⟨a, b, ha1, ha, hb1, hb, hz⟩ := h
  refine ⟨a, b, ?_, ha, ?_, hb, hz⟩
  · rintro rfl; norm_num at ha1
  · rintro rfl; norm_num at hb1

/-- From `|β| ≤ K` for a divisor of a nonzero `b` with `|b| ≤ K`. -/
lemma abs_le_of_dvd' {β b : ℤ} {K : ℕ} (h : β ∣ b) (hb : b ≠ 0) (hbK : |b| ≤ K) : |β| ≤ K := by
  have := Int.natAbs_le_of_dvd_ne_zero h hb
  rw [Int.abs_eq_natAbs] at hbK ⊢
  have : (β.natAbs : ℤ) ≤ b.natAbs := by exact_mod_cast this
  omega

/-- The bound on the numerator/denominator of `r`: `Y ∣ t X v` with `gcd(Y, X) = 1`, `|t| ≤ n`,
`|v| ≤ K` give `1 ≤ |Y| ≤ nK`. -/
lemma natAbs_le_nK {Y X t v : ℤ} {n K : ℕ} (hY : Y ≠ 0) (hcop : Int.gcd Y X = 1)
    (hd : Y ∣ t * X * v) (ht0 : t ≠ 0) (ht : |t| ≤ n) (hv0 : v ≠ 0) (hv : |v| ≤ K) :
    1 ≤ Y.natAbs ∧ Y.natAbs ≤ n * K := by
  refine ⟨Int.natAbs_pos.2 hY, ?_⟩
  have h1 : Y ∣ X * (t * v) := by rw [show X * (t * v) = t * X * v by ring]; exact hd
  have h2 := Int.dvd_of_dvd_mul_right_of_gcd_one h1 hcop
  have h3 := Int.natAbs_le_of_dvd_ne_zero h2 (mul_ne_zero ht0 hv0)
  rw [Int.natAbs_mul] at h3
  rw [Int.abs_eq_natAbs] at ht hv
  have ht' : t.natAbs ≤ n := by exact_mod_cast ht
  have hv' : v.natAbs ≤ K := by exact_mod_cast hv
  exact h3.trans (Nat.mul_le_mul ht' hv')

/-- Cross-multiplication in the three cases of `lem:C`. -/
lemma crossA {t P Q a b : ℤ} (ht : t ≠ 0) (hQ : Q ≠ 0) (hb : b ≠ 0)
    (h : ((t : ℚ))⁻¹ = (P : ℚ) / Q * ((a : ℚ) / b)) : t * (P * a) = Q * b := by
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  field_simp at h
  have : (t : ℚ) * (P * a) = Q * b := by linear_combination -h
  exact_mod_cast this
lemma crossA' {t P Q a b : ℤ} (hQ : Q ≠ 0) (hb : b ≠ 0)
    (h : (t : ℚ) = (P : ℚ) / Q * ((a : ℚ) / b)) : t * (Q * b) = P * a := by
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have : (t : ℚ) * (Q * b) = P * a := by rw [h]; field_simp
  exact_mod_cast this
lemma crossB {u v P Q a b : ℤ} (hu : u ≠ 0) (hv : v ≠ 0) (hQ : Q ≠ 0) (hb : b ≠ 0)
    (h : ((u : ℚ))⁻¹ / ((v : ℚ))⁻¹ = (P : ℚ) / Q * ((a : ℚ) / b)) : v * (Q * b) = u * (P * a) := by
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  rw [inv_div_inv] at h
  have : (v : ℚ) * (Q * b) = u * (P * a) := by
    field_simp at h; linear_combination h
  exact_mod_cast this

/-- **`lem:C`**, sharp form: `|C| ≤ 1 + 2Kτ*(n)τ*(nK)` (the printed bound has `τ*(nK)²`). -/
theorem C_core_sharp {n K : ℕ} (d d' : Fin (n + 2)) (hdd : d ≠ d') (r : ℚ) (hr : r ≠ 0)
    (C : Finset (Fin (n + 2))) (hC : C.Nonempty)
    (hmem : ∀ c ∈ C, c ≠ d ∧ c ≠ d' ∧ ∃ z ∈ QK K,
      wN (0 : Fin (n + 2)) Z3NetA.placeA c d / wN (0 : Fin (n + 2)) Z3NetA.placeA c d' = r * z) :
    C.card ≤ 1 + 2 * K * tauStar n * tauStar (n * K) := by
  -- `r = P / Q`
  set P := r.num
  set Q : ℤ := (r.den : ℤ)
  have hP : P ≠ 0 := Rat.num_ne_zero.2 hr
  have hQ : Q ≠ 0 := by simp only [Q]; exact_mod_cast r.den_nz
  have hPQ : Int.gcd P Q = 1 := r.reduced
  have hQP : Int.gcd Q P = 1 := by rw [Int.gcd_comm]; exact hPQ
  have hrPQ : r = (P : ℚ) / Q := (Rat.num_div_den r).symm
  have hPq : (P : ℚ) ≠ 0 := by exact_mod_cast hP
  have hQq : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  obtain ⟨c0, hc0⟩ := hC
  obtain ⟨hc0d, hc0d', z0, hz0, -⟩ := hmem c0 hc0
  obtain ⟨a0, b0, ha00, ha0K, -, -, -⟩ := mem_QK' hz0
  have hK1 : 1 ≤ K := by
    have := Int.one_le_abs ha00; exact_mod_cast this.trans ha0K
  have hn1 : 1 ≤ n := by
    by_contra h
    have h1 := Fin.val_ne_of_ne hc0d
    have h2 := Fin.val_ne_of_ne hc0d'
    have h3 := Fin.val_ne_of_ne hdd
    have := c0.isLt; have := d.isLt; have := d'.isLt
    omega
  have hτn := one_le_tauStar hn1
  have hnK : 1 ≤ n * K := by nlinarith
  have hτnK := one_le_tauStar hnK
  -- the integer value of a coordinate
  let iv : Fin (n + 2) → ℤ := fun c => ((c : ℕ) : ℤ)
  have hiv : Set.InjOn iv (C : Set (Fin (n + 2))) := by
    intro c1 _ c2 _ h; apply Fin.ext; simp only [iv] at h; omega
  by_cases hd'0 : d' = 0
  · -- `d' = ∞`: `φ(c) = 1/t`, `t = c - d`
    have hd0 : d ≠ 0 := by rw [hd'0] at hdd; exact hdd
    let T := C.image fun c => iv c - iv d
    have hTc : T.card = C.card := card_image_of_injOn (fun c1 h1 c2 h2 h => hiv h1 h2 (sub_left_inj.1 h))
    have key : ∀ c ∈ C, iv c - iv d ≠ 0 ∧ |iv c - iv d| ≤ n ∧
        ∃ a b : ℤ, a ≠ 0 ∧ |a| ≤ K ∧ b ≠ 0 ∧ |b| ≤ K ∧ (iv c - iv d) * (P * a) = Q * b := by
      intro c hc
      obtain ⟨hcd, hcd', z, hz, hφ⟩ := hmem c hc
      have hc0 : c ≠ 0 := by rw [← hd'0]; exact hcd'
      obtain ⟨a, b, ha0, haK, hb0, hbK, rfl⟩ := mem_QK' hz
      refine ⟨sub_ne_zero' hcd, abs_sub_le c d hc0 hd0, a, b, ha0, haK, hb0, hbK, ?_⟩
      rw [wstd_fin c d hc0 hd0, wstd_inf c d' (Or.inr hd'0), div_one, hrPQ] at hφ
      exact crossA (sub_ne_zero' hcd) hQ hb0 hφ
    have hQn : 1 ≤ Q.natAbs ∧ Q.natAbs ≤ n * K := by
      obtain ⟨ht0, htn, a, b, ha0, haK, -, -, he⟩ := key c0 hc0
      exact natAbs_le_nK hQ hQP ⟨b, by rw [← he]; ring⟩ ht0 htn ha0 haK
    have hcnt := count_div hQ K T (by
      intro t ht
      obtain ⟨c, hc, rfl⟩ := mem_image.1 ht
      obtain ⟨ht0, -, a, b, -, -, hb0, hbK, he⟩ := key c hc
      exact ⟨ht0, abs_le_of_dvd' (div_gcd_dvd ht0 he) hb0 hbK⟩)
    rw [hTc] at hcnt
    have := tau_le_tauStar hQn.1 hQn.2
    calc C.card ≤ Q.natAbs.divisors.card * (2 * K) := hcnt
      _ ≤ tauStar (n * K) * (2 * K) := Nat.mul_le_mul_right _ this
      _ ≤ 1 + 2 * K * tauStar n * tauStar (n * K) := by
        have h3 := Nat.mul_le_mul_left (2 * K * tauStar (n * K)) hτn
        linarith
  by_cases hd0 : d = 0
  · -- `d = ∞`: `φ(c) = t`, `t = c - d'`
    let T := C.image fun c => iv c - iv d'
    have hTc : T.card = C.card := card_image_of_injOn (fun c1 h1 c2 h2 h => hiv h1 h2 (sub_left_inj.1 h))
    have key : ∀ c ∈ C, iv c - iv d' ≠ 0 ∧ |iv c - iv d'| ≤ n ∧
        ∃ a b : ℤ, a ≠ 0 ∧ |a| ≤ K ∧ b ≠ 0 ∧ |b| ≤ K ∧ (iv c - iv d') * (Q * b) = P * a := by
      intro c hc
      obtain ⟨hcd, hcd', z, hz, hφ⟩ := hmem c hc
      have hc0 : c ≠ 0 := by rw [← hd0]; exact hcd
      obtain ⟨a, b, ha0, haK, hb0, hbK, rfl⟩ := mem_QK' hz
      refine ⟨sub_ne_zero' hcd', abs_sub_le c d' hc0 hd'0, a, b, ha0, haK, hb0, hbK, ?_⟩
      rw [wstd_fin c d' hc0 hd'0, wstd_inf c d (Or.inr hd0), one_div, inv_inv, hrPQ] at hφ
      exact crossA' hQ hb0 hφ
    have hPn : 1 ≤ P.natAbs ∧ P.natAbs ≤ n * K := by
      obtain ⟨ht0, htn, a, b, -, -, hb0, hbK, he⟩ := key c0 hc0
      exact natAbs_le_nK hP hPQ ⟨a, by rw [← he]; ring⟩ ht0 htn hb0 hbK
    have hcnt := count_div hP K T (by
      intro t ht
      obtain ⟨c, hc, rfl⟩ := mem_image.1 ht
      obtain ⟨ht0, -, a, b, ha0, haK, -, -, he⟩ := key c hc
      exact ⟨ht0, abs_le_of_dvd' (div_gcd_dvd ht0 he) ha0 haK⟩)
    rw [hTc] at hcnt
    have := tau_le_tauStar hPn.1 hPn.2
    calc C.card ≤ P.natAbs.divisors.card * (2 * K) := hcnt
      _ ≤ tauStar (n * K) * (2 * K) := Nat.mul_le_mul_right _ this
      _ ≤ 1 + 2 * K * tauStar n * tauStar (n * K) := by
        have h3 := Nat.mul_le_mul_left (2 * K * tauStar (n * K)) hτn
        linarith
  -- `d, d'` finite: row `∞` and the finite rows, `φ(c) = v/u`, `u = c - d`, `v = c - d'`
  set g := iv d - iv d'
  have hg : g ≠ 0 := sub_ne_zero' hdd
  have hgn : 1 ≤ g.natAbs ∧ g.natAbs ≤ n := by
    refine ⟨Int.natAbs_pos.2 hg, ?_⟩
    have h1 := abs_sub_le d d' hd0 hd'0
    have h2 : (g.natAbs : ℤ) ≤ n := by rw [← Int.abs_eq_natAbs]; exact h1
    exact_mod_cast h2
  set Cf := C.filter fun c => ¬ c = 0
  have hsplit : C.card ≤ 1 + Cf.card := by
    have h1 : (C.filter fun c => c = 0).card ≤ 1 := by
      refine card_le_one.2 fun a ha b hb => ?_
      rw [(mem_filter.1 ha).2, (mem_filter.1 hb).2]
    have := card_filter_add_card_filter_not (s := C) (fun c => c = 0)
    simp only [Cf] at this ⊢; omega
  have key : ∀ c ∈ Cf, iv c - iv d' ≠ 0 ∧ |iv c - iv d'| ≤ n ∧ iv c - iv d ≠ 0 ∧
      ∃ a b : ℤ, a ≠ 0 ∧ |a| ≤ K ∧ b ≠ 0 ∧ |b| ≤ K ∧
        (iv c - iv d') * (Q * b) = (iv c - iv d) * (P * a) := by
    intro c hc
    obtain ⟨hcC, hc0⟩ := mem_filter.1 hc
    obtain ⟨hcd, hcd', z, hz, hφ⟩ := hmem c hcC
    obtain ⟨a, b, ha0, haK, hb0, hbK, rfl⟩ := mem_QK' hz
    refine ⟨sub_ne_zero' hcd', abs_sub_le c d' hc0 hd'0, sub_ne_zero' hcd, a, b, ha0, haK, hb0,
      hbK, ?_⟩
    rw [wstd_fin c d hc0 hd0, wstd_fin c d' hc0 hd'0, hrPQ] at hφ
    exact crossB (sub_ne_zero' hcd) (sub_ne_zero' hcd') hQ hb0 hφ
  rcases Cf.eq_empty_or_nonempty with he | ⟨c1, hc1⟩
  · rw [he, card_empty] at hsplit; omega
  have hPn : 1 ≤ P.natAbs ∧ P.natAbs ≤ n * K := by
    obtain ⟨hv0, hvn, hu0, a, b, -, -, hb0, hbK, he⟩ := key c1 hc1
    exact natAbs_le_nK hP hPQ ⟨(iv c1 - iv d) * a, by linear_combination he⟩ hv0 hvn hb0 hbK
  let V := Cf.image fun c => iv c - iv d'
  have hVc : V.card = Cf.card := card_image_of_injOn (fun c1 h1 c2 h2 h => hiv
    (mem_filter.1 h1).1 (mem_filter.1 h2).1 (sub_left_inj.1 h))
  have hcnt := count_div2 hg hP K V (by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hv
    obtain ⟨hv0, -, hu0, a, b, ha0, haK, -, -, he⟩ := key c hc
    refine ⟨hv0, ?_⟩
    have hug : iv c - iv d' - g = iv c - iv d := by simp only [g]; ring
    rw [hug]
    -- `h = gcd(u, v)`, `u = u' h`, `v = v' h`, `gcd(v', u') = 1`
    set u := iv c - iv d
    set v := iv c - iv d'
    have hh : 0 < Int.gcd u v := Int.gcd_pos_of_ne_zero_left v hu0
    set h : ℤ := (Int.gcd u v : ℤ)
    have hh0 : h ≠ 0 := by simp only [h]; exact_mod_cast hh.ne'
    have eu : u / h * h = u := Int.ediv_mul_cancel (Int.gcd_dvd_left u v)
    have ev : v / h * h = v := Int.ediv_mul_cancel (Int.gcd_dvd_right u v)
    have hcop : Int.gcd (v / h) (u / h) = 1 := by
      rw [Int.gcd_comm]; exact Int.gcd_div_gcd_div_gcd hh
    have he' : v / h * (Q * b) = u / h * (P * a) := by
      apply mul_right_cancel₀ hh0
      calc v / h * (Q * b) * h = (v / h * h) * (Q * b) := by ring
        _ = (u / h * h) * (P * a) := by rw [ev, eu, he]
        _ = u / h * (P * a) * h := by ring
    have hdv : v / h ∣ P * a :=
      Int.dvd_of_dvd_mul_right_of_gcd_one ⟨Q * b, he'.symm⟩ hcop
    obtain ⟨k, hk⟩ := hdv
    have hv'0 : v / h ≠ 0 := by
      intro h0; rw [h0, zero_mul] at ev; exact hv0 ev.symm
    exact abs_le_of_dvd' (div_gcd_dvd hv'0 hk.symm) ha0 haK)
  rw [hVc] at hcnt
  have h1 := tau_le_tauStar hgn.1 hgn.2
  have h2 := tau_le_tauStar hPn.1 hPn.2
  have : g.natAbs.divisors.card * P.natAbs.divisors.card * (2 * K) ≤
      tauStar n * tauStar (n * K) * (2 * K) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2)
  nlinarith

/-- **`lem:C`** as printed: `|C| ≤ 1 + 2Kτ*(n)τ*(nK)²`. -/
theorem C_core {n K : ℕ} (d d' : Fin (n + 2)) (hdd : d ≠ d') (r : ℚ) (hr : r ≠ 0)
    (C : Finset (Fin (n + 2))) (hC : C.Nonempty)
    (hmem : ∀ c ∈ C, c ≠ d ∧ c ≠ d' ∧ ∃ z ∈ QK K,
      wN (0 : Fin (n + 2)) Z3NetA.placeA c d / wN (0 : Fin (n + 2)) Z3NetA.placeA c d' = r * z) :
    C.card ≤ 1 + 2 * K * tauStar n * tauStar (n * K) ^ 2 := by
  have h := C_core_sharp d d' hdd r hr C hC hmem
  rcases Nat.eq_zero_or_pos (tauStar (n * K)) with h0 | h0
  · rw [h0] at h ⊢; simpa using h
  · calc C.card ≤ 1 + 2 * K * tauStar n * tauStar (n * K) := h
      _ ≤ 1 + 2 * K * tauStar n * tauStar (n * K) ^ 2 := by
        have : tauStar (n * K) ≤ tauStar (n * K) ^ 2 := by nlinarith
        have := Nat.mul_le_mul_left (2 * K * tauStar n) this
        omega

end crossratio

/-! ## The convexity count of `thm:L`, with an arbitrary bound per pair of columns -/

section convex

/-- **The convexity count** (proof of `thm:L`): if every pair of distinct coordinates carries an arc
`c → d` (`sm c d` or `sm d c`) and every two distinct columns `d, d'` have at most `B` common rows
`c` (`sm c d ∧ sm c d'`), then `s - 3 ≤ 4B`; i.e. some two columns have at least `(s-3)/4` common
rows. (`ObsL.L_core` is the case `B = 2K²`.) -/
theorem pair_count {s : ℕ} (hs : 4 ≤ s) (sm : Fin s → Fin s → Prop) [DecidableRel sm]
    (harc : ∀ c d, c ≠ d → sm c d ∨ sm d c) (B : ℕ)
    (hB : ∀ d d', d ≠ d' → (univ.filter fun c => sm c d ∧ sm c d').card ≤ B) :
    (s : ℤ) - 3 ≤ 4 * B := by
  classical
  let sm' : Fin s → Fin s → Prop := fun c d => c ≠ d ∧ sm c d
  let D : Fin s → Finset (Fin s) := fun c => univ.filter (sm' c)
  -- (1) every pair carries an arc
  have h1 : (s : ℤ) * (s - 1) ≤ 2 * ∑ c, ((D c).card : ℤ) := by
    have e : ∀ c, ((D c).card : ℤ) = ∑ d, (if sm' c d then 1 else 0 : ℤ) := by
      intro c; simp only [D, card_filter]; push_cast; rfl
    simp only [e]
    have hsw : ∑ c, ∑ d, (if sm' c d then 1 else 0 : ℤ) = ∑ c, ∑ d, (if sm' d c then 1 else 0 : ℤ) :=
      Finset.sum_comm
    have : 2 * ∑ c, ∑ d, (if sm' c d then 1 else 0 : ℤ) =
        ∑ c, ∑ d, ((if sm' c d then 1 else 0 : ℤ) + (if sm' d c then 1 else 0)) := by
      rw [two_mul]; nth_rewrite 2 [hsw]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => (Finset.sum_add_distrib).symm
    rw [this]
    have hle : ∀ c d, (if c ≠ d then 1 else 0 : ℤ) ≤
        (if sm' c d then 1 else 0 : ℤ) + (if sm' d c then 1 else 0) := by
      intro c d
      by_cases hcd : c = d
      · simp only [hcd, ne_eq, not_true_eq_false, ite_false]
        split_ifs <;> norm_num
      · have hsm : sm' c d ∨ sm' d c := by
          rcases harc c d hcd with h | h
          · exact Or.inl ⟨hcd, h⟩
          · exact Or.inr ⟨Ne.symm hcd, h⟩
        simp only [ne_eq, hcd, not_false_eq_true, ite_true]
        rcases hsm with h | h
        · simp only [h, ite_true]; split_ifs <;> norm_num
        · simp only [h, ite_true]; split_ifs <;> norm_num
    calc (s : ℤ) * (s - 1) = ∑ c : Fin s, ∑ d : Fin s, (if c ≠ d then 1 else 0 : ℤ) := by
          have : ∀ c : Fin s, ∑ d : Fin s, (if c ≠ d then 1 else 0 : ℤ) = s - 1 := by
            intro c
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
              mul_one]
            have : (univ.filter fun d : Fin s => c ≠ d) = univ.erase c := by
              ext d; simp [eq_comm]
            rw [this, card_erase_of_mem (mem_univ c), card_univ, Fintype.card_fin]
            push_cast [Nat.cast_sub (show 1 ≤ s by omega)]; ring
          simp only [this, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => hle c d
  -- (2) the pairs of columns
  have h2 : ∑ c, (((D c).card : ℤ) ^ 2 - (D c).card) ≤ (B : ℤ) * ((s : ℤ) * (s - 1)) := by
    have e1 : ∀ c, ((D c).card : ℤ) ^ 2 - (D c).card = ((D c).offDiag.card : ℤ) := by
      intro c
      rw [offDiag_card, Nat.cast_sub (Nat.le_mul_self _)]; push_cast; ring
    simp only [e1]
    have e2 : ∀ c, ((D c).offDiag.card : ℤ) =
        ∑ p ∈ (univ : Finset (Fin s)).offDiag, (if sm' c p.1 ∧ sm' c p.2 then 1 else 0 : ℤ) := by
      intro c
      rw [Finset.sum_boole]
      congr 2
      ext p
      simp only [D, mem_offDiag, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h3, h1, h2⟩
      · rintro ⟨h3, h1, h2⟩; exact ⟨h1, h2, h3⟩
    simp only [e2]
    rw [Finset.sum_comm]
    have hb : ∀ p ∈ (univ : Finset (Fin s)).offDiag,
        ∑ c, (if sm' c p.1 ∧ sm' c p.2 then 1 else 0 : ℤ) ≤ (B : ℤ) := by
      intro p hp
      rw [mem_offDiag] at hp
      rw [Finset.sum_boole]
      have hsub : (univ.filter fun c => sm' c p.1 ∧ sm' c p.2) ⊆
          (univ.filter fun c => sm c p.1 ∧ sm c p.2) := by
        intro c hc
        simp only [mem_filter, mem_univ, true_and, sm'] at hc ⊢
        exact ⟨hc.1.2, hc.2.2⟩
      have := (card_le_card hsub).trans (hB p.1 p.2 hp.2.2)
      exact_mod_cast this
    calc ∑ p ∈ (univ : Finset (Fin s)).offDiag, ∑ c, (if sm' c p.1 ∧ sm' c p.2 then 1 else 0 : ℤ)
        ≤ ∑ p ∈ (univ : Finset (Fin s)).offDiag, (B : ℤ) := Finset.sum_le_sum hb
      _ = (B : ℤ) * ((s : ℤ) * (s - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, offDiag_card, card_univ, Fintype.card_fin,
          Nat.cast_sub (Nat.le_mul_self _)]
        push_cast; ring
  -- (3) Cauchy–Schwarz
  have h3 : (∑ c, ((D c).card : ℤ)) ^ 2 ≤ (s : ℤ) * ∑ c, ((D c).card : ℤ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin s)))
      (f := fun c => ((D c).card : ℤ))
    simpa using this
  set T := ∑ c, ((D c).card : ℤ)
  set Q := ∑ c, ((D c).card : ℤ) ^ 2
  have h2' : Q - T ≤ (B : ℤ) * ((s : ℤ) * (s - 1)) := by
    have : ∑ c, (((D c).card : ℤ) ^ 2 - (D c).card) = Q - T := by
      rw [Finset.sum_sub_distrib]
    rw [← this]; exact h2
  have hs' : (4 : ℤ) ≤ s := by exact_mod_cast hs
  have hA : 0 ≤ 2 * T - s * (s - 1) := by linarith
  have hB' : 0 ≤ 2 * T + s * (s - 1) - 2 * s := by nlinarith
  have hprod := mul_nonneg hA hB'
  have hmain : (s : ℤ) ^ 2 * (s - 1) * (s - 3) ≤ 4 * (B : ℤ) * ((s : ℤ) ^ 2 * (s - 1)) := by
    nlinarith
  have hpos : (0 : ℤ) < (s : ℤ) ^ 2 * (s - 1) := by
    have : (0 : ℤ) < s - 1 := by linarith
    positivity
  by_contra hcon
  push Not at hcon
  nlinarith

end convex

/-! ## `thm:Lstar` -/

section frame

/-- `D_cd = α_c β_d - α_d β_c` (before `lem:CH`). -/
def Dh (P Q : Fin 2 → ℚ) : ℚ := P 0 * Q 1 - Q 0 * P 1

/-- The sign `-1` of the column `∞` (`D_{c∞} = -1`, `w_{c∞} = 1`). -/
def sg {s : ℕ} (inf d : Fin s) : ℚ := if d = inf then -1 else 1

lemma sg_sq {s : ℕ} (inf d : Fin s) : sg inf d * sg inf d = 1 := by
  unfold sg; split_ifs <;> norm_num

/-- `w_cd = ±1/D_cd` in homogeneous coordinates (`prop:Ns`). -/
lemma wN_hom {s : ℕ} (inf : Fin s) (x : Fin s → ℚ) (c d : Fin s) (hcd : c ≠ d) :
    wN inf x c d = sg inf d / Dh (homPt inf x c) (homPt inf x d) := by
  unfold wN sg Dh homPt
  by_cases hc : c = inf
  · have hd : d ≠ inf := fun h => hcd (hc.trans h.symm)
    simp [hc, hd]
  · by_cases hd : d = inf
    · simp [hc, hd]
    · simp [hc, hd, Ring.inverse_eq_inv']

/-- `D` of the image: `D(t g P, t' g Q) = t t' det g · D(P, Q)`. -/
lemma Dh_smul {g : Matrix (Fin 2) (Fin 2) ℚ} (t t' : ℚ) (P Q : Fin 2 → ℚ) :
    Dh (t • g *ᵥ P) (t' • g *ᵥ Q) = t * t' * g.det * Dh P Q := by
  simp only [Dh, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.det_fin_two]
  ring

/-- The weights of a `PGL₂(ℚ)`-image of the places `∞, 0, …, s-2`: `w_cd = ρ_c ν_d w°_{π c, π d}`
with nonzero `ρ`, `ν` (the paper: "every `D_cd` is multiplied by a factor depending only on `c` times
one depending only on `d`"). -/
lemma wN_pgl {n : ℕ} (inf : Fin (n + 2)) (x : Fin (n + 2) → ℚ) (g : Matrix (Fin 2) (Fin 2) ℚ)
    (π : Fin (n + 2) ≃ Fin (n + 2)) (t : Fin (n + 2) → ℚ) (hg : g.det ≠ 0) (ht : ∀ c, t c ≠ 0)
    (hh : ∀ c, homPt inf x c = t c • g *ᵥ homPt (0 : Fin (n + 2)) Z3NetA.placeA (π c)) :
    ∃ ρ ν : Fin (n + 2) → ℚ, (∀ c, ρ c ≠ 0) ∧ (∀ d, ν d ≠ 0) ∧ ∀ c d, c ≠ d →
      wN inf x c d = ρ c * ν d * wN (0 : Fin (n + 2)) Z3NetA.placeA (π c) (π d) := by
  refine ⟨fun c => (t c)⁻¹, fun d => sg inf d * sg 0 (π d) * (t d * g.det)⁻¹,
    fun c => inv_ne_zero (ht c), fun d => ?_, fun c d hcd => ?_⟩
  · refine mul_ne_zero (mul_ne_zero ?_ ?_) (inv_ne_zero (mul_ne_zero (ht d) hg)) <;>
      · unfold sg; split_ifs <;> norm_num
  · have hpcd : π c ≠ π d := fun h => hcd (π.injective h)
    rw [wN_hom inf x c d hcd, wN_hom 0 _ _ _ hpcd, hh c, hh d, Dh_smul]
    set D := Dh (homPt 0 Z3NetA.placeA (π c)) (homPt 0 Z3NetA.placeA (π d))
    have hs := sg_sq (0 : Fin (n + 2)) (π d)
    simp only [div_eq_mul_inv, mul_inv]
    linear_combination (sg inf d * (t c)⁻¹ * (t d)⁻¹ * g.det⁻¹ * D⁻¹) * hs.symm

lemma wstd_ne {n : ℕ} (c d : Fin (n + 2)) (hcd : c ≠ d) :
    wN (0 : Fin (n + 2)) (Z3NetA.placeA : Fin (n + 2) → ℚ) c d ≠ 0 := by
  by_cases h : c = 0 ∨ d = 0
  · rw [wstd_inf c d h]; norm_num
  · push Not at h
    rw [wstd_fin c d h.1 h.2]
    exact inv_ne_zero (by exact_mod_cast sub_ne_zero' hcd)

/-- The places `∞, 0, …, s-2` themselves satisfy `PGLImage` (`g = 1`, `π = id`, `t = 1`). -/
theorem PGLImage_self_core {s : ℕ} [NeZero s] :
    PGLImage (0 : Fin s) (Z3NetA.placeA : Fin s → ℚ) :=
  ⟨1, Equiv.refl _, fun _ => 1, by simp, fun _ => one_ne_zero, fun c => by simp⟩

/-- **`thm:Lstar`.** -/
theorem Lstar_core {s L K : ℕ} [NeZero s] (hs : 5 ≤ s) (hL : 1 ≤ L) (inf : Fin s) (x : Fin s → ℚ)
    (hplace : PGLImage inf x) (F : ℕ → Fin s → Fin s → ℤ) (lam : Fin s → ℚ)
    (Ur : Fin s → ℕ → ℕ → ℚ) (hres : Residual inf x (fun n c d => (F n c d : ℚ)) lam Ur)
    (hK : Kdef F L = (K : WithTop ℕ)) :
    ((s : ℝ) - 3) / 4 ≤ 1 + 2 * (K : ℝ) * tauStar (s - 2) * (tauStar ((s - 2) * K) : ℝ) ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 2 := ⟨s - 2, by omega⟩
  obtain ⟨g, π, t, hg, ht, hh⟩ := hplace
  obtain ⟨hl0, hU0, hF0⟩ := res0 (by omega) hres
  obtain ⟨ρ, ν, hρ, hν, hw⟩ := wN_pgl inf x g π t hg ht hh
  have hwne : ∀ c d, c ≠ d → wN inf x c d ≠ 0 := by
    intro c d hcd
    rw [hw c d hcd]
    exact mul_ne_zero (mul_ne_zero (hρ c) (hν d))
      (wstd_ne _ _ (fun h => hcd (π.injective h)))
  have hFne : ∀ c d, c ≠ d → F 0 c d ≠ 0 := by
    intro c d hcd h0
    have := hF0 c d hcd
    rw [h0, Int.cast_zero] at this
    exact mul_ne_zero (mul_ne_zero (hl0 c) (hwne c d hcd)) (hU0 d) this.symm
  -- the orientation at level `0` (`lem:O`)
  let sm : Fin (n + 2) → Fin (n + 2) → Prop := fun c d => c ≠ d ∧ |F 0 c d| ≤ K
  have harc : ∀ c d, c ≠ d → sm c d ∨ sm d c := by
    intro c d hcd
    rcases O_core F L hK c d hcd with h | h
    · exact Or.inl ⟨hcd, by simpa [Msum_zero] using h 0 (by omega)⟩
    · exact Or.inr ⟨Ne.symm hcd, by simpa [Msum_zero] using h 0 (by omega)⟩
  set X := 1 + 2 * K * tauStar n * tauStar (n * K) ^ 2
  have hB : ∀ d d', d ≠ d' → (univ.filter fun c => sm c d ∧ sm c d').card ≤ X := by
    intro d d' hdd
    set C := univ.filter fun c => sm c d ∧ sm c d'
    rcases C.eq_empty_or_nonempty with he | hne
    · rw [he, card_empty]; exact Nat.zero_le _
    have hκ : ∀ e, Ur e 0 0 ≠ 0 := hU0
    let r : ℚ := ν d' / ν d * (Ur d' 0 0 / Ur d 0 0)
    have hr : r ≠ 0 := mul_ne_zero (div_ne_zero (hν d') (hν d)) (div_ne_zero (hκ d') (hκ d))
    have hcard := C_core (π d) (π d') (fun h => hdd (π.injective h)) r hr (C.map π.toEmbedding)
      (hne.map) (by
        intro c' hc'
        obtain ⟨c, hc, rfl⟩ := mem_map.1 hc'
        obtain ⟨⟨hcd, hcdK⟩, ⟨hcd', hcd'K⟩⟩ := (mem_filter.1 hc).2
        refine ⟨fun h => hcd (π.injective h), fun h => hcd' (π.injective h),
          (F 0 c d : ℚ) / (F 0 c d' : ℚ), ⟨F 0 c d, F 0 c d',
            Int.one_le_abs (hFne c d hcd), hcdK, Int.one_le_abs (hFne c d' hcd'), hcd'K, rfl⟩, ?_⟩
        simp only [Equiv.toEmbedding_apply]
        have e1 := hw c d hcd
        have e2 := hw c d' hcd'
        have f1 := hF0 c d hcd
        have f2 := hF0 c d' hcd'
        have hwS1 := wstd_ne (π c) (π d) (fun h => hcd (π.injective h))
        have hwS2 := wstd_ne (π c) (π d') (fun h => hcd' (π.injective h))
        have hρc := hρ c
        have hνd := hν d
        have hνd' := hν d'
        have hl := hl0 c
        have hk1 := hκ d
        have hk2 := hκ d'
        have hF2 : (F 0 c d' : ℚ) ≠ 0 := by exact_mod_cast hFne c d' hcd'
        rw [f1, f2, e1, e2]
        simp only [r]
        field_simp)
    rwa [card_map] at hcard
  have := pair_count (by omega) sm harc X hB
  have hX : ((n + 2 : ℕ) : ℝ) - 3 ≤ 4 * (X : ℝ) := by
    have : ((n + 2 : ℕ) : ℤ) - 3 ≤ 4 * (X : ℤ) := by exact_mod_cast this
    exact_mod_cast this
  simp only [X] at hX
  rw [show n + 2 - 2 = n by omega]
  push_cast at hX ⊢
  linarith

end frame

end Z3NetF.Proofs.Lstar

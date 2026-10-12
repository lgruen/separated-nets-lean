module
public import Z3Net.FHermite
public import Z3Net.FBox

@[expose] public section

/-!
# Entry F, part 5: `lem:hermite` (as stated) and the net criterion of `lem:Ts`

* `hermite_det_core`: the Hermite matrix of `n` points and an `∞`-jet is the frame box matrix with
  `∞` at the last coordinate; the product is re-indexed.
* `hermite_ne_zero_core`, `hermite_rows_core`: the two consequences.
* `frame_net_iff_core`: for rational places (reduced modulo `q`) and `m ≥ 2`: the frame is a
  `(0,m,s)`-net over `ℤ/qℤ` iff the finite places are distinct modulo every prime factor of `q`
  (`lem:nie` plus the exact minors; for the converse, the box with `d_c = m - 1`, `d_c' = 1`).
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

section hermite

variable {R : Type*} [CommRing R] {n m : ℕ}

/-- The places of the Hermite matrix as a frame (`∞` last). -/
def hx (x : Fin n → R) : Fin (n + 1) → R := fun P => if h : (P : ℕ) < n then x ⟨P, h⟩ else 0

/-- The multiplicities of the Hermite matrix as a frame. -/
def hα (α : Fin n → ℕ) (αinf : ℕ) : Fin (n + 1) → ℕ :=
  fun P => if h : (P : ℕ) < n then α ⟨P, h⟩ else αinf

lemma hermite_eq_frame (x : Fin n → R) (α : Fin n → ℕ) (αinf : ℕ) :
    Z3NetF.hermiteMat m x α αinf = Z3NetF.boxMatrix (Z3NetF.frameRead m (Fin.last n) (hx x)) (hα α αinf) := by
  unfold Z3NetF.hermiteMat
  congr 1
  funext P
  unfold Z3NetF.frameRead
  by_cases h : (P : ℕ) < n
  · rw [dif_pos h, if_neg (fun he => by rw [he] at h; simp at h)]
    simp [hx, h]
  · rw [dif_neg h, if_pos (Fin.ext (by have := P.isLt; simp; omega))]

lemma hα_sum (α : Fin n → ℕ) (αinf : ℕ) : ∑ P, hα α αinf P = ∑ P, α P + αinf := by
  rw [Fin.sum_univ_castSucc]
  simp [hα]

lemma hermite_prod (x : Fin n → R) (α : Fin n → ℕ) (αinf : ℕ) :
    ∏ c : Fin (n + 1), ∏ c' : Fin (n + 1),
        (if c' < c ∧ c ≠ Fin.last n ∧ c' ≠ Fin.last n then
          (hx x c - hx x c') ^ (hα α αinf c' * hα α αinf c) else 1) =
      ∏ Q : Fin n, ∏ P : Fin n, (if P < Q then (x Q - x P) ^ (α P * α Q) else 1) := by
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ c' : Fin (n + 1), (if c' < Fin.last n ∧ Fin.last n ≠ Fin.last n ∧ c' ≠ Fin.last n then
      (hx x (Fin.last n) - hx x c') ^ (hα α αinf c' * hα α αinf (Fin.last n)) else 1) = 1 := by
    apply Finset.prod_eq_one; intro c' _; rw [if_neg]; simp
  rw [hlast, mul_one]
  refine Finset.prod_congr rfl fun Q _ => ?_
  rw [Fin.prod_univ_castSucc]
  have hl2 : (if Fin.last n < Q.castSucc ∧ Q.castSucc ≠ Fin.last n ∧ Fin.last n ≠ Fin.last n then
      (hx x Q.castSucc - hx x (Fin.last n)) ^ (hα α αinf (Fin.last n) * hα α αinf Q.castSucc) else 1) = 1 := by
    rw [if_neg]; simp
  rw [hl2, mul_one]
  refine Finset.prod_congr rfl fun P _ => ?_
  have e1 : hx x Q.castSucc = x Q := by simp [hx]
  have e2 : hx x P.castSucc = x P := by simp [hx]
  have e3 : hα α αinf Q.castSucc = α Q := by simp [hα]
  have e4 : hα α αinf P.castSucc = α P := by simp [hα]
  rw [e1, e2, e3, e4]
  by_cases h : P < Q
  · rw [if_pos ⟨Fin.castSucc_lt_castSucc_iff.mpr h, Fin.castSucc_ne_last Q, Fin.castSucc_ne_last P⟩,
      if_pos h]
  · rw [if_neg (fun h' => h (Fin.castSucc_lt_castSucc_iff.mp h'.1)), if_neg h]

theorem hermite_det_core (x : Fin n → R) (α : Fin n → ℕ) (αinf : ℕ) (hm : ∑ P, α P + αinf = m) :
    (Z3NetF.hermiteMat m x α αinf).det =
        ∏ Q : Fin n, ∏ P : Fin n, (if P < Q then (x Q - x P) ^ (α P * α Q) else 1) ∨
      (Z3NetF.hermiteMat m x α αinf).det =
        -∏ Q : Fin n, ∏ P : Fin n, (if P < Q then (x Q - x P) ^ (α P * α Q) else 1) := by
  rw [hermite_eq_frame, ← hermite_prod x α αinf]
  exact frame_minor_core (Fin.last n) (hx x) (d := hα α αinf) (by rw [hα_sum, hm])

theorem hermite_ne_zero_core {K : Type*} [Field K] (x : Fin n → K) (α : Fin n → ℕ) (αinf : ℕ)
    (hm : ∑ P, α P + αinf = m) (hxd : ∀ P Q, P ≠ Q → 1 ≤ α P → 1 ≤ α Q → x P ≠ x Q) :
    (Z3NetF.hermiteMat m x α αinf).det ≠ 0 := by
  have hne : ∏ Q : Fin n, ∏ P : Fin n, (if P < Q then (x Q - x P) ^ (α P * α Q) else 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro Q _
    rw [Finset.prod_ne_zero_iff]; intro P _
    split_ifs with h
    · by_cases h0 : α P * α Q = 0
      · rw [h0, pow_zero]; exact one_ne_zero
      · apply pow_ne_zero
        rw [sub_ne_zero]
        exact hxd Q P (ne_of_gt h) (by rcases Nat.eq_zero_or_pos (α Q) with h' | h' <;> simp_all <;> omega)
          (by rcases Nat.eq_zero_or_pos (α P) with h' | h' <;> simp_all <;> omega)
    · exact one_ne_zero
  rcases hermite_det_core x α αinf hm with h | h <;> rw [h]
  · exact hne
  · exact neg_ne_zero.mpr hne

theorem hermite_rows_core (x : Fin n → R) (α : Fin n → ℕ) (αinf : ℕ) (hm : ∑ P, α P + αinf = m)
    (P Q : Fin n) (hPQ : P ≠ Q) (hP : 1 ≤ α P) (hQ : 1 ≤ α Q) (hxe : x P = x Q) :
    ∃ r r' : Fin m, r ≠ r' ∧ Z3NetF.hermiteMat m x α αinf r = Z3NetF.hermiteMat m x α αinf r' := by
  have hd : ∑ c, hα α αinf c = m := by rw [hα_sum, hm]
  have hP' : 0 < hα α αinf P.castSucc := by simp [hα]; omega
  have hQ' : 0 < hα α αinf Q.castSucc := by simp [hα]; omega
  refine ⟨⟨pre (hα α αinf) P.castSucc + 0, pre_add_lt _ hd _ 0 hP'⟩,
    ⟨pre (hα α αinf) Q.castSucc + 0, pre_add_lt _ hd _ 0 hQ'⟩, ?_, ?_⟩
  · intro h
    have := pos_inj (hα α αinf) _ _ 0 0 hP' hQ' (congrArg Fin.val h)
    exact hPQ (Fin.castSucc_injective _ this.1)
  · rw [hermite_eq_frame, box_row_pre _ _ hd _ 0 hP', box_row_pre _ _ hd _ 0 hQ']
    simp only [Z3NetF.frameRead, Fin.castSucc_ne_last, if_false]
    simp [hx, hxe]

end hermite

/-! ## The net criterion of `lem:Ts` -/

lemma zmod_isUnit_of_primes (q : ℕ) [NeZero q] (z : ZMod q)
    (h : ∀ p : ℕ, p.Prime → ∀ hpq : p ∣ q, ZMod.castHom hpq (ZMod p) z ≠ 0) : IsUnit z := by
  rw [← ZMod.natCast_zmod_val z, ZMod.isUnit_iff_coprime]
  by_contra hc
  obtain ⟨p, hp, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  apply h p hp h2
  rw [← ZMod.natCast_zmod_val z, map_natCast, (ZMod.natCast_eq_zero_iff _ _).mpr h1]

lemma castHom_ratRed (q p : ℕ) (hp : p.Prime) (hpq : p ∣ q) (a : ℚ) (ha : Nat.Coprime a.den q) :
    ZMod.castHom hpq (ZMod p) (Z3NetF.ratRed q a) = Z3NetF.ratRed p a := by
  haveI := Fact.mk hp
  unfold Z3NetF.ratRed
  rw [map_mul, map_intCast]
  congr 1
  have h1 : ((a.den : ℕ) : ZMod q) * ((a.den : ℕ) : ZMod q)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one _ ha
  have h2 := congrArg (ZMod.castHom hpq (ZMod p)) h1
  rw [map_mul, map_natCast, map_one] at h2
  exact eq_inv_of_mul_eq_one_right h2

theorem frame_net_iff_core {s q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) (inf : Fin s) (a : Fin s → ℚ)
    (hden : ∀ c, c ≠ inf → Nat.Coprime (a c).den q) :
    Z3NetF.IsNet0 s q m (Z3NetF.digPoint q m (Z3NetF.frameRead m inf (fun c => Z3NetF.ratRed q (a c)))) ↔
      ∀ p : ℕ, p.Prime → p ∣ q → ∀ c c', c ≠ inf → c' ≠ inf → c ≠ c' →
        Z3NetF.ratRed p (a c) ≠ Z3NetF.ratRed p (a c') := by
  haveI : NeZero q := ⟨by omega⟩
  rw [nie_zmod]
  set xq : Fin s → ZMod q := fun c => Z3NetF.ratRed q (a c) with hxq
  constructor
  · intro H p hp hpq c c' hc hc' hcc' heq
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    let d : Fin s → ℕ := fun t => if t = c then m - 1 else if t = c' then 1 else 0
    have hd : ∑ t, d t = m := by
      rw [Fintype.sum_eq_add c c' hcc']
      · simp only [d, if_pos rfl, if_neg (Ne.symm hcc'), if_true]; omega
      · intro b hb
        simp [d, hb.1, hb.2]
    have hdc : d c = m - 1 := by simp [d]
    have hdc' : d c' = 1 := by simp [d, Ne.symm hcc']
    have hu := H d hd
    set f := ZMod.castHom hpq (ZMod p)
    have hfu : IsUnit (f (Z3NetF.boxMatrix (Z3NetF.frameRead m inf xq) d).det) := hu.map f
    have himg : ∀ t, t ≠ inf → f (xq t) = Z3NetF.ratRed p (a t) := fun t ht =>
      castHom_ratRed q p hp hpq (a t) (hden t ht)
    -- the image of the product vanishes
    have hz : f (∏ t : Fin s, ∏ t' : Fin s,
        (if t' < t ∧ t ≠ inf ∧ t' ≠ inf then (xq t - xq t') ^ (d t' * d t) else 1)) = 0 := by
      rw [map_prod]
      rcases lt_or_gt_of_ne hcc' with hlt | hgt
      · apply Finset.prod_eq_zero (mem_univ c')
        rw [map_prod]
        apply Finset.prod_eq_zero (mem_univ c)
        rw [if_pos ⟨hlt, hc', hc⟩, map_pow, map_sub, himg c' hc', himg c hc, heq, sub_self]
        apply zero_pow
        rw [hdc, hdc']; omega
      · apply Finset.prod_eq_zero (mem_univ c)
        rw [map_prod]
        apply Finset.prod_eq_zero (mem_univ c')
        rw [if_pos ⟨hgt, hc, hc'⟩, map_pow, map_sub, himg c' hc', himg c hc, heq, sub_self]
        apply zero_pow
        rw [hdc, hdc']; omega
    rcases frame_minor_core inf xq (d := d) hd with h | h <;> rw [h] at hfu
    · rw [hz] at hfu; exact not_isUnit_zero hfu
    · rw [map_neg, hz, neg_zero] at hfu; exact not_isUnit_zero hfu
  · intro H d hd
    have hfac : ∀ t t', t ≠ inf → t' ≠ inf → t ≠ t' → IsUnit (xq t - xq t') := by
      intro t t' ht ht' htt'
      apply zmod_isUnit_of_primes
      intro p hp hpq
      rw [map_sub, castHom_ratRed q p hp hpq _ (hden t ht), castHom_ratRed q p hp hpq _ (hden t' ht'),
        sub_ne_zero]
      exact H p hp hpq t t' ht ht' htt'
    have hprod : IsUnit (∏ t : Fin s, ∏ t' : Fin s,
        (if t' < t ∧ t ≠ inf ∧ t' ≠ inf then (xq t - xq t') ^ (d t' * d t) else 1)) := by
      rw [IsUnit.prod_univ_iff]; intro t
      rw [IsUnit.prod_univ_iff]; intro t'
      split_ifs with h
      · exact (hfac t t' h.2.1 h.2.2 (ne_of_gt h.1)).pow _
      · exact isUnit_one
    rcases frame_minor_core inf xq (d := d) hd with h | h <;> rw [h]
    · exact hprod
    · exact hprod.neg

end

end Z3NetF.Proofs

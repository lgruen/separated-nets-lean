module
public import Mathlib
public import Z3Net.SUDefs

@[expose] public section

/-!
# Entry U, part 1: the frame as polynomial readings, the basis `E_{d,j}`, Lemma T_s

* Coefficient lists: `linPowL`, `pmul`, `Ecoef` compute the coefficients of
  `EPoly R k d j = ∏_b (X - Eroot b)^(Eexp k d b j)` (`Evec_coeff`, `pv_EvecR`).
* Readings: reading `c ≥ 1` is the Taylor expansion at `a_c` (`frame_fin`), reading `0` is the
  reversed coefficient list (`frame_inf`).
* Factorisation of `E_{d,j}` at a finite place, exponent sums, monicity.
* **Lemma T_s** (`lemmaT`): over a commutative ring in which the differences of the finite places
  are units, a polynomial of degree `< m` whose first `d_c` digits vanish in every reading
  (`∑ d_c = m`) is zero.
-/

namespace Z3NetU.Proofs

open Polynomial Finset Matrix Z3NetU

noncomputable section

/-! ## Polynomials from coefficient vectors (copied from the 4D entry) -/

section generic

variable {R : Type*} [CommRing R]

/-- The polynomial `∑_i v_i t^i` with coefficient vector `v`. -/
def pv {m : ℕ} (v : Fin m → R) : R[X] := ∑ i : Fin m, monomial (i : ℕ) (v i)

lemma coeff_pv {m : ℕ} (v : Fin m → R) (n : ℕ) :
    (pv v).coeff n = if h : n < m then v ⟨n, h⟩ else 0 := by
  simp only [pv, finset_sum_coeff, coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h'; apply hb; ext; exact h'
    · simp
  · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; intro h'; apply h; rw [← h']; exact b.isLt

lemma coeff_pv_fin {m : ℕ} (v : Fin m → R) (i : Fin m) : (pv v).coeff i = v i := by
  rw [coeff_pv, dif_pos i.isLt]

lemma degree_pv_lt {m : ℕ} (v : Fin m → R) : (pv v).degree < m := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_pv, dif_neg (by omega)]

lemma pv_eq_zero {m : ℕ} {v : Fin m → R} (h : pv v = 0) : v = 0 := by
  funext i
  rw [← coeff_pv_fin v i, h, coeff_zero]; rfl

lemma taylor_X_sub_C_pow_mul (r : R) (e : ℕ) (G : R[X]) :
    taylor r ((X - C r) ^ e * G) = X ^ e * taylor r G := by
  rw [taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]

lemma coeff_taylor_X_sub_C_pow_mul (r : R) (e : ℕ) (G : R[X]) (i : ℕ) :
    (taylor r ((X - C r) ^ e * G)).coeff i = if e ≤ i then (taylor r G).coeff (i - e) else 0 := by
  rw [taylor_X_sub_C_pow_mul, coeff_X_pow_mul']

lemma dvd_of_taylor (r : R) (e : ℕ) (V : R[X]) (h : ∀ i < e, (taylor r V).coeff i = 0) :
    (X - C r) ^ e ∣ V := by
  obtain ⟨G, hG⟩ := X_pow_dvd_iff.mpr h
  refine ⟨taylor (-r) G, ?_⟩
  have h1 : V = taylor (-r) (taylor r V) := by rw [taylor_taylor, neg_add_cancel, taylor_zero]
  rw [h1, hG, taylor_mul, taylor_pow, taylor_X, C_neg, ← sub_eq_add_neg]

end generic

/-! ## Coefficient lists -/

/-- `f` is a coefficient list of `P`. -/
def Rep (f : List ℤ) (P : ℤ[X]) : Prop := f ≠ [] ∧ ∀ i, f.getD i 0 = P.coeff i

lemma getD_range_map (n : ℕ) (f : ℕ → ℤ) (i : ℕ) :
    ((List.range n).map f).getD i 0 = if i < n then f i else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

lemma rep_linPowL (a : ℤ) (e : ℕ) : Rep (linPowL a e) ((X - C a) ^ e) := by
  refine ⟨by simp [linPowL], fun i => ?_⟩
  rw [linPowL, getD_range_map, sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
  split_ifs with h
  · ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma pmul_getD (f g : List ℤ) (hf : f ≠ []) (hg : g ≠ []) (n : ℕ) :
    (pmul f g).getD n 0 = ∑ i ∈ range (n + 1), f.getD i 0 * g.getD (n - i) 0 := by
  rw [pmul, getD_range_map]
  split_ifs with h
  · rfl
  · symm
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hi' : i < f.length
    · have : g.length ≤ n - i := by omega
      rw [List.getD_eq_getElem?_getD (l := g), List.getElem?_eq_none this]; simp
    · rw [List.getD_eq_getElem?_getD (l := f), List.getElem?_eq_none (by omega)]; simp

lemma pmul_ne_nil (f g : List ℤ) (hf : f ≠ []) (hg : g ≠ []) : pmul f g ≠ [] := by
  have h1 : 0 < f.length := List.length_pos_iff.mpr hf
  have h2 : 0 < g.length := List.length_pos_iff.mpr hg
  simp [pmul]; omega

lemma rep_pmul {f g : List ℤ} {P Q : ℤ[X]} (hf : Rep f P) (hg : Rep g Q) : Rep (pmul f g) (P * Q) := by
  refine ⟨pmul_ne_nil f g hf.1 hg.1, fun n => ?_⟩
  rw [pmul_getD f g hf.1 hg.1, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun i _ => ?_
  rw [hf.2, hg.2]

lemma rep_foldr {s : ℕ} (F : Fin s → List ℤ) (G : Fin s → ℤ[X]) (hFG : ∀ b, Rep (F b) (G b)) :
    ∀ l : List (Fin s), Rep (l.foldr (fun b acc => pmul (F b) acc) [1]) (l.map G).prod
  | [] => ⟨by simp, fun i => by rcases i with _ | i <;> simp [coeff_one]⟩
  | b :: l => by
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    exact rep_pmul (hFG b) (rep_foldr F G hFG l)

/-! ## The basis polynomials -/

/-- `E_{d,j} = ∏_b (t - Eroot b)^(Eexp k d b j)` over `R`. -/
def EPoly (R : Type*) [CommRing R] {s : ℕ} (k : ℕ) (d : Fin s) (j : ℕ) : R[X] :=
  ∏ b : Fin s, (X - C ((Eroot b : ℤ) : R)) ^ Eexp k d b j

lemma rep_Ecoef {s : ℕ} (k : ℕ) (d : Fin s) (j : ℕ) : Rep (Ecoef k d j) (EPoly ℤ k d j) := by
  have := rep_foldr (fun b => linPowL (Eroot b) (Eexp k d b j))
    (fun b => (X - C (Eroot b)) ^ Eexp k d b j) (fun b => rep_linPowL _ _) (List.finRange s)
  simpa [EPoly, Fin.prod_univ_def, Ecoef] using this

variable {R : Type*} [CommRing R]

lemma EPoly_map {s : ℕ} (k : ℕ) (d : Fin s) (j : ℕ) :
    (EPoly ℤ k d j).map (Int.castRingHom R) = EPoly R k d j := by
  simp [EPoly, Polynomial.map_prod, Polynomial.map_pow]

lemma EPoly_monic {s : ℕ} (k : ℕ) (d : Fin s) (j : ℕ) : (EPoly R k d j).Monic :=
  monic_prod_of_monic _ _ fun b _ => (monic_X_sub_C _).pow _

lemma natDegree_EPoly [Nontrivial R] {s : ℕ} (k : ℕ) (d : Fin s) (j : ℕ) :
    (EPoly R k d j).natDegree = ∑ b, Eexp k d b j := by
  rw [EPoly, natDegree_prod_of_monic _ _ (fun b _ => (monic_X_sub_C _).pow _)]
  refine sum_congr rfl fun b _ => ?_
  rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]

lemma natDegree_EPoly_le {s : ℕ} (k : ℕ) (d : Fin s) (j : ℕ) :
    (EPoly R k d j).natDegree ≤ ∑ b, Eexp k d b j := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (EPoly R k d j) 0]; simp
  · exact (natDegree_EPoly k d j).le

/-- The coordinate `0` (the place `∞`). -/
def c0 {s : ℕ} (hs : 0 < s) : Fin s := ⟨0, hs⟩

lemma val_eq_zero_iff {s : ℕ} (hs : 0 < s) (c : Fin s) : (c : ℕ) = 0 ↔ c = c0 hs := by
  rw [Fin.ext_iff]; rfl

lemma Eexp_c0 {s : ℕ} (hs : 0 < s) (k : ℕ) (d : Fin s) (j : ℕ) :
    Eexp k d (c0 hs) j = if (d : ℕ) = 0 then k - 1 - j else 0 := by
  simp [Eexp, c0]

lemma Eexp_fin {s : ℕ} (k : ℕ) (d b : Fin s) (j : ℕ) (hb : (b : ℕ) ≠ 0) :
    Eexp k d b j = if b = d then j else k := by
  simp [Eexp, hb]

lemma sum_erase_c0 {M : Type*} [AddCommMonoid M] {s : ℕ} (hs : 0 < s) (f : Fin s → M) :
    ∑ b, f b = f (c0 hs) + ∑ b ∈ univ.erase (c0 hs), f b :=
  (Finset.add_sum_erase _ _ (mem_univ _)).symm

lemma card_erase_c0 {s : ℕ} (hs : 0 < s) : (univ.erase (c0 hs)).card = s - 1 := by
  rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

/-- Exponent sum of `E_{d,j}` for finite `d`: `(s-2)k + j`. -/
lemma Esum_fin {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (d : Fin s) (hd : (d : ℕ) ≠ 0) (j : ℕ) :
    ∑ b, Eexp k d b j = (s - 2) * k + j := by
  have hs0 : 0 < s := by omega
  rw [sum_erase_c0 hs0, Eexp_c0, if_neg hd, zero_add]
  have hdm : d ∈ univ.erase (c0 hs0) := by
    rw [mem_erase]; exact ⟨fun h => hd (by rw [h]; rfl), mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hdm]
  have e1 : Eexp k d d j = j := by simp [Eexp, hd]
  have e2 : ∀ b ∈ (univ.erase (c0 hs0)).erase d, Eexp k d b j = k := by
    intro b hb
    rw [mem_erase, mem_erase] at hb
    have hb0 : (b : ℕ) ≠ 0 := fun h => hb.2.1 (by rw [Fin.ext_iff]; exact h)
    simp [Eexp, hb0, hb.1]
  rw [e1, sum_congr rfl e2, sum_const, card_erase_of_mem hdm, card_erase_c0, smul_eq_mul]
  rw [show s - 1 - 1 = s - 2 by omega]; ring

/-- Exponent sum of `E_{∞,j}`: `(s-1)k + (k-1-j)`. -/
lemma Esum_inf {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (d : Fin s) (hd : (d : ℕ) = 0) (j : ℕ) :
    ∑ b, Eexp k d b j = (s - 1) * k + (k - 1 - j) := by
  have hs0 : 0 < s := by omega
  rw [sum_erase_c0 hs0, Eexp_c0, if_pos hd]
  have e2 : ∀ b ∈ univ.erase (c0 hs0), Eexp k d b j = k := by
    intro b hb
    rw [mem_erase] at hb
    have hb0 : (b : ℕ) ≠ 0 := fun h => hb.1 (by rw [Fin.ext_iff]; exact h)
    have hbd : b ≠ d := fun h => hb0 (by rw [h]; exact hd)
    simp [Eexp, hb0, hbd]
  rw [sum_congr rfl e2, sum_const, card_erase_c0, smul_eq_mul]; ring

lemma Esum_lt {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (d : Fin s) (j : ℕ) (hj : j < k) :
    ∑ b, Eexp k d b j < s * k := by
  by_cases hd : (d : ℕ) = 0
  · rw [Esum_inf hs k d hd j]
    have : (s - 1) * k + k = s * k := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    omega
  · rw [Esum_fin hs k d hd j]
    have : (s - 2) * k + k + k = s * k := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    omega

lemma Evec_coeff {s : ℕ} (k : ℕ) (d : Fin s) (j : ℕ) (i : Fin (s * k)) :
    Evec k d j i = (EPoly ℤ k d j).coeff i := (rep_Ecoef k d j).2 i

/-- The coefficient vector of `E_{d,j}` (cast to `R`). -/
def EvecR {s : ℕ} (k : ℕ) (d : Fin s) (j : ℕ) : Fin (s * k) → R := fun i => ((Evec k d j i : ℤ) : R)

lemma pv_EvecR {s : ℕ} (hs : 2 ≤ s) (k : ℕ) (d : Fin s) (j : ℕ) (hj : j < k) :
    pv (EvecR (R := R) k d j) = EPoly R k d j := by
  ext n
  rw [coeff_pv]
  split_ifs with hn
  · simp only [EvecR, Evec_coeff, ← EPoly_map (R := R), coeff_map, eq_intCast]
  · symm
    apply coeff_eq_zero_of_natDegree_lt
    have := natDegree_EPoly_le (R := R) k d j
    have := Esum_lt hs k d j hj
    omega

/-! ## Readings of the frame -/

lemma frame_fin {s : ℕ} (m : ℕ) (c : Fin s) (hc : (c : ℕ) ≠ 0) (v : Fin m → R) (i : Fin m) :
    ((frameGen m c).map (Int.cast : ℤ → R) *ᵥ v) i = (taylor ((place c : ℤ) : R) (pv v)).coeff i := by
  simp only [mulVec, dotProduct, map_apply, frameGen, if_neg hc]
  rw [pv, map_sum, finset_sum_coeff]
  refine sum_congr rfl fun l _ => ?_
  rw [taylor_monomial, coeff_C_mul, coeff_X_add_C_pow]
  push_cast
  ring

lemma frame_inf {s : ℕ} (m : ℕ) (c : Fin s) (hc : (c : ℕ) = 0) (v : Fin m → R) (i : Fin m) :
    ((frameGen m c).map (Int.cast : ℤ → R) *ᵥ v) i = (pv v).coeff (m - 1 - i) := by
  have hi := i.isLt
  simp only [mulVec, dotProduct, map_apply, frameGen, if_pos hc]
  rw [coeff_pv, dif_pos (by omega)]
  rw [Finset.sum_eq_single ⟨m - 1 - i, by omega⟩]
  · simp [show m - 1 - (i : ℕ) + i + 1 = m by omega]
  · intro b _ hb
    rw [if_neg]
    · simp
    · intro h; apply hb; ext; simp; omega
  · simp

/-! ## Factorisation at a finite place -/

/-- The cofactor of `(t - a_c)^(Eexp c)` in `E_{d,j}`. -/
def Rest (R : Type*) [CommRing R] {s : ℕ} (k : ℕ) (c d : Fin s) (j : ℕ) : R[X] :=
  ∏ b ∈ univ.erase c, (X - C ((Eroot b : ℤ) : R)) ^ Eexp k d b j

lemma Eroot_fin {s : ℕ} (c : Fin s) (hc : (c : ℕ) ≠ 0) : Eroot c = place c := by
  simp [Eroot, hc]

lemma EPoly_fac {s : ℕ} (k : ℕ) (c d : Fin s) (j : ℕ) (hc : (c : ℕ) ≠ 0) :
    EPoly R k d j = (X - C ((place c : ℤ) : R)) ^ Eexp k d c j * Rest R k c d j := by
  rw [EPoly, Rest, ← Eroot_fin c hc, Finset.mul_prod_erase _ (fun b => (X - C ((Eroot b : ℤ) : R)) ^ Eexp k d b j) (mem_univ c)]

lemma taylor_EPoly_fin {s : ℕ} (k : ℕ) (c d : Fin s) (j : ℕ) (hc : (c : ℕ) ≠ 0) (i : ℕ) :
    (taylor ((place c : ℤ) : R) (EPoly R k d j)).coeff i =
      if Eexp k d c j ≤ i then (taylor ((place c : ℤ) : R) (Rest R k c d j)).coeff (i - Eexp k d c j)
      else 0 := by
  rw [EPoly_fac k c d j hc, coeff_taylor_X_sub_C_pow_mul]

lemma Rest_eval {s : ℕ} (k : ℕ) (c d : Fin s) (j : ℕ) :
    (Rest R k c d j).eval ((place c : ℤ) : R) =
      ∏ b ∈ univ.erase c, (((place c : ℤ) : R) - ((Eroot b : ℤ) : R)) ^ Eexp k d b j := by
  simp [Rest, eval_prod]

/-! ## Lemma T_s -/

/-- **Lemma T_s** (frame `t = 0`): over a commutative ring in which the differences of the finite
places are units, a polynomial of degree `< m` whose first `d c` Taylor coefficients at `a_c`
(`c ≥ 1`) and whose top `d 0` coefficients vanish, with `∑ d = m`, is zero. -/
theorem lemmaT {s : ℕ} (hs : 0 < s) (a : Fin s → R)
    (hunit : ∀ c c' : Fin s, (c : ℕ) ≠ 0 → (c' : ℕ) ≠ 0 → c ≠ c' → IsUnit (a c - a c'))
    (m : ℕ) (V : R[X]) (hV : V.degree < m) (d : Fin s → ℕ) (hd : ∑ c, d c = m)
    (hfin : ∀ c : Fin s, (c : ℕ) ≠ 0 → ∀ i < d c, (taylor (a c) V).coeff i = 0)
    (hinf : ∀ i < d (c0 hs), V.coeff (m - 1 - i) = 0) : V = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  set T := univ.erase (c0 hs) with hT
  have hTm : ∀ c ∈ T, (c : ℕ) ≠ 0 := by
    intro c hc h; rw [hT, mem_erase] at hc; exact hc.1 (by rw [Fin.ext_iff]; exact h)
  have hdvd : ∏ c ∈ T, (X - C (a c)) ^ d c ∣ V := by
    apply Finset.prod_dvd_of_coprime
    · intro c hc c' hc' hne
      exact IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub (hunit c c' (hTm c hc) (hTm c' hc') hne))
    · intro c hc
      exact dvd_of_taylor _ _ V (hfin c (hTm c hc))
  have hmon : (∏ c ∈ T, (X - C (a c)) ^ d c).Monic :=
    monic_prod_of_monic _ _ fun c _ => (monic_X_sub_C _).pow _
  have hdeg : (∏ c ∈ T, (X - C (a c)) ^ d c).natDegree = ∑ c ∈ T, d c := by
    rw [natDegree_prod_of_monic _ _ (fun c _ => (monic_X_sub_C _).pow _)]
    refine sum_congr rfl fun c _ => ?_
    rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hsum : d (c0 hs) + ∑ c ∈ T, d c = m := by rw [hT, Finset.add_sum_erase _ _ (mem_univ _), hd]
  by_contra hne
  apply hmon.not_dvd_of_degree_lt hne _ hdvd
  rw [degree_eq_natDegree hmon.ne_zero, hdeg]
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  have hn' : ∑ c ∈ T, d c ≤ n := by exact_mod_cast hn
  by_cases hnm : m ≤ n
  · exact (degree_lt_iff_coeff_zero V m).mp hV n (by exact_mod_cast hnm)
  · have := hinf (m - 1 - n) (by omega)
    rwa [show m - 1 - (m - 1 - n) = n by omega] at this

end

end Z3NetU.Proofs

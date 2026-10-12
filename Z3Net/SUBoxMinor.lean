module
public import Mathlib
public import Z3Net.SUThm1

@[expose] public section

/-!
# Entry U, part 9: box minors over `ℚ` are units of `ℤ[1/(s-2)!]`

All definitions are polynomial in the inverses `iv i` (`1 ≤ i ≤ n := s - 2`), and only these
values are used (`map_UPhi`). Over `ℤ[X]` with `iv i = (n!/i) X` a box minor is a polynomial
`Δ ∈ ℤ[X]`; evaluating at `1/n! ∈ ℚ` gives the box minor over `ℚ`, evaluating at `(n!)⁻¹ ∈ 𝔽_p`
the box minor over `𝔽_p`, which is nonzero for every prime `p ≥ s - 1` (kernel argument of
`U_net`). Hence the integer `z = (n!)^(deg Δ) Δ(1/n!)` is prime to every `p ≥ s - 1`, and the minor
over `ℚ` is `z / (n!)^(deg Δ)`, of `p`-adic valuation `0`.
-/

namespace Z3NetU.Proofs

open Polynomial Finset Matrix Z3NetU

noncomputable section

section map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {s : ℕ} (iv : ℕ → R) (iv' : ℕ → S)
  (hf : ∀ i, 1 ≤ i → i ≤ s - 2 → f (iv i) = iv' i)

include hf

lemma map_ivz (z : ℤ) (hz : z ≠ 0) (hzn : |z| ≤ (s - 2 : ℕ)) : f (ivz iv z) = ivz iv' z := by
  unfold ivz
  split_ifs with h0
  · exact hf _ (by omega) (by rw [abs_of_nonneg h0] at hzn; omega)
  · rw [map_neg, hf _ (by omega) (by rw [abs_of_neg (by omega)] at hzn; omega)]

lemma map_Qinv (k : ℕ) (c : Fin s) : f (Qinv iv k c) = Qinv iv' k c := by
  unfold Qinv
  split_ifs with hc
  · simp
  · rw [map_pow, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [mem_filter] at hb
    obtain ⟨h1, h2⟩ := diff_small c b hc hb.2.1 (Ne.symm hb.2.2)
    exact map_ivz f iv iv' hf _ h1 h2

lemma map_invFact (n : ℕ) (hn : n ≤ s - 2) : f (invFact iv n) = invFact iv' n := by
  unfold invFact
  rw [map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  exact hf _ (by omega) (by omega)

lemma map_yN (c d : Fin s) (hcd : c ≠ d) : f (yN iv c d) = yN iv' c d := by
  unfold yN
  split_ifs with h1 h2
  · simp
  · simp
  · obtain ⟨a, b⟩ := diff_small c d h1 h2 hcd
    exact map_ivz f iv iv' hf _ a b

lemma map_wN (c d : Fin s) (hcd : c ≠ d) : f (wN iv c d) = wN iv' c d := by
  unfold wN
  split_ifs with h1
  · simp
  · push_neg at h1
    obtain ⟨a, b⟩ := diff_small c d h1.1 h1.2 hcd
    exact map_ivz f iv iv' hf _ a b

omit hf in
lemma map_rootsPoly : ∀ (ys : List R) (i : ℕ), f (rootsPoly ys i) = rootsPoly (ys.map f) i
  | [], i => by simp only [rootsPoly, List.map_nil]; split_ifs <;> simp
  | y :: ys, i => by
    simp only [rootsPoly, List.map_cons]
    rw [map_sub, map_mul, map_rootsPoly ys i]
    split_ifs
    · simp
    · rw [map_rootsPoly ys (i - 1)]

omit hf in
lemma map_xpowRem (p : ℕ → R) (r : ℕ) : ∀ (n i : ℕ), f (xpowRem p r n i) = xpowRem (fun j => f (p j)) r n i
  | 0, i => by simp only [xpowRem]; split_ifs <;> simp
  | n + 1, i => by
    simp only [xpowRem]
    rw [map_sub, map_mul, map_xpowRem p r n (r - 1)]
    split_ifs
    · simp
    · rw [map_xpowRem p r n (i - 1)]

lemma map_nodes (d : Fin s) : (nodes iv d).map f = nodes iv' d := by
  unfold nodes
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  rw [List.mem_filter] at hc
  exact map_yN f iv iv' hf c d (by simpa using hc.2)

lemma map_gam (d : Fin s) (n i : ℕ) : f (gam iv d n i) = gam iv' d n i := by
  unfold gam
  rw [map_xpowRem]
  congr 1
  funext j
  rw [map_rootsPoly, map_nodes f iv iv' hf]

lemma map_Ux (d : Fin s) (n' n : ℕ) : f (Ux iv d n' n) = Ux iv' d n' n := by
  unfold Ux
  by_cases h1 : n < s - 1
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : n' < s - 1
    · rw [if_pos h2, if_pos h2]; unfold Ures
      by_cases hd : (d : ℕ) = 0
      · rw [if_pos hd, if_pos hd, map_mul, map_intCast, map_invFact f iv iv' hf n (by omega)]
      · rw [if_neg hd, if_neg hd]; split_ifs <;> simp
    · rw [if_neg h2, if_neg h2, map_zero]
  · rw [if_neg h1, if_neg h1]
    split_ifs <;> simp [map_gam f iv iv' hf]

lemma map_UPhi (k : ℕ) (c d : Fin s) : (UPhi R iv k c d).map f = UPhi S iv' k c d := by
  ext r j
  simp only [map_apply, UPhi]
  split_ifs <;> simp [map_sum, map_Qinv f iv iv' hf, Uk, map_Ux f iv iv' hf]

omit hf in
lemma map_graphGen (k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) R) (c : Fin s) :
    (graphGen s k Φ c).map f = graphGen s k (fun c d => (Φ c d).map f) c := by
  ext i j
  simp only [map_apply, graphGen]
  split_ifs <;> simp

omit hf in
lemma map_boxMatrix {m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R) (d : Fin s → ℕ) :
    (boxMatrix C d).map f = boxMatrix (fun c => (C c).map f) d := by
  ext r j
  simp only [map_apply, boxMatrix]
  split_ifs <;> simp

lemma box_map (k : ℕ) (d : Fin s → ℕ) :
    (boxMatrix (graphGen s k (UPhi R iv k)) d).map f = boxMatrix (graphGen s k (UPhi S iv' k)) d := by
  rw [map_boxMatrix]
  congr 1
  funext c
  rw [map_graphGen]
  congr 1
  funext c' d'
  exact map_UPhi f iv iv' hf k c' d'

end map

/-! ## Rows of the box matrix -/

lemma boxLoc_spec : ∀ (ds : List ℕ) (c0 j i : ℕ) (hj : j < ds.length), i < ds[j] →
    boxLoc ds c0 ((ds.take j).sum + i) = (c0 + j, i)
  | [], _, _, _, hj, _ => absurd hj (by simp)
  | x :: xs, c0, 0, i, _, hi => by simp at hi; simp [boxLoc, hi]
  | x :: xs, c0, j + 1, i, hj, hi => by
    have e : (List.take (j + 1) (x :: xs)).sum + i = x + ((xs.take j).sum + i) := by
      simp [List.take_succ_cons]; ring
    rw [e]
    simp only [boxLoc]
    rw [if_neg (by omega), Nat.add_sub_cancel_left,
      boxLoc_spec xs (c0 + 1) j i (by simpa using hj) (by simpa using hi)]
    simp only [Prod.mk.injEq, and_true]; omega

lemma box_row {R : Type*} [CommRing R] {s m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) R)
    (d : Fin s → ℕ) (hd : ∑ c, d c = m) (v : Fin m → R) (c : Fin s) (i : Fin m)
    (hi : (i : ℕ) < d c) : ∃ r : Fin m, (boxMatrix C d *ᵥ v) r = (C c *ᵥ v) i := by
  have hlen : (c : ℕ) < (List.ofFn d).length := by simp
  have hget : (List.ofFn d)[(c : ℕ)] = d c := by simp
  have hsum : (List.ofFn d).sum = m := by rw [List.sum_ofFn, hd]
  have hdrop : (List.ofFn d)[(c : ℕ)] ≤ ((List.ofFn d).drop c).sum := by
    rw [List.drop_eq_getElem_cons hlen, List.sum_cons]; omega
  have htd := List.sum_take_add_sum_drop (List.ofFn d) c
  have hr : ((List.ofFn d).take c).sum + (i : ℕ) < m := by rw [hget] at hdrop; omega
  refine ⟨⟨((List.ofFn d).take c).sum + i, hr⟩, ?_⟩
  have hloc := boxLoc_spec (List.ofFn d) 0 c i hlen (by rw [hget]; exact hi)
  have hrow : boxMatrix C d ⟨((List.ofFn d).take c).sum + i, hr⟩ = C c i := by
    funext l
    simp [boxMatrix, hloc]
  show ∑ l, boxMatrix C d ⟨((List.ofFn d).take c).sum + i, hr⟩ l * v l = ∑ l, C c i l * v l
  rw [hrow]

/-! ## The universal minor -/

/-- `F = (s-2)!`. -/
def Ffac (s : ℕ) : ℕ := (s - 2).factorial

lemma Ffac_div_mul (s i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ s - 2) : (Ffac s / i) * i = Ffac s :=
  Nat.div_mul_cancel (Nat.dvd_factorial (by omega) h2)

/-- `F^D · Δ(u) = ∑_{i ≤ D} Δ_i F^(D-i)` whenever `F u = 1`. -/
lemma scaled_eval {S : Type*} [CommRing S] (F : ℕ) (u : S) (hu : (F : S) * u = 1) (Δ : ℤ[X]) :
    (((∑ i ∈ range (Δ.natDegree + 1), Δ.coeff i * (F : ℤ) ^ (Δ.natDegree - i) : ℤ)) : S) =
      (F : S) ^ Δ.natDegree * Δ.eval₂ (Int.castRingHom S) u := by
  rw [eval₂_eq_sum_range, Finset.mul_sum]
  push_cast
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  have : (F : S) ^ Δ.natDegree * u ^ i = (F : S) ^ (Δ.natDegree - i) := by
    rw [show Δ.natDegree = (Δ.natDegree - i) + i by omega, pow_add, mul_assoc, ← mul_pow, hu,
      one_pow, mul_one, Nat.add_sub_cancel]
  rw [eq_intCast, ← this]; ring

/-- The universal inverses over `ℤ[X]`: `iv i = (F/i) X`. -/
def ivX (s : ℕ) : ℕ → ℤ[X] := fun i => C ((Ffac s / i : ℕ) : ℤ) * X

lemma eval_ivX {S : Type*} [CommRing S] (s : ℕ) (u : S) (hu : (Ffac s : S) * u = 1)
    (iv' : ℕ → S) (hiv' : ∀ i, 1 ≤ i → i ≤ s - 2 → (i : S) * iv' i = 1) (i : ℕ) (h1 : 1 ≤ i)
    (h2 : i ≤ s - 2) : (eval₂RingHom (Int.castRingHom S) u) (ivX s i) = iv' i := by
  have e : (eval₂RingHom (Int.castRingHom S) u) (ivX s i) = ((Ffac s / i : ℕ) : S) * u := by
    rw [ivX, map_mul, coe_eval₂RingHom, eval₂_C, eval₂_X]
    simp only [eq_intCast, Int.cast_natCast]
  rw [e]
  have hi : (i : S) * (((Ffac s / i : ℕ) : S) * u) = 1 := by
    rw [← mul_assoc, ← Nat.cast_mul, mul_comm i, Ffac_div_mul s i h1 h2, hu]
  calc ((Ffac s / i : ℕ) : S) * u = (iv' i * (i : S)) * (((Ffac s / i : ℕ) : S) * u) := by
        rw [mul_comm (iv' i), hiv' i h1 h2, one_mul]
    _ = iv' i := by rw [mul_assoc, hi, mul_one]

/-- **Box minors.** -/
theorem U_boxMinor (s k : ℕ) (hs : 3 ≤ s) (hk : 1 ≤ k) (d : Fin s → ℕ) (hd : ∑ c, d c = s * k) :
    (boxMatrix (graphGen s k (UPhi ℚ (fun i => ((i : ℕ) : ℚ)⁻¹) k)) d).det ≠ 0 ∧
      ∀ p : ℕ, p.Prime → s - 1 ≤ p →
        padicValRat p (boxMatrix (graphGen s k (UPhi ℚ (fun i => ((i : ℕ) : ℚ)⁻¹) k)) d).det = 0 := by
  set F := Ffac s with hF
  have hF0 : 0 < F := Nat.factorial_pos _
  set Δ : ℤ[X] := (boxMatrix (graphGen s k (UPhi ℤ[X] (ivX s) k)) d).det with hΔ
  set D := Δ.natDegree
  set z : ℤ := ∑ i ∈ range (D + 1), Δ.coeff i * (F : ℤ) ^ (D - i) with hz
  -- the minor over a ring `S` with `F u = 1` is `Δ(u)`
  have hdet : ∀ (S : Type) [CommRing S] (u : S) (hu : (F : S) * u = 1) (iv' : ℕ → S)
      (hiv' : ∀ i, 1 ≤ i → i ≤ s - 2 → (i : S) * iv' i = 1),
      (boxMatrix (graphGen s k (UPhi S iv' k)) d).det = Δ.eval₂ (Int.castRingHom S) u := by
    intro S _ u hu iv' hiv'
    have := box_map (eval₂RingHom (Int.castRingHom S) u) (ivX s) iv'
      (fun i h1 h2 => eval_ivX s u hu iv' hiv' i h1 h2) k d
    rw [← this]
    exact (RingHom.map_det (eval₂RingHom (Int.castRingHom S) u) _).symm
  -- nonzero modulo every prime `p ≥ s - 1`
  have hpz : ∀ p : ℕ, p.Prime → s - 1 ≤ p → (z : ZMod p) ≠ 0 := by
    intro p hp hps
    haveI := Fact.mk hp
    have hadm : Admissible s p := ⟨hp.two_le, fun p' hp' hdvd => by
      rw [(Nat.prime_dvd_prime_iff_eq hp' hp).mp hdvd]; exact hps⟩
    have hFu : IsUnit ((F : ℕ) : ZMod p) := by
      rw [ZMod.isUnit_iff_coprime]
      apply Nat.Coprime.symm
      rw [hF, Ffac, Nat.Prime.coprime_iff_not_dvd hp, hp.dvd_factorial]
      omega
    have hu : ((F : ℕ) : ZMod p) * ((F : ℕ) : ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hFu
    rw [hz, scaled_eval F _ hu Δ, ← hdet (ZMod p) _ hu _ (ivOK_zmod s p hadm)]
    refine mul_ne_zero (pow_ne_zero _ hFu.ne_zero) ?_
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv0
    refine box_kernel _ hs (ivOK_zmod s p hadm) k d hd v ?_
    intro c i hi
    obtain ⟨r, hr⟩ := box_row _ d hd v c i hi
    rw [← hr, hv]; rfl
  have hz0 : z ≠ 0 := by
    intro h0
    obtain ⟨p0, hp0, hp0p⟩ := Nat.exists_infinite_primes (s - 1)
    have := hpz p0 hp0p hp0
    rw [h0, Int.cast_zero] at this
    exact this rfl
  have hq := scaled_eval (S := ℚ) F (1 / (F : ℚ)) (by field_simp) Δ
  rw [← hz, ← hdet ℚ (1 / (F : ℚ)) (by field_simp) (fun i => ((i : ℕ) : ℚ)⁻¹) (fun i h1 _ => by
    have : (i : ℚ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
    exact mul_inv_cancel₀ this)] at hq
  have hFD : (F : ℚ) ^ D ≠ 0 := by positivity
  have key : (boxMatrix (graphGen s k (UPhi ℚ (fun i => ((i : ℕ) : ℚ)⁻¹) k)) d).det = (z : ℚ) / (F : ℚ) ^ D := by
    rw [hq]; field_simp; rfl
  rw [key]
  refine ⟨div_ne_zero (by exact_mod_cast hz0) hFD, fun p hp hps => ?_⟩
  haveI := Fact.mk hp
  rw [padicValRat.div (by exact_mod_cast hz0) hFD, padicValRat.pow,
    padicValRat.of_int, padicValRat.of_nat]
  have h1 : padicValInt p z = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hdvd
    exact hpz p hp hps ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mpr hdvd)
  have h2 : padicValNat p F = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rw [hF, Ffac, hp.dvd_factorial]
    omega
  rw [h1, h2]; simp

end

end Z3NetU.Proofs

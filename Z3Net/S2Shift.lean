/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.SkSepS2Final
public import Z3Net.S1Shift

@[expose] public section

/-!
# V14 stage S10′: `thm:S2` under digital shifts (`prop:shift`)

The separation proof of `thm:S2` (`S2_core`, `Z3Net/SkSepS2.lean`) uses the points only through the
fine positions `P_c` (`lem:skelred`): `lem:skelred`(i) bounds the toroidal distance by the centred
difference `a_c` of the fine positions, `lem:skelred`(ii) is about two integers in `[0, p^(k+1))`, and
the skeleton relations use the residues `a_c mod p` (the change of digit `k`) and the change of digit
`k - 1`, plus "equal fine positions give equal indices". For the shifted net the fine positions are
`Pf k 1 (C_c v + τ_c)` (`finePosS_eq`, via `shift_coord`); the shift cancels in both residues
(`aDiffS_cast`, `finePosS_div_sub`, from `PfSh_mod`, `PfSh_div`), and equal shifted fine positions give
equal unshifted ones (`PfSh_inj`, `ne_zero_of_neS`). With these transfer lemmas and
`lem:skelred`(i) for the shifted coordinates (`skelred_sepS`), the proof of `S2_core` goes through
unchanged (`S2_core_shift`), hence `thm:S2`(1)–(3) for every digital shift (`S2_sep4_shift_core`,
`S2_sep4_real_shift_core`, `S2_sep_shift_core`, `S2_sep_real_shift_core`), with the generator family
`C` of the skeleton net itself.
-/

namespace Z3NetF.Proofs

open Finset Matrix

namespace SkSep

/-! ## Shifted fine positions -/

/-- Fine position `P_c` of coordinate `c` of the shifted point with index `v`. -/
def finePosS {s : ℕ} (p m k : ℕ) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (τ : Fin s → Fin m → ZMod p) (v : Fin m → ZMod p) (c : Fin s) : ℕ :=
  Z3NetF.digPointShift p m C τ v c / p ^ (m - (k + 1))

variable {s p : ℕ}

lemma finePosS_eq [NeZero p] {m : ℕ} (k : ℕ) (hkm : k + 1 ≤ m) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (τ : Fin s → Fin m → ZMod p) (v : Fin m → ZMod p) (c : Fin s) :
    finePosS p m k C τ v c = Z3NetKN.Geom.Pf k (1 : Matrix (Fin m) (Fin m) (ZMod p)) (C c *ᵥ v + τ c) := by
  unfold finePosS
  rw [Z3NetKN.Geom.shift_coord, Z3NetKN.Geom.coord_split _ _ (k + 1) hkm, Nat.mul_comm,
    Nat.mul_add_div (pow_pos (Nat.pos_of_neZero p) _),
    Nat.div_eq_of_lt (Z3NetKN.Geom.low_lt _ _ _), add_zero]
  rfl

lemma finePosS_lt [NeZero p] {m : ℕ} (k : ℕ) (hkm : k + 1 ≤ m) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (τ : Fin s → Fin m → ZMod p) (v : Fin m → ZMod p) (c : Fin s) :
    finePosS p m k C τ v c < p ^ (k + 1) := by
  rw [finePosS_eq k hkm]; exact Z3NetKN.Geom.Pf_lt _ _

/-- The change of digit `k - 1` read off the shifted fine positions is the unshifted one. -/
lemma finePosS_div_sub [NeZero p] {m : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (τ : Fin s → Fin m → ZMod p)
    (v w : Fin m → ZMod p) (c : Fin s) :
    ((finePosS p m k C τ w c / p ^ 1 % p : ℕ) : ZMod p) -
        ((finePosS p m k C τ v c / p ^ 1 % p : ℕ) : ZMod p) =
      Z3NetKN.Geom.vz (C c *ᵥ w) (k - 1) - Z3NetKN.Geom.vz (C c *ᵥ v) (k - 1) := by
  rw [pow_one, finePosS_eq k hkm, finePosS_eq k hkm, Z3NetKN.Geom.PfSh_div hk,
    Z3NetKN.Geom.Pf_div_gen hk, Z3NetKN.Geom.Pf_div_gen hk]

/-- Centred difference of the shifted fine positions. -/
def aDiffS {m : ℕ} (p k : ℕ) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (τ : Fin s → Fin m → ZMod p) (v w : Fin m → ZMod p) (c : Fin s) : ℤ :=
  cmod (p ^ (k + 1)) ((finePosS p m k C τ w c : ℤ) - finePosS p m k C τ v c)

/-- The residue of `a_c` modulo `p` is the unshifted change of digit `k`: the shift cancels. -/
lemma aDiffS_cast [NeZero p] {m : ℕ} (k : ℕ) (hkm : k + 1 ≤ m) (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p))
    (τ : Fin s → Fin m → ZMod p) (v w : Fin m → ZMod p) (c : Fin s) :
    ((aDiffS p k C τ v w c : ℤ) : ZMod p) =
      Z3NetKN.Geom.vz (C c *ᵥ w) k - Z3NetKN.Geom.vz (C c *ᵥ v) k := by
  unfold aDiffS
  rw [cmod_eq_cen, Z3NetKN.Geom.cen_cast_mod (k + 1) _ _ (by omega), finePosS_eq k hkm, finePosS_eq k hkm,
    Z3NetKN.Geom.PfSh_mod, Z3NetKN.Geom.Pf_mod_gen, Z3NetKN.Geom.Pf_mod_gen]

/-- Distinct indices have some nonzero shifted centred difference. -/
lemma ne_zero_of_neS [NeZero p] {r k : ℕ} {C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p)}
    (hr : r ≤ s) (hC : IsSkGF s r p k C) (hkm : k + 1 ≤ s * k + r)
    (τ : Fin s → Fin (s * k + r) → ZMod p) (v w : Fin (s * k + r) → ZMod p) (hvw : v ≠ w) :
    ∃ c, aDiffS p k C τ v w c ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hvw
  refine eq_of_finePos_eq hr hC hkm v w fun c => ?_
  have := hall c
  unfold aDiffS at this
  rw [cmod_eq_cen] at this
  have h := (Z3NetKN.Geom.eq_of_cen_zero _ _ _ (finePosS_lt k hkm C τ w c)
    (finePosS_lt k hkm C τ v c) this).symm
  rw [finePosS_eq k hkm, finePosS_eq k hkm] at h
  rw [finePos_eq k hkm, finePos_eq k hkm]
  exact Z3NetKN.Geom.PfSh_inj (C c) (τ c) v w h

end SkSep

open SkSep

/-! ## `lem:skelred`(i) for the shifted coordinates -/

lemma skelred_coord_digS {s : ℕ} (p m k : ℕ) (hp : 1 ≤ p) (hkm : k + 1 ≤ m)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (τ : Fin s → Fin m → ZMod p) (v w : Fin m → ZMod p)
    (c : Fin s) :
    (|cmod (p ^ (k + 1)) ((finePosS p m k C τ w c : ℤ) - finePosS p m k C τ v c)| - 1) *
        ((p ^ (m - (k + 1)) : ℕ) : ℤ) ≤
      (cres (p ^ m) ((Z3NetF.digPointShift p m C τ v c : ℤ) -
        (Z3NetF.digPointShift p m C τ w c : ℤ)) : ℤ) := by
  have : NeZero p := ⟨by omega⟩
  have hN : p ^ m = p ^ (k + 1) * p ^ (m - (k + 1)) := by rw [← pow_add]; congr 1; omega
  have hX := digPointShift_lt C τ v c
  have hY := digPointShift_lt C τ w c
  rw [hN] at hX hY
  have := skelred_coord (p ^ (k + 1)) (p ^ (m - (k + 1))) _ _ hX hY
  rw [← cres_neg, neg_sub, hN]
  exact this

/-- **`lem:skelred`(i)**, integer form, for the shifted net. -/
theorem skelred_sepS {s : ℕ} (p m k M : ℕ) (hp : 2 ≤ p) (hkm : k + 1 ≤ m)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (τ : Fin s → Fin m → ZMod p) (v w : Fin m → ZMod p)
    (hM : ∃ c, (M : ℤ) ≤ |cmod (p ^ (k + 1)) ((finePosS p m k C τ w c : ℤ) - finePosS p m k C τ v c)|) :
    (M - 1) ^ 2 * p ^ (2 * (m - (k + 1))) ≤
      torusDist2 (p ^ m) (Z3NetF.digPointShift p m C τ v) (Z3NetF.digPointShift p m C τ w) := by
  obtain ⟨c, hc⟩ := hM
  have hb := skelred_coord_digS p m k (by omega) hkm C τ v w c
  set f := p ^ (m - (k + 1))
  set cr := cres (p ^ m) ((Z3NetF.digPointShift p m C τ v c : ℤ) - (Z3NetF.digPointShift p m C τ w c : ℤ))
  have h1 : (M - 1) * f ≤ cr := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · simp [h0]
    · have : (((M - 1) * f : ℕ) : ℤ) ≤ cr := by
        push_cast [Nat.cast_sub h0]
        have hf0 : (0 : ℤ) ≤ f := by positivity
        nlinarith
      exact_mod_cast this
  calc (M - 1) ^ 2 * p ^ (2 * (m - (k + 1))) = ((M - 1) * f) ^ 2 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm 2]
    _ ≤ cr ^ 2 := Nat.pow_le_pow_left h1 2
    _ ≤ _ := cres_le_torus _ _ _ c

/-! ## The separation core and `thm:S2` -/

open Z3NetKN.Geom

/-- **`prop:shift`**, the separation core of `thm:S2` for every digitally shifted net. -/
theorem S2_core_shift (s p k L : ℕ) (hp : p.Prime) (hs : 4 ≤ s) (hk : 1 ≤ k) (D1 : Finset ℕ)
    (hD1 : ((range (s - 2)).filter (· ∈ D1)).card + 1 ≤ Fs s)
    (hD2 : ((range (s - 2)).filter (· ∉ D1)).card + 1 ≤ Fs s)
    (hL : ∀ (x : Fin (s - 2) → ℤ) (z : Fin 2 → ℤ),
      (∀ i, (p : ℤ) ∣ z i - ∑ d : Fin (s - 2), S2A s p i (d : ℕ) * x d) → ¬(x = 0 ∧ z = 0) →
        (L : ℤ) ≤ |z 0| ∨ (L : ℤ) ≤ |z 1| ∨ ∃ d, (L : ℤ) ≤ |x d|)
    (C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p))
    (hC : IsS2skel s p k D1 C) (τ : Fin s → Fin (s * k + (s - 2)) → ZMod p)
    (v w : Fin (s * k + (s - 2)) → ZMod p) (hvw : v ≠ w) :
    (L - Fs s - 1) ^ 2 * p ^ (2 * ((s - 1) * k + s - 3)) ≤
      torusDist2 (p ^ (s * k + (s - 2))) (Z3NetF.digPointShift p (s * k + (s - 2)) C τ v)
        (Z3NetF.digPointShift p (s * k + (s - 2)) C τ w) := by
  have hp2 := hp.two_le
  have : NeZero p := ⟨by omega⟩
  have hr : s - 2 ≤ s := Nat.sub_le _ _
  have hkm : k + 1 ≤ s * k + (s - 2) := by nlinarith
  have hmk : s * k + (s - 2) - (k + 1) = (s - 1) * k + s - 3 := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 4 := ⟨s - 4, by omega⟩
    have e1 : (t + 4) * k = t * k + 4 * k := by ring
    have e2 : (t + 4 - 1) * k = t * k + 3 * k := by
      rw [show t + 4 - 1 = t + 3 by omega]; ring
    omega
  rw [← hmk]
  rcases Nat.lt_or_ge L (Fs s + 2) with hLF | hLF
  · rw [show L - Fs s - 1 = 0 by omega]; simp
  apply skelred_sepS p _ k (L - Fs s) hp2 hkm C τ v w
  by_contra hcon
  push Not at hcon
  set a := aDiffS p k C τ v w with ha
  have hlt : ∀ c, |a c| < ((L - Fs s : ℕ) : ℤ) := fun c => hcon c
  -- `L ≤ p` (the lattice vector `(p, …, p, 0, 0)`)
  have hLp : L ≤ p := by
    have h := hL (fun _ => (p : ℤ)) 0 (fun i => by
      simp only [Pi.zero_apply, zero_sub, dvd_neg]
      exact Finset.dvd_sum fun d _ => dvd_mul_left _ _)
      (fun h => by
        have := congrFun h.1 ⟨0, by omega⟩
        simp only [Pi.zero_apply, Nat.cast_eq_zero] at this; omega)
    simp only [Pi.zero_apply, abs_zero, Nat.abs_cast] at h
    rcases h with h | h | ⟨_, h⟩ <;> omega
  have hFp : 1 ≤ Fs s := by unfold Fs; omega
  have hap : ∀ c, |a c| < p := fun c => by have := hlt c; push_cast [Nat.cast_sub (by omega : Fs s ≤ L)] at this; omega
  -- carries
  have hcar : ∀ c : Fin s, ∃ x : ℤ,
      ((finePosS p (s * k + (s - 2)) k C τ w c / p ^ 1 : ℕ) : ℤ) - (finePosS p (s * k + (s - 2)) k C τ v c / p ^ 1 : ℕ)
        ≡ x [ZMOD (p : ℤ) ^ (k + 1 - 1)] ∧ (x = 0 ∨ x = Int.sign (a c)) := by
    intro c
    obtain ⟨ξ, h1, -⟩ := skelred_carry p k (finePosS p (s * k + (s - 2)) k C τ v c)
      (finePosS p (s * k + (s - 2)) k C τ w c) hp2 (finePosS_lt k hkm C τ v c) (finePosS_lt k hkm C τ w c) (hap c)
    exact ⟨ξ 1, h1 1 le_rfl hk⟩
  choose ξ hξ using hcar
  have hξcast : ∀ c, ((ξ c : ℤ) : ZMod p) = vz (C c *ᵥ w) (k - 1) - vz (C c *ᵥ v) (k - 1) := by
    intro c
    have hmod := Int.ModEq.of_dvd (dvd_pow_self (p : ℤ) (by omega : k + 1 - 1 ≠ 0)) (hξ c).1
    have := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hmod
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
    rw [← this, ← ZMod.natCast_mod (finePosS p (s * k + (s - 2)) k C τ w c / p ^ 1) p,
      ← ZMod.natCast_mod (finePosS p (s * k + (s - 2)) k C τ v c / p ^ 1) p]
    exact finePosS_div_sub k hk hkm C τ v w c
  -- totals
  set aN := totN a with haN
  set ξN := totN ξ with hξN
  have haN' : ∀ d (hd : d < s), aN d = a ⟨d, hd⟩ := fun d hd => by simp [haN, totN, hd]
  have hξN' : ∀ d (hd : d < s), ξN d = ξ ⟨d, hd⟩ := fun d hd => by simp [hξN, totN, hd]
  have hdigk : ∀ d (hd : d < s - 2), vz w (skOff (s - 2) k d + k) - vz v (skOff (s - 2) k d + k) =
      ((aN d : ℤ) : ZMod p) := by
    intro d hd
    have hdep : k < skDepth (s - 2) k (⟨d, by omega⟩ : Fin s) := by
      unfold skDepth; simp only; rw [if_pos hd]; omega
    rw [haN' d (by omega), ha, aDiffS_cast k hkm, graph_digit hr hC.1 w _ k hdep,
      graph_digit hr hC.1 v _ k hdep]
  have hdigk1 : ∀ d (hd : d < s), vz w (skOff (s - 2) k d + (k - 1)) - vz v (skOff (s - 2) k d + (k - 1)) =
      ((ξN d : ℤ) : ZMod p) := by
    intro d hd
    have hdep : k - 1 < skDepth (s - 2) k (⟨d, hd⟩ : Fin s) := by
      unfold skDepth; simp only; split_ifs <;> omega
    rw [hξN' d hd, hξcast, graph_digit hr hC.1 w _ _ hdep, graph_digit hr hC.1 v _ _ hdep]
  -- the skeleton rows
  have hrow : ∀ z : Fin s, ((a z : ℤ) : ZMod p) = ∑ d ∈ range s, rowBlk C z v w d := by
    intro z
    rw [ha, aDiffS_cast k hkm, row_diff hr _ v w k (by omega)]
    exact Fin.sum_univ_eq_sum_range (fun d => rowBlk C z v w d) s
  have hent : ∀ (i : Fin 2) (z : Fin s), (z : ℕ) = s - 2 + (i : ℕ) → ∀ d (hd : d < s), ∀ l < depthN (s - 2) k d,
      ent (C z) k (skOff (s - 2) k d + l) =
        sk2Coef (s - 2) k (fun i d => ((S2A s p i d : ℤ) : ZMod p))
          (fun i d => ((betaD D1 i d : ℤ) : ZMod p)) ![1, -1] 0 i d l :=
    fun i z hz d hd l hl => hC.2 i z ⟨d, hd⟩ hz l hl
  have blk_full : ∀ (i : Fin 2) (z : Fin s), (z : ℕ) = s - 2 + (i : ℕ) → ∀ d, d < s - 2 →
      rowBlk C z v w d = ((S2A s p i d : ℤ) : ZMod p) * ((aN d : ℤ) : ZMod p) +
        ((betaD D1 i d : ℤ) : ZMod p) * ((ξN d : ℤ) : ZMod p) := by
    intro i z hz d hd
    have hdep : depthN (s - 2) k d = k - 1 + 1 + 1 := by unfold depthN; rw [if_pos hd]; omega
    unfold rowBlk
    rw [hdep, sum_range_succ, sum_range_succ, sum_eq_zero (fun l hl => by
      simp only [mem_range] at hl
      rw [hent i z hz d (by omega) l (by rw [hdep]; omega)]
      simp only [sk2Coef, if_pos hd, if_neg (show l ≠ k by omega), if_neg (show l + 1 ≠ k by omega),
        zero_mul]), zero_add,
      hent i z hz d (by omega) _ (by rw [hdep]; omega), hent i z hz d (by omega) _ (by rw [hdep]; omega)]
    simp only [sk2Coef, if_pos hd, if_neg (show k - 1 ≠ k by omega), if_pos (show k - 1 + 1 = k by omega),
      if_pos (show k - 1 + 1 = k by omega)]
    rw [hdigk1 d (by omega), show k - 1 + 1 = k by omega, hdigk d hd]
    ring
  have blk_own : ∀ (i : Fin 2) (z : Fin s), (z : ℕ) = s - 2 + (i : ℕ) → ∀ d, d = s - 2 + (i : ℕ) →
      rowBlk C z v w d = 0 := by
    intro i z hz d hdi
    unfold rowBlk
    refine sum_eq_zero fun l hl => ?_
    simp only [mem_range] at hl
    have hd : d < s := by omega
    rw [hent i z hz _ hd l hl]
    simp only [sk2Coef, if_neg (show ¬(d < s - 2) by omega), if_pos hdi, Pi.zero_apply]
    split_ifs <;> simp
  have blk_oth : ∀ (i : Fin 2) (z : Fin s), (z : ℕ) = s - 2 + (i : ℕ) → ∀ d, d < s → s - 2 ≤ d →
      d ≠ s - 2 + (i : ℕ) → rowBlk C z v w d = (![(1 : ZMod p), -1] i) * ((ξN d : ℤ) : ZMod p) := by
    intro i z hz d hd hd2 hdi
    have hdep : depthN (s - 2) k d = k - 1 + 1 := by unfold depthN; rw [if_neg (by omega)]; omega
    unfold rowBlk
    rw [hdep, sum_range_succ, sum_eq_zero (fun l hl => by
      simp only [mem_range] at hl
      rw [hent i z hz d hd l (by rw [hdep]; omega)]
      simp only [sk2Coef, if_neg (show ¬(d < s - 2) by omega), if_neg hdi,
        if_neg (show l + 1 ≠ k by omega), zero_mul]), zero_add,
      hent i z hz d hd _ (by rw [hdep]; omega)]
    simp only [sk2Coef, if_neg (show ¬(d < s - 2) by omega), if_neg hdi, if_pos (show k - 1 + 1 = k by omega)]
    rw [hdigk1 d hd]
  have hsplit : ∀ z : Fin s, ∑ d ∈ range s, rowBlk C z v w d =
      ∑ d ∈ range (s - 2), rowBlk C z v w d + rowBlk C z v w (s - 2) + rowBlk C z v w (s - 1) := by
    intro z
    rw [show s - 1 = s - 2 + 1 by omega, ← sum_range_succ, ← sum_range_succ,
      show s - 2 + 1 + 1 = s by omega]
  set z1 : Fin s := ⟨s - 2, by omega⟩
  set z2 : Fin s := ⟨s - 1, by omega⟩
  have hz1 : s - 2 < s := by omega
  have hz2 : s - 1 < s := by omega
  have R0 : ((aN (s - 2) : ℤ) : ZMod p) =
      ∑ d ∈ range (s - 2), (((S2A s p 0 d : ℤ) : ZMod p) * ((aN d : ℤ) : ZMod p) +
        ((betaD D1 0 d : ℤ) : ZMod p) * ((ξN d : ℤ) : ZMod p)) + ((ξN (s - 1) : ℤ) : ZMod p) := by
    rw [haN' _ hz1, hrow ⟨_, hz1⟩, hsplit,
      sum_congr rfl fun d hd => blk_full 0 ⟨_, hz1⟩ (by simp) d (mem_range.mp hd),
      blk_own 0 ⟨_, hz1⟩ (by simp) (s - 2) (by simp),
      blk_oth 0 ⟨_, hz1⟩ (by simp) (s - 1) hz2 (by omega) (by simp <;> omega)]
    simp
  have R1 : ((aN (s - 1) : ℤ) : ZMod p) =
      ∑ d ∈ range (s - 2), (((S2A s p 1 d : ℤ) : ZMod p) * ((aN d : ℤ) : ZMod p) +
        ((betaD D1 1 d : ℤ) : ZMod p) * ((ξN d : ℤ) : ZMod p)) - ((ξN (s - 2) : ℤ) : ZMod p) := by
    have e : ((⟨s - 1, hz2⟩ : Fin s) : ℕ) = s - 2 + ((1 : Fin 2) : ℕ) := by simp <;> omega
    rw [haN' _ hz2, hrow ⟨_, hz2⟩, hsplit,
      sum_congr rfl fun d hd => blk_full 1 ⟨_, hz2⟩ e d (mem_range.mp hd),
      blk_own 1 ⟨_, hz2⟩ e (s - 1) (by simp <;> omega),
      blk_oth 1 ⟨_, hz2⟩ e (s - 2) hz1 le_rfl (by simp <;> omega)]
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  -- bounds on `a` and `ξ`
  have hM0 : ((L - Fs s : ℕ) : ℤ) = (L : ℤ) - Fs s := by push_cast [Nat.cast_sub (by omega : Fs s ≤ L)]; ring
  have haB : ∀ d, d < s → |aN d| ≤ (L : ℤ) - Fs s - 1 := by
    intro d hd; have := hlt ⟨d, hd⟩; rw [hM0] at this; rw [haN' d hd]; omega
  have hsg : ∀ d, d < s → ξN d = 0 ∨ ξN d = (aN d).sign := by
    intro d hd; rw [hξN' d hd, haN' d hd]; exact (hξ _).2
  have hξB : ∀ d, d < s → |ξN d| ≤ 1 := fun d hd => xi_abs _ _ (hsg d hd)
  have hξB' : ∀ d, d < s - 2 → |ξN d| ≤ 1 := fun d hd => hξB d (by omega)
  have hcard0 : |∑ d ∈ range (s - 2), betaD D1 0 d * ξN d| ≤ (Fs s : ℤ) - 1 := by
    have := sum_beta_bound (s - 2) (· ∈ D1) ξN hξB'
    rw [sum_congr rfl fun d _ => by rw [betaD_zero]]
    have h1 : ((#{x ∈ range (s - 2) | x ∈ D1} : ℕ) : ℤ) + 1 ≤ Fs s := by exact_mod_cast hD1
    linarith
  have hcard1 : |∑ d ∈ range (s - 2), betaD D1 1 d * ξN d| ≤ (Fs s : ℤ) - 1 := by
    have := sum_beta_bound (s - 2) (· ∉ D1) ξN hξB'
    rw [sum_congr rfl fun d _ => by rw [betaD_one]]
    have h1 : ((#{x ∈ range (s - 2) | x ∉ D1} : ℕ) : ℤ) + 1 ≤ Fs s := by exact_mod_cast hD2
    linarith
  -- the lattice vector `u`
  set u0 : ℤ := aN (s - 2) - ∑ d ∈ range (s - 2), betaD D1 0 d * ξN d - ξN (s - 1) with hu0
  set u1 : ℤ := aN (s - 1) - ∑ d ∈ range (s - 2), betaD D1 1 d * ξN d + ξN (s - 2) with hu1
  have hdiv : ∀ i : Fin 2, (p : ℤ) ∣ ![u0, u1] i - ∑ d : Fin (s - 2), S2A s p i (d : ℕ) * aN d := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have e := Fin.sum_univ_eq_sum_range (fun d => S2A s p i d * aN d) (s - 2)
    rw [e]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hu0]; push_cast
      rw [R0, sum_add_distrib]; ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hu1]; push_cast
      rw [R1, sum_add_distrib]; ring
  by_cases hzero : (fun d : Fin (s - 2) => aN d) = 0 ∧ ![u0, u1] = 0
  · have hx0 : ∀ d, d < s - 2 → aN d = 0 := fun d hd => by
      have := congrFun hzero.1 ⟨d, hd⟩; simpa using this
    have hξ0 : ∀ d, d < s - 2 → ξN d = 0 := fun d hd => xi_zero _ _ (hsg d (by omega)) (hx0 d hd)
    have hs0 : ∀ i : Fin 2, ∑ d ∈ range (s - 2), betaD D1 i d * ξN d = 0 := fun i =>
      sum_eq_zero fun d hd => by rw [hξ0 d (mem_range.mp hd), mul_zero]
    have e0 : u0 = 0 := by have := congrFun hzero.2 0; simpa using this
    have e1 : u1 = 0 := by have := congrFun hzero.2 1; simpa using this
    rw [hu0, hs0 0] at e0
    rw [hu1, hs0 1] at e1
    obtain ⟨h1, h2⟩ := skew (aN (s - 2)) (aN (s - 1)) (ξN (s - 2)) (ξN (s - 1)) (hsg _ hz1) (hsg _ hz2)
      (by linarith) (by linarith)
    obtain ⟨c, hc⟩ := ne_zero_of_neS hr hC.1 hkm τ v w hvw
    apply hc
    have : aN c = 0 := by
      rcases Nat.lt_or_ge (c : ℕ) (s - 2) with h | h
      · exact hx0 c h
      · rcases (show (c : ℕ) = s - 2 ∨ (c : ℕ) = s - 1 by omega) with h' | h'
        · rw [h']; exact h1
        · rw [h']; exact h2
    rw [haN' c c.isLt] at this
    exact this
  · have hb0 := hcard0
    have hb1 := hcard1
    have a1 := abs_le.mp (haB (s - 2) hz1)
    have a2 := abs_le.mp (haB (s - 1) hz2)
    have x1 := abs_le.mp (hξB (s - 2) hz1)
    have x2 := abs_le.mp (hξB (s - 1) hz2)
    have c0 := abs_le.mp hb0
    have c1 := abs_le.mp hb1
    rcases hL (fun d => aN d) ![u0, u1] hdiv hzero with h | h | ⟨d, h⟩
    · simp only [Matrix.cons_val_zero] at h
      have : |u0| < L := abs_lt.mpr ⟨by rw [hu0]; linarith, by rw [hu0]; linarith⟩
      linarith
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      have : |u1| < L := abs_lt.mpr ⟨by rw [hu1]; linarith, by rw [hu1]; linarith⟩
      linarith
    · have := haB d (by omega)
      have : (Fs s : ℤ) ≥ 1 := by exact_mod_cast hFp
      linarith

/-- **`prop:shift`, `thm:S2`(1)**, separation (integer form), for every digital shift. -/
theorem S2_sep4_shift_core (p k : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hk : 1 ≤ k)
    (C : Fin 4 → Matrix (Fin (4 * k + 2)) (Fin (4 * k + 2)) (ZMod p)) (hC : IsS2skel 4 p k {1} C)
    (τ : Fin 4 → Fin (4 * k + 2) → ZMod p) (v w : Fin (4 * k + 2) → ZMod p) (hvw : v ≠ w) :
    (rhoT p - 4) ^ 2 * p ^ (2 * (3 * k + 1)) ≤
      torusDist2 (p ^ (4 * k + 2)) (Z3NetF.digPointShift p (4 * k + 2) C τ v) (Z3NetF.digPointShift p (4 * k + 2) C τ w) := by
  have hρ2 := two_le_rhoT p hp
  have hρp := rhoT_sq p hp
  have hcore := S2_core_shift 4 p k (rhoT p - 1) Fact.out le_rfl hk {1} (by decide) (by decide)
    (fun x z hz hne => by
      have h0 := hz 0
      have h1 := hz 1
      simp only [S2A, if_true, AT, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue,
        Fin.val_zero, Fin.val_succ, Fin.val_one] at h0 h1
      norm_num at h0 h1
      have hc : (((rhoT p - 1 : ℕ)) : ℤ) = (rhoT p : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ rhoT p)]; ring
      rw [hc]
      rcases skellat_T p (rhoT p) hρ2 hρp x z (by simpa [add_comm] using h0) (by simpa using h1) hne with
        h | h | h | h
      · exact Or.inr (Or.inr ⟨0, h⟩)
      · exact Or.inr (Or.inr ⟨1, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    C hC τ v w hvw
  have e1 : rhoT p - 1 - Fs 4 - 1 = rhoT p - 4 := by simp only [Fs]; omega
  rw [e1] at hcore
  exact hcore

/-- **`prop:shift`, `thm:S2`(1)**, separation (real form), for every digital shift. -/
theorem S2_sep4_real_shift_core (p k : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hk : 1 ≤ k)
    (C : Fin 4 → Matrix (Fin (4 * k + 2)) (Fin (4 * k + 2)) (ZMod p)) (hC : IsS2skel 4 p k {1} C)
    (τ : Fin 4 → Fin (4 * k + 2) → ZMod p) (v w : Fin (4 * k + 2) → ZMod p) (hvw : v ≠ w) :
    ((rhoT p : ℝ) - 4) * (p : ℝ) ^ (-(1 / 2 : ℝ)) * ((p : ℝ) ^ (4 * k + 2)) ^ (-(1 / 4 : ℝ))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (4 * k + 2))
          ((Z3NetF.digPointShift p (4 * k + 2) C τ v c : ℤ) - (Z3NetF.digPointShift p (4 * k + 2) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (4 * k + 2)) ^ 2) := by
  have hsc := rpow_scale p 4 2 k (by omega) (by norm_num) (by norm_num) (by omega)
  have e1 : (-(((4 - 2 : ℕ) : ℝ) / ((4 : ℕ) : ℝ))) = -(1 / 2 : ℝ) := by norm_num
  have e2 : (-(1 / ((4 : ℕ) : ℝ))) = -(1 / 4 : ℝ) := by norm_num
  rw [e1, e2] at hsc
  rw [mul_assoc, hsc]
  have hZ := S2_sep4_shift_core p k hp hk C hC τ v w hvw
  rw [show 2 * (3 * k + 1) = 2 * (4 * k + 2 - (k + 1)) by omega] at hZ
  refine real_of_int_sep p _ _ _ (by omega) _ _ _ ?_ hZ
  have : (rhoT p : ℝ) - 4 ≤ ((rhoT p - 4 : ℕ) : ℝ) := by
    rcases le_or_gt 4 (rhoT p) with h | h
    · push_cast [Nat.cast_sub h]; rfl
    · have : (rhoT p : ℝ) < 4 := by exact_mod_cast h
      have : (0 : ℝ) ≤ ((rhoT p - 4 : ℕ) : ℝ) := by positivity
      linarith
  exact this

/-- **`prop:shift`, `thm:S2`(2), (3)**, separation (integer form), for every digital shift. -/
theorem S2_sep_shift_core (s p k : ℕ) [Fact p.Prime] (hs : 5 ≤ s) (hk : 1 ≤ k) (D1 : Finset ℕ)
    (hD1 : D1 ⊆ range (s - 2)) (hD1c : D1.card = (s - 2) / 2)
    (C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p))
    (hC : IsS2skel s p k D1 C) (τ : Fin s → Fin (s * k + (s - 2)) → ZMod p)
    (v w : Fin (s * k + (s - 2)) → ZMod p) (hvw : v ≠ w) :
    (Bp s p - Fs s) ^ 2 * p ^ (2 * ((s - 1) * k + s - 3)) ≤
      torusDist2 (p ^ (s * k + (s - 2))) (Z3NetF.digPointShift p (s * k + (s - 2)) C τ v)
        (Z3NetF.digPointShift p (s * k + (s - 2)) C τ w) := by
  rcases Nat.eq_zero_or_pos (Bp s p) with h0 | hB
  · have : Bp s p - Fs s = 0 := by omega
    rw [this]; simp
  obtain ⟨c1, c2⟩ := SkSep.card_D s hs D1 hD1 hD1c
  have hcore := S2_core_shift s p k (Bp s p + 1) Fact.out (by omega) hk D1 c1 c2
    (fun x z hz hne => skellatG_at_Bp s p hs hB x z hz hne) C hC τ v w hvw
  rw [show Bp s p + 1 - Fs s - 1 = Bp s p - Fs s by omega] at hcore
  exact hcore

/-- **`prop:shift`, `thm:S2`(2), (3)**, separation (real form), for every digital shift. -/
theorem S2_sep_real_shift_core (s p k : ℕ) [Fact p.Prime] (hs : 5 ≤ s) (hk : 1 ≤ k) (D1 : Finset ℕ)
    (hD1 : D1 ⊆ range (s - 2)) (hD1c : D1.card = (s - 2) / 2)
    (C : Fin s → Matrix (Fin (s * k + (s - 2))) (Fin (s * k + (s - 2))) (ZMod p))
    (hC : IsS2skel s p k D1 C) (τ : Fin s → Fin (s * k + (s - 2)) → ZMod p)
    (v w : Fin (s * k + (s - 2)) → ZMod p) (hvw : v ≠ w) :
    ((Bp s p : ℝ) - Fs s) * (p : ℝ) ^ (-(2 / (s : ℝ))) *
        ((p : ℝ) ^ (s * k + (s - 2))) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * k + (s - 2)))
          ((Z3NetF.digPointShift p (s * k + (s - 2)) C τ v c : ℤ) - (Z3NetF.digPointShift p (s * k + (s - 2)) C τ w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (s * k + (s - 2))) ^ 2) := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hkm : k + 1 ≤ s * k + (s - 2) := by nlinarith
  have hsc := rpow_scale p s (s - 2) k (by omega) (by omega) (Nat.sub_le _ _) hkm
  have e1 : ((s - (s - 2) : ℕ) : ℝ) = 2 := by rw [show s - (s - 2) = 2 by omega]; norm_num
  rw [e1] at hsc
  rw [mul_assoc, hsc]
  have hZ := S2_sep_shift_core s p k hs hk D1 hD1 hD1c C hC τ v w hvw
  have hmk : (s - 1) * k + s - 3 = s * k + (s - 2) - (k + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 5 := ⟨s - 5, by omega⟩
    have e1 : (t + 5) * k = t * k + 5 * k := by ring
    have e2 : (t + 5 - 1) * k = t * k + 4 * k := by rw [show t + 5 - 1 = t + 4 by omega]; ring
    omega
  rw [hmk] at hZ
  refine real_of_int_sep p _ _ _ (by omega) _ _ _ ?_ hZ
  rcases le_or_gt (Fs s) (Bp s p) with h | h
  · push_cast [Nat.cast_sub h]; rfl
  · have : (Bp s p : ℝ) < Fs s := by exact_mod_cast h
    have : (0 : ℝ) ≤ ((Bp s p - Fs s : ℕ) : ℝ) := by positivity
    linarith

end Z3NetF.Proofs

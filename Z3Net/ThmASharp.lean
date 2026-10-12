/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmAThm
public import Z3Net.SUSharp

@[expose] public section

/-!
# Theorem A, part 6: the first-order sharpness of `a*_s` (`thm:A`(2), `k ≥ 2`)

V14 stage S5. The part "Sharpness" of the proof of `thm:A` (`sec:Ustar`), for the net `Apoint`
(`PGen` over `R_S`, reduced modulo `q`), generalizing the proof of `thm:U` (`Z3Net/SUSharp.lean`):
its counting step `USharp.sharp_core` is stated for any graph-form net, and (H1), (H2) of the graph
form of `𝒫^{U*_s}_{k,q}` come from `PGen_H1H2` (`prop:Gs`, `def:Ns`), as in the lower bound.

* `A_sharp_core`: for a coordinate `i` with `α_i = a*_s`, `q > 2a*_s` and
  `q > ∑_{u ≠ i} |F_0[u][i]|`, two distinct points at squared (Euclidean and toroidal) distance, in
  cell units, `< (1 - a*_s/q)² + ∑_{u ≠ i} (|F_0[u][i]| + 1)²/q²`;
* `A_sharp_simple_core`: for `q > (s-1) a*_s` the constant `(s-1)(a*_s+1)²` in place of the sum;
* `A_sharp_real_core`: `δ N^(1/s) < 1 - a*_s/q + (s-1)(a*_s+1)²/q²` (with `q ≥ 5a*_s + 4`).
-/

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

variable {s : ℕ} [NeZero s]

lemma UstarF0_off (hs : 3 ≤ s) (c d : Fin s) (hcd : c ≠ d) : UstarF s 0 c d = Ecol d 0 c := by
  unfold UstarF
  rw [if_neg hcd, if_neg (by omega), if_pos rfl]

lemma UstarF0_diag (c : Fin s) : UstarF s 0 c c = -(alphaS c : ℤ) := by
  unfold UstarF; simp

lemma entry_le_alpha (hs : 3 ≤ s) (c d : Fin s) (hcd : c ≠ d) (j : ℕ) (hj : j ≤ s - 2) :
    (Ecol d j c).natAbs ≤ alphaS c := by
  unfold alphaS
  calc (Ecol d j c).natAbs ≤ (range (s - 1)).sup fun j => (Ecol d j c).natAbs :=
        le_sup (f := fun j => (Ecol d j c).natAbs) (mem_range.2 (by omega))
    _ ≤ _ := single_le_sum (f := fun d => (range (s - 1)).sup fun j => (Ecol d j c).natAbs)
        (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨mem_univ _, fun h => hcd h.symm⟩)

lemma alpha_le_aStar (c : Fin s) : alphaS c ≤ aStar s :=
  le_sup (f := fun c : Fin s => alphaS c) (mem_univ c)

/-- `E_{d,0}[c] = w_c γ_0 ≠ 0` for `c ≠ d`, so `a*_s ≥ 1`. -/
lemma Ecol0_ne (hs : 3 ≤ s) (c d : Fin s) (hcd : c ≠ d) : Ecol d 0 c ≠ 0 := by
  obtain ⟨⟨-, g, hg, hrep⟩, hk, -⟩ := (Ustar_cols_core hs d).1 0 (Nat.zero_le _)
  have hkap := kappa_eq hs (Nat.zero_le _) (Ecol d 0) g hg hrep
  rw [hk] at hkap
  have hγ := (gamS_spec hs d 0 (Nat.zero_le _)).1
  have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_le_zero hg
  intro h0
  have := hrep c hcd
  rw [h0, hgC, eval_C, ← hkap] at this
  push_cast at this
  rcases mul_eq_zero.mp this.symm with h | h
  · exact (wQ_unit_RS (by omega) c d hcd).2.2 h
  · exact hγ.ne' h

lemma aStar_pos (hs : 3 ≤ s) : 1 ≤ aStar s := by
  set d1 : Fin s := ⟨1, by omega⟩
  have h01 : (0 : Fin s) ≠ d1 := by simp [d1, Fin.ext_iff]
  have h1 := entry_le_alpha hs (0 : Fin s) d1 h01 0 (Nat.zero_le _)
  have h2 : 1 ≤ (Ecol d1 0 (0 : Fin s)).natAbs := Int.natAbs_pos.2 (Ecol0_ne hs 0 d1 h01)
  exact h2.trans (h1.trans (alpha_le_aStar 0))

/-- `N^(-1/s) = q^(-k)` for `N = q^(sk)`. -/
lemma rpow_N (s q k : ℕ) (hs : 1 ≤ s) (hq : 0 < q) :
    ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) = 1 / (q : ℝ) ^ k := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : (s : ℝ) ≠ 0 := by
    have h0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    exact h0.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, show ((s * k : ℕ) : ℝ) * (-(1 / (s : ℝ))) =
    -(k : ℝ) by push_cast; field_simp, Real.rpow_neg hq0.le, Real.rpow_natCast, one_div]

lemma sq_lt_of_abs' {D G q t : ℝ} (hG : 0 < G) (hq : 0 < q) (ht : 0 ≤ t) (h : |D| < G * t) :
    (D / (G * q)) ^ 2 < (t / q) ^ 2 :=
  Z3NetU.Proofs.USharp.sq_lt_of_abs hG hq ht h

/-- **Sharpness** (`thm:A`(2), `k ≥ 2`, the printed proof): let `i` attain `a*_s = α_i`. For `q` as in
(1) with `q > 2a*_s` and `q > ∑_{u ≠ i} |F_0[u][i]|`, two distinct points of `𝒫^{U*_s}_{k,q}` have
squared Euclidean and toroidal distance, in cell units,
`< (1 - a*_s/q)² + ∑_{u ≠ i} (|F_0[u][i]| + 1)²/q²`. -/
theorem A_sharp_core (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k) (i : Fin s)
    (hi : alphaS i = aStar s) (hq2 : 2 * aStar s < q)
    (hcol : ∑ u ∈ univ.erase i, |UstarF s 0 u i| < q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 +
          ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (s * k))
          ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 +
          ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  classical
  have : NeZero q := ⟨by have := hq.1; omega⟩
  have hapos := aStar_pos hs
  obtain ⟨ψ⟩ := (A_hom_core hs hq).1
  set Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q) :=
    fun c d => (PPhi k (0 : Fin s) placeA (UstarR s) 1 (UrS s) (betaS s) c d).map ψ with hΦ
  have hpt : Apoint s q k = gfPoint q k Φ := by
    rw [Apoint_eq k ψ]
    unfold gfPoint
    rw [Z3NetF.Proofs.PGen_map_eq]
  obtain ⟨hH1, hH2'⟩ := Z3NetF.Proofs.PGen_H1H2 ψ k (0 : Fin s) placeA (placesOK (by omega))
    (UstarF s) 1 (UrS s) (betaS s) (Ustar_data_core hs).1 (Ustar_data_core hs).2
  have hsk : 0 < s * k - k := by
    have : 2 * k ≤ s * k := Nat.mul_le_mul_right k (by omega)
    omega
  have hent0 : ∀ c d, ent (Φ c d) 0 (k - 1) = ((UstarF s 0 c d : ℤ) : ZMod q) := by
    intro c d
    unfold ent
    rw [dif_pos ⟨hsk, by omega⟩]
    have := hH1 c d ⟨0, hsk⟩ rfl ⟨k - 1, by omega⟩
    simp only at this
    rw [Nat.sub_self, if_pos (by omega)] at this
    exact this
  have hH2 : ∀ r, 1 ≤ r → ent (Φ i i) r (k - 1) = 0 := by
    intro r hr
    unfold ent
    split_ifs with h
    · exact hH2' i ⟨r, h.1⟩ (by simp; omega) ⟨k - 1, h.2⟩
    · rfl
  have hent_le : ∀ u, u ≠ i → |UstarF s 0 u i| ≤ (aStar s : ℤ) := by
    intro u hu
    rw [UstarF0_off hs u i hu, Int.abs_eq_natAbs]
    exact_mod_cast (entry_le_alpha hs u i hu 0 (Nat.zero_le _)).trans (alpha_le_aStar u)
  have hMt : ∀ u, u ≠ i → Mt Φ u i = UstarF s 0 u i := by
    intro u hu
    unfold Mt
    rw [hent0]
    apply Z3NetU.Proofs.USharp.valMinAbs_eq
    have := hent_le u hu
    have : (2 * aStar s : ℤ) < q := by exact_mod_cast hq2
    omega
  have hcolMt : ∑ u ∈ univ.erase i, |Mt Φ u i| < q := by
    rw [Finset.sum_congr rfl fun u hu => by rw [hMt u (mem_erase.mp hu).1]]
    exact hcol
  have hμval : (ent (Φ i i) 0 (k - 1)).val = q - aStar s := by
    rw [hent0, UstarF0_diag, hi, Int.cast_neg, Int.cast_natCast, ZMod.neg_val, if_neg,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hμ : 1 ≤ (ent (Φ i i) 0 (k - 1)).val := by rw [hμval]; omega
  have hnet : IsNet0 s q (s * k) (gfPoint q k Φ) := by
    rw [← hpt]; exact A_net_core s q k hs hq
  obtain ⟨v, w, hvw, hXa, hXu⟩ :=
    Z3NetF.Proofs.USharp.sharp_core hs (by omega) hk Φ hnet i hcolMt hμ hH2
  rw [← hpt, hμval] at hXa
  refine ⟨v, w, hvw, ?_⟩
  set X := Apoint s q k with hX
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set G : ℝ := (q : ℝ) ^ (s * k - k - 1) with hG
  have hGpos : 0 < G := by positivity
  have hQ : (q : ℝ) ^ (s * k) = G * q * (q : ℝ) ^ k := by
    rw [hG, mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
  have hk2 : ((q : ℝ) ^ k) ^ 2 = (q : ℝ) ^ (2 * k) := by rw [← pow_mul, mul_comm]
  have key : ∀ c, (q : ℝ) ^ (2 * k) * (((X v c : ℝ) - X w c) / (q : ℝ) ^ (s * k)) ^ 2 =
      (((X v c : ℝ) - X w c) / (G * q)) ^ 2 := by
    intro c
    rw [hQ, ← hk2]
    field_simp
  have hA : (((X v i : ℝ) - X w i) / (G * q)) ^ 2 = (1 - (aStar s : ℝ) / q) ^ 2 := by
    have : ((X v i : ℝ) - X w i) = -(G * ((q : ℝ) - aStar s)) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hXa
      push_cast [Nat.cast_sub (show aStar s ≤ q by omega)] at this
      rw [hG]; linarith
    rw [this]
    field_simp
  have hU : ∀ u, u ≠ i → (((X v u : ℝ) - X w u) / (G * q)) ^ 2 <
      (((|UstarF s 0 u i| : ℝ) + 1) / q) ^ 2 := by
    intro u hu
    obtain ⟨Δ, hΔ, hXΔ⟩ := hXu u hu
    rw [← hpt] at hXΔ
    apply sq_lt_of_abs' hGpos hq0 (by positivity)
    have e1 : ((X v u : ℝ) - X w u) = -(G * (Mt Φ u i : ℝ) + Δ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hXΔ
      push_cast at this
      rw [hG]; linarith
    rw [e1, abs_neg]
    have hF : |(Mt Φ u i : ℝ)| = (|UstarF s 0 u i| : ℝ) := by
      rw [hMt u hu]
    have hΔ' : |(Δ : ℝ)| < G := by rw [hG]; exact_mod_cast hΔ
    calc |G * (Mt Φ u i : ℝ) + Δ| ≤ G * |(Mt Φ u i : ℝ)| + |(Δ : ℝ)| := by
          rw [← abs_of_pos hGpos, ← abs_mul, abs_of_pos hGpos]; exact abs_add_le _ _
      _ < G * (|UstarF s 0 u i| : ℝ) + G := by rw [hF]; linarith
      _ = G * ((|UstarF s 0 u i| : ℝ) + 1) := by ring
  have hsum : (q : ℝ) ^ (2 * k) * ∑ c, (((X v c : ℝ) - X w c) / (q : ℝ) ^ (s * k)) ^ 2 <
      (1 - (aStar s : ℝ) / q) ^ 2 +
        ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun c _ => key c, ← Finset.add_sum_erase _ _ (mem_univ i),
      hA]
    have hne : (univ.erase i).Nonempty := by
      obtain ⟨u, hu⟩ : ∃ u : Fin s, u ≠ i :=
        ⟨if (i : ℕ) = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
          split_ifs with h <;> intro h' <;> simp [Fin.ext_iff] at h' <;> omega⟩
      exact ⟨u, mem_erase.mpr ⟨hu, mem_univ _⟩⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne fun u hu => hU u (mem_erase.mp hu).1
    have hcongr : ∑ u ∈ univ.erase i, (((|UstarF s 0 u i| : ℝ) + 1) / q) ^ 2 =
        ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 :=
      Finset.sum_congr rfl fun u _ => div_pow _ _ _
    linarith
  refine ⟨hsum, lt_of_le_of_lt ?_ hsum⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum fun c _ => ?_
  rw [div_pow, div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := Z3NetF.Proofs.Deficit.cres_le_abs (q ^ (s * k)) (pow_pos (Nat.pos_of_neZero q) _)
    ((X v c : ℤ) - (X w c : ℤ))
  have h0 : (0 : ℤ) ≤ (cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) := by positivity
  have h1' : ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) : ℝ) ≤ |((X v c : ℝ) - X w c)| := by
    have : ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℤ) : ℝ) ≤
        (((|(X v c : ℤ) - (X w c : ℤ)|) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    exact this
  have h0' : (0 : ℝ) ≤ ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ) := by positivity
  calc ((cres (q ^ (s * k)) ((X v c : ℤ) - (X w c : ℤ)) : ℕ) : ℝ) ^ 2
      ≤ |((X v c : ℝ) - X w c)| ^ 2 := by
        apply pow_le_pow_left₀ h0'
        exact_mod_cast h1'
    _ = ((X v c : ℝ) - X w c) ^ 2 := sq_abs _

/-- **Sharpness**, uniform constant: for `q` as in (1) with `q > (s-1) a*_s` (so `q > 2a*_s` and
`q > ∑_{u ≠ i} |F_0[u][i]|`, since every entry of `F_0` off the diagonal is at most `a*_s`), two
distinct points at squared distance, in cell units, `< (1 - a*_s/q)² + (s-1)(a*_s+1)²/q²`. -/
theorem A_sharp_simple_core (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k)
    (hqa : (s - 1) * aStar s < q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (s * k))
          ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  obtain ⟨i, -, hi⟩ := exists_mem_eq_sup (univ : Finset (Fin s)) univ_nonempty fun c => alphaS c
  have hi' : alphaS i = aStar s := hi.symm
  have hent : ∀ u, u ≠ i → |UstarF s 0 u i| ≤ (aStar s : ℤ) := by
    intro u hu
    rw [UstarF0_off hs u i hu, Int.abs_eq_natAbs]
    exact_mod_cast (entry_le_alpha hs u i hu 0 (Nat.zero_le _)).trans (alpha_le_aStar u)
  have hcard : ((univ.erase i).card : ℝ) = (s : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin, Nat.cast_sub (by omega)]
    push_cast; ring
  have hq2 : 2 * aStar s < q := lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hqa
  have hcol : ∑ u ∈ univ.erase i, |UstarF s 0 u i| < q := by
    calc ∑ u ∈ univ.erase i, |UstarF s 0 u i| ≤ ∑ _u ∈ univ.erase i, (aStar s : ℤ) :=
          sum_le_sum fun u hu => hent u (mem_erase.mp hu).1
      _ = ((s - 1) * aStar s : ℕ) := by
          rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ < q := by exact_mod_cast hqa
  obtain ⟨v, w, hvw, h1, h2⟩ := A_sharp_core hs q k hq hk i hi' hq2 hcol
  have hle : ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ≤
      ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
    rw [← hcard, ← sum_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun u hu => ?_
    have : (|UstarF s 0 u i| : ℝ) ≤ aStar s := by exact_mod_cast hent u (mem_erase.mp hu).1
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  exact ⟨v, w, hvw, by linarith, by linarith⟩

/-- **Sharpness, real form** (`thm:A`(2), `k ≥ 2`): for `q` as in (1) with `q ≥ 5a*_s + 4` and
`q > (s-1) a*_s`, two distinct points of `𝒫^{U*_s}_{k,q}` at toroidal and Euclidean distance
`< (1 - a*_s/q + (s-1)(a*_s+1)²/q²) N^(-1/s)`, `N = q^(sk)`; with the lower bound,
`δ N^(1/s) = 1 - a*_s/q + O(q⁻²)`. -/
theorem A_sharp_real_core (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k)
    (hqa : 5 * aStar s + 4 ≤ q) (hqs : (s - 1) * aStar s < q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((Apoint s q k v c : ℤ) - (Apoint s q k w c : ℤ)) : ℝ)
          / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ∧
      Real.sqrt (∑ c, (((Apoint s q k v c : ℝ) - Apoint s q k w c) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by
  obtain ⟨v, w, hvw, hE, hT⟩ := A_sharp_simple_core hs q k hq hk hqs
  refine ⟨v, w, hvw, ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by have := hq.1; omega)
  rw [rpow_N s q k (by omega) (by have := hq.1; omega)]
  set α : ℝ := 1 - (aStar s : ℝ) / q
  set β : ℝ := ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hα : (4 : ℝ) / 5 ≤ α := by
    have : (5 * aStar s + 4 : ℝ) ≤ q := by exact_mod_cast hqa
    have : (aStar s : ℝ) / q ≤ 1 / 5 := by
      rw [div_le_iff₀ hq0]; linarith
    linarith
  have hβ : 0 ≤ β := by
    have : (1 : ℝ) ≤ s - 1 := by
      have : (3 : ℝ) ≤ s := by exact_mod_cast hs
      linarith
    positivity
  have hk2 : (q : ℝ) ^ (2 * k) = ((q : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  have hsq : α ^ 2 + β ≤ (α + β) ^ 2 := by nlinarith
  have key : ∀ S : ℝ, 0 ≤ S → (q : ℝ) ^ (2 * k) * S < α ^ 2 + β →
      Real.sqrt S < (α + β) * (1 / (q : ℝ) ^ k) := by
    intro S hS0 h
    have h1 : (q : ℝ) ^ (2 * k) * S < (α + β) ^ 2 := by linarith
    rw [hk2] at h1
    rw [Real.sqrt_lt' (by positivity), mul_one_div, div_pow, lt_div_iff₀ (by positivity)]
    linarith
  exact ⟨key _ (by positivity) hT, key _ (by positivity) hE⟩

end

end Z3NetA.Proofs

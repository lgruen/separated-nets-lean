/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.ThmASharp
public import Z3Net.ThmAShift

@[expose] public section

/-!
# V14 stage S10′: `prop:shift` for the sharpness in `thm:A`(2)

The first-order sharpness of `a*_s` (`thm:A`(2), `k ≥ 2`) holds for every digital shift of the net of
`thm:A`. By `lem:shift` (`Z3NetF.Proofs.shift_affine`), re-indexed by `v ↦ v + TcK τ`, the shifted net
is the affine graph form with digits `G_c v + γ_c`, `γ = gammaK Φ τ` vanishing on the cell digits.

* `Z3NetF.Proofs.USharpShift.sharp_coreA`: the counting step `USharp.sharp_core` for the affine graph
  form. The index is chosen by `exists_good` (the joint uniformity of leading digits given by `t = 0`)
  with the translated digit sets: the first offset digit of coordinate `a` is prescribed to be
  `-1 - γ_a(k)` (so the shifted digit is `-1`), and the bad set of a test coordinate `u` is the set of
  wrapping digits translated by `-γ_u(k)`, of the same cardinality. The differences of digits under the
  own-axis step are those of the unshifted form (`γ` cancels).
* `Z3NetA.Proofs.A_sharp_shift_core`, `A_sharp_simple_shift_core`, `A_sharp_shift_real_core`: the
  statements of `A_sharp_core`, `A_sharp_simple_core`, `A_sharp_real_core` for
  `digPointShift q (s*k) (AGen s q k) τ`, every shift `τ`.
-/

namespace Z3NetF.Proofs

open Matrix Finset ObsCount ObsStep

noncomputable section

set_option linter.unusedSectionVars false

namespace USharpShift

variable {s q k : ℕ} [NeZero q]

/-- Total accessor of the additive constant: digit `j` of `γ_c`, `0` out of range. -/
def gd (γ : Fin s → Fin (s * k) → ZMod q) (c : Fin s) (j : ℕ) : ZMod q :=
  if h : j < s * k then γ c ⟨j, h⟩ else 0

lemma dv_eqA (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (γ : Fin s → Fin (s * k) → ZMod q) (v : Fin (s * k) → ZMod q) (c : Fin s) (j : ℕ) :
    Z3NetU.Proofs.dv s q k (DgA s q k Φ γ c v) j =
      (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v j + gd γ c j).val := by
  unfold Z3NetU.Proofs.dv DgA dig gd
  rw [ObsStep.Cg_eq Φ]
  split_ifs <;> simp

lemma o0A_eq (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (γ : Fin s → Fin (s * k) → ZMod q) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    o0A s q k Φ γ v c =
      (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v k + gd γ c k).val :=
  dv_eqA Φ γ v c k

lemma tlA_eq (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (γ : Fin s → Fin (s * k) → ZMod q) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    tlA s q k Φ γ v c =
      TS q (fun j => (dig (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ c) v j + gd γ c j).val)
        (k + 1) (s * k) := by
  unfold tlA Z3NetU.Proofs.tail TS
  exact Finset.sum_congr rfl fun j _ => by rw [dv_eqA]

/-- Translating a digit set does not change its size. -/
lemma card_filter_add (P : ZMod q → Prop) [DecidablePred P] (g : ZMod q) :
    (univ.filter fun x => P (x + g)).card = (univ.filter P).card := by
  refine Finset.card_bij (fun x _ => x + g) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact hx
  · intro x _ y _ h
    exact add_right_cancel h
  · intro y hy
    refine ⟨y - g, ?_, sub_add_cancel y g⟩
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    rw [sub_add_cancel]
    exact hy

/-- **The counting step of the sharpness for affine graph forms** (`prop:shift`): `USharp.sharp_core`
for the digits `G_c v + γ_c`, `γ` vanishing on the cell digits. -/
theorem sharp_coreA (hs : 3 ≤ s) (hq : 3 ≤ q) (hk : 2 ≤ k)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (γ : Fin s → Fin (s * k) → ZMod q) (hγ : ∀ c (i : Fin (s * k)), (i : ℕ) < k → γ c i = 0)
    (hnet : Z3NetF.IsNet0 s q (s * k) (Z3NetF.gfPoint q k Φ)) (a : Fin s)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) (hμ : 1 ≤ (Z3NetF.ent (Φ a a) 0 (k - 1)).val)
    (hH2 : ∀ r, 1 ≤ r → Z3NetF.ent (Φ a a) r (k - 1) = 0) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ w a : ℤ) -
          Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v a =
          (q : ℤ) ^ (s * k - k - 1) * (Z3NetF.ent (Φ a a) 0 (k - 1)).val ∧
      ∀ u, u ≠ a → ∃ Δ : ℤ, |Δ| < (q : ℤ) ^ (s * k - k - 1) ∧
        (Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ w u : ℤ) -
          Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v u =
          (q : ℤ) ^ (s * k - k - 1) * Z3NetF.Mt Φ u a + Δ := by
  classical
  have hk0 : 0 < k := by omega
  have hsk : 3 * k ≤ s * k := Nat.mul_le_mul_right k hs
  have hsk1 : k + 1 ≤ s * k := by omega
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  set C := Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ with hC
  have hunit := ObsCeil.unit_of_net C hnet
  obtain ⟨v, hvA, hvB⟩ := exists_good C k hunit
    (fun c => if c = a then s * k - k - 1 else 0)
    (fun _ j => if j < k then {0} else if j = k then {-1 - gd γ a k} else univ)
    (fun c j _ => by split_ifs <;> simp)
    (univ.erase a)
    (by obtain ⟨u, hu⟩ : ∃ u : Fin s, u ≠ a := by
          by_contra h; push Not at h
          have : Fintype.card (Fin s) ≤ 1 := Fintype.card_le_one_iff.mpr fun x y => by
            rw [h x, h y]
          simp at this; omega
        exact ⟨u, mem_erase.mpr ⟨hu, mem_univ _⟩⟩)
    (fun u hu => by simp [(mem_erase.mp hu).1])
    (by rw [Finset.sum_ite_eq']; simp only [mem_univ, if_true]; omega)
    (fun u => univ.filter fun x => ¬ NoWrap (Z3NetF.Mt Φ u a) (x + gd γ u k))
    (by
      calc ∑ u ∈ univ.erase a,
            (univ.filter fun x => ¬ NoWrap (Z3NetF.Mt Φ u a) (x + gd γ u k)).card
          = ∑ u ∈ univ.erase a, (univ.filter fun x => ¬ NoWrap (Z3NetF.Mt Φ u a) x).card :=
            Finset.sum_congr rfl fun u _ =>
              card_filter_add (fun x => ¬ NoWrap (Z3NetF.Mt Φ u a) x) _
        _ ≤ ∑ u ∈ univ.erase a, (Z3NetF.Mt Φ u a).natAbs :=
            Finset.sum_le_sum fun u _ => card_wrap_le _
        _ < q := by
          have : ((∑ u ∈ univ.erase a, (Z3NetF.Mt Φ u a).natAbs : ℕ) : ℤ) =
              ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| := by
            rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun u _ => Int.natCast_natAbs _
          omega)
  have hvA' : ∀ j < s * k - k - 1, dig (C a) v j ∈
      (if j < k then ({0} : Finset (ZMod q)) else if j = k then {-1 - gd γ a k} else univ) := by
    intro j hj
    exact hvA a j (by simpa using hj)
  have hcell0 : ∀ i (hi : i < k), v (Z3NetU.Proofs.ix k a ⟨i, hi⟩) = 0 := by
    intro i hi
    have := hvA' i (by omega)
    rw [if_pos hi, mem_singleton, dig_cell Φ a v i hi] at this
    exact this
  have hd0 : dig (C a) v k = -1 - gd γ a k := by
    have := hvA' k (by omega)
    rwa [if_neg (by omega), if_pos rfl, mem_singleton] at this
  have hgood : ∀ u, u ≠ a → NoWrap (Z3NetF.Mt Φ u a) (dig (C u) v k + gd γ u k) := by
    intro u hu
    have := hvB u (mem_erase.mpr ⟨hu, mem_univ _⟩)
    simpa using this
  -- the neighbour
  set e : Fin s → ZMod q := Pi.single a 1 with he
  set w := v + stepVec hk0 e with hw
  have hstep : ∀ c (r : ℕ), r < s * k - k →
      dig (C c) w (k + r) = dig (C c) v (k + r) + Z3NetF.ent (Φ c a) r (k - 1) := by
    intro c r hr
    have h0 := dig_step_off Φ hk0 e c r hr
    rw [hw, dig_add, h0]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp [he]
    · intro d _ hd; simp [he, hd]
    · simp
  have hvw : v ≠ w := by
    intro h
    have h1 := congrFun h (Z3NetU.Proofs.ix k a ⟨k - 1, by omega⟩)
    rw [hw, Pi.add_apply, stepVec_apply, if_pos rfl] at h1
    simp only [he, Pi.single_eq_same] at h1
    exact one_ne_zero (by linear_combination -h1)
  refine ⟨v, w, hvw, ?_, ?_⟩
  · -- the moving coordinate `a`: exact displacement
    have hX := X_decompA s q k Φ γ hγ hsk1 v a
    have hY := X_decompA s q k Φ γ hγ hsk1 w a
    have hcl := cellN_step hk0 v e a
    rw [hcell0 (k - 1) (by omega)] at hcl
    simp only [he, Pi.single_eq_same, zero_add, ZMod.val_zero, ZMod.val_one] at hcl
    set μ := Z3NetF.ent (Φ a a) 0 (k - 1)
    have hμl := ZMod.val_lt μ
    have ho0w : ((o0A s q k Φ γ w a : ℕ) : ℤ) = μ.val - 1 := by
      have := hstep a 0 (by omega)
      rw [add_zero] at this
      have e1 : dig (C a) w k + gd γ a k = (-1 : ZMod q) + μ := by
        rw [this, hd0]; ring
      rw [o0A_eq, ← hC, e1]
      have : (-1 : ZMod q) + μ = (-1 : ZMod q) + (((μ.val : ℤ)) : ZMod q) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [this, val_wrap_up]
      · rw [val_m1]; omega
      · rw [val_m1]; omega
      · rw [val_m1]; omega
    have ho0v : ((o0A s q k Φ γ v a : ℕ) : ℤ) = q - 1 := by
      rw [o0A_eq, ← hC, hd0, sub_add_cancel, val_m1]; omega
    -- equal tails, by (H2)
    have htl : tlA s q k Φ γ w a = tlA s q k Φ γ v a := by
      rw [tlA_eq, tlA_eq]
      unfold TS
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [mem_Ico] at hj
      have := hstep a (j - k) (by omega)
      rw [show k + (j - k) = j by omega, hH2 (j - k) (by omega), add_zero] at this
      dsimp only
      rw [← hC, this]
    rw [hX, hY, htl]
    have hG : (q : ℤ) ^ (s * k - k) = (q : ℤ) ^ (s * k - k - 1) * q := by
      rw [← pow_succ]; congr 1; omega
    rw [hG, ho0w, ho0v]
    linear_combination (q : ℤ) ^ (s * k - k - 1) * (q : ℤ) * hcl
  · -- the transverse coordinates
    intro u hu
    have hX := X_decompA s q k Φ γ hγ hsk1 v u
    have hY := X_decompA s q k Φ γ hγ hsk1 w u
    have hcl := cellN_step hk0 v e u
    simp only [he, Pi.single_eq_of_ne hu, add_zero, sub_self] at hcl
    have hnw := hgood u hu
    unfold NoWrap at hnw
    have hMt : ((Z3NetF.Mt Φ u a : ℤ) : ZMod q) = Z3NetF.ent (Φ u a) 0 (k - 1) :=
      ZMod.coe_valMinAbs _
    have ho0 : ((o0A s q k Φ γ w u : ℕ) : ℤ) = (o0A s q k Φ γ v u : ℕ) + Z3NetF.Mt Φ u a := by
      have := hstep u 0 (by omega)
      rw [add_zero] at this
      rw [o0A_eq, o0A_eq, ← hC, this,
        show dig (C u) v k + Z3NetF.ent (Φ u a) 0 (k - 1) + gd γ u k =
          dig (C u) v k + gd γ u k + ((Z3NetF.Mt Φ u a : ℤ) : ZMod q) by rw [hMt]; ring]
      exact hnw
    have htv : tlA s q k Φ γ v u < q ^ (s * k - k - 1) := Z3NetU.Proofs.tail_lt s q k hsk1 _
    have htw : tlA s q k Φ γ w u < q ^ (s * k - k - 1) := Z3NetU.Proofs.tail_lt s q k hsk1 _
    refine ⟨(tlA s q k Φ γ w u : ℤ) - tlA s q k Φ γ v u, ?_, ?_⟩
    · rw [abs_lt]
      have h1 : (tlA s q k Φ γ v u : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by exact_mod_cast htv
      have h2 : (tlA s q k Φ γ w u : ℤ) < (q : ℤ) ^ (s * k - k - 1) := by exact_mod_cast htw
      have : (tlA s q k Φ γ w u : ℤ) ≥ 0 := by positivity
      have : (tlA s q k Φ γ v u : ℤ) ≥ 0 := by positivity
      constructor <;> linarith
    · rw [hX, hY, ho0]
      linear_combination (q : ℤ) ^ (s * k - k) * hcl

end USharpShift

end

end Z3NetF.Proofs

namespace Z3NetA.Proofs

open Polynomial Finset Z3NetF Z3NetA

set_option linter.unusedSectionVars false

noncomputable section

variable {s : ℕ} [NeZero s]

/-- **Sharpness under digital shifts** (`prop:shift`, `thm:A`(2), `k ≥ 2`): `A_sharp_core` for every
digitally shifted net `𝒫^{U*_s}_{k,q} ⊕ τ`. -/
theorem A_sharp_shift_core (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k) (i : Fin s)
    (hi : alphaS i = aStar s) (hq2 : 2 * aStar s < q)
    (hcol : ∑ u ∈ univ.erase i, |UstarF s 0 u i| < q) (τ : Fin s → Fin (s * k) → ZMod q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((digPointShift q (s * k) (AGen s q k) τ v c : ℝ) -
          digPointShift q (s * k) (AGen s q k) τ w c) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 +
          ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (s * k))
          ((digPointShift q (s * k) (AGen s q k) τ v c : ℤ) -
            (digPointShift q (s * k) (AGen s q k) τ w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2
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
  have hgen : AGen s q k = graphGenK (m := s * k) (fun _ => k) Φ := by
    rw [AGen_eq k ψ, Z3NetF.Proofs.PGen_map_eq]
  set T := Z3NetF.Proofs.TcK τ with hT
  set γ := Z3NetF.Proofs.gammaK Φ τ with hγ
  -- `lem:shift`: re-indexed by `v ↦ v + T`, the shifted net is the affine graph form with `γ`
  have hsh : ∀ v, digPointShift q (s * k) (AGen s q k) τ v =
      digPointShift q (s * k) (graphGenK (m := s * k) (fun _ => k) Φ) γ (v + T) := by
    intro v
    rw [hgen]
    exact Z3NetF.Proofs.shift_affine Φ τ v
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
  obtain ⟨v₀, w₀, hvw₀, hXa₀, hXu₀⟩ :=
    Z3NetF.Proofs.USharpShift.sharp_coreA hs (by omega) hk Φ γ
      (Z3NetF.Proofs.gammaK_cell Φ τ) hnet i hcolMt hμ hH2
  rw [hμval] at hXa₀
  -- back to the indices of the shifted net
  set v := v₀ - T with hv
  set w := w₀ - T with hw
  have hv0 : v + T = v₀ := sub_add_cancel v₀ T
  have hw0 : w + T = w₀ := sub_add_cancel w₀ T
  set X := digPointShift q (s * k) (AGen s q k) τ with hX
  have hXa : (X w i : ℤ) - X v i = (q : ℤ) ^ (s * k - k - 1) * ((q - aStar s : ℕ) : ℤ) := by
    rw [hsh w, hsh v, hv0, hw0]; exact hXa₀
  have hXu : ∀ u, u ≠ i → ∃ Δ : ℤ, |Δ| < (q : ℤ) ^ (s * k - k - 1) ∧
      (X w u : ℤ) - X v u = (q : ℤ) ^ (s * k - k - 1) * Mt Φ u i + Δ := by
    intro u hu
    rw [hsh w, hsh v, hv0, hw0]; exact hXu₀ u hu
  have hvw : v ≠ w := by
    intro h; apply hvw₀; rw [← hv0, ← hw0, h]
  refine ⟨v, w, hvw, ?_⟩
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

/-- **Sharpness under digital shifts**, uniform constant: `A_sharp_simple_core` for every digital
shift. -/
theorem A_sharp_simple_shift_core (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k)
    (hqa : (s - 1) * aStar s < q) (τ : Fin s → Fin (s * k) → ZMod q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ (2 * k) * ∑ c, (((digPointShift q (s * k) (AGen s q k) τ v c : ℝ) -
          digPointShift q (s * k) (AGen s q k) τ w c) / (q : ℝ) ^ (s * k)) ^ 2
        < (1 - (aStar s : ℝ) / q) ^ 2 + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ∧
      (q : ℝ) ^ (2 * k) * ∑ c, ((cres (q ^ (s * k))
          ((digPointShift q (s * k) (AGen s q k) τ v c : ℤ) -
            (digPointShift q (s * k) (AGen s q k) τ w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2
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
  obtain ⟨v, w, hvw, h1, h2⟩ := A_sharp_shift_core hs q k hq hk i hi' hq2 hcol τ
  have hle : ∑ u ∈ univ.erase i, ((|UstarF s 0 u i| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 ≤
      ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
    rw [← hcard, ← sum_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun u hu => ?_
    have : (|UstarF s 0 u i| : ℝ) ≤ aStar s := by exact_mod_cast hent u (mem_erase.mp hu).1
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  exact ⟨v, w, hvw, by linarith, by linarith⟩

/-- **Sharpness under digital shifts, real form** (`prop:shift`, `thm:A`(2), `k ≥ 2`):
`A_sharp_real_core` for every digitally shifted net `𝒫^{U*_s}_{k,q} ⊕ τ`. -/
theorem A_sharp_shift_real_core (hs : 3 ≤ s) (q k : ℕ) (hq : AdmBase s q) (hk : 2 ≤ k)
    (hqa : 5 * aStar s + 4 ≤ q) (hqs : (s - 1) * aStar s < q) (τ : Fin s → Fin (s * k) → ZMod q) :
    ∃ v w : Fin (s * k) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((cres (q ^ (s * k)) ((digPointShift q (s * k) (AGen s q k) τ v c : ℤ) -
          (digPointShift q (s * k) (AGen s q k) τ w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) ∧
      Real.sqrt (∑ c, (((digPointShift q (s * k) (AGen s q k) τ v c : ℝ) -
          digPointShift q (s * k) (AGen s q k) τ w c) / (q : ℝ) ^ (s * k)) ^ 2) <
        (1 - (aStar s : ℝ) / q + ((s : ℝ) - 1) * ((aStar s : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * k)) ^ (-(1 / (s : ℝ))) := by
  obtain ⟨v, w, hvw, hE, hT⟩ := A_sharp_simple_shift_core hs q k hq hk hqs τ
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

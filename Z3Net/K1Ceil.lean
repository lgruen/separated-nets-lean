/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.SUSharp
public import Z3Net.FDeficit
public import Z3Net.ThmASharp

@[expose] public section

/-!
# V14 stage S8: `prop:k1`(3), the ceiling at one cell level

A digital net in graph form with depths `(1, …, 1)` (`m = s`, `N = q^s`) whose first offset rows form
the integer matrix `F₀` and whose deeper rows vanish in their own column ((H2)). For a coordinate `a`
with `F₀[a][a] = -K₁` and `q > 2 max |F₀|`, the step `e_a` from a cell with `r_a ≥ K₁` and
`r_u + F₀[u][a] ∈ [0, q)` (`u ≠ a`) moves coordinate `a` by exactly `1 - K₁/q` cells and every other
coordinate `u` by less than `(|F₀[u][a]| + 1)/q` (`step_core`). Such a cell exists

* if `gcd(det F₀, q) = 1`: `n ↦ r = F₀ n` is a bijection, so `r` can be prescribed (`cell_det`);
* if the net is a `(0,s,s)`-net with `s ≥ 4` and `∑_{u ≠ a} |F₀[u][a]| < q`: by the union bound over
  the boxes with depth `s - 2` on `a` and `2` on `u` (`ObsCount.exists_good`; the paper uses the
  boxes with depths `2` on `a` and `u`, `0` on two further coordinates and `1` elsewhere: both have
  total depth `s` and contain the two leading digits of `a` and of `u`), with `n_a ≠ q - 1`, so the
  pair does not cross the boundary of the cube (`cell_net`).
-/

namespace Z3NetF.Proofs.K1Ceil

open Matrix Finset ObsCount ObsStep

set_option linter.unusedSectionVars false

noncomputable section

variable {s q : ℕ} [NeZero q]

/-- The generator matrices of the graph form with depths `(1, …, 1)`. -/
abbrev C1 (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q)) :
    Fin s → Matrix (Fin (s * 1)) (Fin (s * 1)) (ZMod q) :=
  Z3NetF.graphGenK (m := s * 1) (fun _ => 1) Φ

/-- The step vector `e_a` (the cell digit of `a` increases by one). -/
abbrev stepA (a : Fin s) : Fin (s * 1) → ZMod q := stepVec (k := 1) (by norm_num) (Pi.single a 1)

lemma cellN_one (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (v : Fin (s * 1) → ZMod q) (c : Fin s) :
    Z3NetU.Proofs.cellN s q 1 v c = (dig (C1 Φ c) v 0).val := by
  rw [dig_cell Φ c v 0 (by norm_num)]
  simp [Z3NetU.Proofs.cellN, Z3NetU.Proofs.ad]

/-- **The step.** -/
theorem step_core (hs : 2 ≤ s) (hq : 2 ≤ q) (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (a : Fin s) (K : ℕ) (hμ : Z3NetF.ent (Φ a a) 0 0 = -(K : ZMod q))
    (hH2 : ∀ r, 1 ≤ r → Z3NetF.ent (Φ a a) r 0 = 0) (v : Fin (s * 1) → ZMod q)
    (hra : K ≤ (dig (C1 Φ a) v 1).val)
    (hgood : ∀ u, u ≠ a → NoWrap (Z3NetF.Mt Φ u a) (dig (C1 Φ u) v 1)) :
    v ≠ v + stepA a ∧
    (Z3NetF.gfPoint q 1 Φ (v + stepA a) a : ℤ) - Z3NetF.gfPoint q 1 Φ v a =
        (q : ℤ) ^ (s * 1 - 1) * (((dig (C1 Φ a) v 0 + 1).val : ℤ) - (dig (C1 Φ a) v 0).val) -
          (q : ℤ) ^ (s * 1 - 1 - 1) * K ∧
    ∀ u, u ≠ a → ∃ Δ : ℤ, |Δ| < (q : ℤ) ^ (s * 1 - 1 - 1) ∧
        (Z3NetF.gfPoint q 1 Φ (v + stepA a) u : ℤ) - Z3NetF.gfPoint q 1 Φ v u =
          (q : ℤ) ^ (s * 1 - 1 - 1) * Z3NetF.Mt Φ u a + Δ := by
  classical
  have hq1 : Fact (1 < q) := ⟨by omega⟩
  have hk0 : (0 : ℕ) < 1 := by norm_num
  set e : Fin s → ZMod q := Pi.single a 1 with he
  set w := v + stepA (q := q) a with hw
  have hsk1 : 1 + 1 ≤ s * 1 := by omega
  have hstep : ∀ c (r : ℕ), r < s * 1 - 1 →
      dig (C1 Φ c) w (1 + r) = dig (C1 Φ c) v (1 + r) + Z3NetF.ent (Φ c a) r 0 := by
    intro c r hr
    have h0 := dig_step_off Φ hk0 e c r hr
    rw [hw, dig_add, h0]
    congr 1
    rw [Finset.sum_eq_single a]
    · simp [he]
    · intro d _ hd; simp [he, hd]
    · simp
  have hcell : ∀ c, dig (C1 Φ c) w 0 = dig (C1 Φ c) v 0 + e c := by
    intro c
    rw [hw, dig_add, dig_step_cell Φ hk0 e c 0 hk0, if_pos rfl]
  have hvw : v ≠ w := by
    intro h
    have h1 := hcell a
    rw [← h] at h1
    simp only [he, Pi.single_eq_same] at h1
    exact one_ne_zero (by linear_combination -h1)
  refine ⟨hvw, ?_, ?_⟩
  · have hX := X_eq Φ hsk1 v a
    have hY := X_eq Φ hsk1 w a
    rw [cellN_one Φ v a] at hX
    rw [cellN_one Φ w a, hcell a] at hY
    simp only [he, Pi.single_eq_same] at hY
    have ho : ((dig (C1 Φ a) w 1).val : ℤ) = (dig (C1 Φ a) v 1).val - K := by
      have := hstep a 0 (by omega)
      rw [add_zero, hμ] at this
      rw [this]
      have hnw : NoWrap (-(K : ℤ)) (dig (C1 Φ a) v 1) := by
        rw [noWrap_iff]
        have := ZMod.val_lt (dig (C1 Φ a) v 1)
        constructor <;> omega
      unfold NoWrap at hnw
      push_cast at hnw
      rw [hnw]; ring
    have htl : tl Φ w a = tl Φ v a := by
      unfold tl TS
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [mem_Ico] at hj
      have := hstep a (j - 1) (by omega)
      rw [show 1 + (j - 1) = j by omega, hH2 (j - 1) (by omega), add_zero] at this
      dsimp only
      rw [this]
    rw [hX, hY, htl, ho]
    have hG : (q : ℤ) ^ (s * 1 - 1) = (q : ℤ) ^ (s * 1 - 1 - 1) * q := by
      rw [← pow_succ]; congr 1; omega
    ring
  · intro u hu
    have hX := X_eq Φ hsk1 v u
    have hY := X_eq Φ hsk1 w u
    rw [cellN_one Φ v u] at hX
    rw [cellN_one Φ w u, hcell u] at hY
    simp only [he, Pi.single_eq_of_ne hu, add_zero] at hY
    have hnw := hgood u hu
    unfold NoWrap at hnw
    have hMt : ((Z3NetF.Mt Φ u a : ℤ) : ZMod q) = Z3NetF.ent (Φ u a) 0 (1 - 1) :=
      ZMod.coe_valMinAbs _
    rw [hMt] at hnw
    have ho0 : ((dig (C1 Φ u) w 1).val : ℤ) = (dig (C1 Φ u) v 1).val + Z3NetF.Mt Φ u a := by
      have := hstep u 0 (by omega)
      rw [add_zero] at this
      rw [this]; exact hnw
    have htv := tl_lt Φ hsk1 v u
    have htw := tl_lt Φ hsk1 w u
    refine ⟨(tl Φ w u : ℤ) - tl Φ v u, ?_, ?_⟩
    · rw [abs_lt]
      have h1 : (tl Φ v u : ℤ) < (q : ℤ) ^ (s * 1 - 1 - 1) := by exact_mod_cast htv
      have h2 : (tl Φ w u : ℤ) < (q : ℤ) ^ (s * 1 - 1 - 1) := by exact_mod_cast htw
      have : (tl Φ w u : ℤ) ≥ 0 := by positivity
      have : (tl Φ v u : ℤ) ≥ 0 := by positivity
      constructor <;> linarith
    · rw [hX, hY, ho0]
      ring

/-! ## The good cell -/

/-- `(0,s,s)`-net, `s ≥ 4`: a cell with `n_a ≠ q - 1`, `r_a ≥ K` and no wrap of `r_u + M̃[u][a]`. -/
theorem cell_net (hs : 4 ≤ s) (hq : 3 ≤ q)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (hnet : Z3NetF.IsNet0 s q (s * 1) (Z3NetF.gfPoint q 1 Φ)) (a : Fin s) (K : ℕ) (hK : K < q)
    (hcol : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q) :
    ∃ v : Fin (s * 1) → ZMod q, dig (C1 Φ a) v 0 ≠ -1 ∧ K ≤ (dig (C1 Φ a) v 1).val ∧
      ∀ u, u ≠ a → NoWrap (Z3NetF.Mt Φ u a) (dig (C1 Φ u) v 1) := by
  classical
  have hunit := ObsCeil.unit_of_net (C1 Φ) hnet
  obtain ⟨v, hvA, hvB⟩ := exists_good (C1 Φ) 1 hunit
    (fun c => if c = a then s * 1 - 2 else 0)
    (fun c j => if c = a then (if j = 0 then univ.erase (-1 : ZMod q)
      else if j = 1 then univ.filter (fun x : ZMod q => K ≤ x.val) else univ) else univ)
    (fun c j _ => by
      split_ifs
      · exact ⟨0, by
          simp only [mem_erase, mem_univ, and_true]
          intro h
          have := congrArg ZMod.val h
          rw [ZMod.val_zero, val_m1] at this
          omega⟩
      · exact ⟨-1, by simp only [mem_filter, mem_univ, true_and]; rw [val_m1]; omega⟩
      · exact univ_nonempty
      · exact univ_nonempty)
    (univ.erase a)
    (by obtain ⟨u, hu⟩ : ∃ u : Fin s, u ≠ a :=
          ⟨if (a : ℕ) = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
            split_ifs with h <;> intro h' <;> simp [Fin.ext_iff] at h' <;> omega⟩
        exact ⟨u, mem_erase.mpr ⟨hu, mem_univ _⟩⟩)
    (fun u hu => by simp [(mem_erase.mp hu).1])
    (by rw [Finset.sum_ite_eq']; simp only [mem_univ, if_true]; omega)
    (fun u => univ.filter fun x => ¬ NoWrap (Z3NetF.Mt Φ u a) x)
    (by
      calc ∑ u ∈ univ.erase a, (univ.filter fun x => ¬ NoWrap (Z3NetF.Mt Φ u a) x).card
          ≤ ∑ u ∈ univ.erase a, (Z3NetF.Mt Φ u a).natAbs :=
            Finset.sum_le_sum fun u _ => card_wrap_le _
        _ < q := by
          have : ((∑ u ∈ univ.erase a, (Z3NetF.Mt Φ u a).natAbs : ℕ) : ℤ) =
              ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| := by
            rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun u _ => Int.natCast_natAbs _
          omega)
  refine ⟨v, ?_, ?_, ?_⟩
  · have := hvA a 0 (by simp; omega)
    simpa using this
  · have := hvA a 1 (by simp; omega)
    simpa using this
  · intro u hu
    have := hvB u (mem_erase.mpr ⟨hu, mem_univ _⟩)
    simpa using this

/-- `gcd(det F₀, q) = 1`: the first offset digits `r = F₀ n` can be prescribed. -/
theorem cell_det (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (hdet : IsUnit (Matrix.of fun c d => (F₀ c d : ZMod q)).det) (r : Fin s → ZMod q) :
    ∃ v : Fin (s * 1) → ZMod q, ∀ c, dig (C1 Φ c) v 1 = r c := by
  classical
  set M : Matrix (Fin s) (Fin s) (ZMod q) := Matrix.of fun c d => (F₀ c d : ZMod q) with hM
  set n := M⁻¹ *ᵥ r with hn
  have hMn : M *ᵥ n = r := by
    rw [hn, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hs1 : ∀ i : Fin (s * 1), (i : ℕ) < s := fun i => by have := i.isLt; simpa using this
  refine ⟨fun i => n ⟨i, hs1 i⟩, fun c => ?_⟩
  have hr : 0 < s * 1 - 1 := by omega
  have h := dig_off Φ c (fun i => n ⟨i, hs1 i⟩) 0 hr
  rw [add_zero] at h
  rw [h, ← hMn]
  simp only [Matrix.mulVec, dotProduct, hM, Matrix.of_apply, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [h1 c d ⟨0, hr⟩ rfl]
  congr 2
  ext
  simp [Z3NetU.Proofs.ix]

/-! ## Assembly -/

lemma cres_shift (N : ℕ) (u z : ℤ) : Z3NetF.cres N (u + z * N) = Z3NetF.cres N u := by
  unfold Z3NetF.cres; rw [Int.add_mul_emod_self_right]

lemma unit_of_gcd (z : ℤ) (h : Int.gcd z q = 1) : IsUnit (z : ZMod q) := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · have hc : Nat.Coprime n q := by simpa [Int.gcd] using h
    simpa using (ZMod.isUnit_iff_coprime n q).2 hc
  · have hc : Nat.Coprime n q := by simpa [Int.gcd] using h
    simpa using ((ZMod.isUnit_iff_coprime n q).2 hc).neg

/-- The data of the step for a graph form with first offset rows `F₀` and (H2). -/
lemma ent_data (hs : 2 ≤ s) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : Z3NetF.H2 Φ) (a : Fin s) (hF : ∀ c d, 2 * |F₀ c d| < q) :
    (∀ c d, Z3NetF.ent (Φ c d) 0 0 = (F₀ c d : ZMod q)) ∧
    (∀ r, 1 ≤ r → Z3NetF.ent (Φ a a) r 0 = 0) ∧ ∀ u, Z3NetF.Mt Φ u a = F₀ u a := by
  have hr : 0 < s * 1 - 1 := by omega
  have he : ∀ c d, Z3NetF.ent (Φ c d) 0 0 = (F₀ c d : ZMod q) := by
    intro c d
    unfold Z3NetF.ent
    rw [dif_pos ⟨hr, by norm_num⟩]
    exact h1 c d ⟨0, hr⟩ rfl
  refine ⟨he, fun r hr1 => ?_, fun u => ?_⟩
  · unfold Z3NetF.ent
    split_ifs with h
    · exact h2 a ⟨r, h.1⟩ (by simp; omega) ⟨0, h.2⟩
    · rfl
  · unfold Z3NetF.Mt
    rw [show (1 - 1 : ℕ) = 0 from rfl, he]
    exact Z3NetU.Proofs.USharp.valMinAbs_eq q _ (hF u a)

/-- Integer form of the ceiling: two distinct indices with
`cres(X_v[a] - X_w[a]) ≤ q^(s-2) (q - K₁)` and `|X_v[u] - X_w[u]| < q^(s-2) (|F₀[u][a]| + 1)`
(`u ≠ a`); in the `(0,s,s)`-net case also `|X_v[a] - X_w[a]| = q^(s-2) (q - K₁)`. -/
theorem ceil_int (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : Z3NetF.H2 Φ) (a : Fin s) (K₁ : ℕ) (ha : F₀ a a = -(K₁ : ℤ))
    (hF : ∀ c d, 2 * |F₀ c d| < q)
    (hcase : Int.gcd (Matrix.of F₀).det q = 1 ∨
      (4 ≤ s ∧ Z3NetF.IsNet0 s q (s * 1) (Z3NetF.gfPoint q 1 Φ) ∧
        ∑ u ∈ univ.erase a, |F₀ u a| < q)) :
    ∃ v w : Fin (s * 1) → ZMod q, v ≠ w ∧
      (Z3NetF.cres (q ^ (s * 1)) ((Z3NetF.gfPoint q 1 Φ v a : ℤ) - Z3NetF.gfPoint q 1 Φ w a) : ℤ) ≤
        (q : ℤ) ^ (s * 1 - 1 - 1) * (q - K₁) ∧
      (∀ u, u ≠ a → |(Z3NetF.gfPoint q 1 Φ v u : ℤ) - Z3NetF.gfPoint q 1 Φ w u| <
        (q : ℤ) ^ (s * 1 - 1 - 1) * (|F₀ u a| + 1)) ∧
      (4 ≤ s ∧ Z3NetF.IsNet0 s q (s * 1) (Z3NetF.gfPoint q 1 Φ) ∧
          ∑ u ∈ univ.erase a, |F₀ u a| < q →
        |(Z3NetF.gfPoint q 1 Φ v a : ℤ) - Z3NetF.gfPoint q 1 Φ w a| =
          (q : ℤ) ^ (s * 1 - 1 - 1) * (q - K₁)) := by
  classical
  obtain ⟨he, hH2, hMt⟩ := ent_data hs F₀ Φ h1 h2 a hF
  have hKq : 2 * (K₁ : ℤ) < q := by have := hF a a; rw [ha, abs_neg] at this; simpa using this
  have hμ : Z3NetF.ent (Φ a a) 0 0 = -(K₁ : ZMod q) := by rw [he, ha]; push_cast; ring
  set G : ℤ := (q : ℤ) ^ (s * 1 - 1 - 1) with hG
  have hGpos : 0 < G := by positivity
  have hG1 : (q : ℤ) ^ (s * 1 - 1) = G * q := by rw [hG, ← pow_succ]; congr 1; omega
  have hG2 : (q : ℤ) ^ (s * 1) = G * q * q := by rw [← hG1, ← pow_succ]; congr 1; omega
  -- the transverse coordinates, for any good cell
  have trans : ∀ v : Fin (s * 1) → ZMod q, ∀ u, u ≠ a → ∀ Δ : ℤ, |Δ| < G →
      (Z3NetF.gfPoint q 1 Φ (v + stepA a) u : ℤ) - Z3NetF.gfPoint q 1 Φ v u = G * Z3NetF.Mt Φ u a + Δ →
      |(Z3NetF.gfPoint q 1 Φ v u : ℤ) - Z3NetF.gfPoint q 1 Φ (v + stepA a) u| < G * (|F₀ u a| + 1) := by
    intro v u hu Δ hΔ heq
    rw [hMt u] at heq
    rw [abs_sub_comm, heq]
    calc |G * F₀ u a + Δ| ≤ |G * F₀ u a| + |Δ| := abs_add_le _ _
      _ < G * |F₀ u a| + G := by rw [abs_mul, abs_of_pos hGpos]; linarith
      _ = G * (|F₀ u a| + 1) := by ring
  by_cases hnetc : 4 ≤ s ∧ Z3NetF.IsNet0 s q (s * 1) (Z3NetF.gfPoint q 1 Φ) ∧
      ∑ u ∈ univ.erase a, |F₀ u a| < q
  · obtain ⟨hs4, hnet, hcol⟩ := hnetc
    have hcol' : ∑ u ∈ univ.erase a, |Z3NetF.Mt Φ u a| < q := by
      rw [Finset.sum_congr rfl fun u _ => by rw [hMt u]]; exact hcol
    obtain ⟨v, hna, hra, hgood⟩ := cell_net hs4 hq Φ hnet a K₁ (by omega) hcol'
    obtain ⟨hvw, hXa, hXu⟩ := step_core hs (by omega) Φ a K₁ hμ hH2 v hra hgood
    have hcell : (((dig (C1 Φ a) v 0 + 1).val : ℤ) - (dig (C1 Φ a) v 0).val) = 1 := by
      have h := val_add_int (dig (C1 Φ a) v 0) 1
      push_cast at h
      have hlt : (dig (C1 Φ a) v 0).val + 1 < q := by
        have h1 := ZMod.val_lt (dig (C1 Φ a) v 0)
        by_contra hc
        apply hna
        apply ZMod.val_injective q
        rw [val_m1]; omega
      rw [h, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)]; ring
    rw [hcell, hG1] at hXa
    have hXa' : (Z3NetF.gfPoint q 1 Φ v a : ℤ) - Z3NetF.gfPoint q 1 Φ (v + stepA a) a =
        -(G * (q - K₁)) := by linear_combination -hXa
    refine ⟨v, v + stepA a, hvw, ?_, fun u hu => ?_, fun _ => ?_⟩
    · rw [hXa']
      refine (Z3NetF.Proofs.Deficit.cres_le_abs _ (by positivity) _).trans (le_of_eq ?_)
      rw [abs_neg, abs_of_nonneg (by nlinarith)]
    · obtain ⟨Δ, hΔ, heq⟩ := hXu u hu
      exact trans v u hu Δ hΔ heq
    · rw [hXa', abs_neg, abs_of_nonneg (by nlinarith)]
  · have hdet : Int.gcd (Matrix.of F₀).det q = 1 := hcase.resolve_right hnetc
    have hdetu : IsUnit (Matrix.of fun c d => (F₀ c d : ZMod q)).det := by
      have : (Matrix.of fun c d => (F₀ c d : ZMod q)) = (Int.castRingHom (ZMod q)).mapMatrix
          (Matrix.of F₀) := by ext; simp
      rw [this, ← RingHom.map_det]
      exact unit_of_gcd _ hdet
    set rs : Fin s → ZMod q := fun c => if c = a then -1 else if 0 ≤ F₀ c a then 0 else -1 with hrs
    obtain ⟨v, hv⟩ := cell_det hs hq F₀ Φ h1 hdetu rs
    have hra : K₁ ≤ (dig (C1 Φ a) v 1).val := by
      rw [hv a, hrs]; simp only [if_true]; rw [val_m1]; omega
    have hgood : ∀ u, u ≠ a → NoWrap (Z3NetF.Mt Φ u a) (dig (C1 Φ u) v 1) := by
      intro u hu
      rw [hv u, hMt u, noWrap_iff]
      have hFu := hF u a
      simp only [hrs, if_neg hu]
      split_ifs with h0
      · rw [ZMod.val_zero]; push_cast; constructor <;> [omega; (rw [abs_of_nonneg h0] at hFu; omega)]
      · rw [val_m1]; push_cast
        have : (q : ℤ) - 1 + 0 = q - 1 := by ring
        rw [abs_of_neg (not_le.mp h0)] at hFu
        constructor <;> omega
    obtain ⟨hvw, hXa, hXu⟩ := step_core hs (by omega) Φ a K₁ hμ hH2 v hra hgood
    have hcell : (((dig (C1 Φ a) v 0 + 1).val : ℤ) - (dig (C1 Φ a) v 0).val) = 1 ∨
        (((dig (C1 Φ a) v 0 + 1).val : ℤ) - (dig (C1 Φ a) v 0).val) = 1 - q := by
      have h := val_add_int (dig (C1 Φ a) v 0) 1
      push_cast at h
      have h1 := ZMod.val_lt (dig (C1 Φ a) v 0)
      rw [h]
      by_cases hlt : (dig (C1 Φ a) v 0).val + 1 < q
      · left; rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)]; ring
      · right
        have heq : ((dig (C1 Φ a) v 0).val : ℤ) + 1 = q := by omega
        rw [heq, Int.emod_self]; omega
    refine ⟨v, v + stepA a, hvw, ?_, fun u hu => ?_, fun h => absurd h hnetc⟩
    · rcases hcell with hc | hc
      · rw [hc, hG1] at hXa
        have hXa' : (Z3NetF.gfPoint q 1 Φ v a : ℤ) - Z3NetF.gfPoint q 1 Φ (v + stepA a) a =
            -(G * (q - K₁)) := by linear_combination -hXa
        rw [hXa']
        refine (Z3NetF.Proofs.Deficit.cres_le_abs _ (by positivity) _).trans (le_of_eq ?_)
        rw [abs_neg, abs_of_nonneg (by nlinarith)]
      · rw [hc, hG1] at hXa
        have hXa' : (Z3NetF.gfPoint q 1 Φ v a : ℤ) - Z3NetF.gfPoint q 1 Φ (v + stepA a) a =
            -(G * (q - K₁)) + 1 * ((q ^ (s * 1) : ℕ) : ℤ) := by
          push_cast; rw [hG2]; linear_combination -hXa
        rw [hXa', cres_shift]
        refine (Z3NetF.Proofs.Deficit.cres_le_abs _ (by positivity) _).trans (le_of_eq ?_)
        rw [abs_neg, abs_of_nonneg (by nlinarith)]
    · obtain ⟨Δ, hΔ, heq⟩ := hXu u hu
      exact trans v u hu Δ hΔ heq

/-- From the integer bounds to the normalized squared distance (`N^(1/s) = q`). -/
lemma real_bound (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ) (a : Fin s) (K₁ : ℕ)
    (hK : 2 * K₁ < q) (D : Fin s → ℝ)
    (hDa : |D a| ≤ (q : ℝ) ^ (s * 1 - 1 - 1) * ((q : ℝ) - K₁))
    (hDu : ∀ u, u ≠ a → |D u| < (q : ℝ) ^ (s * 1 - 1 - 1) * ((|F₀ u a| : ℝ) + 1)) :
    (q : ℝ) ^ 2 * ∑ c, (D c / (q : ℝ) ^ (s * 1)) ^ 2 <
      (1 - (K₁ : ℝ) / q) ^ 2 + ∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set G : ℝ := (q : ℝ) ^ (s * 1 - 1 - 1) with hG
  have hGpos : 0 < G := by positivity
  have hQ : (q : ℝ) ^ (s * 1) = G * q * q := by
    rw [hG, mul_assoc, ← sq, ← pow_add]; congr 1; omega
  have key : ∀ c, (q : ℝ) ^ 2 * (D c / (q : ℝ) ^ (s * 1)) ^ 2 = (D c / (G * q)) ^ 2 := by
    intro c; rw [hQ]; field_simp
  have hKq : (K₁ : ℝ) ≤ q := by exact_mod_cast (show K₁ ≤ q by omega)
  have hA : (D a / (G * q)) ^ 2 ≤ (1 - (K₁ : ℝ) / q) ^ 2 := by
    rw [show 1 - (K₁ : ℝ) / q = (G * ((q : ℝ) - K₁)) / (G * q) by field_simp, div_pow, div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← sq_abs (D a)]
    exact pow_le_pow_left₀ (abs_nonneg _) hDa 2
  have hU : ∀ u, u ≠ a → (D u / (G * q)) ^ 2 < (((|F₀ u a| : ℝ) + 1) / q) ^ 2 :=
    fun u hu => Z3NetA.Proofs.sq_lt_of_abs' hGpos hq0 (by positivity) (hDu u hu)
  rw [Finset.mul_sum, Finset.sum_congr rfl fun c _ => key c,
    ← Finset.add_sum_erase _ _ (mem_univ a)]
  have hne : (univ.erase a).Nonempty := by
    obtain ⟨u, hu⟩ : ∃ u : Fin s, u ≠ a :=
      ⟨if (a : ℕ) = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
        split_ifs with h <;> intro h' <;> simp [Fin.ext_iff] at h' <;> omega⟩
    exact ⟨u, mem_erase.mpr ⟨hu, mem_univ _⟩⟩
  have hlt := Finset.sum_lt_sum_of_nonempty hne fun u hu => hU u (mem_erase.mp hu).1
  have hcongr : ∑ u ∈ univ.erase a, (((|F₀ u a| : ℝ) + 1) / q) ^ 2 =
      ∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 :=
    Finset.sum_congr rfl fun u _ => div_pow _ _ _
  linarith

/-- **`prop:k1`(3)**, toroidal (both cases). -/
theorem k1_ceil_core (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : Z3NetF.H2 Φ) (a : Fin s) (K₁ : ℕ) (ha : F₀ a a = -(K₁ : ℤ))
    (hF : ∀ c d, 2 * |F₀ c d| < q)
    (hcase : Int.gcd (Matrix.of F₀).det q = 1 ∨
      (4 ≤ s ∧ Z3NetF.IsNet0 s q (s * 1) (Z3NetF.gfPoint q 1 Φ) ∧
        ∑ u ∈ univ.erase a, |F₀ u a| < q)) :
    ∃ v w : Fin (s * 1) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ 2 * ∑ c, ((Z3NetF.cres (q ^ (s * 1)) ((Z3NetF.gfPoint q 1 Φ v c : ℤ) -
          (Z3NetF.gfPoint q 1 Φ w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * 1)) ^ 2 <
        (1 - (K₁ : ℝ) / q) ^ 2 + ∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  obtain ⟨v, w, hvw, hA, hU, -⟩ := ceil_int hs hq F₀ Φ h1 h2 a K₁ ha hF hcase
  have hK : 2 * K₁ < q := by
    have := hF a a; rw [ha, abs_neg, Nat.abs_cast] at this; omega
  refine ⟨v, w, hvw, real_bound hs hq F₀ a K₁ hK _ ?_ fun u hu => ?_⟩
  · rw [abs_of_nonneg (by positivity)]
    have : ((Z3NetF.cres (q ^ (s * 1)) ((Z3NetF.gfPoint q 1 Φ v a : ℤ) -
        (Z3NetF.gfPoint q 1 Φ w a : ℤ)) : ℤ) : ℝ) ≤ (((q : ℤ) ^ (s * 1 - 1 - 1) * (q - K₁) : ℤ) : ℝ) := by
      exact_mod_cast hA
    push_cast at this
    exact this
  · rw [abs_of_nonneg (by positivity)]
    have h0 := Z3NetF.Proofs.Deficit.cres_le_abs (q ^ (s * 1)) (by positivity)
      ((Z3NetF.gfPoint q 1 Φ v u : ℤ) - (Z3NetF.gfPoint q 1 Φ w u : ℤ))
    have h1' := (h0.trans_lt (hU u hu))
    have : ((Z3NetF.cres (q ^ (s * 1)) ((Z3NetF.gfPoint q 1 Φ v u : ℤ) -
        (Z3NetF.gfPoint q 1 Φ w u : ℤ)) : ℤ) : ℝ) < (((q : ℤ) ^ (s * 1 - 1 - 1) * (|F₀ u a| + 1) : ℤ) : ℝ) := by
      exact_mod_cast h1'
    push_cast at this
    exact this

/-- **`prop:k1`(3)**, the `(0,s,s)`-net case, Euclidean. -/
theorem k1_ceil_eucl_core (hs : 4 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : Z3NetF.H2 Φ) (a : Fin s) (K₁ : ℕ) (ha : F₀ a a = -(K₁ : ℤ))
    (hF : ∀ c d, 2 * |F₀ c d| < q) (hnet : Z3NetF.IsNet0 s q (s * 1) (Z3NetF.gfPoint q 1 Φ))
    (hcol : ∑ u ∈ univ.erase a, |F₀ u a| < q) :
    ∃ v w : Fin (s * 1) → ZMod q, v ≠ w ∧
      (q : ℝ) ^ 2 * ∑ c, (((Z3NetF.gfPoint q 1 Φ v c : ℝ) - Z3NetF.gfPoint q 1 Φ w c) /
          (q : ℝ) ^ (s * 1)) ^ 2 <
        (1 - (K₁ : ℝ) / q) ^ 2 + ∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 := by
  obtain ⟨v, w, hvw, -, hU, hA⟩ := ceil_int (by omega) hq F₀ Φ h1 h2 a K₁ ha hF
    (Or.inr ⟨hs, hnet, hcol⟩)
  have hK : 2 * K₁ < q := by
    have := hF a a; rw [ha, abs_neg, Nat.abs_cast] at this; omega
  refine ⟨v, w, hvw, real_bound (by omega) hq F₀ a K₁ hK _ ?_ fun u hu => ?_⟩
  · have := hA ⟨hs, hnet, hcol⟩
    have h' : |(((Z3NetF.gfPoint q 1 Φ v a : ℤ) - Z3NetF.gfPoint q 1 Φ w a : ℤ) : ℝ)| =
        (((q : ℤ) ^ (s * 1 - 1 - 1) * (q - K₁) : ℤ) : ℝ) := by
      rw [← Int.cast_abs, this]
    push_cast at h'
    exact le_of_eq h'
  · have h' : |(((Z3NetF.gfPoint q 1 Φ v u : ℤ) - Z3NetF.gfPoint q 1 Φ w u : ℤ) : ℝ)| <
        (((q : ℤ) ^ (s * 1 - 1 - 1) * (|F₀ u a| + 1) : ℤ) : ℝ) := by
      rw [← Int.cast_abs]; exact_mod_cast hU u hu
    push_cast at h'
    exact h'

/-- **`prop:k1`(3)**, real form (toroidal, both cases): `δ N^(1/s) < 1 - K₁/q + C/q²`,
`C = ∑_{u ≠ a} (|F₀[u][a]| + 1)²`; with `prop:k1`(1), `δ N^(1/s) = 1 - K₁/q + O(q⁻²)`. -/
theorem k1_ceil_real_core (hs : 2 ≤ s) (hq : 3 ≤ q) (F₀ : Fin s → Fin s → ℤ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * 1 - 1)) (Fin 1) (ZMod q))
    (h1 : ∀ c d (r : Fin (s * 1 - 1)), (r : ℕ) = 0 → Φ c d r 0 = (F₀ c d : ZMod q))
    (h2 : Z3NetF.H2 Φ) (a : Fin s) (K₁ : ℕ) (ha : F₀ a a = -(K₁ : ℤ))
    (hF : ∀ c d, 2 * |F₀ c d| < q)
    (hcase : Int.gcd (Matrix.of F₀).det q = 1 ∨
      (4 ≤ s ∧ Z3NetF.IsNet0 s q (s * 1) (Z3NetF.gfPoint q 1 Φ) ∧
        ∑ u ∈ univ.erase a, |F₀ u a| < q)) :
    ∃ v w : Fin (s * 1) → ZMod q, v ≠ w ∧
      Real.sqrt (∑ c, ((Z3NetF.cres (q ^ (s * 1)) ((Z3NetF.gfPoint q 1 Φ v c : ℤ) -
          (Z3NetF.gfPoint q 1 Φ w c : ℤ)) : ℝ) / (q : ℝ) ^ (s * 1)) ^ 2) <
        (1 - (K₁ : ℝ) / q + (∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2) / (q : ℝ) ^ 2) *
          ((q : ℝ) ^ (s * 1)) ^ (-(1 / (s : ℝ))) := by
  obtain ⟨v, w, hvw, h⟩ := k1_ceil_core hs hq F₀ Φ h1 h2 a K₁ ha hF hcase
  refine ⟨v, w, hvw, ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hK : 2 * K₁ < q := by
    have := hF a a; rw [ha, abs_neg, Nat.abs_cast] at this; omega
  rw [Z3NetA.Proofs.rpow_N s q 1 (by omega) (by omega), pow_one]
  set α : ℝ := 1 - (K₁ : ℝ) / q
  set β : ℝ := (∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2) / (q : ℝ) ^ 2
  have hα : (1 : ℝ) / 2 ≤ α := by
    have : (2 * K₁ : ℝ) < q := by exact_mod_cast hK
    have : (K₁ : ℝ) / q ≤ 1 / 2 := by rw [div_le_iff₀ hq0]; linarith
    simp only [α]; linarith
  have hβ : 0 ≤ β := by positivity
  have hβ' : ∑ u ∈ univ.erase a, ((|F₀ u a| : ℝ) + 1) ^ 2 / (q : ℝ) ^ 2 = β := by
    simp only [β]; rw [Finset.sum_div]
  rw [hβ'] at h
  have hsq : α ^ 2 + β ≤ (α + β) ^ 2 := by nlinarith
  rw [Real.sqrt_lt' (by positivity), mul_one_div, div_pow, lt_div_iff₀ (by positivity)]
  nlinarith

end

end Z3NetF.Proofs.K1Ceil

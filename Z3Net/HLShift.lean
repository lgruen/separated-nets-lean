/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.HLGF
public import Z3Net.FSepShift2

@[expose] public section

/-!
# V14 stage S10′: the carry relaxation of `prop:Hk` under digital shifts (`prop:shift`)

The relaxation `relaxG` (`Z3Net/HLGF.lean`) for a graph form `Φ` (depths `(k, …, k)`) with an
additive constant `γ` on the offset digits (`γ` vanishing on the cell digits): the digits of
coordinate `c` of the point with index `x` are `G_c x + γ_c` (`DgGA`). The cell digits are those of the
unshifted form (`cellGA_part`), and the change of the first offset digit under a step is that of the
unshifted form (`DgGA_off_sub`: `γ` cancels); the rest of the proof (cells, carries, far steps) is about
the index and is unchanged (`relaxGA`). By `lem:shift` (`digPointShift_reindex`, re-indexing by the
cells `x ↦ x + TcK τ`, constant `gammaK Φ τ`, `Z3Net/FSepShift2.lean`) every digital shift of the net
`GFpoint s q k Φ = digPoint q (sk) (graphGen s k Φ)` is such an affine form (`shiftHL_affine`), so the
relaxation holds verbatim for every digitally shifted net (`relaxG_shift`). Generator family:
`Z3NetHL.graphGen s k Φ` (`GFpoint_shift_zero`: `τ = 0` gives `GFpoint`).
-/

namespace Z3NetHL.Proofs

open Finset Matrix

noncomputable section

open Z3NetU.Proofs (ix ix_surj sk_sub_add graphGen_cell graphGen_off)

/-- Bridge: `GFpoint` is the digital point set of the generator family `graphGen s k Φ`, i.e. the
digital shift `τ = 0` of it. -/
theorem GFpoint_shift_zero (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q)) :
    GFpoint s q k Φ = Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) 0 := by
  funext x c
  simp [GFpoint, Z3NetF.digPointShift, Z3NetHL.digPoint, Z3NetHL.coord]

/-- Bridge: `HLpoint` is the digital point set of the generator family `HLGen`, i.e. the digital
shift `τ = 0` of it. -/
theorem HLpoint_shift_zero (s q k : ℕ) (u v : Fin s → ℤ) (lam : Fin s → ℚ) (gco : Fin s → ℕ → ℕ → ℚ)
    (dg : Fin s → ℕ → ℚ) :
    HLpoint s q k u v lam gco dg = Z3NetF.digPointShift q (s * k) (HLGen s q k u v lam gco dg) 0 := by
  funext x c
  simp [HLpoint, Z3NetF.digPointShift, Z3NetHL.digPoint, Z3NetHL.coord]

section aff

variable (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
  (γ : Fin s → Fin (s * k) → ZMod q)

/-- Digit vector of coordinate `c` of the affine graph-form point with index `x`. -/
def DgGA (c : Fin s) (x : Fin (s * k) → ZMod q) : Fin (s * k) → ZMod q :=
  Z3NetHL.graphGen s k Φ c *ᵥ x + γ c

lemma GFpointA_eq (x : Fin (s * k) → ZMod q) (c : Fin s) :
    Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) γ x c =
      ∑ j : Fin (s * k), (DgGA s q k Φ γ c x j).val * q ^ (s * k - 1 - (j : ℕ)) := rfl

variable [NeZero q]

lemma cellGA_part (hγ : ∀ c (i : Fin (s * k)), (i : ℕ) < k → γ c i = 0) (x : Fin (s * k) → ZMod q)
    (c : Fin s) :
    ∑ i ∈ range k, dv s q k (DgGA s q k Φ γ c x) i * q ^ (k - 1 - i) = cellN s q k x c := by
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  congr 1
  have hik : i < s * k := lt_of_lt_of_le hi (k_le_sk' k c)
  simp only [dv, ad, dif_pos hi, dif_pos hik, DgGA]
  rw [Pi.add_apply, hγ c ⟨i, hik⟩ hi, add_zero]
  exact congrArg ZMod.val (graphGen_cell k Φ c x i hi)

/-- First offset digit and tail of coordinate `c`. -/
def o0GA (x : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := dv s q k (DgGA s q k Φ γ c x) k
def tlGA (x : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := tail s q k (DgGA s q k Φ γ c x)

lemma XGA_decomp (hγ : ∀ c (i : Fin (s * k)), (i : ℕ) < k → γ c i = 0) (hsk : k + 1 ≤ s * k)
    (x : Fin (s * k) → ZMod q) (c : Fin s) :
    (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) γ x c : ℤ) =
      (q : ℤ) ^ (s * k - k) * cellN s q k x c +
      (q : ℤ) ^ (s * k - k - 1) * o0GA s q k Φ γ x c + tlGA s q k Φ γ x c := by
  rw [GFpointA_eq, coord_split s q k hsk, cellGA_part s q k Φ γ hγ]
  push_cast
  simp only [o0GA, tlGA]

lemma o0GA_cast (x : Fin (s * k) → ZMod q) (c : Fin s) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) :
    ((o0GA s q k Φ γ x c : ℕ) : ZMod q) = DgGA s q k Φ γ c x ⟨k + r, sk_sub_add r⟩ := by
  have hk : k < s * k := by have := sk_sub_add r; omega
  simp only [o0GA, dv, dif_pos hk, ZMod.natCast_zmod_val, hr, add_zero]

lemma oGA_bound (x y : Fin (s * k) → ZMod q) (c : Fin s) :
    |(o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c| < q := by
  have h1 := dv_lt s q k (DgGA s q k Φ γ c x) k
  have h2 := dv_lt s q k (DgGA s q k Φ γ c y) k
  simp only [o0GA]
  rw [abs_lt]; constructor <;> omega

lemma tlGA_lt (hsk : k + 1 ≤ s * k) (x : Fin (s * k) → ZMod q) (c : Fin s) :
    tlGA s q k Φ γ x c < q ^ (s * k - k - 1) := tail_lt s q k hsk _

/-- Change of the first offset digit, doubled: the constant `γ` cancels. -/
lemma DgGA_off_sub (hs : 2 ≤ s) (F2 : ℕ → Fin s → Fin s → ℤ) (hrow : RowDesign s q k Φ F2)
    (c : Fin s) (x y : Fin (s * k) → ZMod q) (E : Fin s → ℤ) (J : Fin s → ℕ)
    (hJk : ∀ d, J d < k) (hJs : ∀ d, J d ≤ s - 2)
    (hstep : ∀ d, AxisStep2 s q k x y d (E d) (J d)) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) :
    2 * (DgGA s q k Φ γ c y ⟨k + r, sk_sub_add r⟩ - DgGA s q k Φ γ c x ⟨k + r, sk_sub_add r⟩) =
      (sig2 F2 E J c : ZMod q) := by
  simp only [DgGA, Pi.add_apply, add_sub_add_right_eq_sub]
  exact DgG_off_sub s q k Φ hs F2 hrow c x y E J hJk hJs hstep r hr

/-- **Prop H_k(a) for an affine graph form** (the constant `γ` vanishes on the cell digits). -/
theorem relaxGA (hγ : ∀ c (i : Fin (s * k)), (i : ℕ) < k → γ c i = 0) (hs : 2 ≤ s) (hq7 : 7 ≤ q) (F2 : ℕ → Fin s → Fin s → ℤ)
    (hrow : RowDesign s q k Φ F2) (hk : 1 ≤ k)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤ ∑ c : Fin s,
        ((Z3NetU.cres (q ^ (s * k)) ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) γ x c : ℤ) -
          (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) γ y c : ℤ)) : ℕ) : ℤ) ^ 2 ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          ∑ c : Fin s, ((Z3NetU.cres (q ^ (s * k)) ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) γ x c : ℤ) -
            (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) γ y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  have hq1 : 1 < q := by omega
  have h2k : 2 * k ≤ s * k := Nat.mul_le_mul_right k hs
  have hsk : k + 1 ≤ s * k := by omega
  have hM1 : 1 ≤ (s * k - k) := by omega
  set U : ℤ := (q : ℤ) ^ ((s * k - k) - 1) with hU_def
  have hU : 0 < U := by positivity
  have hpow : (q : ℤ) ^ (s * k - k) = U * q := by rw [hU_def, ← pow_succ]; congr 1; omega
  have hN : ((q ^ (s * k) : ℕ) : ℤ) = (q : ℤ) ^ (s * k - k) * (q : ℤ) ^ k := by
    push_cast; rw [← pow_add]; congr 1; omega
  set X := Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) γ with hXdef
  have hX : ∀ c, (X x c : ℤ) - X y c =
      (q : ℤ) ^ (s * k - k) * ((cellN s q k x c : ℤ) - cellN s q k y c) +
      (U * ((o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c) +
        ((tlGA s q k Φ γ x c : ℤ) - tlGA s q k Φ γ y c)) := by
    intro c; rw [hXdef, XGA_decomp s q k Φ γ hγ hsk, XGA_decomp s q k Φ γ hγ hsk]; ring
  have htl : ∀ c, |(tlGA s q k Φ γ x c : ℤ) - tlGA s q k Φ γ y c| < U := by
    intro c
    have h1 := tlGA_lt s q k Φ γ hsk x c
    have h2 := tlGA_lt s q k Φ γ hsk y c
    have h1' : ((tlGA s q k Φ γ x c : ℕ) : ℤ) < U := by rw [hU_def]; exact_mod_cast h1
    have h2' : ((tlGA s q k Φ γ y c : ℕ) : ℤ) < U := by rw [hU_def]; exact_mod_cast h2
    rw [abs_lt]; constructor <;> omega
  have hsum_nonneg : ∀ c ∈ (univ : Finset (Fin s)), (0 : ℤ) ≤
      ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 :=
    fun c _ => sq_nonneg _
  by_cases hfar : ∃ c, Far3 s q k y x c
  · left
    obtain ⟨c, hc⟩ := hfar
    have ho0 := oGA_bound s q k Φ γ x y c
    have hR : |U * ((o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c) +
        ((tlGA s q k Φ γ x c : ℤ) - tlGA s q k Φ γ y c)| < (q : ℤ) ^ (s * k - k) := by
      have a2 := abs_add_le (U * ((o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c))
        ((tlGA s q k Φ γ x c : ℤ) - tlGA s q k Φ γ y c)
      rw [abs_mul, abs_of_pos hU] at a2
      have := htl c
      have b1 : |(o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c| ≤ q - 1 := by omega
      rw [hpow]; nlinarith
    have hf := far_gen3 (q ^ (s * k)) ((q : ℤ) ^ (s * k - k)) ((q : ℤ) ^ k) (by positivity) (by positivity)
      hN _ _ hR hc
    rw [← hX c] at hf
    have hsq : (2 * (q : ℤ) ^ (s * k - k)) ^ 2 ≤
        ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hf 2
    have hsingle := Finset.single_le_sum hsum_nonneg (mem_univ c)
    calc 4 * (q : ℤ) ^ (2 * (s * k - k)) = (2 * (q : ℤ) ^ (s * k - k)) ^ 2 := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ _ := hsq.trans hsingle
  · right
    push_neg at hfar
    choose E J hE hJs hJk hstep hz hE0 using fun c => axis_classify2 s q k hq7 hk y x c (hfar c)
    have hne : ∃ c, E c ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hxy (eq_of_cellN' s q k hq1 y x (fun d => hE0 d (hall d)))
    refine ⟨E, J, fun c => (o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c,
      hE, hne, fun c => lt_min (hJk c) (by have := hJs c; omega), ?_,
      fun c => oGA_bound s q k Φ γ x y c, ?_⟩
    · intro c
      have h := DgGA_off_sub s q k Φ γ hs F2 hrow c y x E J hJk hJs hstep ⟨0, by omega⟩ rfl
      rw [← o0GA_cast s q k Φ γ x c ⟨0, by omega⟩ rfl,
        ← o0GA_cast s q k Φ γ y c ⟨0, by omega⟩ rfl] at h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h]; ring
    · set V : Fin s → ℤ := fun c => (q : ℤ) * E c +
        ((o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c) with hV
      have hVb : ∀ c, |V c| ≤ 3 * (q : ℤ) - 1 := by
        intro c
        have ho := oGA_bound s q k Φ γ x y c
        have b1 : |(o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c| ≤ q - 1 := by omega
        have b0 : |E c| ≤ 2 := hE c
        have := abs_add_le ((q : ℤ) * E c) ((o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c)
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < q)] at this
        simp only [hV]
        nlinarith
      have hXV : ∀ c, ∃ z : ℤ, (X x c : ℤ) - X y c =
          U * V c + ((tlGA s q k Φ γ x c : ℤ) - tlGA s q k Φ γ y c) +
            z * ((q ^ (s * k) : ℕ) : ℤ) := by
        intro c
        obtain ⟨z, hzc⟩ := hz c
        refine ⟨z, ?_⟩
        rw [hX c, hzc, hN, hpow]; simp only [hV]; ring
      have hqk : (7 : ℤ) ≤ (q : ℤ) ^ k := by
        calc (7 : ℤ) ≤ q := by exact_mod_cast hq7
          _ = (q : ℤ) ^ 1 := (pow_one _).symm
          _ ≤ (q : ℤ) ^ k := pow_le_pow_right₀ (by omega) hk
      set xc : Fin s → ℤ := fun c =>
        ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) / U with hxc_def
      have hnear : ∀ c, 0 ≤ xc c ∧ |V c| - 1 ≤ xc c ∧
          U * xc c ≤ ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) := by
        intro c
        obtain ⟨z, hzc⟩ := hXV c
        simp only [hxc_def]
        rw [hzc]
        have := Z3NetU.Proofs.near_gen (q ^ (s * k)) U (V c) _ z hU (htl c) (by
          rw [hN, hpow]
          have := abs_add_le (U * V c) ((tlGA s q k Φ γ x c : ℤ) - tlGA s q k Φ γ y c)
          rw [abs_mul, abs_of_pos hU] at this
          have := hVb c; have := htl c
          have h7 : 7 * (U * q) ≤ U * q * (q : ℤ) ^ k := by
            have : 0 < U * q := by positivity
            nlinarith
          nlinarith)
        exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hsq : ∀ c, (U * max 0 (|V c| - 1)) ^ 2 ≤
          ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
        intro c
        obtain ⟨h1, h2, h3⟩ := hnear c
        have hm : max 0 (|V c| - 1) ≤ xc c := max_le h1 h2
        have hm0 : 0 ≤ max 0 (|V c| - 1) := le_max_left _ _
        exact pow_le_pow_left₀ (mul_nonneg hU.le hm0) ((mul_le_mul_of_nonneg_left hm hU.le).trans h3) 2
      have hU2 : (q : ℤ) ^ (2 * ((s * k - k) - 1)) = U ^ 2 := by rw [hU_def, ← pow_mul]; ring_nf
      calc (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c +
            ((o0GA s q k Φ γ x c : ℤ) - o0GA s q k Φ γ y c)| - 1)) ^ 2
          = ∑ c, (U * max 0 (|V c| - 1)) ^ 2 := by
            rw [hU2, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by simp only [hV]; ring
        _ ≤ _ := Finset.sum_le_sum fun c _ => hsq c

end aff

/-! ## `lem:shift` for the graph form and the shifted relaxation -/

/-- **`lem:shift`** (depths `(k, …, k)`): the shifted net is the affine graph form with the constant
`gammaK Φ τ`, re-indexed by `x ↦ x + TcK τ`. -/
lemma shiftHL_affine {s q k : ℕ} [NeZero q] (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (τ : Fin s → Fin (s * k) → ZMod q) (x : Fin (s * k) → ZMod q) :
    Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x =
      Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) (Z3NetF.Proofs.gammaK Φ τ)
        (x + Z3NetF.Proofs.TcK τ) := by
  rw [Z3NetF.Proofs.digPointShift_reindex _ τ (Z3NetF.Proofs.TcK τ) x]
  rfl

/-- The carry relaxation (Prop H_k(a), `relaxG`) for every digitally shifted graph-form net. -/
theorem relaxG_shift (s q k : ℕ) [NeZero q] (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
    (hs : 2 ≤ s) (hq7 : 7 ≤ q) (F2 : ℕ → Fin s → Fin s → ℤ)
    (hrow : RowDesign s q k Φ F2) (hk : 1 ≤ k) (τ : Fin s → Fin (s * k) → ZMod q)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤ ∑ c : Fin s,
        ((Z3NetU.cres (q ^ (s * k)) ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x c : ℤ) -
          (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ y c : ℤ)) : ℕ) : ℤ) ^ 2 ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          ∑ c : Fin s, ((Z3NetU.cres (q ^ (s * k))
            ((Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ x c : ℤ) -
            (Z3NetF.digPointShift q (s * k) (Z3NetHL.graphGen s k Φ) τ y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  rw [shiftHL_affine Φ τ x, shiftHL_affine Φ τ y]
  exact relaxGA s q k Φ (Z3NetF.Proofs.gammaK Φ τ) (Z3NetF.Proofs.gammaK_cell Φ τ) hs hq7 F2 hrow hk
    (x + Z3NetF.Proofs.TcK τ) (y + Z3NetF.Proofs.TcK τ) (fun h => hxy (add_right_cancel h))

end

end Z3NetHL.Proofs

/-
`rem:accounting` (first-order accounting), the lower bound for `K_eff`: an explicit pair of points of the net, of the
manuscript *Low-discrepancy quasi-uniform digital nets in every dimension* (`paper/core.tex`). V14 stage S13′.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.AcctUp

@[expose] public section

/-!
# V14 stage S13′: `rem:accounting`, the explicit pair (`liminf K_eff ≥ dr`)

The second half of the printed proof. Fix a binding step `E` with `dr(E) = dr(F₀)`. For an index `w ∈ 𝔽_p⁵` let
`r = F₀ w` (first offset digits, `½ ≡ (p+1)/2`) and `d = D₁ w` (second offset digits). The pair `w`, `w + E` has, in
coordinate `c`, the first-digit change `Δr_c = (p s_c + 2β_c)/2 − p E_c` (the shorter option) as soon as
`r_c + Δr_c ∈ [0, p)`, and the second-digit change `v_c` as soon as `d_c + v_c ∈ [0, p)` (`val_add_int`). Then
`p⁴ E_c + p³ Δr_c = p³ (p s_c + 2β_c)/2` has absolute value `p³ (p − 2dr_c(E))/2`, and the toroidal distance
satisfies `(δN^{1/5})² ≤ 5/4 − 2dr(E)/(2p) + C/p²` (`pair_bound`).

Existence of such `w` (`exists_good`): `w ↦ F₀ w` is a bijection of `𝔽_p⁵` when `p ∤ det 2F₀`, so the `w` whose first
digits all lie in the good ranges number `∏_c (p − |Δr_c|) ≥ (p/4)⁵`; the second-digit condition fails on at most
`|v_c| p⁴` indices for each `c` (`card_fiber_le`: `d_c` is a nonzero linear form once `p` exceeds the entries of
`D₁`). (The printed proof asks for a box of `(p/2 − O(1))⁵` cells; any positive fraction suffices.)
-/

namespace Z3NetHL.Proofs.Acct

open Finset Matrix Z3NetHL Z3NetHL.Proofs

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## Counting -/

/-- A nonzero linear form takes values in `S` on at most `|S| p⁴` points of `𝔽_p⁵`. -/
lemma card_fiber_le (p : ℕ) [Fact p.Prime] (a : Fin 5 → ZMod p) (d0 : Fin 5) (ha : a d0 ≠ 0)
    (S : Finset (ZMod p)) :
    (univ.filter fun w : Fin 5 → ZMod p => (∑ d, a d * w d) ∈ S).card ≤ S.card * p ^ 4 := by
  have hT : (S ×ˢ (univ : Finset ({j : Fin 5 // j ≠ d0} → ZMod p))).card = S.card * p ^ 4 := by
    rw [card_product, card_univ, Fintype.card_fun, ZMod.card]
    congr 2
    simp
  rw [← hT]
  refine card_le_card_of_injOn (fun w => ((∑ d, a d * w d), fun j => w j.1)) ?_ ?_
  · intro w hw
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw
    simp only [coe_product, coe_univ, Set.mem_prod, mem_coe, Set.mem_univ, and_true]
    exact hw
  · intro w _ w' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hj : ∀ j, j ≠ d0 → w j = w' j := fun j hj => congrFun h2 ⟨j, hj⟩
    have hR : ∑ d ∈ univ.erase d0, a d * w d = ∑ d ∈ univ.erase d0, a d * w' d :=
      Finset.sum_congr rfl fun d hd => by rw [hj d (Finset.ne_of_mem_erase hd)]
    rw [← Finset.add_sum_erase _ _ (mem_univ d0), ← Finset.add_sum_erase _ _ (mem_univ d0), hR] at h1
    have h00 : w d0 = w' d0 := mul_left_cancel₀ ha (add_right_cancel h1)
    funext j
    by_cases hjd : j = d0
    · subst hjd; exact h00
    · exact hj j hjd

lemma card_good_res (p : ℕ) [NeZero p] (β : ℤ) :
    p ≤ (univ.filter fun r : ZMod p => 0 ≤ (r.val : ℤ) + β ∧ (r.val : ℤ) + β < p).card + β.natAbs := by
  have h1 := card_bad_res p β
  have h2 := card_filter_add_card_filter_not (s := (univ : Finset (ZMod p)))
    (fun r : ZMod p => 0 ≤ (r.val : ℤ) + β ∧ (r.val : ℤ) + β < p)
  rw [card_univ, ZMod.card] at h2
  omega

/-- **Existence of a good index**: for an invertible `M` over `𝔽_p`, shifts `β_c` with `4|β_c| ≤ 3p`, linear forms
`L_c` that are nonzero whenever `v_c ≠ 0`, and `4⁵ (∑_c |v_c|) p⁴ < p⁵`, some `w` has
`(M w)_c + β_c ∈ [0, p)` and `(L_c w) + v_c ∈ [0, p)` (as integers, via `val`) for every `c`. -/
lemma exists_good_w (p : ℕ) [Fact p.Prime] (M : Matrix (Fin 5) (Fin 5) (ZMod p)) (hM : M.det ≠ 0)
    (β v : Fin 5 → ℤ) (L : Fin 5 → Fin 5 → ZMod p) (hL : ∀ c, v c ≠ 0 → ∃ d, L c d ≠ 0)
    (hβ : ∀ c, 4 * |β c| ≤ 3 * p) (hcount : 4 ^ 5 * (∑ c, (v c).natAbs) * p ^ 4 < p ^ 5) :
    ∃ w : Fin 5 → ZMod p, (∀ c, 0 ≤ (((M *ᵥ w) c).val : ℤ) + β c ∧ (((M *ᵥ w) c).val : ℤ) + β c < p) ∧
      (∀ c, 0 ≤ (((∑ d, L c d * w d) : ZMod p).val : ℤ) + v c ∧
        (((∑ d, L c d * w d) : ZMod p).val : ℤ) + v c < p) := by
  set G : Fin 5 → Finset (ZMod p) := fun c =>
    univ.filter fun r : ZMod p => 0 ≤ (r.val : ℤ) + β c ∧ (r.val : ℤ) + β c < p with hG
  set Box := Fintype.piFinset G with hBox
  set Good := univ.filter fun w : Fin 5 → ZMod p => M *ᵥ w ∈ Box with hGood
  set Bad : Fin 5 → Finset (Fin 5 → ZMod p) := fun c => univ.filter fun w : Fin 5 → ZMod p =>
    ¬ (0 ≤ (((∑ d, L c d * w d) : ZMod p).val : ℤ) + v c ∧ (((∑ d, L c d * w d) : ZMod p).val : ℤ) + v c < p)
    with hBad
  -- the box
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det M).mpr (IsUnit.mk0 _ hM))
  have hsurj : Function.Surjective M.mulVec := Finite.injective_iff_surjective.mp hinj
  have hGoodBox : Good.card = Box.card := by
    rw [← card_image_of_injective Good hinj]
    congr 1
    ext b
    simp only [mem_image, hGood, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hb; obtain ⟨w, rfl⟩ := hsurj b; exact ⟨w, hb, rfl⟩
  have hBox4 : p ^ 5 ≤ 4 ^ 5 * Box.card := by
    rw [hBox, Fintype.card_piFinset]
    have hc : ∀ c, p ≤ 4 * (G c).card := by
      intro c
      have h1 := card_good_res p (β c)
      have h2 := hβ c
      have : ((β c).natAbs : ℤ) = |β c| := Int.natCast_natAbs (β c)
      have h1' : (p : ℤ) ≤ ((G c).card : ℤ) + |β c| := by
        rw [← this]; exact_mod_cast h1
      have : (p : ℤ) ≤ 4 * ((G c).card : ℤ) := by linarith
      exact_mod_cast this
    calc p ^ 5 = ∏ _c : Fin 5, p := by simp
      _ ≤ ∏ c : Fin 5, 4 * (G c).card := Finset.prod_le_prod fun c _ => hc c
      _ = 4 ^ 5 * ∏ c, (G c).card := by rw [Finset.prod_mul_distrib]; simp
  -- the bad sets
  have hBadc : ∀ c, (Bad c).card ≤ (v c).natAbs * p ^ 4 := by
    intro c
    by_cases hv : v c = 0
    · have : Bad c = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        simp only [hBad, mem_filter, mem_univ, true_and, hv, add_zero] at hw
        exact hw ⟨by positivity, by exact_mod_cast ZMod.val_lt _⟩
      rw [this]; simp
    · obtain ⟨d0, hd0⟩ := hL c hv
      have hsub : Bad c ⊆ univ.filter fun w : Fin 5 → ZMod p => (∑ d, L c d * w d) ∈
          univ.filter (fun r : ZMod p => ¬ (0 ≤ (r.val : ℤ) + v c ∧ (r.val : ℤ) + v c < p)) := by
        intro w hw
        simp only [hBad, mem_filter, mem_univ, true_and] at hw ⊢
        exact hw
      refine (card_le_card hsub).trans ((card_fiber_le p (L c) d0 hd0 _).trans ?_)
      exact Nat.mul_le_mul_right _ (card_bad_res p (v c))
  -- conclusion
  by_contra hno
  have hcov : Good ⊆ univ.biUnion Bad := by
    intro w hw
    simp only [hGood, mem_filter, mem_univ, true_and, hBox, Fintype.mem_piFinset, hG] at hw
    simp only [mem_biUnion, mem_univ, true_and, hBad, mem_filter]
    by_contra hall
    push Not at hall
    exact hno ⟨w, hw, hall⟩
  have h1 := card_le_card hcov
  have h2 := card_biUnion_le (s := univ) (t := Bad)
  have h3 : ∑ c, (Bad c).card ≤ ∑ c, (v c).natAbs * p ^ 4 := Finset.sum_le_sum fun c _ => hBadc c
  rw [← Finset.sum_mul] at h3
  have h4 : 4 ^ 5 * Good.card ≤ 4 ^ 5 * ((∑ c, (v c).natAbs) * p ^ 4) :=
    Nat.mul_le_mul_left _ (h1.trans (h2.trans h3))
  rw [hGoodBox] at h4
  have : 4 ^ 5 * ((∑ c, (v c).natAbs) * p ^ 4) = 4 ^ 5 * (∑ c, (v c).natAbs) * p ^ 4 := by ring
  omega

/-! ## The digits of the witness indices -/

section pair

variable (p : ℕ) [NeZero p] (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ)

open Z3NetU.Proofs (ix sk_sub_add)

/-- The coefficient of `w_d` in the first offset digit of coordinate `c` (`2 f_cd = F2 c d`). -/
def f5 (c d : Fin 5) : ZMod p := fE 5 p 1 (halfPhi 5 p F2 D) (by norm_num) le_rfl c d

lemma o1G_xOf (w : Fin 5 → ZMod p) (c : Fin 5) :
    o1G 5 p (halfPhi 5 p F2 D) (xOf 5 p 1 w) c = (∑ d, (D c 1 d : ZMod p) * w d).val := by
  set r1 : Fin (5 * 1 - 1) := ⟨1, by norm_num⟩
  have e := DgG_off 5 p 1 (halfPhi 5 p F2 D) c (xOf 5 p 1 w) r1
  have e2 : DgG 5 p 1 (halfPhi 5 p F2 D) c (xOf 5 p 1 w) ⟨1 + (r1 : ℕ), sk_sub_add r1⟩ =
      DgG 5 p 1 (halfPhi 5 p F2 D) c (xOf 5 p 1 w) ⟨2, by norm_num⟩ := rfl
  unfold o1G dv
  rw [dif_pos (by norm_num : 2 < 5 * 1), ← e2, e]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  rw [Fin.sum_univ_one, xOf_ix]
  simp [halfPhi, r1]

lemma Xdiff2 (w w' : Fin 5 → ZMod p) (c : Fin 5) :
    ∃ τ : ℤ, |τ| < (p : ℤ) ^ 2 ∧
      (GFpoint 5 p 1 (halfPhi 5 p F2 D) (xOf 5 p 1 w') c : ℤ) - GFpoint 5 p 1 (halfPhi 5 p F2 D) (xOf 5 p 1 w) c =
        (p : ℤ) ^ 4 * (((w' c).val : ℤ) - (w c).val) +
        (p : ℤ) ^ 3 * (((∑ d, f5 p F2 D c d * w' d).val : ℤ) - (∑ d, f5 p F2 D c d * w d).val) +
        (p : ℤ) ^ 2 * (((∑ d, (D c 1 d : ZMod p) * w' d).val : ℤ) - (∑ d, (D c 1 d : ZMod p) * w d).val) + τ := by
  set Φ := halfPhi 5 p F2 D
  refine ⟨(tl2G 5 p Φ (xOf 5 p 1 w') c : ℤ) - tl2G 5 p Φ (xOf 5 p 1 w) c, ?_, ?_⟩
  · have h1 := tl2G_lt 5 p Φ (by norm_num) (xOf 5 p 1 w') c
    have h2 := tl2G_lt 5 p Φ (by norm_num) (xOf 5 p 1 w) c
    have h1' : ((tl2G 5 p Φ (xOf 5 p 1 w') c : ℕ) : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast h1
    have h2' : ((tl2G 5 p Φ (xOf 5 p 1 w) c : ℕ) : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast h2
    rw [abs_lt]; constructor <;> omega
  · rw [XG_decomp2 5 p Φ (by norm_num), XG_decomp2 5 p Φ (by norm_num), cellN_xOf 5 p 1 le_rfl,
      cellN_xOf 5 p 1 le_rfl, o0G_xOf 5 p 1 Φ (by norm_num) le_rfl, o0G_xOf 5 p 1 Φ (by norm_num) le_rfl,
      o1G_xOf, o1G_xOf]
    simp only [f5, Φ]
    norm_num
    ring

end pair

/-! ## Local facts on residues -/

lemma cres_le' (N : ℕ) (hN : 0 < N) (u k : ℤ) : (cres N u : ℤ) ≤ |u + N * k| := by
  have hc : ((cres N u : ℕ) : ℤ) = min (u % (N : ℤ)) ((N : ℤ) - u % (N : ℤ)) := by
    have h0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ (by omega)
    have h1 : u % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
    have ht : ((u % (N : ℤ)).toNat : ℤ) = u % (N : ℤ) := Int.toNat_of_nonneg h0
    have hle : (u % (N : ℤ)).toNat ≤ N := by omega
    unfold cres
    rw [Nat.cast_min, Nat.cast_sub hle, ht]
  rw [hc]
  have h0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : u % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
  have hu : u = u % (N : ℤ) + N * (u / N) := (Int.emod_add_mul_ediv u N).symm
  set r := u % (N : ℤ)
  set t := k + u / N
  have he : u + N * k = r + N * t := by simp only [t, r]; linear_combination hu
  rw [he]
  rcases le_or_gt 0 t with ht | ht
  · have : 0 ≤ r + N * t := by nlinarith
    rw [abs_of_nonneg this]; exact le_trans (min_le_left _ _) (by nlinarith)
  · have ht' : t ≤ -1 := by omega
    have : r + N * t < 0 := by nlinarith
    rw [abs_of_neg this]; exact le_trans (min_le_right _ _) (by nlinarith)

lemma cast_eq_zero_of_abs_lt (p : ℕ) (z : ℤ) (h : (z : ZMod p) = 0) (hz : |z| < p) : z = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h) hz

/-! ## The shorter options -/

lemma sgnS_facts (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (E : Fin 5 → ℤ) (hE : E ∈ bind5)
    (c : Fin 5) :
    (sgnS F2 E c = 1 ∨ sgnS F2 E c = -1) ∧ sgnS F2 E c * dotR F2 E c = -drc2 F2 E c ∧
      (E c ≠ 0 → sgnS F2 E c = E c) := by
  have hE' := (TD.mem_bind5 E).mp hE
  have hs : (∑ d, E d) % 2 = 1 := by rw [Fin.sum_univ_five]; exact hE'.2
  have hB := dotR_odd_of_bind F2 hodd E hs c
  have hB0 : dotR F2 E c ≠ 0 := by intro h; rw [h] at hB; exact absurd hB (by decide)
  have he : E c = -1 ∨ E c = 0 ∨ E c = 1 := by have := hE'.1 c; omega
  unfold sgnS drc2
  by_cases h0 : E c = 0
  · simp only [h0, ↓reduceIte, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    refine ⟨?_, ?_⟩
    · rcases lt_or_gt_of_ne hB0 with h | h
      · left; rw [Int.sign_eq_neg_one_of_neg h]; norm_num
      · right; rw [Int.sign_eq_one_of_pos h]
    · rw [neg_mul, Int.sign_mul_self_eq_abs]
  · simp only [h0, ↓reduceIte, ne_eq, not_false_eq_true, forall_const, and_true]
    refine ⟨by omega, by ring⟩

/-- The shorter option of coordinate `c`: `Δr_c = (p s_c + 2β_c)/2 − p E_c`. -/
def dR (p : ℕ) (F2 : Fin 5 → Fin 5 → ℤ) (E : Fin 5 → ℤ) (c : Fin 5) : ℤ :=
  ((p : ℤ) * sgnS F2 E c + dotR F2 E c) / 2 - p * E c

lemma two_dR (p : ℕ) (hp : Odd p) (F2 : Fin 5 → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d)) (E : Fin 5 → ℤ)
    (hE : E ∈ bind5) (c : Fin 5) :
    2 * (((p : ℤ) * sgnS F2 E c + dotR F2 E c) / 2) = (p : ℤ) * sgnS F2 E c + dotR F2 E c := by
  have hE' := (TD.mem_bind5 E).mp hE
  have hs : (∑ d, E d) % 2 = 1 := by rw [Fin.sum_univ_five]; exact hE'.2
  obtain ⟨b, hb⟩ := dotR_odd_of_bind F2 hodd E hs c
  obtain ⟨k, hk⟩ := hp
  rcases (sgnS_facts F2 hodd E hE c).1 with h | h <;> rw [h, hb, hk] <;> push_cast <;> omega

/-! ## The pair -/

lemma two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this
  exact hp2 this

lemma val_sub_cast (p : ℕ) [NeZero p] (a b : ZMod p) (e : ℤ) (h : a = b + (e : ZMod p)) :
    ∃ z : ℤ, ((a.val : ℤ) - b.val) = e + p * z := by
  have : (((a.val : ℤ) - b.val - e : ℤ) : ZMod p) = 0 := by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, h]; ring
  obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
  exact ⟨z, by linarith⟩

/-- **The explicit pair** (the lower bound of the printed proof): for a binding step `E`, if `p ∤ det 2F₀`, `p ≥ 2|2β_c| + 2`,
`p > |D₁[c][d]|`, `p > |v_c|` and `4⁵ (∑|v_c|) p⁴ < p⁵`, two distinct points of the net have, in every coordinate,
`2 · (toroidal difference) ≤ p² (p (p − 2dr_c(E)) + 2(|v_c| + 1))` (integer scale `p⁵`). -/
lemma pair_core (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ)
    (hodd : ∀ c d, Odd (F2 c d)) (E : Fin 5 → ℤ) (hE : E ∈ bind5)
    (hdet : (((Matrix.of F2).det : ℤ) : ZMod p) ≠ 0)
    (hB : ∀ c, 2 * |dotR F2 E c| + 2 ≤ p) (hD1 : ∀ c d, |D c 1 d| < p)
    (hcount : 4 ^ 5 * (∑ c, (dotR (fun c d => D c 1 d) E c).natAbs) * p ^ 4 < p ^ 5) :
    ∃ x y : Fin (5 * 1) → ZMod p, x ≠ y ∧ ∀ c,
      2 * (cres (p ^ (5 * 1)) ((halfNet p F2 D x c : ℤ) - halfNet p F2 D y c) : ℤ) ≤
        (p : ℤ) ^ 2 * (p * (p - drc2 F2 E c) + 2 * (|dotR (fun c d => D c 1 d) E c| + 1)) := by
  have hpP : p.Prime := Fact.out
  have : NeZero p := ⟨hpP.ne_zero⟩
  have hoddp : Odd p := hpP.odd_of_ne_two hp2
  set D1 : Fin 5 → Fin 5 → ℤ := fun c d => D c 1 d with hD1def
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hpP.pos
  have hrow := halfPhi_row 5 p (by norm_num) hoddp F2 D
  have h2f : ∀ c d, 2 * f5 p F2 D c d = (F2 c d : ZMod p) := fun c d =>
    two_fE 5 p 1 (halfPhi 5 p F2 D) (by norm_num) le_rfl (fun _ => F2) hrow c d
  have h2 := two_ne_zero_zmod p hp2
  -- the first digits: an invertible matrix
  set Fh : Matrix (Fin 5) (Fin 5) (ZMod p) := Matrix.of fun c d => f5 p F2 D c d with hFh
  have hFdet : Fh.det ≠ 0 := by
    have hmap : (Matrix.of F2).map (Int.castRingHom (ZMod p)) = (2 : ZMod p) • Fh := by
      ext c d; simp [Fh, h2f]
    have e : (((Matrix.of F2).det : ℤ) : ZMod p) = 2 ^ 5 * Fh.det := by
      rw [show (((Matrix.of F2).det : ℤ) : ZMod p) = (Int.castRingHom (ZMod p)) (Matrix.of F2).det from rfl,
        RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_smul, Fintype.card_fin]
    intro h0; apply hdet; rw [e, h0, mul_zero]
  -- the shifts
  have hβ : ∀ c, 4 * |dR p F2 E c| ≤ 3 * p := by
    intro c
    obtain ⟨hs1, -, hsE⟩ := sgnS_facts F2 hodd E hE c
    have h2r := two_dR p hoddp F2 hodd E hE c
    have hE' := (TD.mem_bind5 E).mp hE
    have he : E c = -1 ∨ E c = 0 ∨ E c = 1 := by have := hE'.1 c; omega
    have hBc := hB c
    unfold dR
    generalize ((p : ℤ) * sgnS F2 E c + dotR F2 E c) / 2 = h at h2r ⊢
    have hab := abs_nonneg (dotR F2 E c)
    rcases he with he | he | he
    · rw [he] at hsE ⊢
      have := hsE (by norm_num)
      rw [this] at h2r
      cases abs_cases (h - ↑p * (-1 : ℤ)) <;> cases abs_cases (dotR F2 E c) <;> nlinarith
    · rw [he]
      rcases hs1 with hs | hs <;> rw [hs] at h2r <;>
        cases abs_cases (h - ↑p * (0 : ℤ)) <;> cases abs_cases (dotR F2 E c) <;> nlinarith
    · rw [he] at hsE ⊢
      have := hsE (by norm_num)
      rw [this] at h2r
      cases abs_cases (h - ↑p * (1 : ℤ)) <;> cases abs_cases (dotR F2 E c) <;> nlinarith
  have hL : ∀ c, dotR D1 E c ≠ 0 → ∃ d, ((D c 1 d : ℤ) : ZMod p) ≠ 0 := by
    intro c hv
    by_contra hall
    push Not at hall
    apply hv
    unfold dotR
    refine Finset.sum_eq_zero fun d _ => ?_
    simp only [D1, cast_eq_zero_of_abs_lt p _ (hall d) (hD1 c d), zero_mul]
  obtain ⟨w, hw1, hw2⟩ := exists_good_w p Fh hFdet (dR p F2 E) (dotR D1 E) (fun c d => ((D c 1 d : ℤ) : ZMod p))
    hL hβ hcount
  have hmv : ∀ c, (Fh *ᵥ w) c = ∑ d, f5 p F2 D c d * w d := fun c => by
    simp [Fh, Matrix.mulVec, dotProduct]
  -- the pair
  set Ec : Fin 5 → ZMod p := fun d => ((E d : ℤ) : ZMod p) with hEc
  refine ⟨xOf 5 p 1 (w + Ec), xOf 5 p 1 w, ?_, fun c => ?_⟩
  · have hE' := (TD.mem_bind5 E).mp hE
    obtain ⟨a, ha⟩ : ∃ a, E a ≠ 0 := by
      by_contra hall; push Not at hall
      have := hE'.2; simp [hall] at this
    refine xOf_ne 5 p 1 le_rfl w (w + Ec) a fun h => ha ?_
    have h0 : ((E a : ℤ) : ZMod p) = 0 := by simpa [Ec] using h
    have h1 : |E a| < p := by
      have := hE'.1 a
      have : |E a| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have : (3 : ℤ) ≤ p := by
        have := hpP.two_le
        have : 3 ≤ p := by omega
        exact_mod_cast this
      linarith
    exact cast_eq_zero_of_abs_lt p _ h0 h1
  · obtain ⟨τ, hτ, hdiff⟩ := Xdiff2 p F2 D w (w + Ec) c
    -- cell digit
    obtain ⟨z, hz⟩ := val_sub_cast p ((w + Ec) c) (w c) (E c) (by simp [Ec])
    -- first offset digit
    have hΔ : ∑ d, f5 p F2 D c d * Ec d = ((dR p F2 E c : ℤ) : ZMod p) := by
      have e1 : 2 * ∑ d, f5 p F2 D c d * Ec d = ((dotR F2 E c : ℤ) : ZMod p) := by
        rw [Finset.mul_sum]; unfold dotR; push_cast
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← mul_assoc, h2f]
      have e2 : 2 * ((dR p F2 E c : ℤ) : ZMod p) = ((dotR F2 E c : ℤ) : ZMod p) := by
        have h2r := two_dR p hoddp F2 hodd E hE c
        have : 2 * dR p F2 E c = dotR F2 E c + p * (sgnS F2 E c - 2 * E c) := by unfold dR; linarith
        have hc : ((2 * dR p F2 E c : ℤ) : ZMod p) = ((dotR F2 E c + p * (sgnS F2 E c - 2 * E c) : ℤ) : ZMod p) := by
          rw [this]
        push_cast at hc
        rw [hc, ZMod.natCast_self]; ring
      have := e1.trans e2.symm
      exact mul_left_cancel₀ h2 this
    have hr : ((∑ d, f5 p F2 D c d * (w + Ec) d).val : ℤ) = (∑ d, f5 p F2 D c d * w d).val + dR p F2 E c := by
      have : ∑ d, f5 p F2 D c d * (w + Ec) d = (∑ d, f5 p F2 D c d * w d) + ((dR p F2 E c : ℤ) : ZMod p) := by
        rw [← hΔ, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [Pi.add_apply]; ring
      rw [this]
      have h := hw1 c
      rw [hmv c] at h
      exact val_add_int p _ _ h.1 h.2
    -- second offset digit
    have hd : ((∑ d, ((D c 1 d : ℤ) : ZMod p) * (w + Ec) d).val : ℤ) =
        (∑ d, ((D c 1 d : ℤ) : ZMod p) * w d).val + dotR D1 E c := by
      have : ∑ d, ((D c 1 d : ℤ) : ZMod p) * (w + Ec) d =
          (∑ d, ((D c 1 d : ℤ) : ZMod p) * w d) + ((dotR D1 E c : ℤ) : ZMod p) := by
        unfold dotR; push_cast
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [Pi.add_apply, Ec, D1]; ring
      rw [this]
      exact val_add_int p _ _ (hw2 c).1 (hw2 c).2
    -- the coordinate
    have hdiff' : (halfNet p F2 D (xOf 5 p 1 (w + Ec)) c : ℤ) - halfNet p F2 D (xOf 5 p 1 w) c =
        (p : ℤ) ^ 4 * E c + p ^ 3 * dR p F2 E c + p ^ 2 * dotR D1 E c + τ + ((p ^ (5 * 1) : ℕ) : ℤ) * z := by
      unfold halfNet
      rw [hdiff, hz, hr, hd]; push_cast; ring
    have hc := cres_le' (p ^ (5 * 1)) (pow_pos hpP.pos _)
      ((halfNet p F2 D (xOf 5 p 1 (w + Ec)) c : ℤ) - halfNet p F2 D (xOf 5 p 1 w) c) (-z)
    rw [hdiff'] at hc ⊢
    have e3 : (p : ℤ) ^ 4 * E c + p ^ 3 * dR p F2 E c + p ^ 2 * dotR D1 E c + τ +
        ((p ^ (5 * 1) : ℕ) : ℤ) * z + ((p ^ (5 * 1) : ℕ) : ℤ) * -z =
        (p : ℤ) ^ 3 * (((p : ℤ) * sgnS F2 E c + dotR F2 E c) / 2) + p ^ 2 * dotR D1 E c + τ := by
      unfold dR; ring
    rw [e3] at hc
    -- `|p s + 2β| = p − 2dr_c`
    obtain ⟨hs1, hsB, -⟩ := sgnS_facts F2 hodd E hE c
    have h2r := two_dR p hoddp F2 hodd E hE c
    have hBc := hB c
    have habs : |(p : ℤ) * sgnS F2 E c + dotR F2 E c| = p - drc2 F2 E c := by
      rcases hs1 with hs | hs
      · rw [hs] at hsB ⊢
        rw [abs_of_nonneg (by cases abs_cases (dotR F2 E c) <;> linarith)]; linarith
      · rw [hs] at hsB ⊢
        rw [abs_of_nonpos (by cases abs_cases (dotR F2 E c) <;> linarith)]; linarith
    generalize ((p : ℤ) * sgnS F2 E c + dotR F2 E c) / 2 = h at h2r hc
    have hh : 2 * |h| = p - drc2 F2 E c := by rw [← habs, ← h2r, abs_mul, abs_two]
    have t1 := abs_add_le ((p : ℤ) ^ 3 * h + p ^ 2 * dotR D1 E c) τ
    have t2 := abs_add_le ((p : ℤ) ^ 3 * h) (p ^ 2 * dotR D1 E c)
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < (p : ℤ) ^ 3),
      abs_of_pos (by positivity : (0 : ℤ) < (p : ℤ) ^ 2)] at t2
    have hp3 : (0 : ℤ) ≤ (p : ℤ) ^ 3 := by positivity
    nlinarith [abs_nonneg h]

/-! ## From the pair to `sepN` -/

lemma pairVal_le_W (p : ℕ) (hp : 1 ≤ p) (X : (Fin (5 * 1) → ZMod p) → Fin 5 → ℕ) (x y : Fin (5 * 1) → ZMod p)
    (W : Fin 5 → ℤ) (h : ∀ c, 2 * (cres (p ^ (5 * 1)) ((X x c : ℤ) - X y c) : ℤ) ≤ (p : ℤ) ^ 2 * W c) :
    pairVal p X x y ≤ Real.sqrt (∑ c, ((W c : ℤ) : ℝ) ^ 2) / (2 * (p : ℝ) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have key : ∀ c, (p : ℝ) ^ 2 * (((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℝ) / (p : ℝ) ^ (5 * 1)) ^ 2
      ≤ ((W c : ℤ) : ℝ) ^ 2 / (2 * (p : ℝ) ^ 2) ^ 2 := by
    intro c
    have hc : 2 * ((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℝ) ≤ (p : ℝ) ^ 2 * (W c : ℝ) := by
      exact_mod_cast h c
    have h0 : (0 : ℝ) ≤ ((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsq := pow_le_pow_left₀ (by positivity) hc 2
    rw [div_pow, show ((p : ℝ) ^ (5 * 1)) ^ 2 = (p : ℝ) ^ 10 by ring, mul_div_assoc',
      div_le_div_iff₀ (by positivity) (by positivity)]
    rw [mul_pow, mul_pow] at hsq
    have h6 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 6)
    nlinarith
  unfold pairVal
  calc (p : ℝ) * Real.sqrt (∑ c, (((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℝ) /
        (p : ℝ) ^ (5 * 1)) ^ 2)
      = Real.sqrt ((p : ℝ) ^ 2 * ∑ c, (((cres (p ^ (5 * 1)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℝ) /
        (p : ℝ) ^ (5 * 1)) ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp0.le]
    _ ≤ Real.sqrt (∑ c, ((W c : ℤ) : ℝ) ^ 2 / (2 * (p : ℝ) ^ 2) ^ 2) :=
        Real.sqrt_le_sqrt (by rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c _ => key c)
    _ = _ := by
        rw [← Finset.sum_div, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]

/-- The integer bound `∑_c W_c² ≤ 5p⁴ − 2p³ · 2dr(E) + G p²`. -/
lemma sum_W_le (p : ℕ) (hp : 1 ≤ p) (δ v : Fin 5 → ℤ) :
    ∑ c, ((p : ℤ) * (p - δ c) + 2 * (|v c| + 1)) ^ 2 ≤
      5 * (p : ℤ) ^ 4 - 2 * p ^ 3 * (∑ c, δ c) +
        (∑ c, (δ c ^ 2 + 4 * (|v c| + 1) + 4 * |δ c| * (|v c| + 1) + 4 * (|v c| + 1) ^ 2)) * p ^ 2 := by
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have key : ∀ c, ((p : ℤ) * (p - δ c) + 2 * (|v c| + 1)) ^ 2 ≤ (p : ℤ) ^ 4 - 2 * p ^ 3 * δ c +
      (δ c ^ 2 + 4 * (|v c| + 1) + 4 * |δ c| * (|v c| + 1) + 4 * (|v c| + 1) ^ 2) * p ^ 2 := by
    intro c
    have hw : (1 : ℤ) ≤ |v c| + 1 := by linarith [abs_nonneg (v c)]
    have hd := neg_abs_le (δ c)
    have h1 : -(4 * (p : ℤ) * δ c * (|v c| + 1)) ≤ 4 * |δ c| * (|v c| + 1) * p ^ 2 := by
      have : (p : ℤ) ≤ (p : ℤ) ^ 2 := by nlinarith
      have h0 : 0 ≤ (|v c| + 1) := by linarith
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (δ c)) h0) (by linarith : (0 : ℤ) ≤ (p : ℤ) ^ 2 - p),
        mul_nonneg (mul_nonneg (by linarith : (0 : ℤ) ≤ |δ c| + δ c) h0) (by linarith : (0 : ℤ) ≤ (p : ℤ))]
    have h2 : 4 * (|v c| + 1) ^ 2 ≤ 4 * (|v c| + 1) ^ 2 * p ^ 2 := by
      have : (1 : ℤ) ≤ (p : ℤ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (|v c| + 1)]
    nlinarith
  calc ∑ c, ((p : ℤ) * (p - δ c) + 2 * (|v c| + 1)) ^ 2
      ≤ ∑ c, ((p : ℤ) ^ 4 - 2 * p ^ 3 * δ c +
          (δ c ^ 2 + 4 * (|v c| + 1) + 4 * |δ c| * (|v c| + 1) + 4 * (|v c| + 1) ^ 2) * p ^ 2) :=
        Finset.sum_le_sum fun c _ => key c
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        simp

/-- `√(5/4 − δ/(2p) + G/(4p²)) ≤ (√5/2)(1 − δ/(5p)) + (G/8)/p²` for `|δ| ≤ p`, `G ≥ 0`. -/
lemma upper_real (p : ℕ) (hp : 1 ≤ p) (δ G Z : ℤ) (hG : 0 ≤ G) (hpδ : |δ| ≤ p)
    (hZ : Z ≤ 5 * (p : ℤ) ^ 4 - 2 * p ^ 3 * δ + G * p ^ 2) :
    Real.sqrt (Z : ℝ) / (2 * (p : ℝ) ^ 2) ≤ Real.sqrt 5 / 2 * (1 - (δ : ℝ) / (5 * p)) + (G : ℝ) / 8 / (p : ℝ) ^ 2 := by
  set a : ℝ := Real.sqrt 5 / 2 with ha
  have ha1 := one_le_a
  have ha2 := a_sq
  rw [← ha] at ha1 ha2
  have ha0 : 0 < a := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hG0 : (0 : ℝ) ≤ G := by exact_mod_cast hG
  have hδ : |(δ : ℝ)| ≤ p := by exact_mod_cast hpδ
  set u : ℝ := (δ : ℝ) / (2 * p) - (G : ℝ) / (4 * p ^ 2) with hu
  set T : ℝ := a - u / (2 * a) with hT
  have h4a : 1 / (4 * a) = a / 5 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]; nlinarith [ha2]
  have eT : T = a * (1 - (δ : ℝ) / (5 * p)) + (G : ℝ) / (8 * a * p ^ 2) := by
    have : u / (2 * a) = (δ : ℝ) / p * (1 / (4 * a)) - (G : ℝ) / (8 * a * p ^ 2) := by
      rw [hu]; field_simp; ring
    rw [hT, this, h4a]; ring
  have hT0 : 0 ≤ T := by
    rw [eT]
    have h1 : (δ : ℝ) / (5 * p) ≤ 1 / 5 := by
      rw [div_le_iff₀ (by positivity)]; linarith [le_abs_self (δ : ℝ)]
    have : 0 ≤ (G : ℝ) / (8 * a * p ^ 2) := by positivity
    nlinarith
  have hZ' : (Z : ℝ) / (2 * (p : ℝ) ^ 2) ^ 2 ≤ T ^ 2 := by
    have hZr : (Z : ℝ) ≤ 5 * (p : ℝ) ^ 4 - 2 * p ^ 3 * δ + G * p ^ 2 := by exact_mod_cast hZ
    have e1 : T ^ 2 = a ^ 2 - u + u ^ 2 / (4 * a ^ 2) := by rw [hT]; field_simp; ring
    have e2 : (5 * (p : ℝ) ^ 4 - 2 * p ^ 3 * δ + G * p ^ 2) / (2 * (p : ℝ) ^ 2) ^ 2 = a ^ 2 - u := by
      rw [ha2, hu]; field_simp; ring
    have e3 : 0 ≤ u ^ 2 / (4 * a ^ 2) := by positivity
    calc (Z : ℝ) / (2 * (p : ℝ) ^ 2) ^ 2 ≤ (5 * (p : ℝ) ^ 4 - 2 * p ^ 3 * δ + G * p ^ 2) / (2 * (p : ℝ) ^ 2) ^ 2 :=
          div_le_div_of_nonneg_right hZr (by positivity)
      _ = a ^ 2 - u := e2
      _ ≤ T ^ 2 := by rw [e1]; linarith
  have hsq : Real.sqrt (Z : ℝ) / (2 * (p : ℝ) ^ 2) ≤ T := by
    rw [show Real.sqrt (Z : ℝ) / (2 * (p : ℝ) ^ 2) = Real.sqrt ((Z : ℝ) / (2 * (p : ℝ) ^ 2) ^ 2) by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]]
    calc Real.sqrt ((Z : ℝ) / (2 * (p : ℝ) ^ 2) ^ 2) ≤ Real.sqrt (T ^ 2) := Real.sqrt_le_sqrt hZ'
      _ = T := Real.sqrt_sq hT0
  refine hsq.trans ?_
  rw [eT]
  have : (G : ℝ) / (8 * a * p ^ 2) ≤ (G : ℝ) / 8 / p ^ 2 := by
    rw [div_div]; apply div_le_div_of_nonneg_left hG0 (by positivity); nlinarith [pow_pos hp0 2]
  linarith

/-- **`rem:accounting`, `liminf K_eff ≥ dr`** (the second half of the printed proof): if `det 2F₀ ≠ 0`, then for every
prime `p ≥ P`, `δN^{1/5} ≤ (√5/2)(1 − 2dr(F₀)/(5p)) + C/p²` (toroidal), for all deeper rows. -/
theorem acct_lower_core (F2 : Fin 5 → Fin 5 → ℤ) (D : Fin 5 → ℕ → Fin 5 → ℤ) (hodd : ∀ c d, Odd (F2 c d))
    (hdet : (Matrix.of F2).det ≠ 0) :
    ∃ C : ℝ, ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      sepN p (halfNet p F2 D) ≤ Real.sqrt 5 / 2 * (1 - (drift2 F2 : ℝ) / (5 * p)) + C / (p : ℝ) ^ 2 := by
  obtain ⟨E, hE, hEq⟩ := Finset.exists_mem_eq_sup' bind5_nonempty (drift2E F2)
  set D1 : Fin 5 → Fin 5 → ℤ := fun c d => D c 1 d with hD1
  set G : ℤ := ∑ c, (drc2 F2 E c ^ 2 + 4 * (|dotR D1 E c| + 1) + 4 * |drc2 F2 E c| * (|dotR D1 E c| + 1) +
    4 * (|dotR D1 E c| + 1) ^ 2) with hG
  set Bs : ℤ := ∑ c, |dotR F2 E c| with hBs
  set Ds : ℤ := ∑ c, ∑ d, |D c 1 d| with hDs
  set Vs : ℕ := ∑ c, (dotR D1 E c).natAbs with hVs
  set P0 : ℤ := 2 * Bs + 2 + Ds + 1 + |(Matrix.of F2).det| + 1 + 1024 * Vs + 1 + |drift2 F2| + 3 with hP0
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun c _ => by
    have h1 := sq_nonneg (drc2 F2 E c)
    have h2 := abs_nonneg (dotR D1 E c)
    have h3 := mul_nonneg (abs_nonneg (drc2 F2 E c)) (by linarith : (0 : ℤ) ≤ |dotR D1 E c| + 1)
    have h4 := sq_nonneg (|dotR D1 E c| + 1)
    linarith
  refine ⟨(G : ℝ) / 8, P0.toNat, fun p hp hPp => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hPp' : P0 ≤ (p : ℤ) := by
    have := Int.self_le_toNat P0
    have h2 : ((P0.toNat : ℕ) : ℤ) ≤ p := by exact_mod_cast hPp
    linarith
  have hBs0 : ∀ c, |dotR F2 E c| ≤ Bs := fun c =>
    Finset.single_le_sum (f := fun c => |dotR F2 E c|) (fun c _ => abs_nonneg _) (mem_univ c)
  have hDs0 : ∀ c d, |D c 1 d| ≤ Ds := fun c d =>
    (Finset.single_le_sum (f := fun d => |D c 1 d|) (fun d _ => abs_nonneg _) (mem_univ d)).trans
      (Finset.single_le_sum (f := fun c => ∑ d, |D c 1 d|) (fun c _ => Finset.sum_nonneg fun d _ => abs_nonneg _)
        (mem_univ c))
  have hBs00 : 0 ≤ Bs := Finset.sum_nonneg fun c _ => abs_nonneg _
  have hDs00 : 0 ≤ Ds := Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => abs_nonneg _
  have hdabs := abs_nonneg (Matrix.of F2).det
  have hdr := abs_nonneg (drift2 F2)
  have hVs0 : (0 : ℤ) ≤ Vs := Int.natCast_nonneg _
  have hp2 : p ≠ 2 := by
    rintro rfl; push_cast at hPp'; linarith
  have hdet' : (((Matrix.of F2).det : ℤ) : ZMod p) ≠ 0 := fun h0 =>
    hdet (cast_eq_zero_of_abs_lt p _ h0 (by linarith))
  have hcount : 4 ^ 5 * (∑ c, (dotR D1 E c).natAbs) * p ^ 4 < p ^ 5 := by
    have h1 : 1024 * (Vs : ℤ) < p := by linarith
    have h1' : 1024 * Vs < p := by exact_mod_cast h1
    have hp4 : 0 < p ^ 4 := pow_pos hp.pos 4
    calc 4 ^ 5 * (∑ c, (dotR D1 E c).natAbs) * p ^ 4 = (1024 * Vs) * p ^ 4 := by rw [hVs]; ring
      _ < p * p ^ 4 := Nat.mul_lt_mul_of_pos_right h1' hp4
      _ = p ^ 5 := by ring
  obtain ⟨x, y, hxy, hcoord⟩ := pair_core p hp2 F2 D hodd E hE hdet'
    (fun c => by linarith [hBs0 c]) (fun c d => by linarith [hDs0 c d]) hcount
  have hle := (sepN_le p _ x y hxy).trans (pairVal_le_W p hp.one_lt.le _ x y _ hcoord)
  refine hle.trans ?_
  have hsum := sum_W_le p hp.one_lt.le (drc2 F2 E) (dotR D1 E)
  have hδ : ∑ c, drc2 F2 E c = drift2 F2 := by
    show drift2E F2 E = bind5.sup' bind5_nonempty (drift2E F2)
    exact hEq.symm
  rw [hδ] at hsum
  have hZ := upper_real p hp.one_lt.le (drift2 F2) G _ hG0 (by linarith) (hsum.trans (le_of_eq (by rw [hG])))
  push_cast at hZ ⊢
  exact hZ

end

end Z3NetHL.Proofs.Acct

/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.KNPPS11
public import Z3Net.S1Shift

@[expose] public section

/-!
# V14 stage S15′: `rem:ppshift` (`prop:ppsep` for every digital shift)

The proof of `prop:ppsep` (`Geom.sep_of_cert`) reads a coordinate through
* its first `K_c` digits, which are the cell digits of `c` (graph form),
* the differences of its skeleton and jitter digits modulo `p` (designed rows),
* the tail digits below position `k + 2`, which agree when only the own cell moves (`IsKN`, (ii)),
* the size bounds of digits and tails.

The proof of `rem:ppshift` (the research notes Part 2) re-indexes the shifted
point set by its own cells (`lem:shift`). Here: with `γ` the cell part of the shift `τ` placed on the index blocks
(`cellShift`), `C_c v + τ_c = C_c (v + γ) + σ_c` with `σ_c = τ_c − C_c γ`, and `σ_c` vanishes on the cell rows of
`c` (`CellFree`). For such a shift the cell digits are those of the unshifted net, and every other digit is shifted by
a constant, which cancels in every difference modulo `p` and keeps the equality of tails; the size bounds hold for
every digit vector. So the four facts above hold verbatim (`far_boundS`, `near_fullS`, `near_skelS`,
`low_eq_of_ownS`, `near_termS`), and so does the reduction theorem (`sep_of_certS`); `ppsep_shift_core` is the
statement for every digital shift.
-/

namespace Z3NetKN.Geom

open Finset Matrix Z3NetKN.Relax

variable {p r k : ℕ}

/-- The shift `σ` vanishes on the cell rows of every coordinate. -/
def CellFree (r k : ℕ) (σ : Fin 3 → Fin (3 * k + r) → ZMod p) : Prop :=
  ∀ c : Fin 3, ∀ j < depth r k c, vz (σ c) j = 0

lemma vz_sub {m : ℕ} (x y : Fin m → ZMod p) (j : ℕ) : vz (x - y) j = vz x j - vz y j := by
  unfold vz; split_ifs <;> simp

lemma dg_cellFree (σ : Fin 3 → Fin (3 * k + r) → ZMod p) (hσ : CellFree r k σ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (v : Fin (3 * k + r) → ZMod p)
    (c : Fin 3) (j : ℕ) (hj : j < depth r k c) :
    dg (1 : Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (C c *ᵥ v + σ c) j = dg (C c) v j := by
  unfold dg
  rw [one_mulVec, vz_add, hσ c j hj, add_zero]

lemma pre_dg_depthS (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hr : r = 1 ∨ r = 2)
    (hC : IsKNskel r p k sk C) (σ : Fin 3 → Fin (3 * k + r) → ZMod p) (hσ : CellFree r k σ)
    (v : Fin (3 * k + r) → ZMod p) (c : Fin 3) :
    pre p (dg (1 : Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (C c *ᵥ v + σ c)) (depth r k c) =
      nC r k v c :=
  pre_congr p _ _ _ (fun j hj => (dg_cellFree σ hσ C v c j hj).trans (graph_digit sk C hr hC v c j hj))

lemma natCast_dgS_sub [NeZero p] (C : Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p))
    (t : Fin (3 * k + r) → ZMod p) (v w : Fin (3 * k + r) → ZMod p) (j : ℕ) :
    ((((dg (1 : Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (C *ᵥ v + t) j : ℤ) -
        dg (1 : Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (C *ᵥ w + t) j : ℤ)) : ZMod p) =
      vz (C *ᵥ v) j - vz (C *ᵥ w) j := by
  rw [natCast_dg_sub, one_mulVec, one_mulVec, vz_add, vz_add, add_sub_add_right_eq_sub]

/-- **Far bound**, shifted. -/
lemma far_boundS [NeZero p] (hr : r = 1 ∨ r = 2) (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKNskel r p k sk C)
    (σ : Fin 3 → Fin (3 * k + r) → ZMod p) (hσ : CellFree r k σ)
    (v w : Fin (3 * k + r) → ZMod p) (c : Fin 3) :
    |cen (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c)| * ((p ^ (3 * k + r - depth r k c) : ℕ) : ℤ)
        - (((p ^ (3 * k + r - depth r k c) : ℕ) : ℤ) - 1) ≤
      (cres (p ^ (3 * k + r)) ((coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) -
        coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) : ℤ) := by
  have hK : depth r k c ≤ 3 * k + r := by have := off_add_depth r k hr c; omega
  set K := depth r k c with hKdef
  set U := p ^ (3 * k + r - K) with hU
  rw [coord_split _ _ K hK, coord_split _ _ K hK, pre_dg_depthS sk C hr hC σ hσ v c,
    pre_dg_depthS sk C hr hC σ hσ w c]
  obtain ⟨z, hz⟩ := cen_spec (p ^ K) ((nC r k v c : ℤ) - nC r k w c)
  have hN : p ^ (3 * k + r) = p ^ K * U := by rw [hU, ← pow_add]; congr 1; omega
  have hp0 : 0 < p := Nat.pos_of_neZero p
  have key : ((nC r k v c * U + low 1 (C c *ᵥ v + σ c) K : ℕ) : ℤ) -
      ((nC r k w c * U + low 1 (C c *ᵥ w + σ c) K : ℕ) : ℤ) =
      cen (p ^ K) ((nC r k v c : ℤ) - nC r k w c) * U +
        ((low 1 (C c *ᵥ v + σ c) K : ℤ) - low 1 (C c *ᵥ w + σ c) K) + z * ((p ^ K * U : ℕ) : ℤ) := by
    push_cast
    have : (nC r k v c : ℤ) - nC r k w c - (cen (p ^ K) ((nC r k v c : ℤ) - nC r k w c) +
        z * ((p ^ K : ℕ) : ℤ)) = 0 := by rw [← hz]; ring
    push_cast at this
    linear_combination (U : ℤ) * this
  rw [hN, key]
  exact cres_lower (p ^ K) U (by positivity) (by positivity) _ _ z _
    (cen_abs _ (by positivity) _) (low_diff _ _ _ K)

/-- Near decomposition, full coordinate, shifted. -/
lemma near_fullS [NeZero p] (hr : r = 1 ∨ r = 2) (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKNskel r p k sk C)
    (σ : Fin 3 → Fin (3 * k + r) → ZMod p) (hσ : CellFree r k σ)
    (v w : Fin (3 * k + r) → ZMod p) (c : Fin 3) (hc : (c : ℕ) < r) (hk : 1 ≤ k) :
    ∃ z : ℤ, (coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) - coord p (3 * k + r) 1 (C c *ᵥ w + σ c) =
      (cen (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c) * p +
          ((dg 1 (C c *ᵥ v + σ c) (k + 1) : ℤ) - dg 1 (C c *ᵥ w + σ c) (k + 1))) *
            ((p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) +
        ((low 1 (C c *ᵥ v + σ c) (k + 2) : ℤ) - low 1 (C c *ᵥ w + σ c) (k + 2)) +
        z * ((p ^ (k + 2) * p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) := by
  have hd : depth r k c = k + 1 := by unfold depth; rw [if_pos hc]
  have hK : k + 2 ≤ 3 * k + r := by omega
  rw [coord_split _ _ (k + 2) hK, coord_split _ _ (k + 2) hK]
  have ev := pre_dg_depthS sk C hr hC σ hσ v c
  have ew := pre_dg_depthS sk C hr hC σ hσ w c
  rw [hd] at ev ew
  have ev2 : pre p (dg 1 (C c *ᵥ v + σ c)) (k + 2) = nC r k v c * p + dg 1 (C c *ᵥ v + σ c) (k + 1) := by
    rw [← ev]; rfl
  have ew2 : pre p (dg 1 (C c *ᵥ w + σ c)) (k + 2) = nC r k w c * p + dg 1 (C c *ᵥ w + σ c) (k + 1) := by
    rw [← ew]; rfl
  rw [ev2, ew2]
  obtain ⟨z, hz⟩ := cen_spec (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c)
  refine ⟨z, ?_⟩
  rw [hd] at hz ⊢
  set δ := cen (p ^ (k + 1)) ((nC r k v c : ℤ) - nC r k w c)
  push_cast at hz ⊢
  linear_combination ((p : ℤ) * (p : ℤ) ^ (3 * k + r - (k + 2))) * hz

/-- Near decomposition, skeleton coordinate, shifted. -/
lemma near_skelS [NeZero p] (hr : r = 1 ∨ r = 2) (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKNskel r p k sk C)
    (σ : Fin 3 → Fin (3 * k + r) → ZMod p) (hσ : CellFree r k σ)
    (v w : Fin (3 * k + r) → ZMod p) (c : Fin 3) (hc : r ≤ (c : ℕ)) (hk : 1 ≤ k) :
    ∃ z : ℤ, (coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) - coord p (3 * k + r) 1 (C c *ᵥ w + σ c) =
      ((cen (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c) * p +
          ((dg 1 (C c *ᵥ v + σ c) k : ℤ) - dg 1 (C c *ᵥ w + σ c) k)) * p +
          ((dg 1 (C c *ᵥ v + σ c) (k + 1) : ℤ) - dg 1 (C c *ᵥ w + σ c) (k + 1))) *
            ((p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) +
        ((low 1 (C c *ᵥ v + σ c) (k + 2) : ℤ) - low 1 (C c *ᵥ w + σ c) (k + 2)) +
        z * ((p ^ (k + 2) * p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) := by
  have hd : depth r k c = k := by unfold depth; rw [if_neg (by omega)]
  have hK : k + 2 ≤ 3 * k + r := by omega
  rw [coord_split _ _ (k + 2) hK, coord_split _ _ (k + 2) hK]
  have ev := pre_dg_depthS sk C hr hC σ hσ v c
  have ew := pre_dg_depthS sk C hr hC σ hσ w c
  rw [hd] at ev ew
  have ev2 : pre p (dg 1 (C c *ᵥ v + σ c)) (k + 2) =
      (nC r k v c * p + dg 1 (C c *ᵥ v + σ c) k) * p + dg 1 (C c *ᵥ v + σ c) (k + 1) := by
    rw [← ev]; rfl
  have ew2 : pre p (dg 1 (C c *ᵥ w + σ c)) (k + 2) =
      (nC r k w c * p + dg 1 (C c *ᵥ w + σ c) k) * p + dg 1 (C c *ᵥ w + σ c) (k + 1) := by
    rw [← ew]; rfl
  rw [ev2, ew2]
  obtain ⟨z, hz⟩ := cen_spec (p ^ depth r k c) ((nC r k v c : ℤ) - nC r k w c)
  refine ⟨z, ?_⟩
  rw [hd] at hz ⊢
  set δ := cen (p ^ k) ((nC r k v c : ℤ) - nC r k w c)
  push_cast at hz ⊢
  linear_combination ((p : ℤ) * (p : ℤ) * (p : ℤ) ^ (3 * k + r - (k + 2))) * hz

/-- Own case, shifted: the tail digits agree. -/
lemma low_eq_of_ownS [NeZero p] (hr : r = 1 ∨ r = 2) (R : Rows)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (σ : Fin 3 → Fin (3 * k + r) → ZMod p)
    (v w : Fin (3 * k + r) → ZMod p) (c : Fin 3) (hother : ∀ d, d ≠ c → nC r k v d = nC r k w d) :
    low 1 (C c *ᵥ v + σ c) (k + 2) = low 1 (C c *ᵥ w + σ c) (k + 2) := by
  unfold low
  refine pre_congr p _ _ _ fun j hj => ?_
  have hi : k + 2 + j < 3 * k + r := by omega
  unfold dg
  rw [one_mulVec, one_mulVec, vz_add, vz_add]
  congr 2
  rw [← sub_eq_zero, row_diff hr _ v w _ hi]
  refine sum_eq_zero fun d _ => sum_eq_zero fun l hl => ?_
  simp only [mem_range] at hl
  by_cases hd : d = c
  · subst hd
    rw [hC.2.2 d (k + 2 + j) l (by rw [jrow_eq]; omega) hi hl, zero_mul]
  · rw [vz_eq_of_nC_eq v w d (hother d hd) l hl, sub_self, mul_zero]

/-- **Near bound** for one coordinate, shifted. -/
theorem near_termS (hr : r = 1 ∨ r = 2) (hk : 2 ≤ k) (hp : 2 ≤ p) (R : Rows) (Rg : Fin 3 → ℕ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (σ : Fin 3 → Fin (3 * k + r) → ZMod p) (hσ : CellFree r k σ)
    (v w : Fin (3 * k + r) → ZMod p) (δ : Fin 3 → ℤ)
    (hδ : ∀ d, δ d = cen (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d))
    (hbox : ∀ d, |δ d| ≤ Rg d) (hRp : ∀ d, Rg d < p) (hRs : ∀ d : Fin 3, r ≤ (d : ℕ) → Rg d = 1)
    (ch : Fin 3 → ℕ) (hch : ∀ d, ch d < min (depth r k d) (win r d))
    (hD : ∀ d : Fin 3, ∀ l < depth r k d, depth r k d - 1 - l < win r d →
      vz v (off r k d + l) - vz w (off r k d + l) = ((pat (δ d) (ch d) (depth r k d - 1 - l) : ℤ) : ZMod p))
    (c : Fin 3) :
    haveI : NeZero p := ⟨by omega⟩
    ((term ⟨p, r, Rg, R⟩ δ ch c : ℕ) : ℤ) * ((p ^ (3 * k + r - (k + 2)) : ℕ) : ℤ) ≤
      (cres (p ^ (3 * k + r)) ((coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) -
        coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) : ℤ) := by
  haveI : NeZero p := ⟨by omega⟩
  set u := p ^ (3 * k + r - (k + 2)) with hu
  have hu0 : 0 < u := by positivity
  have hN : p ^ (3 * k + r) = p ^ (k + 2) * u := by rw [hu, ← pow_add]; congr 1; omega
  have hP4 : 4 * p ^ 2 ≤ p ^ (k + 2) := by
    rw [pow_add]
    have : 4 ≤ p ^ k := by
      calc 4 ≤ 2 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
        _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
    exact Nat.mul_le_mul_right _ this
  have hP4' : (4 : ℤ) * (p : ℤ) ^ 2 ≤ ((p ^ (k + 2) : ℕ) : ℤ) := by exact_mod_cast hP4
  set sl : ℤ := if isOwn δ c then 0 else 1 with hsl
  have hsl01 : sl = 0 ∨ sl = 1 := by rw [hsl]; split_ifs <;> simp
  set e : ℤ := (low 1 (C c *ᵥ v + σ c) (k + 2) : ℤ) - low 1 (C c *ᵥ w + σ c) (k + 2) with he
  have heE : |e| ≤ sl * ((u : ℤ) - 1) := by
    by_cases hown : isOwn δ c = true
    · have : sl = 0 := by rw [hsl, if_pos hown]
      rw [this, zero_mul, he, low_eq_of_ownS hr R C hC σ v w c (fun d hd => nC_eq_of_cen_zero v w d
        (by rw [← hδ d]; exact isOwn_spec δ c hown d hd))]
      simp
    · have : sl = 1 := by rw [hsl, if_neg hown]
      rw [this, one_mul]
      exact low_diff _ _ _ (k + 2)
  have hcr0 : (0 : ℤ) ≤ (cres (p ^ (3 * k + r)) ((coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) -
      coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) : ℤ) := by positivity
  set x : ℤ := (dg 1 (C c *ᵥ v + σ c) (k + 1) : ℤ) - dg 1 (C c *ᵥ w + σ c) (k + 1) with hx
  have hxa : |x| < p := dg_sub_abs _ _ _ _
  have hxm : (x : ZMod p) = ((linC (R.jt c) δ ch : ℤ) : ZMod p) := by
    rw [hx, natCast_dgS_sub]
    refine designed_row_diff hr (C c) (R.jt c) v w (k + 1) (by omega) (fun d l hl => ?_) δ ch hch hD
    have := hC.2.1 c d l hl
    rwa [jrow_eq] at this
  have hδc : |δ c| ≤ (p : ℤ) - 1 := by have := hbox c; have := hRp c; omega
  have hxa' := abs_lt.mp hxa
  have hfin : ∀ B : ℤ, ∀ z : ℤ, 2 * |B| ≤ ((p ^ (k + 2) : ℕ) : ℤ) →
      ((coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) - coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) =
        B * (u : ℤ) + e + z * ((p ^ (k + 2) * u : ℕ) : ℤ) →
      term ⟨p, r, Rg, R⟩ δ ch c ≤ tv B sl →
      ((term ⟨p, r, Rg, R⟩ δ ch c : ℕ) : ℤ) * u ≤
        (cres (p ^ (3 * k + r)) ((coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) -
          coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) : ℤ) := by
    intro B z hB2 hz hterm
    have hcl := cres_lower (p ^ (k + 2)) u (by positivity) hu0 B e z _ hB2 heE
    rw [← hz, ← hN] at hcl
    have h1 : ((term ⟨p, r, Rg, R⟩ δ ch c : ℕ) : ℤ) ≤ ((tv B sl : ℕ) : ℤ) := by
      exact_mod_cast hterm
    exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) (tv_mul_le B sl hsl01 u _ hcl hcr0)
  by_cases hc : (c : ℕ) < r
  · obtain ⟨z, hz⟩ := near_fullS hr R.sk C hC.1 σ hσ v w c hc (by omega)
    rw [← hδ c] at hz
    refine hfin (δ c * p + x) z ?_ hz ?_
    · have h1 : |δ c * p + x| ≤ |δ c| * p + |x| := by
        calc |δ c * p + x| ≤ |δ c * p| + |x| := abs_add_le _ _
          _ = |δ c| * p + |x| := by rw [abs_mul, Nat.abs_cast]
      nlinarith [abs_nonneg (δ c), abs_nonneg x]
    · have hf : (⟨p, r, Rg, R⟩ : Design).full c = true := by simp [Design.full, hc]
      have := term_full_le ⟨p, r, Rg, R⟩ (by simp; omega) δ ch c hf x hxa hxm
      rw [show (p : ℤ) * δ c + x = δ c * p + x by ring] at this
      exact this
  · have hc' : r ≤ (c : ℕ) := by omega
    have hdk : depth r k c = k := by unfold depth; rw [if_neg hc]
    obtain ⟨z, hz⟩ := near_skelS hr R.sk C hC.1 σ hσ v w c hc' (by omega)
    rw [← hδ c] at hz
    have hya : |(dg 1 (C c *ᵥ v + σ c) k : ℤ) - dg 1 (C c *ᵥ w + σ c) k| < p := dg_sub_abs _ _ _ _
    have hym : (((dg 1 (C c *ᵥ v + σ c) k : ℤ) - dg 1 (C c *ᵥ w + σ c) k : ℤ) : ZMod p) =
        ((linC (R.sk c) δ ch : ℤ) : ZMod p) := by
      rw [natCast_dgS_sub]
      refine designed_row_diff hr (C c) (R.sk c) v w k (by omega) (fun d l hl => ?_) δ ch hch hD
      have := hC.1.2 c d hc' l hl
      rwa [hdk] at this
    have hδ1 : |δ c| ≤ 1 := by have := hbox c; rw [hRs c hc'] at this; exact_mod_cast this
    refine hfin ((δ c * p + ((dg 1 (C c *ᵥ v + σ c) k : ℤ) - dg 1 (C c *ᵥ w + σ c) k)) * p + x) z ?_ hz ?_
    · generalize hy : (dg 1 (C c *ᵥ v + σ c) k : ℤ) - dg 1 (C c *ᵥ w + σ c) k = y at hya
      have hya' := abs_lt.mp hya
      have h1 : |(δ c * p + y) * p + x| ≤ (|δ c| * p + |y|) * p + |x| := by
        calc |(δ c * p + y) * p + x| ≤ |(δ c * p + y) * p| + |x| := abs_add_le _ _
          _ = |δ c * p + y| * p + |x| := by rw [abs_mul, Nat.abs_cast]
          _ ≤ (|δ c * p| + |y|) * p + |x| := by
              have := abs_add_le (δ c * p) y
              have hp0 : (0 : ℤ) ≤ p := by positivity
              have := mul_le_mul_of_nonneg_right this hp0
              linarith
          _ = (|δ c| * p + |y|) * p + |x| := by rw [abs_mul, Nat.abs_cast]
      have hya2 : |y| ≤ (p : ℤ) - 1 := by omega
      have hxa2 : |x| ≤ (p : ℤ) - 1 := by omega
      have h2 : (|δ c| * p + |y|) * p ≤ (2 * (p : ℤ) - 1) * p := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hp0 : (0 : ℤ) ≤ p := by positivity
        have := mul_le_mul_of_nonneg_right hδ1 hp0
        linarith
      have h3 : (2 * (p : ℤ) - 1) * p = 2 * (p : ℤ) ^ 2 - p := by ring
      linarith
    · have hf : (⟨p, r, Rg, R⟩ : Design).full c = false := by simp [Design.full, hc]
      have := term_skel_le ⟨p, r, Rg, R⟩ (by simp; omega) δ ch c hf x _ hxa hxm hya hym
      rw [show (p : ℤ) * ((p : ℤ) * δ c + ((dg 1 (C c *ᵥ v + σ c) k : ℤ) - dg 1 (C c *ᵥ w + σ c) k)) + x =
        (δ c * p + ((dg 1 (C c *ᵥ v + σ c) k : ℤ) - dg 1 (C c *ᵥ w + σ c) k)) * p + x by ring] at this
      exact this

/-- **Reduction theorem**, for a shift vanishing on the cell rows. -/
theorem sep_of_certS (hr : r = 1 ∨ r = 2) (hk : 2 ≤ k) (hp : 2 ≤ p) (R : Rows) (Rg : Fin 3 → ℕ)
    (T : ℕ) (hcert : checkAll ⟨p, r, Rg, R⟩ T = true) (hside : sideOK ⟨p, r, Rg, R⟩ T = true)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (σ : Fin 3 → Fin (3 * k + r) → ZMod p) (hσ : CellFree r k σ)
    (v w : Fin (3 * k + r) → ZMod p) (hvw : v ≠ w) :
    T * (p ^ (3 * k + r - (k + 2))) ^ 2 ≤
      torusDist2 (p ^ (3 * k + r)) (fun c => coord p (3 * k + r) 1 (C c *ᵥ v + σ c))
        (fun c => coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) := by
  haveI : NeZero p := ⟨by omega⟩
  set u := p ^ (3 * k + r - (k + 2)) with hu
  have hu0 : 0 < u := by positivity
  set δ : Fin 3 → ℤ := fun d => cen (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d) with hδdef
  have hδ : ∀ d, δ d = cen (p ^ depth r k d) ((nC r k v d : ℤ) - nC r k w d) := fun d => rfl
  have hS := fun c => sideOK_sound _ T hside c
  by_cases hfar : ∃ c, (Rg c : ℤ) < |δ c|
  · obtain ⟨c, hc⟩ := hfar
    have hfb := far_boundS hr R.sk C hC.1 σ hσ v w c
    rw [← hδ c] at hfb
    have hcres : T * u ^ 2 ≤ cres (p ^ (3 * k + r))
        ((coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) - coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) ^ 2 := by
      set cr := cres (p ^ (3 * k + r))
        ((coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) - coord p (3 * k + r) 1 (C c *ᵥ w + σ c))
      by_cases hcr : (c : ℕ) < r
      · have hd : depth r k c = k + 1 := by unfold depth; rw [if_pos hcr]
        have hU : p ^ (3 * k + r - depth r k c) = p * u := by
          rw [hd, hu, ← pow_succ']; congr 1; omega
        rw [hU] at hfb
        have hT := (hS c).2.2.2.1 (by simp [Design.full, hcr])
        have h1 : ((Rg c * p * u : ℕ) : ℤ) ≤ cr := by
          push_cast at hfb ⊢
          have hδ1 : (Rg c : ℤ) + 1 ≤ |δ c| := by omega
          have hpu : (0 : ℤ) ≤ (p : ℤ) * u := by positivity
          nlinarith
        have h2 : Rg c * p * u ≤ cr := by exact_mod_cast h1
        calc T * u ^ 2 ≤ (p * Rg c) ^ 2 * u ^ 2 := Nat.mul_le_mul_right _ hT
          _ = (Rg c * p * u) ^ 2 := by ring
          _ ≤ cr ^ 2 := Nat.pow_le_pow_left h2 2
      · have hd : depth r k c = k := by unfold depth; rw [if_neg hcr]
        have hU : p ^ (3 * k + r - depth r k c) = p * p * u := by
          rw [hd, hu, mul_assoc, ← pow_succ', ← pow_succ']; congr 1; omega
        rw [hU] at hfb
        obtain ⟨hR1, hT⟩ := (hS c).2.2.2.2 (by simp [Design.full, hcr])
        have h1 : ((p * p * u : ℕ) : ℤ) ≤ cr := by
          push_cast at hfb ⊢
          have hR1' : Rg c = 1 := hR1
          rw [hR1'] at hc
          have hδ1 : (2 : ℤ) ≤ |δ c| := by push_cast at hc; omega
          have hpu : (0 : ℤ) ≤ (p : ℤ) * p * u := by positivity
          nlinarith
        have h2 : p * p * u ≤ cr := by exact_mod_cast h1
        calc T * u ^ 2 ≤ (p * p) ^ 2 * u ^ 2 := Nat.mul_le_mul_right _ hT
          _ = (p * p * u) ^ 2 := by ring
          _ ≤ cr ^ 2 := Nat.pow_le_pow_left h2 2
    exact le_trans hcres (cres_le_torus _ (fun c => coord p (3 * k + r) 1 (C c *ᵥ v + σ c))
      (fun c => coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) c)
  · push Not at hfar
    have hsmall : ∀ d, |δ d| < p := fun d => lt_of_le_of_lt (hfar d) (by exact_mod_cast (hS d).1)
    obtain ⟨ch, hch, hch0, hD⟩ := near_patterns hp hr (by omega) v w δ hδ hsmall
    have hRs : ∀ d : Fin 3, r ≤ (d : ℕ) → Rg d = 1 := fun d hd =>
      ((hS d).2.2.2.2 (by simp [Design.full]; omega)).1
    have hterm := fun c => near_termS hr hk hp R Rg C hC σ hσ v w δ hδ hfar (fun d => (hS d).1) hRs ch hch hD c
    have hne : ¬(δ 0 = 0 ∧ δ 1 = 0 ∧ δ 2 = 0) := by
      rintro ⟨h0, h1, h2⟩
      apply hvw
      refine eq_of_nC_eq hr v w fun d => nC_eq_of_cen_zero v w d ?_
      rw [← hδ d]
      fin_cases d <;> assumption
    have hT := checkAll_sound _ T hcert δ ch (fun d => abs_le.mp (hfar d))
      (fun d => mem_chains _ _ _ (hch0 d) (lt_of_lt_of_le (hch d) (min_le_right _ _))) hne
    have hsq : ∀ c : Fin 3, term ⟨p, r, Rg, R⟩ δ ch c ^ 2 * u ^ 2 ≤
        cres (p ^ (3 * k + r)) ((coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) -
          coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) ^ 2 := by
      intro c
      have h := hterm c
      have h' : term ⟨p, r, Rg, R⟩ δ ch c * u ≤
          cres (p ^ (3 * k + r)) ((coord p (3 * k + r) 1 (C c *ᵥ v + σ c) : ℤ) -
            coord p (3 * k + r) 1 (C c *ᵥ w + σ c)) := by
        exact_mod_cast h
      calc term ⟨p, r, Rg, R⟩ δ ch c ^ 2 * u ^ 2 = (term ⟨p, r, Rg, R⟩ δ ch c * u) ^ 2 := by ring
        _ ≤ _ := Nat.pow_le_pow_left h' 2
    unfold torusDist2
    rw [Fin.sum_univ_three]
    unfold total at hT
    calc T * u ^ 2 ≤ (term ⟨p, r, Rg, R⟩ δ ch 0 ^ 2 + term ⟨p, r, Rg, R⟩ δ ch 1 ^ 2 +
          term ⟨p, r, Rg, R⟩ δ ch 2 ^ 2) * u ^ 2 := Nat.mul_le_mul_right _ hT
      _ = term ⟨p, r, Rg, R⟩ δ ch 0 ^ 2 * u ^ 2 + term ⟨p, r, Rg, R⟩ δ ch 1 ^ 2 * u ^ 2 +
          term ⟨p, r, Rg, R⟩ δ ch 2 ^ 2 * u ^ 2 := by ring
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add (hsq 0) (hsq 1)) (hsq 2)

/-! ## Re-indexing by the shifted cells (`lem:shift`) -/

/-- The cell part of a shift `τ`, placed on the index blocks: digit `off c + l` is `τ_c` at row `l < K_c`. -/
def cellShift (r k : ℕ) (τ : Fin 3 → Fin (3 * k + r) → ZMod p) : Fin (3 * k + r) → ZMod p := fun j =>
  if (j : ℕ) < depth r k 0 then vz (τ 0) j
  else if (j : ℕ) < depth r k 0 + depth r k 1 then vz (τ 1) ((j : ℕ) - depth r k 0)
  else vz (τ 2) ((j : ℕ) - (depth r k 0 + depth r k 1))

lemma vz_cellShift (hr : r = 1 ∨ r = 2) (τ : Fin 3 → Fin (3 * k + r) → ZMod p) (c : Fin 3) (l : ℕ)
    (hl : l < depth r k c) : vz (cellShift r k τ) (off r k c + l) = vz (τ c) l := by
  have ho := off_add_depth r k hr c
  have hlt : off r k c + l < 3 * k + r := by omega
  have e : vz (cellShift r k τ) (off r k c + l) = cellShift r k τ ⟨off r k c + l, hlt⟩ := by
    simp [vz, hlt]
  rw [e]
  simp only [cellShift]
  obtain ⟨c, hc⟩ := c
  interval_cases c <;> simp only [off] at hl hlt ⊢ <;> simp at hl hlt ⊢ <;>
    (try split_ifs) <;> (try intro) <;> first | (exfalso; omega) | (congr 1; omega) | rfl

/-- The residual shift `σ_c = τ_c − C_c γ` vanishes on the cell rows. -/
lemma cellFree_resid [NeZero p] (hr : r = 1 ∨ r = 2) (sk : Fin 3 → Fin 3 → Fin 4 → ℤ)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKNskel r p k sk C)
    (τ : Fin 3 → Fin (3 * k + r) → ZMod p) :
    CellFree r k (fun c => τ c - C c *ᵥ cellShift r k τ) := by
  intro c j hj
  rw [vz_sub]
  have h1 := graph_digit sk C hr hC (cellShift r k τ) c j hj
  unfold dg vv at h1
  rw [ZMod.val_injective p h1, vz_cellShift hr τ c j hj, sub_self]

end Z3NetKN.Geom

namespace Z3NetKN.Proofs

open Finset Matrix Z3NetKN.Relax Z3NetKN.Geom

/-- **`rem:ppshift`**, reduction-theorem form: the bound of `sep_of_cert` for every digital shift. -/
theorem sep_of_cert_shift {p r k : ℕ} (hr : r = 1 ∨ r = 2) (hk : 2 ≤ k) (hp : 2 ≤ p) (R : Rows)
    (Rg : Fin 3 → ℕ) (T : ℕ) (hcert : checkAll ⟨p, r, Rg, R⟩ T = true) (hside : sideOK ⟨p, r, Rg, R⟩ T = true)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (τ : Fin 3 → Fin (3 * k + r) → ZMod p) (v w : Fin (3 * k + r) → ZMod p) (hvw : v ≠ w) :
    T * (p ^ (3 * k + r - (k + 2))) ^ 2 ≤
      torusDist2 (p ^ (3 * k + r)) (Z3NetF.digPointShift p (3 * k + r) C τ v)
        (Z3NetF.digPointShift p (3 * k + r) C τ w) := by
  haveI : NeZero p := ⟨by omega⟩
  set γ := cellShift r k τ
  have e : ∀ u : Fin (3 * k + r) → ZMod p, Z3NetF.digPointShift p (3 * k + r) C τ u =
      fun c => coord p (3 * k + r) 1 (C c *ᵥ (u + γ) + (fun c => τ c - C c *ᵥ γ) c) := by
    intro u; funext c
    rw [shift_coord]
    congr 1
    beta_reduce
    rw [mulVec_add]; abel
  rw [e v, e w]
  exact sep_of_certS hr hk hp R Rg T hcert hside C hC _ (cellFree_resid hr R.sk C hC.1 τ) (v + γ) (w + γ)
    (fun h => hvw (add_right_cancel h))

/-- **`rem:ppshift`** (general form, as `ppsep_general`): every digital shift. -/
theorem ppsep_shift_core (p r k T : ℕ) (hp : p.Prime) (hk : (r = 1 ∧ 3 ≤ k) ∨ (r = 2 ∧ 2 ≤ k))
    (R : Rows) (Rg : Fin 3 → ℕ) (hcert : IsPPCert p r Rg R T)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p)) (hC : IsKN r p k R C)
    (τ : Fin 3 → Fin (3 * k + r) → ZMod p) (v w : Fin (3 * k + r) → ZMod p) (hvw : v ≠ w) :
    T * (p ^ (3 * k + r - (k + 2))) ^ 2 ≤
      torusDist2 (p ^ (3 * k + r)) (Z3NetF.digPointShift p (3 * k + r) C τ v)
        (Z3NetF.digPointShift p (3 * k + r) C τ w) :=
  sep_of_cert_shift (by omega) (by omega) hp.two_le R Rg T
    (checkAll_of_isCert _ T (isCert_of p r Rg R T hcert)) (sideOK_of_isCert _ T (isCert_of p r Rg R T hcert))
    C hC τ v w hvw

/-- **`rem:ppshift`**, the designs of `table1` (`m ≡ 1`): the bound of `KN1_sep` for every digital shift. -/
theorem KN1_sep_shift_core (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table1) (k : ℕ) (hk : 3 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p)) (hC : IsKN 1 p k R C)
    (τ : Fin 3 → Fin (3 * k + 1) → ZMod p) (v w : Fin (3 * k + 1) → ZMod p) (hvw : v ≠ w) :
    T * p ^ (4 * k - 2) ≤
      torusDist2 (p ^ (3 * k + 1)) (Z3NetF.digPointShift p (3 * k + 1) C τ v)
        (Z3NetF.digPointShift p (3 * k + 1) C τ w) := by
  obtain ⟨⟨h1, h2⟩, hp⟩ := table1_cert _ hmem
  have := sep_of_cert_shift (Or.inl rfl) (by omega) hp R (rg1 p) T h1 h2 C hC τ v w hvw
  rwa [← pow_mul, show (3 * k + 1 - (k + 2)) * 2 = 4 * k - 2 by omega] at this

/-- **`rem:ppshift`**, the designs of `table2` (`m ≡ 2`): the bound of `KN2_sep` for every digital shift. -/
theorem KN2_sep_shift_core (p T : ℕ) (R : Rows) (hmem : (p, T, R) ∈ table2) (k : ℕ) (hk : 2 ≤ k)
    (C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p)) (hC : IsKN 2 p k R C)
    (τ : Fin 3 → Fin (3 * k + 2) → ZMod p) (v w : Fin (3 * k + 2) → ZMod p) (hvw : v ≠ w) :
    T * p ^ (4 * k) ≤
      torusDist2 (p ^ (3 * k + 2)) (Z3NetF.digPointShift p (3 * k + 2) C τ v)
        (Z3NetF.digPointShift p (3 * k + 2) C τ w) := by
  obtain ⟨⟨h1, h2⟩, hp⟩ := table2_cert _ hmem
  have := sep_of_cert_shift (Or.inr rfl) hk hp R (rg2 p) T h1 h2 C hC τ v w hvw
  rwa [← pow_mul, show (3 * k + 2 - (k + 2)) * 2 = 4 * k by omega] at this

end Z3NetKN.Proofs

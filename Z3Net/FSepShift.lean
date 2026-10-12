/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.FSep
public import Z3Net.DShift

@[expose] public section

/-!
# V14 stage S10′: `lem:Ss` for affine graph forms (`prop:shift`, the core)

The proof of `lem:Ss` (`Z3Net/FSep.lean`) for the graph form `Φ` with an additive constant `γ` on
the offset digits (`γ` vanishes on the cell digits): the digits of coordinate `c` of the point with
index `v` are `G_c v + γ_c`. Only differences of digits enter the proof, so `γ` cancels: the change of
the first offset digit under a step (`Dg_off_subA`) and the equality of the deeper digits when only
the own axis moves (`tl_eq_of_onlyA`) are those of the unshifted form. The cell machinery of `FSep`
(steps, carries, far steps) is about the index and is reused as is. By `lem:shift` every digitally
shifted graph form is such an affine form (`Z3Net/FSepShift2.lean`).

This is the single "the relaxation of `lem:Ss` is shift-invariant" lemma (`Ss_sep_coreA`,
`Ss_coord_coreA`) through which `prop:D`, `thm:A`(2) and their shifted forms go.
-/

namespace Z3NetF.Proofs

open Finset Matrix

noncomputable section

set_option linter.unusedSectionVars false

section aff

variable (s q k : ℕ) [NeZero q] (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
  (γ : Fin s → Fin (s * k) → ZMod q)

/-- Digits of coordinate `c`. -/
def DgA (c : Fin s) (v : Fin (s * k) → ZMod q) : Fin (s * k) → ZMod q := Z3NetU.graphGen s k Φ c *ᵥ v + γ c

/-- First offset digit and tail of coordinate `c`. -/
def o0A (v : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := Z3NetU.Proofs.dv s q k (DgA s q k Φ γ c v) k
def tlA (v : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := Z3NetU.Proofs.tail s q k (DgA s q k Φ γ c v)

variable (hγ : ∀ c (i : Fin (s * k)), (i : ℕ) < k → γ c i = 0)
include hγ

lemma cell_partA (v : Fin (s * k) → ZMod q) (c : Fin s) :
    ∑ i ∈ range k, Z3NetU.Proofs.dv s q k (DgA s q k Φ γ c v) i * q ^ (k - 1 - i) =
      Z3NetU.Proofs.cellN s q k v c := by
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  congr 1
  have hik : i < s * k := lt_of_lt_of_le hi (Z3NetU.Proofs.k_le_sk k c)
  simp only [Z3NetU.Proofs.dv, Z3NetU.Proofs.ad, dif_pos hi, dif_pos hik, DgA]
  rw [Pi.add_apply, Z3NetU.Proofs.graphGen_cell k Φ c v i hi, hγ c _ hi, add_zero]

lemma X_decompA (hsk : k + 1 ≤ s * k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    (Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v c : ℤ) =
      (q : ℤ) ^ (s * k - k) * Z3NetU.Proofs.cellN s q k v c +
        ((q : ℤ) ^ (s * k - k - 1) * o0A s q k Φ γ v c + tlA s q k Φ γ v c) := by
  rw [graphGenK_const]
  show ((∑ j : Fin (s * k), ((Z3NetU.graphGen s k Φ c *ᵥ v + γ c) j).val * q ^ (s * k - 1 - (j : ℕ)) : ℕ) : ℤ) = _
  rw [Z3NetU.Proofs.coord_split s q k hsk, show (Z3NetU.graphGen s k Φ c *ᵥ v + γ c) = DgA s q k Φ γ c v from rfl,
    cell_partA s q k Φ γ hγ]
  push_cast
  simp only [o0A, tlA]
  ring

lemma low_ltA (hsk : k + 1 ≤ s * k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    q ^ (s * k - k - 1) * o0A s q k Φ γ v c + tlA s q k Φ γ v c < q ^ (s * k - k) := by
  have h1 := Z3NetU.Proofs.dv_lt s q k (DgA s q k Φ γ c v) k
  have h2 := Z3NetU.Proofs.tail_lt s q k hsk (DgA s q k Φ γ c v)
  have e : q ^ (s * k - k) = q ^ (s * k - k - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  rw [e]
  simp only [o0A, tlA]
  nlinarith

lemma cell_of_digPointA (hsk : k + 1 ≤ s * k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v c / q ^ (s * k - k) =
      Z3NetU.Proofs.cellN s q k v c ∧
    Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v c % q ^ (s * k - k) =
      q ^ (s * k - k - 1) * o0A s q k Φ γ v c + tlA s q k Φ γ v c := by
  have hX := X_decompA s q k Φ γ hγ hsk v c
  have hX' : Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v c =
      q ^ (s * k - k) * Z3NetU.Proofs.cellN s q k v c +
        (q ^ (s * k - k - 1) * o0A s q k Φ γ v c + tlA s q k Φ γ v c) := by exact_mod_cast hX
  have hl := low_ltA s q k Φ γ hγ hsk v c
  have hp : 0 < q ^ (s * k - k) := pow_pos (Nat.pos_of_neZero q) _
  rw [hX']
  constructor
  · rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hl, add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hl]


lemma o0_castA (v : Fin (s * k) → ZMod q) (c : Fin s) (hk : k < s * k) :
    ((o0A s q k Φ γ v c : ℕ) : ZMod q) = DgA s q k Φ γ c v ⟨k, hk⟩ := by
  simp only [o0A, Z3NetU.Proofs.dv, dif_pos hk, ZMod.natCast_zmod_val]



/-- Offset digits change as in the unshifted graph form (the constant `γ` cancels). -/
lemma Dg_off_subA (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ) (hL : 1 ≤ L) (hLk : L ≤ k) (h1 : Z3NetF.H1 F L Φ) (c : Fin s)
    (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ) (J : Fin s → ℕ) (hJ : ∀ d, J d < k)
    (hstep : ∀ d, AxisStepF s q k v w d (e d) (J d)) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) :
    DgA s q k Φ γ c w ⟨k + r, Z3NetU.Proofs.sk_sub_add r⟩ - DgA s q k Φ γ c v ⟨k + r, Z3NetU.Proofs.sk_sub_add r⟩ =
      ((∑ d, e d * Z3NetF.Msum F (min (J d) (L - 1)) c d : ℤ) : ZMod q) := by
  simp only [DgA, Pi.add_apply, add_sub_add_right_eq_sub]
  exact Dg_off_subF s q k Φ F L hL hLk h1 c v w e J hJ hstep r hr

/-- (H2): if no other axis moves, the tail of coordinate `c` does not change. -/
lemma tl_eq_of_onlyA (hq : 1 < q) (h2 : Z3NetF.H2 Φ) (c : Fin s) (v w : Fin (s * k) → ZMod q)
    (hother : ∀ d, d ≠ c → Z3NetU.Proofs.cellN s q k w d = Z3NetU.Proofs.cellN s q k v d) :
    tlA s q k Φ γ w c = tlA s q k Φ γ v c := by
  unfold tlA Z3NetU.Proofs.tail
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_Ico] at hj
  congr 1
  unfold Z3NetU.Proofs.dv
  rw [dif_pos hj.2, dif_pos hj.2]
  have hj' : (⟨j, hj.2⟩ : Fin (s * k)) =
      ⟨k + ((⟨j - k, by omega⟩ : Fin (s * k - k)) : ℕ), Z3NetU.Proofs.sk_sub_add ⟨j - k, by omega⟩⟩ := by
    ext; simp; omega
  rw [hj']
  have e1 := Z3NetU.Proofs.graphGen_off k Φ c w ⟨j - k, by omega⟩
  have e2 := Z3NetU.Proofs.graphGen_off k Φ c v ⟨j - k, by omega⟩
  change ((Z3NetU.graphGen s k Φ c *ᵥ w + γ c) _).val = ((Z3NetU.graphGen s k Φ c *ᵥ v + γ c) _).val
  rw [Pi.add_apply, Pi.add_apply, e1, e2]
  congr 2
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  by_cases hd : d = c
  · subst hd; rw [h2 d _ (by simp; omega) l]; simp
  · rw [Z3NetU.Proofs.digits_eq_of_cellN_eq s q hq k v w d (hother d hd) l]

variable (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ)

/-- The core per-coordinate bound of `lem:Ss`, in terms of digits. -/
lemma coord_coreA (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ)
    (J : Fin s → ℕ) (hJ : ∀ d, J d < k) (hstep : ∀ d, AxisStepF s q k v w d (e d) (J d))
    (hzero : ∀ d, e d = 0 → Z3NetU.Proofs.cellN s q k w d = Z3NetU.Proofs.cellN s q k v d)
    (i : Fin s) :
    Z3NetF.bval q F L e J i * (q : ℤ) ^ (s * k - k - 1) ≤
      |(q : ℤ) ^ (s * k - k - 1) * (e i * q + ((o0A s q k Φ γ w i : ℤ) - o0A s q k Φ γ v i)) +
        ((tlA s q k Φ γ w i : ℤ) - tlA s q k Φ γ v i)| := by
  have hq0 : 0 < q := by omega
  have hsk : k + 1 ≤ s * k := by nlinarith
  have hkk : k < s * k := by omega
  set u : ℤ := (q : ℤ) ^ (s * k - k - 1) with hu_def
  have hu : 0 < u := by positivity
  set tt : ℤ := (o0A s q k Φ γ w i : ℤ) - o0A s q k Φ γ v i with htt
  -- `tt ≡ σ_i`, `|tt| < q`
  have htq : |tt| < q := by
    have a1 := Z3NetU.Proofs.dv_lt s q k (DgA s q k Φ γ i w) k
    have a2 := Z3NetU.Proofs.dv_lt s q k (DgA s q k Φ γ i v) k
    simp only [htt, o0A]
    rw [abs_lt]; constructor <;> omega
  have hσ : tt ≡ Z3NetF.sigma F L e J i [ZMOD q] := by
    have h := Dg_off_subA s q k Φ γ hγ F L hL hLk h1 i v w e J hJ hstep ⟨0, by omega⟩ rfl
    have e1 := o0_castA s q k Φ γ hγ w i hkk
    have e2 := o0_castA s q k Φ γ hγ v i hkk
    rw [← ZMod.intCast_eq_intCast_iff]
    simp only [htt, Z3NetF.sigma]
    push_cast
    rw [e1, e2]
    simpa using h
  have hb := bval_le_of s q F L hq0 e J i tt hσ htq
  have htl : |(tlA s q k Φ γ w i : ℤ) - tlA s q k Φ γ v i| < u := by
    have a1 := Z3NetU.Proofs.tail_lt s q k hsk (DgA s q k Φ γ i w)
    have a2 := Z3NetU.Proofs.tail_lt s q k hsk (DgA s q k Φ γ i v)
    have a1' : ((tlA s q k Φ γ w i : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast a1
    have a2' : ((tlA s q k Φ γ v i : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast a2
    rw [abs_lt]; constructor <;> omega
  have hbu : Z3NetF.bval q F L e J i * u ≤
      max 0 (|e i * q + tt| - if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then 0 else 1) * u :=
    mul_le_mul_of_nonneg_right hb hu.le
  refine hbu.trans ?_
  split_ifs with hj
  · have htl0 : (tlA s q k Φ γ w i : ℤ) - tlA s q k Φ γ v i = 0 := by
      rw [tl_eq_of_onlyA s q k Φ γ hγ (by omega) h2 i v w (fun d hd => hzero d (hj.2 d hd))]; ring
    rw [htl0, add_zero, sub_zero, abs_mul, abs_of_pos hu, max_eq_right (abs_nonneg _), mul_comm]
  · have a := abs_add_le (u * (e i * q + tt) + ((tlA s q k Φ γ w i : ℤ) - tlA s q k Φ γ v i))
      (-((tlA s q k Φ γ w i : ℤ) - tlA s q k Φ γ v i))
    rw [add_neg_cancel_right, abs_neg, abs_mul, abs_of_pos hu] at a
    rcases le_total (|e i * q + tt| - 1) 0 with hc | hc
    · rw [max_eq_left hc, zero_mul]; exact abs_nonneg _
    · rw [max_eq_right hc]; nlinarith


theorem Ss_coord_coreA (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ)
    (he : ∀ d, -1 ≤ e d ∧ e d ≤ 1)
    (hcell : ∀ d, ((Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ w d /
        q ^ (s * k - k) : ℕ) : ℤ) = ((Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v d /
        q ^ (s * k - k) : ℕ) + e d) % (q ^ k : ℕ))
    (i : Fin s) :
    Z3NetF.bval q F L e (fun d => Z3NetF.carryLen q k (Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k)
        (fun _ => k) Φ) γ v d / q ^ (s * k - k)) (e d)) i * (q ^ (s * k - k) : ℕ) ≤
      (q : ℤ) * |e i * (q ^ (s * k - k) : ℕ) +
        ((Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ w i % q ^ (s * k - k) : ℕ) : ℤ) -
        ((Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v i % q ^ (s * k - k) : ℕ) : ℤ)| := by
  have hsk : k + 1 ≤ s * k := by nlinarith
  have hcv := fun d => cell_of_digPointA s q k Φ γ hγ hsk v d
  have hcw := fun d => cell_of_digPointA s q k Φ γ hγ hsk w d
  simp only [(hcv _).1, (hcw _).1, (hcv _).2, (hcw _).2] at hcell ⊢
  have hax := fun d => axis_of_cell s q k hq hk v w d (e d) (he d) (by exact_mod_cast hcell d)
  have hcore := coord_coreA s q k Φ γ hγ F L hs hq (by omega) hL hLk h1 h2 v w e
    (fun d => Z3NetF.carryLen q k (Z3NetU.Proofs.cellN s q k v d) (e d))
    (fun d => carryLen_lt q k (by omega) _ _) (fun d => (hax d).1) (fun d => (hax d).2) i
  have hpow : ((q ^ (s * k - k) : ℕ) : ℤ) = (q : ℤ) ^ (s * k - k - 1) * q := by
    push_cast; rw [← pow_succ]; congr 1; omega
  rw [hpow]
  push_cast
  have e1 : e i * ((q : ℤ) ^ (s * k - k - 1) * q) + ((q : ℤ) ^ (s * k - k - 1) * o0A s q k Φ γ w i + tlA s q k Φ γ w i) -
      ((q : ℤ) ^ (s * k - k - 1) * o0A s q k Φ γ v i + tlA s q k Φ γ v i) =
      (q : ℤ) ^ (s * k - k - 1) * (e i * q + ((o0A s q k Φ γ w i : ℤ) - o0A s q k Φ γ v i)) +
        ((tlA s q k Φ γ w i : ℤ) - tlA s q k Φ γ v i) := by ring
  rw [e1]
  have hq0 : (0 : ℤ) ≤ q := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcore hq0]


lemma sep_mainA (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, Z3NetF.IsConfig k e j → B ≤ ∑ i, Z3NetF.bval q F L e j i ^ 2)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ 2 * ∑ c : Fin s,
      ((Z3NetU.cres (q ^ (s * k))
        ((Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ w c : ℤ) -
         (Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  have hq1 : 1 < q := by omega
  have hsk : k + 1 ≤ s * k := by nlinarith
  have hM1 : 1 ≤ (s * k - k) := by omega
  set u : ℤ := (q : ℤ) ^ ((s * k - k) - 1) with hu_def
  have hu : 0 < u := by positivity
  have hpow : (q : ℤ) ^ (s * k - k) = u * q := by rw [hu_def, ← pow_succ]; congr 1; omega
  have hN : ((q ^ (s * k) : ℕ) : ℤ) = (q : ℤ) ^ (s * k - k) * (q : ℤ) ^ k := by
    push_cast; rw [← pow_add]; congr 1; omega
  -- the torus period in cells is `G = q^k ≥ 3` (`k ≥ 1`); this is the only use of `k`
  have hqk : (3 : ℤ) ≤ (q : ℤ) ^ k := by
    have h3 : (3 : ℤ) ≤ q := by exact_mod_cast hq
    calc (3 : ℤ) ≤ (q : ℤ) ^ 1 := by simpa using h3
      _ ≤ (q : ℤ) ^ k := pow_le_pow_right₀ (by omega) hk
  set X : (Fin (s * k) → ZMod q) → Fin s → ℕ :=
    Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ with hXdef
  have hX : ∀ c, (X w c : ℤ) - X v c =
      (q : ℤ) ^ (s * k - k) * ((Z3NetU.Proofs.cellN s q k w c : ℤ) - Z3NetU.Proofs.cellN s q k v c) +
      (u * ((o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c) + ((tlA s q k Φ γ w c : ℤ) - tlA s q k Φ γ v c)) := by
    intro c; rw [hXdef, X_decompA s q k Φ γ hγ hsk, X_decompA s q k Φ γ hγ hsk]; ring
  have htl : ∀ c, |(tlA s q k Φ γ w c : ℤ) - tlA s q k Φ γ v c| < u := by
    intro c
    have a1 := Z3NetU.Proofs.tail_lt s q k hsk (DgA s q k Φ γ c w)
    have a2 := Z3NetU.Proofs.tail_lt s q k hsk (DgA s q k Φ γ c v)
    have a1' : ((tlA s q k Φ γ w c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast a1
    have a2' : ((tlA s q k Φ γ v c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast a2
    rw [abs_lt]; constructor <;> omega
  have ho : ∀ c, |(o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c| < q := by
    intro c
    have a1 := Z3NetU.Proofs.dv_lt s q k (DgA s q k Φ γ c w) k
    have a2 := Z3NetU.Proofs.dv_lt s q k (DgA s q k Φ γ c v) k
    simp only [o0A]
    rw [abs_lt]; constructor <;> omega
  have hsum_nonneg : ∀ c ∈ (univ : Finset (Fin s)), (0 : ℤ) ≤
      ((Z3NetU.cres (q ^ (s * k)) ((X w c : ℤ) - (X v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
    fun c _ => sq_nonneg _
  have hu2 : (q : ℤ) ^ (2 * (s * k - k)) = (q : ℤ) ^ 2 * u ^ 2 := by
    rw [hu_def, ← pow_mul, ← pow_add]; congr 1; omega
  by_cases hfar : ∃ c, ∀ z : ℤ, 2 ≤ |(Z3NetU.Proofs.cellN s q k w c : ℤ) -
      Z3NetU.Proofs.cellN s q k v c - z * (q : ℤ) ^ k|
  · obtain ⟨c, hc⟩ := hfar
    have hR : |u * ((o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c) + ((tlA s q k Φ γ w c : ℤ) - tlA s q k Φ γ v c)| <
        (q : ℤ) ^ (s * k - k) := by
      have a2 := abs_add_le (u * ((o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c)) ((tlA s q k Φ γ w c : ℤ) - tlA s q k Φ γ v c)
      rw [abs_mul, abs_of_pos hu] at a2
      have := htl c
      have b1 : |(o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c| ≤ q - 1 := by have := ho c; omega
      rw [hpow]; nlinarith
    have hf := Z3NetU.Proofs.far_gen (q ^ (s * k)) ((q : ℤ) ^ (s * k - k)) ((q : ℤ) ^ k) (by positivity) (by positivity)
      hN _ _ hR hc
    rw [← hX c] at hf
    have hsq : ((q : ℤ) ^ (s * k - k)) ^ 2 ≤
        ((Z3NetU.cres (q ^ (s * k)) ((X w c : ℤ) - (X v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hf 2
    have hsingle := Finset.single_le_sum hsum_nonneg (mem_univ c)
    calc (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ (2 * (s * k - k)) * (q : ℤ) ^ 2 := by gcongr
      _ = (q : ℤ) ^ 2 * ((q : ℤ) ^ (s * k - k)) ^ 2 := by rw [← pow_mul]; ring
      _ ≤ _ := by gcongr; exact hsq.trans hsingle
  · have hnf : ∀ c, ¬ ∀ z : ℤ, 2 ≤ |(Z3NetU.Proofs.cellN s q k w c : ℤ) -
        Z3NetU.Proofs.cellN s q k v c - z * (q : ℤ) ^ k| := fun c h => hfar ⟨c, h⟩
    choose e he hcell hax hzero using fun c => axis_classifyF s q k hq hk v w c (hnf c)
    by_cases hall : ∀ c, e c = 0
    · exact absurd (Z3NetU.Proofs.eq_of_cellN s q hq1 k v w (fun d => hzero d (hall d))).symm hvw
    push_neg at hall
    set J : Fin s → ℕ := fun c => Z3NetF.carryLen q k (Z3NetU.Proofs.cellN s q k v c) (e c)
    have hJ : ∀ c, J c < k := fun c => carryLen_lt q k (by omega) _ _
    have hcfg : Z3NetF.IsConfig k e J := ⟨he, hall, hJ⟩
    have hcore := fun c => coord_coreA s q k Φ γ hγ F L hs hq (by omega) hL hLk h1 h2 v w e J hJ hax hzero c
    -- the raw difference in coordinate `c`, in units of `q^(m-k-1)`: `Y_c = u (e_c q + Δr_c) + Δf_c`
    set Y : Fin s → ℤ := fun c => u * (e c * q + ((o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c)) +
      ((tlA s q k Φ γ w c : ℤ) - tlA s q k Φ γ v c) with hYdef
    -- the toroidal residue of `X_c(w) - X_c(v)` is that of `Y_c`
    have hcresY : ∀ c, ((Z3NetU.cres (q ^ (s * k)) ((X w c : ℤ) - (X v c : ℤ)) : ℕ) : ℤ) =
        (Z3NetU.cres (q ^ (s * k)) (Y c) : ℤ) := by
      intro c
      set P : ℤ := ((q ^ k : ℕ) : ℤ)
      have hP : P = (q : ℤ) ^ k := by push_cast; rfl
      have hcz : (Z3NetU.Proofs.cellN s q k w c : ℤ) - Z3NetU.Proofs.cellN s q k v c =
          e c + (-(((Z3NetU.Proofs.cellN s q k v c : ℤ) + e c) / P)) * P := by
        rw [hcell c, Int.emod_def]; ring
      have hYc : (X w c : ℤ) - X v c = Y c +
          (-(((Z3NetU.Proofs.cellN s q k v c : ℤ) + e c) / P)) * ((q ^ (s * k) : ℕ) : ℤ) := by
        rw [hX c, hcz, hN, hP, hpow, hYdef]; ring
      rw [hYc, Z3NetU.Proofs.cres_add_mul]
    -- `|Y_c| ≤ 2 u q - 1`, while the period is `u q · q^k ≥ 3 u q`
    have hYb : ∀ c, |Y c| ≤ 2 * (u * q) - 1 := by
      intro c
      have hq0 : (0 : ℤ) < q := by positivity
      have b0 : |e c| ≤ 1 := abs_le.mpr ⟨(he c).1, (he c).2⟩
      have hec : |e c * q| ≤ q := by
        rw [abs_mul, abs_of_pos hq0]
        calc |e c| * q ≤ 1 * q := mul_le_mul_of_nonneg_right b0 hq0.le
          _ = q := one_mul _
      have hV : |e c * q + ((o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c)| ≤ 2 * q - 1 := by
        have h1 := abs_add_le (e c * q) ((o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c)
        have h2 := ho c
        linarith
      have h1 := abs_add_le (u * (e c * q + ((o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c)))
        ((tlA s q k Φ γ w c : ℤ) - tlA s q k Φ γ v c)
      rw [abs_mul, abs_of_pos hu] at h1
      have h2 := mul_le_mul_of_nonneg_left hV hu.le
      have h3 := htl c
      simp only [hYdef]
      linarith
    have hN3 : 3 * (u * q) ≤ ((q ^ (s * k) : ℕ) : ℤ) := by
      rw [hN, hpow]
      have : 0 < u * q := by positivity
      nlinarith
    by_cases hwrap : ∃ c, ((q ^ (s * k) : ℕ) : ℤ) < 2 * |Y c|
    · -- the toroidal case split of `lem:Ss` (needed only for `q^k < 4`): the toroidal distance in
      -- coordinate `c` is then more than one cell, since `|Y_c| < 2` cells and the period is `≥ 3` cells
      obtain ⟨c, hc⟩ := hwrap
      have hmid : u * q ≤ (Z3NetU.cres (q ^ (s * k)) (Y c) : ℤ) :=
        cres_ge_mid (q ^ (s * k)) (Y c) (u * q) (by positivity) (by linarith [hYb c])
          (by linarith [hYb c])
      have hsingle := Finset.single_le_sum hsum_nonneg (mem_univ c)
      have hsq : ((q : ℤ) ^ (s * k - k)) ^ 2 ≤
          ((Z3NetU.cres (q ^ (s * k)) ((X w c : ℤ) - (X v c : ℤ)) : ℕ) : ℤ) ^ 2 := by
        rw [hcresY c, hpow]; exact pow_le_pow_left₀ (by positivity) hmid 2
      calc (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ (2 * (s * k - k)) * (q : ℤ) ^ 2 := by gcongr
        _ = (q : ℤ) ^ 2 * ((q : ℤ) ^ (s * k - k)) ^ 2 := by rw [← pow_mul]; ring
        _ ≤ _ := by gcongr; exact hsq.trans hsingle
    push_neg at hwrap
    -- `cres = |u (e q + t) + Δtl|`
    have hcres : ∀ c, ((Z3NetU.cres (q ^ (s * k)) ((X w c : ℤ) - (X v c : ℤ)) : ℕ) : ℤ) =
        |u * (e c * q + ((o0A s q k Φ γ w c : ℤ) - o0A s q k Φ γ v c)) + ((tlA s q k Φ γ w c : ℤ) - tlA s q k Φ γ v c)| := by
      intro c
      rw [hcresY c, Z3NetU.Proofs.cres_eq_abs _ _ (hwrap c)]
    have hsq : ∀ c, (Z3NetF.bval q F L e J c * u) ^ 2 ≤
        ((Z3NetU.cres (q ^ (s * k)) ((X w c : ℤ) - (X v c : ℤ)) : ℕ) : ℤ) ^ 2 := by
      intro c
      rw [hcres c]
      exact pow_le_pow_left₀ (mul_nonneg (bval_nonneg q F L e J c) hu.le) (hcore c) 2
    calc (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ (2 * (s * k - k)) * ∑ c, Z3NetF.bval q F L e J c ^ 2 := by
          gcongr; exact hB e J hcfg
      _ = (q : ℤ) ^ 2 * ∑ c, (Z3NetF.bval q F L e J c * u) ^ 2 := by
          rw [hu2, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun c _ => hsq c

theorem Ss_sep_coreA (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, Z3NetF.IsConfig k e j → B ≤ ∑ i, Z3NetF.bval q F L e j i ^ 2)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ 2 *
      (Z3NetF.torusDist2 (q ^ (s * k)) (Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ v)
        (Z3NetF.digPointShift q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) γ w) : ℤ) := by
  have h := sep_mainA s q k Φ γ hγ F L hs hq hk hL hLk h1 h2 B hBq hB w v (Ne.symm hvw)
  unfold Z3NetF.torusDist2
  push_cast
  simpa [cres_eq] using h



end aff

end

end Z3NetF.Proofs

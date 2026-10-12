module
public import Mathlib
public import Z3Net.S1Net3

@[expose] public section

/-!
# Entry S1, part 6: the explicit net `𝒮¹_{k,p,ρ}` of Definition `def:S1` (`S1gen`)

The Challenge definitions `frameBox`, `framePsi`, `gaugeS1` are the proof-side `Bm`, `psi`, `Dm`
(`frameBox_eq`, `framePsi_eq`, `gaugeS1_eq`); `S1gen` differs from the proof net `Cg` only in the
own-block columns of the offset rows (move (a)), where every kernel vector of a box with an offset row
of `c` vanishes. So `S1gen` has the S1 skeleton row and the kernel property of `Cg`.
-/

namespace Z3NetS1.Proofs

open Finset Matrix

section Gen

variable (s k : ℕ)

local notation "MM" => s * k + (s - 1)

variable (p : ℕ)

lemma frameGen_eq (m : ℕ) (c : Fin s) : Z3NetS1.frameGen m c = Z3NetU.frameGen m c := by
  ext i l; unfold Z3NetS1.frameGen Z3NetU.frameGen Z3NetS1.place Z3NetU.place; rfl

lemma frameBox_eq (hs : 0 < s) : frameBox s k p = Bm s k p hs := by
  ext r col
  have hb : blk s k r < s := by unfold blk; omega
  have hlev : lev s k r < MM := by unfold lev; omega
  unfold frameBox Bm Fr
  rw [dif_pos hb]
  unfold ent
  rw [dif_pos ⟨hlev, col.isLt⟩, frameGen_eq]
  rfl

lemma framePsi_eq (hs : 0 < s) (hk : k < MM) : framePsi s k p = psi s k p hs hk := by
  unfold framePsi psi
  rw [frameBox_eq s k p hs]
  congr 1
  funext col
  rw [dif_pos hs]
  unfold ent
  rw [dif_pos ⟨hk, col.isLt⟩, frameGen_eq]
  rfl

lemma gaugeS1_eq (hs : 0 < s) (hk : k < MM) (ρ : ℕ) : gaugeS1 s k p ρ = Dm s k p hs hk ρ := by
  ext r col
  unfold gaugeS1 Dm LF
  rw [framePsi_eq s k p hs hk]

lemma blk_eq_cOf (hs : 0 < s) (col : ℕ) : blk s k col = (cOf s k hs col : ℕ) := rfl

/-- Offset entries of `S1gen` outside the own block are those of `F_c B⁻¹ G`. -/
lemma S1gen_off (hs : 0 < s) (hk : k < MM) (ρ : ℕ) (c : Fin s) (i col : Fin MM)
    (hi : ¬ (i : ℕ) < depth s k c) (hb : blk s k col ≠ (c : ℕ)) :
    S1gen s p k ρ c i col = (Fr s k p c * (Bm s k p hs)⁻¹ * Dm s k p hs hk ρ) i col := by
  unfold S1gen
  rw [if_neg hi, if_neg hb, frameBox_eq s k p hs, gaugeS1_eq s k p hs hk, frameGen_eq]
  rfl

/-- On the skeleton row, `F_z B⁻¹ G` is the S1 row outside the own block. -/
lemma skel_entry [Fact p.Prime] (hs : 0 < s) (hk : k < MM) (hps : s - 2 < p) (ρ : ℕ) (c : Fin s)
    (hc : (c : ℕ) + 1 = s) (col : Fin MM) (hb : blk s k col ≠ (c : ℕ)) :
    (Fr s k p c * (Bm s k p hs)⁻¹ * Dm s k p hs hk ρ) ⟨k, hk⟩ col =
      ((skRow s k ρ col : ℕ) : ZMod p) := by
  have hcz : c = zc s hs := Fin.ext (by simp [zc]; omega)
  subst hcz
  have e : (Fr s k p (zc s hs) * (Bm s k p hs)⁻¹ * Dm s k p hs hk ρ) ⟨k, hk⟩ col =
      (psi s k p hs hk ᵥ* Dm s k p hs hk ρ) col := rfl
  rw [e, psi_vecMul_Dm s k p hs hk hps ρ col, if_neg, add_zero]
  intro h
  apply hb
  unfold blk zc; simp only; omega

lemma S1gen_skel [Fact p.Prime] (hs : 0 < s) (hk : k < MM) (hps : s - 2 < p) (ρ : ℕ) :
    IsS1skel s p k ρ (S1gen s p k ρ) := by
  constructor
  · intro c j hj col hcol
    have hjm : j < MM := by have := off_add_depth s k c; omega
    unfold ent; rw [dif_pos ⟨hjm, hcol⟩]
    simp only [S1gen]; rw [if_pos hj]
  · intro z hz col hcol
    unfold ent; rw [dif_pos ⟨hk, hcol⟩]
    have hdz : ¬ k < depth s k z := by unfold depth; rw [if_neg (by omega)]; omega
    by_cases hb : blk s k col = (z : ℕ)
    · have h0 : skRow s k ρ col = 0 := by
        unfold skRow; rw [if_neg]; intro h; unfold blk at hb; omega
      unfold S1gen; simp only; rw [if_neg hdz, if_pos hb, h0]; simp
    · rw [S1gen_off s k p hs hk ρ z ⟨k, hk⟩ ⟨col, hcol⟩ hdz hb]
      exact skel_entry s k p hs hk hps ρ z hz ⟨col, hcol⟩ hb

theorem S1gen_kernel [Fact p.Prime] (hs : 0 < s) (hk : k < MM) (hps : s - 2 < p) (ρ : ℕ)
    (hρ : 1 ≤ ρ) (hρp : ρ ^ s < p) (d : Fin s → ℕ) (hd : ∑ c, d c = MM) (n : Fin MM → ZMod p)
    (h : ∀ c (i : Fin MM), (i : ℕ) < d c → (S1gen s p k ρ c *ᵥ n) i = 0) : n = 0 := by
  refine Cg_kernel s k p hs hk hps ρ hρ hρp d hd n fun c i hi => ?_
  by_cases hic : (i : ℕ) < depth s k c
  · have e : (Cg s k p hs hk ρ c *ᵥ n) i = (S1gen s p k ρ c *ᵥ n) i := by
      simp only [mulVec, dotProduct, Cg, S1gen, if_pos hic]
    rw [e]; exact h c i hi
  · -- `n` vanishes on the block of `c`
    have hvan : ∀ col : Fin MM, blk s k col = (c : ℕ) → n col = 0 := by
      intro col hcol
      have hc' : cOf s k hs col = c := Fin.ext hcol
      obtain ⟨h1, h2⟩ := off_jOf s k hs col col.isLt
      rw [hc'] at h1 h2
      have hlt : off k c + jOf s k hs col < MM := by omega
      have := h c ⟨jOf s k hs col, by omega⟩ (by simp only; omega)
      have e2 : (S1gen s p k ρ c *ᵥ n) ⟨jOf s k hs col, by omega⟩ = n ⟨off k c + jOf s k hs col, hlt⟩ := by
        simp only [mulVec, dotProduct, S1gen, if_pos h2]
        rw [sum_eq_single ⟨off k c + jOf s k hs col, hlt⟩]
        · simp
        · intro b _ hb; rw [if_neg (fun h' => hb (Fin.ext h')), zero_mul]
        · simp
      rw [e2] at this
      rw [← this]; congr 1; exact Fin.ext h1.symm
    have e : (Cg s k p hs hk ρ c *ᵥ n) i = (S1gen s p k ρ c *ᵥ n) i := by
      simp only [mulVec, dotProduct]
      refine sum_congr rfl fun col _ => ?_
      by_cases hb : blk s k col = (c : ℕ)
      · rw [hvan col hb, mul_zero, mul_zero]
      · rw [S1gen_off s k p hs hk ρ c i col hic hb]
        congr 1
        unfold Cg
        rw [if_neg hic]
        split_ifs with hz
        · have hik : i = ⟨k, hk⟩ := Fin.ext hz.2
          subst hik
          exact (skel_entry s k p hs hk hps ρ c hz.1 col hb).symm
        · rfl
    rw [e]; exact h c i hi

end Gen

/-- **`S1gen_net`**: the explicit net of Definition `def:S1` has the S1 skeleton row and is a
digital `(0, sk+s-1, s)`-net over `𝔽_p`. -/
theorem S1gen_net (s p k ρ : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p) :
    IsS1skel s p k ρ (S1gen s p k ρ) ∧
      IsNet0 s p (s * k + (s - 1)) (digPoint p (s * k + (s - 1)) (S1gen s p k ρ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hs0 : 0 < s := by omega
  have hk : k < s * k + (s - 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; nlinarith
  have hps : s - 2 < p := by
    have h1 : s < 2 ^ s := Nat.lt_two_pow_self
    have h2 : 2 ^ s ≤ ρ ^ s := Nat.pow_le_pow_left hρ s
    omega
  exact ⟨S1gen_skel s k p hs0 hk hps ρ,
    Z3NetU.Proofs.isNet0_of_kernel s p (s * k + (s - 1)) (S1gen s p k ρ)
      (fun d hd n hn => S1gen_kernel s k p hs0 hk hps ρ (by omega) hρp d hd n hn)⟩

end Z3NetS1.Proofs

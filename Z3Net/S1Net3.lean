module
public import Mathlib
public import Z3Net.S1Net2

@[expose] public section

/-!
# Entry S1, part 5: the gauge `Dm`, the net `Cg`, `S1_net`
-/

namespace Z3NetS1.Proofs

open Finset Matrix

section Net3

variable (s k : ℕ)

local notation "MM" => s * k + (s - 1)

variable (p : ℕ)

lemma Dm_mulVec_notLF (hs : 0 < s) (hk : k < MM) (ρ : ℕ) (r : Fin MM) (hr : ¬LF s k r)
    (n : Fin MM → ZMod p) : (Dm s k p hs hk ρ *ᵥ n) r = n r := by
  simp only [mulVec, dotProduct, Dm, if_neg hr]
  rw [sum_eq_single r]
  · simp
  · intro b _ hb; rw [if_neg hb, zero_mul]
  · simp

lemma Dm_mulVec_block (hs : 0 < s) (hk : k < MM) (ρ : ℕ) (r : Fin MM) (n : Fin MM → ZMod p)
    (h : ∀ col : Fin MM, (col : ℕ) / (k + 1) = (r : ℕ) / (k + 1) → n col = 0) :
    (Dm s k p hs hk ρ *ᵥ n) r = 0 := by
  simp only [mulVec, dotProduct]
  refine sum_eq_zero fun col _ => ?_
  by_cases hb : (col : ℕ) / (k + 1) = (r : ℕ) / (k + 1)
  · rw [h col hb, mul_zero]
  · have hne : col ≠ r := fun e => hb (by rw [e])
    have : Dm s k p hs hk ρ r col = 0 := by
      unfold Dm
      rw [if_neg hne, if_neg hne]
      split_ifs with h1 h2
      · exact absurd h2.1 hb
      · rfl
      · rfl
    rw [this, zero_mul]

lemma rho_pow_ne [Fact p.Prime] (ρ : ℕ) (hρ : 1 ≤ ρ) (hρp : ρ ^ s < p) (q : ℕ) (hq : q + 1 < s) :
    ((ρ ^ (q + 1) : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have h1 : 0 < ρ ^ (q + 1) := pow_pos (by omega) _
  have h2 : ρ ^ (q + 1) ≤ ρ ^ s := Nat.pow_le_pow_right (by omega) (by omega)
  have := Nat.le_of_dvd h1 hd
  omega

lemma Dm_ker [Fact p.Prime] (hs : 0 < s) (hk : k < MM) (hps : s - 2 < p) (ρ : ℕ) (hρ : 1 ≤ ρ)
    (hρp : ρ ^ s < p) (n : Fin MM → ZMod p) (h : Dm s k p hs hk ρ *ᵥ n = 0) : n = 0 := by
  have hnot : ∀ r : Fin MM, ¬LF s k r → n r = 0 := fun r hr => by
    rw [← Dm_mulVec_notLF s k p hs hk ρ r hr n, h]; rfl
  funext r
  by_cases hr : LF s k r
  · have e : (Dm s k p hs hk ρ *ᵥ n) r = Dm s k p hs hk ρ r r * n r := by
      simp only [mulVec, dotProduct]
      rw [sum_eq_single r]
      · intro col _ hcol
        by_cases hLc : LF s k col
        · have hb : ¬((col : ℕ) / (k + 1) = (r : ℕ) / (k + 1)) := by
            intro hb
            exact hcol (Fin.ext (blk_eq _ _ _ hb (by rw [hLc.1, hr.1])))
          have : Dm s k p hs hk ρ r col = 0 := by
            unfold Dm; rw [if_pos hr, if_neg hcol, if_neg (fun h' => hb h'.1)]
          rw [this, zero_mul]
        · rw [hnot col hLc, mul_zero]
      · simp
    have h0 : Dm s k p hs hk ρ r r * n r = 0 := by rw [← e, h]; rfl
    have hD : Dm s k p hs hk ρ r r ≠ 0 := by
      unfold Dm; rw [if_pos hr, if_pos rfl]
      exact mul_ne_zero (rho_pow_ne s p ρ hρ hρp _ hr.2) (inv_ne_zero (psi_ne s k p hs hk hps r hr))
    exact (mul_eq_zero.mp h0).resolve_left hD
  · exact hnot r hr

/-- The frame's skeleton row after the gauge: the S1 row on the full blocks, `ψ` on the own block. -/
lemma psi_vecMul_Dm [Fact p.Prime] (hs : 0 < s) (hk : k < MM) (hps : s - 2 < p) (ρ : ℕ)
    (col : Fin MM) :
    (psi s k p hs hk ᵥ* Dm s k p hs hk ρ) col = ((skRow s k ρ col : ℕ) : ZMod p) +
      (if s ≤ (col : ℕ) / (k + 1) + 1 then psi s k p hs hk col else 0) := by
  simp only [vecMul, dotProduct]
  have hmm := mm_eq s k hs
  by_cases hc : LF s k col
  · rw [sum_eq_single col]
    · unfold Dm; rw [if_pos hc, if_pos rfl, skRow_LF, if_pos hc, if_neg (by have := hc.2; omega),
        add_zero, mul_comm, mul_assoc, inv_mul_cancel₀ (psi_ne s k p hs hk hps col hc), mul_one]
    · intro r _ hr
      have : Dm s k p hs hk ρ r col = 0 := by
        unfold Dm
        split_ifs with h1 h2 h3 h4
        · exact absurd h2 (Ne.symm hr)
        · exfalso
          have := blk_le (r : ℕ) col (k + 1) h3.1.symm (by rw [hc.1]; have := Nat.mod_lt (r : ℕ) (show 0 < k + 1 by omega); omega)
          omega
        · rfl
        · exact absurd h4 (Ne.symm hr)
        · rfl
      rw [this, mul_zero]
    · simp
  · rw [skRow_LF, if_neg hc, Nat.cast_zero, zero_add]
    by_cases hfull : (col : ℕ) / (k + 1) + 1 < s
    · rw [if_neg (by omega)]
      have hr0 : ((col : ℕ) / (k + 1)) * (k + 1) + k < MM := by
        have : ((col : ℕ) / (k + 1) + 1) * (k + 1) ≤ (s - 1) * (k + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        nlinarith [hmm, this]
      set r0 : Fin MM := ⟨((col : ℕ) / (k + 1)) * (k + 1) + k, hr0⟩ with hr0def
      have hmod0 : (r0 : ℕ) % (k + 1) = k := by
        show ((col : ℕ) / (k + 1) * (k + 1) + k) % (k + 1) = k
        rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
      have hdiv0 : (r0 : ℕ) / (k + 1) = (col : ℕ) / (k + 1) := by
        show ((col : ℕ) / (k + 1) * (k + 1) + k) / (k + 1) = (col : ℕ) / (k + 1)
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (show k < k + 1 by omega),
          add_zero]
      have hLr0 : LF s k r0 := ⟨hmod0, by rw [hdiv0]; exact hfull⟩
      have hcmod : (col : ℕ) % (k + 1) < k := by
        have := Nat.mod_lt (col : ℕ) (show 0 < k + 1 by omega)
        have : ¬((col : ℕ) % (k + 1) = k) := fun h => hc ⟨h, hfull⟩
        omega
      have hne : col ≠ r0 := fun e => by
        have h1 : (col : ℕ) = r0 := congrArg Fin.val e
        have : (col : ℕ) % (k + 1) = (r0 : ℕ) % (k + 1) := by rw [h1]
        omega
      have hlt : (col : ℕ) < r0 := by
        have := blk_le (col : ℕ) r0 (k + 1) hdiv0.symm (by omega)
        have : (col : ℕ) ≠ r0 := fun h => hne (Fin.ext h)
        omega
      rw [sum_eq_add col r0 hne]
      · unfold Dm
        rw [if_neg hc, if_pos rfl, if_pos hLr0, if_neg hne, if_pos ⟨hdiv0.symm, hlt⟩]
        have := psi_ne s k p hs hk hps r0 hLr0
        field_simp
        ring
      · intro r _ hr
        have : Dm s k p hs hk ρ r col = 0 := by
          unfold Dm
          split_ifs with h1 h2 h3 h4
          · exact absurd h2.symm hr.1
          · exfalso
            apply hr.2
            exact Fin.ext (blk_eq _ _ _ (by rw [hdiv0, h3.1]) (by rw [h1.1, hmod0]))
          · rfl
          · exact absurd h4.symm hr.1
          · rfl
        rw [this, mul_zero]
      · simp
      · simp
    · rw [if_pos (by omega)]
      rw [sum_eq_single col]
      · unfold Dm; rw [if_neg hc, if_pos rfl, mul_one]
      · intro r _ hr
        have : Dm s k p hs hk ρ r col = 0 := by
          unfold Dm
          split_ifs with h1 h2 h3 h4
          · exact absurd h2.symm hr
          · exfalso; have := h1.2; omega
          · rfl
          · exact absurd h4.symm hr
          · rfl
        rw [this, mul_zero]
      · simp

/-- The net: coarse rows = unit vectors, skeleton row = the S1 row, other rows `Fr c Bm⁻¹ Dm`. -/
noncomputable def Cg (hs : 0 < s) (hk : k < MM) (ρ : ℕ) (c : Fin s) :
    Matrix (Fin MM) (Fin MM) (ZMod p) :=
  fun i col =>
    if (i : ℕ) < depth s k c then (if (col : ℕ) = off k c + i then 1 else 0)
    else if (c : ℕ) + 1 = s ∧ (i : ℕ) = k then ((skRow s k ρ col : ℕ) : ZMod p)
    else (Fr s k p c * (Bm s k p hs)⁻¹ * Dm s k p hs hk ρ) i col

lemma Cg_skel (hs : 0 < s) (hk : k < MM) (ρ : ℕ) : IsS1skel s p k ρ (Cg s k p hs hk ρ) := by
  constructor
  · intro c j hj col hcol
    have hjm : j < MM := by have := off_add_depth s k c; omega
    unfold ent; rw [dif_pos ⟨hjm, hcol⟩]
    simp only [Cg]; rw [if_pos hj]
  · intro z hz col hcol
    unfold ent; rw [dif_pos ⟨hk, hcol⟩]
    have hdz : depth s k z = k := by unfold depth; rw [if_neg (by omega)]
    simp [Cg, hdz, hz]

lemma Cg_coarse (hs : 0 < s) (hk : k < MM) (ρ : ℕ) (c : Fin s) (i : Fin MM)
    (hi : (i : ℕ) < depth s k c) (n : Fin MM → ZMod p) :
    (Cg s k p hs hk ρ c *ᵥ n) i =
      n ⟨off k c + i, lt_of_lt_of_le (Nat.add_lt_add_left hi _) (off_add_depth s k c)⟩ := by
  simp only [mulVec, dotProduct, Cg, if_pos hi]
  rw [sum_eq_single ⟨off k c + i, lt_of_lt_of_le (Nat.add_lt_add_left hi _) (off_add_depth s k c)⟩]
  · simp
  · intro b _ hb
    rw [if_neg (fun h => hb (Fin.ext h)), zero_mul]
  · simp

theorem Cg_kernel [Fact p.Prime] (hs : 0 < s) (hk : k < MM) (hps : s - 2 < p) (ρ : ℕ)
    (hρ : 1 ≤ ρ) (hρp : ρ ^ s < p) (d : Fin s → ℕ) (hd : ∑ c, d c = MM) (n : Fin MM → ZMod p)
    (h : ∀ c (i : Fin MM), (i : ℕ) < d c → (Cg s k p hs hk ρ c *ᵥ n) i = 0) : n = 0 := by
  have hdet := Bm_det s k p hs hps
  set V := (Bm s k p hs)⁻¹ *ᵥ (Dm s k p hs hk ρ *ᵥ n) with hV
  have hBV : Bm s k p hs *ᵥ V = Dm s k p hs hk ρ *ᵥ n := by
    rw [hV, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  -- n vanishes on block `c` once `d c ≥ depth c`
  have blockvan : ∀ c : Fin s, depth s k c ≤ d c → ∀ col : Fin MM, cOf s k hs col = c → n col = 0 := by
    intro c hc col hcol
    obtain ⟨h1, h2⟩ := off_jOf s k hs col col.isLt
    rw [hcol] at h1 h2
    have := Cg_coarse s k p hs hk ρ c ⟨jOf s k hs col, by omega⟩ h2 n
    rw [h c _ (by simp only; omega)] at this
    rw [this]; congr 1; exact Fin.ext h1.symm
  have hFV : ∀ c (i : Fin MM), (i : ℕ) < d c → (Fr s k p c *ᵥ V) i = 0 := by
    intro c i hi
    by_cases hic : (i : ℕ) < depth s k c
    · rw [← Bm_mulVec s k p hs c i hic, hBV]
      set r : Fin MM := ⟨off k c + i, lt_of_lt_of_le (Nat.add_lt_add_left hic _) (off_add_depth s k c)⟩
        with hr
      by_cases hLr : LF s k r
      · obtain ⟨hcr, hjr, hdr⟩ := LF_block s k hs r r.isLt hLr
        have hcc : cOf s k hs r = c := cOf_off s k hs c i hic
        have hjj : jOf s k hs r = i := jOf_off s k hs c i hic
        refine Dm_mulVec_block s k p hs hk ρ r n fun col hcol => ?_
        have hik : (i : ℕ) = k := by rw [← hjj, hjr]
        have hdc : depth s k c = k + 1 := by rw [← hcc, hdr]
        refine blockvan c (by omega) col ?_
        rw [← hcc]; apply Fin.ext; unfold cOf; simp only; rw [hcol]
      · rw [Dm_mulVec_notLF s k p hs hk ρ r hLr n, ← Cg_coarse s k p hs hk ρ c i hic n]
        exact h c i hi
    · by_cases hz : (c : ℕ) + 1 = s ∧ (i : ℕ) = k
      · have hcz : c = zc s hs := Fin.ext (by simp [zc]; omega)
        have hik : i = ⟨k, hk⟩ := Fin.ext hz.2
        subst hik
        have hdep : depth s k c ≤ d c := by
          have h1 : depth s k c = k := by rw [hcz]; exact depth_z s k hs
          have h2 : k < d c := hi
          omega
        have e1 : (Fr s k p c *ᵥ V) ⟨k, hk⟩ =
            ∑ col, (psi s k p hs hk ᵥ* Dm s k p hs hk ρ) col * n col := by
          have : (Fr s k p c *ᵥ V) ⟨k, hk⟩ =
              (fun col => Fr s k p (zc s hs) ⟨k, hk⟩ col) ⬝ᵥ V := by rw [hcz]; rfl
          rw [this, hV, dotProduct_mulVec, dotProduct_mulVec]
          rfl
        rw [e1]
        have e2 : ∀ col : Fin MM, (psi s k p hs hk ᵥ* Dm s k p hs hk ρ) col * n col =
            ((skRow s k ρ col : ℕ) : ZMod p) * n col := by
          intro col
          rw [psi_vecMul_Dm s k p hs hk hps ρ col]
          split_ifs with hb
          · have : n col = 0 := by
              refine blockvan c hdep col ?_
              rw [hcz]; apply Fin.ext; unfold cOf zc; simp only; omega
            rw [this, mul_zero, mul_zero]
          · rw [add_zero]
        rw [sum_congr rfl fun col _ => e2 col]
        have := h c ⟨k, hk⟩ hi
        simp [mulVec, dotProduct, Cg, hic, hz.1] at this
        exact this
      · have := h c i hi
        simp only [mulVec, dotProduct, Cg, if_neg hic, if_neg hz] at this
        rw [hV, mulVec_mulVec, mulVec_mulVec]
        exact this
  have hV0 := frame_kernel s k p hs hps d hd V hFV
  have hDn : Dm s k p hs hk ρ *ᵥ n = 0 := by rw [← hBV, hV0, mulVec_zero]
  exact Dm_ker s k p hs hk hps ρ hρ hρp n hDn

end Net3

/-- **Theorem S1, net part.** -/
theorem S1_net (s p k ρ : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p) :
    ∃ C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p),
      IsS1skel s p k ρ C ∧ IsNet0 s p (s * k + (s - 1)) (digPoint p (s * k + (s - 1)) C) := by
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
  refine ⟨Cg s k p hs0 hk ρ, Cg_skel s k p hs0 hk ρ, ?_⟩
  exact Z3NetU.Proofs.isNet0_of_kernel s p (s * k + (s - 1)) (Cg s k p hs0 hk ρ)
    (fun d hd n hn => Cg_kernel s k p hs0 hk hps ρ (by omega) hρp d hd n hn)

end Z3NetS1.Proofs

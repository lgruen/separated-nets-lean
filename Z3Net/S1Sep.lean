module
public import Mathlib
public import Z3Net.S1Defs
public import Z3Net.S1Lat
public import Z3Net.KNBsep

@[expose] public section

/-!
# Entry S1, part 2: separation (`S1_sep`)

Fine positions `P_c` = the first `k + 1` digits of coordinate `c` (`Z3NetKN.Geom.Pf`); `a_c` the
centred difference of `P_c` mod `p^(k+1)`. Graph form gives `P_c ≡ x_{c,k}` (full `c`) and
`P_z ≡ S_z = ∑ ρ^(d+1) x_{d,k}` (mod `p`), so `a ∈ Λ` (no faults); `a ≠ 0` since `P` determines
the index; Lemma L2_s gives some `|a_c| ≥ ρ`, and Lemma T (`Z3NetKN.Geom.prefix_bound`) gives
`cres_c ≥ (ρ - 1) p^(m-k-1)`. The KN digit/prefix toolkit is reused verbatim (its `coord`, `cres`,
`ent` are definitionally the S1 ones).
-/

namespace Z3NetS1.Proofs

open Finset Matrix Z3NetKN.Geom

variable {p : ℕ}

lemma ent_eq {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i j : ℕ) :
    Z3NetS1.ent A i j = Z3NetKN.ent A i j := rfl

lemma coord_eq (q m : ℕ) (C : Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) :
    Z3NetS1.coord q m C v = Z3NetKN.coord q m C v := rfl

lemma cres_eq (N : ℕ) (u : ℤ) : Z3NetS1.cres N u = Z3NetKN.cres N u := rfl

lemma cres_le_torus {s : ℕ} (N : ℕ) (x y : Fin s → ℕ) (c : Fin s) :
    Z3NetS1.cres N ((x c : ℤ) - (y c : ℤ)) ^ 2 ≤ Z3NetS1.torusDist2 N x y := by
  unfold Z3NetS1.torusDist2
  exact Finset.single_le_sum (f := fun c => Z3NetS1.cres N ((x c : ℤ) - (y c : ℤ)) ^ 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

/-! ## Layout -/

lemma depth_le (s k : ℕ) (c : Fin s) : depth s k c ≤ k + 1 := by
  unfold depth; split_ifs <;> omega

lemma off_add_depth (s k : ℕ) (c : Fin s) : off k c + depth s k c ≤ s * k + (s - 1) := by
  have hc := c.isLt
  unfold off depth
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have e1 : (t + 1) * k = t * k + k := by ring
  split_ifs with h
  · have : (c : ℕ) + 1 ≤ t := by omega
    have := Nat.mul_le_mul_right (k + 1) this
    simp only [Nat.add_sub_cancel]
    nlinarith
  · have : (c : ℕ) = t := by omega
    rw [this]
    simp only [Nat.add_sub_cancel]
    nlinarith

/-- Every index digit `col < m` lies in a block: `col = off k c + j`, `j < depth s k c`. -/
lemma blocks_cover (s k : ℕ) (hs : 1 ≤ s) (col : ℕ) (hcol : col < s * k + (s - 1)) :
    ∃ c : Fin s, ∃ j < depth s k c, col = off k c + j := by
  by_cases h : col < (s - 1) * (k + 1)
  · have hd : col / (k + 1) < s - 1 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    refine ⟨⟨col / (k + 1), by omega⟩, col % (k + 1), ?_, ?_⟩
    · unfold depth; rw [if_pos (by simp; omega)]; exact Nat.mod_lt _ (by omega)
    · unfold off; simp only; rw [Nat.mul_comm]; exact (Nat.div_add_mod col (k + 1)).symm
  · refine ⟨⟨s - 1, by omega⟩, col - (s - 1) * (k + 1), ?_, ?_⟩
    · unfold depth; rw [if_neg (by simp; omega)]
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at h hcol ⊢
      have e1 : (t + 1) * k = t * k + k := by ring
      have e2 : t * (k + 1) = t * k + t := by ring
      omega
    · unfold off; simp only; omega

/-! ## Digits of a graph-form net -/

section Graph

variable {s k ρ : ℕ} {C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p)}

lemma coarse_digit (hC : IsS1skel s p k ρ C) (v : Fin (s * k + (s - 1)) → ZMod p) (c : Fin s)
    (j : ℕ) (hj : j < depth s k c) : vz (C c *ᵥ v) j = vz v (off k c + j) := by
  have ho := off_add_depth s k c
  rw [mulVec_vz _ _ _ (by omega)]
  have : ∀ col ∈ range (s * k + (s - 1)), Z3NetKN.ent (C c) j col * vz v col =
      if col = off k c + j then vz v col else 0 := by
    intro col hcol
    simp only [mem_range] at hcol
    rw [← ent_eq, hC.1 c j hj col hcol]; split_ifs <;> simp
  rw [sum_congr rfl this, sum_ite_eq', if_pos (by simp only [mem_range]; omega)]

lemma skRow_full (s k ρ d l : ℕ) (hd : d + 1 < s) (hl : l < k + 1) :
    skRow s k ρ (d * (k + 1) + l) = if l = k then ρ ^ (d + 1) else 0 := by
  have e1 : (d * (k + 1) + l) % (k + 1) = l := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hl
  have e2 : (d * (k + 1) + l) / (k + 1) = d := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hl, add_zero]
  unfold skRow; rw [e1, e2]
  by_cases h : l = k
  · rw [if_pos ⟨h, hd⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma skRow_skel (s k ρ l : ℕ) (hs : 1 ≤ s) (hl : l < k) :
    skRow s k ρ ((s - 1) * (k + 1) + l) = 0 := by
  have e1 : ((s - 1) * (k + 1) + l) % (k + 1) = l := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
  unfold skRow; rw [e1, if_neg (fun h => by omega)]

/-- Splitting a sum over `range ((n)(k+1))` into `n` blocks of `k + 1`. -/
lemma sum_blocks_full {M : Type*} [AddCommMonoid M] (k : ℕ) (g : ℕ → M) : ∀ n : ℕ,
    ∑ col ∈ range (n * (k + 1)), g col = ∑ d ∈ range n, ∑ l ∈ range (k + 1), g (d * (k + 1) + l)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, sum_range_add, sum_blocks_full k g n,
      Finset.sum_range_succ (fun d => ∑ l ∈ range (k + 1), g (d * (k + 1) + l)) n]

/-- The skeleton digit difference: `S_z(v) - S_z(w) = ∑_d ρ^(d+1) (x_{d,k}(v) - x_{d,k}(w))`. -/
lemma skel_diff (hs : 2 ≤ s) (hC : IsS1skel s p k ρ C) (z : Fin s) (hz : (z : ℕ) + 1 = s)
    (v w : Fin (s * k + (s - 1)) → ZMod p) :
    vz (C z *ᵥ v) k - vz (C z *ᵥ w) k = ∑ d ∈ range (s - 1),
      ((ρ ^ (d + 1) : ℕ) : ZMod p) * (vz v (d * (k + 1) + k) - vz w (d * (k + 1) + k)) := by
  have hkm : k < s * k + (s - 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have : t = (z : ℕ) := by omega
    simp only [Nat.add_sub_cancel]
    nlinarith
  rw [mulVec_vz _ _ _ hkm, mulVec_vz _ _ _ hkm, ← sum_sub_distrib]
  have hm : s * k + (s - 1) = (s - 1) * (k + 1) + k := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have e : ∀ col ∈ range (s * k + (s - 1)), Z3NetKN.ent (C z) k col * vz v col -
      Z3NetKN.ent (C z) k col * vz w col = ((skRow s k ρ col : ℕ) : ZMod p) * (vz v col - vz w col) := by
    intro col hcol
    simp only [mem_range] at hcol
    rw [← ent_eq, hC.2 z hz col hcol]; ring
  rw [sum_congr rfl e, show range (s * k + (s - 1)) = range ((s - 1) * (k + 1) + k) by rw [hm],
    sum_range_add, sum_blocks_full k _ (s - 1)]
  have h2 : ∑ x ∈ range k, ((skRow s k ρ ((s - 1) * (k + 1) + x) : ℕ) : ZMod p) *
      (vz v ((s - 1) * (k + 1) + x) - vz w ((s - 1) * (k + 1) + x)) = 0 :=
    sum_eq_zero fun l hl => by
      simp only [mem_range] at hl
      rw [skRow_skel s k ρ l (by omega) hl]; simp
  rw [h2, add_zero]
  refine sum_congr rfl fun d hd => ?_
  simp only [mem_range] at hd
  rw [sum_eq_single k]
  · rw [skRow_full s k ρ d k (by omega) (by omega), if_pos rfl]
  · intro l hl hlk
    simp only [mem_range] at hl
    rw [skRow_full s k ρ d l (by omega) hl, if_neg hlk]; simp
  · intro h; simp at h

end Graph

/-! ## The separation theorem -/

theorem S1_sep (s p k ρ : ℕ) (hs : 3 ≤ s) (hp : p.Prime) (hρ : 2 ≤ ρ) (hρp : ρ ^ s < p)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k ρ C) (v w : Fin (s * k + (s - 1)) → ZMod p) (hvw : v ≠ w) :
    (ρ - 1) ^ 2 * p ^ (2 * ((s - 1) * (k + 1) - 1)) ≤
      torusDist2 (p ^ (s * k + (s - 1))) (digPoint p (s * k + (s - 1)) C v)
        (digPoint p (s * k + (s - 1)) C w) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : 0 < p := hp.pos
  have hkm : k + 1 ≤ s * k + (s - 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; nlinarith
  have hmk : s * k + (s - 1) - (k + 1) = (s - 1) * (k + 1) - 1 := by
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have e1 : (t + 1) * k = t * k + k := by ring
    have e2 : t * (k + 1) = t * k + t := by ring
    omega
  set a : Fin s → ℤ := fun c => cen (p ^ (k + 1)) ((Pf k (C c) v : ℤ) - Pf k (C c) w) with ha
  -- `a_c mod p` is the change of digit `k` of coordinate `c`.
  have hPf : ∀ c (u : Fin (s * k + (s - 1)) → ZMod p), ((Pf k (C c) u % p : ℕ) : ZMod p) = vz (C c *ᵥ u) k := by
    intro c u
    unfold Pf
    rw [pre_succ, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (dg_lt _ _ _)]
    simp [dg, ZMod.natCast_zmod_val]
  have hcast : ∀ c, ((a c : ℤ) : ZMod p) = vz (C c *ᵥ v) k - vz (C c *ᵥ w) k := by
    intro c
    rw [ha]; simp only
    rw [cen_cast_mod (k + 1) _ _ (by omega), hPf, hPf]
  have hfull : ∀ d : ℕ, ∀ hd : d + 1 < s, ((a ⟨d, by omega⟩ : ℤ) : ZMod p) =
      vz v (d * (k + 1) + k) - vz w (d * (k + 1) + k) := by
    intro d hd
    have hdep : k < depth s k ⟨d, by omega⟩ := by unfold depth; rw [if_pos hd]; omega
    rw [hcast, coarse_digit hC v _ k hdep, coarse_digit hC w _ k hdep]; rfl
  set zc : Fin s := ⟨s - 1, by omega⟩ with hzc
  have hrel : ((a zc : ℤ) : ZMod p) = ∑ d ∈ range (s - 1),
      ((ρ ^ (d + 1) : ℕ) : ZMod p) * (vz v (d * (k + 1) + k) - vz w (d * (k + 1) + k)) := by
    rw [hcast, skel_diff (by omega) hC zc (by simp [hzc]; omega) v w]
  -- the lattice vector
  set x : Fin (s - 1) → ℤ := fun i => a ⟨i, by omega⟩ with hx
  have hdiv : (p : ℤ) ∣ a zc - ∑ i : Fin (s - 1), (ρ : ℤ) ^ ((i : ℕ) + 1) * x i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hrel, ← Fin.sum_univ_eq_sum_range
      (fun d => ((ρ ^ (d + 1) : ℕ) : ZMod p) * (vz v (d * (k + 1) + k) - vz w (d * (k + 1) + k))),
      sub_eq_zero]
    refine sum_congr rfl fun i _ => ?_
    rw [hx]; simp only
    rw [hfull i (by omega)]; push_cast; ring
  -- `a ≠ 0`
  have hne : ¬(x = 0 ∧ a zc = 0) := by
    rintro ⟨hx0, hz0⟩
    have hall : ∀ c : Fin s, a c = 0 := by
      intro c
      by_cases hc : (c : ℕ) + 1 < s
      · have := congrFun hx0 ⟨c, by omega⟩
        simpa [hx] using this
      · have : c = zc := Fin.ext (by simp [hzc]; omega)
        rw [this]; exact hz0
    apply hvw
    have hP : ∀ c, Pf k (C c) v = Pf k (C c) w := fun c =>
      eq_of_cen_zero _ _ _ (Pf_lt _ v) (Pf_lt _ w) (hall c)
    funext col
    obtain ⟨c, j, hj, hcol⟩ := blocks_cover s k (by omega) col col.isLt
    have hjk : j < k + 1 := lt_of_lt_of_le hj (depth_le s k c)
    have hd := pre_inj_digit p hp0 _ _ (k + 1) (fun i _ => dg_lt _ v i) (fun i _ => dg_lt _ w i)
      (hP c) j hjk
    have h1 : vz (C c *ᵥ v) j = vz (C c *ᵥ w) j := ZMod.val_injective p hd
    rw [coarse_digit hC v c j hj, coarse_digit hC w c j hj, ← hcol] at h1
    simpa [vz, col.isLt] using h1
  -- Lemma L2_s
  obtain ⟨c, hc⟩ : ∃ c, (ρ : ℤ) ≤ |a c| := by
    rcases L2s_min s p ρ (by omega) hρp x (a zc) hdiv hne with h | ⟨i, h⟩
    · exact ⟨zc, h⟩
    · exact ⟨_, h⟩
  -- Lemma T
  have hb := prefix_bound (C c) v w (k + 1) hkm
  rw [← coord_eq, ← coord_eq, ← cres_eq] at hb
  set f := p ^ (s * k + (s - 1) - (k + 1)) with hf
  set cr := cres (p ^ (s * k + (s - 1)))
    ((coord p (s * k + (s - 1)) (C c) v : ℤ) - coord p (s * k + (s - 1)) (C c) w)
  have h1 : (((ρ - 1) * f : ℕ) : ℤ) ≤ cr := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ ρ)]
    have hf0 : (0 : ℤ) ≤ f := by positivity
    have := mul_le_mul_of_nonneg_right hc hf0
    have e : |cen (p ^ (k + 1)) ((pre p (dg (C c) v) (k + 1) : ℤ) - pre p (dg (C c) w) (k + 1))| = |a c| :=
      rfl
    rw [e] at hb
    linarith
  have h1' : (ρ - 1) * f ≤ cr := by exact_mod_cast h1
  calc (ρ - 1) ^ 2 * p ^ (2 * ((s - 1) * (k + 1) - 1)) = ((ρ - 1) * f) ^ 2 := by
        rw [hf, mul_pow, ← pow_mul, hmk, Nat.mul_comm 2]
    _ ≤ cr ^ 2 := Nat.pow_le_pow_left h1' 2
    _ ≤ _ := cres_le_torus _ (digPoint p (s * k + (s - 1)) C v) (digPoint p (s * k + (s - 1)) C w) c

end Z3NetS1.Proofs

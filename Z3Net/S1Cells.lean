module
public import Mathlib
public import Z3Net.S1Sep
public import Z3Net.S1Net3

@[expose] public section

/-!
# Entry S1, part 7: Theorem `thm:S1`(2) — lattice reading, index, minimum, optimality

* `finePos = Pf` (first `k + 1` digits), `finePos_mem`: `P(v) ∈ Λ` (`P_c ≡ x_{c,k}`,
  `P_z ≡ S_z (mod p)`); `finePos_attained`: every `a ∈ Λ ∩ [0, p^(k+1))^s` is `P(v)` for the index
  `v` whose block digits are the base-`p` digits of `a`; uniqueness since `P` determines the index.
* `S1lat_index`: `Λ` is the kernel of the surjection `a ↦ h · a mod p`.
* `S1lat_min`: Lemma L2_s in subgroup form; `S1_opt`: pigeonhole on `{0, …, ρ}^s`.
-/

namespace Z3NetS1.Proofs

open Finset Matrix Z3NetKN.Geom

/-! ## The check-vector sum -/

/-- `∑_c h_c a_c = ∑_{d < s-1} ρ^(d+1) g d - g (s-1)`, `g` the total extension of `a`. -/
lemma sum_chk (s ρ : ℕ) (hs : 1 ≤ s) (a : Fin s → ℤ) :
    ∑ c, chk s ρ c * a c = ∑ d ∈ range (s - 1), (ρ : ℤ) ^ (d + 1) * (if h : d < s then a ⟨d, h⟩ else 0) -
      (if h : s - 1 < s then a ⟨s - 1, h⟩ else 0) := by
  have e := Fin.sum_univ_eq_sum_range
    (fun n => (if n + 1 < s then (ρ : ℤ) ^ (n + 1) else -1) * (if h : n < s then a ⟨n, h⟩ else 0)) s
  have e2 : ∑ c : Fin s, chk s ρ c * a c = ∑ c : Fin s,
      (if (c : ℕ) + 1 < s then (ρ : ℤ) ^ ((c : ℕ) + 1) else -1) *
        (if h : (c : ℕ) < s then a ⟨c, h⟩ else 0) := by
    refine sum_congr rfl fun c _ => ?_
    rw [dif_pos c.isLt]; rfl
  rw [e2, e]
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [sum_range_succ, Nat.add_sub_cancel, if_neg (by omega)]
  rw [sum_congr rfl fun d hd => by simp only [mem_range] at hd; rw [if_pos (by omega)]]
  ring

/-- Same as `sum_chk` with the `Fin (s-1)` sum of Lemma L2_s. -/
lemma sum_chk' (s ρ : ℕ) (hs : 1 ≤ s) (a : Fin s → ℤ) :
    ∑ c, chk s ρ c * a c = ∑ i : Fin (s - 1), (ρ : ℤ) ^ ((i : ℕ) + 1) * a ⟨i, by omega⟩ -
      a ⟨s - 1, by omega⟩ := by
  rw [sum_chk s ρ hs a, dif_pos (by omega),
    ← Fin.sum_univ_eq_sum_range (fun d => (ρ : ℤ) ^ (d + 1) * (if h : d < s then a ⟨d, h⟩ else 0))]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [dif_pos (by omega)]

lemma mem_S1lat (s p ρ : ℕ) (a : Fin s → ℤ) :
    a ∈ S1lat s p ρ ↔ (p : ℤ) ∣ ∑ c, chk s ρ c * a c := by
  unfold S1lat
  rw [AddMonoidHom.mem_ker, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold chkHom
  simp [AddMonoidHom.finset_sum_apply]

/-! ## Fine positions -/

variable {s p k ρ : ℕ} {C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p)}

lemma kle (hs : 2 ≤ s) : k + 1 ≤ s * k + (s - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; nlinarith

lemma finePos_eq [NeZero p] (hs : 2 ≤ s) (v : Fin (s * k + (s - 1)) → ZMod p) (c : Fin s) :
    finePos s p k C v c = Pf k (C c) v := by
  unfold finePos digPoint
  rw [coord_eq, coord_split (C c) v (k + 1) (kle hs)]
  have hp0 : 0 < p := Nat.pos_of_neZero p
  rw [Nat.add_div_of_dvd_right (dvd_mul_left _ _), Nat.mul_div_cancel _ (pow_pos hp0 _),
    Nat.div_eq_of_lt (low_lt _ _ _), add_zero]
  rfl

lemma Pf_mod [NeZero p] (A : Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (u : Fin (s * k + (s - 1)) → ZMod p) : ((Pf k A u % p : ℕ) : ZMod p) = vz (A *ᵥ u) k := by
  unfold Pf
  rw [pre_succ, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (dg_lt _ _ _)]
  simp [dg]

/-- The S1 relation `P_z ≡ ∑ ρ^(d+1) P_{x_d}` in `𝔽_p`, as membership in `Λ`. -/
theorem finePos_mem (hs : 2 ≤ s) (hp : p.Prime) (hC : IsS1skel s p k ρ C)
    (v : Fin (s * k + (s - 1)) → ZMod p) : (fun c => (finePos s p k C v c : ℤ)) ∈ S1lat s p ρ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [mem_S1lat, ← ZMod.intCast_zmod_eq_zero_iff_dvd, sum_chk s ρ (by omega)]
  have hz : s - 1 < s := by omega
  rw [dif_pos hz]
  push_cast
  -- digit `k` of every coordinate
  have hdig : ∀ c : Fin s, ((finePos s p k C v c : ℕ) : ZMod p) = vz (C c *ᵥ v) k := by
    intro c
    rw [finePos_eq hs, ← ZMod.natCast_mod, Pf_mod]
  rw [hdig ⟨s - 1, hz⟩]
  have hsk := skel_diff (by omega) hC ⟨s - 1, hz⟩ (by simp; omega) v 0
  have h0 : vz (C ⟨s - 1, hz⟩ *ᵥ (0 : Fin (s * k + (s - 1)) → ZMod p)) k = 0 := by
    simp [vz]
  rw [h0, sub_zero] at hsk
  rw [hsk, sub_eq_zero]
  refine sum_congr rfl fun d hd => ?_
  simp only [mem_range] at hd
  rw [dif_pos (by omega)]
  push_cast
  rw [hdig ⟨d, by omega⟩]
  have hdep : k < depth s k ⟨d, by omega⟩ := by unfold depth; rw [if_pos (by simp; omega)]; omega
  rw [coarse_digit hC v _ k hdep]
  simp only [vz, off]
  by_cases hh : d * (k + 1) + k < s * k + (s - 1) <;> simp [hh]

/-- Base-`p` digits reassemble: `pre p (j ↦ ⌊x / p^(N-1-j)⌋ mod p) n = ⌊x / p^(N-n)⌋`, `n ≤ N`,
`x < p^N`. -/
lemma pre_digits (hp : 0 < p) (x N : ℕ) (hx : x < p ^ N) :
    ∀ n ≤ N, pre p (fun j => x / p ^ (N - 1 - j) % p) n = x / p ^ (N - n)
  | 0, _ => by simp [Nat.div_eq_of_lt hx]
  | n + 1, hn => by
    rw [pre_succ, pre_digits hp x N hx n (by omega)]
    have e : N - n = (N - (n + 1)) + 1 := by omega
    rw [e, pow_succ, ← Nat.div_div_eq_div_mul, show N - 1 - n = N - (n + 1) by omega]
    exact Nat.div_add_mod' _ _

/-- The index whose block digits are the base-`p` digits of `a`. -/
noncomputable def idxOf (hs : 0 < s) (a : Fin s → ℕ) : Fin (s * k + (s - 1)) → ZMod p :=
  fun col => ((a (cOf s k hs col) / p ^ (k - jOf s k hs col) % p : ℕ) : ZMod p)

theorem finePos_attained (hs : 2 ≤ s) (hp : p.Prime) (hC : IsS1skel s p k ρ C) (a : Fin s → ℕ)
    (ha : ∀ c, a c < p ^ (k + 1)) (hmem : (fun c => (a c : ℤ)) ∈ S1lat s p ρ) :
    ∀ c, finePos s p k C (idxOf (by omega) a) c = a c := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 := hp.pos
  have hs0 : 0 < s := by omega
  set v : Fin (s * k + (s - 1)) → ZMod p := idxOf hs0 a with hv
  -- index digits
  have hvd : ∀ (c : Fin s) (j : ℕ) (hj : j < depth s k c),
      vz v (off k c + j) = ((a c / p ^ (k - j) % p : ℕ) : ZMod p) := by
    intro c j hj
    have hlt : off k c + j < s * k + (s - 1) := by have := off_add_depth s k c; omega
    simp only [vz, dif_pos hlt, hv, idxOf]
    rw [cOf_off s k hs0 c j hj, jOf_off s k hs0 c j hj]
  intro c
  rw [finePos_eq hs]
  unfold Pf
  have key : ∀ j < k + 1, dg (C c) v j = a c / p ^ (k + 1 - 1 - j) % p := by
    intro j hj
    rw [show k + 1 - 1 - j = k - j by omega]
    by_cases hjd : j < depth s k c
    · unfold dg; rw [coarse_digit hC v c j hjd, hvd c j hjd, ZMod.val_natCast,
        Nat.mod_eq_of_lt (Nat.mod_lt _ hp0)]
    · -- the skeleton digit
      have hjk : j = k := by have := depth_le s k c; unfold depth at hjd; split_ifs at hjd <;> omega
      rw [hjk] at hjd ⊢
      have hcz : (c : ℕ) + 1 = s := by
        by_contra h; apply hjd; unfold depth; rw [if_pos (by omega)]; omega
      have hsk := skel_diff (by omega) hC c hcz v 0
      have h0 : vz (C c *ᵥ (0 : Fin (s * k + (s - 1)) → ZMod p)) k = 0 := by simp [vz]
      rw [h0, sub_zero] at hsk
      unfold dg; rw [hsk, Nat.sub_self, pow_zero, Nat.div_one]
      -- the skeleton digit is `∑ ρ^(d+1) (a_d mod p) ≡ a_z (mod p)`
      have hrel : (∑ d ∈ range (s - 1), ((ρ ^ (d + 1) : ℕ) : ZMod p) *
          (vz v (d * (k + 1) + k) - vz (0 : Fin (s * k + (s - 1)) → ZMod p) (d * (k + 1) + k))) =
          ((a c : ℕ) : ZMod p) := by
        have hm := (mem_S1lat s p ρ _).1 hmem
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, sum_chk s ρ (by omega)] at hm
        have hcc : (⟨s - 1, by omega⟩ : Fin s) = c := Fin.ext (by simp; omega)
        rw [dif_pos (by omega), hcc] at hm
        push_cast at hm
        rw [sub_eq_zero] at hm
        rw [← hm]
        refine sum_congr rfl fun d hd => ?_
        simp only [mem_range] at hd
        rw [dif_pos (by omega)]
        have hdep : k < depth s k ⟨d, by omega⟩ := by unfold depth; rw [if_pos (by simp; omega)]; omega
        have := hvd ⟨d, by omega⟩ k hdep
        simp only [off] at this
        rw [this]
        simp [vz, Nat.sub_self]
      rw [hrel, ZMod.val_natCast]
  rw [pre_congr p _ _ (k + 1) key, pre_digits hp0 (a c) (k + 1) (ha c) (k + 1) le_rfl, Nat.sub_self,
    pow_zero, Nat.div_one]

/-- Fine positions determine the index. -/
theorem eq_of_finePos_eq (hs : 2 ≤ s) (hp : p.Prime) (hC : IsS1skel s p k ρ C)
    (v w : Fin (s * k + (s - 1)) → ZMod p) (h : ∀ c, finePos s p k C v c = finePos s p k C w c) :
    v = w := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 := hp.pos
  funext col
  obtain ⟨c, j, hj, hcol⟩ := blocks_cover s k (by omega) col col.isLt
  have hjk : j < k + 1 := lt_of_lt_of_le hj (depth_le s k c)
  have hP : Pf k (C c) v = Pf k (C c) w := by rw [← finePos_eq hs, ← finePos_eq hs, h c]
  have hd := pre_inj_digit p hp0 _ _ (k + 1) (fun i _ => dg_lt _ v i) (fun i _ => dg_lt _ w i) hP j hjk
  have h1 : vz (C c *ᵥ v) j = vz (C c *ᵥ w) j := ZMod.val_injective p hd
  rw [coarse_digit hC v c j hj, coarse_digit hC w c j hj, ← hcol] at h1
  simpa [vz, col.isLt] using h1

theorem S1_cells (s p k ρ : ℕ) (hs : 2 ≤ s) (hp : p.Prime)
    (C : Fin s → Matrix (Fin (s * k + (s - 1))) (Fin (s * k + (s - 1))) (ZMod p))
    (hC : IsS1skel s p k ρ C) :
    (∀ v, (fun c => (finePos s p k C v c : ℤ)) ∈ S1lat s p ρ) ∧
      ∀ a : Fin s → ℕ, (∀ c, a c < p ^ (k + 1)) → (fun c => (a c : ℤ)) ∈ S1lat s p ρ →
        ∃! v, ∀ c, finePos s p k C v c = a c := by
  refine ⟨finePos_mem hs hp hC, fun a ha hmem => ?_⟩
  refine ⟨idxOf (by omega) a, finePos_attained hs hp hC a ha hmem, fun w hw => ?_⟩
  exact eq_of_finePos_eq hs hp hC w _ fun c => by rw [hw c, finePos_attained hs hp hC a ha hmem c]

/-! ## Index, minimum, optimality -/

theorem S1lat_index (s p ρ : ℕ) (hs : 1 ≤ s) : (S1lat s p ρ).index = p := by
  have hker : S1lat s p ρ = (chkHom s p ρ).ker := rfl
  have happ : ∀ a, chkHom s p ρ a = ((∑ c, chk s ρ c * a c : ℤ) : ZMod p) := by
    intro a; unfold chkHom; simp [AddMonoidHom.finset_sum_apply]
  have hsurj : Function.Surjective (chkHom s p ρ) := by
    intro t
    refine ⟨fun c => if (c : ℕ) = s - 1 then -(t.valMinAbs) else 0, ?_⟩
    rw [happ]
    rw [sum_eq_single (⟨s - 1, by omega⟩ : Fin s)]
    · simp only [if_pos rfl]
      unfold chk; rw [if_neg (by simp; omega)]
      push_cast; simp [ZMod.coe_valMinAbs]
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
    · simp
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top,
    Nat.card_zmod]

theorem S1lat_min (s p ρ : ℕ) (hs : 2 ≤ s) (hρ : 1 ≤ ρ) (hρp : ρ ^ s < p) :
    (∀ a ∈ S1lat s p ρ, a ≠ 0 → ∃ c, (ρ : ℤ) ≤ |a c|) ∧
      ∃ a ∈ S1lat s p ρ, a ≠ 0 ∧ ∀ c, |a c| ≤ ρ := by
  constructor
  · intro a ha hne
    rw [mem_S1lat, sum_chk' s ρ (by omega)] at ha
    have hdiv : (p : ℤ) ∣ a ⟨s - 1, by omega⟩ -
        ∑ i : Fin (s - 1), (ρ : ℤ) ^ ((i : ℕ) + 1) * a ⟨i, by omega⟩ := by
      rw [← dvd_neg, neg_sub]; exact ha
    have hne' : ¬((fun i : Fin (s - 1) => a ⟨i, by omega⟩) = 0 ∧ a ⟨s - 1, by omega⟩ = 0) := by
      rintro ⟨hx, hz⟩
      apply hne; funext c
      by_cases hc : (c : ℕ) < s - 1
      · have := congrFun hx ⟨c, hc⟩; simpa using this
      · have : c = ⟨s - 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [this]; exact hz
    rcases L2s_min s p ρ (by omega) hρp _ _ hdiv hne' with h | ⟨i, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  · refine ⟨fun c => if (c : ℕ) = 0 then 1 else if (c : ℕ) = s - 1 then (ρ : ℤ) else 0, ?_, ?_, ?_⟩
    · rw [mem_S1lat, sum_chk' s ρ (by omega)]
      dsimp only
      rw [if_neg (show s - 1 ≠ 0 by omega), if_pos rfl]
      rw [sum_eq_single (⟨0, by omega⟩ : Fin (s - 1))]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
        have hb2 := b.isLt
        rw [if_neg this, if_neg (show (b : ℕ) ≠ s - 1 by omega), mul_zero]
      · simp
    · intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
    · intro c
      dsimp only
      split_ifs <;> simp <;> omega

/-- `p < (ρ_s(p) + 1)^s` for prime `p`, `s ≥ 2`. -/
lemma lt_rhoS_succ_pow (s p : ℕ) (hs : 2 ≤ s) (hp : p.Prime) : p < (rhoS s p + 1) ^ s := by
  have hle : rhoS s p ≤ p := Nat.findGreatest_le p
  have hspec : rhoS s p ^ s < p := Nat.findGreatest_spec (P := fun ρ => ρ ^ s < p) (Nat.zero_le p)
    (by simp only [zero_pow (show s ≠ 0 by omega)]; exact hp.pos)
  have hρlt : rhoS s p < p := by
    rcases Nat.lt_or_ge (rhoS s p) p with h | h
    · exact h
    · have heq : rhoS s p = p := le_antisymm hle h
      rw [heq] at hspec
      have : p ≤ p ^ s := Nat.le_self_pow (by omega) p
      omega
  have hnot := Nat.findGreatest_is_greatest (P := fun ρ => ρ ^ s < p) (n := p)
    (k := rhoS s p + 1) (by unfold rhoS; omega) (by omega)
  simp only [not_lt] at hnot
  rcases Nat.lt_or_ge p ((rhoS s p + 1) ^ s) with h | h
  · exact h
  · have heq : (rhoS s p + 1) ^ s = p := le_antisymm h hnot
    have := (Nat.Prime.pow_eq_iff hp).1 heq
    omega

theorem S1_opt (s p : ℕ) (hs : 2 ≤ s) (hp : p.Prime) (L : AddSubgroup (Fin s → ℤ))
    (hL : L.index = p) : ∃ a ∈ L, a ≠ 0 ∧ ∀ c, |a c| ≤ rhoS s p := by
  classical
  have hlt := lt_rhoS_succ_pow s p hs hp
  haveI : Finite ((Fin s → ℤ) ⧸ L) := Nat.finite_of_card_ne_zero (by
    rw [← AddSubgroup.index]; rw [hL]; exact hp.ne_zero)
  haveI : Fintype ((Fin s → ℤ) ⧸ L) := Fintype.ofFinite _
  let f : (Fin s → Fin (rhoS s p + 1)) → (Fin s → ℤ) ⧸ L := fun x => ((fun c => ((x c : ℕ) : ℤ)) : Fin s → ℤ)
  have hcard : Fintype.card ((Fin s → ℤ) ⧸ L) < Fintype.card (Fin s → Fin (rhoS s p + 1)) := by
    rw [← Nat.card_eq_fintype_card, ← AddSubgroup.index, hL]
    simpa using hlt
  obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  refine ⟨fun c => ((x c : ℕ) : ℤ) - ((y c : ℕ) : ℤ), ?_, ?_, ?_⟩
  · have := (QuotientAddGroup.eq (s := L)).1 hfxy
    have h2 : -(fun c => ((x c : ℕ) : ℤ)) + (fun c => ((y c : ℕ) : ℤ)) =
        -(fun c => ((x c : ℕ) : ℤ) - ((y c : ℕ) : ℤ)) := by funext c; simp; ring
    rw [h2] at this
    exact L.neg_mem_iff.1 this
  · intro h
    apply hxy; funext c
    have := congrFun h c
    simp only [Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at this
    exact Fin.ext this
  · intro c
    have h1 := (x c).isLt; have h2 := (y c).isLt
    show |((x c : ℕ) : ℤ) - ((y c : ℕ) : ℤ)| ≤ (rhoS s p : ℤ)
    rw [abs_le]; constructor <;> omega

end Z3NetS1.Proofs

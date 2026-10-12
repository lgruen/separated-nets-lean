module
public import Mathlib
public import Z3Net.HLDefs
public import Z3Net.HLSep

@[expose] public section

/-!
# Entry HL, stage 1, part 1: the carry relaxation for an arbitrary graph form

`relax_core` of `Z3Net/HLRelax.lean` is stated for the split-frame net `HLpoint`; it uses only
the graph-form structure and (H1) (row `0` of every block is the design). Here the same argument
is carried out for an arbitrary graph form `Φ` over `ℤ/qℤ` under the hypothesis `RowDesign`
(`2 Φ_cd[0, j] = F2 (k-1-j) c d` on the levels `k-1-j < s-1`, `0` below), with no
admissibility hypothesis: the congruence of the first offset digit is obtained directly in the
doubled form `2Δ_c ≡ sig2 (mod q)`.
-/

namespace Z3NetHL.Proofs

open Finset Matrix

noncomputable section

open Z3NetU.Proofs (ix ix_surj sk_sub_add graphGen_cell graphGen_off)

variable (s q k : ℕ) (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))

/-- Digit vector of coordinate `c` of the graph-form point with index `x`. -/
def DgG (c : Fin s) (x : Fin (s * k) → ZMod q) : Fin (s * k) → ZMod q :=
  Z3NetHL.graphGen s k Φ c *ᵥ x

lemma GFpoint_eq (x : Fin (s * k) → ZMod q) (c : Fin s) :
    GFpoint s q k Φ x c =
      ∑ j : Fin (s * k), (DgG s q k Φ c x j).val * q ^ (s * k - 1 - (j : ℕ)) := rfl

lemma DgG_cell (c : Fin s) (x : Fin (s * k) → ZMod q) (i : ℕ) (hi : i < k) :
    DgG s q k Φ c x ⟨i, lt_of_lt_of_le hi (k_le_sk' k c)⟩ = x (ix k c ⟨i, hi⟩) :=
  graphGen_cell k Φ c x i hi

lemma DgG_off (c : Fin s) (x : Fin (s * k) → ZMod q) (r : Fin (s * k - k)) :
    DgG s q k Φ c x ⟨k + r, sk_sub_add r⟩ =
      ∑ d : Fin s, ∑ l : Fin k, Φ c d r l * x (ix k d l) :=
  graphGen_off k Φ c x r

variable [NeZero q]

lemma cellG_part (x : Fin (s * k) → ZMod q) (c : Fin s) :
    ∑ i ∈ range k, dv s q k (DgG s q k Φ c x) i * q ^ (k - 1 - i) = cellN s q k x c := by
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  congr 1
  have hik : i < s * k := lt_of_lt_of_le hi (k_le_sk' k c)
  simp only [dv, ad, dif_pos hi, dif_pos hik]
  rw [DgG_cell s q k Φ c x i hi]

/-- First offset digit and tail of coordinate `c`. -/
def o0G (x : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := dv s q k (DgG s q k Φ c x) k
def tlG (x : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := tail s q k (DgG s q k Φ c x)

lemma XG_decomp (hsk : k + 1 ≤ s * k) (x : Fin (s * k) → ZMod q) (c : Fin s) :
    (GFpoint s q k Φ x c : ℤ) = (q : ℤ) ^ (s * k - k) * cellN s q k x c +
      (q : ℤ) ^ (s * k - k - 1) * o0G s q k Φ x c + tlG s q k Φ x c := by
  rw [GFpoint_eq, coord_split s q k hsk, cellG_part]
  push_cast
  simp only [o0G, tlG]

lemma o0G_cast (x : Fin (s * k) → ZMod q) (c : Fin s) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) :
    ((o0G s q k Φ x c : ℕ) : ZMod q) = DgG s q k Φ c x ⟨k + r, sk_sub_add r⟩ := by
  have hk : k < s * k := by have := sk_sub_add r; omega
  simp only [o0G, dv, dif_pos hk, ZMod.natCast_zmod_val, hr, add_zero]

lemma oG_bound (x y : Fin (s * k) → ZMod q) (c : Fin s) :
    |(o0G s q k Φ x c : ℤ) - o0G s q k Φ y c| < q := by
  have h1 := dv_lt s q k (DgG s q k Φ c x) k
  have h2 := dv_lt s q k (DgG s q k Φ c y) k
  simp only [o0G]
  rw [abs_lt]; constructor <;> omega

lemma tlG_lt (hsk : k + 1 ≤ s * k) (x : Fin (s * k) → ZMod q) (c : Fin s) :
    tlG s q k Φ x c < q ^ (s * k - k - 1) := tail_lt s q k hsk _

/-- Change of the first offset digit, doubled: `2 (r'_c - r_c) = sig2` in `ℤ/qℤ`. -/
lemma DgG_off_sub (hs : 2 ≤ s) (F2 : ℕ → Fin s → Fin s → ℤ) (hrow : RowDesign s q k Φ F2)
    (c : Fin s) (x y : Fin (s * k) → ZMod q) (E : Fin s → ℤ) (J : Fin s → ℕ)
    (hJk : ∀ d, J d < k) (hJs : ∀ d, J d ≤ s - 2)
    (hstep : ∀ d, AxisStep2 s q k x y d (E d) (J d)) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) :
    2 * (DgG s q k Φ c y ⟨k + r, sk_sub_add r⟩ - DgG s q k Φ c x ⟨k + r, sk_sub_add r⟩) =
      (sig2 F2 E J c : ZMod q) := by
  rw [DgG_off, DgG_off, ← sum_sub_distrib, Finset.mul_sum]
  unfold sig2
  push_cast
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_sub_distrib, Finset.mul_sum]
  set f : ℕ → ZMod q := fun t => if t < s - 1 then (F2 t c d : ZMod q) else 0 with hf
  have e1 : ∀ l : Fin k, 2 * (Φ c d r l * y (ix k d l) - Φ c d r l * x (ix k d l)) =
      f (k - 1 - (l : ℕ)) * (if k - 1 - (l : ℕ) = 0 then (E d : ZMod q)
        else ((E d).sign : ZMod q) * (if k - 1 - (l : ℕ) ≤ J d then 1 else 0)) := by
    intro l
    rw [← mul_sub, ← mul_assoc, hrow c d r hr l]
    by_cases hl : k - 1 - (l : ℕ) ≤ s - 2
    · rw [hstep d l hl]
    · simp only [hf, if_neg (show ¬ (k - 1 - (l : ℕ) < s - 1) by omega), zero_mul]
  rw [Finset.sum_congr rfl (fun l _ => e1 l)]
  rw [Fin.sum_univ_eq_sum_range (fun l => f (k - 1 - l) * (if k - 1 - l = 0 then (E d : ZMod q)
        else ((E d).sign : ZMod q) * (if k - 1 - l ≤ J d then 1 else 0))) k,
    Finset.sum_range_reflect (fun t => f t * (if t = 0 then (E d : ZMod q)
        else ((E d).sign : ZMod q) * (if t ≤ J d then 1 else 0))) k,
    sum_steps q k (J d) (hJk d) f (E d)]
  have hs1 : 0 < s - 1 := by omega
  simp only [hf, if_pos hs1]
  congr 1
  congr 1
  refine sum_congr rfl fun t ht => ?_
  have := (mem_Icc.mp ht).2; have := hJs d
  rw [if_pos (by omega)]

lemma eq_of_cellN' (hq : 1 < q) (x y : Fin (s * k) → ZMod q)
    (h : ∀ d, cellN s q k y d = cellN s q k x d) : y = x := by
  funext j
  obtain ⟨d, l, rfl⟩ := ix_surj k j
  exact digits_eq_of_cellN_eq s q k hq x y d (h d) l

/-- **Prop H_k(a) for an arbitrary graph form** (with `cres` of entry U). -/
theorem relaxG (hs : 2 ≤ s) (hq7 : 7 ≤ q) (F2 : ℕ → Fin s → Fin s → ℤ)
    (hrow : RowDesign s q k Φ F2) (hk : 1 ≤ k)
    (x y : Fin (s * k) → ZMod q) (hxy : x ≠ y) :
    4 * (q : ℤ) ^ (2 * (s * k - k)) ≤ ∑ c : Fin s,
        ((Z3NetU.cres (q ^ (s * k)) ((GFpoint s q k Φ x c : ℤ) -
          (GFpoint s q k Φ y c : ℤ)) : ℕ) : ℤ) ^ 2 ∨
      ∃ (E : Fin s → ℤ) (J : Fin s → ℕ) (Δ : Fin s → ℤ),
        (∀ c, |E c| ≤ 2) ∧ (∃ c, E c ≠ 0) ∧ (∀ c, J c < min k (s - 1)) ∧
        (∀ c, (q : ℤ) ∣ 2 * Δ c - sig2 F2 E J c) ∧ (∀ c, |Δ c| < q) ∧
        (q : ℤ) ^ (2 * (s * k - k - 1)) * ∑ c, (max 0 (|(q : ℤ) * E c + Δ c| - 1)) ^ 2 ≤
          ∑ c : Fin s, ((Z3NetU.cres (q ^ (s * k)) ((GFpoint s q k Φ x c : ℤ) -
            (GFpoint s q k Φ y c : ℤ)) : ℕ) : ℤ) ^ 2 := by
  have hq1 : 1 < q := by omega
  have h2k : 2 * k ≤ s * k := Nat.mul_le_mul_right k hs
  have hsk : k + 1 ≤ s * k := by omega
  have hM1 : 1 ≤ (s * k - k) := by omega
  set U : ℤ := (q : ℤ) ^ ((s * k - k) - 1) with hU_def
  have hU : 0 < U := by positivity
  have hpow : (q : ℤ) ^ (s * k - k) = U * q := by rw [hU_def, ← pow_succ]; congr 1; omega
  have hN : ((q ^ (s * k) : ℕ) : ℤ) = (q : ℤ) ^ (s * k - k) * (q : ℤ) ^ k := by
    push_cast; rw [← pow_add]; congr 1; omega
  set X := GFpoint s q k Φ with hXdef
  have hX : ∀ c, (X x c : ℤ) - X y c =
      (q : ℤ) ^ (s * k - k) * ((cellN s q k x c : ℤ) - cellN s q k y c) +
      (U * ((o0G s q k Φ x c : ℤ) - o0G s q k Φ y c) +
        ((tlG s q k Φ x c : ℤ) - tlG s q k Φ y c)) := by
    intro c; rw [hXdef, XG_decomp s q k Φ hsk, XG_decomp s q k Φ hsk]; ring
  have htl : ∀ c, |(tlG s q k Φ x c : ℤ) - tlG s q k Φ y c| < U := by
    intro c
    have h1 := tlG_lt s q k Φ hsk x c
    have h2 := tlG_lt s q k Φ hsk y c
    have h1' : ((tlG s q k Φ x c : ℕ) : ℤ) < U := by rw [hU_def]; exact_mod_cast h1
    have h2' : ((tlG s q k Φ y c : ℕ) : ℤ) < U := by rw [hU_def]; exact_mod_cast h2
    rw [abs_lt]; constructor <;> omega
  have hsum_nonneg : ∀ c ∈ (univ : Finset (Fin s)), (0 : ℤ) ≤
      ((Z3NetU.cres (q ^ (s * k)) ((X x c : ℤ) - (X y c : ℤ)) : ℕ) : ℤ) ^ 2 :=
    fun c _ => sq_nonneg _
  by_cases hfar : ∃ c, Far3 s q k y x c
  · left
    obtain ⟨c, hc⟩ := hfar
    have ho0 := oG_bound s q k Φ x y c
    have hR : |U * ((o0G s q k Φ x c : ℤ) - o0G s q k Φ y c) +
        ((tlG s q k Φ x c : ℤ) - tlG s q k Φ y c)| < (q : ℤ) ^ (s * k - k) := by
      have a2 := abs_add_le (U * ((o0G s q k Φ x c : ℤ) - o0G s q k Φ y c))
        ((tlG s q k Φ x c : ℤ) - tlG s q k Φ y c)
      rw [abs_mul, abs_of_pos hU] at a2
      have := htl c
      have b1 : |(o0G s q k Φ x c : ℤ) - o0G s q k Φ y c| ≤ q - 1 := by omega
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
    refine ⟨E, J, fun c => (o0G s q k Φ x c : ℤ) - o0G s q k Φ y c,
      hE, hne, fun c => lt_min (hJk c) (by have := hJs c; omega), ?_,
      fun c => oG_bound s q k Φ x y c, ?_⟩
    · intro c
      have h := DgG_off_sub s q k Φ hs F2 hrow c y x E J hJk hJs hstep ⟨0, by omega⟩ rfl
      rw [← o0G_cast s q k Φ x c ⟨0, by omega⟩ rfl,
        ← o0G_cast s q k Φ y c ⟨0, by omega⟩ rfl] at h
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h]; ring
    · set V : Fin s → ℤ := fun c => (q : ℤ) * E c +
        ((o0G s q k Φ x c : ℤ) - o0G s q k Φ y c) with hV
      have hVb : ∀ c, |V c| ≤ 3 * (q : ℤ) - 1 := by
        intro c
        have ho := oG_bound s q k Φ x y c
        have b1 : |(o0G s q k Φ x c : ℤ) - o0G s q k Φ y c| ≤ q - 1 := by omega
        have b0 : |E c| ≤ 2 := hE c
        have := abs_add_le ((q : ℤ) * E c) ((o0G s q k Φ x c : ℤ) - o0G s q k Φ y c)
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < q)] at this
        simp only [hV]
        nlinarith
      have hXV : ∀ c, ∃ z : ℤ, (X x c : ℤ) - X y c =
          U * V c + ((tlG s q k Φ x c : ℤ) - tlG s q k Φ y c) +
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
          have := abs_add_le (U * V c) ((tlG s q k Φ x c : ℤ) - tlG s q k Φ y c)
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
            ((o0G s q k Φ x c : ℤ) - o0G s q k Φ y c)| - 1)) ^ 2
          = ∑ c, (U * max 0 (|V c| - 1)) ^ 2 := by
            rw [hU2, Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by simp only [hV]; ring
        _ ≤ _ := Finset.sum_le_sum fun c _ => hsq c

end

end Z3NetHL.Proofs

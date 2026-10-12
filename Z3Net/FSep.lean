module
public import Z3Net.FDom
public import Z3Net.FPropF

@[expose] public section

/-!
# Entry F, part 13: `lem:Ss` for an arbitrary design and graph form over `ℤ/qℤ`

Generalizes entry U's `SUGeom`/`SUSep` from the net `𝒫^s_{k,q}` of `U_s` to any graph form with
(H1), (H2): carries of every length (capped at `L-1` by (H1)), residue representatives, the
jitter via (H2), and far steps.
-/

namespace Z3NetF.Proofs

open Finset Matrix

noncomputable section

/-! ## Bridges to entry U's graph forms -/

lemma graphGenK_const {R : Type*} [Zero R] [One R] (s k : ℕ)
    (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) R) :
    Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ = Z3NetU.graphGen s k Φ := by
  funext c
  ext i j
  obtain ⟨d, l, rfl⟩ := Z3NetU.Proofs.ix_surj k j
  have hj : Z3NetU.Proofs.ix k d l = ⟨pre (fun _ : Fin s => k) d + l,
      pre_add_lt (fun _ : Fin s => k) (sum_const_k k) d l l.isLt⟩ := by
    ext; simp [Z3NetU.Proofs.ix, pre_const]
  rw [hj, graphGenK_apply (fun _ : Fin s => k) (sum_const_k k) Φ c i d l l.isLt]
  rw [← hj]
  simp only [Z3NetU.graphGen]
  by_cases hi : (i : ℕ) < k
  · rw [dif_pos hi, dif_pos hi]
    simp only [Z3NetU.Proofs.ix]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩; subst h1; rw [h2]
    · intro h
      have := Z3NetU.Proofs.ix_div k d l
      have h2 := Z3NetU.Proofs.ix_mod k d l
      simp only [Z3NetU.Proofs.ix] at this h2
      rw [h] at this h2
      constructor
      · ext; rw [← this, Nat.add_comm, Nat.add_mul_div_right _ _ (by have := l.isLt; omega),
          Nat.div_eq_of_lt hi]; simp
      · rw [← h2, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  · rw [dif_neg hi, dif_neg hi]
    congr 1
    · ext; simp [Z3NetU.Proofs.ix_div]
    · ext; simp [Z3NetU.Proofs.ix_mod]

lemma digPoint_eq {s q m : ℕ} (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) :
    Z3NetF.digPoint q m C = Z3NetU.digPoint q m C := rfl

lemma torusDist2_eq {s : ℕ} (N : ℕ) (x y : Fin s → ℕ) :
    Z3NetF.torusDist2 N x y = Z3NetU.torusDist2 N x y := rfl

lemma cres_eq (N : ℕ) (u : ℤ) : Z3NetF.cres N u = Z3NetU.cres N u := rfl

section geom

variable (s q k : ℕ) [NeZero q] (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))

/-- Digits of coordinate `c`. -/
def DgF (c : Fin s) (v : Fin (s * k) → ZMod q) : Fin (s * k) → ZMod q := Z3NetU.graphGen s k Φ c *ᵥ v

/-- First offset digit and tail of coordinate `c`. -/
def o0F (v : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := Z3NetU.Proofs.dv s q k (DgF s q k Φ c v) k
def tlF (v : Fin (s * k) → ZMod q) (c : Fin s) : ℕ := Z3NetU.Proofs.tail s q k (DgF s q k Φ c v)

lemma cell_partF (v : Fin (s * k) → ZMod q) (c : Fin s) :
    ∑ i ∈ range k, Z3NetU.Proofs.dv s q k (DgF s q k Φ c v) i * q ^ (k - 1 - i) =
      Z3NetU.Proofs.cellN s q k v c := by
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  congr 1
  have hik : i < s * k := lt_of_lt_of_le hi (Z3NetU.Proofs.k_le_sk k c)
  simp only [Z3NetU.Proofs.dv, Z3NetU.Proofs.ad, dif_pos hi, dif_pos hik, DgF]
  rw [Z3NetU.Proofs.graphGen_cell k Φ c v i hi]

lemma X_decompF (hsk : k + 1 ≤ s * k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    (Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) v c : ℤ) =
      (q : ℤ) ^ (s * k - k) * Z3NetU.Proofs.cellN s q k v c +
        ((q : ℤ) ^ (s * k - k - 1) * o0F s q k Φ v c + tlF s q k Φ v c) := by
  rw [graphGenK_const]
  show ((∑ j : Fin (s * k), ((Z3NetU.graphGen s k Φ c *ᵥ v) j).val * q ^ (s * k - 1 - (j : ℕ)) : ℕ) : ℤ) = _
  rw [Z3NetU.Proofs.coord_split s q k hsk, show (Z3NetU.graphGen s k Φ c *ᵥ v) = DgF s q k Φ c v from rfl,
    cell_partF]
  push_cast
  simp only [o0F, tlF]
  ring

lemma low_lt (hsk : k + 1 ≤ s * k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    q ^ (s * k - k - 1) * o0F s q k Φ v c + tlF s q k Φ v c < q ^ (s * k - k) := by
  have h1 := Z3NetU.Proofs.dv_lt s q k (DgF s q k Φ c v) k
  have h2 := Z3NetU.Proofs.tail_lt s q k hsk (DgF s q k Φ c v)
  have e : q ^ (s * k - k) = q ^ (s * k - k - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  rw [e]
  simp only [o0F, tlF]
  nlinarith

lemma cell_of_digPoint (hsk : k + 1 ≤ s * k) (v : Fin (s * k) → ZMod q) (c : Fin s) :
    Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) v c / q ^ (s * k - k) =
      Z3NetU.Proofs.cellN s q k v c ∧
    Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) v c % q ^ (s * k - k) =
      q ^ (s * k - k - 1) * o0F s q k Φ v c + tlF s q k Φ v c := by
  have hX := X_decompF s q k Φ hsk v c
  have hX' : Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) v c =
      q ^ (s * k - k) * Z3NetU.Proofs.cellN s q k v c +
        (q ^ (s * k - k - 1) * o0F s q k Φ v c + tlF s q k Φ v c) := by exact_mod_cast hX
  have hl := low_lt s q k Φ hsk v c
  have hp : 0 < q ^ (s * k - k) := pow_pos (Nat.pos_of_neZero q) _
  rw [hX']
  constructor
  · rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hl, add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hl]

/-- Per-axis step data on all levels. -/
def AxisStepF (v w : Fin (s * k) → ZMod q) (d : Fin s) (e : ℤ) (J : ℕ) : Prop :=
  ∀ l : Fin k, w (Z3NetU.Proofs.ix k d l) - v (Z3NetU.Proofs.ix k d l) =
    (e : ZMod q) * (if k - 1 - (l : ℕ) ≤ J then 1 else 0)

lemma findGreatest_iff (P : ℕ → Prop) [DecidablePred P] (N t : ℕ) (ht : t ≤ N)
    (hmono : ∀ a b, a ≤ b → P b → P a) (h0 : P 0) :
    P t ↔ t ≤ Nat.findGreatest P N := by
  constructor
  · intro h; exact Nat.le_findGreatest ht h
  · intro h
    exact hmono _ _ h (Nat.findGreatest_spec (P := P) (Nat.zero_le _) h0)

lemma axis_plusF (hq : 1 < q) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (h : Z3NetU.Proofs.cellN s q k w d = (Z3NetU.Proofs.cellN s q k v d + 1) % q ^ k) :
    AxisStepF s q k v w d 1 (Z3NetF.carryLen q k (Z3NetU.Proofs.cellN s q k v d) 1) := by
  intro l
  rw [Z3NetU.Proofs.carry_digits s q hq k v w d h l]
  have hcl : Z3NetF.carryLen q k (Z3NetU.Proofs.cellN s q k v d) 1 =
      Nat.findGreatest (fun t => q ^ t ∣ Z3NetU.Proofs.cellN s q k v d + 1) (k - 1) := by
    simp [Z3NetF.carryLen]
  rw [hcl]
  have := findGreatest_iff (fun t => q ^ t ∣ Z3NetU.Proofs.cellN s q k v d + 1) (k - 1) (k - 1 - l)
    (by omega) (fun a b hab hb => (pow_dvd_pow q hab).trans hb) (by simp)
  by_cases h' : q ^ (k - 1 - (l : ℕ)) ∣ Z3NetU.Proofs.cellN s q k v d + 1
  · rw [if_pos h', if_pos (this.mp h')]; simp
  · rw [if_neg h', if_neg (fun h2 => h' (this.mpr h2))]; simp

lemma axis_minusF (hq : 1 < q) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (h : Z3NetU.Proofs.cellN s q k v d = (Z3NetU.Proofs.cellN s q k w d + 1) % q ^ k) :
    AxisStepF s q k v w d (-1) (Z3NetF.carryLen q k (Z3NetU.Proofs.cellN s q k v d) (-1)) := by
  intro l
  have hl := l.isLt
  have hc := Z3NetU.Proofs.carry_digits s q hq k w v d h l
  rw [← neg_sub, hc]
  have hcl : Z3NetF.carryLen q k (Z3NetU.Proofs.cellN s q k v d) (-1) =
      Nat.findGreatest (fun t => q ^ t ∣ Z3NetU.Proofs.cellN s q k v d) (k - 1) := by
    simp [Z3NetF.carryLen]
  rw [hcl]
  have hiff : q ^ (k - 1 - (l : ℕ)) ∣ Z3NetU.Proofs.cellN s q k w d + 1 ↔
      q ^ (k - 1 - (l : ℕ)) ∣ Z3NetU.Proofs.cellN s q k v d := by
    rw [h, Nat.dvd_mod_iff (pow_dvd_pow q (by omega))]
  have := findGreatest_iff (fun t => q ^ t ∣ Z3NetU.Proofs.cellN s q k v d) (k - 1) (k - 1 - l)
    (by omega) (fun a b hab hb => (pow_dvd_pow q hab).trans hb) (by simp)
  by_cases h' : q ^ (k - 1 - (l : ℕ)) ∣ Z3NetU.Proofs.cellN s q k v d
  · rw [if_pos (hiff.mpr h'), if_pos (this.mp h')]; simp
  · rw [if_neg (fun h2 => h' (hiff.mp h2)), if_neg (fun h2 => h' (this.mpr h2))]; simp

lemma axis_zeroF (hq : 1 < q) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (h : Z3NetU.Proofs.cellN s q k w d = Z3NetU.Proofs.cellN s q k v d) (J : ℕ) :
    AxisStepF s q k v w d 0 J := by
  intro l
  rw [Z3NetU.Proofs.digits_eq_of_cellN_eq s q hq k v w d h l]; simp

end geom

section ss

variable (s q k : ℕ) [NeZero q] (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
  (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ)

lemma o0_castF (v : Fin (s * k) → ZMod q) (c : Fin s) (hk : k < s * k) :
    ((o0F s q k Φ v c : ℕ) : ZMod q) = DgF s q k Φ c v ⟨k, hk⟩ := by
  simp only [o0F, Z3NetU.Proofs.dv, dif_pos hk, ZMod.natCast_zmod_val]

/-- Change of the first offset digit under per-axis steps, from (H1). -/
lemma Dg_off_subF (hL : 1 ≤ L) (hLk : L ≤ k) (h1 : Z3NetF.H1 F L Φ) (c : Fin s)
    (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ) (J : Fin s → ℕ) (hJ : ∀ d, J d < k)
    (hstep : ∀ d, AxisStepF s q k v w d (e d) (J d)) (r : Fin (s * k - k)) (hr : (r : ℕ) = 0) :
    DgF s q k Φ c w ⟨k + r, Z3NetU.Proofs.sk_sub_add r⟩ - DgF s q k Φ c v ⟨k + r, Z3NetU.Proofs.sk_sub_add r⟩ =
      ((∑ d, e d * Z3NetF.Msum F (min (J d) (L - 1)) c d : ℤ) : ZMod q) := by
  simp only [DgF]
  rw [Z3NetU.Proofs.graphGen_off, Z3NetU.Proofs.graphGen_off, ← sum_sub_distrib]
  push_cast
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_sub_distrib]
  have hmin : min (J d) (L - 1) < k := by have := hJ d; omega
  rw [Z3NetF.Msum, ← Z3NetU.Proofs.sum_tab_indicator (fun t => F t c d) k _ hmin]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [← mul_sub, h1 c d r hr l, hstep d l]
  have hl := l.isLt
  by_cases ha : k - 1 - (l : ℕ) < L
  · rw [if_pos ha]
    by_cases hb : k - 1 - (l : ℕ) ≤ J d
    · rw [if_pos hb, if_pos (by omega)]; ring
    · rw [if_neg hb, if_neg (by omega)]; ring
  · have hb : ¬ (k - 1 - (l : ℕ) ≤ min (J d) (L - 1)) := by
      have := min_le_right (J d) (L - 1); omega
    rw [if_neg ha, if_neg hb]; ring

/-- (H2): if no other axis moves, the tail of coordinate `c` does not change. -/
lemma tl_eq_of_onlyF (hq : 1 < q) (h2 : Z3NetF.H2 Φ) (c : Fin s) (v w : Fin (s * k) → ZMod q)
    (hother : ∀ d, d ≠ c → Z3NetU.Proofs.cellN s q k w d = Z3NetU.Proofs.cellN s q k v d) :
    tlF s q k Φ w c = tlF s q k Φ v c := by
  unfold tlF Z3NetU.Proofs.tail
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
  change ((Z3NetU.graphGen s k Φ c *ᵥ w) _).val = ((Z3NetU.graphGen s k Φ c *ᵥ v) _).val
  rw [e1, e2]
  congr 1
  refine sum_congr rfl fun d _ => sum_congr rfl fun l _ => ?_
  by_cases hd : d = c
  · subst hd; rw [h2 d _ (by simp; omega) l]; simp
  · rw [Z3NetU.Proofs.digits_eq_of_cellN_eq s q hq k v w d (hother d hd) l]

/-- `b_i` is at most the value at any representative of `σ_i`. -/
lemma bval_le_of (hq : 0 < q) (e : Fin s → ℤ) (j : Fin s → ℕ) (i : Fin s) (t : ℤ)
    (ht : t ≡ Z3NetF.sigma F L e j i [ZMOD q]) (htq : |t| < q) :
    Z3NetF.bval q F L e j i ≤
      max 0 (|e i * q + t| - if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then 0 else 1) := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  set σ := Z3NetF.sigma F L e j i
  have hδ0 : 0 ≤ σ % (q : ℤ) := Int.emod_nonneg _ (by omega)
  have hδ1 : σ % (q : ℤ) < q := Int.emod_lt_of_pos _ hq'
  have htmod : t % (q : ℤ) = σ % (q : ℤ) := ht
  rw [abs_lt] at htq
  -- `t = σ mod q` or `t = σ mod q - q`
  have hcases : t = σ % (q : ℤ) ∨ t = σ % (q : ℤ) - q := by
    have hd := Int.mul_ediv_add_emod t (q : ℤ)
    have h0' := Int.emod_nonneg t (show (q : ℤ) ≠ 0 by omega)
    have h1' := Int.emod_lt_of_pos t hq'
    have hb1 : -1 ≤ t / (q : ℤ) := by
      by_contra h; push_neg at h
      have : t / (q : ℤ) ≤ -2 := by omega
      nlinarith
    have hb2 : t / (q : ℤ) ≤ 0 := by
      by_contra h; push_neg at h
      have : 1 ≤ t / (q : ℤ) := by omega
      nlinarith
    rcases (show t / (q : ℤ) = -1 ∨ t / (q : ℤ) = 0 by omega) with h | h
    · right; rw [h] at hd; rw [← htmod]; linarith
    · left; rw [h] at hd; rw [← htmod]; linarith
  unfold Z3NetF.bval
  simp only []
  set jit : ℤ := if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then 0 else 1 with hjit
  by_cases h0 : σ % (q : ℤ) = 0
  · rw [if_pos h0]
    rcases hcases with h | h
    · rw [h, h0, add_zero]
    · rw [h0] at h; omega
  · rw [if_neg h0]
    rcases hcases with h | h
    · rw [h]; exact min_le_left _ _
    · rw [h, ← add_sub_assoc]; exact min_le_right _ _

end ss

section ss2

variable (s q k : ℕ) [NeZero q] (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
  (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ)

/-- The core per-coordinate bound of `lem:Ss`, in terms of digits. -/
lemma coord_core (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ)
    (J : Fin s → ℕ) (hJ : ∀ d, J d < k) (hstep : ∀ d, AxisStepF s q k v w d (e d) (J d))
    (hzero : ∀ d, e d = 0 → Z3NetU.Proofs.cellN s q k w d = Z3NetU.Proofs.cellN s q k v d)
    (i : Fin s) :
    Z3NetF.bval q F L e J i * (q : ℤ) ^ (s * k - k - 1) ≤
      |(q : ℤ) ^ (s * k - k - 1) * (e i * q + ((o0F s q k Φ w i : ℤ) - o0F s q k Φ v i)) +
        ((tlF s q k Φ w i : ℤ) - tlF s q k Φ v i)| := by
  have hq0 : 0 < q := by omega
  have hsk : k + 1 ≤ s * k := by nlinarith
  have hkk : k < s * k := by omega
  set u : ℤ := (q : ℤ) ^ (s * k - k - 1) with hu_def
  have hu : 0 < u := by positivity
  set tt : ℤ := (o0F s q k Φ w i : ℤ) - o0F s q k Φ v i with htt
  -- `tt ≡ σ_i`, `|tt| < q`
  have htq : |tt| < q := by
    have a1 := Z3NetU.Proofs.dv_lt s q k (DgF s q k Φ i w) k
    have a2 := Z3NetU.Proofs.dv_lt s q k (DgF s q k Φ i v) k
    simp only [htt, o0F]
    rw [abs_lt]; constructor <;> omega
  have hσ : tt ≡ Z3NetF.sigma F L e J i [ZMOD q] := by
    have h := Dg_off_subF s q k Φ F L hL hLk h1 i v w e J hJ hstep ⟨0, by omega⟩ rfl
    have e1 := o0_castF s q k Φ w i hkk
    have e2 := o0_castF s q k Φ v i hkk
    rw [← ZMod.intCast_eq_intCast_iff]
    simp only [htt, Z3NetF.sigma]
    push_cast
    rw [e1, e2]
    simpa using h
  have hb := bval_le_of s q F L hq0 e J i tt hσ htq
  have htl : |(tlF s q k Φ w i : ℤ) - tlF s q k Φ v i| < u := by
    have a1 := Z3NetU.Proofs.tail_lt s q k hsk (DgF s q k Φ i w)
    have a2 := Z3NetU.Proofs.tail_lt s q k hsk (DgF s q k Φ i v)
    have a1' : ((tlF s q k Φ w i : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast a1
    have a2' : ((tlF s q k Φ v i : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast a2
    rw [abs_lt]; constructor <;> omega
  have hbu : Z3NetF.bval q F L e J i * u ≤
      max 0 (|e i * q + tt| - if e i ≠ 0 ∧ ∀ d, d ≠ i → e d = 0 then 0 else 1) * u :=
    mul_le_mul_of_nonneg_right hb hu.le
  refine hbu.trans ?_
  split_ifs with hj
  · have htl0 : (tlF s q k Φ w i : ℤ) - tlF s q k Φ v i = 0 := by
      rw [tl_eq_of_onlyF s q k Φ (by omega) h2 i v w (fun d hd => hzero d (hj.2 d hd))]; ring
    rw [htl0, add_zero, sub_zero, abs_mul, abs_of_pos hu, max_eq_right (abs_nonneg _), mul_comm]
  · have a := abs_add_le (u * (e i * q + tt) + ((tlF s q k Φ w i : ℤ) - tlF s q k Φ v i))
      (-((tlF s q k Φ w i : ℤ) - tlF s q k Φ v i))
    rw [add_neg_cancel_right, abs_neg, abs_mul, abs_of_pos hu] at a
    rcases le_total (|e i * q + tt| - 1) 0 with hc | hc
    · rw [max_eq_left hc, zero_mul]; exact abs_nonneg _
    · rw [max_eq_right hc]; nlinarith

/-- Classification of the cell step of one axis (not far). -/
lemma axis_classifyF (hq : 3 ≤ q) (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (d : Fin s)
    (hnf : ¬ ∀ z : ℤ, 2 ≤ |(Z3NetU.Proofs.cellN s q k w d : ℤ) - Z3NetU.Proofs.cellN s q k v d - z * (q : ℤ) ^ k|) :
    ∃ e : ℤ, (-1 ≤ e ∧ e ≤ 1) ∧
      ((Z3NetU.Proofs.cellN s q k w d : ℤ) = ((Z3NetU.Proofs.cellN s q k v d : ℤ) + e) % ((q ^ k : ℕ) : ℤ)) ∧
      AxisStepF s q k v w d e (Z3NetF.carryLen q k (Z3NetU.Proofs.cellN s q k v d) e) ∧
      (e = 0 → Z3NetU.Proofs.cellN s q k w d = Z3NetU.Proofs.cellN s q k v d) := by
  have hq1 : 1 < q := by omega
  have hP : 3 ≤ q ^ k := by
    calc 3 ≤ q ^ 1 := by simpa using hq
      _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  have hv := Z3NetU.Proofs.cellN_lt s q k v d
  have hw := Z3NetU.Proofs.cellN_lt s q k w d
  rcases Z3NetU.Proofs.step_cases (q ^ k) (Z3NetU.Proofs.cellN s q k v d) (Z3NetU.Proofs.cellN s q k w d) hP
    hv hw with h | h | h | h
  · refine ⟨0, by norm_num, ?_, axis_zeroF s q k hq1 v w d h _, fun _ => h⟩
    rw [h, add_zero, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hv)]
  · refine ⟨1, by norm_num, ?_, axis_plusF s q k hq1 v w d h, fun h1 => absurd h1 (by norm_num)⟩
    rw [h]; push_cast; rfl
  · refine ⟨-1, by norm_num, ?_, axis_minusF s q k hq1 v w d h, fun h1 => absurd h1 (by norm_num)⟩
    set W := Z3NetU.Proofs.cellN s q k w d
    set V := Z3NetU.Proofs.cellN s q k v d
    have hcase : (V : ℤ) + (-1) = (W : ℤ) + (if W + 1 < q ^ k then 0 else -1) * ((q ^ k : ℕ) : ℤ) := by
      split_ifs with hlt
      · rw [Nat.mod_eq_of_lt hlt] at h; rw [h]; push_cast; ring
      · have h' : W + 1 = q ^ k := by omega
        have h'' : (W : ℤ) + 1 = (q : ℤ) ^ k := by exact_mod_cast h'
        rw [h', Nat.mod_self] at h; rw [h]; push_cast; linarith
    rw [hcase, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hw)]
  · exact absurd h hnf

end ss2

section ss3

variable (s q k : ℕ) [NeZero q] (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
  (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ)

lemma axis_of_cell (hq : 3 ≤ q) (hk : 1 ≤ k) (v w : Fin (s * k) → ZMod q) (d : Fin s) (e : ℤ)
    (he : -1 ≤ e ∧ e ≤ 1)
    (hc : (Z3NetU.Proofs.cellN s q k w d : ℤ) = ((Z3NetU.Proofs.cellN s q k v d : ℤ) + e) % ((q ^ k : ℕ) : ℤ)) :
    AxisStepF s q k v w d e (Z3NetF.carryLen q k (Z3NetU.Proofs.cellN s q k v d) e) ∧
      (e = 0 → Z3NetU.Proofs.cellN s q k w d = Z3NetU.Proofs.cellN s q k v d) := by
  have hq1 : 1 < q := by omega
  have hv := Z3NetU.Proofs.cellN_lt s q k v d
  have hw := Z3NetU.Proofs.cellN_lt s q k w d
  set W := Z3NetU.Proofs.cellN s q k w d
  set V := Z3NetU.Proofs.cellN s q k v d
  have hP : (0 : ℤ) < ((q ^ k : ℕ) : ℤ) := by positivity
  rcases (show e = 0 ∨ e = 1 ∨ e = -1 by omega) with h | h | h
  · subst h
    have hWV : W = V := by
      rw [add_zero, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hv)] at hc
      exact_mod_cast hc
    exact ⟨axis_zeroF s q k hq1 v w d hWV _, fun _ => hWV⟩
  · subst h
    have hWV : W = (V + 1) % q ^ k := by
      have : ((W : ℕ) : ℤ) = (((V + 1) % q ^ k : ℕ) : ℤ) := by rw [hc]; push_cast; rfl
      exact_mod_cast this
    exact ⟨axis_plusF s q k hq1 v w d hWV, fun h1 => absurd h1 (by norm_num)⟩
  · subst h
    have hVW : V = (W + 1) % q ^ k := by
      have : ((V : ℕ) : ℤ) = (((W + 1) % q ^ k : ℕ) : ℤ) := by
        rw [Int.natCast_mod, Nat.cast_add, Nat.cast_one, hc, Int.emod_add_emod,
          show (V : ℤ) + -1 + 1 = V by ring, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hv)]
      exact_mod_cast this
    exact ⟨axis_minusF s q k hq1 v w d hVW, fun h1 => absurd h1 (by norm_num)⟩

omit [NeZero q] in
lemma carryLen_lt (hk : 1 ≤ k) (n : ℕ) (e : ℤ) : Z3NetF.carryLen q k n e < k := by
  unfold Z3NetF.carryLen
  split_ifs
  · have := Nat.findGreatest_le (P := fun t => q ^ t ∣ n + 1) (k - 1); omega
  · have := Nat.findGreatest_le (P := fun t => q ^ t ∣ n) (k - 1); omega

theorem Ss_coord_core (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (v w : Fin (s * k) → ZMod q) (e : Fin s → ℤ)
    (he : ∀ d, -1 ≤ e d ∧ e d ≤ 1)
    (hcell : ∀ d, ((Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) w d /
        q ^ (s * k - k) : ℕ) : ℤ) = ((Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) v d /
        q ^ (s * k - k) : ℕ) + e d) % (q ^ k : ℕ))
    (i : Fin s) :
    Z3NetF.bval q F L e (fun d => Z3NetF.carryLen q k (Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k)
        (fun _ => k) Φ) v d / q ^ (s * k - k)) (e d)) i * (q ^ (s * k - k) : ℕ) ≤
      (q : ℤ) * |e i * (q ^ (s * k - k) : ℕ) +
        ((Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) w i % q ^ (s * k - k) : ℕ) : ℤ) -
        ((Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) v i % q ^ (s * k - k) : ℕ) : ℤ)| := by
  have hsk : k + 1 ≤ s * k := by nlinarith
  have hcv := fun d => cell_of_digPoint s q k Φ hsk v d
  have hcw := fun d => cell_of_digPoint s q k Φ hsk w d
  simp only [(hcv _).1, (hcw _).1, (hcv _).2, (hcw _).2] at hcell ⊢
  have hax := fun d => axis_of_cell s q k hq hk v w d (e d) (he d) (by exact_mod_cast hcell d)
  have hcore := coord_core s q k Φ F L hs hq (by omega) hL hLk h1 h2 v w e
    (fun d => Z3NetF.carryLen q k (Z3NetU.Proofs.cellN s q k v d) (e d))
    (fun d => carryLen_lt q k (by omega) _ _) (fun d => (hax d).1) (fun d => (hax d).2) i
  have hpow : ((q ^ (s * k - k) : ℕ) : ℤ) = (q : ℤ) ^ (s * k - k - 1) * q := by
    push_cast; rw [← pow_succ]; congr 1; omega
  rw [hpow]
  push_cast
  have e1 : e i * ((q : ℤ) ^ (s * k - k - 1) * q) + ((q : ℤ) ^ (s * k - k - 1) * o0F s q k Φ w i + tlF s q k Φ w i) -
      ((q : ℤ) ^ (s * k - k - 1) * o0F s q k Φ v i + tlF s q k Φ v i) =
      (q : ℤ) ^ (s * k - k - 1) * (e i * q + ((o0F s q k Φ w i : ℤ) - o0F s q k Φ v i)) +
        ((tlF s q k Φ w i : ℤ) - tlF s q k Φ v i) := by ring
  rw [e1]
  have hq0 : (0 : ℤ) ≤ q := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcore hq0]

end ss3

/-- A residue `Y` with `G ≤ |Y| ≤ N - G` has toroidal residue at least `G`. -/
lemma cres_ge_mid (N : ℕ) (Y G : ℤ) (hG : 0 ≤ G) (h1 : G ≤ |Y|) (h2 : |Y| ≤ N - G) :
    G ≤ (Z3NetU.cres N Y : ℤ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN0
  · subst hN
    have : G = 0 := by have := abs_nonneg Y; push_cast at h2; omega
    rw [this]; positivity
  obtain ⟨z, hz⟩ := Z3NetU.Proofs.cres_eq_abs_sub N hN0 Y
  rw [hz]
  rcases lt_trichotomy z 0 with hz0 | hz0 | hz0
  · have : (N : ℤ) ≤ -z * N := by nlinarith
    rw [abs_of_nonneg (by have := neg_abs_le Y; nlinarith)]
    have := neg_abs_le Y; nlinarith
  · subst hz0; simpa using h1
  · have : (N : ℤ) ≤ z * N := by nlinarith
    rw [abs_of_nonpos (by have := le_abs_self Y; nlinarith)]
    have := le_abs_self Y; nlinarith

section ss4

variable (s q k : ℕ) [NeZero q] (Φ : Fin s → Fin s → Matrix (Fin (s * k - k)) (Fin k) (ZMod q))
  (F : ℕ → Fin s → Fin s → ℤ) (L : ℕ)

lemma sep_main (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, Z3NetF.IsConfig k e j → B ≤ ∑ i, Z3NetF.bval q F L e j i ^ 2)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ 2 * ∑ c : Fin s,
      ((Z3NetU.cres (q ^ (s * k))
        ((Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) w c : ℤ) -
         (Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) v c : ℤ)) : ℕ) : ℤ) ^ 2 := by
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
    Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) with hXdef
  have hX : ∀ c, (X w c : ℤ) - X v c =
      (q : ℤ) ^ (s * k - k) * ((Z3NetU.Proofs.cellN s q k w c : ℤ) - Z3NetU.Proofs.cellN s q k v c) +
      (u * ((o0F s q k Φ w c : ℤ) - o0F s q k Φ v c) + ((tlF s q k Φ w c : ℤ) - tlF s q k Φ v c)) := by
    intro c; rw [hXdef, X_decompF s q k Φ hsk, X_decompF s q k Φ hsk]; ring
  have htl : ∀ c, |(tlF s q k Φ w c : ℤ) - tlF s q k Φ v c| < u := by
    intro c
    have a1 := Z3NetU.Proofs.tail_lt s q k hsk (DgF s q k Φ c w)
    have a2 := Z3NetU.Proofs.tail_lt s q k hsk (DgF s q k Φ c v)
    have a1' : ((tlF s q k Φ w c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast a1
    have a2' : ((tlF s q k Φ v c : ℕ) : ℤ) < u := by rw [hu_def]; exact_mod_cast a2
    rw [abs_lt]; constructor <;> omega
  have ho : ∀ c, |(o0F s q k Φ w c : ℤ) - o0F s q k Φ v c| < q := by
    intro c
    have a1 := Z3NetU.Proofs.dv_lt s q k (DgF s q k Φ c w) k
    have a2 := Z3NetU.Proofs.dv_lt s q k (DgF s q k Φ c v) k
    simp only [o0F]
    rw [abs_lt]; constructor <;> omega
  have hsum_nonneg : ∀ c ∈ (univ : Finset (Fin s)), (0 : ℤ) ≤
      ((Z3NetU.cres (q ^ (s * k)) ((X w c : ℤ) - (X v c : ℤ)) : ℕ) : ℤ) ^ 2 :=
    fun c _ => sq_nonneg _
  have hu2 : (q : ℤ) ^ (2 * (s * k - k)) = (q : ℤ) ^ 2 * u ^ 2 := by
    rw [hu_def, ← pow_mul, ← pow_add]; congr 1; omega
  by_cases hfar : ∃ c, ∀ z : ℤ, 2 ≤ |(Z3NetU.Proofs.cellN s q k w c : ℤ) -
      Z3NetU.Proofs.cellN s q k v c - z * (q : ℤ) ^ k|
  · obtain ⟨c, hc⟩ := hfar
    have hR : |u * ((o0F s q k Φ w c : ℤ) - o0F s q k Φ v c) + ((tlF s q k Φ w c : ℤ) - tlF s q k Φ v c)| <
        (q : ℤ) ^ (s * k - k) := by
      have a2 := abs_add_le (u * ((o0F s q k Φ w c : ℤ) - o0F s q k Φ v c)) ((tlF s q k Φ w c : ℤ) - tlF s q k Φ v c)
      rw [abs_mul, abs_of_pos hu] at a2
      have := htl c
      have b1 : |(o0F s q k Φ w c : ℤ) - o0F s q k Φ v c| ≤ q - 1 := by have := ho c; omega
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
    have hcore := fun c => coord_core s q k Φ F L hs hq (by omega) hL hLk h1 h2 v w e J hJ hax hzero c
    -- the raw difference in coordinate `c`, in units of `q^(m-k-1)`: `Y_c = u (e_c q + Δr_c) + Δf_c`
    set Y : Fin s → ℤ := fun c => u * (e c * q + ((o0F s q k Φ w c : ℤ) - o0F s q k Φ v c)) +
      ((tlF s q k Φ w c : ℤ) - tlF s q k Φ v c) with hYdef
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
      have hV : |e c * q + ((o0F s q k Φ w c : ℤ) - o0F s q k Φ v c)| ≤ 2 * q - 1 := by
        have h1 := abs_add_le (e c * q) ((o0F s q k Φ w c : ℤ) - o0F s q k Φ v c)
        have h2 := ho c
        linarith
      have h1 := abs_add_le (u * (e c * q + ((o0F s q k Φ w c : ℤ) - o0F s q k Φ v c)))
        ((tlF s q k Φ w c : ℤ) - tlF s q k Φ v c)
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
        |u * (e c * q + ((o0F s q k Φ w c : ℤ) - o0F s q k Φ v c)) + ((tlF s q k Φ w c : ℤ) - tlF s q k Φ v c)| := by
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

theorem Ss_sep_core (hs : 2 ≤ s) (hq : 3 ≤ q) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLk : L ≤ k)
    (h1 : Z3NetF.H1 F L Φ) (h2 : Z3NetF.H2 Φ) (B : ℤ) (hBq : B ≤ (q : ℤ) ^ 2)
    (hB : ∀ e j, Z3NetF.IsConfig k e j → B ≤ ∑ i, Z3NetF.bval q F L e j i ^ 2)
    (v w : Fin (s * k) → ZMod q) (hvw : v ≠ w) :
    (q : ℤ) ^ (2 * (s * k - k)) * B ≤ (q : ℤ) ^ 2 *
      (Z3NetF.torusDist2 (q ^ (s * k)) (Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) v)
        (Z3NetF.digPoint q (s * k) (Z3NetF.graphGenK (m := s * k) (fun _ => k) Φ) w) : ℤ) := by
  have h := sep_main s q k Φ F L hs hq hk hL hLk h1 h2 B hBq hB w v (Ne.symm hvw)
  unfold Z3NetF.torusDist2
  push_cast
  simpa [cres_eq] using h

end ss4

end

end Z3NetF.Proofs

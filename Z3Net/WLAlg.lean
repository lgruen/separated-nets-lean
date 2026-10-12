/-
Entry WhyLat: `lem:hom`, `cor:linoff` (a), (b) and `lem:phase` (i) of `paper/core.tex`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.WLDefs

@[expose] public section

/-!
# `lem:hom`, `cor:linoff` (a), (b), `lem:phase` (i)
-/

namespace Z3NetF

open Matrix Finset

/-! ## `lem:hom` -/

theorem natCast_mod_pow {q j : ℕ} (hj : 1 ≤ j) (a : ℕ) :
    (((a % q ^ j : ℕ)) : ZMod q) = (a : ZMod q) := by
  rw [← ZMod.natCast_mod (a % q ^ j) q, Nat.mod_mod_of_dvd _ (dvd_pow_self q (by omega)),
    ZMod.natCast_mod]

theorem phiDig_of_zero {q j : ℕ} (hj : 1 ≤ j) (β : Fin j → ZMod q)
    (hβ : ∀ i : Fin j, 1 ≤ (i : ℕ) → β i = 0) (P : ZMod (q ^ j)) :
    phiDig q j β P = β ⟨0, by omega⟩ * (P.val : ZMod q) := by
  unfold phiDig
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp [digitAt]
  · intro b _ hb
    rw [hβ b (by
      rcases Nat.eq_zero_or_pos b with h | h
      · exact absurd (Fin.ext h) hb
      · exact h), zero_mul]
  · simp

theorem hom_iff' (q j : ℕ) (hq : 2 ≤ q) (hj : 1 ≤ j) (β : Fin j → ZMod q) :
    (∀ P P' : ZMod (q ^ j), phiDig q j β (P + P') = phiDig q j β P + phiDig q j β P') ↔
      ∀ i : Fin j, 1 ≤ (i : ℕ) → β i = 0 := by
  haveI : NeZero (q ^ j) := ⟨by positivity⟩
  constructor
  · intro hadd i hi
    -- φ(n) = n φ(1)
    have h0 : phiDig q j β 0 = 0 := by
      have := hadd 0 0; rw [add_zero] at this
      linear_combination -this
    have hn : ∀ n : ℕ, phiDig q j β (n : ZMod (q ^ j)) = (n : ZMod q) * phiDig q j β 1 := by
      intro n
      induction n with
      | zero => simp [h0]
      | succ n ih => rw [Nat.cast_succ, hadd, ih, Nat.cast_succ]; ring
    have hqi : (q ^ (i : ℕ) : ℕ) < q ^ j := Nat.pow_lt_pow_right (by omega) i.isLt
    have hP := hn (q ^ (i : ℕ))
    have hz : ((q ^ (i : ℕ) : ℕ) : ZMod q) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact dvd_pow_self q (by omega)
    rw [hz, zero_mul] at hP
    -- the left side is β_i
    have hval : ((q ^ (i : ℕ) : ℕ) : ZMod (q ^ j)).val = q ^ (i : ℕ) := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hqi]
    unfold phiDig at hP
    rw [Finset.sum_eq_single i] at hP
    · simp only [digitAt, hval, Nat.div_self (by positivity : 0 < q ^ (i : ℕ))] at hP
      simpa using hP
    · intro k _ hk
      simp only [digitAt, hval]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hk) with h | h
      · rw [Nat.pow_div h.le (by omega)]
        have : ((q ^ ((i : ℕ) - k) : ℕ) : ZMod q) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]; exact dvd_pow_self q (by omega)
        rw [this, mul_zero]
      · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by omega) h)]; simp
    · simp
  · intro hβ P P'
    rw [phiDig_of_zero hj β hβ, phiDig_of_zero hj β hβ, phiDig_of_zero hj β hβ, ZMod.val_add,
      natCast_mod_pow hj]
    push_cast; ring

/-! ## `cor:linoff` (a) -/

theorem modVec_add (q : ℕ) {s : ℕ} (Y Y' : Fin s → ℤ) :
    modVec q (Y + Y') = modVec q Y + modVec q Y' := by
  funext c; simp [modVec]

theorem modVec_neg (q : ℕ) {s : ℕ} (Y : Fin s → ℤ) : modVec q (-Y) = -modVec q Y := by
  funext c; simp [modVec]

theorem modVec_sub (q : ℕ) {s : ℕ} (Y Y' : Fin s → ℤ) :
    modVec q (Y - Y') = modVec q Y - modVec q Y' := by
  funext c; simp [modVec]

theorem linoff_a' (q : ℕ) [NeZero q] {s k : ℕ} (H : Matrix (Fin k) (Fin s) (ZMod q))
    (b : Fin k → ZMod q) :
    (∃ L : AddSubgroup (Fin s → ℤ), (∀ Y, Y ∈ L ↔ H *ᵥ modVec q Y = 0) ∧
      ∀ z : Fin s → ℤ, (q : ℤ) • z ∈ L) ∧
    (∀ Y : Fin s → ℤ, H *ᵥ modVec q Y = 0 ↔
      ∃ v : Fin s → ZMod q, H *ᵥ v = 0 ∧ ∃ z : Fin s → ℤ, Y = liftVec q v + (q : ℤ) • z) ∧
    (∀ Y₀ Y : Fin s → ℤ, H *ᵥ modVec q Y₀ = b →
      (H *ᵥ modVec q Y = b ↔ H *ᵥ modVec q (Y - Y₀) = 0)) := by
  have hqz : ∀ z : Fin s → ℤ, modVec q ((q : ℤ) • z) = 0 := by
    intro z; funext c; simp [modVec]
  let L : AddSubgroup (Fin s → ℤ) :=
    { carrier := {Y | H *ᵥ modVec q Y = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [modVec_add, mulVec_add, ha, hb, add_zero]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        have : modVec q (0 : Fin s → ℤ) = 0 := by funext c; simp [modVec]
        rw [this, mulVec_zero]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [modVec_neg, mulVec_neg, ha, neg_zero] }
  refine ⟨⟨L, fun Y => Iff.rfl, fun z => ?_⟩, fun Y => ?_, fun Y₀ Y h0 => ?_⟩
  · show H *ᵥ modVec q ((q : ℤ) • z) = 0
    rw [hqz, mulVec_zero]
  · constructor
    · intro hY
      refine ⟨modVec q Y, hY, fun c => Y c / q, ?_⟩
      funext c
      simp only [liftVec, modVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ZMod.val_intCast]
      have := Int.mul_ediv_add_emod (Y c) q
      linarith
    · rintro ⟨v, hv, z, rfl⟩
      have : modVec q (liftVec q v + (q : ℤ) • z) = v := by
        rw [modVec_add, hqz, add_zero]
        funext c; simp [modVec, liftVec]
      rw [this, hv]
  · rw [modVec_sub, mulVec_sub, h0, sub_eq_zero]

/-! ## `cor:linoff` (b) -/

theorem two_digit {q : ℕ} (hq : 0 < q) (A w : ℕ) (hw : w < q) :
    (q * A + w) % q ^ 2 = q * (A % q) + w := by
  have hA := Nat.div_add_mod A q
  have hlt : q * (A % q) + w < q ^ 2 := by
    have := Nat.mod_lt A hq
    have : q * (A % q) + w < q * (A % q) + q := by omega
    calc q * (A % q) + w < q * (A % q + 1) := by rw [mul_add, mul_one]; exact this
      _ ≤ q * q := Nat.mul_le_mul_left _ (by omega)
      _ = q ^ 2 := by ring
  have e : q * A + w = q ^ 2 * (A / q) + (q * (A % q) + w) := by
    conv_lhs => rw [← hA]
    ring
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem digit_pair_eq {q : ℕ} (hq : 0 < q) {a w a' w' : ℕ} (ha : a < q) (ha' : a' < q)
    (hw : w < q) (hw' : w' < q) (h : q * a + w = q * a' + w') : a = a' ∧ w = w' := by
  have h1 : (q * a + w) % q = (q * a' + w') % q := by rw [h]
  have h2 : (q * a + w) / q = (q * a' + w') / q := by rw [h]
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hw'] at h1
  rw [Nat.mul_add_div hq, Nat.mul_add_div hq, Nat.div_eq_of_lt hw, Nat.div_eq_of_lt hw'] at h2
  omega

theorem natCast_two_digit_iff {q : ℕ} (hq : 0 < q) (A w A' w' : ℕ) (hw : w < q) (hw' : w' < q) :
    ((q * A + w : ℕ) : ZMod (q ^ 2)) = ((q * A' + w' : ℕ) : ZMod (q ^ 2)) ↔
      A % q = A' % q ∧ w = w' := by
  rw [ZMod.natCast_eq_natCast_iff', two_digit hq A w hw, two_digit hq A' w' hw']
  constructor
  · intro h
    exact digit_pair_eq hq (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) hw hw' h
  · rintro ⟨h1, rfl⟩; rw [h1]

/-- The point of `T_B` with parameter `ℓ`. -/
def FB (q : ℕ) {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod q)) (ℓ : Fin s → ZMod q) :
    Fin s → ZMod (q ^ 2) :=
  fun i => ((q * (ℓ i).val + ((B *ᵥ ℓ) i).val : ℕ) : ZMod (q ^ 2))

theorem TB_eq (q : ℕ) {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod q)) :
    TB q B = Set.range (FB q B) := rfl

/-- The sum of two points of `T_B` lies in `T_B` iff `B c ≡ 0` for their carry vector. -/
theorem FB_add_iff {q : ℕ} [NeZero q] {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod q))
    (ℓ ℓ' : Fin s → ZMod q) :
    (∃ ℓ'', FB q B ℓ'' = FB q B ℓ + FB q B ℓ') ↔
      B *ᵥ (fun i => ((carryVec q (fun i => ((B *ᵥ ℓ) i).val) (fun i => ((B *ᵥ ℓ') i).val) i : ℕ) :
        ZMod q)) = 0 := by
  have hq : 0 < q := Nat.pos_of_neZero q
  set v : Fin s → ℕ := fun i => ((B *ᵥ ℓ) i).val with hv
  set v' : Fin s → ℕ := fun i => ((B *ᵥ ℓ') i).val with hv'
  set cv : Fin s → ZMod q := fun i => ((carryVec q v v' i : ℕ) : ZMod q) with hcv
  -- the sum, as a two-digit cast
  have hsum : ∀ i, (FB q B ℓ + FB q B ℓ') i = ((q * ((ℓ i).val + (ℓ' i).val + carryVec q v v' i) +
      (v i + v' i) % q : ℕ) : ZMod (q ^ 2)) := by
    intro i
    simp only [FB, Pi.add_apply, carryVec]
    have := Nat.div_add_mod (v i + v' i) q
    rw [← Nat.cast_add]
    congr 1
    simp only [hv, hv'] at this ⊢
    linarith
  have hw : ∀ i, (v i + v' i) % q < q := fun i => Nat.mod_lt _ hq
  -- `(v i + v' i : ZMod q) = (Bℓ + Bℓ') i`
  have hvv : ∀ i, (((v i + v' i) % q : ℕ) : ZMod q) = (B *ᵥ ℓ) i + (B *ᵥ ℓ') i := by
    intro i; rw [ZMod.natCast_mod]; simp [hv, hv']
  constructor
  · rintro ⟨ℓ'', h⟩
    funext i
    have hi := congrFun h i
    rw [hsum i] at hi
    simp only [FB] at hi
    obtain ⟨h1, h2⟩ := (natCast_two_digit_iff hq _ _ _ _ (ZMod.val_lt _) (hw i)).1 hi
    -- ℓ'' i = ℓ i + ℓ' i + c i
    have hl : ℓ'' = ℓ + ℓ' + cv := by
      funext k
      have hk := congrFun h k
      rw [hsum k] at hk
      simp only [FB] at hk
      obtain ⟨k1, _⟩ := (natCast_two_digit_iff hq _ _ _ _ (ZMod.val_lt _) (hw k)).1 hk
      rw [Nat.mod_eq_of_lt (ZMod.val_lt _)] at k1
      have : ((ℓ'' k).val : ZMod q) = (((ℓ k).val + (ℓ' k).val + carryVec q v v' k) % q : ℕ) := by
        rw [k1]
      rw [ZMod.natCast_zmod_val, ZMod.natCast_mod] at this
      rw [this]; simp [hcv]
    have hB : (B *ᵥ ℓ'') i = (B *ᵥ ℓ) i + (B *ᵥ ℓ') i := by
      rw [← hvv i, ← h2, ZMod.natCast_zmod_val]
    rw [hl, mulVec_add, mulVec_add] at hB
    simp only [Pi.add_apply] at hB
    simpa using hB
  · intro hc
    refine ⟨ℓ + ℓ' + cv, ?_⟩
    funext i
    rw [hsum i]
    simp only [FB]
    rw [natCast_two_digit_iff hq _ _ _ _ (ZMod.val_lt _) (hw i)]
    constructor
    · rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
      simp only [Pi.add_apply, hcv, ZMod.val_add, ZMod.val_natCast]
      conv_rhs => rw [Nat.add_mod]
    · rw [mulVec_add, mulVec_add, hc]
      simp only [Pi.add_apply, Pi.zero_apply, ZMod.val_zero, add_zero, ZMod.val_add, hv, hv',
        Nat.mod_mod]

theorem nsmul_mem_TB {q : ℕ} [NeZero q] {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod q))
    (hadd : ∀ x ∈ TB q B, ∀ y ∈ TB q B, x + y ∈ TB q B) (h0 : (0 : Fin s → ZMod (q ^ 2)) ∈ TB q B)
    (x : Fin s → ZMod (q ^ 2)) (hx : x ∈ TB q B) : ∀ n : ℕ, n • x ∈ TB q B := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul]; exact hadd _ ih _ hx

theorem linoff_b' (q : ℕ) (hq : 2 ≤ q) {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod q)) :
    ((∃ G : AddSubgroup (Fin s → ZMod (q ^ 2)), (G : Set (Fin s → ZMod (q ^ 2))) = TB q B) ↔
      ∀ ℓ ℓ' : Fin s → ZMod q,
        B *ᵥ (fun i => ((carryVec q (fun i => ((B *ᵥ ℓ) i).val) (fun i => ((B *ᵥ ℓ') i).val) i :
          ℕ) : ZMod q)) = 0) ∧
    (0 < s → IsUnit B →
      ¬ ∃ G : AddSubgroup (Fin s → ZMod (q ^ 2)), (G : Set (Fin s → ZMod (q ^ 2))) = TB q B) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero (q ^ 2) := ⟨by positivity⟩
  have hq0 : 0 < q := by omega
  have h0 : (0 : Fin s → ZMod (q ^ 2)) ∈ TB q B := ⟨0, by funext i; simp [FB]⟩
  have hiff : (∃ G : AddSubgroup (Fin s → ZMod (q ^ 2)), (G : Set (Fin s → ZMod (q ^ 2))) = TB q B) ↔
      ∀ ℓ ℓ' : Fin s → ZMod q,
        B *ᵥ (fun i => ((carryVec q (fun i => ((B *ᵥ ℓ) i).val) (fun i => ((B *ᵥ ℓ') i).val) i :
          ℕ) : ZMod q)) = 0 := by
    constructor
    · rintro ⟨G, hG⟩ ℓ ℓ'
      have h1 : FB q B ℓ ∈ G := by rw [← SetLike.mem_coe, hG]; exact ⟨ℓ, rfl⟩
      have h2 : FB q B ℓ' ∈ G := by rw [← SetLike.mem_coe, hG]; exact ⟨ℓ', rfl⟩
      have h3 := G.add_mem h1 h2
      rw [← SetLike.mem_coe, hG] at h3
      obtain ⟨ℓ'', h⟩ := h3
      exact (FB_add_iff B ℓ ℓ').1 ⟨ℓ'', h⟩
    · intro hc
      have hadd : ∀ x ∈ TB q B, ∀ y ∈ TB q B, x + y ∈ TB q B := by
        rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
        exact (FB_add_iff B ℓ ℓ').2 (hc ℓ ℓ')
      refine ⟨{ carrier := TB q B
                add_mem' := fun {a b} ha hb => hadd a ha b hb
                zero_mem' := h0
                neg_mem' := fun {x} hx => ?_ }, rfl⟩
      have hcard := card_nsmul_eq_zero (G := Fin s → ZMod (q ^ 2)) (x := x)
      have hpos : 0 < Fintype.card (Fin s → ZMod (q ^ 2)) := Fintype.card_pos
      have : -x = (Fintype.card (Fin s → ZMod (q ^ 2)) - 1) • x := by
        have e : Fintype.card (Fin s → ZMod (q ^ 2)) = (Fintype.card (Fin s → ZMod (q ^ 2)) - 1) + 1 :=
          by omega
        rw [e, succ_nsmul] at hcard
        exact (neg_eq_of_add_eq_zero_left hcard)
      show -x ∈ TB q B
      rw [this]
      exact nsmul_mem_TB B hadd h0 x hx _
  refine ⟨hiff, fun hs hB hG => ?_⟩
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hc := hiff.1 hG
  set i0 : Fin s := ⟨0, hs⟩
  set h : ℕ := (q + 1) / 2 with hh
  have hhq : h < q := by omega
  set y : Fin s → ZMod q := Pi.single i0 (h : ZMod q)
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  set ℓ := B⁻¹ *ᵥ y
  have hBl : B *ᵥ ℓ = y := by
    simp only [ℓ, mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  have hcar := hc ℓ ℓ
  have hcv : (fun i => ((carryVec q (fun i => ((B *ᵥ ℓ) i).val) (fun i => ((B *ᵥ ℓ) i).val) i : ℕ) :
      ZMod q)) = Pi.single i0 1 := by
    funext i
    simp only [carryVec, hBl, y]
    by_cases hi : i = i0
    · subst hi
      simp only [Pi.single_eq_same, ZMod.val_natCast, Nat.mod_eq_of_lt hhq]
      rw [show (h + h) / q = 1 from Nat.div_eq_of_lt_le (by omega) (by omega)]
      simp
    · simp [Pi.single_eq_of_ne hi]
  rw [hcv] at hcar
  have : (Pi.single i0 (1 : ZMod q) : Fin s → ZMod q) = 0 := by
    rw [← one_mulVec (Pi.single i0 (1 : ZMod q)), ← Matrix.nonsing_inv_mul _ hdet,
      ← mulVec_mulVec, hcar, mulVec_zero]
  have h1 := congrFun this i0
  simp at h1

/-! ## `lem:phase` (i) -/

theorem phase_i' (p : ℕ) (hp : p.Prime) {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod p))
    (n : Fin s → ZMod p) (E : Fin s → ℤ) (c : Fin s) :
    (geoR p B (n + fun i => ((E i : ℤ) : ZMod p)) c : ℤ) =
      geoR p B n c + betaE p B E c - p * wrapK p B n E c ∧
    (betaE p B E c = 0 → wrapK p B n E c = 0) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : 0 < p := hp.pos
  have ha : geoR p B n c < p := ZMod.val_lt _
  have hb : betaE p B E c < p := ZMod.val_lt _
  have hsum : geoR p B (n + fun i => ((E i : ℤ) : ZMod p)) c =
      (geoR p B n c + betaE p B E c) % p := by
    simp only [geoR, betaE, mulVec_add, Pi.add_apply, ZMod.val_add]
  constructor
  · rw [hsum]
    unfold wrapK
    by_cases h : p ≤ geoR p B n c + betaE p B E c
    · rw [if_pos h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      push_cast [h]; ring
    · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]; push_cast; ring
  · intro h0
    unfold wrapK
    rw [if_neg]
    omega

theorem phase_i_free' (p : ℕ) (hp : p.Prime) {s : ℕ} (B : Matrix (Fin s) (Fin s) (ZMod p))
    (hB : IsUnit B) (E : Fin s → ℤ) (κ : Fin s → ℕ) (hκ : ∀ c, κ c ≤ 1)
    (hκβ : ∀ c, betaE p B E c = 0 → κ c = 0) :
    ∃ n : Fin s → ZMod p, ∀ c, wrapK p B n E c = κ c := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  set y : Fin s → ZMod p := fun c => if κ c = 1 then -1 else 0
  refine ⟨B⁻¹ *ᵥ y, fun c => ?_⟩
  have hBy : B *ᵥ (B⁻¹ *ᵥ y) = y := by
    simp only [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  unfold wrapK geoR
  rw [hBy]
  have hb : betaE p B E c < p := ZMod.val_lt _
  have hp1 : 1 < p := hp.one_lt
  have hv : ((-1 : ZMod p)).val = p - 1 := by
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  by_cases hk : κ c = 1
  · have hβ : betaE p B E c ≠ 0 := fun h => by have := hκβ c h; omega
    simp only [y, hk, if_true]
    rw [if_pos (by rw [hv]; omega)]
  · have hk0 : κ c = 0 := by have := hκ c; omega
    simp only [y, hk, if_false, ZMod.val_zero, zero_add]
    rw [if_neg (by omega), hk0]

end Z3NetF

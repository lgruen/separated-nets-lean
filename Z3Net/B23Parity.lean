/-
Proof module (V14 stage S16′): `rem:shiftparity` (why every-shift certificates vanish at some resolutions).
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23Check2
public import Z3Net.B23ParityDefs

@[expose] public section

/-!
# `rem:shiftparity`: parity, dichotomy and the consequences

* Digits: `dval_head` (the first digit), `dval_pad` (top and two jitter digits `0`: the factor `b²`).
* The `μ` lemma (`plain_of_muD_le_one`): if `μ_H(t) ≤ 1` (toroidal), some `X` has `|int(X ⊕ t) − int X| ≤ 1`
  (plain); the wrapped case `int(X ⊕ t) − int X = b^H − 1` (`t = (b−1,…,b−1)`) is moved to `X = (1, 0, …, 0)`.
  Hence `μ_{H+1}(0 ‖ t) ≤ 1` (`muD_cons_le`).
* (i) `parity_core`, `first_even_core`; (ii) `chain_embed` (the indices whose new digits are `0` embed `P_L` with top
  and jitter digits `0`), `dichotomy_int`, `dichotomy_core`; (iii) `seq_chain`, `bnd_small`, `tendsto_core`,
  `floor_iff_core`.
-/

namespace Z3NetB23.Proofs

namespace Parity

open Matrix Finset Z3NetB23

/-! ## Digits -/

section digits

variable {b : ℕ}

/-- The first digit of a digit vector. -/
lemma dval_head {n : ℕ} (y : Fin (n + 1) → ZMod b) :
    dval b y = (y 0).val * b ^ n + dval b (fun j : Fin n => y j.succ) := by
  unfold dval
  rw [Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun j _ => ?_)
  simp only [Fin.val_succ]
  congr 2
  omega

/-- A digit vector with top digit `0`, block `x` and two jitter digits `0` has the integer `b² int(x)`. -/
lemma dval_pad {ℓ : ℕ} (y : Fin (ℓ + 3) → ZMod b) (x : Fin ℓ → ZMod b) (h0 : y ⟨0, by omega⟩ = 0)
    (hk : ∀ (k : ℕ) (hk : k < ℓ), y ⟨k + 1, by omega⟩ = x ⟨k, hk⟩)
    (hj : ∀ (t : ℕ) (ht : t < 2), y ⟨ℓ + 1 + t, by omega⟩ = 0) :
    dval b y = b ^ 2 * dval b x := by
  rw [dval_succ y, dval_succ]
  have e1 : y (Fin.last (ℓ + 2)) = 0 := by
    have := hj 1 (by omega); convert this using 2; ext; simp
  have e2 : y (Fin.last (ℓ + 1)).castSucc = 0 := by
    have := hj 0 (by omega); convert this using 2; ext; simp
  rw [e1, e2, ZMod.val_zero, add_zero, add_zero, dval_head]
  have e3 : y (0 : Fin (ℓ + 1)).castSucc.castSucc = 0 := by
    convert h0 using 2; ext; simp
  rw [e3, ZMod.val_zero, zero_mul, zero_add]
  have e4 : (fun j : Fin ℓ => y j.succ.castSucc.castSucc) = x := by
    funext j
    have := hk j j.isLt
    convert this using 2; ext; simp
  rw [e4]
  ring

end digits

/-! ## The `μ` lemma -/

section mu

variable {b : ℕ} [Fact b.Prime]

-- for a prime `b`, this instance would give `Neg (ZMod b)` through `IsSimpleAddGroup`, not reducibly equal to the ring
-- negation (then `rw`/`ring` fail on `X + t + -t`)
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma bpos : 0 < b := (Fact.out : b.Prime).pos

/-- The wrapped case: if `int(X ⊕ t) − int X = b^H − 1`, then `t = (b−1, …, b−1)` and `Y = (1, 0, …, 0)` has
`int(Y ⊕ t) − int Y = −1`. -/
lemma plain_wrap {H : ℕ} (X t : Fin H → ZMod b) (hu : (dval b (X + t) : ℤ) - dval b X = (b : ℤ) ^ H - 1) :
    ∃ Y : Fin H → ZMod b, |(dval b (Y + t) : ℤ) - dval b Y| ≤ 1 := by
  have : NeZero b := ⟨bpos.ne'⟩
  have : Fact (1 < b) := ⟨(Fact.out : b.Prime).one_lt⟩
  have hb := (Fact.out : b.Prime).two_le
  cases H with
  | zero => exact ⟨X, by rw [hu]; simp⟩
  | succ n =>
    have h1 := dval_lt (X + t)
    have h2 := dval_lt X
    have hX0 : dval b X = 0 := by
      have : ((dval b (X + t) : ℕ) : ℤ) < (b : ℤ) ^ (n + 1) := by exact_mod_cast h1
      omega
    have hX : X = 0 := dval_eq_zero X hX0
    subst hX
    rw [zero_add] at hu
    rw [hX0, Nat.cast_zero, sub_zero] at hu
    -- the digits of `t`
    have ht := dval_head t
    set a := (t 0).val
    set r := dval b (fun j : Fin n => t j.succ)
    have ha : a < b := ZMod.val_lt _
    have hr : r < b ^ n := dval_lt _
    have hsum : a * b ^ n + r + 1 = b * b ^ n := by
      have h' : ((dval b t : ℕ) : ℤ) + 1 = (b : ℤ) ^ (n + 1) := by linarith
      rw [ht] at h'
      push_cast at h'
      rw [pow_succ] at h'
      have : ((a * b ^ n + r + 1 : ℕ) : ℤ) = ((b * b ^ n : ℕ) : ℤ) := by
        push_cast; linarith [mul_comm ((b : ℤ) ^ n) (b : ℤ)]
      exact_mod_cast this
    have hBn : 1 ≤ b ^ n := Nat.one_le_pow _ _ bpos
    have hab : a + 1 = b := by
      by_contra hne
      have h3 : (a + 2) * b ^ n ≤ b * b ^ n := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have hr' : r + 1 = b ^ n := by
      have : (a + 1) * b ^ n = b * b ^ n := by rw [hab]
      nlinarith
    -- `Y = (1, 0, …, 0)`
    refine ⟨fun j => if (j : ℕ) = 0 then 1 else 0, ?_⟩
    rw [dval_head, dval_head (fun j : Fin (n + 1) => if (j : ℕ) = 0 then (1 : ZMod b) else 0)]
    have e0 : (t 0 : ZMod b) = ((b - 1 : ℕ) : ZMod b) := by
      rw [← ZMod.natCast_zmod_val (t 0)]; congr 1; omega
    have e1 : (1 : ZMod b) + t 0 = 0 := by
      rw [e0, Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self]; ring
    simp only [Pi.add_apply, Fin.val_zero, ite_true, Fin.val_succ, Nat.add_one_ne_zero, ite_false, zero_add, e1,
      ZMod.val_zero, zero_mul, ZMod.val_one]
    have e2 : dval b (fun _ : Fin n => (0 : ZMod b)) = 0 := by simp [dval]
    rw [e2]
    change |((r : ℕ) : ℤ) - ((1 * b ^ n + 0 : ℕ) : ℤ)| ≤ 1
    have : ((r : ℕ) : ℤ) + 1 = ((b ^ n : ℕ) : ℤ) := by exact_mod_cast hr'
    push_cast
    rw [abs_le]; constructor <;> linarith

/-- **The `μ` lemma**: if `μ_H(t) ≤ 1`, there is `X` with `|int(X ⊕ t) − int X| ≤ 1` (the plain, non-toroidal
difference): the toroidal values `0, ±1` are plain except `±(b^H − 1)`, which are moved by `plain_wrap`. -/
lemma plain_of_muD_le_one {H : ℕ} (t : Fin H → ZMod b) (h : muD b t ≤ 1) :
    ∃ X : Fin H → ZMod b, |(dval b (X + t) : ℤ) - dval b X| ≤ 1 := by
  have : NeZero b := ⟨bpos.ne'⟩
  obtain ⟨X, -, hX⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin H → ZMod b))
    (fun X : Fin H → ZMod b => Z3NetF.cres (b ^ H) ((dval b (X + t) : ℤ) - dval b X))
  have hmu : Z3NetF.cres (b ^ H) ((dval b (X + t) : ℤ) - dval b X) ≤ 1 := by
    have e : muD b t = Z3NetF.cres (b ^ H) ((dval b (X + t) : ℤ) - dval b X) := hX
    omega
  set N := b ^ H with hN
  have hNp : 0 < N := pow_pos bpos H
  set u : ℤ := (dval b (X + t) : ℤ) - dval b X with hudef
  have h1 : ((dval b (X + t) : ℕ) : ℤ) < N := by exact_mod_cast dval_lt (X + t)
  have h2 : ((dval b X : ℕ) : ℤ) < N := by exact_mod_cast dval_lt X
  have hlo : -(N : ℤ) < u := by simp only [hudef]; omega
  have hhi : u < (N : ℤ) := by simp only [hudef]; omega
  have hs := Z3NetC.Proofs.cres_spec N hNp u
  have hm : min (u % (N : ℤ)) ((N : ℤ) - u % (N : ℤ)) ≤ 1 := by rw [← hs]; exact_mod_cast hmu
  by_cases habs : |u| ≤ 1
  · exact ⟨X, habs⟩
  rcases le_or_gt 0 u with hu0 | hu0
  · -- `u = N − 1`
    have hmod : u % (N : ℤ) = u := Int.emod_eq_of_lt hu0 hhi
    rw [hmod] at hm
    have hu1 : 2 ≤ u := by rw [abs_of_nonneg hu0] at habs; omega
    have hu : u = (b : ℤ) ^ H - 1 := by
      have : (N : ℤ) - u ≤ 1 := by
        rcases min_le_iff.1 hm with h' | h'
        · omega
        · exact h'
      have : ((N : ℕ) : ℤ) = (b : ℤ) ^ H := by rw [hN]; push_cast; rfl
      omega
    exact plain_wrap X t hu
  · -- `u = 1 − N`: the wrapped case for `(X ⊕ t, −t)`
    have hmod : u % (N : ℤ) = u + N := by
      rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod] at hm
    have hu1 : u ≤ -2 := by rw [abs_of_neg hu0] at habs; omega
    have hu : (dval b ((X + t) + -t) : ℤ) - dval b (X + t) = (b : ℤ) ^ H - 1 := by
      rw [add_neg_cancel_right X t]
      have : u + N ≤ 1 := by
        rcases min_le_iff.1 hm with h' | h'
        · exact h'
        · omega
      have : ((N : ℕ) : ℤ) = (b : ℤ) ^ H := by rw [hN]; push_cast; rfl
      simp only [hudef] at *
      omega
    obtain ⟨Y, hY⟩ := plain_wrap (X + t) (-t) hu
    refine ⟨Y + -t, ?_⟩
    rw [neg_add_cancel_right Y t, abs_sub_comm]
    exact hY

/-- **`μ_{H+1}(0 ‖ t)` is at most the plain value of `t`**: for `y = (0, t)` (top digit `0`) and every `X`,
`μ_{H+1}(y) ≤ |int(X ⊕ t) − int X|`; stated for a length `n = H + 1`. -/
lemma muD_cons_le {H n : ℕ} (hn : n = H + 1) (t : Fin H → ZMod b) (y : Fin n → ZMod b)
    (h0 : ∀ r : Fin n, (r : ℕ) = 0 → y r = 0) (hs : ∀ (r : Fin n) (j : Fin H), (r : ℕ) = j + 1 → y r = t j)
    (X : Fin H → ZMod b) : (muD b y : ℤ) ≤ |(dval b (X + t) : ℤ) - dval b X| := by
  have : NeZero b := ⟨bpos.ne'⟩
  subst hn
  have hle : muD b y ≤ Z3NetF.cres (b ^ (H + 1)) ((dval b (Fin.cons 0 X + y) : ℤ) - dval b (Fin.cons 0 X : Fin (H + 1) → ZMod b)) :=
    Finset.inf'_le _ (Finset.mem_univ _)
  have hc := Z3NetC.Proofs.cres_le (b ^ (H + 1)) (pow_pos bpos _)
    ((dval b (Fin.cons 0 X + y) : ℤ) - dval b (Fin.cons 0 X : Fin (H + 1) → ZMod b)) 0
  rw [mul_zero, add_zero] at hc
  have e1 : dval b (Fin.cons 0 X + y) = dval b (X + t) := by
    rw [dval_head]
    have a0 : (Fin.cons 0 X + y : Fin (H + 1) → ZMod b) 0 = 0 := by
      simp only [Pi.add_apply, Fin.cons_zero, h0 0 rfl, add_zero]
    have a1 : (fun j : Fin H => (Fin.cons 0 X + y : Fin (H + 1) → ZMod b) j.succ) = X + t := by
      funext j
      simp only [Pi.add_apply, Fin.cons_succ, hs j.succ j (by simp)]
    rw [a0, a1, ZMod.val_zero, zero_mul, zero_add]
  have e2 : dval b (Fin.cons 0 X : Fin (H + 1) → ZMod b) = dval b X := by
    rw [dval_head]; simp
  rw [e1, e2] at hc hle
  calc (muD b y : ℤ) ≤ _ := by exact_mod_cast hle
    _ ≤ _ := hc

end mu

/-! ## (i) Parity -/

section parity

variable {b : ℕ} [Fact b.Prime]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- The zero extension of an index: the new index entries are `0`. -/
def zext {L m : ℕ} (d : Fin L → ZMod b) : Fin m → ZMod b := fun i => if h : (i : ℕ) < L then d ⟨i, h⟩ else 0

lemma zext_self {L : ℕ} (d : Fin L → ZMod b) : (zext d : Fin L → ZMod b) = d := by
  funext i; simp [zext]

lemma zext_zero {L m : ℕ} : (zext (0 : Fin L → ZMod b) : Fin m → ZMod b) = 0 := by
  funext i; simp [zext]

lemma zext_out {L m : ℕ} (d : Fin L → ZMod b) (i : Fin m) (hi : L ≤ (i : ℕ)) : zext d i = 0 := by
  simp only [zext]; rw [dif_neg (by omega)]

lemma zext_ne {L m : ℕ} (hLm : L ≤ m) (d : Fin L → ZMod b) (hd : d ≠ 0) : (zext d : Fin m → ZMod b) ≠ 0 := by
  intro h
  apply hd
  funext i
  have := congrFun h ⟨i, by omega⟩
  simpa [zext] using this

lemma nOf_zext {L ℓ : ℕ} (d : Fin L → ZMod b) : nOf (zext d : Fin (ℓ + 3) → ZMod b) = zext d := by
  funext i; simp [nOf, zext]

/-- If `v°_L = 0` (`L ≥ 1`), some nonzero index difference `d` has `μ_H(top_H(C_c d)) ≤ 1` for every `c`. -/
lemma vcirc_zero_pair {L : ℕ} (hL : 1 ≤ L) (C : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) (h0 : vcirc b L C = 0) :
    ∃ d : Fin L → ZMod b, d ≠ 0 ∧ ∀ c, muD b (topD (L / 2) (Nat.div_le_self L 2) (C c *ᵥ d)) ≤ 1 := by
  have hne : Nonempty {p : (Fin L → ZMod b) × (Fin L → ZMod b) // p.1 ≠ p.2} :=
    ⟨⟨(0, Pi.single ⟨0, hL⟩ 1), fun h => by have := congrFun h ⟨0, hL⟩; simp at this⟩⟩
  obtain ⟨p, hp⟩ := ciInf_mem (fun p : {p : (Fin L → ZMod b) × (Fin L → ZMod b) // p.1 ≠ p.2} =>
      ∑ c : Fin 3, hW (muD b (topD (L / 2) (Nat.div_le_self L 2) (C c *ᵥ (p.1.2 - p.1.1)))))
  have hp' : ∑ c : Fin 3, hW (muD b (topD (L / 2) (Nat.div_le_self L 2) (C c *ᵥ (p.1.2 - p.1.1)))) = 0 :=
    hp.trans h0
  refine ⟨p.1.2 - p.1.1, sub_ne_zero.2 (Ne.symm p.2), fun c => ?_⟩
  have h1 := (Finset.sum_eq_zero_iff.1 hp') c (Finset.mem_univ _)
  unfold hW at h1
  have h2 := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h1
  omega

/-- **`rem:shiftparity`(i), parity**: if `L ≥ 1` is even and `v°_L = 0`, then `v°_{L+3} = 0` for every lift of `P_L`
(any `s_A, s_B`). -/
theorem parity_core {L : ℕ} (hL : 1 ≤ L) (hev : Even L) (C : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b))
    (h0 : vcirc b L C = 0) (sA sB : Fin 3 → Fin L → ZMod b) : vcirc b (L + 3) (liftGen C sA sB) = 0 := by
  obtain ⟨d, hd, hmu⟩ := vcirc_zero_pair hL C h0
  have hH : (L + 3) / 2 = L / 2 + 1 := by obtain ⟨k, rfl⟩ := hev; omega
  apply Nat.le_zero.1
  refine (ciInf_le (OrderBot.bddBelow _) ⟨((0 : Fin (L + 3) → ZMod b), zext d),
    (zext_ne (by omega) d hd).symm⟩).trans (le_of_eq (Finset.sum_eq_zero fun c _ => ?_))
  simp only [sub_zero]
  obtain ⟨X, hX⟩ := plain_of_muD_le_one _ (hmu c)
  have h1 := muD_cons_le hH (topD (L / 2) (Nat.div_le_self L 2) (C c *ᵥ d))
    (topD ((L + 3) / 2) (Nat.div_le_self _ 2) (liftGen C sA sB c *ᵥ zext d)) ?_ ?_ X
  · have : muD b (topD ((L + 3) / 2) (Nat.div_le_self _ 2) (liftGen C sA sB c *ᵥ zext d)) ≤ 1 := by
      have := h1.trans hX; exact_mod_cast this
    unfold hW; rw [Nat.sub_eq_zero_of_le this]; rfl
  · intro r hr
    simp only [topD]
    have e : (Fin.castLE (Nat.div_le_self _ 2) r : Fin (L + 3)) = ⟨0, by omega⟩ := Fin.ext (by simp [hr])
    rw [e, liftGen_mulVec_top, zext_out d _ (by simp), zext_out d _ (by simp), zext_out d _ (by simp)]
    simp
  · intro r j hr
    simp only [topD]
    have e : (Fin.castLE (Nat.div_le_self _ 2) r : Fin (L + 3)) = ⟨(j : ℕ) + 1, by omega⟩ :=
      Fin.ext (by simp [hr])
    rw [e, liftGen_mulVec_block C sA sB _ c j (by omega), nOf_zext, zext_self, zext_out d _ (by simp),
      zext_out d _ (by simp)]
    simp only [mul_zero, add_zero]
    rfl

/-- **`rem:shiftparity`(i), contrapositive**: if `v°_L = 0` (`L ≥ 1`) and `v°_{L+3} > 0` for a lift of `P_L`, then
`L + 3` is even: a certificate can first become positive only at an even resolution. -/
theorem first_even_core {L : ℕ} (hL : 1 ≤ L) (C : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) (h0 : vcirc b L C = 0)
    (sA sB : Fin 3 → Fin L → ZMod b) (hpos : 0 < vcirc b (L + 3) (liftGen C sA sB)) : Even (L + 3) := by
  rcases Nat.even_or_odd L with he | ho
  · rw [parity_core hL he C h0 sA sB] at hpos; exact absurd hpos (lt_irrefl 0)
  · obtain ⟨k, rfl⟩ := ho; exact ⟨k + 2, by omega⟩

end parity

/-! ## (ii) Dichotomy -/

section dich

variable {b : ℕ} [Fact b.Prime]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- **The embedding of `P_L`** (proof of `rem:shiftparity`(ii)): along every chain of lifts from `P_L` (any depth
parameters and shifts) to level `m = L + 3j`, for every shift `τ₀` of `P_L` there is a shift `τ` of `P_m` such that
the index `zext d` (new index entries `0`) has the coordinates `b^(2j) · int(C₀_c d + τ₀_c)`: top and jitter digits
`0`, block digits those of `P_L ⊕ τ₀`. -/
theorem chain_embed {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)} {σ₀ : Fin 3 → Fin L → ZMod b}
    {D : ℕ → ℕ} {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b L C₀ σ₀ D m C σ) :
    ∃ j, m = L + 3 * j ∧ ∀ τ₀ : Fin 3 → Fin L → ZMod b, ∃ τ : Fin 3 → Fin m → ZMod b,
      ∀ (d : Fin L → ZMod b) (c : Fin 3),
        dval b (C c *ᵥ zext d + τ c) = b ^ (2 * j) * dval b (C₀ c *ᵥ d + τ₀ c) := by
  induction h with
  | refl => exact ⟨0, by omega, fun τ₀ => ⟨τ₀, fun d c => by rw [zext_self]; simp⟩⟩
  | @step ℓ C σ sA sB hch hA hB ih =>
    obtain ⟨j, hm, hτ⟩ := ih
    have hLl : L ≤ ℓ := by omega
    refine ⟨j + 1, by omega, fun τ₀ => ?_⟩
    obtain ⟨τ, hτ'⟩ := hτ τ₀
    refine ⟨liftShift τ, fun d c => ?_⟩
    rw [dval_pad _ (C c *ᵥ zext d + τ c), hτ' d c]
    · ring
    · simp only [Pi.add_apply]
      rw [liftGen_mulVec_top, zext_out d _ (by simp; omega), zext_out d _ (by simp; omega),
        zext_out d _ (by simp; omega)]
      simp only [liftShift]
      rw [dif_neg (by simp)]
      simp
    · intro k hk
      simp only [Pi.add_apply]
      rw [liftGen_mulVec_block C sA sB _ c k hk, nOf_zext, zext_out d _ (by simp; omega),
        zext_out d _ (by simp; omega)]
      simp only [liftShift, mul_zero, add_zero]
      rw [dif_pos (by simp; omega)]
      rfl
    · intro t ht
      simp only [Pi.add_apply]
      rw [liftGen_mulVec_jit C sA sB _ c t ht, zext_out d _ (by simp; omega), zext_out d _ (by simp; omega),
        zext_out d _ (by simp; omega)]
      simp only [liftShift, mul_zero, add_zero]
      rw [dif_neg (by simp; omega)]
      exact add_zero 0

/-- **`rem:shiftparity`(ii), integer form**: if `v°_L = 0` (`L ≥ 1`), then along every chain of lifts from `P_L` to
level `m = L + 3j` there are a digital shift `τ` and two distinct indices whose coordinates differ (as integers at
scale `b^m`, not toroidally) by at most `b^(2j) (2W − 1)` in every coordinate, `W = b^(L − ⌊L/2⌋)`. -/
theorem dichotomy_int {L : ℕ} (hL : 1 ≤ L) {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)}
    {σ₀ : Fin 3 → Fin L → ZMod b} {D : ℕ → ℕ} {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    {σ : Fin 3 → Fin m → ZMod b} (h0 : vcirc b L C₀ = 0) (h : LiftChain b L C₀ σ₀ D m C σ) :
    ∃ j, m = L + 3 * j ∧ ∃ τ : Fin 3 → Fin m → ZMod b, ∃ v w : Fin m → ZMod b, v ≠ w ∧
      ∀ c, |(Z3NetF.digPointShift b m C τ v c : ℤ) - Z3NetF.digPointShift b m C τ w c| ≤
        (b : ℤ) ^ (2 * j) * (2 * (b : ℤ) ^ (L - L / 2) - 1) := by
  have : NeZero b := ⟨bpos.ne'⟩
  obtain ⟨d, hd, hmu⟩ := vcirc_zero_pair hL C₀ h0
  choose X hX using fun c => plain_of_muD_le_one _ (hmu c)
  obtain ⟨j, hm, hτ⟩ := chain_embed h
  let τ₀ : Fin 3 → Fin L → ZMod b := fun c i => if hi : (i : ℕ) < L / 2 then X c ⟨i, hi⟩ else 0
  obtain ⟨τ, hτ'⟩ := hτ τ₀
  refine ⟨j, hm, τ, zext (0 : Fin L → ZMod b), zext d, ?_, fun c => ?_⟩
  · rw [zext_zero]; exact (zext_ne (by omega) d hd).symm
  change |((dval b (C c *ᵥ zext (0 : Fin L → ZMod b) + τ c) : ℕ) : ℤ) - ((dval b (C c *ᵥ zext d + τ c) : ℕ) : ℤ)| ≤ _
  rw [hτ' 0 c, hτ' d c, mulVec_zero, zero_add]
  set W := b ^ (L - L / 2) with hWdef
  have hWp : 0 < W := pow_pos bpos _
  have hdec : ∀ z : Fin L → ZMod b, dval b z = W * dval b (topD (L / 2) (Nat.div_le_self L 2) z) + dval b z % W := by
    intro z; rw [dval_topD]; exact (Nat.div_add_mod _ _).symm
  have e0 : topD (L / 2) (Nat.div_le_self L 2) (τ₀ c) = X c := by
    funext r; simp only [topD, τ₀, Fin.val_castLE]; rw [dif_pos r.isLt]
  have e1 : topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ d + τ₀ c) =
      X c + topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ d) := by
    funext r; simp only [topD, Pi.add_apply, τ₀, Fin.val_castLE]; rw [dif_pos r.isLt]; ring
  have hr0 := Nat.mod_lt (dval b (τ₀ c)) hWp
  have hr1 := Nat.mod_lt (dval b (C₀ c *ᵥ d + τ₀ c)) hWp
  have hXc := hX c
  rw [hdec (τ₀ c), hdec (C₀ c *ᵥ d + τ₀ c), e0, e1]
  set x0 := dval b (X c)
  set x1 := dval b (X c + topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ d))
  set r0 := dval b (τ₀ c) % W
  set r1 := dval b (C₀ c *ᵥ d + τ₀ c) % W
  have hB : (0 : ℤ) ≤ (b : ℤ) ^ (2 * j) := by positivity
  have hk : |(W : ℤ) * ((x0 : ℤ) - x1) + ((r0 : ℤ) - r1)| ≤ 2 * (W : ℤ) - 1 := by
    rw [abs_le] at hXc ⊢
    have a1 : (W : ℤ) * ((x0 : ℤ) - x1) ≤ W := by nlinarith
    have a2 : -(W : ℤ) ≤ (W : ℤ) * ((x0 : ℤ) - x1) := by nlinarith
    have a3 : ((r0 : ℕ) : ℤ) < W := by exact_mod_cast hr0
    have a4 : ((r1 : ℕ) : ℤ) < W := by exact_mod_cast hr1
    constructor <;> omega
  have e : ((b ^ (2 * j) * (W * x0 + r0) : ℕ) : ℤ) - ((b ^ (2 * j) * (W * x1 + r1) : ℕ) : ℤ) =
      (b : ℤ) ^ (2 * j) * ((W : ℤ) * ((x0 : ℤ) - x1) + ((r0 : ℤ) - r1)) := by push_cast; ring
  rw [e, abs_mul, abs_of_nonneg hB]
  have hW' : (W : ℤ) = (b : ℤ) ^ (L - L / 2) := by rw [hWdef]; push_cast; rfl
  rw [← hW']
  exact mul_le_mul_of_nonneg_left hk hB

lemma rpow_combo (B : ℝ) (hB : 0 < B) (L j : ℕ) :
    (B ^ L) ^ (-(2 / 3 : ℝ)) * (B ^ (L + 3 * j)) ^ (-(1 / 3 : ℝ)) = B ^ (2 * j) / B ^ (L + 3 * j) := by
  have hBL : 0 < B ^ L := pow_pos hB L
  set u : ℝ := (B ^ L) ^ (-(1 / 3 : ℝ)) with hudef
  have hu3 : u ^ 3 = (B ^ L)⁻¹ := by
    rw [hudef, ← Real.rpow_mul_natCast hBL.le, show (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 by norm_num,
      Real.rpow_neg_one]
  have h23 : (B ^ L) ^ (-(2 / 3 : ℝ)) = u ^ 2 := by
    rw [hudef, ← Real.rpow_mul_natCast hBL.le, show (-(1 / 3 : ℝ)) * ((2 : ℕ) : ℝ) = -(2 / 3) by norm_num]
  have hm : (B ^ (L + 3 * j)) ^ (-(1 / 3 : ℝ)) = u * (B ^ j)⁻¹ := by
    rw [pow_add, show B ^ (3 * j) = (B ^ j) ^ 3 by ring, Real.mul_rpow hBL.le (by positivity), ← hudef,
      ← Real.rpow_natCast_mul (by positivity), show ((3 : ℕ) : ℝ) * (-(1 / 3 : ℝ)) = -1 by norm_num,
      Real.rpow_neg_one]
  rw [h23, hm, show u ^ 2 * (u * (B ^ j)⁻¹) = u ^ 3 * (B ^ j)⁻¹ by ring, hu3, pow_add,
    show B ^ (3 * j) = B ^ (2 * j) * B ^ j by rw [← pow_add]; ring_nf]
  have : 0 < B ^ j := pow_pos hB j
  have : 0 < B ^ (2 * j) := pow_pos hB _
  field_simp

/-- **`rem:shiftparity`(ii)**: if `v°_L = 0` (`L ≥ 1`), then along every chain of lifts from `P_L` (any depth
parameters, any shifts), at every level `m` there are a digital shift `τ` and two distinct indices whose toroidal
distance is at most their Euclidean distance, which is `< 2√3 b^(⌈L/2⌉ − 2L/3) N^{−1/3}`, `N = b^m`. -/
theorem dichotomy_core {L : ℕ} (hL : 1 ≤ L) {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)}
    {σ₀ : Fin 3 → Fin L → ZMod b} {D : ℕ → ℕ} {m : ℕ} {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    {σ : Fin 3 → Fin m → ZMod b} (h0 : vcirc b L C₀ = 0) (h : LiftChain b L C₀ σ₀ D m C σ) :
    ∃ τ : Fin 3 → Fin m → ZMod b, ∃ v w : Fin m → ZMod b, v ≠ w ∧
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) ≤
        Real.sqrt (∑ c, (((Z3NetF.digPointShift b m C τ v c : ℝ) - Z3NetF.digPointShift b m C τ w c) /
          (b : ℝ) ^ m) ^ 2) ∧
      Real.sqrt (∑ c, (((Z3NetF.digPointShift b m C τ v c : ℝ) - Z3NetF.digPointShift b m C τ w c) /
          (b : ℝ) ^ m) ^ 2) <
        2 * Real.sqrt 3 * (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ)) * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨j, hm, τ, v, w, hvw, hbd⟩ := dichotomy_int hL h0 h
  refine ⟨τ, v, w, hvw, ?_, ?_⟩
  · apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun c _ => ?_
    have hpos : (0 : ℝ) < (b : ℝ) ^ m := pow_pos (by exact_mod_cast bpos) m
    rw [div_pow, div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 := Z3NetC.Proofs.cres_le (b ^ m) (pow_pos bpos m)
      ((Z3NetF.digPointShift b m C τ v c : ℤ) - Z3NetF.digPointShift b m C τ w c) 0
    rw [mul_zero, add_zero] at h1
    have h2 : ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℕ) : ℝ) ≤
        |(Z3NetF.digPointShift b m C τ v c : ℝ) - Z3NetF.digPointShift b m C τ w c| := by
      have := (Int.cast_le (R := ℝ)).2 h1
      push_cast at this
      exact this
    calc ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℕ) : ℝ) ^ 2 ≤
        |(Z3NetF.digPointShift b m C τ v c : ℝ) - Z3NetF.digPointShift b m C τ w c| ^ 2 :=
          pow_le_pow_left₀ (by positivity) h2 2
      _ = _ := sq_abs _
  · subst hm
    set B : ℝ := (b : ℝ) with hBdef
    have hB0 : 0 < B := by rw [hBdef]; exact_mod_cast bpos
    set Wr : ℝ := B ^ (L - L / 2) with hWr
    have hW1 : 1 ≤ Wr := one_le_pow₀ (by rw [hBdef]; exact_mod_cast bpos)
    set K : ℝ := B ^ (2 * j) * (2 * Wr - 1) with hK
    have hK0 : 0 ≤ K := by have : 0 < B ^ (2 * j) := pow_pos hB0 _; rw [hK]; nlinarith
    have hBm : 0 < B ^ (L + 3 * j) := pow_pos hB0 _
    have hc : ∀ c, |(Z3NetF.digPointShift b (L + 3 * j) C τ v c : ℝ) -
        Z3NetF.digPointShift b (L + 3 * j) C τ w c| ≤ K := by
      intro c
      have := (Int.cast_le (R := ℝ)).2 (hbd c)
      push_cast at this
      rw [hK, hWr, hBdef]; exact this
    have hsum : ∑ c, (((Z3NetF.digPointShift b (L + 3 * j) C τ v c : ℝ) -
        Z3NetF.digPointShift b (L + 3 * j) C τ w c) / B ^ (L + 3 * j)) ^ 2 ≤ 3 * (K / B ^ (L + 3 * j)) ^ 2 := by
      have : ∀ c ∈ (Finset.univ : Finset (Fin 3)), (((Z3NetF.digPointShift b (L + 3 * j) C τ v c : ℝ) -
          Z3NetF.digPointShift b (L + 3 * j) C τ w c) / B ^ (L + 3 * j)) ^ 2 ≤ (K / B ^ (L + 3 * j)) ^ 2 := by
        intro c _
        rw [div_pow, div_pow]
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hc c) 2
      calc _ ≤ ∑ _c : Fin 3, (K / B ^ (L + 3 * j)) ^ 2 := Finset.sum_le_sum this
        _ = _ := by simp
    have hs1 : Real.sqrt (3 * (K / B ^ (L + 3 * j)) ^ 2) = Real.sqrt 3 * (K / B ^ (L + 3 * j)) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    calc Real.sqrt _ ≤ Real.sqrt 3 * (K / B ^ (L + 3 * j)) := (Real.sqrt_le_sqrt hsum).trans (le_of_eq hs1)
      _ < 2 * Real.sqrt 3 * Wr * (B ^ (2 * j) / B ^ (L + 3 * j)) := by
          rw [hK]
          have h3 : 0 < Real.sqrt 3 := by positivity
          have h4 : 0 < B ^ (2 * j) / B ^ (L + 3 * j) := by positivity
          have : Real.sqrt 3 * (B ^ (2 * j) * (2 * Wr - 1) / B ^ (L + 3 * j)) =
              Real.sqrt 3 * (2 * Wr - 1) * (B ^ (2 * j) / B ^ (L + 3 * j)) := by ring
          rw [this]
          apply mul_lt_mul_of_pos_right _ h4
          nlinarith
      _ = _ := by rw [mul_assoc (2 * Real.sqrt 3 * Wr), ← rpow_combo B hB0 L j]

end dich

/-! ## (iii) Consequences -/

section conseq

variable {b : ℕ} [Fact b.Prime]

omit [Fact b.Prime] in
/-- An infinite chain of lifts gives a finite chain from each of its levels `L` to each later level. -/
lemma seq_chain {m₀ : ℕ} {D : ℕ → ℕ} {G : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    {S : (m : ℕ) → Fin 3 → Fin m → ZMod b} (hseq : IsLiftSeq b m₀ D G S) {L : ℕ} (hL : m₀ ≤ L)
    (hLc : L % 3 = m₀ % 3) : ∀ i, LiftChain b L (G L) (S L) D (L + 3 * i) (G (L + 3 * i)) (S (L + 3 * i)) := by
  intro i
  induction i with
  | zero => exact LiftChain.refl
  | succ i ih =>
    obtain ⟨sA, sB, hA, hB, hG, hS⟩ := hseq (L + 3 * i) (by omega) (by omega)
    have := LiftChain.step sA sB ih hA hB
    rw [← hG, ← hS] at this
    rw [show L + 3 * (i + 1) = L + 3 * i + 3 by ring]
    exact this

/-- `2√3 b^(⌈L/2⌉) b^(−2L/3) → 0`. -/
lemma bnd_small (ε : ℝ) (hε : 0 < ε) : ∃ L₁ : ℕ, ∀ L, L₁ ≤ L →
    2 * Real.sqrt 3 * (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ)) < ε := by
  have hB : (1 : ℝ) < b := by exact_mod_cast (Fact.out : b.Prime).one_lt
  have hB0 : (0 : ℝ) < b := by linarith
  have hr0 : 0 < (b : ℝ) ^ (-(1 / 6 : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hr1 : (b : ℝ) ^ (-(1 / 6 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hB (by norm_num)
  have hK : 0 < 2 * Real.sqrt 3 * (b : ℝ) ^ (1 / 2 : ℝ) := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hK) hr1
  refine ⟨n, fun L hL => ?_⟩
  have e1 : (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ)) =
      (b : ℝ) ^ (((L - L / 2 : ℕ) : ℝ) + (L : ℝ) * (-(2 / 3 : ℝ))) := by
    rw [Real.rpow_add hB0, Real.rpow_mul hB0.le, Real.rpow_natCast, Real.rpow_natCast]
  have e2 : (b : ℝ) ^ (1 / 2 : ℝ) * ((b : ℝ) ^ (-(1 / 6 : ℝ))) ^ L =
      (b : ℝ) ^ ((1 / 2 : ℝ) + (-(1 / 6 : ℝ)) * (L : ℝ)) := by
    rw [Real.rpow_add hB0, Real.rpow_mul hB0.le, Real.rpow_natCast]
  have key : (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ)) ≤
      (b : ℝ) ^ (1 / 2 : ℝ) * ((b : ℝ) ^ (-(1 / 6 : ℝ))) ^ L := by
    rw [e1, e2]
    apply Real.rpow_le_rpow_of_exponent_le hB.le
    have : 2 * (L - L / 2) ≤ L + 1 := by omega
    have h' : (2 : ℝ) * ((L - L / 2 : ℕ) : ℝ) ≤ L + 1 := by exact_mod_cast this
    linarith
  have hrL : ((b : ℝ) ^ (-(1 / 6 : ℝ))) ^ L ≤ ((b : ℝ) ^ (-(1 / 6 : ℝ))) ^ n :=
    pow_le_pow_of_le_one hr0.le hr1.le hL
  have h5 : 2 * Real.sqrt 3 * (b : ℝ) ^ (1 / 2 : ℝ) * ((b : ℝ) ^ (-(1 / 6 : ℝ))) ^ n < ε := by
    have := mul_lt_mul_of_pos_left hn hK
    rwa [mul_div_cancel₀ _ hK.ne'] at this
  have h6 : (0 : ℝ) < 2 * Real.sqrt 3 := by positivity
  calc 2 * Real.sqrt 3 * (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ))
      = 2 * Real.sqrt 3 * ((b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ))) := by ring
    _ ≤ 2 * Real.sqrt 3 * ((b : ℝ) ^ (1 / 2 : ℝ) * ((b : ℝ) ^ (-(1 / 6 : ℝ))) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ h6.le
        exact key.trans (mul_le_mul_of_nonneg_left hrL (by positivity))
    _ < ε := by rw [← mul_assoc]; exact h5

/-- **`rem:shiftparity`(iii), the second consequence**: if along an infinite chain of lifts from `m₀ ≥ 1` the
certificate `v°_L` vanishes at arbitrarily large levels `L`, then the every-shift separation tends to `0`: for every
`ε > 0`, from some level on every level `m` has a digital shift and two distinct indices at toroidal (and Euclidean)
distance `< ε N^{−1/3}`. -/
theorem tendsto_core {m₀ : ℕ} (hm₀ : 1 ≤ m₀) {D : ℕ → ℕ} {G : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)}
    {S : (m : ℕ) → Fin 3 → Fin m → ZMod b} (hseq : IsLiftSeq b m₀ D G S)
    (hinf : ∀ M, ∃ L, M ≤ L ∧ m₀ ≤ L ∧ L % 3 = m₀ % 3 ∧ vcirc b L (G L) = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ M, ∀ m, M ≤ m → m₀ ≤ m → m % 3 = m₀ % 3 → ∃ τ : Fin 3 → Fin m → ZMod b, ∃ v w : Fin m → ZMod b, v ≠ w ∧
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m (G m) τ v c : ℤ) -
        Z3NetF.digPointShift b m (G m) τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) ≤
        Real.sqrt (∑ c, (((Z3NetF.digPointShift b m (G m) τ v c : ℝ) - Z3NetF.digPointShift b m (G m) τ w c) /
          (b : ℝ) ^ m) ^ 2) ∧
      Real.sqrt (∑ c, (((Z3NetF.digPointShift b m (G m) τ v c : ℝ) - Z3NetF.digPointShift b m (G m) τ w c) /
          (b : ℝ) ^ m) ^ 2) < ε * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨L₁, hL₁⟩ := bnd_small (b := b) ε hε
  obtain ⟨L, hLL, hL0, hLc, hz⟩ := hinf L₁
  refine ⟨L, fun m hm hm0 hmc => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = L + 3 * i := ⟨(m - L) / 3, by omega⟩
  obtain ⟨τ, v, w, hvw, h1, h2⟩ := dichotomy_core (by omega) hz (seq_chain hseq hL0 hLc i)
  refine ⟨τ, v, w, hvw, h1, h2.trans_le ?_⟩
  exact mul_le_mul_of_nonneg_right (hL₁ L hLL).le (by positivity)

lemma muD_len_zero {n : ℕ} (hn : n = 0) (x : Fin n → ZMod b) : muD b x = 0 := by
  subst hn
  apply Nat.le_zero.1
  refine (Finset.inf'_le _ (Finset.mem_univ (0 : Fin 0 → ZMod b))).trans (le_of_eq ?_)
  simp [Z3NetF.cres]

/-- **`rem:shiftparity`(iii), the first consequence**: for an infinite chain of lifts from `m₀ ≥ 1`, frozen from every
resolution, a floor for every shift exists (some `κ > 0` with `δ(P_m ⊕ τ) N^{1/3} ≥ κ` for every digital shift `τ`
and every level `m` of the chain from some level on) if and only if `v°_L > 0` at some level `L` of the chain. -/
theorem floor_iff_core {m₀ : ℕ} (hm₀ : 1 ≤ m₀) {D : ℕ → ℕ}
    {G : (m : ℕ) → Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {S : (m : ℕ) → Fin 3 → Fin m → ZMod b}
    (hseq : IsLiftSeq b m₀ D G S) (hfz : FrozenFromEvery m₀ D) :
    (∃ κ : ℝ, 0 < κ ∧ ∃ M, ∀ m, M ≤ m → m₀ ≤ m → m % 3 = m₀ % 3 → ∀ (τ : Fin 3 → Fin m → ZMod b)
      (v w : Fin m → ZMod b), v ≠ w →
        κ * ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤ Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m)
          ((Z3NetF.digPointShift b m (G m) τ v c : ℤ) - Z3NetF.digPointShift b m (G m) τ w c) : ℝ) /
            (b : ℝ) ^ m) ^ 2)) ↔
      ∃ L, m₀ ≤ L ∧ L % 3 = m₀ % 3 ∧ 0 < vcirc b L (G L) := by
  constructor
  · rintro ⟨κ, hκ, M, hfl⟩
    by_contra hne
    simp only [not_exists, not_and, not_lt] at hne
    have hinf : ∀ M', ∃ L, M' ≤ L ∧ m₀ ≤ L ∧ L % 3 = m₀ % 3 ∧ vcirc b L (G L) = 0 := fun M' =>
      ⟨m₀ + 3 * M', by omega, by omega, by omega, Nat.le_zero.1 (hne _ (by omega) (by omega))⟩
    obtain ⟨M', hM'⟩ := tendsto_core hm₀ hseq hinf κ hκ
    obtain ⟨τ, v, w, hvw, h1, h2⟩ := hM' (m₀ + 3 * (M + M')) (by omega) (by omega) (by omega)
    have := hfl (m₀ + 3 * (M + M')) (by omega) (by omega) (by omega) τ v w hvw
    linarith
  · rintro ⟨L, hL0, hLc, hpos⟩
    have hb := (Fact.out : b.Prime).one_lt
    have hL2 : 1 ≤ L / 2 := by
      by_contra hlt
      have hL1 : 1 ≤ L := by omega
      have : Nonempty {p : (Fin L → ZMod b) × (Fin L → ZMod b) // p.1 ≠ p.2} :=
        ⟨⟨(0, Pi.single ⟨0, hL1⟩ 1), fun h => by have := congrFun h ⟨0, hL1⟩; simp at this⟩⟩
      have : vcirc b L (G L) = 0 := by
        apply Nat.le_zero.1
        refine (ciInf_le (OrderBot.bddBelow _) (Classical.arbitrary _)).trans (le_of_eq ?_)
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [muD_len_zero (by omega)]; rfl
      omega
    set B : ℝ := (b : ℝ) with hBdef
    have hB : 1 < B := by rw [hBdef]; exact_mod_cast hb
    have hB0 : 0 < B := by linarith
    have hBL : 0 < B ^ L := pow_pos hB0 L
    set u : ℝ := (B ^ L) ^ (-(1 / 3 : ℝ)) with hudef
    have hu : 0 < u := Real.rpow_pos_of_pos hBL _
    have hu3 : u ^ 3 = (B ^ L)⁻¹ := by
      rw [hudef, ← Real.rpow_mul_natCast hBL.le, show (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 by norm_num,
        Real.rpow_neg_one]
    have h13 : (B ^ L) ^ (1 / 3 : ℝ) = u⁻¹ := by rw [hudef, Real.rpow_neg hBL.le, inv_inv]
    have h23 : (B ^ L) ^ (-(2 / 3 : ℝ)) = u ^ 2 := by
      rw [hudef, ← Real.rpow_mul_natCast hBL.le, show (-(1 / 3 : ℝ)) * ((2 : ℕ) : ℝ) = -(2 / 3) by norm_num]
    have hWL : B ^ (L - L / 2) < B ^ L := pow_lt_pow_right₀ hB (by omega)
    have hWu : B ^ (L - L / 2) * u ^ 3 < 1 := by
      rw [hu3, ← div_eq_mul_inv]; exact (div_lt_one hBL).2 hWL
    have hκ2 : 0 < (B ^ L) ^ (1 / 3 : ℝ) - B ^ (L - L / 2) * (B ^ L) ^ (-(2 / 3 : ℝ)) := by
      rw [h13, h23]
      have e : u⁻¹ - B ^ (L - L / 2) * u ^ 2 = (1 - B ^ (L - L / 2) * u ^ 3) * u⁻¹ := by
        field_simp
      rw [e]; exact mul_pos (by linarith) (inv_pos.2 hu)
    have hκ1 : 0 < gL b L (vcirc b L (G L)) := by
      unfold gL
      have : (0 : ℝ) < Real.sqrt (vcirc b L (G L)) := Real.sqrt_pos.2 (by exact_mod_cast hpos)
      positivity
    refine ⟨_, lt_min hκ1 hκ2, L, fun m hm hm0 hmc τ v w hvw => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, m = L + 3 * i := ⟨(m - L) / 3, by omega⟩
    exact shiftcert_a (fun ℓ hℓ => hfz L ℓ hL0 hLc hℓ) (seq_chain hseq hL0 hLc i) τ v w hvw

end conseq

end Parity

end Z3NetB23.Proofs

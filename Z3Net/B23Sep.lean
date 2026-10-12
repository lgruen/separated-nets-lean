/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23Lift
public import Z3Net.ColBasic

@[expose] public section

/-!
# V14 stage S14′: `lem:liftsep` (freezing and separation) and `lem:shiftcert`

* Digits: `dval` is `Z3Net.Proofs.digSum` of the values; the prefix (`dval_div`) and the window of `h` digits after
  `a` digits (`dval_div_mod`) of a digit vector.
* `cres_window`: `Q · |A − A'|_N ≤ |X − X'|_{NQ} + |e − e'|` for `X = AQ + e` (the integer core of the proof of
  `lem:liftsep`), and `cres_le_mul` (reducing modulo a divisor of the period does not increase toroidal distances).
* Freezing (`Frozen`, `chain_frozen`): after `j` lifts from level `L` with `D_{L+3j'} ≥ ⌊L/2⌋ + j'`, the digits
  `j, …, j + ⌊L/2⌋ − 1` of every coordinate are those of the point of `P_L` with the same first `L` index entries
  (and the shift of `P_L`), and the first `j` digits separate the remaining index entries.
* `frozen_sep`: the separation inequality for every digital shift `τ`, in integer form, with the weight of the
  frozen windows.
* `liftsep_int`, `liftsep` (`lem:liftsep`): `δN^{1/3} ≥ min(g_L, b^{L/3} − W b^{-2L/3})` with `v*_L`.
* `shiftcert_a`, `vcirc_eq_iInf` (`lem:shiftcert`(a)), `shiftcert_b` (`lem:shiftcert`(b)).
-/

namespace Z3NetB23.Proofs

open Matrix Finset Z3NetB23

/-! ## Digit vectors -/

section digits

variable {b : ℕ}

lemma dval_eq (n : ℕ) (x : Fin n → ZMod b) : dval b x = Z3Net.Proofs.digSum b n (fun j => (x j).val) := rfl

lemma dval_lt [NeZero b] {n : ℕ} (x : Fin n → ZMod b) : dval b x < b ^ n :=
  Z3Net.Proofs.digSum_lt b n _ (fun _ => ZMod.val_lt _)

/-- The prefix of `d` digits. -/
lemma dval_div [NeZero b] {n : ℕ} (x : Fin n → ZMod b) (d : ℕ) (hd : d ≤ n) :
    dval b x / b ^ (n - d) = dval b (topD d hd x) := by
  rw [dval_eq, Z3NetF.Proofs.digSum_div_prefix b (Nat.pos_of_neZero b) n _ (fun _ => ZMod.val_lt _) d hd]
  rfl

/-- The last `h` digits of a digit sum. -/
lemma digSum_mod_suffix (q : ℕ) (hq : 0 < q) (a : ℕ) : ∀ (h : ℕ) (f : Fin (a + h) → ℕ), (∀ j, f j < q) →
    Z3Net.Proofs.digSum q (a + h) f % q ^ h = Z3Net.Proofs.digSum q h (fun r => f ⟨a + r, by omega⟩) := by
  intro h
  induction h with
  | zero => intro f _; simp [Z3Net.Proofs.digSum, Nat.mod_one]
  | succ h ih =>
    intro f hf
    have e1 := Z3Net.Proofs.digSum_succ q (a + h) f
    have e2 := Z3Net.Proofs.digSum_succ q h (fun r => f ⟨a + r, by omega⟩)
    change Z3Net.Proofs.digSum q (a + h + 1) f % q ^ (h + 1) = _
    rw [e1, e2]
    set A := Z3Net.Proofs.digSum q (a + h) (fun j => f j.castSucc)
    have hr := hf (Fin.last (a + h))
    have hA := ih (fun j => f j.castSucc) (fun j => hf _)
    -- `(q A + r) mod q^(h+1) = q (A mod q^h) + r`
    have key : (q * A + f (Fin.last (a + h))) % q ^ (h + 1) = q * (A % q ^ h) + f (Fin.last (a + h)) := by
      have hlt : q * (A % q ^ h) + f (Fin.last (a + h)) < q ^ (h + 1) := by
        have := Nat.mod_lt A (pow_pos hq h)
        calc q * (A % q ^ h) + f (Fin.last (a + h)) < q * (A % q ^ h) + q := by omega
          _ = q * (A % q ^ h + 1) := by ring
          _ ≤ q * q ^ h := Nat.mul_le_mul_left _ this
          _ = q ^ (h + 1) := by ring
      have e : q * A + f (Fin.last (a + h)) =
          q ^ (h + 1) * (A / q ^ h) + (q * (A % q ^ h) + f (Fin.last (a + h))) := by
        have := Nat.div_add_mod A (q ^ h)
        calc q * A + f (Fin.last (a + h)) = q * (q ^ h * (A / q ^ h) + A % q ^ h) + f (Fin.last (a + h)) := by
              rw [this]
          _ = _ := by ring
      rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    rw [key, hA]
    rfl

/-- The window of `h` digits after the first `a` digits. -/
def winD {R : Type*} {n : ℕ} (a h : ℕ) (hah : a + h ≤ n) (x : Fin n → R) : Fin h → R :=
  fun r => x ⟨a + r, by omega⟩

lemma dval_div_mod [NeZero b] {n : ℕ} (x : Fin n → ZMod b) (a h : ℕ) (hah : a + h ≤ n) :
    dval b x / b ^ (n - (a + h)) % b ^ h = dval b (winD a h hah x) := by
  rw [dval_div x (a + h) hah, dval_eq, digSum_mod_suffix b (Nat.pos_of_neZero b) a h _ (fun _ => ZMod.val_lt _)]
  rfl

end digits

/-! ## Toroidal distances -/

section cres

open Z3NetC.Proofs in
/-- Reducing modulo a divisor `N` of the period `N k` does not increase toroidal distances. -/
lemma cres_le_mul (N k : ℕ) (hN : 0 < N) (hk : 0 < k) (u : ℤ) : Z3NetF.cres N u ≤ Z3NetF.cres (N * k) u := by
  obtain ⟨t, ht⟩ := cres_exists (N * k) (by positivity) u
  have := cres_le N hN u (k * t)
  have e : u + (N : ℤ) * (k * t) = u + ((N * k : ℕ) : ℤ) * t := by push_cast; ring
  rw [e, ← ht] at this
  exact_mod_cast this

open Z3NetC.Proofs in
/-- The integer core of the proof of `lem:liftsep`: for `X = A Q + e`, `X' = A' Q + e'`,
`Q |A − A'|_N ≤ |X − X'|_{NQ} + |e − e'|`. -/
lemma cres_window (N Q : ℕ) (hN : 0 < N) (hQ : 0 < Q) (X X' : ℤ) :
    (Q : ℤ) * Z3NetF.cres N (X / Q - X' / Q) ≤ Z3NetF.cres (N * Q) (X - X') + |X % Q - X' % Q| := by
  obtain ⟨t, ht⟩ := cres_exists (N * Q) (by positivity) (X - X')
  have hX := Int.emod_add_mul_ediv X Q
  have hX' := Int.emod_add_mul_ediv X' Q
  have h1 := cres_le N hN (X / Q - X' / Q) t
  have e : X - X' + ((N * Q : ℕ) : ℤ) * t = (Q : ℤ) * (X / Q - X' / Q + (N : ℤ) * t) + (X % Q - X' % Q) := by
    push_cast; linear_combination hX' - hX
  rw [ht, e]
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have h2 : (Q : ℤ) * Z3NetF.cres N (X / Q - X' / Q) ≤ (Q : ℤ) * |X / Q - X' / Q + (N : ℤ) * t| :=
    mul_le_mul_of_nonneg_left h1 hQ'.le
  have h3 : (Q : ℤ) * |X / Q - X' / Q + (N : ℤ) * t| ≤
      |(Q : ℤ) * (X / Q - X' / Q + (N : ℤ) * t) + (X % Q - X' % Q)| + |X % Q - X' % Q| := by
    rw [← abs_of_pos hQ', ← abs_mul, abs_of_pos hQ']
    have := abs_sub_abs_le_abs_sub ((Q : ℤ) * (X / Q - X' / Q + (N : ℤ) * t) + (X % Q - X' % Q))
      (X % Q - X' % Q)
    rw [add_sub_cancel_right] at this
    have h4 := abs_sub_abs_le_abs_sub ((Q : ℤ) * (X / Q - X' / Q + (N : ℤ) * t))
      (-(X % Q - X' % Q))
    rw [sub_neg_eq_add, abs_neg] at h4
    linarith
  linarith

end cres

/-! ## Freezing -/

section frozen

variable {b : ℕ} [Fact b.Prime]

/-- The frozen structure of `P_{L+3j}` relative to `P_L` (proof of `lem:liftsep`): the digits `j + r`,
`r < ⌊L/2⌋`, of `C_c w + σ_c` are digit `r` of `C₀_c n + σ₀_c`, `n` the first `L` entries of `w`; and the first
`j` digits of the three coordinates determine the entries of `w` after the first `L`. -/
structure Frozen (L : ℕ) (C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) (σ₀ : Fin 3 → Fin L → ZMod b)
    (m : ℕ) (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)) (σ : Fin 3 → Fin m → ZMod b) (j : ℕ) : Prop where
  hm : m = L + 3 * j
  win : ∀ (c : Fin 3) (r : ℕ) (hr : r < L / 2) (h1 : j + r < m) (h2 : r < L) (w : Fin m → ZMod b),
    (C c *ᵥ w) ⟨j + r, h1⟩ = (C₀ c *ᵥ fun i : Fin L => w ⟨i, by omega⟩) ⟨r, h2⟩
  sh : ∀ (c : Fin 3) (r : ℕ) (hr : r < L / 2) (h1 : j + r < m) (h2 : r < L), σ c ⟨j + r, h1⟩ = σ₀ c ⟨r, h2⟩
  inj : ∀ w : Fin m → ZMod b, (∀ i : Fin m, (i : ℕ) < L → w i = 0) →
    (∀ (c : Fin 3) (r : Fin m), (r : ℕ) < j → (C c *ᵥ w) r = 0) → w = 0

/-- **Freezing** (`lem:liftsep`, first paragraph of the proof): along a deep-shift chain from level `L` whose lift
at level `ℓ ≥ L` has depth `D ℓ ≥ ⌊L/2⌋ + (ℓ − L)/3`, the net at level `m` has the frozen structure, with
`m = L + 3j`. -/
theorem chain_frozen {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)} {σ₀ : Fin 3 → Fin L → ZMod b}
    {D : ℕ → ℕ} (hD : ∀ ℓ, L ≤ ℓ → L / 2 + (ℓ - L) / 3 ≤ D ℓ) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b L C₀ σ₀ D m C σ) : ∃ j, Frozen L C₀ σ₀ m C σ j := by
  induction h with
  | refl =>
    refine ⟨0, ⟨by omega, ?_, ?_, ?_⟩⟩
    · intro c r hr h1 h2 w
      have e : (⟨0 + r, h1⟩ : Fin L) = ⟨r, h2⟩ := Fin.ext (Nat.zero_add r)
      rw [e]
    · intro c r hr h1 h2
      have e : (⟨0 + r, h1⟩ : Fin L) = ⟨r, h2⟩ := Fin.ext (Nat.zero_add r)
      rw [e]
    · intro w hw _
      funext i; exact hw i i.isLt
  | @step ℓ C σ sA sB hch hA hB ih =>
    obtain ⟨j, hfz⟩ := ih
    have hm := hfz.hm
    have hDl : L / 2 + j ≤ D ℓ := by
      have := hD ℓ (by omega)
      rwa [show (ℓ - L) / 3 = j by omega] at this
    refine ⟨j + 1, ⟨by omega, ?_, ?_, ?_⟩⟩
    · intro c r hr h1 h2 w
      have e := liftGen_mulVec_block C sA sB w c (j + r) (by omega)
      have e2 : (⟨j + 1 + r, h1⟩ : Fin (ℓ + 3)) = ⟨j + r + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e2, e, hA c ⟨j + r, by omega⟩ (by simp; omega), hB c ⟨j + r, by omega⟩ (by simp; omega),
        zero_mul, zero_mul, add_zero, add_zero]
      rw [hfz.win c r hr (by omega) h2 (nOf w)]
      rfl
    · intro c r hr h1 h2
      simp only [liftShift]
      rw [dif_pos (by constructor <;> omega)]
      have := hfz.sh c r hr (by omega) h2
      convert this using 2
      exact Fin.ext (by simp only [Fin.val_mk]; omega)
    · intro w hw htop
      -- the top digits give `α = δ₁ = δ₂ = 0`
      have t0 := htop 0 ⟨0, by omega⟩ (by simp)
      have t1 := htop 1 ⟨0, by omega⟩ (by simp)
      have t2 := htop 2 ⟨0, by omega⟩ (by simp)
      rw [liftGen_mulVec_top] at t0 t1 t2
      simp [liftTop] at t0 t1 t2
      rw [t0, zero_add] at t1
      rw [t0, t1, zero_add, zero_add] at t2
      -- the earlier top digits give `n = 0`
      have hn : nOf w = 0 := by
        apply hfz.inj (nOf w)
        · intro i hi; exact hw (Fin.castAdd 3 i) (by simpa using hi)
        · intro c r hr
          have := htop c ⟨(r : ℕ) + 1, by omega⟩ (by simp; omega)
          rw [liftGen_mulVec_block C sA sB w c r r.isLt, t1, t2, mul_zero, mul_zero, add_zero, add_zero]
            at this
          exact this
      exact idx_eq_zero w hn t0 t1 t2

end frozen

/-! ## Separation -/

section sep

variable {b : ℕ} [Fact b.Prime]

lemma b_pos : 0 < b := (Fact.out : b.Prime).pos

open Z3NetC.Proofs in
lemma cres_pos' (N : ℕ) (hN : 0 < N) (u : ℤ) (hu : u % (N : ℤ) ≠ 0) : 1 ≤ Z3NetF.cres N u := by
  have h := cres_spec N hN u
  have h0 : 0 ≤ u % (N : ℤ) := Int.emod_nonneg _ (by omega)
  have h1 : u % (N : ℤ) < N := Int.emod_lt_of_pos _ (by omega)
  have : (1 : ℤ) ≤ min (u % (N : ℤ)) ((N : ℤ) - u % (N : ℤ)) := le_min (by omega) (by omega)
  rw [← h] at this
  exact_mod_cast this

lemma hW_mono {s t : ℕ} (h : s ≤ t) : hW s ≤ hW t := by
  unfold hW; exact Nat.pow_le_pow_left (by omega) 2

/-- The first `L` index entries. -/
def nL {L m : ℕ} (hLm : L ≤ m) (w : Fin m → ZMod b) : Fin L → ZMod b := fun i => w ⟨i, by omega⟩

/-- One coordinate, distinct windows: `Q (|K − K'|_{b^H} − 1) ≤ |X − X'|_{b^m}` for the digit vectors `x, x'` of
length `m`, `K` the window of `H` digits after the first `j`, `Q = b^(m - (j + H))`. -/
lemma coord_win (m j H : ℕ) (hjH : j + H ≤ m) (x x' : Fin m → ZMod b) :
    b ^ (m - (j + H)) * (Z3NetF.cres (b ^ H) ((dval b (winD j H hjH x) : ℤ) - dval b (winD j H hjH x')) - 1) ≤
      Z3NetF.cres (b ^ m) ((dval b x : ℤ) - dval b x') := by
  have hb := b_pos (b := b)
  have : NeZero b := ⟨hb.ne'⟩
  set Q := b ^ (m - (j + H)) with hQ
  have hQp : 0 < Q := pow_pos hb _
  have hBH : 0 < b ^ H := pow_pos hb _
  set X := dval b x
  set X' := dval b x'
  -- `|X − X'|_{b^m} ≥ |X − X'|_{b^H Q}`
  have hm : b ^ m = b ^ H * Q * b ^ j := by
    rw [hQ, ← pow_add, ← pow_add]; congr 1; omega
  have h1 : Z3NetF.cres (b ^ H * Q) ((X : ℤ) - X') ≤ Z3NetF.cres (b ^ m) ((X : ℤ) - X') := by
    rw [hm]; exact cres_le_mul _ _ (by positivity) (pow_pos hb _) _
  have h2 := cres_window (b ^ H) Q hBH hQp (X : ℤ) X'
  -- `X / Q ≡ K (mod b^H)`
  have hK : ∀ y : Fin m → ZMod b, ((dval b y : ℤ) / (Q : ℤ)) =
      (dval b (winD j H hjH y) : ℤ) + (b ^ H : ℕ) * ((dval b y / Q / b ^ H : ℕ) : ℤ) := by
    intro y
    have e := dval_div_mod y j H hjH
    have := Nat.mod_add_div (dval b y / Q) (b ^ H)
    rw [← Int.natCast_div, ← e]
    exact_mod_cast this.symm
  have h3 : Z3NetF.cres (b ^ H) ((X : ℤ) / Q - (X' : ℤ) / Q) =
      Z3NetF.cres (b ^ H) ((dval b (winD j H hjH x) : ℤ) - dval b (winD j H hjH x')) := by
    rw [hK x, hK x']
    have e : (dval b (winD j H hjH x) : ℤ) + (b ^ H : ℕ) * ((X / Q / b ^ H : ℕ) : ℤ) -
        ((dval b (winD j H hjH x') : ℤ) + (b ^ H : ℕ) * ((X' / Q / b ^ H : ℕ) : ℤ)) =
        ((dval b (winD j H hjH x) : ℤ) - dval b (winD j H hjH x')) +
          (b ^ H : ℕ) * ((X / Q / b ^ H : ℕ) - (X' / Q / b ^ H : ℕ) : ℤ) := by ring
    rw [e, Z3NetC.Proofs.cres_add_mul]
  have h4 : |(X : ℤ) % Q - (X' : ℤ) % Q| ≤ Q - 1 := by
    have a1 : 0 ≤ (X : ℤ) % Q := Int.emod_nonneg _ (by omega)
    have a2 : (X : ℤ) % Q < Q := Int.emod_lt_of_pos _ (by omega)
    have a3 : 0 ≤ (X' : ℤ) % Q := Int.emod_nonneg _ (by omega)
    have a4 : (X' : ℤ) % Q < Q := Int.emod_lt_of_pos _ (by omega)
    rw [abs_le]; constructor <;> omega
  rw [h3] at h2
  set κ := Z3NetF.cres (b ^ H) ((dval b (winD j H hjH x) : ℤ) - dval b (winD j H hjH x'))
  have : (Q : ℤ) * κ ≤ Z3NetF.cres (b ^ m) ((X : ℤ) - X') + (Q - 1) := by
    have := Int.ofNat_le.2 h1; push_cast at this; linarith
  rcases Nat.eq_zero_or_pos κ with hκ | hκ
  · rw [hκ]; simp
  · have : ((Q * (κ - 1) : ℕ) : ℤ) ≤ Z3NetF.cres (b ^ m) ((X : ℤ) - X') := by
      push_cast [Nat.cast_sub hκ]; linarith
    exact_mod_cast this

/-- The window of the frozen digits of a shifted point: digit `r` of the window is digit `r` of the point of `P_L`
with the same first `L` index entries, shifted by digit `j + r` of the shift. -/
lemma frozen_win {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)} {σ₀ : Fin 3 → Fin L → ZMod b} {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b} {j : ℕ}
    (hfz : Frozen L C₀ σ₀ m C σ j) (hjH : j + L / 2 ≤ m) (hLm : L ≤ m) (τ : Fin 3 → Fin m → ZMod b)
    (w : Fin m → ZMod b) (c : Fin 3) :
    winD j (L / 2) hjH (C c *ᵥ w + τ c) =
      topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ nL hLm w) +
        fun r : Fin (L / 2) => τ c ⟨j + (r : ℕ), by have := r.isLt; omega⟩ := by
  funext r
  simp only [winD, Pi.add_apply, topD]
  rw [hfz.win c r r.isLt (by omega) (by omega) w]
  rfl

/-- **The separation inequality, distinct windows** (proof of `lem:liftsep`, "different `p ≠ p'`"), for every
digital shift `τ`: `Q² ∑_c max(0, |K_c − K'_c|_{b^H} − 1)² ≤ |X − X'|²` (squared toroidal distance at scale `b^m`),
`K_c` the frozen windows, `Q = b^(m - (j + ⌊L/2⌋))`. -/
lemma sep_diff (L m j : ℕ) (hjH : j + L / 2 ≤ m) (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b))
    (τ : Fin 3 → Fin m → ZMod b) (w w' : Fin m → ZMod b) :
    (b ^ (m - (j + L / 2))) ^ 2 * ∑ c : Fin 3, hW (Z3NetF.cres (b ^ (L / 2))
        ((dval b (winD j (L / 2) hjH (C c *ᵥ w + τ c)) : ℤ) - dval b (winD j (L / 2) hjH (C c *ᵥ w' + τ c)))) ≤
      Z3NetF.torusDist2 (b ^ m) (Z3NetF.digPointShift b m C τ w) (Z3NetF.digPointShift b m C τ w') := by
  unfold Z3NetF.torusDist2
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have h := coord_win m j (L / 2) hjH (C c *ᵥ w + τ c) (C c *ᵥ w' + τ c)
  have h2 := Nat.pow_le_pow_left h 2
  unfold hW
  calc (b ^ (m - (j + L / 2))) ^ 2 * (Z3NetF.cres (b ^ (L / 2)) _ - 1) ^ 2 = _ := by rw [← mul_pow]
    _ ≤ _ := h2

/-- **The separation inequality, same window** (proof of `lem:liftsep`, "same `p`, different `u`"): if two indices
agree on their first `L` entries but differ, `(b^(m-j) − Q + 1)² ≤ |X − X'|²`, for every digital shift. -/
lemma sep_same {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)} {σ₀ : Fin 3 → Fin L → ZMod b} {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b} {j : ℕ}
    (hfz : Frozen L C₀ σ₀ m C σ j) (hjH : j + L / 2 ≤ m) (hLm : L ≤ m) (τ : Fin 3 → Fin m → ZMod b)
    (w w' : Fin m → ZMod b) (hn : nL hLm w = nL hLm w') (hww : w ≠ w') :
    (b ^ (m - j) - b ^ (m - (j + L / 2)) + 1) ^ 2 ≤
      Z3NetF.torusDist2 (b ^ m) (Z3NetF.digPointShift b m C τ w) (Z3NetF.digPointShift b m C τ w') := by
  have hb := b_pos (b := b)
  have : NeZero b := ⟨hb.ne'⟩
  -- a coordinate whose first `j` digits differ
  obtain ⟨c, r, hr, hcr⟩ : ∃ (c : Fin 3) (r : Fin m), (r : ℕ) < j ∧ (C c *ᵥ (w - w')) r ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hww
    have := hfz.inj (w - w') (fun i hi => by
      have := congrFun hn ⟨i, hi⟩
      simp only [nL] at this
      simp [Pi.sub_apply, this]) hcon
    exact sub_eq_zero.1 this
  set H := L / 2
  set Q := b ^ (m - (j + H))
  set Q2 := b ^ (m - j)
  set x := C c *ᵥ w + τ c
  set x' := C c *ᵥ w' + τ c
  have hj : j ≤ m := by omega
  -- the tops differ
  have hS : dval b (topD j hj x) ≠ dval b (topD j hj x') := by
    intro h
    have := Z3NetF.Proofs.digSum_inj b hb j _ _ (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _) h
    have h2 := congrFun this ⟨r, hr⟩
    simp only [topD, x, x'] at h2
    apply hcr
    have h3 : (C c *ᵥ w) r + τ c r = (C c *ᵥ w') r + τ c r := ZMod.val_injective b h2
    rw [mulVec_sub, Pi.sub_apply, sub_eq_zero]
    exact add_right_cancel h3
  -- the windows agree
  have hK : dval b (winD j H hjH x) = dval b (winD j H hjH x') := by
    simp only [x, x']
    rw [frozen_win hfz hjH hLm τ w c, frozen_win hfz hjH hLm τ w' c, hn]
  set X := dval b x
  set X' := dval b x'
  have hQ2 : Q2 = Q * b ^ H := by
    simp only [Q, Q2]; rw [← pow_add]; congr 1; omega
  have hm : b ^ m = b ^ j * Q2 := by
    simp only [Q2]; rw [← pow_add]; congr 1; omega
  have hQp : 0 < Q := pow_pos hb _
  have hQ2p : 0 < Q2 := pow_pos hb _
  have hw := cres_window (b ^ j) Q2 (pow_pos hb _) hQ2p (X : ℤ) X'
  -- `X / Q2` is the top
  have hdiv : ∀ y : Fin m → ZMod b, (dval b y : ℤ) / (Q2 : ℤ) = dval b (topD j hj y) := by
    intro y; rw [← Int.natCast_div]; exact_mod_cast dval_div y j hj
  rw [hdiv x, hdiv x'] at hw
  have hc1 : 1 ≤ Z3NetF.cres (b ^ j) ((dval b (topD j hj x) : ℤ) - dval b (topD j hj x')) := by
    apply cres_pos' _ (pow_pos hb _)
    have a1 := dval_lt (topD j hj x)
    have a2 := dval_lt (topD j hj x')
    intro h0
    have hd : ((b ^ j : ℕ) : ℤ) ∣ ((dval b (topD j hj x) : ℤ) - dval b (topD j hj x')) :=
      Int.dvd_of_emod_eq_zero h0
    have b1 : ((dval b (topD j hj x) : ℕ) : ℤ) < ((b ^ j : ℕ) : ℤ) := Int.ofNat_lt.2 a1
    have b2 : ((dval b (topD j hj x') : ℕ) : ℤ) < ((b ^ j : ℕ) : ℤ) := Int.ofNat_lt.2 a2
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    exact hS (by omega)
  -- the remainders differ by less than `Q`
  have hrem : |(X : ℤ) % Q2 - (X' : ℤ) % Q2| ≤ Q - 1 := by
    have e : ∀ y : Fin m → ZMod b, (dval b y : ℤ) % Q2 =
        (dval b y % Q : ℕ) + (Q : ℤ) * (dval b (winD j H hjH y) : ℕ) := by
      intro y
      have h1 : dval b y % Q2 = dval b y % Q + Q * dval b (winD j H hjH y) := by
        rw [hQ2, Nat.mod_mul, dval_div_mod]
      rw [← Int.natCast_mod, h1]
      push_cast; ring
    rw [e x, e x', show dval b (winD j H hjH x) = dval b (winD j H hjH x') from hK]
    have a1 := Nat.mod_lt (dval b x) hQp
    have a2 := Nat.mod_lt (dval b x') hQp
    rw [abs_le]; constructor <;> push_cast <;> omega
  have key : (Q2 : ℤ) - (Q - 1) ≤ Z3NetF.cres (b ^ m) ((X : ℤ) - X') := by
    rw [hm]
    have := mul_le_mul_of_nonneg_left (Int.ofNat_le.2 hc1) (show (0 : ℤ) ≤ Q2 by positivity)
    push_cast at this
    linarith
  have hQQ : Q ≤ Q2 := by rw [hQ2]; exact Nat.le_mul_of_pos_right _ (pow_pos hb _)
  have key' : Q2 - Q + 1 ≤ Z3NetF.cres (b ^ m) ((X : ℤ) - X') := by
    have : ((Q2 - Q + 1 : ℕ) : ℤ) ≤ Z3NetF.cres (b ^ m) ((X : ℤ) - X') := by
      push_cast [Nat.cast_sub hQQ]; linarith
    exact_mod_cast this
  unfold Z3NetF.torusDist2
  calc (Q2 - Q + 1) ^ 2 ≤ Z3NetF.cres (b ^ m) ((X : ℤ) - X') ^ 2 := Nat.pow_le_pow_left key' 2
    _ ≤ ∑ c', Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ w c' : ℤ) -
        Z3NetF.digPointShift b m C τ w' c') ^ 2 :=
      Finset.single_le_sum (f := fun c' => Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ w c' : ℤ) -
        Z3NetF.digPointShift b m C τ w' c') ^ 2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

end sep

/-! ## `lem:liftsep` and `lem:shiftcert` -/

section main

variable {b : ℕ} [Fact b.Prime]

/-- The weight of a pair of distinct indices of `P_L` in `v*_L`. -/
lemma weight_eq_win (L : ℕ) (C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) (σ₀ : Fin 3 → Fin L → ZMod b)
    (n : Fin L → ZMod b) (c : Fin 3) :
    Z3NetF.digPointShift b L C₀ σ₀ n c / b ^ (L - L / 2) = dval b (topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ n + σ₀ c)) := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  exact dval_div (C₀ c *ᵥ n + σ₀ c) (L / 2) (Nat.div_le_self L 2)

/-- **`lem:liftsep`, integer form**: along a deep-shift chain from `P_L` (generator matrices `C₀`, shift `σ₀`) with
`D_ℓ ≥ ⌊L/2⌋ + (ℓ − L)/3` for `ℓ ≥ L`, the net at level `m = L + 3j` (with its own shift) satisfies, for any two
distinct indices, `min(Q² v*_L, (b^(L+2j) − Q + 1)²) ≤ |X − X'|²` with `Q = W b^(2j)`, `W = b^(L − ⌊L/2⌋)`
(squared toroidal distance at integer scale `b^m`). -/
theorem liftsep_int {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)} {σ₀ : Fin 3 → Fin L → ZMod b}
    {D : ℕ → ℕ} (hD : ∀ ℓ, L ≤ ℓ → L / 2 + (ℓ - L) / 3 ≤ D ℓ) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b L C₀ σ₀ D m C σ) (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    ∃ j, m = L + 3 * j ∧
      min ((b ^ (L - L / 2 + 2 * j)) ^ 2 * vstar b L C₀ σ₀) ((b ^ (L + 2 * j) - b ^ (L - L / 2 + 2 * j) + 1) ^ 2) ≤
        Z3NetF.torusDist2 (b ^ m) (Z3NetF.digPointShift b m C σ v) (Z3NetF.digPointShift b m C σ w) := by
  obtain ⟨j, hfz⟩ := chain_frozen hD h
  have hm := hfz.hm
  refine ⟨j, hm, ?_⟩
  have hjH : j + L / 2 ≤ m := by omega
  have hLm : L ≤ m := by omega
  have e1 : m - (j + L / 2) = L - L / 2 + 2 * j := by omega
  have e2 : m - j = L + 2 * j := by omega
  by_cases hn : nL hLm v = nL hLm w
  · exact min_le_of_right_le (by rw [← e1, ← e2]; exact sep_same hfz hjH hLm σ v w hn hvw)
  · apply min_le_of_left_le
    have hs := sep_diff L m j hjH C σ v w
    rw [e1] at hs
    refine le_trans (Nat.mul_le_mul_left _ ?_) hs
    -- the windows are the top digits of the points of `P_L`
    refine ciInf_le (OrderBot.bddBelow _) ⟨(nL hLm v, nL hLm w), hn⟩ |>.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun c _ => ?_
    have esh : ∀ y : Fin m → ZMod b, topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ nL hLm y + σ₀ c) =
        topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ nL hLm y) +
          fun r : Fin (L / 2) => σ c ⟨j + (r : ℕ), by have := r.isLt; omega⟩ := by
      intro y; funext r; simp only [topD, Pi.add_apply]; rw [hfz.sh c r r.isLt (by omega) (by omega)]; rfl
    simp only
    rw [weight_eq_win, weight_eq_win, frozen_win hfz hjH hLm σ v c, frozen_win hfz hjH hLm σ w c, esh v, esh w]

/-- **`lem:shiftcert`(a), integer form**: under the hypothesis of `lem:liftsep`, for every `j`, every digital shift
`τ` of depth `m` and any two distinct indices, `min(Q² v°_L, (b^(L+2j) − Q + 1)²) ≤ |X − X'|²`. -/
theorem shiftcert_a_int {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)} {σ₀ : Fin 3 → Fin L → ZMod b}
    {D : ℕ → ℕ} (hD : ∀ ℓ, L ≤ ℓ → L / 2 + (ℓ - L) / 3 ≤ D ℓ) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b L C₀ σ₀ D m C σ) (τ : Fin 3 → Fin m → ZMod b) (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    ∃ j, m = L + 3 * j ∧
      min ((b ^ (L - L / 2 + 2 * j)) ^ 2 * vcirc b L C₀) ((b ^ (L + 2 * j) - b ^ (L - L / 2 + 2 * j) + 1) ^ 2) ≤
        Z3NetF.torusDist2 (b ^ m) (Z3NetF.digPointShift b m C τ v) (Z3NetF.digPointShift b m C τ w) := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  obtain ⟨j, hfz⟩ := chain_frozen hD h
  have hm := hfz.hm
  refine ⟨j, hm, ?_⟩
  have hjH : j + L / 2 ≤ m := by omega
  have hLm : L ≤ m := by omega
  have e1 : m - (j + L / 2) = L - L / 2 + 2 * j := by omega
  have e2 : m - j = L + 2 * j := by omega
  by_cases hn : nL hLm v = nL hLm w
  · exact min_le_of_right_le (by rw [← e1, ← e2]; exact sep_same hfz hjH hLm τ v w hn hvw)
  · apply min_le_of_left_le
    have hs := sep_diff L m j hjH C τ v w
    rw [e1] at hs
    refine le_trans (Nat.mul_le_mul_left _ ?_) hs
    refine ciInf_le (OrderBot.bddBelow _) ⟨(nL hLm v, nL hLm w), hn⟩ |>.trans ?_
    refine Finset.sum_le_sum fun c _ => hW_mono ?_
    simp only
    rw [frozen_win hfz hjH hLm τ v c, frozen_win hfz hjH hLm τ w c, ← Z3NetC.Proofs.cres_neg _
      (pow_pos (Fact.out : b.Prime).pos _), neg_sub]
    set X := topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ nL hLm v) + fun r : Fin (L / 2) => τ c ⟨j + (r : ℕ), by
      have := r.isLt; omega⟩
    have e : topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ nL hLm w) + (fun r : Fin (L / 2) => τ c ⟨j + (r : ℕ), by
        have := r.isLt; omega⟩) = X + topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ (nL hLm w - nL hLm v)) := by
      funext r; simp only [X, topD, Pi.add_apply, mulVec_sub, Pi.sub_apply]; ring
    rw [e]
    exact Finset.inf'_le _ (Finset.mem_univ X)

/-- **`lem:shiftcert`(a), `v°_L` as a minimum over shifts**: `v°_L = min_{τ'} v*_L(P_L ⊕ τ')` (`τ'` over all digital
shifts of `P_L`; `v*_L` of `P_L` with the shift `τ'`). Here `P_L` has generator matrices `C₀` and `L ≥ 1`. -/
theorem vcirc_eq_iInf (L : ℕ) (hL : 1 ≤ L) (C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)) :
    vcirc b L C₀ = ⨅ τ' : Fin 3 → Fin L → ZMod b, vstar b L C₀ τ' := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  have hb := (Fact.out : b.Prime).pos
  haveI hne : Nonempty {p : (Fin L → ZMod b) × (Fin L → ZMod b) // p.1 ≠ p.2} :=
    ⟨⟨(0, Pi.single ⟨0, hL⟩ 1), fun h => by
      have := congrFun h ⟨0, hL⟩; simp at this⟩⟩
  -- every pair weight with any shift dominates its every-shift weight
  have hpair : ∀ (τ' : Fin 3 → Fin L → ZMod b) (n n' : Fin L → ZMod b) (c : Fin 3),
      muD b (topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ (n' - n))) ≤
        Z3NetF.cres (b ^ (L / 2)) (((Z3NetF.digPointShift b L C₀ τ' n c / b ^ (L - L / 2) : ℕ) : ℤ) -
          ((Z3NetF.digPointShift b L C₀ τ' n' c / b ^ (L - L / 2) : ℕ) : ℤ)) := by
    intro τ' n n' c
    rw [weight_eq_win, weight_eq_win, ← Z3NetC.Proofs.cres_neg _ (pow_pos hb _), neg_sub]
    have e : topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ n' + τ' c) =
        topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ n + τ' c) + topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ (n' - n)) := by
      funext r; simp only [topD, Pi.add_apply, mulVec_sub, Pi.sub_apply]; ring
    rw [e]
    exact Finset.inf'_le _ (Finset.mem_univ _)
  apply le_antisymm
  · apply le_ciInf
    intro τ'
    apply le_ciInf
    intro p
    refine ciInf_le (OrderBot.bddBelow _) p |>.trans ?_
    exact Finset.sum_le_sum fun c _ => hW_mono (hpair τ' p.1.1 p.1.2 c)
  · -- a pair and digits attaining `v°_L`
    obtain ⟨p, hp⟩ := ciInf_mem (fun p : {p : (Fin L → ZMod b) × (Fin L → ZMod b) // p.1 ≠ p.2} =>
      ∑ c : Fin 3, hW (muD b (topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ (p.1.2 - p.1.1)))))
    have hX : ∀ c : Fin 3, ∃ X : Fin (L / 2) → ZMod b,
        muD b (topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ (p.1.2 - p.1.1))) =
          Z3NetF.cres (b ^ (L / 2)) ((dval b (X + topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ (p.1.2 - p.1.1))) : ℤ) -
            dval b X) := by
      intro c
      obtain ⟨X, -, hX⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin (L / 2) → ZMod b))
        (fun X : Fin (L / 2) → ZMod b => Z3NetF.cres (b ^ (L / 2))
          ((dval b (X + topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ (p.1.2 - p.1.1))) : ℤ) - dval b X))
      exact ⟨X, hX⟩
    choose X hXc using hX
    -- the shift that puts the first point of the pair on the digits `X`
    let τ' : Fin 3 → Fin L → ZMod b := fun c i =>
      if h : (i : ℕ) < L / 2 then X c ⟨i, h⟩ - (C₀ c *ᵥ p.1.1) i else 0
    refine (ciInf_le (OrderBot.bddBelow _) τ').trans ?_
    refine (ciInf_le (OrderBot.bddBelow _) p).trans (le_of_eq ?_)
    unfold vcirc
    rw [← hp]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hXc c, weight_eq_win, weight_eq_win, ← Z3NetC.Proofs.cres_neg _ (pow_pos hb _), neg_sub]
    have e1 : topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ p.1.1 + τ' c) = X c := by
      funext r
      simp only [topD, Pi.add_apply, τ', Fin.coe_castLE, dif_pos r.isLt]
      ring
    have e2 : topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ p.1.2 + τ' c) =
        X c + topD (L / 2) (Nat.div_le_self L 2) (C₀ c *ᵥ (p.1.2 - p.1.1)) := by
      funext r
      simp only [topD, Pi.add_apply, τ', Fin.coe_castLE, dif_pos r.isLt, mulVec_sub, Pi.sub_apply]
      ring
    rw [e1, e2]

/-- **`lem:shiftcert`(b)**: for every digital net (generator matrices `C`, level `m`): (i) for every digital shift `τ`
and any two distinct indices `v, w`, `∑_c μ_m(Δ_c)² ≤ |X − X'|²` (squared toroidal distance at scale `b^m`), where
`Δ = C(w − v)` is the digit difference; (ii) for every nonzero `d` some shift attains it with the pair `(0, d)`.
So `min_τ δ(P ⊕ τ)² = b^{-2m} min_{Δ ≠ 0} ∑_c μ_m(Δ_c)²` (over the nonzero digit differences `Δ` of two points). -/
theorem shiftcert_b {m : ℕ} (C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)) :
    (∀ (τ : Fin 3 → Fin m → ZMod b) (v w : Fin m → ZMod b),
      ∑ c : Fin 3, muD b (C c *ᵥ (w - v)) ^ 2 ≤
        Z3NetF.torusDist2 (b ^ m) (Z3NetF.digPointShift b m C τ v) (Z3NetF.digPointShift b m C τ w)) ∧
    (∀ d : Fin m → ZMod b, ∃ τ : Fin 3 → Fin m → ZMod b,
      Z3NetF.torusDist2 (b ^ m) (Z3NetF.digPointShift b m C τ 0) (Z3NetF.digPointShift b m C τ d) =
        ∑ c : Fin 3, muD b (C c *ᵥ d) ^ 2) := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  have hb := (Fact.out : b.Prime).pos
  constructor
  · intro τ v w
    unfold Z3NetF.torusDist2
    refine Finset.sum_le_sum fun c _ => Nat.pow_le_pow_left ?_ 2
    simp only [Z3NetF.digPointShift]
    change muD b (C c *ᵥ (w - v)) ≤ Z3NetF.cres (b ^ m) ((dval b (C c *ᵥ v + τ c) : ℤ) - dval b (C c *ᵥ w + τ c))
    rw [← Z3NetC.Proofs.cres_neg _ (pow_pos hb _), neg_sub]
    have e : C c *ᵥ w + τ c = (C c *ᵥ v + τ c) + C c *ᵥ (w - v) := by
      rw [mulVec_sub]; abel
    rw [e]
    exact Finset.inf'_le _ (Finset.mem_univ _)
  · intro d
    have hX : ∀ c : Fin 3, ∃ X : Fin m → ZMod b, muD b (C c *ᵥ d) =
        Z3NetF.cres (b ^ m) ((dval b (X + C c *ᵥ d) : ℤ) - dval b X) := by
      intro c
      obtain ⟨X, -, hX⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin m → ZMod b))
        (fun X : Fin m → ZMod b => Z3NetF.cres (b ^ m) ((dval b (X + C c *ᵥ d) : ℤ) - dval b X))
      exact ⟨X, hX⟩
    choose X hXc using hX
    refine ⟨X, ?_⟩
    unfold Z3NetF.torusDist2
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hXc c, ← Z3NetC.Proofs.cres_neg _ (pow_pos hb _), neg_sub]
    simp only [Z3NetF.digPointShift, mulVec_zero, zero_add]
    rw [add_comm (C c *ᵥ d)]
    rfl

end main

/-! ## Real form -/

section real

lemma sqrt_torus (N : ℕ) (hN : 0 < N) (x y : Fin 3 → ℕ) :
    Real.sqrt (∑ c, ((Z3NetF.cres N ((x c : ℤ) - y c) : ℝ) / N) ^ 2) =
      Real.sqrt (Z3NetF.torusDist2 N x y : ℝ) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ∑ c, ((Z3NetF.cres N ((x c : ℤ) - y c) : ℝ) / N) ^ 2 = (Z3NetF.torusDist2 N x y : ℝ) / (N : ℝ) ^ 2 := by
    unfold Z3NetF.torusDist2
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [div_pow]
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hN'.le]

/-- From the integer form of `lem:liftsep` to `δN^{1/3} ≥ min(g_L, b^{L/3} − W b^{-2L/3})` at level `m = L + 3j`. -/
lemma real_bound (b L j V T : ℕ) (hb : 1 < b)
    (hT : min ((b ^ (L - L / 2 + 2 * j)) ^ 2 * V) ((b ^ (L + 2 * j) - b ^ (L - L / 2 + 2 * j) + 1) ^ 2) ≤ T) :
    min (gL b L V) (((b : ℝ) ^ L) ^ (1 / 3 : ℝ) - (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ))) *
      ((b : ℝ) ^ (L + 3 * j)) ^ (-(1 / 3 : ℝ)) ≤ Real.sqrt T / (b : ℝ) ^ (L + 3 * j) := by
  set B : ℝ := (b : ℝ) with hBdef
  have hB : 1 < B := by rw [hBdef]; exact_mod_cast hb
  have hB0 : 0 < B := by linarith
  have hBL : 0 < B ^ L := pow_pos hB0 L
  set u : ℝ := (B ^ L) ^ (-(1 / 3 : ℝ)) with hudef
  have hu : 0 < u := Real.rpow_pos_of_pos hBL _
  have hu3 : u ^ 3 = (B ^ L)⁻¹ := by
    rw [hudef, ← Real.rpow_mul_natCast hBL.le, show (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 by norm_num,
      Real.rpow_neg_one]
  have h13 : (B ^ L) ^ (1 / 3 : ℝ) = u⁻¹ := by
    rw [hudef, Real.rpow_neg hBL.le, inv_inv]
  have h23 : (B ^ L) ^ (-(2 / 3 : ℝ)) = u ^ 2 := by
    rw [hudef, ← Real.rpow_mul_natCast hBL.le, show (-(1 / 3 : ℝ)) * ((2 : ℕ) : ℝ) = -(2 / 3) by norm_num]
  have hm : (B ^ (L + 3 * j)) ^ (-(1 / 3 : ℝ)) = u * (B ^ j)⁻¹ := by
    rw [pow_add, show B ^ (3 * j) = (B ^ j) ^ 3 by ring, Real.mul_rpow hBL.le (by positivity), ← hudef,
      ← Real.rpow_natCast_mul (by positivity), show ((3 : ℕ) : ℝ) * (-(1 / 3 : ℝ)) = -1 by norm_num,
      Real.rpow_neg_one]
  set W : ℝ := B ^ (L - L / 2) with hWdef
  have hW0 : 0 < W := pow_pos hB0 _
  have hgL : gL b L V = W * Real.sqrt V * u ^ 2 := by
    unfold gL; rw [← hBdef, h23]
  rw [hgL, h13, h23, hm]
  have hk : 0 ≤ u * (B ^ j)⁻¹ := by positivity
  have hBm : 0 < B ^ (L + 3 * j) := pow_pos hB0 _
  have hQ : ((b ^ (L - L / 2 + 2 * j) : ℕ) : ℝ) = W * B ^ (2 * j) := by
    push_cast; rw [pow_add]
  have hQ2 : ((b ^ (L + 2 * j) : ℕ) : ℝ) = B ^ L * B ^ (2 * j) := by
    push_cast; rw [pow_add]
  rcases min_le_iff.1 hT with h | h
  · -- distinct windows
    calc min (W * Real.sqrt V * u ^ 2) (u⁻¹ - W * u ^ 2) * (u * (B ^ j)⁻¹)
        ≤ W * Real.sqrt V * u ^ 2 * (u * (B ^ j)⁻¹) := mul_le_mul_of_nonneg_right (min_le_left _ _) hk
      _ = W * B ^ (2 * j) * Real.sqrt V / B ^ (L + 3 * j) := by
          rw [show W * Real.sqrt V * u ^ 2 * (u * (B ^ j)⁻¹) = W * Real.sqrt V * u ^ 3 * (B ^ j)⁻¹ by ring, hu3,
            pow_add, show B ^ (3 * j) = B ^ (2 * j) * B ^ j by rw [← pow_add]; ring_nf]
          field_simp
      _ ≤ Real.sqrt T / B ^ (L + 3 * j) := by
          apply div_le_div_of_nonneg_right _ hBm.le
          rw [← hQ]
          have h' : (((b ^ (L - L / 2 + 2 * j)) ^ 2 * V : ℕ) : ℝ) ≤ T := by exact_mod_cast h
          calc ((b ^ (L - L / 2 + 2 * j) : ℕ) : ℝ) * Real.sqrt V
              = Real.sqrt ((((b ^ (L - L / 2 + 2 * j)) ^ 2 * V : ℕ) : ℝ)) := by
                push_cast
                rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
            _ ≤ Real.sqrt T := Real.sqrt_le_sqrt h'
  · -- same window
    have hQQ : b ^ (L - L / 2 + 2 * j) ≤ b ^ (L + 2 * j) := Nat.pow_le_pow_right (by omega) (by omega)
    calc min (W * Real.sqrt V * u ^ 2) (u⁻¹ - W * u ^ 2) * (u * (B ^ j)⁻¹)
        ≤ (u⁻¹ - W * u ^ 2) * (u * (B ^ j)⁻¹) := mul_le_mul_of_nonneg_right (min_le_right _ _) hk
      _ = (B ^ L * B ^ (2 * j) - W * B ^ (2 * j)) / B ^ (L + 3 * j) := by
          rw [show (u⁻¹ - W * u ^ 2) * (u * (B ^ j)⁻¹) = (u⁻¹ * u - W * u ^ 3) * (B ^ j)⁻¹ by ring,
            inv_mul_cancel₀ hu.ne', hu3, pow_add, show B ^ (3 * j) = B ^ (2 * j) * B ^ j by rw [← pow_add]; ring_nf]
          field_simp
      _ ≤ Real.sqrt T / B ^ (L + 3 * j) := by
          apply div_le_div_of_nonneg_right _ hBm.le
          have e1 : B ^ L * B ^ (2 * j) = (b : ℝ) ^ (L + 2 * j) := by rw [hBdef, ← pow_add]
          have e2 : W * B ^ (2 * j) = (b : ℝ) ^ (L - L / 2 + 2 * j) := by rw [hWdef, hBdef, ← pow_add]
          rw [e1, e2]
          have h' : ((((b ^ (L + 2 * j) - b ^ (L - L / 2 + 2 * j) + 1)) ^ 2 : ℕ) : ℝ) ≤ T := by exact_mod_cast h
          have h'' := Real.sqrt_le_sqrt h'
          rw [Nat.cast_pow, Real.sqrt_sq (by positivity)] at h''
          push_cast [Nat.cast_sub hQQ] at h''
          linarith

end real

section realmain

variable {b : ℕ} [Fact b.Prime]

/-- **`lem:liftsep`**: let `P_L → P_{L+3} → ⋯` be lifts (a deep-shift chain from `P_L` with generator matrices `C₀`
and shift `σ₀`) whose depth parameters satisfy `D_{L+3j'} ≥ ⌊L/2⌋ + j'` for every `j' ≥ 0`. Then for every `j ≥ 0` the
toroidal minimum distance of `P_{L+3j}` (with its own shift) satisfies
`δ N^{1/3} ≥ min(g_L, b^{L/3} − W b^{-2L/3})`, `g_L = W √(v*_L) b^{-2L/3}`, `W = b^(L − ⌊L/2⌋)`: for any two
distinct indices `v, w` the toroidal distance of the points is at least `min(…) · N^{-1/3}`, `N = b^m`. -/
theorem liftsep {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)} {σ₀ : Fin 3 → Fin L → ZMod b}
    {D : ℕ → ℕ} (hD : ∀ ℓ, L ≤ ℓ → L / 2 + (ℓ - L) / 3 ≤ D ℓ) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b L C₀ σ₀ D m C σ) (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    min (gL b L (vstar b L C₀ σ₀)) (((b : ℝ) ^ L) ^ (1 / 3 : ℝ) - (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ))) *
        ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C σ v c : ℤ) -
        Z3NetF.digPointShift b m C σ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  have hb := (Fact.out : b.Prime).one_lt
  obtain ⟨j, hm, hT⟩ := liftsep_int hD h v w hvw
  have e := sqrt_torus (b ^ m) (pow_pos (by omega) m) (Z3NetF.digPointShift b m C σ v) (Z3NetF.digPointShift b m C σ w)
  push_cast at e
  rw [e]
  have := real_bound b L j _ _ hb hT
  rw [← hm] at this
  exact this

/-- **`lem:shiftcert`(a)**: under the hypothesis of `lem:liftsep`, for every `j ≥ 0` and every digital shift `τ` of
`P_{L+3j}` (depth `m`), `δ(P_{L+3j} ⊕ τ) N^{1/3} ≥ min(W √(v°_L) b^{-2L/3}, b^{L/3} − W b^{-2L/3})`. -/
theorem shiftcert_a {L : ℕ} {C₀ : Fin 3 → Matrix (Fin L) (Fin L) (ZMod b)} {σ₀ : Fin 3 → Fin L → ZMod b}
    {D : ℕ → ℕ} (hD : ∀ ℓ, L ≤ ℓ → L / 2 + (ℓ - L) / 3 ≤ D ℓ) {m : ℕ}
    {C : Fin 3 → Matrix (Fin m) (Fin m) (ZMod b)} {σ : Fin 3 → Fin m → ZMod b}
    (h : LiftChain b L C₀ σ₀ D m C σ) (τ : Fin 3 → Fin m → ZMod b) (v w : Fin m → ZMod b) (hvw : v ≠ w) :
    min (gL b L (vcirc b L C₀)) (((b : ℝ) ^ L) ^ (1 / 3 : ℝ) - (b : ℝ) ^ (L - L / 2) * ((b : ℝ) ^ L) ^ (-(2 / 3 : ℝ))) *
        ((b : ℝ) ^ m) ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (∑ c, ((Z3NetF.cres (b ^ m) ((Z3NetF.digPointShift b m C τ v c : ℤ) -
        Z3NetF.digPointShift b m C τ w c) : ℝ) / (b : ℝ) ^ m) ^ 2) := by
  have hb := (Fact.out : b.Prime).one_lt
  obtain ⟨j, hm, hT⟩ := shiftcert_a_int hD h τ v w hvw
  have e := sqrt_torus (b ^ m) (pow_pos (by omega) m) (Z3NetF.digPointShift b m C τ v) (Z3NetF.digPointShift b m C τ w)
  push_cast at e
  rw [e]
  have := real_bound b L j _ _ hb hT
  rw [← hm] at this
  exact this

end realmain

end Z3NetB23.Proofs

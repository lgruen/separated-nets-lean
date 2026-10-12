/-
Proof module (stage 11, entry main): `prop:cell`, `prop:rows` and `cor:rows` as compared
statements.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.Defs
public import Z3Net.Sep
public import Z3Net.TwoRows

@[expose] public section

/-!
# Stage 11 additions to entry main

Restatements (identical to the stage-11 block of `Challenge.lean`) of

* `cell_digits` — `prop:cell` (a), (b), (c), from `Sep.Dg_geo`, `Sep.Dg_jit`;
* `cell_layer` — the consequence `r ≡ M ℓ + J h (mod q)` and the independence of `f_c` from
  `n_c`, from `Sep.Dg_geo`, `Sep.Dg_jit`, `Sep.Ppoint_split`, `Sep.tail_eq`;
* `frame_rows` — `prop:rows`, from `Two.frameB_row0`, `Two.frameB_row1'`, `Two.frameC_row0`,
  `Two.frameC_row1'`, `Two.sum_mul_U0`;
* `Q_rows` — `cor:rows`, from `Two.QPhi_row0`, `Two.QPhi_row1`, `Two.QPhi_self_row`.
-/

namespace Z3Net

open Matrix

namespace S11

theorem ent_apply {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i : ℕ) (hi : i < a)
    (j : Fin b) : ent A i (j : ℕ) = A ⟨i, hi⟩ j := by
  simp [ent, hi, j.isLt]

theorem ent_row_ge {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i : ℕ) (hi : a ≤ i)
    (j : ℕ) : ent A i j = 0 := by
  unfold ent
  split_ifs with h
  · omega
  · rfl

theorem coeff_X_pow_mul_sub (k : ℕ) (l : Fin k) (F : PowerSeries ℤ) :
    PowerSeries.coeff (k - 1) (PowerSeries.X ^ (l : ℕ) * F) = PowerSeries.coeff (k - 1 - l) F := by
  have := l.isLt
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rfl
  · omega

end S11

/-- **Proposition `prop:cell`** (a), (b), (c) (`k ≥ 2`, every base `q ≥ 2`). Write
`d^c = (PGen k c mod q) *ᵥ v` for the digit vector of coordinate `c` of the point of `𝒫_{k,q}`
with index `v` (digit `0` most significant; the cell `n_c` is given by the digits `0, …, k-1`).
(a) + (c): for every coordinate `c` (indices mod 3, `x → y → z`; `c = x` is (a), `c = y, z` is
the cyclic shift (c)), `d^c_k = -d^c_{k-1} - d^{c+1}_{k-1} + d^{c+2}_{k-1} - d^{c+2}_{k-2}` (the
positions `k, k-1, k-2` are `i0, i1, i2`). (b) + (c): for `j > k`, `d^c_j` is a function of the
cells `(n_{c+1}, n_{c+2})` alone: two indices whose cells of the coordinates `c+1`, `c+2` agree
have the same digits `j > k` in coordinate `c`. -/
theorem cell_digits (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) :
    (∀ (v : Fin (3 * k) → ZMod q) (c : Fin 3) (i0 i1 i2 : Fin (3 * k)),
        (i0 : ℕ) = k → (i1 : ℕ) + 1 = k → (i2 : ℕ) + 2 = k →
        ((PGen k c).map (Int.cast : ℤ → ZMod q) *ᵥ v) i0 =
          -((PGen k c).map (Int.cast : ℤ → ZMod q) *ᵥ v) i1
            - ((PGen k (c + 1)).map (Int.cast : ℤ → ZMod q) *ᵥ v) i1
            + ((PGen k (c + 2)).map (Int.cast : ℤ → ZMod q) *ᵥ v) i1
            - ((PGen k (c + 2)).map (Int.cast : ℤ → ZMod q) *ᵥ v) i2) ∧
      (∀ (v w : Fin (3 * k) → ZMod q) (c : Fin 3),
        (∀ j : Fin (3 * k), (j : ℕ) < k →
          ((PGen k (c + 1)).map (Int.cast : ℤ → ZMod q) *ᵥ v) j =
            ((PGen k (c + 1)).map (Int.cast : ℤ → ZMod q) *ᵥ w) j) →
        (∀ j : Fin (3 * k), (j : ℕ) < k →
          ((PGen k (c + 2)).map (Int.cast : ℤ → ZMod q) *ᵥ v) j =
            ((PGen k (c + 2)).map (Int.cast : ℤ → ZMod q) *ᵥ w) j) →
        ∀ j : Fin (3 * k), k < (j : ℕ) →
          ((PGen k c).map (Int.cast : ℤ → ZMod q) *ᵥ v) j =
            ((PGen k c).map (Int.cast : ℤ → ZMod q) *ᵥ w) j) := by
  have : Fact (1 < q) := ⟨by omega⟩
  have b0 : k < 3 * k := by omega
  have b1 : k - 1 < 3 * k := by omega
  have b2 : k - 2 < 3 * k := by omega
  refine ⟨fun v c i0 i1 i2 h0 h1 h2 => ?_, fun v w c hy hz => Sep.Dg_jit k hk c v w hy hz⟩
  have e0 : i0 = ⟨k, b0⟩ := Fin.ext h0
  have e1 : i1 = ⟨k - 1, b1⟩ := Fin.ext (by simp; omega)
  have e2 : i2 = ⟨k - 2, b2⟩ := Fin.ext (by simp; omega)
  subst e0 e1 e2
  exact Sep.Dg_geo k hk c v

/-- **Proposition `prop:cell`, consequence** (`k ≥ 2`, `q ≥ 2`). With the geometric digit
`r_c = d^c_k` and the last two cell digits `ℓ_c = d^c_{k-1}`, `h_c = d^c_{k-2}` (in `ℤ/qℤ`, so
equality is congruence mod `q`): `r = M ℓ + J h` with `M = Mcell` and
`J = !![0,0,-1; -1,0,0; 0,-1,0]`. And the jitter `f_c = ∑_{j>k} (d^c_j mod q) q^(k-j)` does not
depend on `n_c`: `q^(2k-1) f_c` is the integer coordinate `X_c = Ppoint q k v c` modulo
`q^(2k-1)`, and it is the same for two indices whose cells of the coordinates `c+1`, `c+2` agree
(whatever their cells `n_c`). -/
theorem cell_layer (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) :
    (∀ (v : Fin (3 * k) → ZMod q) (i0 i1 i2 : Fin (3 * k)),
        (i0 : ℕ) = k → (i1 : ℕ) + 1 = k → (i2 : ℕ) + 2 = k →
        (fun c => ((PGen k c).map (Int.cast : ℤ → ZMod q) *ᵥ v) i0) =
          Mcell.map (Int.cast : ℤ → ZMod q) *ᵥ
              (fun c => ((PGen k c).map (Int.cast : ℤ → ZMod q) *ᵥ v) i1) +
            (!![0, 0, -1; -1, 0, 0; 0, -1, 0] : Matrix (Fin 3) (Fin 3) ℤ).map
                (Int.cast : ℤ → ZMod q) *ᵥ
              (fun c => ((PGen k c).map (Int.cast : ℤ → ZMod q) *ᵥ v) i2)) ∧
      (∀ (v w : Fin (3 * k) → ZMod q) (c : Fin 3),
        (∀ j : Fin (3 * k), (j : ℕ) < k →
          ((PGen k (c + 1)).map (Int.cast : ℤ → ZMod q) *ᵥ v) j =
            ((PGen k (c + 1)).map (Int.cast : ℤ → ZMod q) *ᵥ w) j) →
        (∀ j : Fin (3 * k), (j : ℕ) < k →
          ((PGen k (c + 2)).map (Int.cast : ℤ → ZMod q) *ᵥ v) j =
            ((PGen k (c + 2)).map (Int.cast : ℤ → ZMod q) *ᵥ w) j) →
        Ppoint q k v c % q ^ (2 * k - 1) = Ppoint q k w c % q ^ (2 * k - 1)) := by
  have : Fact (1 < q) := ⟨by omega⟩
  have : NeZero q := ⟨by omega⟩
  have b0 : k < 3 * k := by omega
  have b1 : k - 1 < 3 * k := by omega
  have b2 : k - 2 < 3 * k := by omega
  refine ⟨fun v i0 i1 i2 h0 h1 h2 => ?_, fun v w c hy hz => ?_⟩
  · have e0 : i0 = ⟨k, b0⟩ := Fin.ext h0
    have e1 : i1 = ⟨k - 1, b1⟩ := Fin.ext (by simp; omega)
    have e2 : i2 = ⟨k - 2, b2⟩ := Fin.ext (by simp; omega)
    subst e0 e1 e2
    have g0 := Sep.Dg_geo (R := ZMod q) k hk 0 v
    have g1 := Sep.Dg_geo (R := ZMod q) k hk 1 v
    have g2 := Sep.Dg_geo (R := ZMod q) k hk 2 v
    simp only [Sep.Dg] at g0 g1 g2
    funext c
    fin_cases c <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Mcell] at g0 g1 g2 ⊢
    · rw [g0]; ring
    · rw [g1]; ring
    · rw [g2]; ring
  · have hj := Sep.tail_eq v w c (Sep.Dg_jit k hk c v w hy hz)
    have hk1 : 1 ≤ k := by omega
    rw [Sep.Ppoint_split hk1 v c, Sep.Ppoint_split hk1 w c, hj]
    have e : ∀ a b F : ℕ, a * (q * q ^ (2 * k - 1)) + b * q ^ (2 * k - 1) + F =
        F + q ^ (2 * k - 1) * (a * q + b) := fun a b F => by ring
    rw [e, e, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]

/-- **Proposition `prop:rows`** (`k ≥ 2`), over `ℤ`. For a row `ρ` indexed by levels, the
reverse-level generating function is `ρ(x) = ∑_{l<k} ρ_l x^(k-1-l) mod x^k`, so `ρ(x) = F(x)`
means `ρ_l = [x^(k-1-l)] F` for every level `l < k`. With `β_r, γ_r` row `r` of `B = frameB k`,
`C = frameC k`, `β'_1 = β_1 + (k-1) β_0`, `γ'_1 = γ_1 + (k-1) γ_0`, and
`PowerSeries.mk 1 = (1-x)^(-1)`: `β_0(x) = (1-x)^(-k)`, `γ_0(x) = -(1-x)^(-k-1)`,
`β'_1(x) = -x (1-x)^(-k)`, `γ'_1(x) = (1-x)^(-k-2)`; after the column gauge `U_0 = U0 k`
(`(ρ U_0)_l = ∑_j ρ_j (U_0)_{jl}`) these four rows become `1 - x`, `-1`, `-x + x²`,
`(1-x)^(-1)`. -/
theorem frame_rows (k : ℕ) (hk : 2 ≤ k) (l : Fin k) :
    ent (frameB k) 0 l = PowerSeries.coeff (k - 1 - l) ((PowerSeries.mk 1 : PowerSeries ℤ) ^ k) ∧
      ent (frameC k) 0 l =
        -PowerSeries.coeff (k - 1 - l) ((PowerSeries.mk 1 : PowerSeries ℤ) ^ (k + 1)) ∧
      ent (frameB k) 1 l + ((k : ℤ) - 1) * ent (frameB k) 0 l =
        -PowerSeries.coeff (k - 1 - l) (PowerSeries.X * (PowerSeries.mk 1 : PowerSeries ℤ) ^ k) ∧
      ent (frameC k) 1 l + ((k : ℤ) - 1) * ent (frameC k) 0 l =
        PowerSeries.coeff (k - 1 - l) ((PowerSeries.mk 1 : PowerSeries ℤ) ^ (k + 2)) ∧
      ∑ j : Fin k, ent (frameB k) 0 j * U0 k j l =
        PowerSeries.coeff (k - 1 - l) (1 - PowerSeries.X : PowerSeries ℤ) ∧
      ∑ j : Fin k, ent (frameC k) 0 j * U0 k j l = PowerSeries.coeff (k - 1 - l) (-1 : PowerSeries ℤ) ∧
      ∑ j : Fin k, (ent (frameB k) 1 j + ((k : ℤ) - 1) * ent (frameB k) 0 j) * U0 k j l =
        PowerSeries.coeff (k - 1 - l) (-PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℤ) ∧
      ∑ j : Fin k, (ent (frameC k) 1 j + ((k : ℤ) - 1) * ent (frameC k) 0 j) * U0 k j l =
        PowerSeries.coeff (k - 1 - l) (PowerSeries.mk 1 : PowerSeries ℤ) := by
  have h0 : 0 < 2 * k := by omega
  have h1 : 1 < 2 * k := by omega
  -- the four rows as functions of the level
  have rB0 : ∀ j : Fin k, ent (frameB k) 0 j =
      PowerSeries.coeff (k - 1) (PowerSeries.X ^ (j : ℕ) * Two.E1 ^ k) := fun j => by
    rw [S11.ent_apply _ 0 h0, Two.frameB_row0 k hk]
  have rC0 : ∀ j : Fin k, ent (frameC k) 0 j =
      PowerSeries.coeff (k - 1) (PowerSeries.X ^ (j : ℕ) * -(Two.E1 ^ (k + 1))) := fun j => by
    rw [S11.ent_apply _ 0 h0, Two.frameC_row0 k hk]
  have rB1 : ∀ j : Fin k, ent (frameB k) 1 j + ((k : ℤ) - 1) * ent (frameB k) 0 j =
      PowerSeries.coeff (k - 1) (PowerSeries.X ^ (j : ℕ) * -(PowerSeries.X * Two.E1 ^ k)) :=
    fun j => by rw [S11.ent_apply _ 0 h0, S11.ent_apply _ 1 h1, Two.frameB_row1' k hk]
  have rC1 : ∀ j : Fin k, ent (frameC k) 1 j + ((k : ℤ) - 1) * ent (frameC k) 0 j =
      PowerSeries.coeff (k - 1) (PowerSeries.X ^ (j : ℕ) * Two.E1 ^ (k + 2)) :=
    fun j => by rw [S11.ent_apply _ 0 h0, S11.ent_apply _ 1 h1, Two.frameC_row1' k hk]
  have hE : (PowerSeries.mk 1 : PowerSeries ℤ) = Two.E1 := rfl
  have hk1 : 1 ≤ k := by omega
  have hEk : Two.E1 ^ k * (1 - PowerSeries.X : PowerSeries ℤ) ^ k = 1 :=
    Two.E1_pow_mul_one_sub_pow k
  have hE1 : Two.E1 * (1 - PowerSeries.X : PowerSeries ℤ) = 1 := Two.E1_mul_one_sub
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rB0, S11.coeff_X_pow_mul_sub, hE]
  · rw [rC0, S11.coeff_X_pow_mul_sub, hE, map_neg]
  · rw [rB1, S11.coeff_X_pow_mul_sub, hE, map_neg]
  · rw [rC1, S11.coeff_X_pow_mul_sub, hE]
  · simp_rw [rB0]
    rw [Two.sum_mul_U0 k hk1]
    congr 1
    rw [pow_succ, ← mul_assoc, hEk, one_mul]
  · simp_rw [rC0]
    rw [Two.sum_mul_U0 k hk1]
    congr 1
    rw [neg_mul, ← mul_pow, hE1, one_pow]
  · simp_rw [rB1]
    rw [Two.sum_mul_U0 k hk1]
    congr 1
    rw [pow_succ, show -(PowerSeries.X * Two.E1 ^ k) * ((1 - PowerSeries.X) ^ k * (1 - PowerSeries.X))
      = -(PowerSeries.X * (1 - PowerSeries.X)) * (Two.E1 ^ k * (1 - PowerSeries.X : PowerSeries ℤ) ^ k)
      by ring, hEk]
    ring
  · simp_rw [rC1]
    rw [Two.sum_mul_U0 k hk1, hE]
    congr 1
    rw [pow_succ Two.E1 (k + 1), mul_right_comm, ← mul_pow, hE1, one_pow, one_mul]

/-- **Corollary `cor:rows`** (`k ≥ 2`). Rows `0` and `1`, at level `l`, of the blocks
`Φ_cc = A_*`, `Φ_{c,c+1}`, `Φ_{c,c+2}` of the integer circulant graph form
`𝒬_k = QPhiOf k (frameB k) (frameC k)` of Definition `def:Q`: they vanish outside the levels
`k-1, k-2, k-3, k-4` (levels that do not exist for `k < 4` are dropped), where they are the table
of the paper (listed at the levels `(k-1, k-2, k-3, k-4)`): `Φ_cc`: row 0 `(-1,0,0,0)`, row 1
`0`; `Φ_{c,c+1}`: `(-1,-1,0,0)`, `(0,-1,-2,-2)`; `Φ_{c,c+2}`: `(-1,0,0,0)`, `(1,-1,2,-2)`.
All rows `r ≥ 1` of `Φ_cc` vanish. -/
theorem Q_rows (k : ℕ) (hk : 2 ≤ k) (c : Fin 3) (l : Fin k) :
    ent (QPhiOf k (frameB k) (frameC k) c c) 0 l = (if (l : ℕ) + 1 = k then -1 else 0) ∧
      (∀ r : ℕ, 1 ≤ r → ent (QPhiOf k (frameB k) (frameC k) c c) r l = 0) ∧
      ent (QPhiOf k (frameB k) (frameC k) c (c + 1)) 0 l =
        (if k ≤ (l : ℕ) + 2 then -1 else 0) ∧
      ent (QPhiOf k (frameB k) (frameC k) c (c + 1)) 1 l =
        (if (l : ℕ) + 2 = k then -1 else if (l : ℕ) + 3 = k ∨ (l : ℕ) + 4 = k then -2 else 0) ∧
      ent (QPhiOf k (frameB k) (frameC k) c (c + 2)) 0 l = (if (l : ℕ) + 1 = k then -1 else 0) ∧
      ent (QPhiOf k (frameB k) (frameC k) c (c + 2)) 1 l =
        (if (l : ℕ) + 1 = k then 1 else if (l : ℕ) + 2 = k then -1
          else if (l : ℕ) + 3 = k then 2 else if (l : ℕ) + 4 = k then -2 else 0) := by
  have h0 : 0 < 2 * k := by omega
  have h1 : 1 < 2 * k := by omega
  have hl := l.isLt
  have e1 : c + 1 - c = 1 := by abel
  have e2 : c + 2 - c = 2 := by abel
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [S11.ent_apply _ 0 h0, Two.QPhi_row0 k hk, sub_self, Two.tab0_zero, Two.tabC0]
    split_ifs <;> omega
  · by_cases hr' : r < 2 * k
    · rw [S11.ent_apply _ r hr', Two.QPhi_self_row k c _ (by simp; omega)]
    · exact S11.ent_row_ge _ r (by omega) _
  · rw [S11.ent_apply _ 0 h0, Two.QPhi_row0 k hk, e1, Two.tab0_one, Two.tabB0]
    split_ifs <;> omega
  · rw [S11.ent_apply _ 1 h1, Two.QPhi_row1 k hk, e1, Two.tab1_one, Two.tabB1]
    split_ifs <;> first | rfl | omega
  · rw [S11.ent_apply _ 0 h0, Two.QPhi_row0 k hk, e2, Two.tab0_two, Two.tabC0]
    split_ifs <;> omega
  · rw [S11.ent_apply _ 1 h1, Two.QPhi_row1 k hk, e2, Two.tab1_two, Two.tabC1]
    split_ifs <;> first | rfl | omega

end Z3Net

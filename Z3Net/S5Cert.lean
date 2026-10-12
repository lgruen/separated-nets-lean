/-
Proof module of entry S5R2 (`prop:s5r2`, `tab:s5r2`): the kernel-evaluable checks and their soundness.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.S5R2Defs

@[expose] public section

/-!
# Entry S5R2: the checks

* `chk D W`: the relaxation of the proof of `prop:s5r2`, enumerated exhaustively with two sound
  prunings: all `a_x = (a_{x_1}, a_{x_2})` with `0 ≤ a_{x_1} ≤ A`, `|a_{x_2}| ≤ A` (the case
  `a_{x_1} < 0` follows by the symmetry `(a, ξ) ↦ (-a, -ξ)`; `|a_{x_d}| > A ≥ M_p - 1`, `A² ≥ J_p²`
  already gives both bounds); a pair `a_x` whose own contribution gives both bounds is accepted; for
  the others all prefix patterns of `x` (sign-consistent by construction, `patsOf`), the `x`-part
  `b_i` of the congruence of `a_{z_i}`, and if some `|cen b_i| ≥ T + B_i` (`B_i` bounds the
  contribution of the `z`-patterns, `T ≥ M_p`, `(T - 1)² ≥ J_p²`) the case is accepted, since then
  `|a_{z_i}| ≥ T`; otherwise all patterns of the `z_i` and the centred `a_{z_i}`. Every consistent
  nonzero solution must have `|a|_∞ ≥ M_p` and `∑ (|a_c| - 1)₊² ≥ J_p²`. `chk_sound`: then every
  nonzero solution of `S5Rel` does.
* `latchk D`: every nonzero `u_x` with `|u_x|_∞ < λ_∞` has `max(|u_x|_∞, |cen(κ u_x)|_∞) ≥ λ_∞`;
  `latchk_sound`.
* `wchk D W`: the frame-orbit conditions of the reachability proof, as integer congruences modulo
  `p`: the paper's places are distinct, `P_c (b_c - b_1) ≡ 1` (`P` the Möbius places), the `P_c`
  (`c ≠ x_1`) distinct, row scalars `lam`, column gauges `U0` (column `x_1`, at `∞`), `U1` (column
  `x_2`), `Uz j` (column `z_j`); `smallOK D W`: `wchk`, the attaining relaxation solutions and lattice
  vector, `latchk`, the side conditions of `chk_sound`, and the integer forms of the printed values
  of `tab:s5r2`.
-/

namespace Z3NetF.Proofs.S5

open Finset

/-- Witness data of a design (see `Z3Net/S5Wit.lean`). -/
structure Wit where
  P : Fin 5 → ℤ
  lam : Fin 3 → ℤ
  U0 : Fin 3 → Fin 3 → ℤ
  U1 : Fin 3 → Fin 3 → ℤ
  Uz : Fin 3 → Fin 2 → Fin 2 → ℤ
  T : ℕ
  A : ℕ
  B : Fin 3 → ℤ
  aM : Fin 5 → ℤ
  ξ1M : Fin 5 → ℤ
  ξ2M : Fin 5 → ℤ
  aJ : Fin 5 → ℤ
  ξ1J : Fin 5 → ℤ
  ξ2J : Fin 5 → ℤ
  u : Fin 5 → ℤ

/-- Centred residue modulo `p` (representative in `(-p/2, p/2]`). -/
def cen (p : ℕ) (v : ℤ) : ℤ := if 2 * (v % (p : ℤ)) < p then v % (p : ℤ) else v % (p : ℤ) - p

/-- Sign-consistent prefix pattern `(ξ1, ξ2) ∈ {(0,0), (σ,0), (σ,σ)}`, `σ = sgn a`. -/
def patOK (a x1 x2 : ℤ) : Bool :=
  (x1 == 0 || x1 == a.sign) && (x2 == 0 || x2 == a.sign) && (x2 == 0 || x1 != 0)

/-- All five prefix patterns. -/
def pats5 : List (ℤ × ℤ) := [(0, 0), (1, 0), (1, 1), (-1, 0), (-1, -1)]

/-- The prefix patterns of a coordinate of sign `sgn a`. -/
def patsOf (a : ℤ) : List (ℤ × ℤ) := [(0, 0), (a.sign, 0), (a.sign, a.sign)]

/-- The `x`-part of the congruence of `a_{z_i}`. -/
def baseX (D : S5Design) (i : Fin 3) (a0 a1 : ℤ) (x0 x1 : ℤ × ℤ) : ℤ :=
  D.κ i 0 * a0 + D.β i 0 * x0.1 + D.η i 0 * x0.2 + (D.κ i 1 * a1 + D.β i 1 * x1.1 + D.η i 1 * x1.2)

/-- Contribution of `z_j` to the congruence of `a_{z_i}`. -/
def zt (D : S5Design) (i j : Fin 3) (z1 z2 : ℤ) : ℤ :=
  if j = i then D.o i * z1 else D.g i j * z1 + D.H i j * z2

/-- The `z`-part of the congruence of `a_{z_i}`. -/
def zoff (D : S5Design) (i : Fin 3) (z0 z1 z2 : ℤ × ℤ) : ℤ :=
  zt D i 0 z0.1 z0.2 + zt D i 1 z1.1 z1.2 + zt D i 2 z2.1 z2.2

/-- A bound for the `z`-part (`|zoff| ≤ bz` for patterns with entries in `{-1, 0, 1}`). -/
def bz (D : S5Design) (i : Fin 3) : ℤ :=
  ∑ j : Fin 3, (if j = i then |D.o i| else |D.g i j| + |D.H i j|)

/-- One fully enumerated case. -/
def caseOK (D : S5Design) (a0 a1 b0 b1 b2 : ℤ) (z0 z1 z2 : ℤ × ℤ) : Bool :=
  let c0 := cen D.p (b0 + zoff D 0 z0 z1 z2)
  let c1 := cen D.p (b1 + zoff D 1 z0 z1 z2)
  let c2 := cen D.p (b2 + zoff D 2 z0 z1 z2)
  !(patOK c0 z0.1 z0.2 && patOK c1 z1.1 z1.2 && patOK c2 z2.1 z2.2) ||
    (a0 == 0 && a1 == 0 && c0 == 0 && c1 == 0 && c2 == 0) ||
    (decide ((D.M : ℤ) ≤ max (max (max |a0| |a1|) (max |c0| |c1|)) |c2|) &&
      decide (D.J2 ≤ (a0.natAbs - 1) ^ 2 + (a1.natAbs - 1) ^ 2 + (c0.natAbs - 1) ^ 2 +
        (c1.natAbs - 1) ^ 2 + (c2.natAbs - 1) ^ 2))

/-- The cases of one `a_x` and one pattern of `x`, with the pruning on the `x`-part. -/
def xpatOK (D : S5Design) (W : Wit) (a0 a1 b0 b1 b2 : ℤ) : Bool :=
  decide ((W.T : ℤ) + W.B 0 ≤ |cen D.p b0|) || decide ((W.T : ℤ) + W.B 1 ≤ |cen D.p b1|) ||
    decide ((W.T : ℤ) + W.B 2 ≤ |cen D.p b2|) ||
    pats5.all fun z0 => pats5.all fun z1 => pats5.all fun z2 => caseOK D a0 a1 b0 b1 b2 z0 z1 z2

/-- All cases of one `a_x`. -/
def axOK (D : S5Design) (W : Wit) (a0 a1 : ℤ) : Bool :=
  (decide (D.J2 ≤ (a0.natAbs - 1) ^ 2 + (a1.natAbs - 1) ^ 2) &&
      decide ((D.M : ℤ) ≤ max |a0| |a1|)) ||
    (patsOf a0).all fun x0 => (patsOf a1).all fun x1 =>
      xpatOK D W a0 a1 (baseX D 0 a0 a1 x0 x1) (baseX D 1 a0 a1 x0 x1) (baseX D 2 a0 a1 x0 x1)

/-- The relaxation certificate. -/
def chk (D : S5Design) (W : Wit) : Bool :=
  (List.range (W.A + 1)).all fun n0 => (List.range (2 * W.A + 1)).all fun n1 =>
    axOK D W (n0 : ℤ) ((n1 : ℤ) - W.A)

/-- The lattice certificate. -/
def latchk (D : S5Design) : Bool :=
  (List.range D.lat).all fun n0 => (List.range (2 * D.lat - 1)).all fun n1 =>
    let a0 : ℤ := n0
    let a1 : ℤ := (n1 : ℤ) - ((D.lat : ℤ) - 1)
    (a0 == 0 && a1 == 0) ||
      decide ((D.lat : ℤ) ≤ max (max |a0| |a1|) (max (max |cen D.p (D.κ 0 0 * a0 + D.κ 0 1 * a1)|
        |cen D.p (D.κ 1 0 * a0 + D.κ 1 1 * a1)|) |cen D.p (D.κ 2 0 * a0 + D.κ 2 1 * a1)|))

/-- `F_n` on the full column `x_{d+1}` (`x`-index `n`): `κ, β, η`. -/
def fxZ (D : S5Design) (n : Fin 3) (i : Fin 3) (d : Fin 2) : ℤ := ![D.κ i d, D.β i d, D.η i d] n

/-- `F_n` on the column `z_j` (`x`-index `n`): `g, H`. -/
def fzZ (D : S5Design) (n : Fin 2) (i j : Fin 3) : ℤ := ![D.g i j, D.H i j] n

/-- The frame-orbit conditions, modulo `p`. -/
def wchk (D : S5Design) (W : Wit) : Bool :=
  let p : ℤ := D.p
  (List.finRange 5).all (fun c => (List.finRange 5).all fun d =>
    c == d || ((D.pl c : ℤ) - D.pl d) % p != 0) &&
  (List.finRange 5).all (fun c => c == 0 || (((D.pl c : ℤ) - D.pl 0) * W.P c - 1) % p == 0) &&
  (List.finRange 5).all (fun c => (List.finRange 5).all fun d =>
    c == 0 || d == 0 || c == d || (W.P c - W.P d) % p != 0) &&
  (List.finRange 3).all (fun i => W.lam i % p != 0) &&
  (List.finRange 3).all (fun n => W.U0 n n % p != 0 && W.U1 n n % p != 0) &&
  (List.finRange 3).all (fun j => (List.finRange 2).all fun n => W.Uz j n n % p != 0) &&
  (List.finRange 3).all (fun i => (List.finRange 3).all fun n =>
    (fxZ D n i 0 - W.lam i * ∑ n' ∈ univ.filter (fun n' : Fin 3 => n' ≤ n),
      W.P (s5z i) ^ (n' : ℕ) * W.U0 n' n) % p == 0) &&
  (List.finRange 3).all (fun i => (List.finRange 3).all fun n =>
    (fxZ D n i 1 * (W.P (s5z i) - W.P 1) ^ ((n : ℕ) + 1) - W.lam i *
      ∑ n' ∈ univ.filter (fun n' : Fin 3 => n' ≤ n),
        (W.P (s5z i) - W.P 1) ^ ((n : ℕ) - (n' : ℕ)) * W.U1 n' n) % p == 0) &&
  (List.finRange 3).all (fun i => (List.finRange 3).all fun j => i == j ||
    (List.finRange 2).all fun n =>
      (fzZ D n i j * (W.P (s5z i) - W.P (s5z j)) ^ ((n : ℕ) + 1) - W.lam i *
        ∑ n' ∈ univ.filter (fun n' : Fin 2 => n' ≤ n),
          (W.P (s5z i) - W.P (s5z j)) ^ ((n : ℕ) - (n' : ℕ)) * W.Uz j n' n) % p == 0)

/-- The relaxation, as a Boolean (for the attaining witnesses). -/
def relB (D : S5Design) (a ξ1 ξ2 : Fin 5 → ℤ) : Bool :=
  (List.finRange 5).all (fun c => decide (2 * |a c| < D.p) && patOK (a c) (ξ1 c) (ξ2 c)) &&
  (List.finRange 3).all fun i =>
    (a (s5z i) - (baseX D i (a 0) (a 1) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1) +
      zoff D i (ξ1 2, ξ2 2) (ξ1 3, ξ2 3) (ξ1 4, ξ2 4))) % (D.p : ℤ) == 0

/-- The lattice `Λ_κ`, as a Boolean. -/
def latB (D : S5Design) (u : Fin 5 → ℤ) : Bool :=
  (List.finRange 3).all fun i => (u (s5z i) - (D.κ i 0 * u 0 + D.κ i 1 * u 1)) % (D.p : ℤ) == 0

/-- All cheap checks of a design. -/
def smallOK (D : S5Design) (W : Wit) : Bool :=
  wchk D W && relB D W.aM W.ξ1M W.ξ2M && decide (W.aM ≠ 0) && decide (s5MaxAbs W.aM = D.M) &&
    relB D W.aJ W.ξ1J W.ξ2J && decide (W.aJ ≠ 0) && decide (jitNorm2 W.aJ = D.J2) &&
    latB D W.u && decide (W.u ≠ 0) && decide (s5MaxAbs W.u = D.lat) && latchk D &&
    decide (0 < D.p) && decide (D.p % 2 = 1) && decide (1 ≤ D.lat) &&
    decide (2 * D.lat ≤ D.p + 1) && decide (2 * D.M ≤ D.p + 1) && decide (4 * D.J2 ≤ (D.p - 1) ^ 2) &&
    decide ((D.M : ℤ) ≤ W.T) && decide (D.J2 ≤ (W.T - 1) ^ 2) && decide (1 ≤ W.T) &&
    decide (D.M ≤ W.A + 1) && decide (D.J2 ≤ W.A ^ 2) &&
    decide (bz D 0 ≤ W.B 0) && decide (bz D 1 ≤ W.B 1) && decide (bz D 2 ≤ W.B 2) &&
    decide (D.tabM ^ 5 * D.p ^ 3 ≤ (D.M - 1) ^ 5 * 10 ^ 15) &&
    decide ((D.M - 1) ^ 5 * 10 ^ 15 < (D.tabM + 1) ^ 5 * D.p ^ 3) &&
    decide (D.tabJ ^ 10 * D.p ^ 6 ≤ D.J2 ^ 5 * 10 ^ 30) &&
    decide (D.J2 ^ 5 * 10 ^ 30 < (D.tabJ + 1) ^ 10 * D.p ^ 6) &&
    decide (D.pig ^ 5 ≤ D.p ^ 3) && decide (D.p ^ 3 < (D.pig + 1) ^ 5) && decide (D.lat ≤ D.pig) &&
    decide (2 ≤ D.M) && decide (1 ≤ D.J2)

/-! ## Soundness -/

lemma cen_eq (p : ℕ) (hp : 0 < p) (a v : ℤ) (ha : 2 * |a| < p) (hd : (p : ℤ) ∣ a - v) :
    cen p v = a := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hmod : v % (p : ℤ) = a % (p : ℤ) := (Int.modEq_iff_dvd.mpr hd).eq
  unfold cen
  rw [hmod]
  rcases abs_cases a with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at ha
    rw [Int.emod_eq_of_lt h2 (by omega), if_pos (by omega)]
  · rw [h1] at ha
    have e : a % (p : ℤ) = a + p := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [e, if_neg (by omega)]
    ring

lemma cen_zero (p : ℕ) : cen p 0 = 0 := by
  unfold cen; simp

/-- The centred residue is the least absolute value in its class. -/
lemma cen_abs_le (p : ℕ) (hp : 0 < p) (b y : ℤ) (hd : (p : ℤ) ∣ y - b) : |cen p b| ≤ |y| := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hmod : b % (p : ℤ) = y % (p : ℤ) := (Int.modEq_iff_dvd.mpr hd).eq
  have hr0 := Int.emod_nonneg y hp'.ne'
  have hr1 := Int.emod_lt_of_pos y hp'
  have hy := Int.mul_ediv_add_emod y (p : ℤ)
  set r := y % (p : ℤ)
  set q := y / (p : ℤ)
  have hq : 0 ≤ (p : ℤ) * q ∨ (p : ℤ) * q ≤ -p := by
    rcases le_or_gt 0 q with h | h
    · exact Or.inl (mul_nonneg hp'.le h)
    · right; nlinarith
  unfold cen
  rw [hmod]
  split_ifs with h
  · rw [abs_of_nonneg hr0]
    rcases hq with hq | hq
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_neg (by omega)]; omega
  · rw [abs_of_neg (by omega)]
    rcases hq with hq | hq
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_neg (by omega)]; omega

lemma patOK_iff (a x1 x2 : ℤ) : patOK a x1 x2 = true ↔
    (x1 = 0 ∨ x1 = a.sign) ∧ (x2 = 0 ∨ x2 = a.sign) ∧ (x2 ≠ 0 → x1 ≠ 0) := by
  simp only [patOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  tauto

lemma sign_cases' (a : ℤ) : a.sign = -1 ∧ a < 0 ∨ a.sign = 0 ∧ a = 0 ∨ a.sign = 1 ∧ 0 < a := by
  rcases lt_trichotomy a 0 with h | h | h
  · exact Or.inl ⟨Int.sign_eq_neg_one_of_neg h, h⟩
  · exact Or.inr (Or.inl ⟨by simp [h], h⟩)
  · exact Or.inr (Or.inr ⟨Int.sign_eq_one_of_pos h, h⟩)

lemma mem_pats5 (a x1 x2 : ℤ) (h1 : x1 = 0 ∨ x1 = a.sign) (h2 : x2 = 0 ∨ x2 = a.sign)
    (h3 : x2 ≠ 0 → x1 ≠ 0) : (x1, x2) ∈ pats5 := by
  have hs := sign_cases' a
  simp only [pats5, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

lemma mem_patsOf (a x1 x2 : ℤ) (h1 : x1 = 0 ∨ x1 = a.sign) (h2 : x2 = 0 ∨ x2 = a.sign)
    (h3 : x2 ≠ 0 → x1 ≠ 0) : (x1, x2) ∈ patsOf a := by
  simp only [patsOf, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · by_cases hs : a.sign = 0
    · exact Or.inl ⟨h1, h2.trans hs⟩
    · exact absurd h1 (h3 (h2 ▸ hs))
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h1, h2⟩)

lemma le_maxAbs (u : Fin 5 → ℤ) (c : Fin 5) : |u c| ≤ s5MaxAbs u := by
  unfold s5MaxAbs
  fin_cases c <;> simp

lemma maxAbs_neg (u : Fin 5 → ℤ) : s5MaxAbs (-u) = s5MaxAbs u := by
  simp [s5MaxAbs, abs_neg]

lemma jit_neg (u : Fin 5 → ℤ) : jitNorm2 (-u) = jitNorm2 u := by
  simp [jitNorm2]

lemma jit_eq (u : Fin 5 → ℤ) : jitNorm2 u = ((u 0).natAbs - 1) ^ 2 + ((u 1).natAbs - 1) ^ 2 +
    ((u 2).natAbs - 1) ^ 2 + ((u 3).natAbs - 1) ^ 2 + ((u 4).natAbs - 1) ^ 2 := by
  simp [jitNorm2, Fin.sum_univ_five]

lemma jit_ge (u : Fin 5 → ℤ) (c : Fin 5) : ((u c).natAbs - 1) ^ 2 ≤ jitNorm2 u :=
  Finset.single_le_sum (f := fun c => ((u c).natAbs - 1) ^ 2) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ c)

lemma s5z_val (i : Fin 3) : ((s5z i : Fin 5) : ℕ) = (i : ℕ) + 2 := by simp [s5z]

lemma s5x_val (d : Fin 2) : ((s5x d : Fin 5) : ℕ) = (d : ℕ) := by simp [s5x]

@[simp] lemma s5x_zero : s5x 0 = 0 := rfl
@[simp] lemma s5x_one : s5x 1 = 1 := rfl
@[simp] lemma s5z_zero : s5z 0 = 2 := rfl
@[simp] lemma s5z_one : s5z 1 = 3 := rfl
@[simp] lemma s5z_two : s5z 2 = 4 := rfl

lemma rhs_eq (D : S5Design) (a ξ1 ξ2 : Fin 5 → ℤ) (i : Fin 3) :
    baseX D i (a 0) (a 1) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1) + zoff D i (ξ1 2, ξ2 2) (ξ1 3, ξ2 3) (ξ1 4, ξ2 4) =
      ∑ d : Fin 2, (D.κ i d * a (s5x d) + D.β i d * ξ1 (s5x d) + D.η i d * ξ2 (s5x d)) +
        ∑ j : Fin 3, (if j = i then D.o i * ξ1 (s5z j)
          else D.g i j * ξ1 (s5z j) + D.H i j * ξ2 (s5z j)) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  simp only [baseX, zoff, zt, s5x_zero, s5x_one, s5z_zero, s5z_one, s5z_two]

lemma rel_neg (D : S5Design) (a ξ1 ξ2 : Fin 5 → ℤ) (h : S5Rel D a ξ1 ξ2) :
    S5Rel D (-a) (-ξ1) (-ξ2) := by
  obtain ⟨hA, hP, hE⟩ := h
  refine ⟨fun c => by simpa [abs_neg] using hA c, fun c => ?_, fun i => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hP c
    simp only [Pi.neg_apply, Int.sign_neg, neg_eq_zero, neg_inj, ne_eq]
    exact ⟨h1, h2, h3⟩
  · have key : ∀ j : Fin 3, (if j = i then D.o i * (-ξ1) (s5z j)
        else D.g i j * (-ξ1) (s5z j) + D.H i j * (-ξ2) (s5z j)) =
        -(if j = i then D.o i * ξ1 (s5z j) else D.g i j * ξ1 (s5z j) + D.H i j * ξ2 (s5z j)) := by
      intro j; simp only [Pi.neg_apply]; split_ifs <;> ring
    have keyx : ∀ d : Fin 2, D.κ i d * (-a) (s5x d) + D.β i d * (-ξ1) (s5x d) +
        D.η i d * (-ξ2) (s5x d) = -(D.κ i d * a (s5x d) + D.β i d * ξ1 (s5x d) +
          D.η i d * ξ2 (s5x d)) := by
      intro d; simp only [Pi.neg_apply]; ring
    simp only [key, keyx, Finset.sum_neg_distrib]
    have := (hE i).neg_right
    convert this using 1
    simp only [Pi.neg_apply]
    ring

/-- The `z`-part is bounded by `bz`. -/
lemma zoff_le (D : S5Design) (i : Fin 3) (ξ1 ξ2 : Fin 5 → ℤ) (h1 : ∀ c, |ξ1 c| ≤ 1)
    (h2 : ∀ c, |ξ2 c| ≤ 1) :
    |zoff D i (ξ1 2, ξ2 2) (ξ1 3, ξ2 3) (ξ1 4, ξ2 4)| ≤ bz D i := by
  have ht : ∀ j : Fin 3, ∀ z1 z2 : ℤ, |z1| ≤ 1 → |z2| ≤ 1 →
      |zt D i j z1 z2| ≤ (if j = i then |D.o i| else |D.g i j| + |D.H i j|) := by
    intro j z1 z2 hz1 hz2
    have m1 : ∀ x y : ℤ, |y| ≤ 1 → |x * y| ≤ |x| := fun x y hy => by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg x) hy
    unfold zt
    split_ifs
    · exact m1 _ _ hz1
    · exact (abs_add_le _ _).trans (add_le_add (m1 _ _ hz1) (m1 _ _ hz2))
  unfold zoff bz
  rw [Fin.sum_univ_three]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    (ht 0 _ _ (h1 2) (h2 2)) (ht 1 _ _ (h1 3) (h2 3)))) (ht 2 _ _ (h1 4) (h2 4)))

lemma abs_pat_le (a x1 x2 : ℤ) (h1 : x1 = 0 ∨ x1 = a.sign) (h2 : x2 = 0 ∨ x2 = a.sign) :
    |x1| ≤ 1 ∧ |x2| ≤ 1 := by
  have hs := sign_cases' a
  constructor
  · rcases h1 with h | h <;> rw [h] <;> rcases hs with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> simp [h']
  · rcases h2 with h | h <;> rw [h] <;> rcases hs with ⟨h', _⟩ | ⟨h', _⟩ | ⟨h', _⟩ <;> simp [h']

/-- Side conditions of `chk_sound`. -/
structure ChkSide (D : S5Design) (W : Wit) : Prop where
  p0 : 0 < D.p
  T1 : (D.M : ℤ) ≤ W.T
  T2 : D.J2 ≤ (W.T - 1) ^ 2
  T0 : 1 ≤ W.T
  A1 : D.M ≤ W.A + 1
  A2 : D.J2 ≤ W.A ^ 2
  B : ∀ i, bz D i ≤ W.B i

/-- A single coordinate of absolute value at least `T` gives both bounds. -/
lemma good_of_T (D : S5Design) (W : Wit) (hs : ChkSide D W) (a : Fin 5 → ℤ) (c : Fin 5)
    (h : (W.T : ℤ) ≤ |a c|) : (D.M : ℤ) ≤ s5MaxAbs a ∧ D.J2 ≤ jitNorm2 a := by
  refine ⟨hs.T1.trans (h.trans (le_maxAbs a c)), ?_⟩
  have h' : W.T ≤ (a c).natAbs := by
    have : ((W.T : ℕ) : ℤ) ≤ ((a c).natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact h
    exact_mod_cast this
  have : (W.T - 1) ^ 2 ≤ ((a c).natAbs - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact hs.T2.trans (this.trans (jit_ge a c))

/-- A coordinate of absolute value larger than `A` gives both bounds. -/
lemma good_of_A (D : S5Design) (W : Wit) (hs : ChkSide D W) (a : Fin 5 → ℤ) (c : Fin 5)
    (h : (W.A : ℤ) < |a c|) : (D.M : ℤ) ≤ s5MaxAbs a ∧ D.J2 ≤ jitNorm2 a := by
  have h' : W.A + 1 ≤ (a c).natAbs := by
    have : ((W.A : ℕ) : ℤ) < ((a c).natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact h
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · have hA1 : (D.M : ℤ) ≤ W.A + 1 := by exact_mod_cast hs.A1
    exact (hA1.trans (by omega)).trans (le_maxAbs a c)
  · have : W.A ^ 2 ≤ ((a c).natAbs - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact hs.A2.trans (this.trans (jit_ge a c))

/-- `chk` bounds every nonzero relaxation solution with `a_{x_1} ≥ 0`. -/
lemma chk_sound_pos (D : S5Design) (W : Wit) (hs : ChkSide D W) (h : chk D W = true)
    (a ξ1 ξ2 : Fin 5 → ℤ) (hR : S5Rel D a ξ1 ξ2) (ha : a ≠ 0) (h0 : 0 ≤ a 0) :
    (D.M : ℤ) ≤ s5MaxAbs a ∧ D.J2 ≤ jitNorm2 a := by
  obtain ⟨hA, hP, hE⟩ := hR
  by_cases hbig : (W.A : ℤ) < |a 0| ∨ (W.A : ℤ) < |a 1|
  · rcases hbig with hb | hb
    · exact good_of_A D W hs a 0 hb
    · exact good_of_A D W hs a 1 hb
  push Not at hbig
  obtain ⟨hb0, hb1⟩ := hbig
  set n0 := (a 0).toNat with hn0def
  have hn0 : (n0 : ℤ) = a 0 := Int.toNat_of_nonneg h0
  set n1 := (a 1 + W.A).toNat with hn1def
  have hn1 : (n1 : ℤ) - W.A = a 1 := by
    rw [hn1def, Int.toNat_of_nonneg (by have := neg_abs_le (a 1); omega)]; ring
  have hn0r : n0 ∈ List.range (W.A + 1) := by
    rw [List.mem_range]; rw [abs_of_nonneg h0] at hb0; omega
  have hn1r : n1 ∈ List.range (2 * W.A + 1) := by
    rw [List.mem_range]
    have := le_abs_self (a 1); have := neg_abs_le (a 1)
    omega
  have hax : axOK D W (a 0) (a 1) = true := by
    simp only [chk, List.all_eq_true] at h
    have := h n0 hn0r n1 hn1r
    rwa [hn0, hn1] at this
  have hpat : ∀ c, patOK (a c) (ξ1 c) (ξ2 c) = true := fun c => (patOK_iff _ _ _).mpr (hP c)
  have hξ : ∀ c, |ξ1 c| ≤ 1 ∧ |ξ2 c| ≤ 1 := fun c => abs_pat_le (a c) _ _ (hP c).1 (hP c).2.1
  simp only [axOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hax
  rcases hax with ⟨hj, hm⟩ | hax
  · refine ⟨hm.trans ?_, ?_⟩
    · exact max_le (le_maxAbs a 0) (le_maxAbs a 1)
    · rw [jit_eq]; omega
  have hx := hax _ (mem_patsOf (a 0) _ _ (hP 0).1 (hP 0).2.1 (hP 0).2.2) _
    (mem_patsOf (a 1) _ _ (hP 1).1 (hP 1).2.1 (hP 1).2.2)
  -- the congruences in the form of the check
  have hE' : ∀ i : Fin 3, (D.p : ℤ) ∣ a (s5z i) - (baseX D i (a 0) (a 1) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1) +
      zoff D i (ξ1 2, ξ2 2) (ξ1 3, ξ2 3) (ξ1 4, ξ2 4)) := fun i => by rw [rhs_eq]; exact hE i
  simp only [xpatOK, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at hx
  -- pruning: some `|cen b_i| ≥ T + B_i`
  have prune : ∀ i : Fin 3, (W.T : ℤ) + W.B i ≤
      |cen D.p (baseX D i (a 0) (a 1) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1))| →
      (D.M : ℤ) ≤ s5MaxAbs a ∧ D.J2 ≤ jitNorm2 a := by
    intro i hi
    apply good_of_T D W hs a (s5z i)
    have hz := zoff_le D i ξ1 ξ2 (fun c => (hξ c).1) (fun c => (hξ c).2)
    have hd : (D.p : ℤ) ∣ (a (s5z i) - zoff D i (ξ1 2, ξ2 2) (ξ1 3, ξ2 3) (ξ1 4, ξ2 4)) -
        baseX D i (a 0) (a 1) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1) := by
      have := hE' i; convert this using 1; ring
    have hc := cen_abs_le D.p hs.p0 _ _ hd
    have h3 := abs_sub (a (s5z i)) (zoff D i (ξ1 2, ξ2 2) (ξ1 3, ξ2 3) (ξ1 4, ξ2 4))
    linarith [hs.B i]
  rcases hx with ((hx | hx) | hx) | hx
  · exact prune 0 hx
  · exact prune 1 hx
  · exact prune 2 hx
  have hc := hx _ (mem_pats5 (a 2) _ _ (hP 2).1 (hP 2).2.1 (hP 2).2.2) _
    (mem_pats5 (a 3) _ _ (hP 3).1 (hP 3).2.1 (hP 3).2.2) _
    (mem_pats5 (a 4) _ _ (hP 4).1 (hP 4).2.1 (hP 4).2.2)
  have hb : ∀ i : Fin 3, cen D.p (baseX D i (a 0) (a 1) (ξ1 0, ξ2 0) (ξ1 1, ξ2 1) +
      zoff D i (ξ1 2, ξ2 2) (ξ1 3, ξ2 3) (ξ1 4, ξ2 4)) = a (s5z i) := fun i =>
    cen_eq D.p hs.p0 _ _ (hA _) (hE' i)
  simp only [caseOK, hb 0, hb 1, hb 2, s5z_zero, s5z_one, s5z_two, hpat 2, hpat 3, hpat 4] at hc
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨h0', h1⟩, h2⟩, h3⟩, h4⟩ | ⟨hm, hj⟩
  · exfalso; apply ha
    funext c; fin_cases c
    · exact h0'
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · refine ⟨hm.trans_eq ?_, ?_⟩
    · simp [s5MaxAbs]
    · rw [jit_eq]; exact hj

/-- **Soundness of `chk`**: every nonzero solution of the relaxation has `|a|_∞ ≥ M_p` and
`∑ (|a_c| - 1)₊² ≥ J_p²`. -/
theorem chk_sound (D : S5Design) (W : Wit) (hs : ChkSide D W) (h : chk D W = true)
    (a ξ1 ξ2 : Fin 5 → ℤ) (hR : S5Rel D a ξ1 ξ2) (ha : a ≠ 0) :
    (D.M : ℤ) ≤ s5MaxAbs a ∧ D.J2 ≤ jitNorm2 a := by
  rcases le_or_gt 0 (a 0) with h0 | h0
  · exact chk_sound_pos D W hs h a ξ1 ξ2 hR ha h0
  · have := chk_sound_pos D W hs h (-a) (-ξ1) (-ξ2) (rel_neg D a ξ1 ξ2 hR) (neg_ne_zero.mpr ha)
      (by simp only [Pi.neg_apply]; omega)
    rwa [maxAbs_neg, jit_neg] at this

lemma lat_neg (D : S5Design) (u : Fin 5 → ℤ)
    (h : ∀ i : Fin 3, (D.p : ℤ) ∣ u (s5z i) - ∑ d : Fin 2, D.κ i d * u (s5x d)) :
    ∀ i : Fin 3, (D.p : ℤ) ∣ (-u) (s5z i) - ∑ d : Fin 2, D.κ i d * (-u) (s5x d) := by
  intro i
  have := (h i).neg_right
  convert this using 1
  simp only [Pi.neg_apply, Fin.sum_univ_two]; ring

lemma latchk_sound_pos (D : S5Design) (hp : 0 < D.p) (h : latchk D = true) (hl : 1 ≤ D.lat)
    (u : Fin 5 → ℤ) (hu : u ≠ 0)
    (hL : ∀ i : Fin 3, (D.p : ℤ) ∣ u (s5z i) - ∑ d : Fin 2, D.κ i d * u (s5x d))
    (hs : ∀ c, 2 * |u c| < D.p) (h0 : 0 ≤ u 0) : (D.lat : ℤ) ≤ s5MaxAbs u := by
  by_cases hbig : (D.lat : ℤ) ≤ |u 0| ∨ (D.lat : ℤ) ≤ |u 1|
  · rcases hbig with hb | hb
    · exact hb.trans (le_maxAbs u 0)
    · exact hb.trans (le_maxAbs u 1)
  push Not at hbig
  obtain ⟨hb0, hb1⟩ := hbig
  have hb : ∀ i : Fin 3, cen D.p (D.κ i 0 * u 0 + D.κ i 1 * u 1) = u (s5z i) := fun i => by
    apply cen_eq D.p hp _ _ (hs _)
    have := hL i
    simpa [Fin.sum_univ_two] using this
  set n0 := (u 0).toNat with hn0def
  have hn0 : (n0 : ℤ) = u 0 := Int.toNat_of_nonneg h0
  set n1 := (u 1 + ((D.lat : ℤ) - 1)).toNat with hn1def
  have hn1 : (n1 : ℤ) - ((D.lat : ℤ) - 1) = u 1 := by
    rw [hn1def, Int.toNat_of_nonneg (by have := neg_abs_le (u 1); omega)]; ring
  have hn0r : n0 ∈ List.range D.lat := by
    rw [List.mem_range]; rw [abs_of_nonneg h0] at hb0; omega
  have hn1r : n1 ∈ List.range (2 * D.lat - 1) := by
    rw [List.mem_range]
    have := le_abs_self (u 1); have := neg_abs_le (u 1)
    omega
  simp only [latchk, List.all_eq_true] at h
  have := h n0 hn0r n1 hn1r
  rw [hn0, hn1] at this
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hb 0, hb 1, hb 2,
    s5z_zero, s5z_one, s5z_two] at this
  rcases this with ⟨h0', h1'⟩ | this
  · exfalso; apply hu
    have hz : ∀ i : Fin 3, u (s5z i) = 0 := by
      intro i
      rw [← hb i, h0', h1']
      simp [cen_zero]
    funext c; fin_cases c
    · exact h0'
    · exact h1'
    · exact hz 0
    · exact hz 1
    · exact hz 2
  · exact this.trans_eq (by simp [s5MaxAbs])

/-- **Soundness of `latchk`**: every nonzero vector of `Λ_κ` has `|u|_∞ ≥ λ_∞`. -/
theorem latchk_sound (D : S5Design) (hp : 0 < D.p) (h : latchk D = true) (hl : 1 ≤ D.lat)
    (h2 : 2 * D.lat ≤ D.p + 1) (u : Fin 5 → ℤ) (hu : u ≠ 0)
    (hL : ∀ i : Fin 3, (D.p : ℤ) ∣ u (s5z i) - ∑ d : Fin 2, D.κ i d * u (s5x d)) :
    (D.lat : ℤ) ≤ s5MaxAbs u := by
  by_cases hbig : ∃ c, (D.p : ℤ) ≤ 2 * |u c|
  · obtain ⟨c, hc⟩ := hbig
    have := le_maxAbs u c
    have h2' : 2 * (D.lat : ℤ) ≤ D.p + 1 := by exact_mod_cast h2
    omega
  push Not at hbig
  rcases le_or_gt 0 (u 0) with h0 | h0
  · exact latchk_sound_pos D hp h hl u hu hL hbig h0
  · have := latchk_sound_pos D hp h hl (-u) (neg_ne_zero.mpr hu) (lat_neg D u hL)
      (fun c => by simpa [abs_neg] using hbig c) (by simp only [Pi.neg_apply]; omega)
    rwa [maxAbs_neg] at this

lemma relB_sound (D : S5Design) (a ξ1 ξ2 : Fin 5 → ℤ) (h : relB D a ξ1 ξ2 = true) :
    S5Rel D a ξ1 ξ2 := by
  simp only [relB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun c => (h1 c).1, fun c => (patOK_iff _ _ _).mp (h1 c).2, fun i => ?_⟩
  rw [← rhs_eq]
  exact Int.dvd_of_emod_eq_zero (h2 i)

lemma latB_sound (D : S5Design) (u : Fin 5 → ℤ) (h : latB D u = true) :
    ∀ i : Fin 3, (D.p : ℤ) ∣ u (s5z i) - ∑ d : Fin 2, D.κ i d * u (s5x d) := by
  simp only [latB, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  intro i
  rw [Fin.sum_univ_two, s5x_zero, s5x_one]
  exact Int.dvd_of_emod_eq_zero (h i)

/-- The facts delivered by `smallOK`. -/
structure Small (D : S5Design) (W : Wit) : Prop where
  w : wchk D W = true
  rM : relB D W.aM W.ξ1M W.ξ2M = true
  aM : W.aM ≠ 0
  mM : s5MaxAbs W.aM = D.M
  rJ : relB D W.aJ W.ξ1J W.ξ2J = true
  aJ : W.aJ ≠ 0
  mJ : jitNorm2 W.aJ = D.J2
  lB : latB D W.u = true
  u0 : W.u ≠ 0
  mu : s5MaxAbs W.u = D.lat
  lc : latchk D = true
  p0 : 0 < D.p
  podd : D.p % 2 = 1
  lat1 : 1 ≤ D.lat
  lat2 : 2 * D.lat ≤ D.p + 1
  M2 : 2 * D.M ≤ D.p + 1
  J2p : 4 * D.J2 ≤ (D.p - 1) ^ 2
  T1 : (D.M : ℤ) ≤ W.T
  T2 : D.J2 ≤ (W.T - 1) ^ 2
  T0 : 1 ≤ W.T
  A1 : D.M ≤ W.A + 1
  A2 : D.J2 ≤ W.A ^ 2
  B0 : bz D 0 ≤ W.B 0
  B1 : bz D 1 ≤ W.B 1
  B2 : bz D 2 ≤ W.B 2
  tM1 : D.tabM ^ 5 * D.p ^ 3 ≤ (D.M - 1) ^ 5 * 10 ^ 15
  tM2 : (D.M - 1) ^ 5 * 10 ^ 15 < (D.tabM + 1) ^ 5 * D.p ^ 3
  tJ1 : D.tabJ ^ 10 * D.p ^ 6 ≤ D.J2 ^ 5 * 10 ^ 30
  tJ2 : D.J2 ^ 5 * 10 ^ 30 < (D.tabJ + 1) ^ 10 * D.p ^ 6
  pg1 : D.pig ^ 5 ≤ D.p ^ 3
  pg2 : D.p ^ 3 < (D.pig + 1) ^ 5
  latpig : D.lat ≤ D.pig
  M2' : 2 ≤ D.M
  J1 : 1 ≤ D.J2

lemma small_sound (D : S5Design) (W : Wit) (h : smallOK D W = true) : Small D W := by
  simp only [smallOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩,
    h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩,
    h27⟩, h28⟩, h29⟩, h30⟩, h31⟩, h32⟩, h33⟩, h34⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩

lemma Small.side {D : S5Design} {W : Wit} (h : Small D W) : ChkSide D W :=
  ⟨h.p0, h.T1, h.T2, h.T0, h.A1, h.A2, fun i => by
    fin_cases i
    exacts [h.B0, h.B1, h.B2]⟩

end Z3NetF.Proofs.S5

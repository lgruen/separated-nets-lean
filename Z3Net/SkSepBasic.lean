module
public import Mathlib
public import Z3Net.SkelDefs
public import Z3Net.KNBsep

@[expose] public section

/-!
# Entry Skel, separation part 1: `lem:skelred` (`sec:fine`)

`skelred_coord` (one coordinate: toroidal distance `≥ (|a_c| - 1) f`), `skelred_sep` and its real
form `skelred_sep_real`, and the carry propagation `skelred_carry`. The base-`p` prefix toolkit,
the centred residue `cen` and the toroidal lower bound `cres_lower` of entry KN
(`Z3Net/KNGeomBasic.lean`, `Z3Net/KNSepCoord.lean`) are reused; their `coord`, `cres`, `ent` are
definitionally those of entry F.
-/

namespace Z3NetF.Proofs

open Finset Matrix

namespace SkSep

lemma cres_eq (N : ℕ) (u : ℤ) : Z3NetF.cres N u = Z3NetKN.cres N u := rfl

lemma coord_eq (q m : ℕ) (C : Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) :
    Z3NetF.coord q m C v = Z3NetKN.coord q m C v := rfl

lemma ent_eq {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (i j : ℕ) :
    Z3NetF.ent A i j = Z3NetKN.ent A i j := rfl

lemma cmod_eq_cen (M : ℕ) (u : ℤ) : cmod M u = Z3NetKN.Geom.cen M u := by
  unfold cmod Z3NetKN.Geom.cen; simp only [two_mul]

/-- `cres` is even. -/
lemma cres_neg (N : ℕ) (u : ℤ) : cres N (-u) = cres N u := by
  unfold cres
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  set r := u % (N : ℤ) with hr
  have h0 : 0 ≤ r := Int.emod_nonneg u hN'.ne'
  have h1 : r < N := Int.emod_lt_of_pos u hN'
  have hd := Int.mul_ediv_add_emod u (N : ℤ)
  rcases eq_or_lt_of_le h0 with hr0 | hr0
  · have h00 : u % (N : ℤ) = 0 := by rw [← hr, ← hr0]
    have e : -u = (N : ℤ) * (-(u / N)) := by linarith
    rw [e, Int.mul_emod_right, ← hr0]
  · have e : -u = ((N : ℤ) - r) + (N : ℤ) * (-(u / N) - 1) := by linarith
    have e2 : (-u) % (N : ℤ) = (N : ℤ) - r := by
      rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by linarith) (by linarith)]
    rw [e2]
    have ht : ((N : ℤ) - r).toNat = N - r.toNat := by omega
    rw [ht, Nat.sub_sub_self (by omega), min_comm]

lemma coord_lt {p m : ℕ} [NeZero p] (A : Matrix (Fin m) (Fin m) (ZMod p)) (v : Fin m → ZMod p) :
    coord p m A v < p ^ m := by
  rw [coord_eq, Z3NetKN.Geom.coord_eq_pre]
  exact Z3NetKN.Geom.pre_lt p (Nat.pos_of_neZero p) _ _ (fun j _ => Z3NetKN.Geom.dg_lt A v _)

lemma cres_le_torus {s : ℕ} (N : ℕ) (x y : Fin s → ℕ) (c : Fin s) :
    cres N ((x c : ℤ) - (y c : ℤ)) ^ 2 ≤ torusDist2 N x y := by
  unfold torusDist2
  exact Finset.single_le_sum (f := fun c => cres N ((x c : ℤ) - (y c : ℤ)) ^ 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

/-- Real form from the integer form: `L² g² ≤ ∑ x_c²` gives `L (g / N) ≤ √(∑ (x_c / N)²)`. -/
lemma sqrt_bound {s : ℕ} (x : Fin s → ℝ) (L g Nr : ℝ) (hN : 0 < Nr)
    (h : L ^ 2 * g ^ 2 ≤ ∑ c, x c ^ 2) : L * (g / Nr) ≤ Real.sqrt (∑ c, (x c / Nr) ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have e : ∑ c, (x c / Nr) ^ 2 = (∑ c, x c ^ 2) / Nr ^ 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun c _ => by rw [div_pow]
  rw [e, le_div_iff₀ (by positivity)]
  calc (L * (g / Nr)) ^ 2 * Nr ^ 2 = L ^ 2 * g ^ 2 := by field_simp
    _ ≤ _ := h

/-- Floor change of a step `|a| < q`: `0` or `sgn a`. -/
lemma floor_step (x a q : ℤ) (hq : 0 < q) (ha : |a| < q) :
    (x + a) / q - x / q = 0 ∨ (x + a) / q - x / q = Int.sign a := by
  have h1 := Int.ediv_mul_le x hq.ne'
  have h2 := Int.lt_ediv_add_one_mul_self x hq
  have h3 := Int.ediv_mul_le (x + a) hq.ne'
  have h4 := Int.lt_ediv_add_one_mul_self (x + a) hq
  set t := x / q
  set t' := (x + a) / q
  have hab := abs_lt.mp ha
  have hu : q * (t' - t) < a + q := by nlinarith
  have hl : a - q < q * (t' - t) := by nlinarith
  have d1 : t' - t < 2 := by
    by_contra h; rw [not_lt] at h; nlinarith
  have d2 : -2 < t' - t := by
    by_contra h; rw [not_lt] at h; nlinarith
  rcases (show t' - t = -1 ∨ t' - t = 0 ∨ t' - t = 1 by omega) with hd | hd | hd
  · rw [hd] at hu hl
    have : a < 0 := by linarith
    right; rw [hd, Int.sign_eq_neg_one_of_neg this]
  · left; exact hd
  · rw [hd] at hu hl
    have : 0 < a := by linarith
    right; rw [hd, Int.sign_eq_one_of_pos this]

end SkSep

open SkSep

/-- **`lem:skelred`(i)**, one coordinate. -/
theorem skelred_coord (Q f X Y : ℕ) (hX : X < Q * f) (hY : Y < Q * f) :
    (|cmod Q ((Y / f : ℕ) - (X / f : ℕ) : ℤ)| - 1) * (f : ℤ) ≤ (cres (Q * f) ((Y : ℤ) - X) : ℤ) := by
  have hQf : 0 < Q * f := by omega
  have hQ : 0 < Q := Nat.pos_of_ne_zero (fun h => by simp [h] at hQf)
  have hf : 0 < f := Nat.pos_of_ne_zero (fun h => by simp [h] at hQf)
  rw [cmod_eq_cen]
  set δ := Z3NetKN.Geom.cen Q (((Y / f : ℕ) : ℤ) - ((X / f : ℕ) : ℤ)) with hδ
  obtain ⟨z, hz⟩ := Z3NetKN.Geom.cen_spec Q (((Y / f : ℕ) : ℤ) - ((X / f : ℕ) : ℤ))
  rw [← hδ] at hz
  have dY := Nat.div_add_mod Y f
  have dX := Nat.div_add_mod X f
  have mY := Nat.mod_lt Y hf
  have mX := Nat.mod_lt X hf
  set e : ℤ := ((Y % f : ℕ) : ℤ) - ((X % f : ℕ) : ℤ) with he
  have key : (Y : ℤ) - X = δ * f + e + z * ((Q * f : ℕ) : ℤ) := by
    have cY : (Y : ℤ) = (f : ℤ) * ((Y / f : ℕ) : ℤ) + ((Y % f : ℕ) : ℤ) := by exact_mod_cast dY.symm
    have cX : (X : ℤ) = (f : ℤ) * ((X / f : ℕ) : ℤ) + ((X % f : ℕ) : ℤ) := by exact_mod_cast dX.symm
    rw [cY, cX, he, Nat.cast_mul]
    linear_combination (f : ℤ) * hz
  have heE : |e| ≤ (f : ℤ) - 1 := by
    rw [abs_le]; constructor <;> omega
  have hb := Z3NetKN.Geom.cres_lower Q f hQ hf δ e z ((f : ℤ) - 1)
    (Z3NetKN.Geom.cen_abs Q hQ _) heE
  rw [← key, ← cres_eq] at hb
  have : (|δ| - 1) * (f : ℤ) = |δ| * f - f := by ring
  rw [this]; linarith

/-- `lem:skelred`(i) for one coordinate of a digital point set, in the orientation of
`torusDist2`. -/
lemma skelred_coord_dig {s : ℕ} (p m k : ℕ) (hp : 1 ≤ p) (hkm : k + 1 ≤ m)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p) (c : Fin s) :
    (|cmod (p ^ (k + 1)) ((finePos p m k C w c : ℤ) - finePos p m k C v c)| - 1) *
        ((p ^ (m - (k + 1)) : ℕ) : ℤ) ≤
      (cres (p ^ m) ((digPoint p m C v c : ℤ) - (digPoint p m C w c : ℤ)) : ℤ) := by
  have : NeZero p := ⟨by omega⟩
  have hN : p ^ m = p ^ (k + 1) * p ^ (m - (k + 1)) := by rw [← pow_add]; congr 1; omega
  have hX := coord_lt (C c) v
  have hY := coord_lt (C c) w
  rw [hN] at hX hY
  have := skelred_coord (p ^ (k + 1)) (p ^ (m - (k + 1))) _ _ hX hY
  rw [← cres_neg, neg_sub, hN]
  exact this

/-- `lem:skelred`(i), integer form, for every `p ≥ 1`. -/
lemma skelred_sep_pos {s : ℕ} (p m k M : ℕ) (hp : 1 ≤ p) (hkm : k + 1 ≤ m)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p)
    (hM : ∃ c, (M : ℤ) ≤ |cmod (p ^ (k + 1)) ((finePos p m k C w c : ℤ) - finePos p m k C v c)|) :
    (M - 1) ^ 2 * p ^ (2 * (m - (k + 1))) ≤
      torusDist2 (p ^ m) (digPoint p m C v) (digPoint p m C w) := by
  obtain ⟨c, hc⟩ := hM
  have hb := skelred_coord_dig p m k hp hkm C v w c
  set f := p ^ (m - (k + 1))
  set cr := cres (p ^ m) ((digPoint p m C v c : ℤ) - (digPoint p m C w c : ℤ))
  have h1 : (M - 1) * f ≤ cr := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · simp [h0]
    · have : (((M - 1) * f : ℕ) : ℤ) ≤ cr := by
        push_cast [Nat.cast_sub h0]
        have hf0 : (0 : ℤ) ≤ f := by positivity
        nlinarith
      exact_mod_cast this
  calc (M - 1) ^ 2 * p ^ (2 * (m - (k + 1))) = ((M - 1) * f) ^ 2 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm 2]
    _ ≤ cr ^ 2 := Nat.pow_le_pow_left h1 2
    _ ≤ _ := cres_le_torus _ _ _ c

/-- **`lem:skelred`(i)**, the separation. -/
theorem skelred_sep {s : ℕ} (p m k M : ℕ) (hp : 2 ≤ p) (hkm : k + 1 ≤ m)
    (C : Fin s → Matrix (Fin m) (Fin m) (ZMod p)) (v w : Fin m → ZMod p)
    (hM : ∃ c, (M : ℤ) ≤ |cmod (p ^ (k + 1)) ((finePos p m k C w c : ℤ) - finePos p m k C v c)|) :
    (M - 1) ^ 2 * p ^ (2 * (m - (k + 1))) ≤
      torusDist2 (p ^ m) (digPoint p m C v) (digPoint p m C w) :=
  skelred_sep_pos p m k M (by omega) hkm C v w hM

namespace SkSep

/-- `p^(-(s-r)/s) (p^(sk+r))^(-1/s) = p^(sk+r-(k+1)) / p^(sk+r)`. -/
lemma rpow_scale (p s r k : ℕ) (hp : 1 ≤ p) (hs : 1 ≤ s) (hr : r ≤ s) (hkm : k + 1 ≤ s * k + r) :
    (p : ℝ) ^ (-(((s - r : ℕ) : ℝ) / (s : ℝ))) * ((p : ℝ) ^ (s * k + r)) ^ (-(1 / (s : ℝ))) =
      (p : ℝ) ^ (s * k + r - (k + 1)) / (p : ℝ) ^ (s * k + r) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  have e1 : (p : ℝ) ^ (s * k + r) = (p : ℝ) ^ (s * k + r - (k + 1)) * (p : ℝ) ^ (k + 1) := by
    rw [← pow_add]; congr 1; omega
  have e2 : (p : ℝ) ^ (s * k + r - (k + 1)) / (p : ℝ) ^ (s * k + r) = (p : ℝ) ^ (-((k + 1 : ℕ) : ℝ)) := by
    rw [e1, Real.rpow_neg hp0.le, Real.rpow_natCast]
    have : (0 : ℝ) < (p : ℝ) ^ (s * k + r - (k + 1)) := by positivity
    field_simp
  rw [e2, ← Real.rpow_natCast (p : ℝ) (s * k + r), ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
  congr 1
  push_cast [Nat.cast_sub hr]
  field_simp
  ring

end SkSep

/-- **`lem:skelred`(i)**, real form. -/
theorem skelred_sep_real {s : ℕ} (p r k M : ℕ) (hp : 2 ≤ p) (hs : 1 ≤ s) (hr : r ≤ s)
    (hkm : k + 1 ≤ s * k + r)
    (C : Fin s → Matrix (Fin (s * k + r)) (Fin (s * k + r)) (ZMod p))
    (v w : Fin (s * k + r) → ZMod p)
    (hM : ∃ c, (M : ℤ) ≤ |cmod (p ^ (k + 1))
      ((finePos p (s * k + r) k C w c : ℤ) - finePos p (s * k + r) k C v c)|) :
    ((M : ℝ) - 1) * (p : ℝ) ^ (-(((s - r : ℕ) : ℝ) / (s : ℝ))) *
        ((p : ℝ) ^ (s * k + r)) ^ (-(1 / (s : ℝ)))
      ≤ Real.sqrt (∑ c, ((cres (p ^ (s * k + r))
          ((digPoint p (s * k + r) C v c : ℤ) - (digPoint p (s * k + r) C w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (s * k + r)) ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [mul_assoc, rpow_scale p s r k (by omega) hs hr hkm]
  rcases Nat.eq_zero_or_pos M with h0 | h0
  · subst h0
    have : (0 : ℝ) ≤ (p : ℝ) ^ (s * k + r - (k + 1)) / (p : ℝ) ^ (s * k + r) := by positivity
    have h2 := Real.sqrt_nonneg (∑ c, ((cres (p ^ (s * k + r))
          ((digPoint p (s * k + r) C v c : ℤ) - (digPoint p (s * k + r) C w c : ℤ)) : ℝ)
          / (p : ℝ) ^ (s * k + r)) ^ 2)
    push_cast; nlinarith
  apply sqrt_bound _ _ _ _ (by positivity)
  have hZ := skelred_sep p (s * k + r) k M hp hkm C v w hM
  unfold torusDist2 at hZ
  have := (Nat.cast_le (α := ℝ)).mpr hZ
  push_cast [Nat.cast_sub h0] at this
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  convert this using 2
  ring

/-- **`lem:skelred`(ii)** (carry propagation). -/
theorem skelred_carry (p k P P' : ℕ) (hp : 2 ≤ p) (hP : P < p ^ (k + 1)) (hP' : P' < p ^ (k + 1))
    (ha : |cmod (p ^ (k + 1)) ((P' : ℤ) - P)| < p) :
    ∃ ξ : ℕ → ℤ, (∀ j, 1 ≤ j → j ≤ k →
        ((P' / p ^ j : ℕ) : ℤ) - (P / p ^ j : ℕ) ≡ ξ j [ZMOD (p : ℤ) ^ (k + 1 - j)] ∧
          (ξ j = 0 ∨ ξ j = Int.sign (cmod (p ^ (k + 1)) ((P' : ℤ) - P)))) ∧
      ∀ j, 2 ≤ j → j ≤ k → ξ j ≠ 0 → ξ (j - 1) ≠ 0 := by
  set a := cmod (p ^ (k + 1)) ((P' : ℤ) - P) with ha_def
  obtain ⟨z, hz⟩ := Z3NetKN.Geom.cen_spec (p ^ (k + 1)) ((P' : ℤ) - P)
  rw [← cmod_eq_cen, ← ha_def] at hz
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (show 0 < p by omega)
  refine ⟨fun j => ((P : ℤ) + a) / (p : ℤ) ^ j - (P : ℤ) / (p : ℤ) ^ j, fun j hj1 hjk => ⟨?_, ?_⟩, ?_⟩
  · have hpj : ((p : ℤ) ^ j) ≠ 0 := by positivity
    have e : (P' : ℤ) = ((P : ℤ) + a) + (z * (p : ℤ) ^ (k + 1 - j)) * (p : ℤ) ^ j := by
      have : (p : ℤ) ^ (k + 1 - j) * (p : ℤ) ^ j = ((p ^ (k + 1) : ℕ) : ℤ) := by
        push_cast; rw [← pow_add]; congr 1; omega
      rw [mul_assoc, this]; linarith
    push_cast
    rw [e, Int.add_mul_ediv_right _ _ hpj]
    rw [Int.modEq_iff_dvd]
    exact ⟨-z, by ring⟩
  · apply floor_step _ _ _ (by positivity)
    calc |a| < p := ha
      _ = (p : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℤ) ^ j := pow_le_pow_right₀ (by omega) hj1
  · intro j hj2 _ hne h0
    apply hne
    simp only at h0 ⊢
    have e1 : ((P : ℤ) + a) / (p : ℤ) ^ (j - 1) = (P : ℤ) / (p : ℤ) ^ (j - 1) := by linarith
    have hpj : (p : ℤ) ^ j = (p : ℤ) ^ (j - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hpj, ← Int.ediv_ediv_of_nonneg (by positivity), ← Int.ediv_ediv_of_nonneg (by positivity), e1,
      sub_self]

end Z3NetF.Proofs

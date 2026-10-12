/-
Proof module of entry Obs: counting cells with prescribed leading digits (the counting step of
`prop:ceil`, `cor:ceils`, `prop:P2`), and the passage from coordinate bounds to `PairBelow`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.ObsDefs
public import Z3Net.FNie

@[expose] public section

/-!
# Entry Obs: counting and distances

* `count_box`: for a box `d` (`∑ d = m`) with a unit box minor, the number of indices whose
  leading digits (the first `d_c` digits of coordinate `c`) lie in prescribed sets is the product
  of the sizes of these sets. So prescribed leading digits on boxes of total depth `≤ m` are
  jointly uniform ("all counts multiplied by `q^(...)`" in the proof of `cor:ceils`).
* `pair_of_bounds`: coordinatewise bounds `|X_c(w) - X_c(v)| < b_c q^(m-k)` give `PairBelow` with
  `B = ∑ b_c²` (Euclidean, and toroidal since the toroidal distance is at most the Euclidean one).
-/

namespace Z3NetF.Proofs

open Matrix Finset

noncomputable section

namespace ObsCount

/-- Total digit accessor: digit `j` of `C v`, `0` out of range. -/
def dig {q m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod q)) (v : Fin m → ZMod q) (j : ℕ) : ZMod q :=
  if h : j < m then (C *ᵥ v) ⟨j, h⟩ else 0

lemma dig_add {q m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod q)) (v w : Fin m → ZMod q) (j : ℕ) :
    dig C (v + w) j = dig C v j + dig C w j := by
  unfold dig; split_ifs <;> simp [mulVec_add]

lemma dig_smul {q m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod q)) (t : ZMod q)
    (v : Fin m → ZMod q) (j : ℕ) : dig C (t • v) j = t * dig C v j := by
  unfold dig; split_ifs <;> simp [mulVec_smul]

variable {q s m : ℕ} [NeZero q]

/-- Leading digits of the coordinates, as a function of the index. -/
def lead (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) (d : Fin s → ℕ) (v : Fin m → ZMod q) :
    (c : Fin s) → Fin (d c) → ZMod q :=
  fun c j => dig (C c) v j

lemma lead_bij (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) (d : Fin s → ℕ) (hd : ∑ c, d c = m)
    (hu : IsUnit (Z3NetF.boxMatrix C d).det) : Function.Bijective (lead C d) := by
  classical
  have hB := (isUnit_iff_bij (Z3NetF.boxMatrix C d)).1 hu
  have hinj : Function.Injective (lead C d) := by
    intro v w hvw
    apply hB.1
    funext r
    obtain ⟨c, i, hi, hr, hrow⟩ := box_row_get C d hd r
    have h1 := congrFun (congrFun hvw c) ⟨i, hi⟩
    simp only [lead, dig, dif_pos (lt_of_lt_of_le hi (le_of_sum d hd c))] at h1
    change (Z3NetF.boxMatrix C d r) ⬝ᵥ v = (Z3NetF.boxMatrix C d r) ⬝ᵥ w
    rw [hrow]
    exact h1
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
  simp only [Fintype.card_fun, Fintype.card_pi, ZMod.card, Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum, hd]

/-- **Counting.** -/
theorem count_box (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) (d : Fin s → ℕ)
    (hd : ∑ c, d c = m) (hu : IsUnit (Z3NetF.boxMatrix C d).det)
    (A : Fin s → ℕ → Finset (ZMod q)) :
    (univ.filter fun v : Fin m → ZMod q => ∀ c, ∀ j < d c, dig (C c) v j ∈ A c j).card =
      ∏ c, ∏ j ∈ range (d c), (A c j).card := by
  classical
  have hbij := lead_bij C d hd hu
  set S : Finset ((c : Fin s) → Fin (d c) → ZMod q) :=
    Fintype.piFinset fun c => Fintype.piFinset fun j : Fin (d c) => A c j
  have hS : S.card = ∏ c, ∏ j ∈ range (d c), (A c j).card := by
    simp only [S, Fintype.card_piFinset]
    refine Finset.prod_congr rfl fun c _ => ?_
    exact Fin.prod_univ_eq_prod_range (fun j => (A c j).card) (d c)
  rw [← hS]
  refine Finset.card_bij (fun v _ => lead C d v) ?_ ?_ ?_
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    simp only [S, Fintype.mem_piFinset]
    intro c j
    exact hv c j j.isLt
  · intro v _ w _ h
    exact hbij.1 h
  · intro y hy
    obtain ⟨v, rfl⟩ := hbij.2 y
    refine ⟨v, ?_, rfl⟩
    simp only [S, Fintype.mem_piFinset] at hy
    simp only [mem_filter, mem_univ, true_and]
    intro c j hj
    exact hy c ⟨j, hj⟩

/-- **Union bound** (the counting step of `prop:ceil`, `cor:ceils`, `prop:P2`): base conditions
on the leading `dB c` digits of the coordinates (`A c j` nonempty) and, for each test coordinate
`u ∈ U` (with `dB u = 0`), a bad set `B u` for digit `k` of `u`; if every box `dB + (k+1) e_u` is
unit and `∑_{u ∈ U} |B u| < q`, some index satisfies the base conditions and avoids every bad
set. -/
theorem exists_good (C : Fin s → Matrix (Fin m) (Fin m) (ZMod q)) (k : ℕ)
    (hunit : ∀ d : Fin s → ℕ, ∑ c, d c = m → IsUnit (Z3NetF.boxMatrix C d).det)
    (dB : Fin s → ℕ) (A : Fin s → ℕ → Finset (ZMod q)) (hA : ∀ c, ∀ j < dB c, (A c j).Nonempty)
    (U : Finset (Fin s)) (hUne : U.Nonempty) (hU : ∀ u ∈ U, dB u = 0)
    (hsum : ∑ c, dB c + (k + 1) = m)
    (B : Fin s → Finset (ZMod q)) (hB : ∑ u ∈ U, (B u).card < q) :
    ∃ v : Fin m → ZMod q, (∀ c, ∀ j < dB c, dig (C c) v j ∈ A c j) ∧
      ∀ u ∈ U, dig (C u) v k ∉ B u := by
  classical
  set T := univ.filter fun v : Fin m → ZMod q => ∀ c, ∀ j < dB c, dig (C c) v j ∈ A c j
  set Bad := fun u => univ.filter fun v : Fin m → ZMod q =>
    (∀ c, ∀ j < dB c, dig (C c) v j ∈ A c j) ∧ dig (C u) v k ∈ B u
  set P := ∏ c, ∏ j ∈ range (dB c), (A c j).card
  have hP : 0 < P := Finset.prod_pos fun c _ => Finset.prod_pos fun j hj =>
    Finset.card_pos.mpr (hA c j (mem_range.mp hj))
  -- the box `dB + (k+1) e_u`
  have key : ∀ u ∈ U, T.card = P * q ^ (k + 1) ∧ (Bad u).card = P * (q ^ k * (B u).card) := by
    intro u hu
    let d : Fin s → ℕ := fun c => if c = u then k + 1 else dB c
    have hd : ∑ c, d c = m := by
      have e1 : ∀ c, d c = dB c + (if c = u then k + 1 else 0) := by
        intro c; by_cases hc : c = u
        · subst hc; simp [d, hU c hu]
        · simp [d, hc]
      simp only [e1, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, if_true]
      exact hsum
    have hdu : d u = k + 1 := by simp [d]
    have hdc : ∀ c, c ≠ u → d c = dB c := fun c hc => by simp [d, hc]
    have hprod : ∀ F : Fin s → ℕ → ℕ, ∏ c, ∏ j ∈ range (d c), F c j =
        (∏ j ∈ range (k + 1), F u j) * ∏ c ∈ ({u}ᶜ : Finset (Fin s)), ∏ j ∈ range (dB c), F c j := by
      intro F
      rw [Fintype.prod_eq_mul_prod_compl u, hdu]
      congr 1
      refine Finset.prod_congr rfl fun c hc => ?_
      have hc' : c ≠ u := by simpa using hc
      rw [hdc c hc']
    have hP' : ∀ F : Fin s → ℕ → Finset (ZMod q), (∀ c, c ≠ u → ∀ j, F c j = A c j) →
        ∏ c ∈ ({u}ᶜ : Finset (Fin s)), ∏ j ∈ range (dB c), (F c j).card = P := by
      intro F hF
      simp only [P]
      rw [Fintype.prod_eq_mul_prod_compl u (fun c => ∏ j ∈ range (dB c), (A c j).card), hU u hu]
      simp only [range_zero, prod_empty, one_mul]
      refine Finset.prod_congr rfl fun c hc => ?_
      have hc' : c ≠ u := by simpa using hc
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hF c hc' j]
    constructor
    · have h1 := count_box C d hd (hunit d hd) (fun c j => if c = u then univ else A c j)
      rw [hprod, hP' _ (fun c hc j => by simp [hc])] at h1
      simp only [if_true, card_univ, ZMod.card, prod_const, card_range] at h1
      have hTe : T = univ.filter fun v : Fin m → ZMod q =>
          ∀ c, ∀ j < d c, dig (C c) v j ∈ (if c = u then univ else A c j) := by
        ext v
        simp only [T, mem_filter, mem_univ, true_and]
        constructor
        · intro h c j hj
          by_cases hc : c = u
          · simp [hc]
          · rw [if_neg hc]; exact h c j (by rw [hdc c hc] at hj; exact hj)
        · intro h c j hj
          by_cases hc : c = u
          · subst hc; rw [hU c hu] at hj; omega
          · have := h c j (by rw [hdc c hc]; exact hj)
            rwa [if_neg hc] at this
      rw [hTe, h1, mul_comm]
    · have h1 := count_box C d hd (hunit d hd)
        (fun c j => if c = u then (if j = k then B u else univ) else A c j)
      rw [hprod, hP' _ (fun c hc j => by simp [hc])] at h1
      simp only [if_true] at h1
      have hBe : Bad u = univ.filter fun v : Fin m → ZMod q =>
          ∀ c, ∀ j < d c, dig (C c) v j ∈
            (if c = u then (if j = k then B u else univ) else A c j) := by
        ext v
        simp only [Bad, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨h, hb⟩ c j hj
          by_cases hc : c = u
          · subst hc
            rw [if_pos rfl]
            by_cases hjk : j = k
            · subst hjk; rw [if_pos rfl]; exact hb
            · rw [if_neg hjk]; exact mem_univ _
          · rw [if_neg hc]; exact h c j (by rw [hdc c hc] at hj; exact hj)
        · intro h
          refine ⟨fun c j hj => ?_, ?_⟩
          · by_cases hc : c = u
            · subst hc; rw [hU c hu] at hj; omega
            · have := h c j (by rw [hdc c hc]; exact hj)
              rwa [if_neg hc] at this
          · have := h u k (by rw [hdu]; omega)
            simpa using this
      have hpr : ∏ j ∈ range (k + 1), (if j = k then B u else univ).card = q ^ k * (B u).card := by
        rw [Finset.prod_range_succ, if_pos rfl,
          Finset.prod_congr rfl (fun j hj => by rw [if_neg (by simp at hj; omega)]),
          prod_const, card_range, card_univ, ZMod.card]
      rw [hBe, h1, hpr, mul_comm]
  -- union bound
  obtain ⟨u0, hu0⟩ := hUne
  have hT := (key u0 hu0).1
  have hcard : (U.biUnion Bad).card < T.card := by
    calc (U.biUnion Bad).card ≤ ∑ u ∈ U, (Bad u).card := card_biUnion_le
      _ = ∑ u ∈ U, P * (q ^ k * (B u).card) :=
        Finset.sum_congr rfl fun u hu => (key u hu).2
      _ = P * q ^ k * ∑ u ∈ U, (B u).card := by rw [Finset.mul_sum]; ring_nf
      _ < P * q ^ k * q := by
        apply Nat.mul_lt_mul_of_pos_left hB
        exact Nat.mul_pos hP (pow_pos (Nat.pos_of_neZero q) k)
      _ = T.card := by rw [hT]; ring
  obtain ⟨v, hvT, hvB⟩ : ∃ v ∈ T, v ∉ U.biUnion Bad := by
    by_contra hno
    push Not at hno
    have : T ⊆ U.biUnion Bad := fun v hv => hno v hv
    exact absurd (card_le_card this) (not_le.mpr hcard)
  refine ⟨v, (mem_filter.mp hvT).2, fun u hu hb => hvB ?_⟩
  rw [mem_biUnion]
  exact ⟨u, hu, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hvT).2, hb⟩⟩

/-! ## From coordinate bounds to `PairBelow` -/

lemma cres_le_abs (N : ℕ) (hN : 0 < N) (u : ℤ) : (Z3NetF.cres N u : ℤ) ≤ |u| := by
  unfold Z3NetF.cres
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 := Int.emod_nonneg u hN'.ne'
  have h1 := Int.emod_lt_of_pos u hN'
  have hd := Int.mul_ediv_add_emod u (N : ℤ)
  set r := (u % (N : ℤ)).toNat with hrdef
  have hr : (r : ℤ) = u % N := Int.toNat_of_nonneg h0
  have hrN : r ≤ N := by omega
  rcases le_or_gt 0 u with hu | hu
  · have hq : 0 ≤ u / N := Int.ediv_nonneg hu hN'.le
    calc ((min r (N - r) : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast min_le_left _ _
      _ ≤ |u| := by rw [hr, abs_of_nonneg hu]; nlinarith
  · have hq : u / N ≤ -1 := by
      by_contra h
      push Not at h
      have : 0 ≤ u / N := by omega
      nlinarith
    calc ((min r (N - r) : ℕ) : ℤ) ≤ ((N - r : ℕ) : ℤ) := by exact_mod_cast min_le_right _ _
      _ ≤ |u| := by rw [Nat.cast_sub hrN, hr, abs_of_neg hu]; nlinarith

theorem pair_of_bounds {s q m k : ℕ} (hq : 0 < q) (hs : 0 < s)
    (X : (Fin m → ZMod q) → Fin s → ℕ) (v w : Fin m → ZMod q) (hvw : v ≠ w) (b : Fin s → ℝ)
    (hb : ∀ c, |(X w c : ℝ) - X v c| < b c * (q : ℝ) ^ (m - k)) :
    Z3NetF.PairBelow q m k X (∑ c, b c ^ 2) := by
  have hG : (0 : ℝ) < (q : ℝ) ^ (m - k) := by positivity
  have hne : (univ : Finset (Fin s)).Nonempty := ⟨⟨0, hs⟩, mem_univ _⟩
  have hterm : ∀ c, (((X v c : ℝ) - X w c) / (q : ℝ) ^ (m - k)) ^ 2 < b c ^ 2 := by
    intro c
    have h1 := hb c
    have hbpos : 0 < b c := by
      by_contra h; push Not at h
      have : b c * (q : ℝ) ^ (m - k) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hG.le
      linarith [abs_nonneg ((X w c : ℝ) - X v c)]
    rw [div_pow, div_lt_iff₀ (by positivity)]
    calc ((X v c : ℝ) - X w c) ^ 2 = |(X w c : ℝ) - X v c| ^ 2 := by rw [sq_abs]; ring
      _ < (b c * (q : ℝ) ^ (m - k)) ^ 2 := by gcongr
      _ = b c ^ 2 * ((q : ℝ) ^ (m - k)) ^ 2 := by ring
  have heuc : Z3NetF.cellDist2 q m k (X v) (X w) < ∑ c, b c ^ 2 := by
    unfold Z3NetF.cellDist2
    exact Finset.sum_lt_sum_of_nonempty hne fun c _ => hterm c
  refine ⟨v, w, hvw, heuc, lt_of_le_of_lt ?_ heuc⟩
  unfold Z3NetF.torusDist2 Z3NetF.cellDist2
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun c _ => ?_
  have hN : 0 < q ^ m := pow_pos hq m
  have h1 := cres_le_abs (q ^ m) hN ((X v c : ℤ) - X w c)
  have h2 : ((Z3NetF.cres (q ^ m) ((X v c : ℤ) - X w c) : ℕ) : ℝ) ≤ |(X v c : ℝ) - X w c| := by
    have : ((Z3NetF.cres (q ^ m) ((X v c : ℤ) - X w c) : ℤ) : ℝ) ≤ ((|(X v c : ℤ) - X w c| : ℤ) : ℝ) :=
      by exact_mod_cast h1
    simpa using this
  rw [div_pow, show (q : ℝ) ^ (2 * (m - k)) = ((q : ℝ) ^ (m - k)) ^ 2 by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ((Z3NetF.cres (q ^ m) ((X v c : ℤ) - X w c) : ℕ) : ℝ) ^ 2 ≤ |(X v c : ℝ) - X w c| ^ 2 := by
        gcongr
    _ = ((X v c : ℝ) - X w c) ^ 2 := sq_abs _

end ObsCount

end

end Z3NetF.Proofs

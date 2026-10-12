module
public import Z3Net.FTs

@[expose] public section

/-!
# Entry F, part 6: the frame of `s` places with `m = s k`: graph form, `E`-basis, `prop:Ns`

* `frameGraph_spec_core`: the `(k, …, k)` box `G` of the frame is invertible and `Φ^F` (defined
  via Mathlib's `G⁻¹`) is the graph form of the frame.
* The `E`-basis: `E_{d,j} = Π_d (t - x_d)^j` (finite `d`), `E_{∞,j} = Π t^(k-1-j)`; its cells
  vanish off `d` and form `Toep(uN_d)` at `d`; its first offset digit at `c ≠ d` is
  `Q_c^k w_cd y_cd^(k-1-j)`. Hence `Φ^F_cd · Toep(uN_d) = Ψ_cd` (the offset digits of the
  `E`-basis), which gives `prop:Ns` (`Ns_row0_core`).
-/

namespace Z3NetF.Proofs

open Polynomial Finset Matrix

noncomputable section

variable {R : Type*} [CommRing R] {s m : ℕ}

/-! ## Graph forms: matrix-vector products -/

lemma sum_cols {M : Type*} [AddCommMonoid M] (K : Fin s → ℕ) (hK : ∑ c, K c = m) (f : Fin m → M) :
    ∑ j, f j = ∑ d : Fin s, ∑ l : Fin (K d), f ⟨pre K d + l, pre_add_lt K hK d l l.isLt⟩ := by
  rw [← Fintype.sum_sigma (fun (p : Σ d : Fin s, Fin (K d)) =>
    f ⟨pre K p.1 + p.2, pre_add_lt K hK p.1 p.2 p.2.isLt⟩)]
  symm
  apply Fintype.sum_bijective (fun p : Σ d : Fin s, Fin (K d) =>
    (⟨pre K p.1 + p.2, pre_add_lt K hK p.1 p.2 p.2.isLt⟩ : Fin m))
  · constructor
    · rintro ⟨d, l⟩ ⟨d', l'⟩ h
      have := pos_inj K d d' l l' l.isLt l'.isLt (congrArg Fin.val h)
      exact sigma_eq_of d d' l l' this.1 this.2
    · intro j
      obtain ⟨e, l, hl, rfl⟩ := col_cover K hK j
      exact ⟨⟨e, ⟨l, hl⟩⟩, rfl⟩
  · intro p; rfl

lemma graphGenK_mulVec_off (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R) (c : Fin s) (v : Fin m → R)
    (r : Fin (m - K c)) :
    (Z3NetF.graphGenK K Φ c *ᵥ v) ⟨K c + r, by omega⟩ =
      ∑ d : Fin s, ∑ l : Fin (K d), Φ c d r l * v ⟨pre K d + l, pre_add_lt K hK d l l.isLt⟩ := by
  simp only [mulVec, dotProduct]
  rw [sum_cols K hK]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun l _ => ?_
  rw [graphGenK_apply K hK Φ c _ d l l.isLt, dif_neg (by simp)]
  congr 2
  ext; simp

lemma graphGenK_mulVec_cell (K : Fin s → ℕ) (hK : ∑ c, K c = m)
    (Φ : (c d : Fin s) → Matrix (Fin (m - K c)) (Fin (K d)) R) (c : Fin s) (v : Fin m → R)
    (i : ℕ) (hi : i < K c) :
    (Z3NetF.graphGenK K Φ c *ᵥ v) ⟨i, lt_of_lt_of_le hi (le_of_sum K hK c)⟩ =
      v ⟨pre K c + i, pre_add_lt K hK c i hi⟩ := by
  simp only [mulVec, dotProduct]
  rw [sum_cols K hK, Finset.sum_eq_single c, Finset.sum_eq_single ⟨i, hi⟩]
  · rw [graphGenK_apply K hK Φ c _ c i hi, dif_pos hi, if_pos ⟨rfl, rfl⟩, one_mul]
  · intro l _ hl
    rw [graphGenK_apply K hK Φ c _ c l l.isLt, dif_pos hi, if_neg, zero_mul]
    intro h; exact hl (Fin.ext h.2)
  · simp
  · intro d _ hd
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [graphGenK_apply K hK Φ c _ d l l.isLt, dif_pos hi, if_neg, zero_mul]
    intro h; exact hd h.1
  · simp

lemma box_mulVec_pre (C : Fin s → Matrix (Fin m) (Fin m) R) (d : Fin s → ℕ) (hd : ∑ c, d c = m)
    (v : Fin m → R) (c : Fin s) (i : ℕ) (hi : i < d c) :
    (Z3NetF.boxMatrix C d *ᵥ v) ⟨pre d c + i, pre_add_lt d hd c i hi⟩ =
      (C c *ᵥ v) ⟨i, lt_of_lt_of_le hi (le_of_sum d hd c)⟩ := by
  change Z3NetF.boxMatrix C d ⟨_, _⟩ ⬝ᵥ v = C c ⟨i, _⟩ ⬝ᵥ v
  rw [box_row_pre C d hd c i hi]

lemma mat_congr2 {p r : ℕ} (M : Matrix (Fin p) (Fin r) R) (a a' b b' : ℕ) (h1 : a < p)
    (h1' : a' < p) (h2 : b < r) (h2' : b' < r) (ha : a = a') (hb : b = b') :
    M ⟨a, h1⟩ ⟨b, h2⟩ = M ⟨a', h1'⟩ ⟨b', h2'⟩ := by
  subst ha; subst hb; rfl

/-! ## Constant depths -/

lemma sum_const_k (k : ℕ) : ∑ _c : Fin s, k = s * k := by simp

lemma pre_const (k : ℕ) (d : Fin s) : pre (fun _ : Fin s => k) d = d * k := by
  show ((List.ofFn (fun _ : Fin s => k)).take d).sum = d * k
  rw [List.ofFn_const, List.take_replicate, List.sum_replicate, smul_eq_mul,
    min_eq_left (le_of_lt d.isLt)]

/-! ## The frame's graph form -/

variable (k : ℕ) (inf : Fin s) (x : Fin s → R)

/-- The `(k, …, k)` box of the frame. -/
abbrev Gk : Matrix (Fin (s * k)) (Fin (s * k)) R :=
  Z3NetF.boxMatrix (Z3NetF.frameRead (s * k) inf x) (fun _ => k)

lemma Gk_unit (hx : Z3NetF.PlacesOK inf x) : IsUnit (Gk k inf x).det := by
  have hprod : IsUnit (∏ c : Fin s, ∏ c' : Fin s,
      (if c' < c ∧ c ≠ inf ∧ c' ≠ inf then (x c - x c') ^ (k * k) else 1)) := by
    rw [IsUnit.prod_univ_iff]; intro c
    rw [IsUnit.prod_univ_iff]; intro c'
    split_ifs with h
    · exact (hx c c' h.2.1 h.2.2 (ne_of_gt h.1)).pow _
    · exact isUnit_one
  rcases frame_minor_core inf x (d := fun _ => k) (sum_const_k k) with h | h <;> rw [h]
  · exact hprod
  · exact hprod.neg

lemma frameGraph_eq_invPhi :
    Z3NetF.frameGraph R k inf x = invPhi (m := s * k) (fun _ => k) (sum_const_k k)
      (Z3NetF.frameRead (s * k) inf x) := by
  funext c d r l
  simp only [Z3NetF.frameGraph, invPhi]
  exact mat_congr2 _ _ _ _ _ _ _ _ _ rfl (by rw [pre_const])

theorem frameGraph_spec_core (hx : Z3NetF.PlacesOK inf x) :
    IsUnit (Gk k inf x).det ∧
      ∀ c, Z3NetF.graphGenK (m := s * k) (fun _ => k) (Z3NetF.frameGraph R k inf x) c * Gk k inf x =
        Z3NetF.frameRead (s * k) inf x c := by
  refine ⟨Gk_unit k inf x hx, fun c => ?_⟩
  rw [frameGraph_eq_invPhi, graphGenK_inv _ (sum_const_k k) _ (Gk_unit k inf x hx) c,
    Matrix.mul_assoc, nonsing_inv_mul _ (Gk_unit k inf x hx), Matrix.mul_one]

end

end Z3NetF.Proofs

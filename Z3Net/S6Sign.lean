/-
Proof module (stage 6, main entry): `rem:sign`, the flipped diagonal.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.NetQ
public import Z3Net.Ceil
public import Z3Net.SepDig

@[expose] public section

/-!
# `rem:sign`

`E' = N E` with `N = I + 2 E_{k,k-1}`, so `PGenFlip c = N · PGen c`: the flip keeps the `(k,k,k)`
box `G` and adds twice the unit row `n_{c,k-1}` to the first offset row of every coordinate. From
`prop:cell` (`Sep.Dg_geo`), the level-`(k-1)` first-offset entries of `𝒫_{k,p}` are `-1` (own),
`-1` (block `c,c+1`), `+1` (block `c,c+2`); after the flip the own entry is `+1`, and
`prop:ceil`(ii) caps the minimum distance at `√12/p`.
-/

namespace Z3Net.Proofs

open Matrix Finset

noncomputable section

namespace Sign

/-- `N = I + 2 E_{k,k-1}`. -/
def Nf (k : ℕ) : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ :=
  fun i j => if i = j then 1 else if (i : ℕ) = k ∧ (j : ℕ) + 1 = k then 2 else 0

lemma Nf_mul_apply (k : ℕ) (hk : 1 ≤ k) (A : Matrix (Fin (3 * k)) (Fin (3 * k)) ℤ) (i j : Fin (3 * k)) :
    (Nf k * A) i j = A i j + (if (i : ℕ) = k then 2 * A ⟨k - 1, by omega⟩ j else 0) := by
  rw [mul_apply]
  by_cases hi : (i : ℕ) = k
  · have hne : i ≠ (⟨k - 1, by omega⟩ : Fin (3 * k)) := by
      intro h; rw [Fin.ext_iff] at h; simp at h; omega
    rw [if_pos hi, Finset.sum_eq_add i ⟨k - 1, by omega⟩ hne _ (by simp) (by simp)]
    · simp only [Nf, if_true]
      rw [if_neg hne, if_pos ⟨hi, by show k - 1 + 1 = k; omega⟩]
      ring
    · intro l _ hl
      simp only [Nf]
      rw [if_neg (Ne.symm hl.1), if_neg (by intro h; apply hl.2; ext; simp; omega), zero_mul]
  · rw [if_neg hi, add_zero, Finset.sum_eq_single i]
    · simp [Nf]
    · intro l _ hl
      simp only [Nf]
      rw [if_neg (Ne.symm hl), if_neg (by tauto), zero_mul]
    · simp

lemma Eflip_eq (k : ℕ) (hk : 1 ≤ k) : Eflip k = Nf k * E k := by
  ext i j
  rw [Nf_mul_apply k hk]
  have hi := i.isLt; have hj := j.isLt
  simp only [Eflip, E]
  split_ifs <;> first | omega | (simp_all [Fin.ext_iff]; try omega)

lemma Nf_lower (k : ℕ) : ∀ i j : Fin (3 * k), i < j → Nf k i j = 0 := by
  intro i j h
  have h' : (i : ℕ) < j := h
  simp only [Nf]
  rw [if_neg (ne_of_lt h), if_neg (by omega)]

lemma Nf_diag (k : ℕ) (i : Fin (3 * k)) : Nf k i i = 1 := by simp [Nf]

lemma Lflip_eq (k : ℕ) (hk : 1 ≤ k) : Lflip k = Nf k * L k := by
  rw [Lflip, Eflip_eq k hk, L, Matrix.mul_assoc]

lemma Lflip_lower (k : ℕ) (hk : 1 ≤ k) (i j : Fin (3 * k)) (h : i < j) : Lflip k i j = 0 := by
  rw [Lflip_eq k hk]; exact lower_mul _ _ (Nf_lower k) (fun a b => L_lower k a b) i j h

lemma Lflip_diag (k : ℕ) (hk : 1 ≤ k) (i : Fin (3 * k)) : Lflip k i i = 1 ∨ Lflip k i i = -1 := by
  rw [Lflip_eq k hk, diag_mul_of_lower _ _ (Nf_lower k) (fun a b => L_lower k a b), Nf_diag, one_mul]
  exact L_diag k i

theorem sign_boxMinor (k : ℕ) (hk : 1 ≤ k) (d : Fin 3 → ℕ) (hd : d 0 + d 1 + d 2 = 3 * k) :
    (boxMatrix (PGenFlip k) d).det = 1 ∨ (boxMatrix (PGenFlip k) d).det = -1 :=
  scrambled_boxMinor k hk (Lflip k) (Lflip_lower k hk) (Lflip_diag k hk) d hd

theorem sign_net (q k : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) : IsNet0 q (3 * k) (PpointFlip q k) := by
  haveI : NeZero q := ⟨by omega⟩
  apply isNet0_of_box_injective
  intro d hd
  apply mulVec_injective_of_isUnit_det
  have hmap := boxMatrix_map (Int.castRingHom (ZMod q)) (PGenFlip k) d
  have : boxMatrix (fun c => (PGenFlip k c).map (Int.cast : ℤ → ZMod q)) d =
      (boxMatrix (PGenFlip k) d).map (Int.castRingHom (ZMod q)) := hmap
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rcases sign_boxMinor k hk d hd with h | h <;> rw [h] <;> simp

lemma PGenFlip_eq (k : ℕ) (hk : 1 ≤ k) (c : Fin 3) : PGenFlip k c = Nf k * PGen k c := by
  fin_cases c <;> simp [PGenFlip, PGen, Lflip_eq k hk, Matrix.mul_assoc]

/-- Rows `< k` of `PGenFlip` and `PGen` agree. -/
lemma PGenFlip_row_lt (k : ℕ) (hk : 1 ≤ k) (c : Fin 3) (i : Fin (3 * k)) (hi : (i : ℕ) < k) :
    PGenFlip k c i = PGen k c i := by
  funext j
  rw [PGenFlip_eq k hk, Nf_mul_apply k hk, if_neg (by omega), add_zero]

lemma PGenFlip_row_k (k : ℕ) (hk : 1 ≤ k) (c : Fin 3) (j : Fin (3 * k)) :
    PGenFlip k c ⟨k, by omega⟩ j = PGen k c ⟨k, by omega⟩ j + 2 * PGen k c ⟨k - 1, by omega⟩ j := by
  rw [PGenFlip_eq k hk, Nf_mul_apply k hk, if_pos rfl]

variable {F : Type*} [Field F]

lemma box_eq (k : ℕ) (hk : 1 ≤ k) :
    boxMatrix (fun c => (PGenFlip k c).map (Int.cast : ℤ → F)) (fun _ => k) =
      boxMatrix (fun c => (PGen k c).map (Int.cast : ℤ → F)) (fun _ => k) := by
  ext r l
  have hr := r.isLt
  unfold boxMatrix
  split_ifs with h1 h2
  · simp only [map_apply]; rw [PGenFlip_row_lt k hk 0 r h1]
  · simp only [map_apply]; rw [PGenFlip_row_lt k hk 1 _ (by simp only at h1 h2 ⊢; omega)]
  · simp only [map_apply]; rw [PGenFlip_row_lt k hk 2 _ (by simp only at h1 h2 ⊢; omega)]

/-- `(C_e G⁻¹)` on the cell rows: the unit rows. -/
lemma cell_rows (k : ℕ) (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) F)
    (hG : IsUnit (boxMatrix C (fun _ => k)).det) (e : Fin 3) (i : Fin (3 * k)) (hi : (i : ℕ) < k)
    (j : Fin (3 * k)) :
    (C e * (boxMatrix C (fun _ => k))⁻¹) i j =
      if (e : ℕ) * k + (i : ℕ) = j then 1 else 0 := by
  have hrow := box_kkk_row k C e i hi
  have : (C e * (boxMatrix C (fun _ => k))⁻¹) i j =
      (boxMatrix C (fun _ => k) * (boxMatrix C (fun _ => k))⁻¹)
        ⟨(e : ℕ) * k + i, by have := e.isLt; nlinarith⟩ j := by
    simp only [mul_apply]
    rw [hrow]
  rw [this, mul_nonsing_inv _ hG, one_apply]
  by_cases h : (e : ℕ) * k + (i : ℕ) = j
  · rw [if_pos (Fin.ext h), if_pos h]
  · rw [if_neg (fun h' => h (congrArg Fin.val h')), if_neg h]

lemma idx_lt (d : Fin 3) (k : ℕ) (hk : 1 ≤ k) : (d : ℕ) * k + (k - 1) < 3 * k := by
  have := d.isLt
  have : (d : ℕ) * k + k ≤ 3 * k := by nlinarith
  omega

/-- `prop:cell` in graph form: the level-`(k-1)` first-offset entries of `𝒫_{k,·}` over a field. -/
lemma P_entry (k : ℕ) (hk : 2 ≤ k)
    (hG : IsUnit (boxMatrix (fun c => (PGen k c).map (Int.cast : ℤ → F)) (fun _ => k)).det)
    (c d : Fin 3) :
    ((fun c => (PGen k c).map (Int.cast : ℤ → F)) c *
        (boxMatrix (fun c => (PGen k c).map (Int.cast : ℤ → F)) (fun _ => k))⁻¹)
      ⟨k, by omega⟩ ⟨(d : ℕ) * k + (k - 1), idx_lt d k (by omega)⟩ =
      -(if c = d then 1 else 0) - (if c + 1 = d then 1 else 0) + (if c + 2 = d then 1 else 0) := by
  set C := fun c => (PGen k c).map (Int.cast : ℤ → F) with hC
  set G := boxMatrix C (fun _ => k)
  set j : Fin (3 * k) := ⟨(d : ℕ) * k + (k - 1), idx_lt d k (by omega)⟩
  set v := G⁻¹ *ᵥ Pi.single j 1
  have hD : ∀ e i, Sep.Dg k e v i = (C e * G⁻¹) i j := by
    intro e i
    show ((PGen k e).map (Int.cast : ℤ → F) *ᵥ (G⁻¹ *ᵥ Pi.single j 1)) i = _
    rw [mulVec_mulVec, mulVec_single_one]
    rfl
  have h := Sep.Dg_geo k hk c v
  simp only [hD] at h
  rw [h]
  have cr := fun e (i : ℕ) (hi : i < k) => cell_rows k C hG e ⟨i, by omega⟩ hi j
  rw [cr c (k - 1) (by omega), cr (c + 1) (k - 1) (by omega), cr (c + 2) (k - 1) (by omega),
    cr (c + 2) (k - 2) (by omega)]
  simp only [j]
  have key : ∀ e : Fin 3, ((e : ℕ) * k + (k - 1) = (d : ℕ) * k + (k - 1)) ↔ e = d := by
    intro e
    constructor
    · intro h; apply Fin.ext
      have : (e : ℕ) * k = (d : ℕ) * k := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    · intro h; rw [h]
  have key2 : ∀ e : Fin 3, ¬ ((e : ℕ) * k + (k - 2) = (d : ℕ) * k + (k - 1)) := by
    intro e h
    have h1 := e.isLt; have h2 := d.isLt
    rcases lt_trichotomy (e : ℕ) (d : ℕ) with h3 | h3 | h3
    · have : (e : ℕ) * k + k ≤ (d : ℕ) * k := by nlinarith
      omega
    · rw [h3] at h; omega
    · have : (d : ℕ) * k + k ≤ (e : ℕ) * k := by nlinarith
      omega
  simp only [key, key2, if_false]
  ring

lemma Flip_entry (k : ℕ) (hk : 2 ≤ k)
    (hG : IsUnit (boxMatrix (fun c => (PGen k c).map (Int.cast : ℤ → F)) (fun _ => k)).det)
    (c d : Fin 3) :
    ((fun c => (PGenFlip k c).map (Int.cast : ℤ → F)) c *
        (boxMatrix (fun c => (PGenFlip k c).map (Int.cast : ℤ → F)) (fun _ => k))⁻¹)
      ⟨k, by omega⟩ ⟨(d : ℕ) * k + (k - 1), idx_lt d k (by omega)⟩ =
      (if c = d then 1 else 0) - (if c + 1 = d then 1 else 0) + (if c + 2 = d then 1 else 0) := by
  rw [box_eq k (by omega)]
  set C := fun c => (PGen k c).map (Int.cast : ℤ → F) with hC
  set G := boxMatrix C (fun _ => k)
  have hrow : ((PGenFlip k c).map (Int.cast : ℤ → F)) ⟨k, by omega⟩ =
      C c ⟨k, by omega⟩ + (2 : F) • C c ⟨k - 1, by omega⟩ := by
    funext l
    simp only [map_apply, hC, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [PGenFlip_row_k k (by omega)]
    push_cast; ring
  have e1 : ((fun c => (PGenFlip k c).map (Int.cast : ℤ → F)) c * G⁻¹)
      ⟨k, by omega⟩ ⟨(d : ℕ) * k + (k - 1), idx_lt d k (by omega)⟩ =
      (C c * G⁻¹) ⟨k, by omega⟩ ⟨(d : ℕ) * k + (k - 1), idx_lt d k (by omega)⟩ +
        2 * (C c * G⁻¹) ⟨k - 1, by omega⟩ ⟨(d : ℕ) * k + (k - 1), idx_lt d k (by omega)⟩ := by
    simp only [mul_apply]
    rw [hrow, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e1, P_entry k hk hG c d, cell_rows k C hG c ⟨k - 1, by omega⟩ (by simp; omega)]
  have key : ((c : ℕ) * k + (k - 1) = (d : ℕ) * k + (k - 1)) ↔ c = d := by
    constructor
    · intro h; apply Fin.ext
      have : (c : ℕ) * k = (d : ℕ) * k := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    · intro h; rw [h]
  simp only [key]
  split_ifs <;> ring

lemma Mtilde_eq {p : ℕ} (k : ℕ) (hk : 1 ≤ k) (C : Fin 3 → Matrix (Fin (3 * k)) (Fin (3 * k)) (ZMod p))
    (c d : Fin 3) :
    Mtilde k C c d = ((C c * (boxMatrix C (fun _ => k))⁻¹) ⟨k, by omega⟩
      ⟨(d : ℕ) * k + (k - 1), idx_lt d k hk⟩).valMinAbs := by
  unfold Mtilde graphBlock ent
  rw [dif_pos ⟨by omega, by omega⟩]
  simp only
  rw [dif_pos ⟨by omega, idx_lt d k hk⟩]
  rfl

lemma vma_one (p : ℕ) (hp : 3 ≤ p) : (1 : ZMod p).valMinAbs = 1 := by
  haveI : NeZero p := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]; refine ⟨by simp, ?_, ?_⟩ <;> push_cast <;> omega

lemma vma_neg_one (p : ℕ) (hp : 3 ≤ p) : (-1 : ZMod p).valMinAbs = -1 := by
  haveI : NeZero p := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]; refine ⟨by simp, ?_, ?_⟩ <;> push_cast <;> omega

theorem sign_cap (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) :
    ∃ v w : Fin (3 * k) → ZMod p, v ≠ w ∧
      cellDist2 p k (PpointFlip p k v) (PpointFlip p k w) < 12 / (p : ℝ) ^ 2 := by
  haveI := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set C' := fun c => (PGenFlip k c).map (Int.cast : ℤ → ZMod p) with hC'
  have hnet : IsNet0 p (3 * k) (digPoint p (3 * k) C') := sign_net p k (by omega) (by omega)
  have hG : IsUnit (boxMatrix (fun c => (PGen k c).map (Int.cast : ℤ → ZMod p)) (fun _ => k)).det := by
    have hmap := boxMatrix_map (Int.castRingHom (ZMod p)) (PGen k) (fun _ => k)
    have : boxMatrix (fun c => (PGen k c).map (Int.cast : ℤ → ZMod p)) (fun _ => k) =
        (boxMatrix (PGen k) (fun _ => k)).map (Int.castRingHom (ZMod p)) := hmap
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rcases P_boxMinor k (by omega) (fun _ => k) (by ring) with h | h <;> rw [h] <;> simp
  have hM : ∀ c : Fin 3, Mtilde k C' c 0 =
      (((if c = 0 then 1 else 0) - (if c + 1 = 0 then 1 else 0) + (if c + 2 = 0 then 1 else 0) : ℤ) :
        ZMod p).valMinAbs := by
    intro c
    rw [Mtilde_eq k (by omega) C' c 0]
    have := Flip_entry (F := ZMod p) k hk hG c 0
    simp only [Fin.val_zero, zero_mul, zero_add] at this ⊢
    rw [this]
    push_cast
    rfl
  have h0 : Mtilde k C' 0 0 = 1 := by rw [hM]; simp; exact vma_one p hp3
  have h1 : Mtilde k C' (0 + 1) 0 = 1 := by
    rw [hM]; simp [show (1 : Fin 3) + 2 = 0 from rfl]; exact vma_one p hp3
  have h2 : Mtilde k C' (0 + 2) 0 = -1 := by
    rw [hM]; simp [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 ≠ 0 by decide]
    exact vma_neg_one p hp3
  obtain ⟨v, w, hvw, hlt⟩ := ceil_pos p k hp hp2 hk C' hnet 0 (by rw [h0])
  refine ⟨v, w, hvw, lt_of_lt_of_eq hlt ?_⟩
  rw [h0, h1, h2]
  norm_num

/-- `rem:sign`: over any field, the flip changes only the entry `(Φ_cc)_{0,k-1}` of the graph
form (by `+2`, from `-1` to `+1`). -/
theorem sign_graph (k : ℕ) (hk : 2 ≤ k) (c d : Fin 3) (r : Fin (2 * k)) (l : Fin k) :
    graphBlock k (fun c => (PGenFlip k c).map (Int.cast : ℤ → F)) c d r l =
      graphBlock k (fun c => (PGen k c).map (Int.cast : ℤ → F)) c d r l +
        (if (r : ℕ) = 0 ∧ d = c ∧ (l : ℕ) = k - 1 then 2 else 0) := by
  have hG : IsUnit (boxMatrix (fun c => (PGen k c).map (Int.cast : ℤ → F)) (fun _ => k)).det := by
    have hmap := boxMatrix_map (Int.castRingHom F) (PGen k) (fun _ => k)
    have : boxMatrix (fun c => (PGen k c).map (Int.cast : ℤ → F)) (fun _ => k) =
        (boxMatrix (PGen k) (fun _ => k)).map (Int.castRingHom F) := hmap
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rcases P_boxMinor k (by omega) (fun _ => k) (by ring) with h | h <;> rw [h] <;> simp
  unfold graphBlock ent
  have hl : (d : ℕ) * k + (l : ℕ) < 3 * k := by
    have := d.isLt; have := l.isLt
    have : (d : ℕ) * k + k ≤ 3 * k := by nlinarith
    omega
  rw [dif_pos ⟨by have := r.isLt; omega, hl⟩, dif_pos ⟨by have := r.isLt; omega, hl⟩, box_eq k (by omega)]
  set C := fun c => (PGen k c).map (Int.cast : ℤ → F) with hC
  set G := boxMatrix C (fun _ => k)
  have hrow : ((PGenFlip k c).map (Int.cast : ℤ → F)) ⟨k + r, by have := r.isLt; omega⟩ =
      C c ⟨k + r, by have := r.isLt; omega⟩ +
        (if (r : ℕ) = 0 then (2 : F) • C c ⟨k - 1, by omega⟩ else 0) := by
    funext j
    simp only [map_apply, hC, Pi.add_apply]
    rw [PGenFlip_eq k (by omega), Nf_mul_apply k (by omega)]
    by_cases hr : (r : ℕ) = 0
    · have hkr : ((⟨k + r, by have := r.isLt; omega⟩ : Fin (3 * k)) : ℕ) = k := by simp; omega
      rw [if_pos hkr, if_pos hr]
      simp [smul_eq_mul]
    · rw [if_neg (by simp; omega), if_neg hr]; simp
  simp only [mul_apply]
  rw [hrow]
  by_cases hr : (r : ℕ) = 0
  · simp only [if_pos hr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    congr 1
    have := cell_rows k C hG c ⟨k - 1, by omega⟩ (by simp; omega) ⟨(d : ℕ) * k + l, hl⟩
    simp only [mul_apply] at this
    rw [show ∀ (a b : Fin (3 * k) → F), ∑ j, 2 * a j * b j = 2 * ∑ j, a j * b j from
      fun a b => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, this]
    · have key : ((c : ℕ) * k + (k - 1) = (d : ℕ) * k + l) ↔ (d = c ∧ (l : ℕ) = k - 1) := by
        constructor
        · intro h
          have hl' := l.isLt
          have hc := c.isLt; have hd := d.isLt
          rcases lt_trichotomy (c : ℕ) (d : ℕ) with h3 | h3 | h3
          · have : (c : ℕ) * k + k ≤ (d : ℕ) * k := by nlinarith
            omega
          · exact ⟨Fin.ext h3.symm, by rw [h3] at h; omega⟩
          · have : (d : ℕ) * k + k ≤ (c : ℕ) * k := by nlinarith
            omega
        · rintro ⟨h1, h2⟩; rw [h1, h2]
      simp only [key, and_true, true_and, hr]
      split_ifs <;> simp
  · simp only [if_neg hr, Pi.add_apply, Pi.zero_apply, zero_mul, add_zero, Finset.sum_const_zero]
    simp [hr]

end Sign

end

end Z3Net.Proofs

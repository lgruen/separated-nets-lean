module
public import Mathlib
public import Z3Net.S1Net

@[expose] public section

/-!
# Entry S1, part 4: the skeleton row of the frame in graph form, the gauge `Dm`, `S1_net`
-/

namespace Z3NetS1.Proofs

open Finset Matrix

lemma blk_le (a b K : ℕ) (h : a / K = b / K) (ha : a % K ≤ b % K) : a ≤ b := by
  rw [← Nat.div_add_mod a K, ← Nat.div_add_mod b K, h]; omega

lemma blk_eq (a b K : ℕ) (h : a / K = b / K) (ha : a % K = b % K) : a = b := by
  rw [← Nat.div_add_mod a K, ← Nat.div_add_mod b K, h, ha]

section Net2

variable (s k : ℕ)

local notation "MM" => s * k + (s - 1)

lemma mm_eq (hs : 0 < s) : MM = (s - 1) * (k + 1) + k := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

/-- The skeleton coordinate `z = s - 1`. -/
def zc (hs : 0 < s) : Fin s := ⟨s - 1, by omega⟩

/-- Last-level digit of a full block. -/
def LF (r : ℕ) : Prop := r % (k + 1) = k ∧ r / (k + 1) + 1 < s

instance (r : ℕ) : Decidable (LF s k r) := by unfold LF; infer_instance

lemma skRow_LF (ρ col : ℕ) : skRow s k ρ col = if LF s k col then ρ ^ (col / (k + 1) + 1) else 0 := rfl

variable (p : ℕ)

/-- `ψ = (row k of reading z) · Bm⁻¹`: the frame's skeleton row in graph form. -/
noncomputable def psi (hs : 0 < s) (hk : k < MM) : Fin MM → ZMod p :=
  (fun col => Fr s k p (zc s hs) ⟨k, hk⟩ col) ᵥ* (Bm s k p hs)⁻¹

/-- The column gauge. -/
noncomputable def Dm (hs : 0 < s) (hk : k < MM) (ρ : ℕ) : Matrix (Fin MM) (Fin MM) (ZMod p) :=
  fun r col =>
    if LF s k r then
      (if col = r then ((ρ ^ ((r : ℕ) / (k + 1) + 1) : ℕ) : ZMod p) * (psi s k p hs hk r)⁻¹
       else if (col : ℕ) / (k + 1) = (r : ℕ) / (k + 1) ∧ (col : ℕ) < r then
         -(psi s k p hs hk col) * (psi s k p hs hk r)⁻¹ else 0)
    else if col = r then 1 else 0

lemma depth_z (hs : 0 < s) : depth s k (zc s hs) = k := by
  unfold depth zc; simp only; rw [if_neg (by omega)]

lemma LF_block (hs : 0 < s) (r : ℕ) (hr : r < MM) (h : LF s k r) :
    cOf s k hs r = ⟨r / (k + 1), by have := h.2; omega⟩ ∧ jOf s k hs r = k ∧
      depth s k (cOf s k hs r) = k + 1 := by
  have hc : cOf s k hs r = ⟨r / (k + 1), by have := h.2; omega⟩ := by
    apply Fin.ext; unfold cOf; simp only; have := h.2; omega
  refine ⟨hc, ?_, ?_⟩
  · unfold jOf; rw [hc]; simp only
    have := Nat.div_add_mod r (k + 1); have := h.1
    rw [Nat.mul_comm]; omega
  · rw [hc]; unfold depth; simp only; rw [if_pos h.2]

/-- **(N1)**: the frame's skeleton row has nonzero last-level entries on every full block. -/
lemma psi_ne [Fact p.Prime] (hs : 0 < s) (hk : k < MM) (hps : s - 2 < p) (r : Fin MM)
    (hr : LF s k r) : psi s k p hs hk r ≠ 0 := by
  intro h0
  obtain ⟨hcr, hjr, hdr⟩ := LF_block s k hs r r.isLt hr
  set d0 := cOf s k hs r with hd0
  have hrk := (off_jOf s k hs r r.isLt).1
  rw [hjr] at hrk
  have hdz : d0 ≠ zc s hs := by
    intro h; rw [hcr] at h; have := congrArg Fin.val h; simp [zc] at this; have := hr.2; omega
  set e : Fin MM → ZMod p := Pi.single r 1 with he
  set n0 := (Bm s k p hs)⁻¹ *ᵥ e with hn0
  have hBn : Bm s k p hs *ᵥ n0 = e := by
    rw [hn0, mulVec_mulVec, mul_nonsing_inv _ (Bm_det s k p hs hps), one_mulVec]
  let K' : Fin s → ℕ := fun c => if c = d0 then k else if c = zc s hs then k + 1 else depth s k c
  have hK' : ∑ c, K' c = MM := by
    rw [← depth_sum s k hs, ← Finset.add_sum_erase _ _ (mem_univ d0),
      ← Finset.add_sum_erase _ _ (mem_univ d0),
      ← Finset.add_sum_erase _ _ (mem_erase.2 ⟨hdz.symm, mem_univ (zc s hs)⟩),
      ← Finset.add_sum_erase _ _ (mem_erase.2 ⟨hdz.symm, mem_univ (zc s hs)⟩)]
    have hrest : ∑ x ∈ ((univ.erase d0).erase (zc s hs)), K' x =
        ∑ x ∈ ((univ.erase d0).erase (zc s hs)), depth s k x := by
      refine sum_congr rfl fun c hc => ?_
      simp only [mem_erase] at hc
      simp only [K', if_neg hc.2.1, if_neg hc.1]
    rw [hrest]
    simp only [K', if_pos rfl, if_neg hdz.symm]
    rw [hdr, depth_z s k hs]; simp; ring
  have hvan : ∀ c (i : Fin MM), (i : ℕ) < K' c → (Fr s k p c *ᵥ n0) i = 0 := by
    intro c i hi
    by_cases hic : (i : ℕ) < depth s k c
    · rw [← Bm_mulVec s k p hs c i hic, hBn, he]
      rw [Pi.single_apply, if_neg]
      intro heq
      have hv := congrArg Fin.val heq
      simp only at hv
      have h1 : c = d0 := by rw [hd0, ← hv, cOf_off s k hs c i hic]
      have h2 : (i : ℕ) = k := by
        have := jOf_off s k hs c i hic
        rw [hv] at this; omega
      simp only [K', if_pos h1] at hi
      omega
    · have hcz : c = zc s hs := by
        by_contra hcz
        by_cases hcd : c = d0
        · simp only [K', if_pos hcd] at hi; rw [hcd, hdr] at hic; omega
        · simp only [K', if_neg hcd, if_neg hcz] at hi; exact hic hi
      have hcd : c ≠ d0 := fun h => hdz (h ▸ hcz)
      simp only [K', if_neg hcd, if_pos hcz] at hi
      rw [hcz, depth_z s k hs] at hic
      have hik : i = ⟨k, hk⟩ := Fin.ext (by simp only; omega)
      rw [hik, hcz]
      have : (Fr s k p (zc s hs) *ᵥ n0) ⟨k, hk⟩ =
          (fun col => Fr s k p (zc s hs) ⟨k, hk⟩ col) ⬝ᵥ ((Bm s k p hs)⁻¹ *ᵥ e) := rfl
      rw [this, dotProduct_mulVec, he, dotProduct_single]
      change psi s k p hs hk r * 1 = 0
      rw [h0, zero_mul]
  have := frame_kernel s k p hs hps K' hK' n0 hvan
  have h1 : e r = 1 := by rw [he, Pi.single_eq_same]
  rw [← hBn, this, mulVec_zero] at h1
  exact zero_ne_one h1

end Net2

end Z3NetS1.Proofs

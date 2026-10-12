module
public import Z3Net.KNNetGen

@[expose] public section

/-!
# The realization theorem (KN entry, `KN1_net` / `KN2_net`)

Given a `t = 0` graph form `G` with depths `K`, a *row gauge* `L` (lower triangular on the
geometric rows of each coordinate), a *column gauge* `U` (upper triangular on the needed window
columns, in the window index `i`, `i = 0` the last level) and block factors `μ`, and target values
`Tgt c d ρ i` for the geometric rows of `c` on the last `P d` levels of the cell of `d` such that

* `Tgt = μ · L · W · U` on the needed columns `i < P d - 1` (`W` = the geometric rows of `G`),
* every pivot block `(Tgt c d ρ i)_{(c,ρ), i < P d}` is invertible,

`realize` produces a `t = 0` graph form `C` whose geometric rows are `Tgt` on the last `P d` levels
of every other cell and `0` above, and whose offset rows take prescribed values `Own` on their own
cell.  The proof: row gauge (`T0_rows`), then one column move (`T0_cols`) per cell -- the levels
above the pivot levels are cleared with the (invertible, `pivot_inj`) pivot matrix, the needed
pivot columns are transformed by `U`, and the top pivot column is solved for the target (its
leading coefficient is nonzero because the target pivot block is invertible) -- then block
scalings and the own cells (`T0_transfer`).
-/

namespace Z3NetKN.Realize

open Matrix Finset Z3NetKN.Frame

/-- Shape data: depths `K`, numbers `g c ≤ 2` of geometric rows, pivot counts `P d` and an
enumeration `rw d a`, `a < P d`, of the geometric rows `(c, ρ)` of the coordinates `c ≠ d`. -/
structure Setup (m : ℕ) where
  K : Fin 3 → ℕ
  hK : K 0 + K 1 + K 2 = m
  g : Fin 3 → ℕ
  P : Fin 3 → ℕ
  rw : Fin 3 → ℕ → Fin 3 × ℕ
  hP1 : ∀ d, 1 ≤ P d
  hP4 : ∀ d, P d ≤ 4
  hPK : ∀ d, P d ≤ K d
  hg : ∀ c, g c ≤ 2
  hbox : ∀ d : Fin 3, (fun c => if c = d then K d - P d else K c + g c) 0 +
      (fun c => if c = d then K d - P d else K c + g c) 1 +
      (fun c => if c = d then K d - P d else K c + g c) 2 = m
  hrw : ∀ d a, a < P d → (rw d a).1 ≠ d ∧ (rw d a).2 < g (rw d a).1
  hrw_surj : ∀ d c ρ, c ≠ d → ρ < g c → ∃ a, a < P d ∧ rw d a = (c, ρ)

variable {F : Type*} [Field F] {m : ℕ}

/-- Total accessors of the gauge matrices. -/
def Le (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) (c : Fin 3) (a b : ℕ) : F :=
  if h : a < 2 ∧ b < 2 then L c ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def Ue (U : Fin 3 → Matrix (Fin 3) (Fin 3) F) (d : Fin 3) (a b : ℕ) : F :=
  if h : a < 3 ∧ b < 3 then U d ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

/-- The window matrix: geometric row `ρ` of `c` on window column `i` of `d`. -/
def Wm (K : Fin 3 → ℕ) (G : Fin 3 → Matrix (Fin m) (Fin m) F) (c d : Fin 3) :
    Matrix (Fin 2) (Fin 3) F :=
  fun ρ i => ent (G c) (K c + ρ) (offK K d + (K d - 1 - i))

section

variable (S : Setup m)

lemma Setup.hgm (c : Fin 3) : S.K c + S.g c ≤ m := by
  have := S.hK
  fin_cases c
  · have h := S.hbox 1; simp at h ⊢; omega
  · have h := S.hbox 2; simp at h ⊢; omega
  · have h := S.hbox 0; simp at h ⊢; omega

/-- Column of window level `i` of the cell of `d`. -/
def pos (d : Fin 3) (i : ℕ) : ℕ := offK S.K d + (S.K d - 1 - i)

lemma pos_lt (d : Fin 3) (i : ℕ) (hi : i < S.P d) : pos S d i < m :=
  offK_lt S.K S.hK d _ (by have := S.hPK d; omega)

lemma blk_pos (d : Fin 3) (i : ℕ) (hi : i < S.P d) :
    blk S.K (pos S d i) = d ∧ lev S.K (pos S d i) = S.K d - 1 - i :=
  blk_of S.K d _ (by have := S.hPK d; omega)

/-! ### Step 1: the row gauge -/

def Lam (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) (c : Fin 3) : Matrix (Fin m) (Fin m) F :=
  fun i j =>
    if (i : ℕ) < S.K c ∨ S.K c + S.g c ≤ i then (if i = j then 1 else 0)
    else ∑ ρ' ∈ range (S.g c), if (j : ℕ) = S.K c + ρ' then Le L c ((i : ℕ) - S.K c) ρ' else 0

def G1 (G : Fin 3 → Matrix (Fin m) (Fin m) F) (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) :
    Fin 3 → Matrix (Fin m) (Fin m) F :=
  fun c => Lam S L c * G c

variable {S}

lemma Lam_low (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) (hL : ∀ c, L c 0 1 = 0) (c : Fin 3)
    (i j : Fin m) (hij : i < j) : Lam S L c i j = 0 := by
  simp only [Lam]
  by_cases h : (i : ℕ) < S.K c ∨ S.K c + S.g c ≤ i
  · rw [if_pos h, if_neg (ne_of_lt hij)]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro ρ' hρ'
    split_ifs with hj
    · have hg := S.hg c
      simp at hρ'
      have : (i : ℕ) < j := hij
      simp only [Le]
      rw [dif_pos ⟨by omega, by omega⟩]
      have e1 : (⟨(i : ℕ) - S.K c, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp; omega)
      have e2 : (⟨ρ', by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
      rw [e1, e2, hL]
    · rfl

lemma Lam_diag (L : Fin 3 → Matrix (Fin 2) (Fin 2) F)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0) (c : Fin 3) (i : Fin m) :
    Lam S L c i i ≠ 0 := by
  simp only [Lam]
  by_cases h : (i : ℕ) < S.K c ∨ S.K c + S.g c ≤ i
  · rw [if_pos h]; simp
  · rw [if_neg h]
    push_neg at h
    rw [Finset.sum_eq_single ((i : ℕ) - S.K c)]
    · rw [if_pos (by omega)]
      have hg := S.hg c
      simp only [Le]
      rw [dif_pos ⟨by omega, by omega⟩]
      exact hLd c _ (by simp; omega)
    · intro b _ hb
      rw [if_neg (by omega)]
    · intro hb; simp at hb; omega

lemma G1_T0 {G : Fin 3 → Matrix (Fin m) (Fin m) F} (hG : T0 G)
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) (hL : ∀ c, L c 0 1 = 0)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0) : T0 (G1 S G L) :=
  T0_rows hG (Lam S L) (Lam_low L hL) (Lam_diag L hLd)

lemma G1_GF {G : Fin 3 → Matrix (Fin m) (Fin m) F} (hGF : IsGF G S.K)
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) : IsGF (G1 S G L) S.K := by
  intro c j col hj
  simp only [G1, mul_apply, Lam]
  rw [Finset.sum_eq_single j]
  · rw [if_pos (Or.inl hj), if_pos rfl, one_mul, hGF c j col hj]
  · intro b _ hb
    rw [if_pos (Or.inl hj), if_neg (Ne.symm hb), zero_mul]
  · simp

/-- Geometric rows of `G1`. -/
lemma G1_geo (G : Fin 3 → Matrix (Fin m) (Fin m) F) (L : Fin 3 → Matrix (Fin 2) (Fin 2) F)
    (hL : ∀ c, L c 0 1 = 0) (c : Fin 3) (ρ : Fin 2) (hρ : (ρ : ℕ) < S.g c) (n : ℕ) :
    ent (G1 S G L c) (S.K c + ρ) n = ∑ ρ' : Fin 2, L c ρ ρ' * ent (G c) (S.K c + ρ') n := by
  have hgm := S.hgm c
  have hg := S.hg c
  by_cases hn : n < m
  · have hi : S.K c + (ρ : ℕ) < m := by omega
    unfold ent
    rw [dif_pos ⟨hi, hn⟩]
    simp only [G1, mul_apply, Lam]
    simp only [show ¬(S.K c + (ρ : ℕ) < S.K c ∨ S.K c + S.g c ≤ S.K c + (ρ : ℕ)) by omega, if_false]
    have hq : ∀ ρ' ∈ range (S.g c), S.K c + ρ' < m := by intro ρ' h; simp at h; omega
    rw [sum_pick_left (fun j => G c j ⟨n, hn⟩) (fun ρ' => S.K c + ρ') _ hq]
    simp only [Fin.isValue, add_tsub_cancel_left]
    rw [Fin.sum_univ_two]
    have hfe : ∀ ρ' : ℕ, ρ' < S.g c → fe (fun j => G c j ⟨n, hn⟩) (S.K c + ρ') =
        (if h : S.K c + ρ' < m ∧ n < m then G c ⟨S.K c + ρ', h.1⟩ ⟨n, h.2⟩ else 0) := by
      intro ρ' h; simp [fe, show S.K c + ρ' < m by omega, hn]
    interval_cases hgc : S.g c
    · omega
    · have hρ0 : ρ = 0 := Fin.ext (by omega)
      subst hρ0
      simp only [Finset.sum_range_one, Le]
      rw [dif_pos ⟨by omega, by omega⟩, hfe 0 (by omega), hL]
      simp
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Le]
      rw [dif_pos ⟨by omega, by omega⟩, dif_pos ⟨by omega, by omega⟩, hfe 0 (by omega),
        hfe 1 (by omega)]
      simp
  · unfold ent
    rw [dif_neg (by omega)]
    simp [hn]

/-! ### Step 2: pivot matrices, clearing and the free column -/

variable (S)

/-- Geometric entry of `G1` on pivot column `i` of `d`. -/
def A1 (G : Fin 3 → Matrix (Fin m) (Fin m) F) (L : Fin 3 → Matrix (Fin 2) (Fin 2) F)
    (c : Fin 3) (ρ : ℕ) (d : Fin 3) (i : ℕ) : F :=
  ent (G1 S G L c) (S.K c + ρ) (pos S d i)

/-- The padded pivot matrix of `d`. -/
def Ap (G : Fin 3 → Matrix (Fin m) (Fin m) F) (L : Fin 3 → Matrix (Fin 2) (Fin 2) F)
    (d : Fin 3) : Matrix (Fin 4) (Fin 4) F :=
  fun a i => if (a : ℕ) < S.P d ∧ (i : ℕ) < S.P d then
      A1 S G L (S.rw d a).1 (S.rw d a).2 d i else if a = i then 1 else 0

/-- Extension of a `Fin 4` vector by zero. -/
def ex4 (x : Fin 4 → F) (i : ℕ) : F := if h : i < 4 then x ⟨i, h⟩ else 0

variable {S}

/-- Row `a < P d` of a padded matrix times a vector. -/
lemma padded_row (P : ℕ) (hP : P ≤ 4) (f : ℕ → ℕ → F) (x : Fin 4 → F) (a : Fin 4)
    (ha : (a : ℕ) < P) :
    ((fun a i : Fin 4 => if (a : ℕ) < P ∧ (i : ℕ) < P then f a i else if a = i then 1 else 0 :
        Matrix (Fin 4) (Fin 4) F) *ᵥ x) a = ∑ i ∈ range P, f a i * ex4 x i := by
  simp only [mulVec, dotProduct]
  set f' : ℕ → F := fun i : ℕ =>
    (if (a : ℕ) < P ∧ i < P then f a i else if (a : ℕ) = i then 1 else 0) * ex4 x i with hf'
  have hs : ∀ i : Fin 4, (if (a : ℕ) < P ∧ (i : ℕ) < P then f a i else if a = i then 1 else 0) * x i =
      f' i := by
    intro i; simp [hf', ex4, Fin.ext_iff]
  rw [Finset.sum_congr rfl (fun i _ => hs i), Fin.sum_univ_eq_sum_range f' 4,
    ← Finset.sum_range_add_sum_Ico _ hP]
  rw [Finset.sum_eq_zero (s := Ico P 4)]
  · rw [add_zero]
    apply Finset.sum_congr rfl
    intro i hi; simp at hi
    simp only [hf']
    rw [if_pos ⟨ha, hi⟩]
  · intro i hi; simp at hi
    simp only [hf']
    rw [if_neg (by omega), if_neg (by omega), zero_mul]

/-- Row `a ≥ P` of a padded matrix times a vector. -/
lemma padded_row_hi (P : ℕ) (f : ℕ → ℕ → F) (x : Fin 4 → F) (a : Fin 4) (ha : P ≤ (a : ℕ)) :
    ((fun a i : Fin 4 => if (a : ℕ) < P ∧ (i : ℕ) < P then f a i else if a = i then 1 else 0 :
        Matrix (Fin 4) (Fin 4) F) *ᵥ x) a = x a := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single a]
  · rw [if_neg (by omega), if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg (by omega), if_neg (Ne.symm hb), zero_mul]
  · simp

end

lemma Ap_row (S : Setup m) (G : Fin 3 → Matrix (Fin m) (Fin m) F)
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) (d : Fin 3) (x : Fin 4 → F) (a : Fin 4)
    (ha : (a : ℕ) < S.P d) :
    (Ap S G L d *ᵥ x) a = ∑ i ∈ range (S.P d), A1 S G L (S.rw d a).1 (S.rw d a).2 d i * ex4 x i :=
  padded_row (S.P d) (S.hP4 d) (fun a i => A1 S G L (S.rw d a).1 (S.rw d a).2 d i) x a ha

lemma Ap_row_hi (S : Setup m) (G : Fin 3 → Matrix (Fin m) (Fin m) F)
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) (d : Fin 3) (x : Fin 4 → F) (a : Fin 4)
    (ha : S.P d ≤ (a : ℕ)) : (Ap S G L d *ᵥ x) a = x a :=
  padded_row_hi (S.P d) (fun a i => A1 S G L (S.rw d a).1 (S.rw d a).2 d i) x a ha

lemma sum_fin3 (h : Fin 3 → F) :
    ∑ b, h b = ∑ j ∈ range 3, (if hj : j < 3 then h ⟨j, hj⟩ else 0) := by
  simp [Finset.sum_range_succ, Fin.sum_univ_three]

noncomputable section Solve

variable {S : Setup m} {G : Fin 3 → Matrix (Fin m) (Fin m) F}
  {L : Fin 3 → Matrix (Fin 2) (Fin 2) F}

lemma Ap_inj (hG : T0 G) (hGF : IsGF G S.K) (hL : ∀ c, L c 0 1 = 0)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0) (d : Fin 3) (x : Fin 4 → F)
    (hx : Ap S G L d *ᵥ x = 0) : x = 0 := by
  have hG1 := G1_T0 (S := S) hG L hL hLd
  have hGF1 := G1_GF (S := S) hGF L
  have h1 : ∀ i < S.P d, ex4 x i = 0 := by
    refine pivot_inj S.hK hG1 hGF1 S.g d (S.P d) (S.hPK d)
      (fun c => if c = d then S.K d - S.P d else S.K c + S.g c) (S.hbox d) (by simp)
      (by intro c hc; simp [hc]) (ex4 x) ?_
    intro c hc ρ hρ
    obtain ⟨a, ha, hra⟩ := S.hrw_surj d c ρ hc hρ
    have := congrFun hx ⟨a, by have := S.hP4 d; omega⟩
    rw [Ap_row S G L d x _ ha] at this
    simp only [hra, A1, pos] at this
    exact this
  funext i
  by_cases hi : (i : ℕ) < S.P d
  · have := h1 i hi; simpa [ex4] using this
  · have := congrFun hx i
    rw [Ap_row_hi S G L d x i (by omega)] at this
    exact this

lemma Ap_unit (hG : T0 G) (hGF : IsGF G S.K) (hL : ∀ c, L c 0 1 = 0)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0) (d : Fin 3) :
    IsUnit (Ap S G L d) := by
  rw [← mulVec_injective_iff_isUnit]
  intro v w hvw
  have := Ap_inj hG hGF hL hLd d (v - w) (by rw [mulVec_sub, hvw, sub_self])
  exact sub_eq_zero.mp this

lemma mulVec_inv_solve (M : Matrix (Fin 4) (Fin 4) F) (hM : IsUnit M) (b : Fin 4 → F) :
    M *ᵥ (M⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hM), one_mulVec]

variable (S G L)

/-- Right-hand side for clearing level `l` of the cell of `d`. -/
def bkill (d : Fin 3) (l : ℕ) : Fin 4 → F := fun a =>
  if (a : ℕ) < S.P d then
    ent (G1 S G L (S.rw d a).1) (S.K (S.rw d a).1 + (S.rw d a).2) (offK S.K d + l) else 0

def xkill (d : Fin 3) (l : ℕ) : Fin 4 → F := -((Ap S G L d)⁻¹ *ᵥ bkill S G L d l)

/-- Right-hand side for the top pivot column. -/
def bfree (μ : Fin 3 → Fin 3 → F) (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F) (d : Fin 3) : Fin 4 → F :=
  fun a => if (a : ℕ) < S.P d then
    (μ (S.rw d a).1 d)⁻¹ * Tgt (S.rw d a).1 d (S.rw d a).2 (S.P d - 1) else 0

def wfree (μ : Fin 3 → Fin 3 → F) (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F) (d : Fin 3) : Fin 4 → F :=
  (Ap S G L d)⁻¹ *ᵥ bfree S μ Tgt d

/-- The full pivot-column gauge: `U` on the needed columns, the solved column on the top one. -/
def Uh (U : Fin 3 → Matrix (Fin 3) (Fin 3) F) (μ : Fin 3 → Fin 3 → F)
    (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F) (d : Fin 3) (i' i : ℕ) : F :=
  if i + 1 < S.P d then Ue U d i' i
  else if i + 1 = S.P d then ex4 (wfree S G L μ Tgt d) i' else 0

variable {S G L}

lemma xkill_spec (hG : T0 G) (hGF : IsGF G S.K) (hL : ∀ c, L c 0 1 = 0)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0) (d : Fin 3) (l : ℕ)
    (c : Fin 3) (hc : c ≠ d) (ρ : ℕ) (hρ : ρ < S.g c) :
    ∑ i ∈ range (S.P d), A1 S G L c ρ d i * ex4 (xkill S G L d l) i =
      -ent (G1 S G L c) (S.K c + ρ) (offK S.K d + l) := by
  obtain ⟨a, ha, hra⟩ := S.hrw_surj d c ρ hc hρ
  have hsol : Ap S G L d *ᵥ xkill S G L d l = -bkill S G L d l := by
    rw [xkill, mulVec_neg, mulVec_inv_solve _ (Ap_unit hG hGF hL hLd d)]
  have := congrFun hsol ⟨a, by have := S.hP4 d; omega⟩
  rw [Ap_row S G L d _ _ ha] at this
  simp only [hra, Pi.neg_apply, bkill, if_pos ha] at this
  exact this

lemma wfree_spec (hG : T0 G) (hGF : IsGF G S.K) (hL : ∀ c, L c 0 1 = 0)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0) (μ : Fin 3 → Fin 3 → F)
    (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F) (d : Fin 3)
    (c : Fin 3) (hc : c ≠ d) (ρ : ℕ) (hρ : ρ < S.g c) :
    ∑ i ∈ range (S.P d), A1 S G L c ρ d i * ex4 (wfree S G L μ Tgt d) i =
      (μ c d)⁻¹ * Tgt c d ρ (S.P d - 1) := by
  obtain ⟨a, ha, hra⟩ := S.hrw_surj d c ρ hc hρ
  have hsol : Ap S G L d *ᵥ wfree S G L μ Tgt d = bfree S μ Tgt d := by
    rw [wfree, mulVec_inv_solve _ (Ap_unit hG hGF hL hLd d)]
  have := congrFun hsol ⟨a, by have := S.hP4 d; omega⟩
  rw [Ap_row S G L d _ _ ha] at this
  simp only [hra, bfree, if_pos ha] at this
  exact this

/-- Sums over `range P` of terms vanishing beyond `i`. -/
lemma sum_range_trunc (h : ℕ → F) (i n : ℕ) (hi : i < n) (hz : ∀ j, i < j → h j = 0) :
    ∑ j ∈ range n, h j = ∑ j ∈ range (i + 1), h j := by
  symm
  apply Finset.sum_subset
  · intro j hj; simp at hj ⊢; omega
  · intro j hj hj'; simp at hj hj'; exact hz j (by omega)

/-- **Key identity**: the target on every pivot column is `μ · (geometric rows of `G1`) · Uh`. -/
lemma key_identity (hG : T0 G) (hGF : IsGF G S.K) (hL : ∀ c, L c 0 1 = 0)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0)
    (U : Fin 3 → Matrix (Fin 3) (Fin 3) F) (hU : ∀ d (a b : Fin 3), b < a → U d a b = 0)
    (μ : Fin 3 → Fin 3 → F) (hμ : ∀ c d, c ≠ d → μ c d ≠ 0)
    (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F)
    (hW : ∀ c d, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < S.g c → (i : ℕ) + 1 < S.P d →
      Tgt c d ρ i = μ c d * (L c * Wm S.K G c d * U d) ρ i)
    (c d : Fin 3) (hc : c ≠ d) (ρ : ℕ) (hρ : ρ < S.g c) (i : ℕ) (hi : i < S.P d) :
    Tgt c d ρ i = μ c d * ∑ i' ∈ range (S.P d), A1 S G L c ρ d i' * Uh S G L U μ Tgt d i' i := by
  by_cases hi1 : i + 1 < S.P d
  · have hg := S.hg c
    have hP4 := S.hP4 d
    have h3 : i < 3 := by omega
    have := hW c d hc ⟨ρ, by omega⟩ ⟨i, h3⟩ hρ hi1
    simp only at this
    rw [this]
    congr 1
    simp only [Uh, if_pos hi1]
    rw [sum_range_trunc _ i _ hi (by
      intro j hj
      simp only [Ue]
      split_ifs with h
      · rw [hU d ⟨j, h.1⟩ ⟨i, h.2⟩ (by simp; omega), mul_zero]
      · rw [mul_zero])]
    rw [mul_apply, sum_fin3, sum_range_trunc _ i 3 h3 (by
      intro j hj
      split_ifs with h
      · rw [hU d ⟨j, h⟩ ⟨i, h3⟩ (by simp; omega), mul_zero]
      · rfl)]
    apply Finset.sum_congr rfl
    intro j hj
    simp at hj
    rw [dif_pos (by omega : j < 3)]
    simp only [A1, Ue, dif_pos (And.intro (show j < 3 by omega) h3)]
    rw [G1_geo G L hL c ⟨ρ, by omega⟩ hρ, mul_apply]
    simp only [Wm, pos]
  · have hi2 : i + 1 = S.P d := by omega
    simp only [Uh, if_neg hi1, if_pos hi2]
    rw [wfree_spec hG hGF hL hLd μ Tgt d c hc ρ hρ, ← mul_assoc, mul_inv_cancel₀ (hμ c d hc),
      one_mul, show S.P d - 1 = i by omega]

/-- The padded target pivot block of `d`. -/
def Tpad (S : Setup m) (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F) (d : Fin 3) : Matrix (Fin 4) (Fin 4) F :=
  fun a i => if (a : ℕ) < S.P d ∧ (i : ℕ) < S.P d then
    Tgt (S.rw d a).1 d (S.rw d a).2 i else if a = i then 1 else 0

lemma Uh_upper (U : Fin 3 → Matrix (Fin 3) (Fin 3) F) (hU : ∀ d (a b : Fin 3), b < a → U d a b = 0)
    (μ : Fin 3 → Fin 3 → F) (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F) (d : Fin 3) (i' i : ℕ)
    (hi' : i' < S.P d) (h : Uh S G L U μ Tgt d i' i ≠ 0) : i' ≤ i := by
  simp only [Uh] at h
  split_ifs at h with h1 h2
  · simp only [Ue] at h
    split_ifs at h with h3
    · by_contra hlt
      exact h (hU d ⟨i', h3.1⟩ ⟨i, h3.2⟩ (by simp; omega))
    · exact absurd rfl h
  · omega
  · exact absurd rfl h

/-- The solved top pivot coefficient is nonzero (the target pivot block is invertible). -/
lemma wfree_ne (hG : T0 G) (hGF : IsGF G S.K) (hL : ∀ c, L c 0 1 = 0)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0)
    (U : Fin 3 → Matrix (Fin 3) (Fin 3) F) (hU : ∀ d (a b : Fin 3), b < a → U d a b = 0)
    (μ : Fin 3 → Fin 3 → F) (hμ : ∀ c d, c ≠ d → μ c d ≠ 0)
    (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F)
    (hW : ∀ c d, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < S.g c → (i : ℕ) + 1 < S.P d →
      Tgt c d ρ i = μ c d * (L c * Wm S.K G c d * U d) ρ i)
    (hdet : ∀ d, IsUnit (Tpad S Tgt d)) (d : Fin 3) :
    ex4 (wfree S G L μ Tgt d) (S.P d - 1) ≠ 0 := by
  intro h0
  have hP1 := S.hP1 d
  have hP4 := S.hP4 d
  let Uh4 : Matrix (Fin 4) (Fin 4) F := fun a i =>
    if (a : ℕ) < S.P d ∧ (i : ℕ) < S.P d then Uh S G L U μ Tgt d a i else if a = i then 1 else 0
  have htri : Uh4.BlockTriangular id := by
    intro a i hia
    simp only [id] at hia
    simp only [Uh4]
    split_ifs with h1 h2
    · by_contra hne
      have := Uh_upper U hU μ Tgt d a i h1.1 hne
      have : (i : ℕ) < a := hia
      omega
    · exact absurd h2 (ne_of_gt hia)
    · rfl
  have hdet0 : Uh4.det = 0 := by
    rw [Matrix.det_of_upperTriangular htri]
    apply Finset.prod_eq_zero (i := ⟨S.P d - 1, by omega⟩) (Finset.mem_univ _)
    simp only [Uh4]
    rw [if_pos ⟨by simp; omega, by simp; omega⟩]
    simp only [Uh, show S.P d - 1 + 1 = S.P d by omega, if_true, lt_irrefl, if_false]
    exact h0
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  apply hy0
  have hinj := (mulVec_injective_iff_isUnit.2 (hdet d))
  apply hinj
  rw [mulVec_zero]
  funext a
  by_cases ha : (a : ℕ) < S.P d
  · rw [show Tpad S Tgt d = fun a i : Fin 4 => if (a : ℕ) < S.P d ∧ (i : ℕ) < S.P d then
      Tgt (S.rw d a).1 d (S.rw d a).2 i else if a = i then 1 else 0 from rfl,
      padded_row (S.P d) hP4 (fun a i => Tgt (S.rw d a).1 d (S.rw d a).2 i) y a ha]
    have hrw := S.hrw d a ha
    simp only [Pi.zero_apply]
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [key_identity hG hGF hL hLd U hU μ hμ Tgt hW _ d hrw.1 _ hrw.2 i (by simpa using hi)])]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i' hi'
    simp at hi'
    have hrow := congrFun hy ⟨i', by omega⟩
    rw [padded_row (S.P d) hP4 (fun a i => Uh S G L U μ Tgt d a i) y _ (by simpa using hi')] at hrow
    simp only [Pi.zero_apply] at hrow
    have : ∑ i ∈ range (S.P d), μ (S.rw d ↑a).1 d *
        (A1 S G L (S.rw d ↑a).1 (S.rw d ↑a).2 d i' * Uh S G L U μ Tgt d i' i) * ex4 y i =
        μ (S.rw d ↑a).1 d * A1 S G L (S.rw d ↑a).1 (S.rw d ↑a).2 d i' *
          ∑ i ∈ range (S.P d), Uh S G L U μ Tgt d i' i * ex4 y i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hrow, mul_zero]
  · rw [show Tpad S Tgt d = fun a i : Fin 4 => if (a : ℕ) < S.P d ∧ (i : ℕ) < S.P d then
      Tgt (S.rw d a).1 d (S.rw d a).2 i else if a = i then 1 else 0 from rfl,
      padded_row_hi (S.P d) (fun a i => Tgt (S.rw d a).1 d (S.rw d a).2 i) y a (by omega)]
    have := congrFun hy a
    rw [padded_row_hi (S.P d) (fun a i => Uh S G L U μ Tgt d a i) y a (by omega)] at this
    exact this

variable (S G L)

/-- The column move: clearing above the pivot levels, `Uh` on the pivot levels. -/
def Vm (U : Fin 3 → Matrix (Fin 3) (Fin 3) F) (μ : Fin 3 → Fin 3 → F)
    (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F) : Matrix (Fin m) (Fin m) F := fun n' n =>
  if lev S.K n + S.P (blk S.K n) < S.K (blk S.K n) then
    (if n' = n then 1 else 0) + ∑ i ∈ range (S.P (blk S.K n)),
      (if (n' : ℕ) = pos S (blk S.K n) i then ex4 (xkill S G L (blk S.K n) (lev S.K n)) i else 0)
  else ∑ i' ∈ range (S.P (blk S.K n)),
      (if (n' : ℕ) = pos S (blk S.K n) i' then
        Uh S G L U μ Tgt (blk S.K n) i' (S.K (blk S.K n) - 1 - lev S.K n) else 0)

variable {S G L}

lemma Vm_levlow (hG : T0 G) (hGF : IsGF G S.K) (hL : ∀ c, L c 0 1 = 0)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0)
    (U : Fin 3 → Matrix (Fin 3) (Fin 3) F) (hU : ∀ d (a b : Fin 3), b < a → U d a b = 0)
    (hUd : ∀ d (a : Fin 3), (a : ℕ) + 1 < S.P d → U d a a ≠ 0)
    (μ : Fin 3 → Fin 3 → F) (hμ : ∀ c d, c ≠ d → μ c d ≠ 0)
    (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F)
    (hW : ∀ c d, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < S.g c → (i : ℕ) + 1 < S.P d →
      Tgt c d ρ i = μ c d * (L c * Wm S.K G c d * U d) ρ i)
    (hdet : ∀ d, IsUnit (Tpad S Tgt d)) : LevLow S.K (Vm S G L U μ Tgt) := by
  constructor
  · intro n' n hne
    obtain ⟨hl, hpos⟩ := blk_lev S.K S.hK n
    simp only [Vm] at hne
    generalize hd : blk S.K n = d at hl hpos hne ⊢
    generalize hl' : lev S.K n = l at hl hpos hne ⊢
    have := S.hPK d
    by_cases habove : l + S.P d < S.K d
    · rw [if_pos habove] at hne
      by_cases hnn : n' = n
      · subst hnn; exact ⟨hd, le_of_eq hl'.symm⟩
      · rw [if_neg hnn, zero_add] at hne
        obtain ⟨i, hi, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
        simp at hi
        have hpi : (n' : ℕ) = pos S d i := by by_contra h; rw [if_neg h] at hne'; exact hne' rfl
        have := blk_pos S d i hi
        rw [← hpi] at this
        refine ⟨this.1, ?_⟩
        rw [this.2]; omega
    · rw [if_neg habove] at hne
      obtain ⟨i', hi', hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      simp at hi'
      have hpi : (n' : ℕ) = pos S d i' := by by_contra h; rw [if_neg h] at hne'; exact hne' rfl
      rw [if_pos hpi] at hne'
      have hup := Uh_upper U hU μ Tgt d i' _ hi' hne'
      have := blk_pos S d i' hi'
      rw [← hpi] at this
      refine ⟨this.1, ?_⟩
      rw [this.2]; omega
  · intro n
    obtain ⟨hl, hpos⟩ := blk_lev S.K S.hK n
    simp only [Vm]
    generalize hd : blk S.K n = d at hl hpos ⊢
    generalize hl' : lev S.K n = l at hl hpos ⊢
    have := S.hPK d
    have := S.hP4 d
    by_cases habove : l + S.P d < S.K d
    · rw [if_pos habove, Finset.sum_eq_zero]
      · simp
      · intro i hi
        simp at hi
        rw [if_neg]
        intro h
        simp only [pos] at h
        omega
    · rw [if_neg habove]
      have hiP : S.K d - 1 - l < S.P d := by omega
      rw [Finset.sum_eq_single (S.K d - 1 - l)]
      · rw [if_pos (by simp only [pos]; omega)]
        simp only [Uh]
        split_ifs with h1 h2
        · have h3 : S.K d - 1 - l < 3 := by omega
          simp only [Ue, dif_pos (And.intro h3 h3)]
          exact hUd d ⟨_, h3⟩ h1
        · rw [show S.K d - 1 - l = S.P d - 1 by omega]
          exact wfree_ne hG hGF hL hLd U hU μ hμ Tgt hW hdet d
        · omega
      · intro i hi hne
        simp at hi
        rw [if_neg]
        simp only [pos]
        omega
      · intro h; simp at h; omega

/-- **Realization theorem.** -/
theorem realize (S : Setup m) (G : Fin 3 → Matrix (Fin m) (Fin m) F) (hG : T0 G)
    (hGF : IsGF G S.K)
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) (hL : ∀ c, L c 0 1 = 0)
    (hLd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0)
    (U : Fin 3 → Matrix (Fin 3) (Fin 3) F) (hU : ∀ d (a b : Fin 3), b < a → U d a b = 0)
    (hUd : ∀ d (a : Fin 3), (a : ℕ) + 1 < S.P d → U d a a ≠ 0)
    (μ : Fin 3 → Fin 3 → F) (hμ : ∀ c d, c ≠ d → μ c d ≠ 0)
    (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F)
    (hW : ∀ c d, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < S.g c → (i : ℕ) + 1 < S.P d →
      Tgt c d ρ i = μ c d * (L c * Wm S.K G c d * U d) ρ i)
    (hdet : ∀ d, IsUnit (Tpad S Tgt d)) (Own : Fin 3 → ℕ → ℕ → F) :
    ∃ C : Fin 3 → Matrix (Fin m) (Fin m) F, T0 C ∧ IsGF C S.K ∧
      (∀ c d, c ≠ d → ∀ ρ, ρ < S.g c → ∀ l, l < S.K d →
        ent (C c) (S.K c + ρ) (offK S.K d + l) =
          if S.K d - 1 - l < S.P d then Tgt c d ρ (S.K d - 1 - l) else 0) ∧
      (∀ c (i l : ℕ), S.K c ≤ i → i < m → l < S.K c → ent (C c) i (offK S.K c + l) = Own c i l) := by
  have hG1 := G1_T0 (S := S) hG L hL hLd
  have hGF1 := G1_GF (S := S) hGF L
  have hV := Vm_levlow hG hGF hL hLd U hU hUd μ hμ Tgt hW hdet
  set V := Vm S G L U μ Tgt with hVdef
  set G2 := colMove S.K (G1 S G L) V with hG2def
  have hT2 : T0 G2 := T0_cols S.hK hG1 hGF1 hV
  have hGF2 : IsGF G2 S.K := colMove_GF hGF1 V
  let C : Fin 3 → Matrix (Fin m) (Fin m) F := fun c i n =>
    if (i : ℕ) < S.K c then G2 c i n
    else if blk S.K n = c then Own c i (lev S.K n) else μ c (blk S.K n) * G2 c i n
  have hGFC : IsGF C S.K := by
    intro c j col hj
    simp only [C, if_pos hj]
    exact hGF2 c j col hj
  refine ⟨C, T0_transfer S.hK hT2 hGF2 hGFC μ hμ (by
    intro c i n hi hb
    simp only [C, if_neg (show ¬ (i : ℕ) < S.K c by omega), if_neg hb]), hGFC, ?_, ?_⟩
  · intro c d hcd ρ hρ l hl
    have hgm := S.hgm c
    have hi : S.K c + ρ < m := by omega
    have hn : offK S.K d + l < m := offK_lt S.K S.hK d l hl
    have hbo := blk_of S.K d l hl
    unfold ent
    rw [dif_pos ⟨hi, hn⟩]
    simp only [C, if_neg (show ¬ (S.K c + ρ < S.K c) by omega), hbo.1, if_neg (Ne.symm hcd)]
    simp only [hG2def, colMove, if_neg (show ¬ (S.K c + ρ < S.K c) by omega), mul_apply]
    have hq : ∀ i ∈ range (S.P d), pos S d i < m := fun i hi => pos_lt S d i (by simpa using hi)
    simp only [hVdef, Vm, hbo.1, hbo.2]
    split_ifs with habove hwin hwin
    · omega
    · -- above the pivot levels: cleared
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, sum_pick_right _ _ _ hq]
      rw [Finset.sum_eq_single ⟨offK S.K d + l, hn⟩ (by
        intro b _ hb; rw [if_neg hb, mul_zero]) (by simp), if_pos rfl, mul_one]
      have hx := xkill_spec hG hGF hL hLd d l c hcd ρ hρ
      have : ∑ i ∈ range (S.P d), fe (fun n' => G1 S G L c ⟨S.K c + ρ, hi⟩ n') (pos S d i) *
          ex4 (xkill S G L d l) i =
          ∑ i ∈ range (S.P d), A1 S G L c ρ d i * ex4 (xkill S G L d l) i := by
        apply Finset.sum_congr rfl
        intro i hi'
        simp [fe, A1, ent, hq i hi', hi]
      rw [this, hx]
      simp [ent, hi, hn]
    · -- pivot levels: the target
      rw [sum_pick_right _ _ _ hq]
      rw [key_identity hG hGF hL hLd U hU μ hμ Tgt hW c d hcd ρ hρ _ hwin]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      simp [fe, A1, ent, hq i hi', hi]
    · omega
  · intro c i l hi him hl
    have hn : offK S.K c + l < m := offK_lt S.K S.hK c l hl
    have hbo := blk_of S.K c l hl
    unfold ent
    rw [dif_pos ⟨him, hn⟩]
    simp only [C, if_neg (show ¬ i < S.K c by omega), hbo.1, hbo.2, if_true]

end Solve

end Z3NetKN.Realize

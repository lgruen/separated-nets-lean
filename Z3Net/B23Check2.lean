/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.B23Check

@[expose] public section

/-!
# V14 stage S14′: kernel checkers for the base-2/3 certificates, part 2 (the checkers and their soundness)

* `chk1` (the certificate `v°_L ≥ v` at a certificate level, window code of the top `H = L/2` digits, with
  `Δ_z = G_x Δ_x + G_y Δ_y`): the per-coordinate lists are complete by the window bound `win_lb` (a coordinate whose top
  `H − r` digits have `μ ≥ 2` already has weight `≥ (b^r + 1 − 1)² ≥ v`), the pairs are enumerated with their weight
  budget. Soundness `chk1_sound`.
* `chk2` (the exact every-shift distance `≥ U` at a level `m` between the seed and `L`; window of `H' ≥ m/3` digits,
  box `(H', H', m − 2H')`): only codewords whose three windows have `μ ≤ 1` are completed. Soundness `chk2_sound`.
* `chkNet` / `chkDist` (small nets: all box maps injective; every-shift distance by enumerating all codewords).
* `admPair` (one condition `λ^{cc'}_e(s) ≠ 0` of `def:lift` from a functional `λ` given as data). Soundness
  `admPair_sound`.
-/

namespace Z3NetB23

/-- The complete list of the `n`-digit vectors with `mulb ≤ 1`. -/
def stList (b n : ℕ) : List ℕ := (List.range (b ^ n)).filter (fun x => decide (mulb b n x ≤ 1))

/-- The candidates of weight `< v` (top `H − r` digits in `stList`). -/
def sList (b H r v : ℕ) : List ℕ :=
  ((stList b (H - r)).flatMap (fun t => (List.range (b ^ r)).map (fun l => t * b ^ r + l))).filter
    (fun x => decide (hW (mulb b H x) < v))

/-- **The certificate `v°_L ≥ v`** at a certificate level (window `H` digits, `Δ_z = G_x Δ_x + G_y Δ_y`). -/
def chk1 (b H r v : ℕ) (gx gy : List ℕ) : Bool :=
  decide (v ≤ hW (b ^ r + 1)) && decide (r ≤ H) &&
  (let S := sList b H r v
   let SX := S.map (fun x => (x, hW (mulb b H x), matvec b H H gx x))
   let SY := S.map (fun y => (y, hW (mulb b H y), matvec b H H gy y))
   SX.all (fun p => SY.all (fun q => decide (v ≤ p.2.1 + q.2.1) || (p.1 == 0 && q.1 == 0) ||
     decide (v ≤ p.2.1 + q.2.1 + hW (mulb b H (dadd b H p.2.2 q.2.2))))))

/-- **The exact every-shift distance `≥ U`** at a level `m` (window `Hp` digits, box `(Hp, Hp, m − 2Hp)`; `Mx`, `My`,
`Mz` the columns of `Δ_c` as a function of the box digits, per coordinate `c`). -/
def chk2 (b m Hp U : ℕ) (Mx My Mz : List (List ℕ)) : Bool :=
  decide (U ≤ (b ^ (m - Hp)) ^ 2) && decide (m ≤ 3 * Hp) && decide (2 * Hp ≤ m) &&
  (let St := stList b Hp
   let Z := St.map (fun s => s / b ^ (3 * Hp - m))
   let A := St.map (fun tx => (tx, Mx.map (fun cs => matvec b m Hp cs tx)))
   let B := St.map (fun ty => (ty, My.map (fun cs => matvec b m Hp cs ty)))
   let C := Z.map (fun z => (z, Mz.map (fun cs => matvec b m (m - 2 * Hp) cs z)))
   A.all (fun a => B.all (fun bb => C.all (fun cc =>
     (a.1 == 0 && bb.1 == 0 && cc.1 == 0) ||
     decide (1 < mulb b Hp (dadd b m (dadd b m (a.2.getD 0 0) (bb.2.getD 0 0)) (cc.2.getD 0 0) / b ^ (m - Hp))) ||
     decide (1 < mulb b Hp (dadd b m (dadd b m (a.2.getD 1 0) (bb.2.getD 1 0)) (cc.2.getD 1 0) / b ^ (m - Hp))) ||
     decide (1 < mulb b Hp (dadd b m (dadd b m (a.2.getD 2 0) (bb.2.getD 2 0)) (cc.2.getD 2 0) / b ^ (m - Hp))) ||
     decide (U ≤ mulb b m (dadd b m (dadd b m (a.2.getD 0 0) (bb.2.getD 0 0)) (cc.2.getD 0 0)) ^ 2 +
       mulb b m (dadd b m (dadd b m (a.2.getD 1 0) (bb.2.getD 1 0)) (cc.2.getD 1 0)) ^ 2 +
       mulb b m (dadd b m (dadd b m (a.2.getD 2 0) (bb.2.getD 2 0)) (cc.2.getD 2 0)) ^ 2)))))

/-- **Small nets, `t = 0`**: for every nonzero index and every box shape `(d₀, d₁, m − d₀ − d₁)` some coordinate has
a nonzero digit among its first `d_c`. -/
def chkNet (b m : ℕ) (cols : List (List ℕ)) : Bool :=
  (List.range (b ^ m)).all (fun n => n == 0 ||
    (List.range (m + 1)).all (fun d0 => (List.range (m + 1 - d0)).all (fun d1 =>
      decide (matvec b m m (cols.getD 0 []) n / b ^ (m - d0) ≠ 0) ||
      decide (matvec b m m (cols.getD 1 []) n / b ^ (m - d1) ≠ 0) ||
      decide (matvec b m m (cols.getD 2 []) n / b ^ (d0 + d1) ≠ 0))))

/-- **Small nets, every-shift distance `≥ U`**: all nonzero codewords. -/
def chkDist (b m U : ℕ) (cols : List (List ℕ)) : Bool :=
  (List.range (b ^ m)).all (fun n => n == 0 ||
    decide (U ≤ mulb b m (matvec b m m (cols.getD 0 []) n) ^ 2 + mulb b m (matvec b m m (cols.getD 1 []) n) ^ 2 +
      mulb b m (matvec b m m (cols.getD 2 []) n) ^ 2))

/-- `∑_k dg x k · dg y k` over `n` digits. -/
def dotc (b : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, x, y => (x % b) * (y % b) + dotc b n (x / b) (y / b)

/-- **One admissibility condition**: the functional `λ = (l₁, l₂)` (supported on the first `e` digits of `c` and the
first `M + 1 − e` digits of `c'`) vanishes on the columns of `P_cc'` (codes `cc`, `cc'`) and not on `(s₁, s₂)`. -/
def admPair (b M e : ℕ) (cc cc' : List ℕ) (l1 l2 s1 s2 : ℕ) : Bool :=
  (l1 % b ^ (M - e) == 0) && (l2 % b ^ (e - 1) == 0) &&
  (List.range M).all (fun i => (dotc b M l1 (cc.getD i 0) + dotc b M l2 (cc'.getD i 0)) % b == 0) &&
  ((dotc b M l1 s1 + dotc b M l2 s2) % b != 0)

end Z3NetB23

namespace Z3NetB23.Proofs

open Matrix Finset Z3NetB23

variable {b : ℕ}

/-! ## Bounds of codes -/

lemma dadd_lt (hb : 2 ≤ b) {n x y : ℕ} (hx : x < b ^ n) (hy : y < b ^ n) : dadd b n x y < b ^ n := by
  unfold dadd
  split_ifs with h
  · subst h; exact Nat.xor_lt_two_pow hx hy
  · exact daddN_lt (by omega) n x y

lemma smul_lt (hb : 2 ≤ b) {n x : ℕ} (hx : x < b ^ n) : ∀ a, smul b n a x < b ^ n := by
  intro a
  induction a with
  | zero => exact pow_pos (by omega) n
  | succ a ih => exact dadd_lt hb hx ih

lemma mvAux_lt (hb : 2 ≤ b) {n k : ℕ} (v : ℕ) : ∀ (cs : List ℕ) (i : ℕ), (∀ c ∈ cs, c < b ^ n) →
    mvAux b n k cs i v < b ^ n := by
  intro cs
  induction cs with
  | nil => intro _ _; exact pow_pos (by omega) n
  | cons c cs ih =>
    intro i h
    exact dadd_lt hb (smul_lt hb (h c List.mem_cons_self) _) (ih (i + 1) fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

lemma matvec_lt (hb : 2 ≤ b) {n k : ℕ} (cols : List ℕ) (h : ∀ c ∈ cols, c < b ^ n) (v : ℕ) :
    matvec b n k cols v < b ^ n := mvAux_lt hb v cols 0 h

/-! ## The window bound -/

/-- The per-coordinate weight `|int(X ⊕ δ) − int X|_{b^n}`. -/
def wt {n : ℕ} (X δ : Fin n → ZMod b) : ℕ := Z3NetF.cres (b ^ n) ((dval b (X + δ) : ℤ) - dval b X)

lemma mulb_le_wt (hb : 2 ≤ b) {n : ℕ} (X δ : Fin n → ZMod b) :
    have : NeZero b := ⟨by omega⟩
    mulb b n (dval b δ) ≤ wt X δ := by
  have : NeZero b := ⟨by omega⟩
  have := mulb_le hb n (dval b δ) (dval_lt δ) X
  rwa [vecOf_dval] at this

/-- **The window bound**: `b^r · mulb_{n−r}(top) ≤ |int(X ⊕ δ) − int X|_{b^n} + b^r − 1`. -/
lemma win_lb (hb : 2 ≤ b) {n : ℕ} (r : ℕ) (hr : r ≤ n) (X δ : Fin n → ZMod b) :
    b ^ r * mulb b (n - r) (dval b δ / b ^ r) ≤ wt X δ + (b ^ r - 1) := by
  have : NeZero b := ⟨by omega⟩
  have hbp : 0 < b := by omega
  have hQ : 0 < b ^ r := pow_pos hbp r
  have h1 := cres_window (b ^ (n - r)) (b ^ r) (pow_pos hbp _) hQ (dval b (X + δ) : ℤ) (dval b X)
  have hn : b ^ (n - r) * b ^ r = b ^ n := by rw [← pow_add]; congr 1; omega
  rw [hn] at h1
  -- the tops
  have htop : ∀ y : Fin n → ZMod b, (dval b y : ℤ) / ((b ^ r : ℕ) : ℤ) = dval b (topD (n - r) (by omega) y) := by
    intro y
    rw [← Int.natCast_div, ← dval_div y (n - r) (by omega)]
    congr 3; omega
  rw [htop, htop] at h1
  have hsplit : topD (n - r) (by omega) (X + δ) = topD (n - r) (by omega) X + topD (n - r) (by omega) δ := rfl
  rw [hsplit] at h1
  have hm := mulb_le_wt hb (topD (n - r) (by omega) X) (topD (n - r) (by omega) δ)
  have hδ : dval b (topD (n - r) (by omega) δ) = dval b δ / b ^ r := by
    rw [← dval_div δ (n - r) (by omega)]; congr 2; omega
  rw [hδ] at hm
  have hrem : |(dval b (X + δ) : ℤ) % ((b ^ r : ℕ) : ℤ) - (dval b X : ℤ) % ((b ^ r : ℕ) : ℤ)| ≤ (b ^ r : ℕ) - 1 := by
    have a1 : 0 ≤ (dval b (X + δ) : ℤ) % ((b ^ r : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
    have a2 : (dval b (X + δ) : ℤ) % ((b ^ r : ℕ) : ℤ) < (b ^ r : ℕ) := Int.emod_lt_of_pos _ (by omega)
    have a3 : 0 ≤ (dval b X : ℤ) % ((b ^ r : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
    have a4 : (dval b X : ℤ) % ((b ^ r : ℕ) : ℤ) < (b ^ r : ℕ) := Int.emod_lt_of_pos _ (by omega)
    rw [abs_le]; constructor <;> omega
  have hm' : ((b ^ r : ℕ) : ℤ) * (mulb b (n - r) (dval b δ / b ^ r) : ℤ) ≤
      ((b ^ r : ℕ) : ℤ) * (wt (topD (n - r) (by omega) X) (topD (n - r) (by omega) δ) : ℤ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hm) (by positivity)
  have : ((b ^ r * mulb b (n - r) (dval b δ / b ^ r) : ℕ) : ℤ) ≤ ((wt X δ + (b ^ r - 1) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hQ.ne')]
    unfold wt at hm' ⊢
    push_cast at hm' h1 hrem
    linarith
  exact_mod_cast this

lemma wt_big (hb : 2 ≤ b) {n : ℕ} (r : ℕ) (hr : r ≤ n) (X δ : Fin n → ZMod b)
    (h : 2 ≤ mulb b (n - r) (dval b δ / b ^ r)) : b ^ r + 1 ≤ wt X δ := by
  have := win_lb hb r hr X δ
  have hQ : 0 < b ^ r := pow_pos (by omega) r
  have : b ^ r * 2 ≤ wt X δ + (b ^ r - 1) := le_trans (Nat.mul_le_mul_left _ h) this
  omega

/-! ## Soundness of `chk1` -/

lemma dval_eq_zero [NeZero b] {n : ℕ} (δ : Fin n → ZMod b) (h : dval b δ = 0) : δ = 0 := by
  rw [← vecOf_dval δ, h, vecOf_zero]

lemma mem_stList [NeZero b] {n x : ℕ} (hx : x < b ^ n) (h : mulb b n x ≤ 1) : x ∈ stList b n := by
  simp only [stList, List.mem_filter, List.mem_range, decide_eq_true_eq]; exact ⟨hx, h⟩

lemma mem_sList (hb : 2 ≤ b) {H r v : ℕ} (hr : r ≤ H) (δ : Fin H → ZMod b)
    (h1 : mulb b (H - r) (dval b δ / b ^ r) ≤ 1) (h2 : hW (mulb b H (dval b δ)) < v) :
    have : NeZero b := ⟨by omega⟩
    dval b δ ∈ sList b H r v := by
  have : NeZero b := ⟨by omega⟩
  have hbp : 0 < b := by omega
  simp only [sList, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨dval b δ / b ^ r, mem_stList ?_ h1, dval b δ % b ^ r, Nat.mod_lt _ (pow_pos hbp r), ?_⟩, h2⟩
  · rw [Nat.div_lt_iff_lt_mul (pow_pos hbp r), ← pow_add, show H - r + r = H by omega]; exact dval_lt δ
  · rw [mul_comm]; exact Nat.div_add_mod _ _

/-- **Soundness of `chk1`**: for all digit vectors `Δ_x, Δ_y` (not both `0`), `Δ_z = G_x Δ_x + G_y Δ_y`, and every
`X`, `v ≤ ∑_c max(0, |int(X_c ⊕ Δ_c) − int X_c|_{b^H} − 1)²`. -/
theorem chk1_sound (hb : 2 ≤ b) {H r v : ℕ} {gx gy : List ℕ} (hgx : gx.length = H) (hgy : gy.length = H)
    (hcx : ∀ c ∈ gx, c < b ^ H) (hcy : ∀ c ∈ gy, c < b ^ H) (h : chk1 b H r v gx gy = true)
    (dx dy : Fin H → ZMod b) (hne : ¬(dx = 0 ∧ dy = 0)) (X : Fin 3 → Fin H → ZMod b) :
    v ≤ hW (wt (X 0) dx) + hW (wt (X 1) dy) + hW (wt (X 2) (colMatR b H H gx *ᵥ dx + colMatR b H H gy *ᵥ dy)) := by
  have : NeZero b := ⟨by omega⟩
  simp only [chk1, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hr⟩, hall⟩ := h
  set dz := colMatR b H H gx *ᵥ dx + colMatR b H H gy *ᵥ dy
  -- a coordinate with a bad window decides
  by_cases hx1 : 2 ≤ mulb b (H - r) (dval b dx / b ^ r)
  · have := hW_mono (wt_big hb r hr (X 0) dx hx1); omega
  by_cases hy1 : 2 ≤ mulb b (H - r) (dval b dy / b ^ r)
  · have := hW_mono (wt_big hb r hr (X 1) dy hy1); omega
  have mx := hW_mono (mulb_le_wt hb (X 0) dx)
  have my := hW_mono (mulb_le_wt hb (X 1) dy)
  by_cases hxv : v ≤ hW (mulb b H (dval b dx))
  · omega
  by_cases hyv : v ≤ hW (mulb b H (dval b dy))
  · omega
  have hxS := mem_sList (v := v) hb hr dx (by omega) (by omega)
  have hyS := mem_sList (v := v) hb hr dy (by omega) (by omega)
  rw [List.all_eq_true] at hall
  have h1 := hall (dval b dx, hW (mulb b H (dval b dx)), matvec b H H gx (dval b dx)) (List.mem_map.2 ⟨_, hxS, rfl⟩)
  rw [List.all_eq_true] at h1
  have h2 := h1 (dval b dy, hW (mulb b H (dval b dy)), matvec b H H gy (dval b dy)) (List.mem_map.2 ⟨_, hyS, rfl⟩)
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h2
  rcases h2 with (h2 | h2) | h2
  · omega
  · exact absurd ⟨dval_eq_zero dx h2.1, dval_eq_zero dy h2.2⟩ hne
  · -- the third coordinate
    have hz : vecOf b H (dadd b H (matvec b H H gx (dval b dx)) (matvec b H H gy (dval b dy))) = dz := by
      rw [vecOf_dadd, vecOf_matvec _ _ _ hgx, vecOf_matvec _ _ _ hgy, vecOf_dval, vecOf_dval]
    have hzlt := dadd_lt hb (matvec_lt hb gx hcx (dval b dx) (k := H)) (matvec_lt hb gy hcy (dval b dy) (k := H))
    have mz := mulb_le hb H _ hzlt (X 2)
    rw [hz] at mz
    have mz' : mulb b H (dadd b H (matvec b H H gx (dval b dx)) (matvec b H H gy (dval b dy))) ≤ wt (X 2) dz := mz
    have := hW_mono mz'
    omega

/-! ## Soundness of `chk2` -/

lemma getD_map_lt {α β : Type*} (f : α → β) (l : List α) (i : ℕ) (hi : i < l.length) (d : α) (e : β) :
    (l.map f).getD i e = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

lemma dval_topD [NeZero b] {n : ℕ} (x : Fin n → ZMod b) (H : ℕ) (hH : H ≤ n) :
    dval b (topD H hH x) = dval b x / b ^ (n - H) := (dval_div x H hH).symm

/-- **Soundness of `chk2`**: for a digit difference `Δ_c = M^x_c t_x + M^y_c t_y + M^z_c z` whose box digits are
`t_x, t_y, z` (not all `0`), `U ≤ ∑_c |int(X_c ⊕ Δ_c) − int X_c|²_{b^m}` for every `X`. -/
theorem chk2_sound (hb : 2 ≤ b) {m Hp U : ℕ} {Mx My Mz : List (List ℕ)} (hm2 : 2 * Hp ≤ m)
    (hMx : Mx.length = 3) (hMy : My.length = 3) (hMz : Mz.length = 3)
    (hlx : ∀ c ∈ Mx, c.length = Hp) (hly : ∀ c ∈ My, c.length = Hp) (hlz : ∀ c ∈ Mz, c.length = m - 2 * Hp)
    (hbx : ∀ c ∈ Mx, ∀ x ∈ c, x < b ^ m) (hby : ∀ c ∈ My, ∀ x ∈ c, x < b ^ m)
    (hbz : ∀ c ∈ Mz, ∀ x ∈ c, x < b ^ m) (h : chk2 b m Hp U Mx My Mz = true)
    (tx ty : Fin Hp → ZMod b) (z : Fin (m - 2 * Hp) → ZMod b) (Δ : Fin 3 → Fin m → ZMod b)
    (hΔ : ∀ c : Fin 3, Δ c = colMatR b m Hp (Mx.getD c []) *ᵥ tx + colMatR b m Hp (My.getD c []) *ᵥ ty +
      colMatR b m (m - 2 * Hp) (Mz.getD c []) *ᵥ z)
    (htx : tx = topD Hp (by omega) (Δ 0)) (hty : ty = topD Hp (by omega) (Δ 1))
    (hz : z = topD (m - 2 * Hp) (by omega) (Δ 2)) (hne : ¬(tx = 0 ∧ ty = 0 ∧ z = 0))
    (X : Fin 3 → Fin m → ZMod b) :
    U ≤ ∑ c : Fin 3, wt (X c) (Δ c) ^ 2 := by
  have : NeZero b := ⟨by omega⟩
  have hbp : 0 < b := by omega
  simp only [chk2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hU, h3⟩, -⟩, hall⟩ := h
  rw [Fin.sum_univ_three]
  -- a coordinate with a bad window decides
  have big : ∀ c : Fin 3, 2 ≤ mulb b Hp (dval b (Δ c) / b ^ (m - Hp)) → U ≤ wt (X c) (Δ c) ^ 2 := by
    intro c hc
    have := wt_big hb (m - Hp) (by omega) (X c) (Δ c) (by rwa [show m - (m - Hp) = Hp by omega])
    exact hU.trans (Nat.pow_le_pow_left (by omega) 2)
  by_cases h0 : 2 ≤ mulb b Hp (dval b (Δ 0) / b ^ (m - Hp))
  · have := big 0 h0; omega
  by_cases h1 : 2 ≤ mulb b Hp (dval b (Δ 1) / b ^ (m - Hp))
  · have := big 1 h1; omega
  by_cases h2 : 2 ≤ mulb b Hp (dval b (Δ 2) / b ^ (m - Hp))
  · have := big 2 h2; omega
  -- the box digits are in the lists
  have ctx : dval b tx = dval b (Δ 0) / b ^ (m - Hp) := by rw [htx, dval_topD]
  have cty : dval b ty = dval b (Δ 1) / b ^ (m - Hp) := by rw [hty, dval_topD]
  have ctz : dval b z = dval b (Δ 2) / b ^ (m - Hp) / b ^ (3 * Hp - m) := by
    rw [hz, dval_topD, Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega
  have mtx : dval b tx ∈ stList b Hp := mem_stList (dval_lt tx) (by rw [ctx]; omega)
  have mty : dval b ty ∈ stList b Hp := mem_stList (dval_lt ty) (by rw [cty]; omega)
  have hsz : dval b (Δ 2) / b ^ (m - Hp) ∈ stList b Hp := by
    apply mem_stList _ (by omega)
    rw [Nat.div_lt_iff_lt_mul (pow_pos hbp _), ← pow_add, show Hp + (m - Hp) = m by omega]; exact dval_lt _
  rw [List.all_eq_true] at hall
  have ha := hall (dval b tx, Mx.map (fun cs => matvec b m Hp cs (dval b tx))) (List.mem_map.2 ⟨_, mtx, rfl⟩)
  rw [List.all_eq_true] at ha
  have hbb := ha (dval b ty, My.map (fun cs => matvec b m Hp cs (dval b ty))) (List.mem_map.2 ⟨_, mty, rfl⟩)
  rw [List.all_eq_true] at hbb
  have hcc := hbb (dval b z, Mz.map (fun cs => matvec b m (m - 2 * Hp) cs (dval b z)))
    (List.mem_map.2 ⟨dval b z, List.mem_map.2 ⟨_, hsz, ctz.symm⟩, rfl⟩)
  -- the computed codewords
  have hcode : ∀ (i : ℕ) (hi : i < 3), dadd b m (dadd b m ((Mx.map (fun cs => matvec b m Hp cs (dval b tx))).getD i 0)
      ((My.map (fun cs => matvec b m Hp cs (dval b ty))).getD i 0))
      ((Mz.map (fun cs => matvec b m (m - 2 * Hp) cs (dval b z))).getD i 0) = dval b (Δ ⟨i, hi⟩) := by
    intro i hi
    rw [getD_map_lt _ _ i (by omega) [] 0, getD_map_lt _ _ i (by omega) [] 0, getD_map_lt _ _ i (by omega) [] 0]
    have mem : ∀ (L : List (List ℕ)), L.length = 3 → L.getD i [] ∈ L := fun L hL => by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    have hlt := dadd_lt hb (dadd_lt hb (matvec_lt hb _ (hbx _ (mem Mx hMx)) (dval b tx) (k := Hp))
      (matvec_lt hb _ (hby _ (mem My hMy)) (dval b ty) (k := Hp)))
      (matvec_lt hb _ (hbz _ (mem Mz hMz)) (dval b z) (k := m - 2 * Hp))
    rw [← dval_vecOf m _ hlt, vecOf_dadd, vecOf_dadd, vecOf_matvec _ _ _ (hlx _ (mem Mx hMx)),
      vecOf_matvec _ _ _ (hly _ (mem My hMy)), vecOf_matvec _ _ _ (hlz _ (mem Mz hMz)), vecOf_dval, vecOf_dval,
      vecOf_dval, hΔ ⟨i, hi⟩]
  dsimp only at hcc
  rw [hcode 0 (by norm_num), hcode 1 (by norm_num), hcode 2 (by norm_num)] at hcc
  have e0 : Δ ⟨0, by norm_num⟩ = Δ 0 := rfl
  have e1 : Δ ⟨1, by norm_num⟩ = Δ 1 := rfl
  have e2 : Δ ⟨2, by norm_num⟩ = Δ 2 := rfl
  rw [e0, e1, e2] at hcc
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hcc
  rcases hcc with ((((hz0 | hw0) | hw1) | hw2) | hfin)
  · exact absurd ⟨dval_eq_zero tx hz0.1.1, dval_eq_zero ty hz0.1.2, dval_eq_zero z hz0.2⟩ hne
  · omega
  · omega
  · omega
  · have m0 := Nat.pow_le_pow_left (mulb_le_wt hb (X 0) (Δ 0)) 2
    have m1 := Nat.pow_le_pow_left (mulb_le_wt hb (X 1) (Δ 1)) 2
    have m2 := Nat.pow_le_pow_left (mulb_le_wt hb (X 2) (Δ 2)) 2
    omega

/-! ## Small nets -/

lemma colMat_mulVec [NeZero b] (m : ℕ) (cols : List (List ℕ)) (c : Fin 3) (hl : (cols.getD c []).length = m)
    (n : ℕ) : vecOf b m (matvec b m m (cols.getD c []) n) = colMat b m cols c *ᵥ vecOf b m n := by
  rw [vecOf_matvec _ _ _ hl]; rfl

/-- **Soundness of `chkNet`**: the small net with column codes `cols` is a `(0,m,3)`-net (with any shift). -/
theorem chkNet_sound [Fact b.Prime] (m : ℕ) (cols : List (List ℕ)) (hl : ∀ c : Fin 3, (cols.getD c []).length = m)
    (hbd : ∀ c : Fin 3, ∀ x ∈ cols.getD c [], x < b ^ m) (h : chkNet b m cols = true)
    (σ : Fin 3 → Fin m → ZMod b) : Z3NetF.IsNet0 3 b m (Z3NetF.digPointShift b m (colMat b m cols) σ) := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  have hb : 2 ≤ b := (Fact.out : b.Prime).two_le
  rw [net_iff_boxInj]
  intro d hd n hn
  rw [Fin.sum_univ_three] at hd
  by_contra hn0
  have hc : dval b n ≠ 0 := fun h0 => hn0 (dval_eq_zero n h0)
  simp only [chkNet, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have h1 := h (dval b n) (dval_lt n)
  rcases h1 with h1 | h1
  · exact hc h1
  have h2 := h1 (d 0) (by omega) (d 1) (by omega)
  -- each coordinate's first `d_c` digits vanish
  have zero : ∀ c : Fin 3, matvec b m m (cols.getD c []) (dval b n) / b ^ (m - d c) = 0 := by
    intro c
    have hlt := matvec_lt hb _ (hbd c) (dval b n) (k := m)
    have e := colMat_mulVec (b := b) m cols c (hl c) (dval b n)
    rw [vecOf_dval] at e
    have hdc : d c ≤ m := by fin_cases c <;> simp <;> omega
    rw [← dval_vecOf m _ hlt, e, ← dval_topD _ (d c) hdc]
    have : topD (d c) hdc (colMat b m cols c *ᵥ n) = 0 := by
      funext j; exact hn c _ (by simp only [Fin.coe_castLE]; exact j.isLt)
    rw [this]
    simp [dval]
  rcases h2 with (h2 | h2) | h2
  · exact h2 (zero 0)
  · exact h2 (zero 1)
  · exact h2 (by have := zero 2; rwa [show m - d 2 = d 0 + d 1 by omega] at this)

/-- **Soundness of `chkDist`**: every nonzero codeword `Δ = C n` of the small net has
`U ≤ ∑_c |int(X_c ⊕ Δ_c) − int X_c|²_{b^m}` for every `X`. -/
theorem chkDist_sound (hb : 2 ≤ b) (m U : ℕ) (cols : List (List ℕ)) (hl : ∀ c : Fin 3, (cols.getD c []).length = m)
    (hbd : ∀ c : Fin 3, ∀ x ∈ cols.getD c [], x < b ^ m) (h : chkDist b m U cols = true)
    (n : Fin m → ZMod b) (hn : n ≠ 0) (X : Fin 3 → Fin m → ZMod b) :
    U ≤ ∑ c : Fin 3, wt (X c) (colMat b m cols c *ᵥ n) ^ 2 := by
  have : NeZero b := ⟨by omega⟩
  have hc : dval b n ≠ 0 := fun h0 => hn (dval_eq_zero n h0)
  simp only [chkDist, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h (dval b n) (dval_lt n) with h1 | h1
  · exact absurd h1 hc
  rw [Fin.sum_univ_three]
  have key : ∀ c : Fin 3, mulb b m (matvec b m m (cols.getD c []) (dval b n)) ≤ wt (X c) (colMat b m cols c *ᵥ n) := by
    intro c
    have hlt := matvec_lt hb _ (hbd c) (dval b n) (k := m)
    have e := colMat_mulVec (b := b) m cols c (hl c) (dval b n)
    rw [vecOf_dval] at e
    have := mulb_le_wt hb (X c) (colMat b m cols c *ᵥ n)
    have hd : dval b (colMat b m cols c *ᵥ n) = matvec b m m (cols.getD c []) (dval b n) := by
      rw [← e, dval_vecOf m _ hlt]
    rwa [hd] at this
  have k0 : mulb b m (matvec b m m (cols.getD 0 []) (dval b n)) ^ 2 ≤ wt (X 0) (colMat b m cols 0 *ᵥ n) ^ 2 :=
    Nat.pow_le_pow_left (key 0) 2
  have k1 : mulb b m (matvec b m m (cols.getD 1 []) (dval b n)) ^ 2 ≤ wt (X 1) (colMat b m cols 1 *ᵥ n) ^ 2 :=
    Nat.pow_le_pow_left (key 1) 2
  have k2 : mulb b m (matvec b m m (cols.getD 2 []) (dval b n)) ^ 2 ≤ wt (X 2) (colMat b m cols 2 *ᵥ n) ^ 2 :=
    Nat.pow_le_pow_left (key 2) 2
  omega

/-! ## Every shift: from all `X` to `μ` -/

lemma sum_muD_ge [NeZero b] {m : ℕ} (U : ℕ) (Δ : Fin 3 → Fin m → ZMod b)
    (h : ∀ X : Fin 3 → Fin m → ZMod b, U ≤ ∑ c : Fin 3, wt (X c) (Δ c) ^ 2) :
    U ≤ ∑ c : Fin 3, muD b (Δ c) ^ 2 := by
  have hX : ∀ c : Fin 3, ∃ X : Fin m → ZMod b, muD b (Δ c) = wt X (Δ c) := by
    intro c
    obtain ⟨X, -, hX⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin m → ZMod b))
      (fun X : Fin m → ZMod b => Z3NetF.cres (b ^ m) ((dval b (X + Δ c) : ℤ) - dval b X))
    exact ⟨X, hX⟩
  choose X hXc using hX
  have := h X
  simp only [hXc]
  exact this

/-! ## Soundness of `admPair` -/

lemma dotc_eq [NeZero b] : ∀ (n x y : ℕ), ((dotc b n x y : ℕ) : ZMod b) = vecOf b n x ⬝ᵥ vecOf b n y := by
  intro n
  induction n with
  | zero => intro x y; simp [dotc]
  | succ n ih =>
    intro x y
    simp only [dotc, dotProduct]
    rw [Fin.sum_univ_castSucc]
    simp only [vecOf_castSucc, vecOf_last]
    push_cast
    rw [ih (x / b) (y / b), dotProduct]
    ring

/-- **Soundness of `admPair`**: the condition `s^{cc'} ∉ P_cc' ⊔ Z_e` of `def:lift` (`Admissible`). -/
theorem admPair_sound [Fact b.Prime] (M e : ℕ) (he1 : 1 ≤ e) (he2 : e ≤ M) (cols : List (List ℕ)) (c c' : Fin 3)
    (l1 l2 s1 s2 : ℕ) (hl : ∀ c : Fin 3, (cols.getD c []).length = M)
    (h : admPair b M e (cols.getD c []) (cols.getD c' []) l1 l2 s1 s2 = true) :
    (vecOf b M s1, vecOf b M s2) ∉ pairSub (colMat b M cols) c c' ⊔ Zsub b M e := by
  have : NeZero b := ⟨(Fact.out : b.Prime).ne_zero⟩
  simp only [admPair, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hs1, hs2⟩, hP⟩, hs⟩ := h
  -- the functional
  let f : ((Fin M → ZMod b) × (Fin M → ZMod b)) →ₗ[ZMod b] ZMod b :=
    { toFun := fun u => vecOf b M l1 ⬝ᵥ u.1 + vecOf b M l2 ⬝ᵥ u.2
      map_add' := by
        intro u v
        simp only [Prod.fst_add, Prod.snd_add, dotProduct_add]
        abel
      map_smul' := by
        intro a u
        simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, RingHom.id_apply, smul_add] }
  have hf : ∀ u, f u = vecOf b M l1 ⬝ᵥ u.1 + vecOf b M l2 ⬝ᵥ u.2 := fun _ => rfl
  -- the support of `λ`
  have hl1 : ∀ j : Fin M, e ≤ (j : ℕ) → vecOf b M l1 j = 0 := by
    intro j hj
    rw [vecOf_apply, dg]
    have : b ^ (M - e) = b ^ (M - 1 - j) * b ^ ((j : ℕ) + 1 - e) := by rw [← pow_add]; congr 1; omega
    have hs1' := Nat.dvd_of_mod_eq_zero hs1
    rw [this] at hs1'
    obtain ⟨k, hk⟩ := hs1'
    rw [hk, Nat.mul_assoc, Nat.mul_div_cancel_left _ (pow_pos (Nat.pos_of_neZero b) _)]
    obtain ⟨t, ht⟩ : ∃ t, (j : ℕ) + 1 - e = t + 1 := ⟨(j : ℕ) - e, by omega⟩
    rw [ht, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_mod_right]
    simp
  have hl2 : ∀ j : Fin M, M + 1 - e ≤ (j : ℕ) → vecOf b M l2 j = 0 := by
    intro j hj
    rw [vecOf_apply, dg]
    have : b ^ (e - 1) = b ^ (M - 1 - j) * b ^ ((j : ℕ) + e - M) := by rw [← pow_add]; congr 1; omega
    have hs2' := Nat.dvd_of_mod_eq_zero hs2
    rw [this] at hs2'
    obtain ⟨k, hk⟩ := hs2'
    rw [hk, Nat.mul_assoc, Nat.mul_div_cancel_left _ (pow_pos (Nat.pos_of_neZero b) _)]
    obtain ⟨t, ht⟩ : ∃ t, (j : ℕ) + e - M = t + 1 := ⟨(j : ℕ) + e - M - 1, by omega⟩
    rw [ht, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_mod_right]
    simp
  have hZ : Zsub b M e ≤ LinearMap.ker f := by
    intro u hu
    rw [LinearMap.mem_ker, hf]
    have a : vecOf b M l1 ⬝ᵥ u.1 = 0 := Finset.sum_eq_zero fun j _ => by
      by_cases hj : (j : ℕ) < e
      · rw [hu.1 j hj, mul_zero]
      · rw [hl1 j (by omega), zero_mul]
    have b' : vecOf b M l2 ⬝ᵥ u.2 = 0 := Finset.sum_eq_zero fun j _ => by
      by_cases hj : (j : ℕ) < M + 1 - e
      · rw [hu.2 j hj, mul_zero]
      · rw [hl2 j (by omega), zero_mul]
    rw [a, b', add_zero]
  have hPk : pairSub (colMat b M cols) c c' ≤ LinearMap.ker f := by
    rintro _ ⟨n, rfl⟩
    rw [LinearMap.mem_ker, hf]
    change vecOf b M l1 ⬝ᵥ (colMat b M cols c *ᵥ n) + vecOf b M l2 ⬝ᵥ (colMat b M cols c' *ᵥ n) = 0
    rw [dotProduct_mulVec, dotProduct_mulVec, ← add_dotProduct]
    have hv : vecOf b M l1 ᵥ* colMat b M cols c + vecOf b M l2 ᵥ* colMat b M cols c' = 0 := by
      funext i
      have := hP i i.isLt
      have e1 : ((dotc b M l1 ((cols.getD c []).getD i 0) + dotc b M l2 ((cols.getD c' []).getD i 0) : ℕ) :
          ZMod b) = 0 := by
        rw [← ZMod.natCast_mod, this]; simp
      push_cast at e1
      rw [dotc_eq, dotc_eq] at e1
      simp only [Pi.add_apply, Pi.zero_apply]
      exact e1
    rw [hv, zero_dotProduct]
  intro hmem
  have := (sup_le hPk hZ) hmem
  rw [LinearMap.mem_ker, hf] at this
  have h0 : ((dotc b M l1 s1 + dotc b M l2 s2 : ℕ) : ZMod b) = 0 := by
    push_cast; rw [dotc_eq, dotc_eq]; exact this
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact hs (Nat.mod_eq_zero_of_dvd h0)

end Z3NetB23.Proofs

module
public import Z3Net.KNNetWm

@[expose] public section

/-!
# From a design certificate to a net for every `k` (KN entry, `KN1_net` / `KN2_net`)

`net_of_cert1`, `net_of_cert2`: if a design `R` has a certificate (`CertOK`: a gauge from the
constant window `Can r` to the design's windows, invertible target pivot blocks, zero design rows
between the pivot levels and the window), then for every `k ≥ 3` resp. `k ≥ 2` there is a
`(0, 3k+r, 3)`-net over `𝔽_p` with exactly the rows `R` (`IsKN`).

Proof: the frame's graph form has the windows `Wcf r` (`Wm_eq1`, `Wm_eq2`), which the explicit
gauge `h r` moves to `Can r` (`act_h1`, `act_h2`); composing with the certificate gives a gauge from
the frame to the design for this `k`; `realize` builds the net.
-/

namespace Z3NetKN.NetKN

open Matrix Z3NetKN.Realize Z3NetKN.Gauge Z3NetKN.Frame Z3NetKN.Phi

section Tri

variable {F : Type*} [CommRing F]

lemma tri_congr (L : Matrix (Fin 2) (Fin 2) F) (hL : L 0 1 = 0) (U : Matrix (Fin 3) (Fin 3) F)
    (hU : ∀ a b : Fin 3, b < a → U a b = 0) (W W' : Matrix (Fin 2) (Fin 3) F) (g n : ℕ)
    (h : ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < g → (i : ℕ) < n → W ρ i = W' ρ i)
    (ρ : Fin 2) (i : Fin 3) (hρ : (ρ : ℕ) < g) (hi : (i : ℕ) < n) :
    (L * W * U) ρ i = (L * W' * U) ρ i := by
  simp only [mul_apply]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : i < b
  · rw [hU b i hb, mul_zero, mul_zero]
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : ρ < a
    · have h0 : ρ = 0 := by fin_cases ρ <;> fin_cases a <;> simp_all
      have h1 : a = 1 := by fin_cases ρ <;> fin_cases a <;> simp_all
      rw [h0, h1, hL, zero_mul, zero_mul]
    · have hb' : (b : ℕ) ≤ i := by simp only [not_lt] at hb; exact hb
      have ha' : (a : ℕ) ≤ ρ := by simp only [not_lt] at ha; exact ha
      rw [h a b (by omega) (by omega)]

lemma low2_mul (A B : Matrix (Fin 2) (Fin 2) F) (hA : A 0 1 = 0) (hB : B 0 1 = 0) :
    (A * B) 0 1 = 0 ∧ ∀ a : Fin 2, (A * B) a a = A a a * B a a := by
  refine ⟨?_, ?_⟩
  · simp [mul_apply, Fin.sum_univ_two, hA, hB]
  · intro a; fin_cases a <;> simp [mul_apply, Fin.sum_univ_two, hA, hB]

lemma up3_mul (A B : Matrix (Fin 3) (Fin 3) F) (hA : ∀ a b : Fin 3, b < a → A a b = 0)
    (hB : ∀ a b : Fin 3, b < a → B a b = 0) :
    (∀ a b : Fin 3, b < a → (A * B) a b = 0) ∧ ∀ a : Fin 3, (A * B) a a = A a a * B a a := by
  have a10 := hA 1 0 (by decide); have a20 := hA 2 0 (by decide); have a21 := hA 2 1 (by decide)
  have b10 := hB 1 0 (by decide); have b20 := hB 2 0 (by decide); have b21 := hB 2 1 (by decide)
  refine ⟨?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab <;>
      simp [mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · intro a
    fin_cases a <;> simp [mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]

/-- Composition of the frame gauge `(Lh, Uh, μh)` with a certificate gauge. -/
lemma hW_of (g P : Fin 3 → ℕ) (Wm Wcf Can : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F)
    (Lh : Fin 3 → Matrix (Fin 2) (Fin 2) F) (hLh : ∀ c, Lh c 0 1 = 0)
    (Uh : Fin 3 → Matrix (Fin 3) (Fin 3) F) (hUh : ∀ d (a b : Fin 3), b < a → Uh d a b = 0)
    (μh : Fin 3 → Fin 3 → F)
    (hcan : ∀ c d, c ≠ d → act Lh Uh μh Wcf c d = Can c d)
    (hwm : ∀ c d, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < g c → (i : ℕ) + 1 < P d →
      Wm c d ρ i = Wcf c d ρ i)
    (L₀ : Fin 3 → Matrix (Fin 2) (Fin 2) F) (hL₀ : ∀ c, L₀ c 0 1 = 0)
    (U₀ : Fin 3 → Matrix (Fin 3) (Fin 3) F) (hU₀ : ∀ d (a b : Fin 3), b < a → U₀ d a b = 0)
    (μ₀ : Fin 3 → Fin 3 → F) (Tgt : Fin 3 → Fin 3 → ℕ → ℕ → F)
    (hcert : ∀ c d, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < g c → (i : ℕ) + 1 < P d →
      act L₀ U₀ μ₀ Can c d ρ i = Tgt c d ρ i) :
    ∀ c d, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < g c → (i : ℕ) + 1 < P d →
      Tgt c d ρ i = (μ₀ c d * μh c d) * ((L₀ c * Lh c) * Wm c d * (Uh d * U₀ d)) ρ i := by
  intro c d hcd ρ i hρ hi
  rw [← hcert c d hcd ρ i hρ hi]
  simp only [act, Matrix.smul_apply, smul_eq_mul]
  rw [← hcan c d hcd]
  simp only [act]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [tri_congr (L₀ c) (hL₀ c) (U₀ d) (hU₀ d) _ (Lh c * Wm c d * Uh d) (g c) (P d - 1)
    (fun ρ' i' hρ' hi' => tri_congr (Lh c) (hLh c) (Uh d) (hUh d) (Wcf c d) (Wm c d) (g c) (P d - 1)
      (fun ρ'' i'' h1 h2 => (hwm c d hcd ρ'' i'' h1 (by omega)).symm) ρ' i' hρ' hi') ρ i hρ
      (by omega)]
  simp only [Matrix.mul_assoc]
  ring

end Tri

/-- `winEntry` against the realized values (pivot count `P ≤` window `L ≤ 4`). -/
lemma winEntry_cast (p : ℕ) (row : Fin 4 → ℤ) (L K l P : ℕ) (hP : P ≤ L) (hL4 : L ≤ 4)
    (hz : ∀ i : Fin 4, P ≤ (i : ℕ) → (i : ℕ) < L → row i = 0) :
    (if K - 1 - l < P then (((if h : K - 1 - l < 4 then row ⟨K - 1 - l, h⟩ else 0 : ℤ)) : ZMod p)
      else 0) = ((winEntry row L K l : ℤ) : ZMod p) := by
  unfold winEntry
  by_cases h1 : K - 1 - l < P
  · rw [if_pos h1, dif_pos (by omega), dif_pos (by omega), if_pos (by omega)]
  · rw [if_neg h1]
    by_cases h4 : K - 1 - l < 4
    · rw [dif_pos h4]
      by_cases hL : K - 1 - l < L
      · rw [if_pos hL, hz ⟨K - 1 - l, h4⟩ (by simp; omega) hL]; simp
      · rw [if_neg hL]; simp
    · rw [dif_neg h4]; simp

/-- Own-cell values of the designed rows. -/
def OwnV (r p k : ℕ) (R : Rows) (c : Fin 3) (i l : ℕ) : ZMod p :=
  if i < depth r k c + gF r c then
    ((winEntry (geoRow r R c (i - depth r k c) c) (win r c) (depth r k c) l : ℤ) : ZMod p)
  else 0

lemma PF_le_win (r : ℕ) (hr : r = 1 ∨ r = 2) (d : Fin 3) : PF r d ≤ win r d := by
  rcases hr with rfl | rfl <;> fin_cases d <;> decide

lemma win_le4 (r : ℕ) (d : Fin 3) : win r d ≤ 4 := by unfold win; split_ifs <;> omega

/-- The realized conditions give `IsKN`. -/
theorem isKN_of (r p k : ℕ) [Fact p.Prime] (hr : r = 1 ∨ r = 2) (hk : 4 ≤ k + r) (R : Rows)
    (C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p))
    (hGF : IsGF C (depth r k))
    (hgeo : ∀ c d, c ≠ d → ∀ ρ, ρ < gF r c → ∀ l, l < depth r k d →
      ent (C c) (depth r k c + ρ) (offK (depth r k) d + l) =
        if depth r k d - 1 - l < PF r d then Tgt r p R c d ρ (depth r k d - 1 - l) else 0)
    (hown : ∀ c (i l : ℕ), depth r k c ≤ i → i < 3 * k + r → l < depth r k c →
      ent (C c) i (offK (depth r k) c + l) = OwnV r p k R c i l)
    (hzero : ∀ c d : Fin 3, c ≠ d → ∀ ρ : Fin 2, (ρ : ℕ) < gF r c → ∀ i : Fin 4, PF r d ≤ (i : ℕ) →
      (i : ℕ) < win r d → geoRow r R c ρ d i = 0) :
    IsKN r p k R C := by
  have hsum := depth_sum r k (by omega)
  have hdm : ∀ c, depth r k c + gF r c ≤ 3 * k + r := by
    intro c; rcases hr with rfl | rfl <;> fin_cases c <;> simp [depth, gF] <;> omega
  -- rows `depth c + ρ`, `ρ < gF r c`, on a cell `d ≠ c`
  have hrow : ∀ c d, c ≠ d → ∀ ρ, ρ < gF r c → ∀ l, l < depth r k d →
      ent (C c) (depth r k c + ρ) (offK (depth r k) d + l) =
        ((winEntry (geoRow r R c ρ d) (win r d) (depth r k d) l : ℤ) : ZMod p) := by
    intro c d hcd ρ hρ l hl
    rw [hgeo c d hcd ρ hρ l hl]
    have hg2 : gF r c ≤ 2 := by unfold gF; split_ifs <;> omega
    exact winEntry_cast p _ _ _ _ _ (PF_le_win r hr d) (win_le4 r d)
      (fun i h1 h2 => hzero c d hcd ⟨ρ, by omega⟩ hρ i h1 h2)
  have hownv : ∀ c ρ, ρ < gF r c → ∀ l, l < depth r k c →
      ent (C c) (depth r k c + ρ) (offK (depth r k) c + l) =
        ((winEntry (geoRow r R c ρ c) (win r c) (depth r k c) l : ℤ) : ZMod p) := by
    intro c ρ hρ l hl
    rw [hown c _ l (by omega) (by have := hdm c; omega) hl]
    simp only [OwnV, if_pos (show depth r k c + ρ < depth r k c + gF r c by omega),
      Nat.add_sub_cancel_left]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro c j col hj hcol
    have hjm : j < 3 * k + r := by have := hdm c; omega
    unfold ent
    rw [dif_pos ⟨hjm, hcol⟩, hGF c ⟨j, hjm⟩ ⟨col, hcol⟩ hj, off_eq]
  · intro c d hc l hl
    have hρ : 0 < gF r c := by unfold gF; split_ifs <;> omega
    have hg0 : geoRow r R c 0 = R.sk c := by
      unfold geoRow; rw [if_neg (by omega), if_pos rfl]
    rw [off_eq, ← add_zero (depth r k c)]
    by_cases hcd : c = d
    · subst hcd; rw [hownv c 0 hρ l hl, hg0]
    · rw [hrow c d hcd 0 hρ l hl, hg0]
  · intro c d l hl
    set ρ : ℕ := if (c : ℕ) < r then 0 else 1 with hρd
    have hρ : ρ < gF r c := by simp only [hρd, gF]; split_ifs <;> omega
    have hj : jrow r k c = depth r k c + ρ := by
      simp only [jrow, hρd]; split_ifs <;> simp_all [depth]
    have hgj : geoRow r R c ρ = R.jt c := by
      unfold geoRow; simp only [hρd]; split_ifs <;> simp_all
    rw [off_eq, hj]
    by_cases hcd : c = d
    · subst hcd; rw [hownv c ρ hρ l hl, hgj]
    · rw [hrow c d hcd ρ hρ l hl, hgj]
  · intro c i l hi him hl
    have hj : jrow r k c + 1 = depth r k c + gF r c := by
      simp only [jrow, gF]; split_ifs <;> omega
    rw [off_eq, hown c i l (by omega) him hl]
    simp only [OwnV, if_neg (show ¬ i < depth r k c + gF r c by omega)]

lemma two_ne_zero_zmod (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

lemma tpad_unit (r p : ℕ) [Fact p.Prime] (R : Rows) (X : Cert p)
    (hTi : ∀ (d : Fin 3) (a b : Fin 4), tiE r p R X d a b = if a = b then 1 else 0) (d : Fin 3) :
    IsUnit (TpadF r p R d) := by
  have h : TpadF r p R d * X.Tim d = 1 := by
    ext a b
    have := hTi d a b
    simp only [tiE] at this
    rw [this, Matrix.one_apply]
  exact @isUnit_of_invertible _ _ _ (invertibleOfRightInverse _ _ h)

/-- **From a certificate to nets for every `k`** (generic in the frame gauge). -/
theorem net_of_cert_gen (r p k : ℕ) [Fact p.Prime] (hr : r = 1 ∨ r = 2) (hk : 4 ≤ k + r)
    (R : Rows) (X : Cert p) (hX : CertOK r p R X)
    (Wcf : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) (ZMod p))
    (Lh : Fin 3 → Matrix (Fin 2) (Fin 2) (ZMod p)) (hLh : ∀ c, Lh c 0 1 = 0)
    (hLhd : ∀ c (a : Fin 2), Lh c a a = 1)
    (Uh : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p)) (hUh : ∀ d (a b : Fin 3), b < a → Uh d a b = 0)
    (hUhd : ∀ d (a : Fin 3), Uh d a a = 1)
    (μh : Fin 3 → Fin 3 → ZMod p) (hμh : ∀ c d, μh c d ≠ 0)
    (hcan : ∀ c d, c ≠ d → act Lh Uh μh Wcf c d = Can r c d)
    (hwm : ∀ c d, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < gF r c → (i : ℕ) + 1 < PF r d →
      Wm (depth r k) (G0 (F := ZMod p) (m := 3 * k + r) (depth r k)) c d ρ i = Wcf c d ρ i) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + r)) (Fin (3 * k + r)) (ZMod p),
      IsKN r p k R C ∧ IsNet0 p (3 * k + r) (digPoint p (3 * k + r) C) := by
  obtain ⟨hL0, hLd, hU0, hUd, hμ0, hact, hTi, hzero⟩ := hX
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set S := setup r k hr hk with hS
  set G := G0 (F := ZMod p) (m := 3 * k + r) (depth r k) with hGd
  have hG : T0 G := G0_T0 _ (depth_sum r k (by omega))
  have hGF : IsGF G S.K := G0_GF _ (depth_sum r k (by omega))
  have hLm0 : ∀ c, X.Lm c 0 1 = 0 := fun c => hL0 c
  have hUm0 : ∀ d (a b : Fin 3), b < a → X.Um d a b = 0 := fun d a b h => hU0 d a b h
  let L : Fin 3 → Matrix (Fin 2) (Fin 2) (ZMod p) := fun c => X.Lm c * Lh c
  let U : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod p) := fun d => Uh d * X.Um d
  let μ : Fin 3 → Fin 3 → ZMod p := fun c d => X.μ c d * μh c d
  have hL : ∀ c, L c 0 1 = 0 := fun c => (low2_mul _ _ (hLm0 c) (hLh c)).1
  have hLdd : ∀ c (a : Fin 2), (a : ℕ) < S.g c → L c a a ≠ 0 := by
    intro c a ha
    simp only [L]
    rw [(low2_mul _ _ (hLm0 c) (hLh c)).2 a, hLhd, mul_one]
    exact hLd c a ha
  have hU : ∀ d (a b : Fin 3), b < a → U d a b = 0 := fun d => (up3_mul _ _ (hUh d) (hUm0 d)).1
  have hUdd : ∀ d (a : Fin 3), (a : ℕ) + 1 < S.P d → U d a a ≠ 0 := by
    intro d a ha
    simp only [U]
    rw [(up3_mul _ _ (hUh d) (hUm0 d)).2 a, hUhd, one_mul]
    exact hUd d a ha
  have hμ : ∀ c d, c ≠ d → μ c d ≠ 0 := fun c d hcd => mul_ne_zero (hμ0 c d hcd) (hμh c d)
  have hW : ∀ c d, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < S.g c → (i : ℕ) + 1 < S.P d →
      Tgt r p R c d ρ i = μ c d * (L c * Wm S.K G c d * U d) ρ i :=
    hW_of (gF r) (PF r) (Wm (depth r k) G) Wcf (Can r) Lh hLh Uh hUh μh hcan hwm X.Lm hLm0 X.Um hUm0
      X.μ (Tgt r p R) hact
  have hdet : ∀ d, IsUnit (Tpad S (Tgt r p R) d) := fun d => tpad_unit r p R X hTi d
  obtain ⟨C, hCT, hCGF, hgeo, hown⟩ :=
    realize S G hG hGF L hL hLdd U hU hUdd μ hμ (Tgt r p R) hW hdet (OwnV r p k R)
  exact ⟨C, isKN_of r p k hr hk R C hCGF hgeo hown hzero, hCT.isNet0⟩

theorem net_of_cert1 (p k : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hk : 3 ≤ k) (R : Rows) (X : Cert p)
    (hX : CertOK 1 p R X) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKN 1 p k R C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) := by
  have h2 := two_ne_zero_zmod p hp5
  have hs : ((-1 : ZMod p) ^ k) = 1 ∨ ((-1 : ZMod p) ^ k) = -1 := neg_one_pow_eq_or _ k
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hs0 : ((-1 : ZMod p) ^ k) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr h1)
  refine net_of_cert_gen 1 p k (Or.inl rfl) (by omega) R X hX (Wcf1 (k : ZMod p) ((-1) ^ k))
    (hL1 (k : ZMod p)) (fun c => by fin_cases c <;> simp [hL1])
    (fun c a => by fin_cases c <;> fin_cases a <;> simp [hL1])
    (hU1 (k : ZMod p)) (fun d a b hab => by fin_cases d <;> fin_cases a <;> fin_cases b <;> simp_all [hU1])
    (fun d a => by fin_cases d <;> fin_cases a <;> simp [hU1])
    (hμ1 ((-1) ^ k)) (fun c d => by fin_cases c <;> fin_cases d <;> simp [hμ1, hs0])
    (fun c d hcd => by rw [Can, if_pos rfl]; exact act_h1 _ _ h2 hs c d hcd)
    (Wm_eq1 h2 k hk)

theorem net_of_cert2 (p k : ℕ) [Fact p.Prime] (hk : 2 ≤ k) (R : Rows) (X : Cert p)
    (hX : CertOK 2 p R X) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 2)) (Fin (3 * k + 2)) (ZMod p),
      IsKN 2 p k R C ∧ IsNet0 p (3 * k + 2) (digPoint p (3 * k + 2) C) := by
  have hs : ((-1 : ZMod p) ^ k) = 1 ∨ ((-1 : ZMod p) ^ k) = -1 := neg_one_pow_eq_or _ k
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hs0 : ((-1 : ZMod p) ^ k) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr h1)
  refine net_of_cert_gen 2 p k (Or.inr rfl) (by omega) R X hX (Wcf2 (k : ZMod p) ((-1) ^ k))
    (hL2 (k : ZMod p)) (fun c => by fin_cases c <;> simp [hL2])
    (fun c a => by fin_cases c <;> fin_cases a <;> simp [hL2])
    (hU2 (k : ZMod p)) (fun d a b hab => by fin_cases d <;> fin_cases a <;> fin_cases b <;> simp_all [hU2])
    (fun d a => by fin_cases d <;> fin_cases a <;> simp [hU2])
    (hμ2 ((-1) ^ k)) (fun c d => by fin_cases c <;> fin_cases d <;> simp [hμ2, hs0])
    (fun c d hcd => by rw [Can, if_neg (by norm_num)]; exact act_h2 _ _ hs c d hcd)
    (Wm_eq2 k hk)

end Z3NetKN.NetKN

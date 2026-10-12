module
public import Mathlib
public import Z3Net.KNRelax
public import Z3Net.KNGeomBasic

@[expose] public section

/-!
# KN separation, part 2: the carry lemma and window sums

For two numbers `a, b ∈ [0, p^K)` with `a - b ≡ δ (mod p^K)`, `|δ| < p`, the level-`i` digits
(`i = 0` least significant) change by `pat δ ch i` (`δ` at level `0`, `sgn δ` on levels
`1..ch`, `0` above) for some chain length `ch < min K L`, at all levels `i < min K L`.
-/

namespace Z3NetKN.Geom

open Finset Z3NetKN.Relax

/-- Digit-change pattern of a step `δ` with carry chain of length `ch`. -/
def pat (δ : ℤ) (ch i : ℕ) : ℤ := if i = 0 then δ else if i ≤ ch then sgn δ else 0

lemma digit_of_mod (p K i x : ℕ) (hi : i < K) : x % p ^ K / p ^ i % p = x / p ^ i % p := by
  rw [show p ^ K = p ^ i * p ^ (K - i) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega))]

/-- A nonincreasing `0/1` sequence (from index `1`) is the indicator of an initial segment. -/
lemma chain_exists (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℕ) (h1 : ∀ i, 1 ≤ i → q i ≤ 1)
    (hm : ∀ i, q i = 0 → q (i + 1) = 0) :
    ∃ ch < n, ∀ i, 1 ≤ i → i < n → q i = if i ≤ ch then 1 else 0 := by
  have hz : ∀ i j, i ≤ j → q i = 0 → q j = 0 := by
    intro i j hij hi
    induction j, hij using Nat.le_induction with
    | base => exact hi
    | succ j _ ih => exact hm j ih
  induction n, hn using Nat.le_induction with
  | base => exact ⟨0, by omega, fun i h1 h2 => by omega⟩
  | succ n hn ih =>
    obtain ⟨ch, hch, hq⟩ := ih
    by_cases hqn : q n = 0
    · refine ⟨ch, by omega, fun i hi1 hi2 => ?_⟩
      rcases Nat.lt_or_ge i n with h | h
      · exact hq i hi1 h
      · rw [show i = n by omega, hqn, if_neg (by omega)]
    · refine ⟨n, by omega, fun i hi1 hi2 => ?_⟩
      rw [if_pos (by omega)]
      have := h1 i hi1
      by_contra hc
      exact hqn (hz i n (by omega) (by omega))

lemma carry_pos (p K L : ℕ) (hp : 1 < p) (hK : 1 ≤ K) (hL1 : 1 ≤ L) (hL : L ≤ 4) (a b : ℕ)
    (ha : a < p ^ K) (δ z : ℤ) (h0 : 0 ≤ δ) (hδ : δ < p) (h : (a : ℤ) - b = δ + z * (p ^ K : ℕ)) :
    ∃ ch, ch < min K L ∧ (δ = 0 → ch = 0) ∧ ∀ i < min K L,
      ((a / p ^ i % p : ℕ) : ZMod p) - ((b / p ^ i % p : ℕ) : ZMod p) = ((pat δ ch i : ℤ) : ZMod p) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, δ = d := ⟨δ.toNat, (Int.toNat_of_nonneg h0).symm⟩
  have hd : d < p := by exact_mod_cast hδ
  set P := p ^ K with hP
  have hP0 : 0 < P := by positivity
  -- a = (b + d) % P
  have haP : a = (b + d) % P := by
    have e1 : ((b + d : ℕ) : ℤ) = a + (-z) * (P : ℤ) := by push_cast; linarith
    have e2 : ((b + d : ℕ) : ℤ) % (P : ℤ) = a := by
      rw [e1, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
    exact_mod_cast e2.symm
  -- q i
  set q : ℕ → ℕ := fun i => (b + d) / p ^ i - b / p ^ i with hq
  have hle : ∀ i, b / p ^ i ≤ (b + d) / p ^ i := fun i => Nat.div_le_div_right (by omega)
  have hdig : ∀ i < K, ((a / p ^ i % p : ℕ) : ZMod p) - ((b / p ^ i % p : ℕ) : ZMod p) =
      ((q i : ℕ) : ZMod p) := by
    intro i hi
    rw [haP, digit_of_mod p K i _ hi, ZMod.natCast_mod, ZMod.natCast_mod, hq]
    simp only
    rw [Nat.cast_sub (hle i)]
  have hq0 : q 0 = d := by simp [hq]
  have hq1 : ∀ i, 1 ≤ i → q i ≤ 1 := by
    intro i hi
    have hpi : p ≤ p ^ i := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi
    have : (b + d) / p ^ i ≤ b / p ^ i + 1 := by
      calc (b + d) / p ^ i ≤ (b + p ^ i) / p ^ i := Nat.div_le_div_right (by omega)
        _ = b / p ^ i + 1 := Nat.add_div_right _ (by positivity)
    simp only [hq]; omega
  have hmono : ∀ i, q i = 0 → q (i + 1) = 0 := by
    intro i hi
    simp only [hq] at hi ⊢
    have e : (b + d) / p ^ i = b / p ^ i := by have := hle i; omega
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e]; simp
  set n := min K L with hn
  have hn1 : 1 ≤ n := by omega
  rcases Nat.eq_zero_or_pos d with hd' | hd'
  · subst hd'
    refine ⟨0, by omega, fun _ => rfl, fun i hi => ?_⟩
    rw [hdig i (by omega)]
    have : q i = 0 := by simp [hq]
    rw [this]; simp only [pat]; split_ifs <;> first | omega | simp
  · obtain ⟨ch, hch, hcq⟩ := chain_exists n hn1 q hq1 hmono
    refine ⟨ch, hch, fun h => by omega, fun i hi => ?_⟩
    rw [hdig i (by omega), ← Int.cast_natCast]
    congr 1
    have s1 : sgn (d : ℤ) = 1 := by simp [sgn]; omega
    simp only [pat, s1]
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; simp [hq0]
    · rw [if_neg (by omega), hcq i h0 hi]; split_ifs <;> simp

/-- **Carry lemma** (both signs). -/
lemma carry (p K L : ℕ) (hp : 1 < p) (hK : 1 ≤ K) (hL1 : 1 ≤ L) (hL : L ≤ 4) (a b : ℕ)
    (ha : a < p ^ K) (hb : b < p ^ K) (δ z : ℤ) (hδ : |δ| < p)
    (h : (a : ℤ) - b = δ + z * (p ^ K : ℕ)) :
    ∃ ch, ch < min K L ∧ (δ = 0 → ch = 0) ∧ ∀ i < min K L,
      ((a / p ^ i % p : ℕ) : ZMod p) - ((b / p ^ i % p : ℕ) : ZMod p) = ((pat δ ch i : ℤ) : ZMod p) := by
  rcases le_or_gt 0 δ with h0 | h0
  · exact carry_pos p K L hp hK hL1 hL a b ha δ z h0 (lt_of_le_of_lt (le_abs_self δ) hδ) h
  · obtain ⟨ch, h1, _, h3⟩ := carry_pos p K L hp hK hL1 hL b a hb (-δ) (-z) (by omega)
      (by rw [abs_of_neg h0] at hδ; exact hδ) (by push_cast at h ⊢; linarith)
    refine ⟨ch, h1, fun h => by omega, fun i hi => ?_⟩
    have := h3 i hi
    rw [← neg_sub, this]
    simp only [pat, sgn]
    split_ifs <;> first | (exfalso; omega) | (push_cast; ring)

/-! ## Window sums -/

/-- Total accessor of a designed row. -/
def rowN (row : Fin 4 → ℤ) (i : ℕ) : ℤ := if h : i < 4 then row ⟨i, h⟩ else 0

lemma winEntry_eq (row : Fin 4 → ℤ) (L K l : ℕ) (hL : L ≤ 4) :
    winEntry row L K l = if K - 1 - l < L then rowN row (K - 1 - l) else 0 := by
  unfold winEntry rowN; split_ifs <;> first | rfl | omega

lemma lin1_eq (row : Fin 4 → ℤ) (δ : ℤ) (ch : ℕ) (hch : ch < 4) :
    ∑ i ∈ range (ch + 1), rowN row i * pat δ ch i = lin1 row δ ch := by
  interval_cases ch <;> simp [Finset.sum_range_succ, rowN, pat, lin1] <;> ring

/-- Window sum: the change of a designed linear form restricted to one block. -/
lemma window_sum {p : ℕ} (row : Fin 4 → ℤ) (L K : ℕ) (hL : L ≤ 4) (D : ℕ → ZMod p) (δ : ℤ)
    (ch : ℕ) (hch : ch < min K L)
    (hD : ∀ l < K, K - 1 - l < L → D l = ((pat δ ch (K - 1 - l) : ℤ) : ZMod p)) :
    ∑ l ∈ range K, ((winEntry row L K l : ℤ) : ZMod p) * D l = ((lin1 row δ ch : ℤ) : ZMod p) := by
  rw [← sum_range_reflect]
  have e1 : ∀ i ∈ range K, ((winEntry row L K (K - 1 - i) : ℤ) : ZMod p) * D (K - 1 - i) =
      ((if i < ch + 1 then rowN row i * pat δ ch i else 0 : ℤ) : ZMod p) := by
    intro i hi
    simp only [mem_range] at hi
    rw [winEntry_eq row L K _ hL, show K - 1 - (K - 1 - i) = i by omega]
    by_cases hiL : i < L
    · rw [if_pos hiL, hD _ (by omega) (by omega), show K - 1 - (K - 1 - i) = i by omega]
      split_ifs with h
      · push_cast; ring
      · simp only [pat]; rw [if_neg (by omega), if_neg (by omega)]; simp
    · rw [if_neg hiL, if_neg (by omega)]; simp
  rw [sum_congr rfl e1, ← Int.cast_sum, ← lin1_eq row δ ch (by omega)]
  congr 1
  rw [← sum_range_add_sum_Ico _ (show ch + 1 ≤ K by omega)]
  rw [sum_eq_zero (s := Ico (ch + 1) K) (fun i hi => by simp only [mem_Ico] at hi; rw [if_neg (by omega)])]
  rw [add_zero]
  exact sum_congr rfl fun i hi => by simp only [mem_range] at hi; rw [if_pos hi]

end Z3NetKN.Geom

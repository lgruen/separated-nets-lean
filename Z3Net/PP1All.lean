/-
Proof module (stage 11, entry KNPP): `prop:pp1` for every prime `p`, including `p = 2`.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Z3Net.PP1
public import Z3Net.PPInvVal

@[expose] public section

/-!
# `prop:pp1` in every characteristic

`PP1.pp1_net` (stage 6) assumes `p ≠ 2`: the closed form `Wcf1` of the frame's windows
(`KNNetGauge`) contains `k(k+1)/2`, `(k+1)(k+2)/2`, … as field quotients, which are meaningless in
characteristic `2`.  Here these entries are written with `b = C(k, 2) + k = C(k+1, 2)` (the cast of a
natural number): `Wcf1b a b S`, the gauge `hU1b a b`, and `act_h1b` (the gauge identity holds in
every field, given `2 b = a² + a`).  The frame's windows are `Wcf1b` in every
characteristic (`Wm_eq1b`, from `win1_xi2'` of entry PPInv, which needs no `2 ≠ 0`).  The design
side (`PP1.cert1`, `PP1.cert1_ok`) never needed `2 ≠ 0`.
-/

namespace Z3NetKN.PP1All

open Matrix Z3NetKN.NetKN Z3NetKN.Gauge Z3NetKN.Realize Z3NetKN.Frame Z3NetKN.Phi Z3NetKN.Win

section Gauge

variable {F : Type*} [Field F]

/-- The frame's windows for `m = 3k + 1` with `b = C(k+1, 2)` in place of `k(k+1)/2`. -/
def Wcf1b (a b S : F) : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F :=
  ![![0, !![S, a * S, 0; 0, 0, 0], !![1, -a, 0; 0, 0, 0]],
    ![!![S, a * S, S * b; -(a * S), -((a ^ 2 - 1) * S), -(S * (a * b - a))], 0,
      !![-S, (a + 1) * S, 0; (a - 1) * S, (2 - a ^ 2) * S, 0]],
    ![!![1, a + 1, b + a + 1; a, a ^ 2 + a + 1, a * b + a ^ 2 + 2 * a + 2],
      !![S, (a + 1) * S, 0; (a - 1) * S, (a ^ 2 - 2) * S, 0], 0]]

/-- The gauge `hU1` with `b` in place of `a(a+1)/2`. -/
def hU1b (a b : F) : Fin 3 → Matrix (Fin 3) (Fin 3) F :=
  ![!![1, -a, b; 0, 1, -(a + 1); 0, 0, 1], !![1, -a, 0; 0, 1, 0; 0, 0, 1],
    !![1, a, 0; 0, 1, 0; 0, 0, 1]]

theorem act_h1b (a b S : F) (hb : 2 * b = a * a + a) (hS : S = 1 ∨ S = -1) (c d : Fin 3)
    (hcd : c ≠ d) : act (hL1 a) (hU1b a b) (hμ1 S) (Wcf1b a b S) c d = Can1 c d := by
  rcases hS with rfl | rfl <;>
  fin_cases c <;> fin_cases d <;> (first | exact absurd rfl hcd | skip) <;>
  ext ρ i <;> fin_cases ρ <;> fin_cases i <;>
  simp [act, Wcf1b, Can1, hL1, hU1b, hμ1, Matrix.mul_apply, Fin.sum_univ_succ] <;>
  first | ring1 | linear_combination hb | linear_combination (-1 : F) * hb

end Gauge

section Frame

variable {F : Type*} [Field F]

theorem Wm_eq1b (k : ℕ) (hk : 3 ≤ k) :
    ∀ c d : Fin 3, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < gF 1 c → (i : ℕ) + 1 < PF 1 d →
      Wm (depth 1 k) (G0 (F := F) (m := 3 * k + 1) (depth 1 k)) c d ρ i =
        Wcf1b (k : F) ((k.choose 2 : ℕ) + (k : F)) ((-1) ^ k) c d ρ i := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have x0 := win1_xi0 (F := F) (j + 3) (by omega)
  have x1 := win1_xi1 (F := F) (j + 2)
  have x2 := Z3NetPI.Val.win1_xi2' (F := F) (j + 1)
  have e0 := win1_eta0 (F := F) (j + 2)
  have e1 := win1_eta1 (F := F) (j + 1)
  have z0 := win1_zeta0 (F := F) (j + 2)
  have z1 := win1_zeta1 (F := F) (j + 1)
  have f1000 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 0 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 0 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x0.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f1010 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 1 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 0 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x0.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2000 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 0 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 0 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x0.2.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2010 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 1 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 0 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x0.2.2.2).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f1001 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 0 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 0 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x1.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f1011 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 1 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 0 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x1.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2001 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 0 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 0 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x1.2.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2011 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 1 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 0 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x1.2.2.2).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f1002 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 0 2 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 0 0 2 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f1012 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 1 2 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 0 1 2 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x2.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2002 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 0 2 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 0 0 2 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x2.2.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2012 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 1 2 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 0 1 2 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x2.2.2.2).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f0100 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 0 1 0 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 0 1 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e0.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2100 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 1 0 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 1 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e0.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2110 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 1 1 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 1 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e0.2.2).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f0101 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 0 1 0 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 0 1 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e1.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2101 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 1 0 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 1 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e1.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f2111 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 1 1 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 2 1 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e1.2.2).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f0200 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 0 2 0 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 0 2 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z0.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f1200 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 2 0 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 2 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z0.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f1210 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 2 1 0 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 2 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z0.2.2).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f0201 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 0 2 0 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 0 2 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z1.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f1201 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 2 0 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 2 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z1.2.1).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  have f1211 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 2 1 1 =
      Wcf1b ((j + 3 : ℕ) : F) (((j + 3).choose 2 : ℕ) + ((j + 3 : ℕ) : F)) ((-1) ^ (j + 3)) 1 2 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z1.2.2).trans (by simp [Wcf1b] <;> push_cast <;> field_simp <;> ring))
  intro c d hcd ρ i hρ hi
  fin_cases c <;> fin_cases d <;> fin_cases ρ <;> fin_cases i
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact f0100
  · exact f0101
  · exact absurd hi (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact f0200
  · exact f0201
  · exact absurd hi (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact f1000
  · exact f1001
  · exact f1002
  · exact f1010
  · exact f1011
  · exact f1012
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact f1200
  · exact f1201
  · exact absurd hi (by decide)
  · exact f1210
  · exact f1211
  · exact absurd hi (by decide)
  · exact f2000
  · exact f2001
  · exact f2002
  · exact f2010
  · exact f2011
  · exact f2012
  · exact f2100
  · exact f2101
  · exact absurd hi (by decide)
  · exact f2110
  · exact f2111
  · exact absurd hi (by decide)
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd

end Frame

section Proof

lemma two_b (k : ℕ) {F : Type*} [Field F] :
    2 * (((k.choose 2 : ℕ) : F) + (k : F)) = (k : F) * k + k := by
  have := Z3NetPI.Val.two_choose_cast (F := F) k
  linear_combination this

/-- `net_of_cert1` for every prime `p` (no `2 ≠ 0`). -/
theorem net_of_cert1_all (p k : ℕ) [Fact p.Prime] (hk : 3 ≤ k) (R : Rows) (X : Cert p)
    (hX : CertOK 1 p R X) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKN 1 p k R C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) := by
  have hs : ((-1 : ZMod p) ^ k) = 1 ∨ ((-1 : ZMod p) ^ k) = -1 := neg_one_pow_eq_or _ k
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hs0 : ((-1 : ZMod p) ^ k) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr h1)
  refine net_of_cert_gen 1 p k (Or.inl rfl) (by omega) R X hX
    (Wcf1b (k : ZMod p) ((k.choose 2 : ℕ) + (k : ZMod p)) ((-1) ^ k))
    (hL1 (k : ZMod p)) (fun c => by fin_cases c <;> simp [hL1])
    (fun c a => by fin_cases c <;> fin_cases a <;> simp [hL1])
    (hU1b (k : ZMod p) ((k.choose 2 : ℕ) + (k : ZMod p)))
    (fun d a b hab => by fin_cases d <;> fin_cases a <;> fin_cases b <;> simp_all [hU1b])
    (fun d a => by fin_cases d <;> fin_cases a <;> simp [hU1b])
    (hμ1 ((-1) ^ k)) (fun c d => by fin_cases c <;> fin_cases d <;> simp [hμ1, hs0])
    (fun c d hcd => by rw [Can, if_pos rfl]; exact act_h1b _ _ _ (two_b k) hs c d hcd)
    (Wm_eq1b k hk)

/-- **`prop:pp1`** for every prime `p` (including `p = 2`). -/
theorem pp1_net_all (p k : ℕ) (hp : p.Prime) (R : Rows) (hS : CondS1 R)
    (hN : CondN1 p R) (hJ1 : J1 p R = 1) (hJ2 : J2 p R = -1) (hJ3 : J3 p R = 2)
    (hJ4 : J4 p R = 2) (hJ5 : J5 p R = 1) (hk : 3 ≤ k) :
    ∃ C : Fin 3 → Matrix (Fin (3 * k + 1)) (Fin (3 * k + 1)) (ZMod p),
      IsKN 1 p k R C ∧ IsNet0 p (3 * k + 1) (digPoint p (3 * k + 1) C) := by
  have := Fact.mk hp
  exact net_of_cert1_all p k hk R (PP1.cert1 R) (PP1.cert1_ok R hS hN hJ1 hJ2 hJ3 hJ4 hJ5)

end Proof

end Z3NetKN.PP1All

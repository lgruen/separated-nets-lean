module
public import Z3Net.KNNetDefs

@[expose] public section

/-!
# The frame's windows in closed form, for every `k` (KN entry, `KN1_net` / `KN2_net`)

`Wm_eq1`, `Wm_eq2`: on every needed window entry, the graph form of the frame `(φ_∞, φ_0, φ_1)`
with depths `depth r k` has the closed forms `Wcf1`, `Wcf2` (`a = k`, `S = (-1)^k`), assembled from
the column lemmas of `KNNetWin1`, `KNNetWin2`.
-/

namespace Z3NetKN.NetKN

open Matrix Z3NetKN.Realize Z3NetKN.Gauge Z3NetKN.Frame Z3NetKN.Phi Z3NetKN.Win

variable {F : Type*} [Field F]

lemma ent_idx {R : Type*} [Zero R] {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) {i i' n n' : ℕ}
    (h1 : i = i') (h2 : n = n') : ent A i n = ent A i' n' := by
  subst h1 h2; rfl

theorem Wm_eq1 (h2 : (2 : F) ≠ 0) (k : ℕ) (hk : 3 ≤ k) :
    ∀ c d : Fin 3, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < gF 1 c → (i : ℕ) + 1 < PF 1 d →
      Wm (depth 1 k) (G0 (F := F) (m := 3 * k + 1) (depth 1 k)) c d ρ i =
        Wcf1 (k : F) ((-1) ^ k) c d ρ i := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have x0 := win1_xi0 (F := F) (j + 3) (by omega)
  have x1 := win1_xi1 (F := F) (j + 2)
  have x2 := win1_xi2 (F := F) (j + 1) h2
  have e0 := win1_eta0 (F := F) (j + 2)
  have e1 := win1_eta1 (F := F) (j + 1)
  have z0 := win1_zeta0 (F := F) (j + 2)
  have z1 := win1_zeta1 (F := F) (j + 1)
  have f1000 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 0 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 0 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x0.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f1010 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 1 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 0 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x0.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2000 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 0 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 0 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x0.2.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2010 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 1 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 0 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x0.2.2.2).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f1001 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 0 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 0 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x1.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f1011 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 1 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 0 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x1.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2001 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 0 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 0 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x1.2.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2011 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 1 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 0 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x1.2.2.2).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f1002 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 0 2 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 0 0 2 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f1012 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 0 1 2 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 0 1 2 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x2.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2002 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 0 2 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 0 0 2 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x2.2.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2012 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 0 1 2 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 0 1 2 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((x2.2.2.2).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f0100 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 0 1 0 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 0 1 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e0.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2100 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 1 0 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 1 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e0.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2110 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 1 1 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 1 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e0.2.2).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f0101 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 0 1 0 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 0 1 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e1.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2101 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 1 0 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 1 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e1.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f2111 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 2 1 1 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 2 1 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((e1.2.2).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f0200 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 0 2 0 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 0 2 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z0.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f1200 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 2 0 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 2 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z0.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f1210 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 2 1 0 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 2 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z0.2.2).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f0201 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 0 2 0 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 0 2 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z1.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f1201 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 2 0 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 2 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z1.2.1).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
  have f1211 : Wm (depth 1 (j + 3)) (G0 (F := F) (m := 3 * (j + 3) + 1) (depth 1 (j + 3))) 1 2 1 1 =
      Wcf1 ((j + 3 : ℕ) : F) ((-1) ^ (j + 3)) 1 2 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((z1.2.2).trans (by simp [Wcf1] <;> push_cast <;> field_simp <;> ring))
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

theorem Wm_eq2 (k : ℕ) (hk : 2 ≤ k) :
    ∀ c d : Fin 3, c ≠ d → ∀ (ρ : Fin 2) (i : Fin 3), (ρ : ℕ) < gF 2 c → (i : ℕ) + 1 < PF 2 d →
      Wm (depth 2 k) (G0 (F := F) (m := 3 * k + 2) (depth 2 k)) c d ρ i =
        Wcf2 (k : F) ((-1) ^ k) c d ρ i := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have xk := win2_xk (F := F) (j + 2)
  have xk1 := win2_xk1 (F := F) (j + 1)
  have yk := win2_yk (F := F) (j + 2)
  have yk1 := win2_yk1 (F := F) (j + 1)
  have zk1 := win2_zk1 (F := F) (j + 1)
  have f1000 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 1 0 0 0 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 1 0 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((xk.1).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f2000 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 2 0 0 0 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 2 0 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((xk.2.1).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f2010 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 2 0 1 0 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 2 0 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((xk.2.2).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f1001 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 1 0 0 1 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 1 0 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((xk1.1).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f2001 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 2 0 0 1 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 2 0 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((xk1.2.1).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f2011 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 2 0 1 1 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 2 0 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((xk1.2.2).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f0100 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 0 1 0 0 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 0 1 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((yk.1).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f2100 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 2 1 0 0 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 2 1 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((yk.2.1).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f2110 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 2 1 1 0 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 2 1 1 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((yk.2.2).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f0101 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 0 1 0 1 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 0 1 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((yk1.1).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f2101 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 2 1 0 1 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 2 1 0 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((yk1.2.1).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f2111 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 2 1 1 1 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 2 1 1 1 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((yk1.2.2).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f0200 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 0 2 0 0 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 0 2 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((zk1.1).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
  have f1200 : Wm (depth 2 (j + 2)) (G0 (F := F) (m := 3 * (j + 2) + 2) (depth 2 (j + 2))) 1 2 0 0 =
      Wcf2 ((j + 2 : ℕ) : F) ((-1) ^ (j + 2)) 1 2 0 0 :=
    (ent_idx _ (by simp [depth]) (by simp [offK, depth]; try omega)).trans
      ((zk1.2).trans (by simp [Wcf2] <;> push_cast <;> field_simp <;> ring))
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
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact f1000
  · exact f1001
  · exact absurd hi (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact absurd rfl hcd
  · exact f1200
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact absurd hρ (by decide)
  · exact f2000
  · exact f2001
  · exact absurd hi (by decide)
  · exact f2010
  · exact f2011
  · exact absurd hi (by decide)
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

end Z3NetKN.NetKN

module
public import Z3Net.KNNetReal

@[expose] public section

/-!
# The window gauge and the `k`-independent canonical form (KN entry, `KN1_net` / `KN2_net`)

Window data are `W c d : Matrix (Fin 2) (Fin 3) F` (geometric rows of `c` on the window columns of
`d`, window index `i = 0` the last level).  The gauge `(L, U, μ)` acts by
`W c d ↦ μ c d • (L c * W c d * U d)` (`act`).

`Wcf1`, `Wcf2` are the closed forms (in `a = k`, `S = (-1)^k`) of the windows of the frame, and the
explicit gauges `h1`, `h2` (polynomial in `a`, unit diagonals) move them to the constant windows
`Can1`, `Can2` (`act_h1`, `act_h2`; `S = ±1`).  This replaces the invariants of `lem:ppinv`: the
frame windows for every `k` lie in the gauge orbit of one constant window, so a design is reachable
for every `k` once it is reachable from `Can` (a finite check per design).
-/

namespace Z3NetKN.Gauge

open Matrix

section Ring

variable {F : Type*} [CommRing F]

/-- The gauge action on window data. -/
def act (L : Fin 3 → Matrix (Fin 2) (Fin 2) F) (U : Fin 3 → Matrix (Fin 3) (Fin 3) F)
    (μ : Fin 3 → Fin 3 → F) (W : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F) :
    Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F :=
  fun c d => μ c d • (L c * W c d * U d)

def Can2 : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F :=
  ![![0, !![1, -1, 0; 0, 0, 0], !![1, 0, 0; 0, 0, 0]],
    ![!![1, -1, 0; 0, 0, 0], 0, !![-1, 0, 0; 0, 0, 0]],
    ![!![1, 0, 0; 1, 1, 0], !![1, 0, 0; 0, -1, 0], 0]]

def Can1 : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F :=
  ![![0, !![1, 0, 0; 0, 0, 0], !![1, 0, 0; 0, 0, 0]],
    ![!![1, 0, 0; 0, 1, -1], 0, !![-1, 1, 0; -1, 2, 0]],
    ![!![1, 1, 0; 0, 1, 1], !![1, 1, 0; -1, -2, 0], 0]]

end Ring

variable {F : Type*} [Field F]

/-! ## `m = 3k + 2` -/

def Wcf2 (a S : F) : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F :=
  ![![0, !![S, a * S, 0; 0, 0, 0], !![1, 0, 0; 0, 0, 0]],
    ![!![S, a * S, 0; 0, 0, 0], 0, !![-S, 0, 0; 0, 0, 0]],
    ![!![1, a + 1, 0; a + 1, a ^ 2 + 2 * a + 2, 0],
      !![S, (a + 1) * S, 0; a * S, (a ^ 2 + a - 1) * S, 0], 0]]

def hL2 (a : F) : Fin 3 → Matrix (Fin 2) (Fin 2) F := ![1, 1, !![1, 0; -a, 1]]
def hU2 (a : F) : Fin 3 → Matrix (Fin 3) (Fin 3) F :=
  ![!![1, -(a + 1), 0; 0, 1, 0; 0, 0, 1], !![1, -(a + 1), 0; 0, 1, 0; 0, 0, 1], 1]
def hμ2 (S : F) : Fin 3 → Fin 3 → F := ![![1, S, 1], ![S, 1, S], ![1, S, 1]]

theorem act_h2 (a S : F) (hS : S = 1 ∨ S = -1) (c d : Fin 3) (hcd : c ≠ d) :
    act (hL2 a) (hU2 a) (hμ2 S) (Wcf2 a S) c d = Can2 c d := by
  rcases hS with rfl | rfl <;>
  fin_cases c <;> fin_cases d <;> (first | exact absurd rfl hcd | skip) <;>
  ext ρ i <;> fin_cases ρ <;> fin_cases i <;>
  simp [act, Wcf2, Can2, hL2, hU2, hμ2, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-! ## `m = 3k + 1` -/

def Wcf1 (a S : F) : Fin 3 → Fin 3 → Matrix (Fin 2) (Fin 3) F :=
  ![![0, !![S, a * S, 0; 0, 0, 0], !![1, -a, 0; 0, 0, 0]],
    ![!![S, a * S, S * (a * (a + 1) / 2);
        -(a * S), -((a ^ 2 - 1) * S), -(S * (a * (a - 1) * (a + 2) / 2))], 0,
      !![-S, (a + 1) * S, 0; (a - 1) * S, (2 - a ^ 2) * S, 0]],
    ![!![1, a + 1, (a + 1) * (a + 2) / 2; a, a ^ 2 + a + 1, (a + 2) * (a ^ 2 + a + 2) / 2],
      !![S, (a + 1) * S, 0; (a - 1) * S, (a ^ 2 - 2) * S, 0], 0]]

def hL1 (a : F) : Fin 3 → Matrix (Fin 2) (Fin 2) F := ![1, !![1, 0; a, 1], !![1, 0; -a, 1]]
def hU1 (a : F) : Fin 3 → Matrix (Fin 3) (Fin 3) F :=
  ![!![1, -a, a * (a + 1) / 2; 0, 1, -(a + 1); 0, 0, 1], !![1, -a, 0; 0, 1, 0; 0, 0, 1],
    !![1, a, 0; 0, 1, 0; 0, 0, 1]]
def hμ1 (S : F) : Fin 3 → Fin 3 → F := ![![1, S, 1], ![S, 1, S], ![1, S, 1]]

theorem act_h1 (a S : F) (h2 : (2 : F) ≠ 0) (hS : S = 1 ∨ S = -1) (c d : Fin 3) (hcd : c ≠ d) :
    act (hL1 a) (hU1 a) (hμ1 S) (Wcf1 a S) c d = Can1 c d := by
  rcases hS with rfl | rfl <;>
  fin_cases c <;> fin_cases d <;> (first | exact absurd rfl hcd | skip) <;>
  ext ρ i <;> fin_cases ρ <;> fin_cases i <;>
  simp [act, Wcf1, Can1, hL1, hU1, hμ1, Matrix.mul_apply, Fin.sum_univ_succ] <;>
  field_simp <;> ring

end Z3NetKN.Gauge

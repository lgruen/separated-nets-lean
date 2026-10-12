/-
Paper: L. Gruenschloss, "Low-discrepancy quasi-uniform digital nets in every dimension"
(version 1; LaTeX source `paper/core.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/module
public import Z3Net.B23Fam
public import Z3Net.B23Data
public import Z3Net.B23Check2

@[expose] public section

/-!
# V14 stage S14′: the certificate checks of `thm:base23` (Boolean, for kernel `decide`)

* `netChk b r`: the seed is a `(0,M₀,3)`-net (`chkNet`), and every lift of the chain is admissible (`admPair` with
  the functionals `b23Lam`).
* `c1Chk b r`: at the certificate level `L`: the top `L/2` digits satisfy `Δ_z = G_x Δ_x + G_y Δ_y` on every
  generator, and `chk1` certifies `v°_L ≥ b23V b r`.
* `c2Chk b r k`: at the chain level `k < b23NL b r`: `Δ_c = M^x_c t_x + M^y_c t_y + M^z_c z` on every generator (box
  digits `(t_x, t_y, z)`), and `chk2` certifies the every-shift distance `≥ U`.
* `witChk b m`: the witness is a net (`chkNet`) with every-shift distance `≥ b23WitU b m` (`chkDist`).
-/

namespace Z3NetB23

/-- Digitwise difference `x − y`. -/
def dsub (b n x y : ℕ) : ℕ := dadd b n x (smul b n (b - 1) y)

/-- All codes of a list of column lists are below `b^n`, with the given lengths. -/
def colsOK (b n k : ℕ) (cols : List (List ℕ)) : Bool :=
  cols.length == 3 && cols.all (fun cs => cs.length == k && cs.all (fun x => decide (x < b ^ n)))

/-- Admissibility of one lift (level `M`, columns `cols`, shift codes `sA`, `sB`, functionals `lam`). -/
def liftChk (b M : ℕ) (cols : List (List ℕ)) (sA sB : List ℕ) (lam : List (List ℕ)) : Bool :=
  lam.length == M && sA.length == 3 && sB.length == 3 &&
  (sA ++ sB).all (fun x => decide (x < b ^ M)) &&
  (List.range M).all (fun e0 =>
    let l := lam.getD e0 []
    admPair b M (e0 + 1) (cols.getD 1 []) (cols.getD 2 []) (l.getD 0 0) (l.getD 1 0) (sA.getD 1 0) (sA.getD 2 0) &&
    admPair b M (e0 + 1) (cols.getD 0 []) (cols.getD 1 []) (l.getD 2 0) (l.getD 3 0) (sB.getD 0 0) (sB.getD 1 0) &&
    admPair b M (e0 + 1) (cols.getD 0 []) (cols.getD 2 []) (l.getD 4 0) (l.getD 5 0)
      (dsub b M (sB.getD 0 0) (sA.getD 0 0)) (dsub b M (sB.getD 2 0) (sA.getD 2 0)))

/-- The seed is a net, every lift of the chain is admissible. -/
def netChk (b r : ℕ) : Bool :=
  colsOK b (b23SeedM b r) (b23SeedM b r) (b23Cols b r 0) && chkNet b (b23SeedM b r) (b23Cols b r 0) &&
  (List.range (b23NL b r)).all (fun k =>
    liftChk b (b23Lev b r k) (b23Cols b r k) ((b23Lifts b r).getD k ([], [])).1 ((b23Lifts b r).getD k ([], [])).2
      ((b23Lam b r).getD k []))

/-- The certificate `v°_L ≥ v` at the certificate level. -/
def c1Chk (b r : ℕ) : Bool :=
  let L := b23Lev b r (b23NL b r)
  let H := L / 2
  let cols := b23Cols b r (b23NL b r)
  colsOK b L L cols && (b23Gx b r).length == H && (b23Gy b r).length == H &&
  (b23Gx b r ++ b23Gy b r).all (fun x => decide (x < b ^ H)) &&
  (List.range L).all (fun i =>
    (cols.getD 2 []).getD i 0 / b ^ (L - H) ==
      dadd b H (matvec b H H (b23Gx b r) ((cols.getD 0 []).getD i 0 / b ^ (L - H)))
        (matvec b H H (b23Gy b r) ((cols.getD 1 []).getD i 0 / b ^ (L - H)))) &&
  chk1 b H (b23R b r) (b23V b r) (b23Gx b r) (b23Gy b r)

/-- The exact every-shift distance at the chain level `k`. -/
def c2Chk (b r k : ℕ) : Bool :=
  let m := b23Lev b r k
  let cols := b23Cols b r k
  let d := (b23Mid b r).getD k (0, 0, [], [], [])
  let Hp := d.1
  let Mx := d.2.2.1
  let My := d.2.2.2.1
  let Mz := d.2.2.2.2
  colsOK b m m cols && colsOK b m Hp Mx && colsOK b m Hp My && colsOK b m (m - 2 * Hp) Mz &&
  decide (2 * Hp ≤ m) &&
  (List.range m).all (fun i =>
    (List.range 3).all (fun c =>
      (cols.getD c []).getD i 0 ==
        dadd b m (dadd b m (matvec b m Hp (Mx.getD c []) ((cols.getD 0 []).getD i 0 / b ^ (m - Hp)))
          (matvec b m Hp (My.getD c []) ((cols.getD 1 []).getD i 0 / b ^ (m - Hp))))
          (matvec b m (m - 2 * Hp) (Mz.getD c []) ((cols.getD 2 []).getD i 0 / b ^ (2 * Hp))))) &&
  chk2 b m Hp d.2.1 Mx My Mz

/-- A witness: net and every-shift distance. -/
def witChk (b m : ℕ) (cols : List (List ℕ)) (U : ℕ) : Bool :=
  colsOK b m m cols && chkNet b m cols && chkDist b m U cols

end Z3NetB23

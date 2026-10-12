module
public import Mathlib
public import Z3Net.KNDefs

@[expose] public section

/-!
# The finite first-digit relaxation for the `m ≢ 0 (mod 3)` nets (KN2 / KNOBS)

This file is a kernel-evaluable transcription of the C++ certificate `kn2_cert.cpp` (research repository)
(independently re-implemented in `knaudit_cert.cpp` / `kn2audit_cert.cpp`), in exact integer
arithmetic.

Units.  A *fine cell* has side `p^(-F)`, `F = k + 1` (`m = 3k+1` or `3k+2`); a *sub-fine unit* is
`1/p` of a fine cell.  A *full* coordinate (coarse depth `F`) sits at `p·n + ρ + f` sub-fine units
(`n` coarse integer, `ρ` the jitter digit, `f ∈ [0,1)` the deeper digits); a *skeleton* coordinate
(coarse depth `F - 1`) sits at `p·(p·n + S) + ρ + f` (`S` the skeleton digit).

A configuration is a coarse step `dl ∈ ∏_c [-R_c, R_c] \ {0}` together with carry-chain lengths
`ch_c ∈ [0, L_c)` (`ch_c = 0` if `dl_c = 0`): the last level of coordinate `d` changes by `dl_d`,
the next `ch_d` levels by `sgn dl_d` (mod `p`).  The skeleton / jitter digit of `c` changes by
`ds_c = ∑_d ∑_i sk[c][d][i]·Δ_{d,i} mod p` resp. `dj_c` (rows supported on the last `L_d` levels,
`i = 0` the last level).  `term c` is the least possible `|Δ coordinate c|` in sub-fine units over
the wrap options `S' - S ∈ {ds, ds - p}`, `ρ' - ρ ∈ {dj, dj - p}`, minus the slack `1` for the
deeper digits (slack `0` when only `c`'s own coarse digits move: deeper own rows are zero).
-/

namespace Z3NetKN.Relax

/-- Relaxation data: the prime `p`, the residue `r` (`m = 3k + r`; coordinates `c < r` are
*full*, the others *skeleton* coordinates; row windows `win r d`), the step ranges `R`, and the
designed rows. -/
structure Design where
  p : ℕ
  r : ℕ
  R : Fin 3 → ℕ
  rows : Rows

/-- Full coordinates (coarse depth `k + 1`). -/
def Design.full (D : Design) (c : Fin 3) : Bool := decide ((c : ℕ) < D.r)

/-- Row windows. -/
def Design.L (D : Design) (c : Fin 3) : ℕ := win D.r c

/-- `±1` sign of a step (only used for `dl ≠ 0`). -/
def sgn (d : ℤ) : ℤ := if 0 < d then 1 else -1

/-- Change of a one-block linear form under a step `dl` with carry chain of length `ch`. -/
def lin1 (row : Fin 4 → ℤ) (dl : ℤ) (ch : ℕ) : ℤ :=
  row 0 * dl + sgn dl * ((if 1 ≤ ch then row 1 else 0) + (if 2 ≤ ch then row 2 else 0)
    + (if 3 ≤ ch then row 3 else 0))

/-- Change of a three-block linear form (before reduction mod `p`). -/
def linC (rows : Fin 3 → Fin 4 → ℤ) (dl : Fin 3 → ℤ) (ch : Fin 3 → ℕ) : ℤ :=
  lin1 (rows 0) (dl 0) (ch 0) + lin1 (rows 1) (dl 1) (ch 1) + lin1 (rows 2) (dl 2) (ch 2)

/-- Only `c`'s own coarse digits move. -/
def isOwn (dl : Fin 3 → ℤ) (c : Fin 3) : Bool :=
  (c = 0 || dl 0 == 0) && (c = 1 || dl 1 == 0) && (c = 2 || dl 2 == 0)

/-- `max(0, |x| - sl)`. -/
def tv (x sl : ℤ) : ℕ := (|x| - sl).toNat

/-- Least `max(0, |b + j| - sl)` over `j ∈ {dj, dj - p}` (only `0` if `dj = 0`). -/
def tvJ (p b dj sl : ℤ) : ℕ := if dj = 0 then tv b sl else min (tv (b + dj) sl) (tv (b + dj - p) sl)

/-- The relaxed distance contribution of coordinate `c` (sub-fine units). -/
def term (D : Design) (dl : Fin 3 → ℤ) (ch : Fin 3 → ℕ) (c : Fin 3) : ℕ :=
  let p : ℤ := D.p
  let ds := linC (D.rows.sk c) dl ch % p
  let dj := linC (D.rows.jt c) dl ch % p
  let sl : ℤ := if isOwn dl c then 0 else 1
  if D.full c then tvJ p (p * dl c) dj sl
  else if ds = 0 then tvJ p (p * (p * dl c)) dj sl
  else min (tvJ p (p * (p * dl c + ds)) dj sl) (tvJ p (p * (p * dl c + ds - p)) dj sl)

/-- Relaxed squared distance of a configuration (sub-fine units squared). -/
def total (D : Design) (dl : Fin 3 → ℤ) (ch : Fin 3 → ℕ) : ℕ :=
  term D dl ch 0 ^ 2 + term D dl ch 1 ^ 2 + term D dl ch 2 ^ 2

/-- Integers in `[-R, R]`. -/
def steps (R : ℕ) : List ℤ := (List.range (2 * R + 1)).map fun i => (i : ℤ) - R

/-- Carry-chain lengths for a step. -/
def chains (L : ℕ) (d : ℤ) : List ℕ := if d = 0 then [0] else List.range L

/-- All configurations satisfy `T ≤ total`. -/
def checkAll (D : Design) (T : ℕ) : Bool :=
  (steps (D.R 0)).all fun d0 => (steps (D.R 1)).all fun d1 => (steps (D.R 2)).all fun d2 =>
    (d0 == 0 && d1 == 0 && d2 == 0) ||
    ((chains (D.L 0) d0).all fun c0 => (chains (D.L 1) d1).all fun c1 =>
      (chains (D.L 2) d2).all fun c2 => decide (T ≤ total D ![d0, d1, d2] ![c0, c1, c2]))

/-- Some configuration has `total = T` (so `T` is the exact relaxation value). -/
def attains (D : Design) (T : ℕ) : Bool :=
  (steps (D.R 0)).any fun d0 => (steps (D.R 1)).any fun d1 => (steps (D.R 2)).any fun d2 =>
    !(d0 == 0 && d1 == 0 && d2 == 0) &&
    ((chains (D.L 0) d0).any fun c0 => (chains (D.L 1) d1).any fun c1 =>
      (chains (D.L 2) d2).any fun c2 => decide (total D ![d0, d1, d2] ![c0, c1, c2] = T))

/-- Side conditions used by the reduction: steps below `p` (analytic carry chains), windows
`≤ 4`, and the range cover `T ≤ (p R_c)²` for full coordinates (steps beyond `R_c` are far), `R_c = 1` and `T ≤ p⁴` for
skeleton coordinates (skeleton steps `|δ| ≥ 2` move the coordinate by more than `p` fine cells). -/
def sideOK (D : Design) (T : ℕ) : Bool :=
  (List.finRange 3).all fun c =>
    decide (D.R c < D.p) && decide (1 ≤ D.L c) && decide (D.L c ≤ 4) &&
    (!D.full c || decide (T ≤ (D.p * D.R c) ^ 2)) &&
    (D.full c || (decide (D.R c = 1) && decide (T ≤ (D.p * D.p) ^ 2)))

end Z3NetKN.Relax

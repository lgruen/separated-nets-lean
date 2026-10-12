# Coverage: what is not formalized

The paper (`paper/core.tex`, version 1) proves every result in the text; `app:formal` lists the formalization status.
Every theorem, proposition, lemma and corollary, every definition except `def:geom` (which only introduces names), and the
proved statements of the remarks listed in `tab:lean` are formalized (616 compared theorems; `STATEMENTS_INDEX.md`),
with the following exceptions.

## Classical theorems used as explicit hypotheses

These theorems are not in the Mathlib version used here; the formal statements take them as hypotheses.

- `rem:Us` (the design `U_s`): the constant 1 in `log a_s = (1 + o(1)) s²` is proved from the prime number theorem
  `ψ(x) ~ x`, hypothesis `PNTpsi` (`Z3NetU.U_growth_pnt`, `U_bound_growth_pnt`); everything else, including
  `(s−1)ψ(s−2) ≤ log a_s ≤ (s−1)ψ(s−2) + s log 2` for `s ≥ 6`, is unconditional.
- `prop:cube`: parts (i)–(iii) with Hajós's theorem (`HajosProp`) and Keller's property for `s ≤ 7` (`KellerProp`) as
  hypotheses; part (iv) unconditionally, except that its strict inequalities for `s = 2, 3` use the optimal packing
  bounds (Thue, Hales) as hypotheses.

Statements of the text that are consequences of cited theorems and are neither formalized nor used as hypotheses:
Niederreiter's discrepancy bound (`rem:lowdisc`); the optimality of the range of `q` (after `thm:A`, `lem:Ts`); the bound
`s ≤ 3` in base two (`rem:base2`); `lcm(1, …, s−3) = e^{(1+o(1))s}` after `prop:E`; `K(F) ≥ s^{1−O(1/log log s)}` after
`thm:Lstar` (Wigert's divisor bound; the `div*` inequality of `thm:Lstar` itself is formalized).

## Finite computations checked by scripts, not in Lean

By decision, finite computations whose printed values no formalized result needs are checked by the programs in
`paper/scripts/` (driver `run_all.sh`; `app:verify`):

- `thm:base23`(1): the exact minimum distances of the shifted nets below the certificate resolution and the certificate
  `v*_L` beyond it (the formal statement of (1) beyond `L` takes the certificate as a hypothesis), and the entries
  `.4699`, `.2586` of column (2) of `tab:base23`. Parts (2) and (3), the nets, the chains, `t = 0` at every resolution
  and the certificates `v°_L` are kernel-checked;
- the values `a*_4, …, a*_10` of `tab:astar`, the base thresholds derived from them after `thm:A`, and the running time
  of the algorithm of `def:Ustar`;
- the thresholds and scans of `tab:Kdesigns` and `tab:practical`, including the bound `δN^{1/s} ≥ 0.8` of
  `prop:k1designs`(2) and the thresholds after `prop:4D2` (the deficits, finite maxima and `t = 0` completions that
  `prop:4D2` and `prop:k1designs` state are formalized);
- the values labelled *computed* in the paper, among them the lines and spectral values of `rem:projlines`, the
  resolutions at which `v°_L` vanishes (`rem:shiftparity`), the comparison of `𝒲*_p` with `𝒲_p` (`rem:wstar`) and the
  shifts of `rem:wshift` that break the lock.

## Partially formalized remark

- `rem:projlines`: the middle-digit relation of two coordinates and the row rescalings (`projlines_*`, `rowScale_*`,
  `*_sep_rowScale`) are formalized; the sentence "so every two-dimensional projection lies on parallel lines, at a dual
  frequency of length about `√(2/q)√N`" is not.

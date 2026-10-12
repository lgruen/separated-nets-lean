# scripts/ — computations and figure builders of the paper

Everything here runs from the paper directory (the one containing `core.tex`, `figs/` and `scripts/`) and needs no
file outside the deposit: Python via [uv](https://docs.astral.sh/uv/), C++ via `g++ -O3`. `truncate_bounds.py` and
`printed_data.py` also read data files of the Lean library (rev 15.1: `Z3Net/KNDefs.lean`, `Z3Net/T3S4Defs.lean`,
`Z3Net/HLDefs.lean` of the restructured library, found in `lean/` next to the paper, in `../lean` = the Lean project (repository root)
of the source repository, or via `$LEAN_DIR`; the rev-15.0 fallback to the stale copy
`../deposit_staging/separated-nets-lean/lean` is gone). Computed values are used in no proof; the computer-assisted certificates
(Appendix `app:verify`) are rerun here.

    bash scripts/run_all.sh          # builds the C++, reruns everything, compares the figures; ~5 min

`run_all.sh` exits non-zero if any asserted value differs from `core.tex` or any regenerated figure differs from
`figs/`. Figures are written to a temporary directory (`$FIGOUT`), never over `figs/`. Measured on an Apple-silicon
laptop (2026-10-12, rev 14.3): see the research notes (rev 14.1: 171 s on one core; rev 14.3 adds
`base23_certs.py`, about 40 s wall with OpenMP on 10 cores, about 4 min on one core, and `printed_data.py`, < 1 s;
rev 15.0: 299 s in total, adding `colnets.py` (50 s wall, about 3.5 min of CPU on one core), `half5_qstar.py`
(3 s), `half5_exact.py` (10 s) and `figs_col.py` (1 s); rev 15.1: 260 s, adding `wnet.py` (27 s; `--full`
43 s) and `figs_wnet.py` (1 s); rev 15.3: 341 s, adding `wfamily.py` (24 s); rev 15.4 adds `gk2d_rescramble.py` (7 s)).

Build the C++ programs (done by `run_all.sh`):

    mkdir -p scripts/bin
    g++ -O3 -std=c++17 -o scripts/bin/netmind     scripts/netmind.cpp
    g++ -O3 -std=c++17 -o scripts/bin/cellmin     scripts/cellmin.cpp
    g++ -O3 -std=c++17 -o scripts/bin/whylat_cube scripts/whylat_cube.cpp
    g++ -O3 -std=c++17 -o scripts/bin/colmind     scripts/colmind.cpp
    g++ -O3 -std=c++17 -pthread -o scripts/bin/half5_mind scripts/half5_mind.cpp
    g++ -O3 -std=c++17 -o scripts/bin/half5_thmD  scripts/half5_thmD.cpp
    g++ -O3 -std=c++17 -o scripts/bin/shiftmin    scripts/shiftmin.cpp
    g++ -O3 -std=c++17 -o scripts/bin/gk2d_rescr  scripts/gk2d_rescr.cpp

`PY` below stands for `uv run --with numpy --with matplotlib --with mpmath --with python-flint python` (each script
needs only a subset; python-flint only for `ustar_det.py`, i.e. `as_table.py` and `deficit_tables.py`).

## Computations

Most scripts read the printed values from `core.tex` at run time (tables by their `\label`, other values by a quoted
snippet); a value or snippet that is no longer in the paper makes the script fail.

| script | reproduces | time | command |
|---|---|---|---|
| `gk09_decay.py` | Introduction and `app:verify`: δN^{1/3} of the base-2 (0,m,3)-net of [GK09], m = 3..13 (built two ways, net property, exact toroidal minimum) | 1 s | `PY scripts/gk09_decay.py` |
| `gk2d_affine.py` | Remark `rem:gk2d`: the 2D nets are (0,m,2)-nets, m = 4, 6, 8, 10 (the script also checks that they are not digitally shifted digital nets, which the paper no longer states) | < 1 s | `PY scripts/gk2d_affine.py` |
| `gk2d_rescramble.py` (+ `gk2d_rescr.cpp`) | rev 15.4, Remark `rem:gk2d`(iii): on GK's lines the phase maps keeping t = 0 are exactly the 2^(R−1) nested scramblings of the van der Corput phases (DFS with box counts, m = 4, 6, 8), all with the same distance 1/4 − 1/(2R) from lattice phases; the re-scramble (third phase digit flipped on the lines u ≡ 2, 3 mod 4) is nested, has t = 0 and exact d² = 977·2^(m−10) in the tiling metric for m = 10..20 and on the standard torus for m = 12..20 (229 < 241 at m = 8, tiling); GK09's 241·2^(m−8) (tiling) as a cross-check; the printed sentences and decimals | 7 s | `PY scripts/gk2d_rescramble.py` |
| `cubecost.py` (+ `whylat_cube.cpp`, `whylat_check.py`) | Remark `rem:cubecost`: all lattices of covolume 1 in (1/e)Z³, e ≤ 11 (counts = sublattice numbers); largest one-per-cube minimum √(29/25) = 1.0770…, at e = 10; maximizers not affine | 25 s | `PY scripts/cubecost.py` |
| `tab_c.py` (+ `netdefs.py`, `netmind.cpp`) | Table `tab:c`: exact minima of P_{2,q} (q = 4..13, 16), m = 6, by a certified neighbour-cell scan of all N points of nets rebuilt from Definition `def:net`; the row c(q) of Theorem `thm:main` (until rev 14.0 this was `tab_c_two.py`, which also checked the former Table `tab:two`) | 2 s | `PY scripts/tab_c.py` |
| `as_table.py` (+ `ustar_det.py`) | Table `tab:astar`: a\*_s and the largest entry of U\*_s for s = 3..10, computed by `ustar_det.py` from Definition `def:Ustar` (exact; also checks the column polynomials of `prop:F` and dominance), 5a\*_s+4, the bound 2(s−1)^{3/2}(3/2)^{s−2}(s−2)! of Theorem A (truncated) and a\*_s ≤ bound, a_s of the monomial design U_s (Remark `rem:Us`); the display of U\*_3, the list of a\*_s and q = 14, 29, 84 in the Introduction, a_5 = 17407, and the rows a\*_s and floor lcm(1,…,s−3) of `tab:Kdesigns` | 1 s | `PY scripts/as_table.py` |
| `deficit_tables.py` (+ `ustar_det.py`, `designs_K.json`, `dim4_deficit2_design.json`) | Section `sec:deficit`, designs read from Appendix `app:designs`: Table `tab:Kdesigns` (K(F) by enumeration of all configurations for s = 4, 5, 6, S(F), largest \|M^{(j)}\|, Q_D of `prop:Dprime` for s = 4..8, and the thresholds "LB ≥ 1−K/q" and ".5/.8/.9" for s = 4, 5, 6 from the exact relaxation of `lem:Ss` below the tail of `prop:Dprime`); Proposition `prop:4D2` (2400 configurations, K = 2, S = 7, Q_D = 23, LB = (q−2)/q at q = 17, 19, 21, 1+102/15 < 8); Table `tab:practical` (K_1 of each level-0 layer, attained by a one-axis step, the thresholds q_0 for c ≥ .5/.8/.9 at k = 1 and N = q_0^s as printed, the s = 3 row from c(q)) and the sizes quoted in its caption and in the Introduction. Not recomputed: K(F) and the thresholds for s = 7, 8 (stated as computed values; K is taken from `designs_K.json`), the ring row, and the t = 0 completions of the free layers | 4 s, 0.9 GB | `PY scripts/deficit_tables.py` |
| `skel_table.py` | Table `tab:skel` (bounds of `thm:S1`, `thm:S2`, p₀), exact integer arithmetic | < 1 s | `PY scripts/skel_table.py` |
| `twocoset.py` (+ `cellmin.cpp`, `twocoset_exact.json`) | values after Proposition `prop:twocoset` and Figure `fig:arctwocoset`(c): exact minima of T_p (p = 101..1009, = the pair value d_*²; the paper prints p = 101 and 1009). Until rev 14.3 also E_p (former `thm:E1`; its stored values stay in the json, unused); `--quick` skips the rerun at p = 1009 (~85 s) and checks its stored value | 110 s | `PY scripts/twocoset.py` |
| `colnets.py` (+ `colmind.cpp`, `cellmin.cpp`, `colnets_exact.json`) | rev 15.0, Sections `sec:m3`, `sec:drift`: Theorem `thm:colmin` on 3600 random column point sets (q = 2..13) against an O(N²) brute force; the closed forms of `thm:col` against both kernels at the 80 q ≤ 241 coprime to 6 (28 composite); box minors and box counts; every digital shift up to isometry at q = 5, 7, 11, 13 and random shifts up to q = 41 against `prop:colshift` (lower bounds, and the upper bound with a_max); the arc claim of its proof (exhaustive, q ≤ 61); the class maximum of the digital column nets (q ≤ 151, `thm:O`); exact T_p at every prime 7..199 (p ≠ 23) and the crossover after `prop:twocoset`; exact E_p, J_p at every prime 5..199 (Figure `fig:drift`(c)). `--full` extends the ranges (152 s), `--write` regenerates the json | 50 s wall (10 cores; ~3.5 min CPU) | `PY scripts/colnets.py` |
| `half5_qstar.py` | rev 15.0, `prop:half5` (net Q*_p): the 126 box minors (primes 2, 3, 5 only; mod-p checks; control: the layer M_5 gives its exceptional set), det 2F_0^* = −880, skewness, P_4 graph, max\|2F_0^*E\| = 22, max\|D_1E\| = 24, dr = dj = 17/2 and the attaining steps, (Λ) and λ = √5/2, the exact scans of `lem:R2` (29 ≤ p < 200) and `prop:Hk`(1) (23 ≤ p < 400) with their exact monotone tails, the M_5 values of `rem:M5` | 3 s | `PY scripts/half5_qstar.py` |
| `half5_exact.py` (+ `half5_mind.cpp`, `half5_thmD.cpp`, `half5_exact.json`) | rev 15.0: exact minimum distances of Q*_p, 7 ≤ p ≤ 61 (the kernel agrees with `algs_mind2` at 7, 11, 13); the computer-assisted part of `thm:D` (1,004,544 normalized layers, none with dr ≤ 15/2; 84 minimizers) and the skew family after it (39,168 admissible, two orbits of 1920); the curves of Figure `fig:half5`; `--quick`, `--write` | 10 s | `PY scripts/half5_exact.py` |
| `wnet.py` (+ `cellmin.cpp`, `shiftmin.cpp`, `w_exact.json`, `colnets_exact.json`) | rev 15.1, Section `sec:wnet`: t = 0 of W_p (all 10 box determinants, every prime 5 ≤ p ≤ 3000) and the printed minors; Lemma `lem:wwrap` by enumeration of all cells (p ≤ 23; `--full` ≤ 31); the rules (M, κ) of the proof of `prop:wnet`(2) against the lemma at every prime 53..1500 (`--full` 5000); Table `tab:wcontacts` parsed and checked row by row (A, steps, (M, κ), Q, the quadratic, its value and slope at 1/48; the printed steps cover every short option up to symmetry; the bound for \|A\|² ≥ 3; the monotone check at p = 53); the tangent-line step of the proof (rev 15.3; Table `tab:wclasses` was removed); independently, the full quadratic of every option in every one of the 24 classes of p mod 48 on 1/p ∈ (0, 1/53]; the relaxation at every prime 53..3000 (`--full` 20000); the pair of (3) against generated points (53..2000); the constants of (2) and (4); exact c(W_p) at every prime 5..199 and at 307, 353 (`cellmin.cpp`, compared with `w_exact.json`; `--write` regenerates it); W_p ahead of T_p; the net T15 at p = 307 (t = 0, c = 1.0160); the digital shifts of W_101 (`shiftmin.cpp`; rev 15.3: a ≡ 2b+1 keeps the lock, every (c,c,0) with 2 ≤ c ≤ 100 breaks it); the limit-model values 33/32, 281/256, 233/225; the printed values | 27 s | `PY scripts/wnet.py` |
| `wfamily.py` (+ `cellmin.cpp`, `wstar_exact.json`, `wnet.py`) | rev 15.3, `prop:wfamily` and `rem:wstar`: the constants ε\*, μ\*² = (72 − 8√31)/25, K = (9√31 − 36)/5 and every numerical fact of the six-contact proof and of part (2), in exact arithmetic in Q(√31); F(τ\*) = μ\*² from all options (8 ties: rows (a), (b) and images); F_p(u) = F(u/p) against a brute force over the points without third digits (all u at p = 5, 7, 11, sampled at 13, 17); max_u F_p(u) < μ\*² over all u at every prime 5..61; part (2) at the nets (all odd ρ, primes 53..400, and W\*_p to 3000); W\*_p: t = 0, \|ε_p − ε\*\| < 1/(2p), F_p > μ\*² − K/p exactly (53..3000); W\*_p = W_p for p < 193 and p ≤ 47; the differing primes ≤ 1009 and p > 8548; the thresholds 67, 97, 9791, 17737; exact c of W_p and W\*_p at the 8 differing primes ≤ 1009 (`cellmin.cpp` at 193, 241, 337; `wstar_exact.json`, cross-checked against `../../wnet_gap_audit/amind.csv` and `../../wnet_gap/out/mind.csv`); the wrap pairs of the digit 2ζ+1 (`rem:shiftshared`); the printed values | 24 s | `PY scripts/wfamily.py` |
| `truncate_bounds.py` (+ `s1e_certs.py`, `codesaudit_e1.py`, `e1_*.txt`, `twocoset_exact.json`, `llg_s5_design.json`) | `app:verify`, last sentence: every printed closed-form bound recomputed in exact arithmetic and checked against the convention of Section `sec:conv` (lower bounds, exact and computed values truncated, upper bounds rounded up; since rev 15.2 a rounded exact value is a failure); also `figs/arc_captions.tex` (values read at run time). Rev 14.1 adds B_4, B_5 of `thm:HL`, the s = 5 half-integer scan behind "p ≥ 89" (`sec:halfms`; since rev 14.3 the proof of `prop:half5`, with LB'(89), LB'(83), 265.2…), c(q) = 1−1/q for q ≥ 8, Q_D < 5a+4, the ℓ∞ mesh ratio < 10/3, and the constants of `thm:base23` against `tab:base23` | 5 s | `PY scripts/truncate_bounds.py` |

| `printed_data.py` | rev 14.3: every data block printed in this revision against its source, entry by entry (rev 15.1: also the rows of W_p of `prop:wnet` against `../twocoset_ext/layers.py` and `../rev15_audit/nets.py` if present, the counterexample in the proof of `lem:drift`(2), the constant of `prop:4D2`(3); Lean data from `Z3Net/*.lean`): the 11 per-prime designs of `tab:ppdesigns` (Lean `Z3Net/KNDefs.lean`), the κ of `tab:S1Ekappa` (`e1_*.txt`), the seeds of `tab:b23seeds` (point files `../witnesses/r1/*_seed_m*.txt`; t = 0 by box ranks), the basis of `rem:cubecost` (same lattice as the e = 10 maximizer, covolume, Gram matrix, Minkowski reduction, minimum 29/25), `prop:korobov4` (Lean `t3d13` and `t3_s4.json`; reachability conditions mod 13, λ∞(κ) = 5, M_13 = 4 by the relaxation of the proof), `prop:half5` (Lean `M5h`, `D5tab`; λ(M_5) = √5/2 over 5^5−1 vectors, A = 13/2, the 126 box minors and their primes), and the identity and estimates in the proof of `prop:twocoset` | < 1 s | `PY scripts/printed_data.py` |
| `base23_certs.py` (+ `../base23_audit/ba.cpp`, `ba_dump.cpp`, `ba_cert.py`, `witness_smallm/`; `../base23_everyshift/es.cpp`, `es_cert.py`, `witness_smallm_es/`; `../witnesses/r1/`) | Theorem `thm:base23`, Table `tab:base23`: builds the audited checker of the research notes, replays the six chains, t = 0 at every level (shifted and unshifted), exact v\*_L and minima with the proviso (`ba_cert.py`), the small-m witnesses (rev 15.7: for b = 2, m = 6, 7 the every-shift replacement witnesses of the research notes); part (3) (rev 15.7): builds `es` (the research notes) and reruns its exact every-shift certifier `es_cert.py` (v°_L, exact every-shift minima, freezing) on the same chains, and checks every-shift c of every small-m witness; asserts every entry of `tab:base23` (three constant columns) and the constants of the theorem | 45 s (OpenMP, 10 cores; part (3) adds a few s); ~4 min on one core | `PY scripts/base23_certs.py` |

## Figures

Each builder asserts the properties stated in its captions (91 checks in `figs_arc.py`, 35 in `figs_part1.py`).
Default output is `figs/`; `--out DIR` writes elsewhere.

| script | figures | time | command |
|---|---|---|---|
| `figs_arc.py` (+ `netdefs.py`, `knallp_audit_build.py`, `dim4_build.py`, `dim4_frame.py`, `llg_lib.py`, `llg_dump.py`, `dim4_deficit2_design.json`, `llg_s5_design.json`, `twocoset_exact.json`) | `fig:arc`, `fig:arcgk`, `fig:arcwhylat`, `fig:arcsmall`, `fig:arcskeleton`, `fig:arclarge`, `fig:arctwocoset`, `fig:arcsplit`, and the caption macros `figs/arc_captions.tex` | 7 s | `PY scripts/figs_arc.py --out DIR` |
| `figs_part1.py` (+ `part1_b3r0_m6.net`, `part1_b3r0_m9.net`) | `fig:thmA` (`thmA_design`), `fig:base23` (`base23_lift`), `fig:projlines` (`projlines`), and the caption macros `figs/part1_captions.tex` | 2 s | `PY scripts/figs_part1.py --out DIR` |
| `figs_col.py` (+ `colnets_exact.json`, `half5_exact.json`) | rev 15.0: `fig:col` (`col_net`: C_5 in 3D with its columns and closest pair, checked against all pairs; C_11 along (1,1,1), deviation from the reflected cube), `fig:drift` (`col_drift`: the holonomy along the cycles of C_11, C_13; the deficits of C_p, J_p, E_p), `fig:half5` (`col_half5`), and `figs/col_captions.tex` (41 checks) | 1 s | `PY scripts/figs_col.py --out DIR` |
| `figs_wnet.py` (+ `w_exact.json`, `colnets_exact.json`; needs `bin/shiftmin`) | rev 15.1: `fig:wnet` (`w_net`: T_101 with the free coordinate x, W_101 with the locked coordinate z and the locked wraps, the same net with the second digit of z shifted (lone wraps of z, folds), δN^{1/3} of W_p against p) and `figs/w_captions.tex` (73 checks; rev 15.3: the dotted line μ*) | 1 s | `PY scripts/figs_wnet.py --out DIR` |
| `figs_net.py` (+ `netdefs.py`) | `fig:slab` (`fig_slab`; nets P_{k,q} from Definition `def:net`); it also writes `fig_full`, `fig_axis`, which are no longer in the paper and are not compared | 2 s | `PY scripts/figs_net.py --out DIR` |
| `figcmp.py` | compares DIR with `figs/` for every PDF that `core.tex` includes (`\includegraphics{figs/…}`, `\arcfig{…}`): identical bytes, or identical pixels after rasterizing with `pdftoppm` (150 dpi); `arc_captions.tex`, `part1_captions.tex`, `col_captions.tex` and `w_captions.tex` must be identical | 3 s | `PY scripts/figcmp.py DIR` |

The committed PDFs were written with matplotlib 3.11.0 (`arc_twocoset`, `arc_whylat`: 3.11.2); with that version
the builders reproduce them byte for byte, except `fig_slab`, which was written with an embedded creation date and is
therefore compared by pixels; other matplotlib versions give the same pixels.

`figs_eis.py` builds the Eisenstein figures of earlier revisions (`eis_fig_*`), which are no longer in the paper; it is
not run by `run_all.sh`.

## Data files

`twocoset_exact.json` (precomputed output of `cellmin.cpp`, rerun by `twocoset.py`), `w_exact.json` (rev 15.1: exact d² of W_p, rerun by `wnet.py`, plotted by `figs_wnet.py`), `wstar_exact.json` (rev 15.3: exact d² of W_p and W\*_p at the primes ≤ 1009 where they differ, from the audit kernel; three of them rerun by `wfamily.py`), `colnets_exact.json` (rev 15.0: exact T_p, E_p, J_p, rerun by `colnets.py`), `half5_exact.json` (rev 15.0: exact c(Q*_p) and the certificate curves, rerun by `half5_exact.py`), `designs_K.json` (the designs of
`tab:Kdesigns`, s = 4..8; s = 4..6 are also printed in `app:designs` and asserted equal), `dim4_deficit2_design.json`
(the design of `prop:4D2`), `llg_s5_design.json`, `t3_s4.json` (the dimension-four designs; `prop:korobov4` is the
one at p = 13), `e1_random_search.txt`,
`e1_rootlattice_rounding.txt`, `part1_b3r0_m6.net`, `part1_b3r0_m9.net`: designs, nets and certificates used by the
builders and the checks (the same data are fixed data of the Lean library where formalized).

Kept for the material of earlier revisions, not used by `run_all.sh` since rev 14.1: `dim4_designs.json`,
`eis_link_t0_witnesses.json`, `t2_ic2digit.py`, `t2_t3s4.py`, `codesaudit_e2cert.cpp`,
`e2_s5r2_frameorbit_designs.txt`, `figs_eis.py`; since rev 14.3 also `llg_s8_design.json` (the dimension-eight
sentence of `sec:halfms` was cut).

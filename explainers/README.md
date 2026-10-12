# explainers/ — interactive, geometry-first companions to the paper

A set of single-file HTML pages for *Low-discrepancy quasi-uniform digital nets in every dimension*
(`paper/core.tex`). Each page shows one construction of the paper with points that are **computed in
the browser** from the paper's generator matrices or graph forms, with exact integer arithmetic. No figure is
hand-drawn and no data file is shipped. Each section cites the paper by `\label` (for example `thm:main`), never by
number, so the pages survive renumbering.

## Pages

| page | status | content |
|---|---|---|
| `anatomy.html` — "How the nets are built" (`<title>` Digits, Cubes, Lattices) | done | Story order (rev 2): (1) the standard frame — the 2D Hammersley net, a box-shape slider with occupancy colouring, the box matrix of the chosen shape and its determinant (`sec:frames`, `lem:nie`, `lem:Ts`); (2) the problem — the frame's closest pair sits across a carry (both geometric digits wrap on a diagonal step; `rem:K`: no backward coordinate), exact δ√N against q for the frame (k = 1, 2) and the turned layer, computed, not a theorem; (3) the t-preserving freedom — lower-triangular scrambles, the scramble L from the frame to the turned layer per coordinate (lower triangular, deeper rows borrowed up to a sign), all box minors (`lem:box`, `eq:scr`, `prop:Gs`); (4) the fix — the turned layer M̃ = −I + quarter turn with lattice patches, slips, closest pair, box overlay and a jitter-off toggle that breaks the thin boxes; (5) the worked example "From index to point" with a plain-Python reference listing; (6) 3D: the frame of the places ∞, 0, 1, 𝒫₂,q (`thm:main`) and 𝒞_q (`thm:col`); (7) the holonomy of the column nets (`lem:drift`, `fig:drift`); (8) nets that are not frame scrambles: box minors and box counts of 𝒞_q, 𝒯_p, 𝒲_p, with and without the third digit. |
| `shifts.html` — "Digital shifts and the question of Dick, Goda and Suzuki" (`<title>` Shifted Digits) | done | (1) what a digital shift does, on the 2D net and the 3D column net, digit by digit against ordinary addition (`def:dshift`, `lem:shift`; Owen 1995 for scramble invariance); (2) why the bounds survive: 𝒫₂,q under an editable 18-digit shift and 40 random shifts against c(q), and the closest pair's digit changes, which keep their residue (`prop:shift`, `rem:ppshift`); (3) column nets under the three kinds of shift, with the wrap windows on a ring (`prop:colshift`, `rem:shiftshared`); (4) the fragile lock of 𝒲_p: every second-digit shift (t, t, t′) at p ≤ 23 as a map, any shift up to p = 101 (`rem:wshift`); (5) bases 2 and 3: the worst wrap μ(d) and the every-shift minimum of 𝒫_k,b as a code weight, with a brute force over all shifts for the two smallest nets (`lem:shiftcert`, `rem:shiftparity`). |
| `beyond.html` — "Beyond the cube" (`<title>` Beyond the Cube) | done | (1) the column ceiling: three height steps around a triangle close up, so g ≤ 1/3 (`cor:colceil`, `thm:colmin`), free steps or 𝒞_q; (2) the two escapes at m = 3: slab side views of 𝒯_p (free x) and 𝒲_p (locked z), and 𝒲_p with z shifted, steps coloured by wrap pattern (`prop:twocoset`, `prop:wnet`, `fig:wnet`), exact δN^{1/3} of both at every prime 11..101 with the proven bounds to 200; (3) the two contacts q_a, q_b of 𝒲_p and the family optimum μ* (`tab:wcontacts`, `prop:wfamily`); (4) the half-integer layer 𝒬*_p in dimension five: a plane of cells by parity, exact δN^{1/5} for p = 7, 11, 13, 17 and the certified bound LB₂(p) of `lem:R2` for the primes 29..199, crossing 1 at 37 (`prop:half5`). |
| `thmA.html` | planned | Theorem A in higher dimensions (`thm:A`, `def:Ustar`): slabs and 2D projections of 𝒫^{U*_s}_{k,q} for s = 4, 5; the projection lines of `rem:projlines` |
| `base23.html` | planned | the deep-shift lift in bases two and three (`def:lift`, `lem:liftsep`, `thm:base23`) |
| `gk2d.html` | planned | the slide arrangement of the Grünschloß–Keller (0,m,2)-nets (`rem:gk2d`; Rudolph for their being (0,m,2)-nets): lines of Λ, van der Corput phases, the re-scramble |

The material once planned for `columns.html`, `twocoset.html`, `half5.html` and `shifts.html` is covered by page 1
(sections 6–8), page 3 and page 2.

## Page conventions

- One `.html` file per page plus the shared `netcore.js`, loaded with `<script src="netcore.js"></script>` (a relative
  path, so the pages work as artifacts with `netcore.js` as a supporting file and on GitHub Pages). Each page is written without `<!doctype>/<html>/<head>/<body>` (the hosting wrapper
  adds them; for GitHub Pages, `site/build_site.sh` adds them too). External scripts only from cdnjs / jsDelivr /
  unpkg with exact versions (three.js r128 + OrbitControls 0.128.0), fonts from Google Fonts with fallback stacks.
- All math in `netcore.js`: pure functions, no DOM. The cross-checks run exactly that file. A small header links the
  three pages.
- Colors as CSS tokens with light and dark values; accent `#2b6cb0` as in the paper's figures. Works at 400 px.
- Sizes are capped so that the exact minimum distance (cell list, `NetCore.minDist`) stays interactive: N ≤ ~10⁵.
- Distances are toroidal (the paper's δ); decimals are truncated, as in the paper (`sec:conv`).

## Cross-check (run after every change to `netcore.js` or to a page)

    uv run --with numpy --with matplotlib python explainers/check/crosscheck.py     # page 1, ~22 s
    uv run --with numpy --with matplotlib python explainers/check/crosscheck23.py   # pages 2-3, ~40 s

Both run `netcore.js` under node (`/opt/homebrew/bin/node`, or `$NODE`): `check/run_core.mjs` dumps every net page 1
can show, `check/run_core23.mjs` (two halves in parallel) the nets of pages 2 and 3. The Python side compares them
with references built from the paper's definitions:

- page 1: the Hammersley frame (generators J, I), its graph form and the gauge moves of `lem:box`; 𝒫_{k,q} against
  `paper/scripts/netdefs.py`, the exact c of 𝒫₂,q against the printed `tab:c`; 𝒞_q against `figs_col.py` and the
  closed form of `thm:col`; minimum distances by an independent numpy kernel; the worked example (15,693 points) and
  the printed Python listing executed; every box minor of the 2D nets (frame and turned, with and without the deeper
  digits) as an exact integer determinant of the reference rows, the box counts on the reference points, and
  unit ⇔ one point per box (`lem:nie`) both ways; the scramble L frame → turned (lower triangular,
  L C_frame = C_turned mod q, deeper rows); the frame's wrap step; the 3D frame (T², I, T) of `netdefs.frame`, its
  ±1 box minors, 𝒫_k = L · frame; the box minors and counts of 𝒞_q, 𝒯_p, 𝒲_p with and without the third digit
  (𝒯₂₃ fails, as `prop:twocoset`(1) says); t = 0 by `explainers/check/net_tparam.py` and by box counts.
- pages 2–3: every shifted net rebuilt by adding the shift digits to the reference points (`def:dshift`), point sets,
  box counts, exact distances (numpy) and, for the m = 3 graph forms, the paper's audited kernel
  `paper/scripts/shiftmin.cpp` (compiled on the fly; the shift enters through the constants γ of `lem:shift`); the
  residues of the digit changes at the closest pair (`lem:shift`); the bounds of `thm:main` under shifts and the three
  cases of `prop:colshift`; the wrap windows; every second-digit shift of 𝒲₁₁, 𝒲₁₃ and the paper's shifts at
  p = 53, 101 (`rem:wshift`: .1355 and 1.0362); 𝒯_p and 𝒲_p at every prime 5..101 against the paper's audited data
  (`colnets_exact.json`, `w_exact.json`), numpy (p ≤ 29), `net_tparam` (p ≤ 41), the bounds and explicit pairs of
  `prop:twocoset` and `prop:wnet`; the steps along the slab axis grouped by wrap pattern; the column triangles and
  g of `thm:colmin` (q ≤ 61) and g ≤ 1/3 on a grid (`cor:colceil`); μ_n by brute force, the every-shift minima of
  𝒫_k,b (b = 2, 3) by the formula of `lem:shiftcert`(b), at the page's shift, against random shifts and, for the two
  smallest nets, against all shifts; 𝒬*_p (p = 7, 11, 13, 17) against `half5_qstar.gens_mod`, `half5_exact.json` and
  numpy, t = 0 at p = 7; LB₂(p) against `half5_qstar.lb_r2_sq` at every prime 29..199; the value of 𝒲_p without
  its third digits (`prop:wfamily`) against a brute force at p = 53, 59; the constants ε*, μ*, q_a, q_b.

Result at the time of writing (2026-10-12): page 1 1191 checks passed, pages 2–3 1792 checks passed, 0 failed.

Limits of the browser: exact minimum distances are computed for N up to about 10⁶ in 3D (p ≤ 101) and p⁵ ≤ 1.5·10⁶
in 5D (p ≤ 17); larger sizes show the paper's certified bounds, labelled as bounds. The 𝒲_p shift map is computed for
p ≤ 23. That only t ≡ 2t′ and 2t′ + 1 keep the lock of 𝒲_p is a computed observation (as in `rem:wshift`).

## On GitHub Pages

`site/build_site.sh` (repository root) assembles the website: a landing page, `paper.pdf`, `blueprint/` (the web
blueprint, built by `scripts/build_blueprint.sh`) and `explainers/` (these pages, each wrapped in
`<!doctype html><html><head><meta charset><meta name=viewport>…`, with `netcore.js` and an index). The workflow
`.github/workflows/pages.yml` runs it on GitHub; it is started by hand only. URL: <https://lgruen.github.io/separated-nets-lean/>
(the paper prints `https://lgruen.github.io/separated-nets-lean/explainers/`).

# Low-discrepancy quasi-uniform digital nets in every dimension

Manuscript, Lean 4 formalization, blueprint and interactive explainers for

> Leonhard Gruenschloss, *Low-discrepancy quasi-uniform digital nets in every dimension*, version 1 (2026).
> Hexagon: HEXAGON_ID_TBD.

Dick, Goda and Suzuki asked for low-discrepancy digital nets that are quasi-uniform, with minimum distance and covering
radius both of the optimal order N^(-1/s), and stated the problem as open in dimension s ≥ 3. The manuscript constructs
such nets in every dimension: for every s ≥ 3, every base q whose prime factors are at least s − 1 and every k ≥ 1,
explicit digital (0, sk, s)-nets over ℤ/qℤ with N = q^(sk) points (Theorem A, `thm:A`). This repository is release
**v1.0.0**, which accompanies **version 1** of the manuscript.

Archived at Zenodo: ZENODO_DOI_TBD (concept DOI, all versions). Palomar entry (Theorem A): PALOMAR_ID_TBD.
Website (blueprint and explainers): <https://lgruen.github.io/separated-nets-lean/>.

## Contents

| path | content | licence |
|---|---|---|
| repository root | the Lean 4 / Mathlib Lake project: statement library `QUNets/Statements/*.lean` (616 statements, one file per part of the paper), roots `Challenge.lean` / `Solution.lean`, Comparator configuration `comparator.json`, proofs in `Z3Net/` and `QUNetsM3/`, fidelity checks `Checks*.lean`, `KNChecks.lean`, tools in `scripts/` | MIT |
| [`Headline/`](Headline/), `comparatorHeadline.json`, [`palomar/headline/formalization.yaml`](palomar/headline/formalization.yaml) | the Palomar entry for Theorem A: a Mathlib-only statement file of 438 lines | MIT |
| [`formalization.yaml`](formalization.yaml) | metadata of the whole library (`comparator.json`) | MIT |
| [`STATEMENTS_INDEX.md`](STATEMENTS_INDEX.md), [`COVERAGE_GAPS.md`](COVERAGE_GAPS.md), [`COMPARATOR_RESULTS.md`](COMPARATOR_RESULTS.md) | theorem → paper label map; what is not formalized; the Comparator runs | MIT |
| [`blueprint/`](blueprint/) | leanblueprint sources, generated from `paper/core.tex` | MIT |
| [`paper/`](paper/) | `core.tex` (bibliography inline), `core.pdf`, `figs/`, [`scripts/`](paper/scripts/) (the programs that reproduce every computed value and figure; driver `scripts/run_all.sh`), `certificates/` (checkers and witness chains of the bases two and three) | manuscript CC BY 4.0 ([`paper/LICENSE.md`](paper/LICENSE.md)); programs and data MIT |
| [`explainers/`](explainers/) | interactive pages that compute the nets in the browser from their generator matrices, with cross-checks against the paper's scripts | MIT |
| `.github/workflows/pages.yml`, `site/` | GitHub Pages build of the blueprint and the explainers (manual trigger only) | MIT |

## Status

All 616 compared theorems are proved. The only axioms are `propext`, `Classical.choice` and `Quot.sound`; there is no
`native_decide` (finite certificates are checked by `decide` in the kernel), and `sorry` occurs only in the statement
files (`QUNets/Statements/*.lean`), one per statement, by design: the Challenge holds the statements, the Solution the
proofs. [Comparator](https://github.com/leanprover/comparator) accepts all 616 theorems of `comparator.json` with both the
Lean kernel and the independent NanoDa kernel (full run of 96 minutes), and the four theorems of the headline entry
`comparatorHeadline.json`; see [`COMPARATOR_RESULTS.md`](COMPARATOR_RESULTS.md).

Everything the paper proves is formalized, except: finite computations whose printed values no formalized result needs,
which are checked by the scripts in `paper/scripts/` (listed in the paper, `app:formal`); two classical theorems that
are not in Mathlib and enter as explicit hypotheses (the prime number theorem for the growth constant of `rem:Us`;
Hajós's theorem, Keller's property for s ≤ 7 and the optimal packing bounds for s = 2, 3 in `prop:cube`); and one
sentence of `rem:projlines` (the parallel lines). Details: [`COVERAGE_GAPS.md`](COVERAGE_GAPS.md).

The headline statement (Theorem A, `Headline/Challenge.lean`) was reviewed against the manuscript and signed off by the
author on 2026-10-12. The author accepts the other statements of the library on the basis of statement-review notes
prepared in AI-assisted review passes, which give each formal statement in words next to the printed statement, with
every divergence. No independent human peer review has been performed.

## Building

The Lean project (needs [elan](https://github.com/leanprover/elan); toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib
`v4.35.0-rc3`, both pinned):

```sh
lake exe cache get        # Mathlib build cache
lake build                # Z3Net, Challenge, Solution (all 616 statements and their proofs)
lake build Headline       # the Palomar headline entry
lake build Checks ChecksCpp Checks4D ChecksU ChecksS1 ChecksHL8   # optional fidelity checks
```

Measured on a 10-core, 32 GB laptop (2026-10-13, Mathlib from the cache): a clean `lake build` compiles about 9,400
modules; it took about an hour of wall time (with the swapping episode described next removed, an estimate:
the run was split into several pieces). A few kernel-certificate modules are heavy: `Z3Net/B23Cert*.lean` need
14–23 GB of memory each (and `Z3Net/HalfCertW8_*.lean`, `Z3Net/TDCert*.lean`, `Z3Net/KNCert*.lean` several minutes
each). Lake builds them in parallel, which can exceed the memory of a 32 GB machine; if it starts swapping, build them
one at a time first (for example `lake build Z3Net.B23CertC1A1`, then the others) and then run `lake build` again.

`lake build` prints `declaration uses 'sorry'` for the 616 statements and `#print axioms` for every compared theorem.
To run Comparator, build it with `lean4export` at the tag of the toolchain and NanoDa (on Linux also `landrun`), then
`COMPARATOR_LEAN4EXPORT=… COMPARATOR_NANODA=… lake env path/to/comparator comparator.json` (about 96 minutes and 21 GB
for the library; about a minute for `comparatorHeadline.json`); `scripts/run_comparator_full.sh` runs it with a log.

The paper and its computations (needs a TeX distribution, [uv](https://docs.astral.sh/uv/), `g++`, and `pdftoppm` from
poppler for the figure comparison):

```sh
cd paper && tectonic core.tex             # or latexmk -pdf core.tex
bash paper/scripts/run_all.sh            # about 5 minutes; exit status 0 iff every value and figure agrees with the paper
```

The blueprint (plasTeX via uv; no TeX Live needed) and the explainers' cross-checks (need `node`):

```sh
scripts/build_blueprint.sh               # regenerates blueprint/src from paper/core.tex, then blueprint/web/
uv run --no-project python scripts/check_blueprint_decls.py      # every \lean{} name resolves (after lake build)
uv run --with numpy --with matplotlib python explainers/check/crosscheck.py     # page 1
uv run --with numpy --with matplotlib python explainers/check/crosscheck23.py   # pages 2 and 3
```

The explainer pages can also be opened locally: `site/build_site.sh _site` assembles the website in `_site/`.

## Versions

Release v1.0.0 = version 1 of the manuscript. A later version of the manuscript gets a new release (v2.0.0, …) of this
repository, a new Zenodo version under the same concept DOI, and a new version of the Palomar entry.

## Use of AI

The constructions, proofs and Lean formalization were produced by AI systems (Anthropic Claude Opus 5.5; some early exploratory results used Claude Fable 5.1) under the author's direction. The author selected the problems, steered the research and reviewed the formal statements, but has not verified every proof by hand. AI systems are not listed as authors; responsibility for the deposit rests with the author.

## Citation

See [`CITATION.cff`](CITATION.cff).

## Licence and third-party material

Code, Lean sources, scripts and data: MIT ([`LICENSE`](LICENSE)). Manuscript (`paper/core.tex`, `paper/core.pdf`,
`paper/figs/`): CC BY 4.0 ([`paper/LICENSE.md`](paper/LICENSE.md)).

The centred-residue helper `cres` (in the `*Defs` modules of `Z3Net/`) is adapted from `GKEvenNet.cres`
(`GKEvenNet/Distance.lean`) in Lennart Rudolph's Palomar formalization of the even-order Grünschloß–Keller nets,
<https://github.com/lennrt/palomar-formalizations> (archived at Zenodo, doi:10.5281/zenodo.22264675), released under
the MIT License, Copyright (c) 2026 Lennart Rudolph; its copyright line is reproduced in `LICENSE`. The layout of the
Lean project follows the same repository's Palomar template. Lean 4, Mathlib and the Python packages used by the scripts
are dependencies fetched at build time; they are not redistributed here.

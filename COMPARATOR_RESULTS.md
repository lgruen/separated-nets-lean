# Comparator results (release v1.0.0)

[Comparator](https://github.com/leanprover/comparator) checks that the theorems of a Solution are exactly the statements
of the Challenge, use only the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`), and replays the proofs in
the Lean kernel and in the independent NanoDa kernel. Both kernels must accept.

Tooling: Comparator, `lean4export` at tag `v4.35.0-rc3`, NanoDa (`enable_nanoda: true`); Lean `v4.35.0-rc3`, Mathlib
`v4.35.0-rc3`; macOS (Apple M-series laptop), where `landrun` is replaced by the shim `scripts/fake-landrun.sh` (no
sandbox). Invocation, from the repository root:

```sh
PATH=<tools>/landrunbin:<tools>/nanoda_lib/target/release:$PATH \
COMPARATOR_LEAN4EXPORT=<tools>/lean4export-rc3/.lake/build/bin/lean4export \
COMPARATOR_NANODA=<tools>/nanoda_lib/target/release/nanoda_bin \
lake env <tools>/comparator/.lake/build/bin/comparator <config>.json
```

or `scripts/run_comparator_full.sh <tools> <config> <tag>` (writes `comparator_<tag>.log` and a summary
`comparator_<tag>.result`).

| configuration | theorems | result | wall clock | user CPU | max RSS |
|---|---|---|---|---|---|
| `comparator.json` (the statement library) | 616 | accepted: `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`, `Your solution is okay!`, exit 0 | 5,758 s (96 min; 2026-10-12 23:41:54 → 2026-10-13 01:17:52) | 8,296 s | 21.0 GB |
| `comparatorHeadline.json` (the Palomar headline entry, Theorem A) | 4 | accepted: both kernels, `Your solution is okay!`, exit 0 — run on this release's files (2026-10-13 06:57:01 → 06:58:07) | 66 s | 52 s | 5.97 GB |

The run of `comparator.json` was made on the Lean files of the development repository from which this release is
staged; the `.lean` files of this release are identical to them apart from comments (paths of research notes, the
paper reference in the file headers, the AI-use pointer), which a script checks file by file after removing comments and
normalizing whitespace (`lean_code_equal`, all 496 `.lean` files). The `lakefile.toml` of this release omits one library of
retired developments that is not a default target and that no module of this release imports. Comments do not enter
the kernel terms that Comparator compares and replays; the headline configuration was re-run on this release itself.

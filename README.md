# Lean formalizations: well-separated three-dimensional (0,m,3)-nets

Machine-checked Lean 4 companions to two manuscripts by Leonhard Grünschloß on
three-dimensional low-discrepancy point sets with large minimum distance.
Each subdirectory will hold an independent Lake project prepared for the
[Palomar registry](https://palomar-registry.org/) (`Challenge.lean` / `Solution.lean` /
`comparator.json` / `formalization.yaml`).

| Directory | Subject | Status |
| --- | --- | --- |
| `z3net/` | Explicit digital (0,3k,3)-nets over Z/q with minimum distance ≥ c(q)·N^(-1/3) for every base q ≥ 4 | in preparation |
| `eisenstein/` | The Eisenstein (0,3,3)-nets over F_p, p ≡ 1 mod 3 | in preparation |

## AI disclosure

The constructions, proofs and Lean formalization were produced by AI systems (Anthropic Claude)
under the author's direction; the author selected the problems, steered the research and reviewed
the formal statements, but has not verified every proof by hand. AI systems are not listed as
authors, in accordance with the policies of Hexagon, Palomar and arXiv; responsibility for the
deposit rests with the author. Each project's `formalization.yaml` and README record the
automation used, the scope of what is formalized, and what remains informal.

## Licence

MIT (see `LICENSE`).

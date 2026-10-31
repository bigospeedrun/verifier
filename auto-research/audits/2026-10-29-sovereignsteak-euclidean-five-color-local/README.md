# Independent local Lean replay: no proper five-coloring of the plane

## Claim and scope

The pinned `openai/math` source proves that there is no function from the Euclidean plane to five colors that assigns different colors to every pair of points at Euclidean distance one. Its theorem is `OAI.EuclideanFiveColor.no_proper_five_coloring`. The statement quantifies over all colorings, with no measurability or continuity premise. It is the lower-bound half of the source's plane-coloring formalization; this audit does not check the separate seven-color construction.

The independent `code/Scope.lean` restates the comparator's `ProperColoring` definition literally and checks in Lean that the source theorem proves its negation for five colors. This covers the complex-plane model, exact unit distance, and unrestricted coloring function. The comparator's placeholder proof is never imported.

The [source scope note](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/158.md) describes the lower and upper bounds. This audit checks only the stated lower-bound theorem and does not establish historical priority.

## Independent check

The source is pinned to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The verifier checks all 132,851 Git-tracked source files against an aggregate path-and-content digest. It checks Lean 4.34.1, all 42 dependency Git heads against the Lake manifest, and hashes the 734 modified or added dependency files against `data/dependency-overlay.json`. The overlay comes from the source's compatibility build configuration.

On the user's FreeBSD machine, Lake built `OAI.Geometry.PlaneColoring.Five`. The independent scope and standard-axiom checks passed, and `leanchecker` replayed the capstone. Evidence is in `evidence/local-build.log` and `evidence/local-run.json`.

## Reproduce

With Git, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-29-sovereignsteak-euclidean-five-color-local/verify.py
```

The verifier fetches the pinned source, resolves its pinned dependencies, rebuilds the capstone, checks its exact scope and axiom closure, and replays the module through Lean's kernel. `verify.py --help` provides an existing-checkout mode.

The trust boundary is Lean's kernel, the three standard axioms if found, the pinned imported libraries, and the source's formal definitions.

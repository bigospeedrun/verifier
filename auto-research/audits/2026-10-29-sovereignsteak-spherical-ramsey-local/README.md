# Independent local Lean replay: twelve-point spherical non-Ramsey witness

## Claim and scope

The pinned OpenAI/math source defines twelve points on the Euclidean unit circle. Its `OAI.GrahamSpherical.full_main` proves that in every positive Euclidean dimension there is a 50-coloring with no monochromatic isometric copy of this set. The source also concludes that this set is not Euclidean Ramsey. `OAI.GrahamSphericalReference.challenge` exports the same full statement.

The independent `code/Scope.lean` matches the theorem to the literal conjunction: cardinality 12, inclusion in the unit circle, avoidance for every positive target dimension, and negation of the source's Euclidean Ramsey property. The `AvoidsCopy` and `EuclideanRamsey` definitions are in the pinned `Model.lean`; colorings are arbitrary functions and copies are isometries of the finite set. This is a formal theorem about the stated witness and definitions, not a claim about every spherical set.

## Independent check

The source is `openai/math` at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The verifier checks all 132,851 Git-tracked source files against an aggregate path-and-content digest. It checks Lean 4.34.1, all 42 dependency Git heads against the Lake manifest, and hashes the 734 modified or added dependency files against `data/dependency-overlay.json`. The compatibility overlay comes from the source build configuration.

On the user's FreeBSD machine, Lake built `OAI.Combinatorics.SphericalRamsey.Result` successfully (2,676 jobs). The scope probe passed, both theorem axiom closures contained only `propext`, `Classical.choice`, and `Quot.sound`, and `leanchecker` replayed the module. Evidence is in `evidence/local-build.log` and `evidence/local-run.json`.

## Reproduce

With Git, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-29-sovereignsteak-spherical-ramsey-local/verify.py
```

The verifier fetches the pinned source, resolves its pinned dependencies, rebuilds the capstone, checks its exact scope and axioms, and replays the module through Lean's kernel. `verify.py --help` provides an existing-checkout mode.

The trust boundary is Lean's kernel, the three standard axioms if found, the pinned imported libraries, and the formal definitions in the source. This audit does not establish historical priority.

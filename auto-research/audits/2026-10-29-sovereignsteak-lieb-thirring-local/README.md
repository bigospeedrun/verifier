# Independent local Lean replay: sharp Lieb–Thirring theorem

## Claim and scope

The pinned `openai/math` source proves the sharp one-dimensional Lieb–Thirring bound for `1/2 < γ < 3/2`. For every admissible nonnegative real potential `W`, the full negative-eigenvalue moment of its Schrödinger form is bounded by the explicit sharp constant times the potential integral. The theorem identifies both the unrestricted and one-state optimal constants and gives an explicit equality potential `(r+1) sech²(rx)` with `r = (γ-1/2)⁻¹`.

The capstone is `OAI.SharpLiebThirring.sharp_lieb_thirring`. The independent `code/Scope.lean` expands the full `MainClaim` into its six conjuncts: the universal bound, two constant equalities, admissibility and positive mass of the equality potential, and equality at that potential. The source's `ComparatorChallenges/LiebThirring.lean` states the same claim. The verifier checks that all definitions from `H1` through `MainClaim` match the solution's `Model.lean` byte for byte, excluding only the comparator theorem's documentation and placeholder proof. The comparator proof is never imported.

The [source scope note](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/262.md) describes the full negative-eigenvalue moment with no finite spectral cutoff. This audit checks the exact formal definitions and theorem; it does not establish historical priority.

## Independent check

The source is pinned to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The verifier checks all 132,851 Git-tracked source files against an aggregate path-and-content digest. It checks Lean 4.34.1, all 42 dependency Git heads against the Lake manifest, and hashes the 734 modified or added dependency files against `data/dependency-overlay.json`. The overlay comes from the source's compatibility build configuration.

On the user's FreeBSD machine, Lake built `OAI.Analysis.LiebThirring.Main`. The scope probe and standard axiom closure check passed, and `leanchecker` replayed the capstone. Evidence is in `evidence/local-build.log` and `evidence/local-run.json`.

## Reproduce

With Git, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-29-sovereignsteak-lieb-thirring-local/verify.py
```

The verifier fetches the pinned source, resolves its pinned dependencies, rebuilds the capstone, checks its scope and axiom closure, and replays the module through Lean's kernel. `verify.py --help` provides an existing-checkout mode.

The trust boundary is Lean's kernel, the three standard axioms if found, the pinned imported libraries, and the source's formal definitions.

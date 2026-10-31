# Independent local Lean replay: one-sample matroid prophet inequality

## Claim and scope

The pinned `openai/math` source proves a one-sample matroid prophet inequality with expected online reward at least `2⁻³¹⁰` times the expected offline optimum. Each labeled matroid element has one sample paired with an identically distributed nonnegative online value; all sample and online coordinates are independent. A finite seed law and online rule depend only on the labeled matroid. The rule is prefix-feasible and irrevocable. The arrival order may be a measurable function of all samples, values, and seed bits. Only the offline optimum is required to be integrable.

The capstone is `OAI.MatroidProphet.one_sample`. The independent `code/Scope.lean` expands the full `OneSampleChallenge` type, including its universe-polymorphic probability space, independence, identical marginal, seed-law, integrability, adaptive-arrival, feasibility, and `2⁻³¹⁰` reward clauses. The source's `ComparatorChallenges/MatroidProphet.lean` states the same claim. The verifier checks that all definitions from `Weights` through `OneSampleChallenge` match the solution's `Model.lean` byte for byte. The comparator's placeholder proof is never imported.

The [source scope note](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/111.md) describes the formal result. This audit checks the exact formal statement, not historical priority.

## Independent check

The source is pinned to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The verifier checks all 132,851 Git-tracked source files against an aggregate path-and-content digest. It checks Lean 4.34.1, all 42 dependency Git heads against the Lake manifest, and hashes the 734 modified or added dependency files against `data/dependency-overlay.json`. The overlay comes from the source's compatibility build configuration.

On the user's FreeBSD machine, Lake built `OAI.Probability.MatroidProphet.Main`. The scope probe and standard axiom closure check passed, and `leanchecker` replayed the capstone. Evidence is in `evidence/local-build.log` and `evidence/local-run.json`.

## Reproduce

With Git, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-29-sovereignsteak-matroid-prophet-local/verify.py
```

The verifier fetches the pinned source, resolves its pinned dependencies, rebuilds the capstone, checks its scope and axiom closure, and replays the module through Lean's kernel. `verify.py --help` provides an existing-checkout mode.

The trust boundary is Lean's kernel, the three standard axioms if found, the pinned imported libraries, and the source's formal definitions.

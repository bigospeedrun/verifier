# Independent local Lean replay: metric-entropy duality counterexample

## Claim and scope

The pinned `openai/math` source proves that for every real `a,b ≥ 1`, some positive finite dimension contains an origin-symmetric compact convex body `K` with nonempty interior whose primal and polar covering numbers both have finite cover witnesses, while

`b · log N(B∞° , a⁻¹ K°) < log N(K, B∞)`.

Here `B∞` is the coordinate cube, `°` denotes the source's literal polar, and `N(A,B)` is the least number of translates of `B` needed to cover `A`. The theorem is `OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers`. The independent `code/Scope.lean` checks the full type, including both `Coverable` conjuncts and strict inequality. The source's `ComparatorChallenges/MetricEntropyDuality.lean` states the same claim. Its definitions of cube, polar, covering number, and symmetric convex body match the solution's `Model.lean`; the comparator's placeholder proof is never imported for this replay.

The [source scope note](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/329.md) describes this as a counterexample to a proposed universal metric-entropy comparison. This audit checks the exact formal statement, not historical priority.

## Independent check

The source is pinned to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The verifier checks all 132,851 Git-tracked source files against an aggregate path-and-content digest. It checks Lean 4.34.1, all 42 dependency Git heads against the Lake manifest, and hashes the 734 modified or added dependency files against `data/dependency-overlay.json`. The overlay comes from the source's compatibility build configuration.

On the user's FreeBSD machine, Lake built `OAI.Analysis.MetricEntropy.Main` successfully (2,244 jobs). The scope probe passed, the theorem's axiom closure contained only `propext`, `Classical.choice`, and `Quot.sound`, and `leanchecker` replayed the capstone. Evidence is in `evidence/local-build.log` and `evidence/local-run.json`.

## Reproduce

With Git, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-29-sovereignsteak-metric-entropy-local/verify.py
```

The verifier fetches the pinned source, resolves its pinned dependencies, rebuilds the capstone, checks its scope and axiom closure, and replays the module through Lean's kernel. `verify.py --help` provides an existing-checkout mode.

The trust boundary is Lean's kernel, the three standard axioms if found, the pinned imported libraries, and the source's formal definitions.

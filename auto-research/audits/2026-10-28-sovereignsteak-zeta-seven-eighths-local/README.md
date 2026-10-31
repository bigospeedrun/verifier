# Independent local Lean replay: the 7/8 zeta zero-free theorem

## Claim and scope

The pinned theorem `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` says that
Mathlib's `_root_.riemannZeta s` is nonzero for every complex `s` with
`Re(s) > 7/8`. The independent `code/Scope.lean` states that exact implication,
including the strict inequality and the Mathlib function name. This package
checks the zeta consequence; the source's uniform Dirichlet and finite-order
Hecke claims are outside scope.

The [site's quasi-Riemann page](https://bigospeedrun.com/other/quasi-riemann)
names OpenAI's 7/8 result as its baseline and ranks uniform Dirichlet
thresholds. This audit does not change that ranking.

## Independent check

The source is `openai/math` at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. All 132,851 Git-tracked
files match the aggregate path-and-content digest in `data/source.json`.
The source pins Lean 4.34.1 and a Lake manifest. Its build configuration
applies compatibility patches to some imported libraries before resolution;
the local verifier checks the resulting dependency Git heads against the
manifest.

On the user's FreeBSD 15.1 machine, the local job resolves dependencies,
obtains Mathlib's cache, rebuilds `OAI.NumberTheory.DirichletL.Nonvanishing`,
and replays that module with `leanchecker`. The separate scope probe checks
the theorem's exact target and allowed axiom closure. The completed local run
passed all checks; `evidence/local-run.json` records its result.

## Reproduce

With Git, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient
network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-28-sovereignsteak-zeta-seven-eighths-local/verify.py
```

The verifier fetches the exact source commit, checks every tracked file,
resolves pinned dependencies, builds the theorem, checks the independent
scope probe and axiom closure, and replays the capstone module. `verify.py
--help` documents an existing-checkout mode.

This audit trusts Lean's kernel, the three standard axioms if found, the
pinned imported libraries, and the formal definitions. It does not prove
the paper's analytic argument separately or settle priority.

# Independent local Lean replay: uniform real Dirichlet zero gap

## Claim and scope

The pinned source proves that there is one real constant `c > 0` such that,
for every modulus `q ≥ 3`, every primitive nonprincipal Dirichlet character
whose values are real, and every real zero `0 < β < 1` of its Mathlib
`LFunction`, the inequality `c ≤ (1 - β) · log q` holds. The constant is
uniform in `q` and the character. The statement includes both character
parities and does not give a numerical value for `c`.

The two source capstones are
`OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap` and
`OAI.SiegelZeros.WeightedTorusJets.dirichletRealZeroBound_proof`. The
independent `code/Scope.lean` checks their exact types against the source's
comparator, including quantifier order, primitivity, nonprincipality,
real-valuedness, the real-zero interval, and the logarithmic inequality.
This is a different conclusion from the earlier 7/8 zeta, Dirichlet, and
Hecke nonvanishing audits.

The [site's quasi-Riemann page](https://bigospeedrun.com/other/quasi-riemann)
ranks uniform Dirichlet zero-free half-plane thresholds. This audit concerns
the source's related uniform real-zero gap and does not change that ranking.

## Independent check

The source is `openai/math` at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. All 132,851 Git-tracked
files match the aggregate path-and-content digest in `data/source.json`.
The source pins Lean 4.34.1 and a Lake manifest. Its build configuration
applies compatibility patches to some imported libraries before resolution.
The local verifier checks all 42 dependency Git heads against the manifest
and hashes the 734 modified or added source files against
`data/dependency-overlay.json`.

On the user's FreeBSD 15.1 machine, the two capstone modules were built
with Lake. The local verifier checks their exact statements and standard
axiom closures and replays both modules with `leanchecker`. The completed
result is in `evidence/local-run.json`, with the Lake build output in
`evidence/local-build.log`.

## Reproduce

With Git, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient
network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-29-sovereignsteak-siegel-real-gap-local/verify.py
```

The verifier fetches the exact source commit, checks every tracked file,
resolves pinned dependencies, builds both capstones, checks the independent
scope probe and axiom closures, and replays both modules through Lean's
kernel. `verify.py --help` documents an existing-checkout mode.

This audit trusts Lean's kernel, the three standard axioms if found, the
pinned imported libraries, and Mathlib's formal definitions. It does not
establish historical priority or a numerical gap constant.

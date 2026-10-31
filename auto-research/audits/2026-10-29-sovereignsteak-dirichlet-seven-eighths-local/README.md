# Independent local Lean replay: uniform Dirichlet 7/8 nonvanishing

## Claim and scope

The pinned theorem `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`
states that every complex Dirichlet character of every positive modulus has
nonzero `LFunction` at every complex `s` with `Re(s) > 7/8`, except at the
principal character's pole `χ = 1` and `s = 1`. The independent `code/Scope.lean`
checks those quantifiers, the strict inequality, the pole exception, and the
exact Mathlib function. This is the uniform Dirichlet theorem itself, which
was outside the earlier zeta-only audit's scope. It does not check the source's
finite-order Hecke theorem or Landau–Siegel corollary.

The [site's quasi-Riemann page](https://bigospeedrun.com/other/quasi-riemann)
ranks uniform Dirichlet thresholds and lists OpenAI's 7/8 theorem as its
baseline. This audit independently reproduces that baseline; it does not
change the site's threshold or ranking.

## Independent check

The source is `openai/math` at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. All 132,851 Git-tracked
files match the aggregate path-and-content digest in `data/source.json`.
The source pins Lean 4.34.1 and a Lake manifest. Its build configuration
applies compatibility patches to some imported libraries before resolution;
the local verifier checks the resulting dependency Git heads against the
manifest.

On the user's FreeBSD 15.1 machine, the pinned capstone module was rebuilt
locally with 7,061 Lake jobs. This audit reuses those artifacts, checks
the exact module target with Lake, tests the theorem scope and allowed
axiom closure, and replays the module with `leanchecker`. The completed
result is in `evidence/local-run.json`.

## Reproduce

With Git, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient
network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-29-sovereignsteak-dirichlet-seven-eighths-local/verify.py
```

The verifier fetches the exact source commit, checks every tracked file,
resolves pinned dependencies, builds the theorem, checks the independent
scope probe and axiom closure, and replays the capstone module. `verify.py
--help` documents an existing-checkout mode.

This audit trusts Lean's kernel, the three standard axioms if found, the
pinned imported libraries, and the formal definitions. It does not establish
historical priority or verify the source's broader claims.

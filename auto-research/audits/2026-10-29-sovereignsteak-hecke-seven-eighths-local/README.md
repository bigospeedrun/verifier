# Independent local Lean replay: finite-order Hecke 7/8 nonvanishing

## Claim and scope

The pinned theorem
`OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re`
proves nonvanishing for every character in the source's finite-order Hecke
family over `CyclotomicField 3 ℚ`, at every complex `s` with `Re(s) > 7/8`,
except when the residue character is principal and `s = 1`. The source
models the function as its continued lattice L-function divided by six.
The independent `code/Scope.lean` checks the exact theorem statement, field,
function definition, its ideal-series identity in `Re(s) > 1`, the strict
inequality, and pole exception.

The [site's quasi-Riemann page](https://bigospeedrun.com/other/quasi-riemann)
ranks uniform Dirichlet thresholds and notes that OpenAI's 7/8 work also
covers finite-order Hecke functions over the Eisenstein field. This audit
checks that separate Hecke theorem. It does not change the site's Dirichlet
ranking, and the previous zeta and Dirichlet audits did not cover it.

## Independent check

The source is `openai/math` at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. All 132,851 Git-tracked
files match the aggregate path-and-content digest in `data/source.json`.
The source pins Lean 4.34.1 and a Lake manifest. Its build configuration
applies compatibility patches to some imported libraries before resolution;
the local verifier checks the resulting dependency Git heads against the
manifest.

On the user's FreeBSD 15.1 machine, the Hecke capstone module was built with
Lake, then the local verifier checked the independent scope and standard
axiom closure and replayed the module with `leanchecker`. The completed
result is in `evidence/local-run.json`; the Lake build output is in
`evidence/local-build.log`.

## Reproduce

With Git, Python 3.12, Lean 4.34.1, Lake, `leanchecker`, and sufficient
network, disk, and compute capacity:

```sh
python3.12 auto-research/audits/2026-10-29-sovereignsteak-hecke-seven-eighths-local/verify.py
```

The verifier fetches the exact source commit, checks every tracked file,
resolves pinned dependencies, builds the theorem, checks the independent
scope probe and axiom closure, and replays the capstone module. `verify.py
--help` documents an existing-checkout mode.

This audit trusts Lean's kernel, the three standard axioms if found, the
pinned imported libraries, and the formal definitions. It does not
independently establish that the source's `LFunction` matches every analytic
convention for Hecke L-functions, or establish historical priority.

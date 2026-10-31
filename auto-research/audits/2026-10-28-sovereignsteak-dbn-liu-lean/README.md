# Independent Lean rebuild: de Bruijn–Newman real-zero bound

## Claim and result

The pinned release proves in Lean that, for every real
`t ≥ 2811857/10000000` and every complex `z`, a zero of its explicit
heat-deformed Fourier integral `DBN.H t z` has imaginary part zero. With the
classical definition of the de Bruijn–Newman constant, this gives the bound
`Λ ≤ 0.2811857`. The Lean source does **not** define `Λ` as a separate object;
the formal theorem is the quantified real-zero statement.

This audit independently materialized the pinned single-toolchain workspace,
checked the release's 124 tracked files, all 225 Liu source hashes (including
219 Lean modules), and the 2,925-module OpenAI closure manifest. Its 42
dependency revisions matched the original OpenAI manifest, including Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The required Lean targets
compiled in [an independent SovereignSteak GitHub Actions run](https://github.com/SovereignSteak/qrh-debruijn-newman/actions/runs/40760974281).
Its separate scope probe checked the literal `Φ` and `H_t` definitions,
Liu's zero-free input, and the exact rational theorem statement. The three
scoped theorems used only `Classical.choice`, `Quot.sound`, and `propext`;
`leanchecker` replayed `ArdaDBNLiu`. The fork differs from the pinned release
only in its scope probe and workflow steps. The run receipt is
`evidence/ci-run.json`; the source-materialization checks are recorded in
`evidence/materialization.json`, and all 42 checkout heads and 23 applied
compatibility patches are recorded in `evidence/dependencies.json`.

Comparator with nanoda accepted the positive challenge and rejected the
tampered `DBN.Φ` negative control in that run. The separate FreeBSD build
reached 10,924 of 12,117 steps without a compiler error, then was stopped
after the fork completed all checks. Partial local probes checked the `Φ` and
`H_t` definitions, the converter's quantifiers, and its axiom-query syntax;
`evidence/local-partial.json` records that attempt. This audit is not a new
proof or a claim that the site's ranked zero-free threshold improved.

## Reproduce

On a host with Git, Bash, Python 3.12, Lean 4.34.1 with Lake and
`leanchecker`, and `patch`:

```sh
python3.12 auto-research/audits/2026-10-28-sovereignsteak-dbn-liu-lean/verify.py
```

The command supplies temporary compatibility wrappers for the publisher's
`python3`, `shasum`, and GNU `patch` calls. It clones the exact release,
Arda tag, OpenAI/math and Liu commits,
checks their source identity, runs the publisher's materialization recipe,
resolves the pinned dependency manifest, fetches the Mathlib build cache,
builds the five declared targets, checks the separate scope probe and allowed
axioms, and replays `ArdaDBNLiu` through `leanchecker`. It needs network access,
substantial disk space, and time. On FreeBSD without `procfs`, Lean also needs
a procfs mount or an equivalent application-path shim. For a fully prepared
local workspace, `verify.py --help` lists the paths and `--reuse-build` option.

The partial FreeBSD run materialized from shallow pinned Git checkouts using
the publisher's nested recipe, with portability wrappers for `python3`,
`shasum`, and GNU `patch` flags. It started with the same pinned Mathlib
4.34.1 source/cache tree as the previous audits; Lake re-elaborated much of
the imported graph while compiling the bridge closure. Lean processes
ran at normal `nice 0`, above the host's `worker` (`nice 19`) and `xmrig`
(`nice 10`) processes.

## Sources and limits

- Verifier base: `49533557838fde36981606aa2098374b09ea8649`.
- Audited release: `DrMurphyIsIn/qrh-debruijn-newman` at
  `afd94c7ddf8bea3a3b8bb2e95657cccae463993c`.
- Arda tag `qrh-liu-v1.1.0` resolves to
  `2b1be6c5023d69aa7c9bc70ee843bdaa1bf383db`.
- OpenAI/math: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Liu source: `7d10420de90efa2f082a06a342fc7accbd57ab37`.
- The site's 2026-10-28 relevant-repository note is in
  `data/site-record.json`. The page ranks a zero-free half-plane parameter
  `θ`; this result concerns the different quantity `Λ`.

The audit assumes Lean's kernel, standard axioms, the pinned imported
libraries, and the source's formal definitions. It does not independently
establish every analytical interpretation of `H_t`, or verify the release's
novelty or historical priority. The site note and evidence level remain under
maintainer control; this package does not invoke the direct proof verifier.

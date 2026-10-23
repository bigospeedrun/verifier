# Sources, credit and AI disclosure

Audit prepared for GitHub user `ptweezy` using Muse Spark via Muse.
The audit was designed and the package assembled by that agent; every
number reported was produced by the bundled program (`code/`), not by
the model. No additional AI models were used. New audit text and code
are contributed under this repository's Apache-2.0 license.

The underlying result — the general design theorem for the Catalan
determinant construction, the design `(96, 15, 6, 8, 5)`, and the
method of certifying its four conditions — is due to Marcos Carreira
(`MarcosCarreira/catalan-designs`, including the paper
`catalan_design_extension.tex`). The smaller design `(36, 6, 2, 3, 2)`
and the certified bound μ(G) < 2401.741 audited here are due to the
author of `fringewidth/catalan-exponent`, whose README credits the
search and certification to Claude. The determinant construction
itself originates in the OpenAI preprint "Catalan's constant is
irrational" (24 September 2026), upstream of both repositories. This
audit claims no authorship of any of those results.

Sources inspected:

- fringewidth/catalan-exponent, commit
  `0e4877172b313a04da51c972ac91348f071b8481`: `README.md`,
  `RESULT.json`, `scripts/` (`certify.py`, `mu_cert.py`,
  `package.py`, `catlib.py`, `catmu.py`, `search.py` — read to pin
  the chain and the assembly; `certify.py` is not runnable in that
  repo's layout, see the audit README §6.4), and
  `certificates/cert_36_6_2_3_2/` in full (the parametrised
  scripts, their logs, and their saved outputs). The bundled
  `data/` files are the claimant's saved JSON outputs: the two
  witness files are load-bearing inputs to the audit's link L5;
  the remaining saved outputs are comparison/context data only.
  Per-file SHA-256 pins are in `data/SOURCES.json`. No claimant
  code is redistributed in this package.
- MarcosCarreira/catalan-designs, commit
  `ec231b32f94cc3ec6a3e61b717b264f8382bb4ac` (the commit the audited
  package pins in its README): `paper/catalan_design_extension.tex`
  (the written definitions and Theorem `thm:main`, Corollary
  `xcor:massminors`, Theorem `xthm:exponent`, Table 1) and
  `new_design/` (the original scripts the fringe package
  parametrised). That repo's newer HEAD (a version-2 claim) was not
  used.
- The OpenAI preprint itself was not among the pinned sources and
  was not consulted. Where the chain depends on it (the `M⁰/Z⁰`
  moment arrays of its Eqs. (14), (16), (17), as implemented by the
  claimant), the audit relies on the paper's published Table 1 as a
  positive control, the exact `ζ(2)` cancellation, and
  cross-method determinants, and says so in the README.
- bigospeedrun/verifier, base commit
  `106c0f1b12f14c2dc735e7c35636e94a382fe858`.
- The Big O Speedrun Catalan row (https://bigospeedrun.com/other/catalan),
  retrieved 2026-10-23: Carreira < 2715, Claimed; the
  fringewidth/catalan-exponent line credits μ(G) < 2401.741. This
  is mutable snapshot evidence; the retrieval date is recorded in
  `data/SOURCES.json`.

The claimant's own parametrised scripts were run once, in a scratch
copy outside this package, purely as a cross-check after the
independent recomputation was complete
(`evidence/claimant_crosscheck.json`); they are not an input to the
audit and are not redistributed here. The independent implementation
was written from the written definitions in the paper.

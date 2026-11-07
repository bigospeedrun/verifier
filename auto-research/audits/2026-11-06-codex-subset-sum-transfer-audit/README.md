# Audit: Subset Sum filter-3 transfer and scalar feasibility

**Result: PASS within the scope below. Publication status: local draft, not submitted.**

This independently implemented checker audits the parameters and moved-boundary
step of Yanni Bills's conditional Subset Sum exponent **0.4876723**, at
commit [`bf1f50f066f2c71a53293791f693f505a67a1540`](https://github.com/yannouli/subset-sum-conditional-refinement/tree/bf1f50f066f2c71a53293791f693f505a67a1540).
The algorithm and predecessor results retain their original authorship.

## Reproduce

From the contribution directory (or a future verifier checkout), run:

```sh
python auto-research/audits/2026-11-06-codex-subset-sum-transfer-audit/verify.py
```

Python 3.10 or later, standard library only. Tested on Python 3.15.2 on Windows.
No network, optimizer, Lean installation, or upstream executable is used.
The command checks the file manifest, recomputes the report, runs the rejection
checks, and compares its result with `evidence/expected.json`. Every line begins
with `PASS`, except the final two scope/submission notices. Failure exits nonzero.
It writes no files, including bytecode caches.

## Hypothesis and findings

The published rational tuple satisfies the twenty listed scalar inequalities
with the proposed common margin, and its two special certificate shifts preserve
the required affine identities.

| Check | Independently computed result |
| --- | --- |
| Alias/auxiliary gaps | All 20 exceed `1e-10` |
| Smallest alias gap | Between `0.000000000999999987694900` and `0.000000000999999987694901` |
| Five conditional moment families | All exceed the reserved `1e-7` |
| Smallest conditional moment margin | Between `0.000000135967911121103700` and `0.000000135967911121103701` |
| Remaining error exponent | Exactly `0.000000097468` |
| Advertised minus internal work exponent | Exactly `0.00000001998` |
| Transfer identities | Both checked by exact coefficient comparison |
| Regions | Ordered endpoints define ten intervals covering nonnegative scores |
| Rejection controls | All 12 invalid variants rejected for the expected reason |

The arithmetic implementation was written for this audit from the mathematical
formulas, without reading or importing the author's checker. It uses exact
rational comparisons and logarithm enclosures with explicit remainder and
rounding bounds. Five 80-digit Decimal spot checks are secondary diagnostics;
they are not used to certify inequalities. See `MATHEMATICS.md`.

## Scope and open obligations

This is a **positive partial audit**, not a new bound or Lean proof. Scalar inputs
were transcribed from pinned web views. The complete 43-filter/430-certificate
baseline was not downloaded or authenticated. Its coefficient maxima, old
moment bounds, and score bound are assumptions of this checker. We did not
evaluate the continuous integrals, execute a Subset Sum solver, or establish
the inherited correctness, isolation, convergence, or word-RAM cost lemmas.
The region check verifies the partition specified in the input, not the existence
of every upstream certificate. Mutation failures concern the checker's sufficient
conditions; they are not counterexamples to the published theorem.

There is no claimed change to the site's evidence level. No defect was found
in the scalar and algebraic slice actually checked.

`RESULT.json` deliberately has `base_commit: null`: the verifier clone was
blocked by network restrictions. Before submission, obtain a checkout and record
its actual commit, complete the prior-package/board/Discord checks described in
`SESSION.md`, and regenerate the manifest. The draft does not yet satisfy all
upstream publication prerequisites. No PR or public post has been made.

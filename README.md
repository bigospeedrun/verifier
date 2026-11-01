# Big O Speedrun verifier

Submit a Lean proof of a bound for Fourier transform, 3SUM, APSP, average
sensitivity, or Catalan's constant.
The verifier checks the proof against our fixed statement on GitHub Actions.
A passing submission appears as **Lean Verified** on [bigospeedrun.com](https://bigospeedrun.com).
An open submission without a passing check appears as **Claimed**.

## Submit

Choose either route. Both use the same statement, record gate, and proof checks.

- **Pull request:** add a new folder under
  `submissions/<problem>/<github-login>-<short-name>/` in this repository.
  Include `Submission.lean`, any extra Lean files under `Submission/`, and
  `manifest.json` containing only `{"problem":"3sum","bound":"1999/1000"}`
  with the problem and bound changed to match the proof. Open a PR that adds
  only that folder. Export `Race.bound` and keep source credits in the Lean files.
- **Issue:** keep the proof in a public repository and
  [open a submission issue](https://github.com/bigospeedrun/verifier/issues/new/choose).
  The form takes the problem, repository URL, complete commit SHA, and reduced
  exact rational bound. Put `Submission.lean` at that repository's root and
  extra Lean files under `Submission/`.

See [the problem guide](docs/targets.md) for the exact target and Lean version.

Use `dft`, `3sum`, `apsp`, `average-sensitivity` or `catalan` for `problem`. Use an
exact nonnegative rational for `bound`. For DFT, the bound is the saving s in
O(n (log n)^(1-s)); a larger saving is better. For 3SUM and APSP, it is the
exponent r in O(n^r); smaller is better. For average sensitivity (an Other bounds
row), it is the coefficient C in AS(f) ≤ C d √n; smaller is better, and only the
issue route takes it. For Catalan's constant (an Other bounds row), it is an upper
bound μ on the irrationality exponent of G; smaller is better, and only the issue
route takes it. The ranges are 0 ≤ s ≤ 1, 0 ≤ r ≤ 2 for 3SUM, 0 ≤ r ≤ 3 for
APSP, 0 ≤ C ≤ 8 for average sensitivity, and 0 ≤ μ ≤ 100000000 for Catalan.

A Catalan proof is large, so it runs in two jobs: a build job, then the check job
([split build](docs/execution.md#split-build-for-large-proofs)). This has three
effects. The bot posts only the final result, not an earlier Lean checkpoint
comment. The run holds the verifier queue for its full time, up to about 12 hours.
Nanoda can end incomplete (time or memory limit); that does not prevent Lean
Verified. To convert an existing proof repository, see
[the Catalan section of the problem guide](docs/targets.md#catalans-constant).

The verifier runs up to nine public submissions and one maintainer test in parallel,
with one queued public run per GitHub account. A run starts only if the bound matches or beats the best Lean Verified result on that board (a Claimed result does not block it);
otherwise, the bot replies that the submission is listed as Claimed and closes it
(it stays listed as Claimed; a better bound is a new submission). A bound worse than the classic bound of its board
is not a race result: the bot replies, closes the issue, and it is not listed.
The bot posts a receipt on the issue or PR. For PRs, a Lean pass causes an
automatic merge. A real Lean or axiom failure, or a real nanoda rejection,
causes an automatic close. A timeout, resource limit, or infrastructure failure
leaves the PR open with a review label and a maintainer mention. A below-record
PR is closed and stays listed as Claimed. Scheduled checks pick up new PR commits.
On an issue, a "Not verified" result gives its reason on the next line. A setup
failure caused by the submission itself (for example, no `Submission.lean` at the
root of the repository) closes the issue: fix it and open a new issue. Other setup
failures can be temporary and stay open for review.

Before merging, the bot checks that the PR adds only its own new submission
folder and that its head is the verified commit. An unsafe diff is closed with a reason.
If the head changed, the bot skips the merge and leaves the PR open for the new check. A check does not transfer another author's credit.

For each submission version, the bot also posts a derivation report: the closest
verified submission of another author by identical Git files, the numbers of
changed, added and removed files, whether only numeric constants changed, and
whether the earlier credit lines are kept. The report quotes no file content.
When at least 80% of the files are identical to a verified submission of another
author and the other files change only numeric constants, the proof still runs,
but a pass does not merge or close the submission and is not listed as Lean
Verified until a maintainer reviews the credit. The bot's hold comment names the
earlier submission and the entry that releases the hold (in the site's
data/review-decisions.json); with that entry, the next scan merges the PR or
closes the issue, and the site lists the result.

## What Lean Verified means

The proof establishes the submitted bound in our fixed computational model.
Comparator checks the statement and definitions against our trusted copy,
checks allowed axioms, and replays the proof with Lean and nanoda. The Lean kernel
and the axiom audit must pass. The bot posts this result immediately. Nanoda
runs afterward as an advisory check and updates the receipt. A nanoda timeout or resource limit does not prevent
Lean Verified; a real nanoda rejection blocks the row for maintainer review.
An ambiguous failure stays pending review. Only `propext`, `Quot.sound`, and `Classical.choice`
are allowed. A normal Lean build alone does not pass this gate.

Lean Verified does not establish novelty, priority, authorship, or practical
speed. A passing check does not by itself mean that the bound is a new record.
The source commit, exact bound, and receipt remain part of the result.

OpenAI wrote the trusted DFT model. Anthropic wrote the trusted 3SUM and APSP
statements, based on the paper by Josh Alman and Virginia Vassilevska Williams.
The [Anthropic statement](challenges/3sum-apsp/EndStatement.lean) is copied
without changes from `anthropics/formal-math` commit
`e1a4e6508154ea59f030480661590a9fe3018011`. Author credits and notices remain
with the source. See [NOTICE](NOTICE).

Proofs run offline on fresh standard GitHub runners, with fixed dependencies,
resource limits, and no access to the token that posts results.
See [issue security and layout](docs/direct-submissions.md),
[PR security and receipt contract](docs/pr-submissions.md),
[execution details](docs/execution.md), and [AGENTS.md](AGENTS.md).

To propose a trusted statement for a problem that has none, see
[the statement contribution guide](docs/new-statements.md).

For research that is not a proof submission (statements, formalization,
audits, tooling and negative results), see [auto-research.md](auto-research.md).

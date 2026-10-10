# Agent instructions

Read README.md and docs/targets.md before you submit a proof.
Choose an issue or a PR. Issues use the four-field form: problem, public repo
URL, full commit SHA, reduced rational bound. PRs add only one new folder at
submissions/<problem>/<github-login>-<short-name>/. Include manifest.json with
exactly problem and bound, Submission.lean exporting Race.bound, and optional
Submission/**/*.lean sources. Keep credit and licenses in source comments.
No other PR files, existing folders, symlinks, executables, build hooks or
compiled objects are permitted. PR titles and bodies are never code or config.

The bot publishes Lean plus axiom acceptance before the nanoda advisory follow-up.
A real later nanoda rejection blocks the earlier evidence and tags the maintainer.
The bot merges passing PRs and closes genuine proof/axiom failures. Resource,
timeout, ambiguous or infrastructure outcomes stay open, labeled for review.
Below-record PRs stay open as Claimed. New commits cause new checks. An unsafe
diff closes with a reason. A changed head skips merge and stays open for its new check.

The verifier owns the statement, target generator, toolchain, dependency pins,
allowed axioms, workflow, and controller. Submission code cannot change them.
Comparator must accept the exact target with the Lean kernel, and the allowed
axiom audit must pass before the site can show Lean Verified. Nanoda resource
limits do not prevent that label. A real nanoda rejection blocks the row and
requires lead review; ambiguous failures remain pending review. A build, a comment, or an author-supplied receipt is
insufficient. A pass does not establish novelty or authorship.

For verifier development, run python3 -m unittest discover -s tests -v.
Run Lean only on GitHub Actions. Never run Lean on the office box.
Keep proof execution and result publication on separate fresh runners.
Never execute submission code in a job with write permission or secrets.
Use the trusted scheduler lease for a shared batch of nine distinct public accounts plus one maintainer smoke.
Never rely on Actions concurrency groups that fork YAML can name.
Reserve issue request hashes and PR heads in the trusted CAS state before
emitting runnable requests. Never deduplicate proof jobs from comment markers.
Poll PR source data from default-branch code; no pull_request or
pull_request_target workflow may select or verify trusted submissions. The workflow_run publisher checks only trusted code and
artifact data. Recheck the complete added-only folder diff, file modes,
controller blob identities and current head. Merge with GitHub’s SHA condition.
Re-read the head immediately before closure; a changed head stays open.
Validate run identity before artifact download; enforce API size and stream caps.
Check the current record at selection and again before compilation. A bound
below the record stays Claimed and starts no Lean run. A tie qualifies unless
a tied leader already has Lean Verified evidence. Preserve separate author rows.
Never check out fork workflow code. Keep action pins and strict input checks.

Current phase: local review only. Do not create public repositories, push,
open PRs, or publish the workflow until the lead confirms README approval.
Tests under tests/fixtures/direct are test-only and must not enter site data.

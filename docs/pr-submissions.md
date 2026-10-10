# Pull-request submissions: local design, 2026-10-10

## Files and automatic outcomes

A PR adds exactly one new directory:
`submissions/<problem>/<lowercase-github-login>-<short-name>/`.
The directory contains `manifest.json` with exactly `problem` and reduced rational
`bound`, `Submission.lean`, and optional ordinary Lean modules in `Submission/`.
The manifest problem must match the path. The PR author login comes from GitHub.
Titles and bodies do not affect the proof request or credit.

Only added regular non-executable files are admitted. Renames, edits, deletions,
symlinks, submodules, compiled objects, hooks, and paths outside that new folder
are rejected. Limit: 500 files, 20 MB each, 150 MB total; manifest at most 1 KB.
The source pin is the PR head SHA in the verifier repository's PR commit graph.
Users need no separate public proof project. A GitHub fork/PR may still be used.

The same all-evidence record gate applies, including a tie unless a tied leader
already has receipt-backed Lean Verified evidence. The check repeats before
compilation. A below-record PR receives a comment, remains open, and stays Claimed.

A Comparator Lean pass plus the permitted-axiom audit qualifies. Nanoda resource
limits do not prevent this result; real rejection does. The bot comments a receipt
and merges a qualifying PR. It comments and closes a real Lean/axiom/nanoda failure.
A timeout, resource limit, cancellation, setup failure, missing artifact, ambiguous
outcome, or failed merge stays open with `verification-needs-review` and a
maintainer mention. A new PR commit triggers a new check. The bot never bypasses
branch protection or retries a merge without the verified SHA.

## Security design

The default-branch `.github/workflows/submissions.yml` scheduler polls open
issues and PRs through the API. There is no trusted `pull_request` or
`pull_request_target` workflow. The scheduler reads PR trees and manifest bytes
as data; `.github/workflows/submission-check.yml` runs each selected proof on a
fresh read-only runner with the trusted scheduler SHA. No job checks out PR code.
A fork-provided workflow cannot select proofs or grant a trusted receipt.

The controller fetches the pinned PR commit with hooks disabled. It copies only
regular Lean files from the validated `source_subdir`. It supplies all Lake files,
dependencies, target definitions, and tools. Proof code executes only in the existing
offline sandbox, with no write token, secrets, checkout, or receipt access.

`.github/workflows/pr-publish.yml` uses `workflow_run` on completed trusted submission batches.
It checks out only the trusted default-branch revision. It never checks out or
executes PR code, even after a pass. It validates the upstream run repository,
workflow ID/path, default-branch event, attempt, controller SHA/repository, and PR identity.
It validates run identity before download, rejects missing or oversized API
`size_in_bytes`, and streams at most 50 MiB plus one sentinel byte. It then
checks the API artifact digest, rejects paths
or duplicate members, and checks receipt/log hashes. Artifact download redirects
do not forward the GitHub token outside api.github.com.

Before any merge, the publisher independently reads the entire current PR diff
and Git trees. It checks the new login-owned folder, added-only paths, regular file
modes, immutable blob identities, manifest hash, full file-list hash, and protected
controller/workflow bytes. The manifest bytes come from the artifact and must match
the PR's Git blob SHA. Proof sources are not read or run in this write-capable job.
An unsafe diff at the checked head is closed with a reason. If the head changed,
the old result skips merge and leaves the PR open for the new commit’s check,
without a review label. This check precedes comparison with the old manifest.
Immediately before closure, the publisher re-reads the PR head and skips closure
if a new commit appeared. GitHub does not offer a SHA condition for closing a PR,
so this narrows rather than eliminates the final read-to-close race. The merge API also receives `sha: verified_head_sha`, which closes the race between
that check and merge. If GitHub declines, the PR stays open for review.

The publisher can reconstruct an accepted artifact after a merge if artifact upload
fails, without merging a second time. The result is not admitted to the site until
GitHub confirms the merge. A passing
receipt alone does not mutate another author's existing row.

## Shared capacity

The trusted selector acquires a Git-ref lease at
`refs/heads/automation/submission-queue`. The ref points to a state-only commit
whose message contains owner run ID/attempt and scan page/offset. A contender
creates a child of the observed commit and uses a non-force fast-forward ref
update. Concurrent sibling updates cannot both win. The selector takes over
only after the prior owner attempt is complete. It admits one batch with at
most nine distinct logins, covering both routes. The manual verifier uses this
same lease. Explicit maintainer smoke uses a separate `automation/smoke-queue`
lease, with one smoke at a time and no public-account slot. Nine plus one preserves
the total cap of ten proof jobs. Proof preflight rechecks ownership, including the attempt, so an
old individual-job rerun cannot reuse admission. Rerun the whole workflow to
acquire a new lease. No trusted workflow uses an Actions concurrency group
that fork YAML can name or cancel.

The selector stops at nine selected entries, forty scanned entries, four minutes,
or four hundred API calls. The cursor advances after each candidate. Request
files and matrix outputs are written after each admission. A later API error
therefore preserves earlier selections; subsequent scans resume at the saved
cursor. Each scan reads at most one hundred comments per candidate. Page/offset
pagination wraps to the start; deletion can shift an item into the next cycle.
Lease-state writes have a fixed bound of two calls per candidate, plus three
calls when reserving an admission. Before emitting a runnable request, the
scheduler stores a permanent reservation under
`admitted/<key-prefix>/<key>.json` in the same CAS-protected state ref. Each
JSON record is at most 1 KiB. The key hashes the route, submission number, and
issue normalized/raw-body hashes or PR head SHA. Lookups fetch exactly that
file at the immutable state commit; they never enumerate a growing ledger.
Each update uses the prior tree and adds one file, preserving previous keys.
There is no eviction that could make an old failed proof runnable again.

Comment markers are display data, not proof deduplication authority. A marker
hidden after hundreds of comments cannot cause a repeat proof job. Reservation
also stops automatic replay after infrastructure failure; such submissions stay
open for review. A crash after reservation but before dispatch fails closed:
it does not erase the reservation or automatically spend proof capacity again.
A changed issue request or new PR head has its own admission identity.

On 2026-10-10, Lead authorized setting repository Actions fork approval to
`all_external_contributors` (the strictest policy). The setting was applied and
an independent API read-back confirmed it. Recheck this prerequisite at deployment. This applies to fork-owned
PR YAML and does not block trusted schedule/issue/default-branch dispatch runs.
Never approve fork workflow YAML to submit a proof; the scheduler reads the
proof files itself. See GitHub’s [fork approval API](https://docs.github.com/en/rest/actions/permissions#update-fork-pr-contributor-approval-permissions-for-a-repository)
and [non-force ref updates](https://docs.github.com/en/rest/git/refs#update-a-reference).
The fork approval setting is the only authorized remote change so far.
The first approved trusted scheduler run creates the state-only ref.

## PR receipt contract for the site

Issue envelopes retain schema version 1. PR publication emits schema version 2 in
`pr-submission-VERIFICATION_RUN_ID-ATTEMPT-publisher-PUBLISHER_RUN_ID-PUBLISHER_ATTEMPT`,
containing `pr-submission-PR_NUMBER.json` for each PR in the batch.
The publisher workflow's own run ID identifies where that artifact lives.

- `schema_version: 2`, `route: pull_request`, `test_only: false`.
- `request`: PR number/URL, authenticated `pr_submitter_login`, `pr_created_at`,
  `head_sha`, observed `base_sha`, actual `verifier_commit`, `source_subdir`,
  normalized `submission`, `submission_sha256`, and the exact controller `inputs`.
- The normalized submission adds `source_subdir` to the issue schema. It keeps
  `repo_url: https://github.com/bigospeedrun/verifier`, `commit: PR_HEAD_SHA`,
  `authors: []`, and `problem`/`bound`. Authors remain subject to source-credit review.
  `inputs` also includes `source_subdir`. The source directory is hash-bound to the
  request; the generated target remains the same `Race.bound` as the issue route.
- `request.manifest_utf8`, `manifest_sha256`, `changed_files`, `changed_files_sha256`.
  The file-list hash covers canonical JSON of sorted `{path, mode, sha, size}`
  objects; `sha` is the Git blob SHA. JSON serialization matches the issue contract.
- `request.record_gate` and `gate: ready|claimed_only|invalid_layout|superseded`.
- `receipt`: full controller receipt with request, profile, generated target hash,
  per-theorem/per-kernel results, axiom audit, UTC checked_at, and artifact hashes.
  A skipped/failed setup may have no mathematical receipt.
- `run_id`, `run_attempt`, `run_url`, `workflow_path`, `workflow_conclusion`,
  `verifier_commit` identify the trusted scheduler run. Its API head SHA is `verifier_commit`,
  not the PR source head. `workflow_path` is `.github/workflows/submissions.yml`;
  the reusable workflow is `.github/workflows/submission-check.yml`.
- `receipt_artifact`: API ID, name, digest, and public URL for
  `pr-verification-RUN-ATTEMPT-PR_NUMBER`. A skipped proof still records its
  selected request and gate; a missing artifact cannot admit a row.
- `receipt_sha256`: SHA-256 of the raw `receipt.json` artifact bytes, before JSON
  parsing or normalization; null when no receipt exists.
- `publisher_commit`, `publisher_run_id`, and `publisher_run_attempt` identify the
  trusted publisher revision and exact attempt. Run IDs and attempts are strings.
  The importer binds these to the publisher API run/attempt and artifact name.
  Source verification run/attempt fields retain their existing meaning.
- `disposition: merge|close|keep_open|claimed_only`, `reason`, `merge_commit`.
  `importable` is true only after a successful merge. A declined merge changes it
  to false and preserves an open review state.

The importer must independently bind both workflow identities/revisions, run
attempts, artifact IDs/digests, source head, folder/manifest/file hashes, exact
problem/target, Lean/axiom policy, and the PR's GitHub merge evidence. It must accept
an API-merged PR for this route (issues still require their issue-state policy).
Open below-record/unverified PRs are Claimed. Closed-unmerged failures stay off
the board. Equal-bound passes create a separate row with their own proof credit.
Never enable a fixture or an unreviewed verifier/publisher revision.
`tests/fixtures/direct/pr-envelope.json` is a synthetic, explicitly non-importable
example; both it and its request carry `test_only: true`. Its raw synthetic receipt
bytes are in `tests/fixtures/direct/pr-receipt.json` so the receipt hash is testable.

## Local validation limits

Python tests cover allowed paths/modes, source-folder staging, manifest injection,
artifact digest/path attacks, run identity, stale heads, protected-code changes,
atomic merge SHA, real failure closure, and incomplete-run labels. Workflow lint
runs on the exact YAML. No Lean runs on the office box. Hosted scheduler/reusable metadata,
GitHub token permissions, merge behavior, and API artifact digests still need an
approved live smoke test. This phase commits locally and performs no public action.

## Early Lean receipt and advisory update (2026-10-11)

The proof runner executes Lean and the axiom audit first. It writes
`verification_stage: lean`, with nanoda `pending/advisory_queued`, and uploads an
immutable proof artifact with the normal name plus `-lean`. It then runs nanoda
on the same read-only runner, preserving the source build. The final immutable
artifact retains its old name and records `verification_stage: final`.

The trusted publisher also starts on `workflow_run: in_progress`. It polls only
API metadata and bounded artifacts, on a separate write-capable runner. It exits
when every selected entry has a Lean checkpoint or the source run finishes.
The selection artifact limits its expected entries. This watcher posts issue
results and merges passing PRs immediately after Lean plus the axiom audit. It
never runs or checks out submitted code. Final completed-run publication reports
the advisory outcome. A real nanoda rejection of an already merged proof emits
`disposition: blocked`, `importable: false`, retains the API merge commit, and
comments/labels for maintainer review. The site must supersede the early passing
status with this block; it must not fall back to the older passing receipt.

Early result files are `direct-submission-N-lean.json` (v1) and
`pr-submission-N-lean.json` (v2), in the publisher’s attempt-specific result
artifact. Both carry publisher run/attempt/revision and `verification_stage`.
Their source verification run can still be in progress. The importer must bind
both workflow identities, the `-lean` source artifact, all proof hashes, and the
explicit pending advisory state. A generic unknown nanoda outcome is not a Lean
checkpoint. Test flags continue to exclude every smoke receipt and row.

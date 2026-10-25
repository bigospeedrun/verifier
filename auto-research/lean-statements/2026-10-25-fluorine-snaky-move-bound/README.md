# Snaky: parameterized infinite-board Maker-move statement

Hypothesis: OpenAI's fixed 21-move policy statement can become the board's
integer move-bound target without weakening legality or restricting Breaker.
Result: proposed `BigOSpeedrun.Snaky.Bound n` in `challenges/other-snaky`.
This package does not prove any positive bound and does not enable submissions.

## Selection and current state

OS randomness selected seed **37**, assigning lean-statements. Three narrow
candidates were checked: Catalan's exponent (already open PR #21), Subset Sum's
exponent (already open PR #12), and Snaky's move bound (selected). These were
not tied candidates. The three prior statement packages were read; matrix
multiplication, Heilbronn and average sensitivity do not duplicate this target.
Base: `084df82196fb1417ad8c466dc83d6b3362e36344`.

One request to chat-knowledge.json supplied the snapshot in `selection.json`:
19 moves, **Claimed**. The existing ptweezy audit independently rebuilt that
result in the inductive `PlaneBlackWinsIn` model. It is credited and reused as
context, not repeated or presented as a proof of this policy target. Open
issues/PRs at selection contained only #12 and #21. The Snaky board feed
(`other-snaky`, not `snaky`) had no posts. Discord's invite was inaccessible
to the web reader; authenticated channel discussion was not inspected.

## Model comparison and vacuity review

The board requires the infinite integer square board, exact Snaky with all
eight orientations, alternating single fresh claims, Maker first, and an
upper bound on Maker's claims including the winning claim. The source model
and new target implement these through `Cell`, `snaky`, `placement`,
`HasSnaky`, global policy freshness, and `LegalRepliesBeforeFinal`.
The policy is quantified before all Breaker sequences. It can depend on the
remaining budget and both ownership sets; it cannot read future replies.

The entire OpenAI theorem conclusion is parameterized, not just HasSnaky:
cardinality and disjointness controls are retained. `verify.py` compares the
whole proposition after substituting 21 -> n and 20 -> n-1. `Model.lean`
retains the original definition block exactly, with four narrower imports
in place of the aggregate `import Mathlib`. The archived template contains
an unproved challenge theorem, so it is data only and never imported.

Potential mistakes and rejected alternatives:

- Restricting replies to 17x17 would strengthen Maker's position and weaken
  the board claim. The target quantifies over all integer pairs.
- Breaker after the final Maker move is a simulation artifact. Requiring
  legality or disjointness against that last reply could impose an extra
  turn. The target keeps all earlier legality conditions and uses Breaker's
  penultimate ownership set for final disjointness. Eight collision/control
  cases exercise this boundary in the finite simulator.
- Counting both players' moves or omitting the winning claim changes the
  ranked quantity. The budget equals the exact number of fresh Maker claims.
- A policy could otherwise repeat an old claim or land on Breaker. Global
  freshness excludes both, even on unreachable states. Finite histories on
  the infinite board always leave a free cell; no finite-board exhaustion
  argument is used to make a reply implication vacuous.
- No empty configuration contains Snaky. `not_bound_zero` is the explicit
  Lean negative control. Finite geometry checks additionally establish six
  distinct cells in each of eight distinct orientations and rule out owning
  a shape after fewer than six claims. The latter is not a Lean lower bound.
- No integer rounding, epsilon slack or asymptotic convention applies.
  The proposed admission domain is natural numbers, denominator one only.

## Reproduce and scope

### Recorded validation

[GitHub Actions run 40166179622, attempt 2](https://github.com/fluorine/verifier/actions/runs/40166179622/attempts/2)
passed on 2026-10-25, checking source commit
`de8628ccaca5afff47eccb0974a6211f6eaa4bf8` on the contributor's own fork.
It compiled the exact committed model, statement and controls with the pinned
Lean/Mathlib versions. Both named control theorems reported exactly
`[propext, Classical.choice, Quot.sound]`. `validation.json` pins the run,
tested source hashes and relevant output. Only documentation and evidence
were added after that successful run; tested Lean/Python files are unchanged.
The separate validation branch owns its temporary workflow; no workflow
change is proposed upstream. The earlier attempts found a cache storage
limit, an incorrect cache path argument, and a doc-comment header before
imports; these were corrected before the successful run.

The offline command also passed from a fresh git archive of the uploaded
source. An intentional change from `(n - 1)` to `n` was rejected by the
challenge integrity check. This is an integrity mutation, not a production
Comparator test of a submitted proof.

From the repository root, with Python 3.10+ and no packages or network:

```sh
python3 auto-research/lean-statements/2026-10-25-fluorine-snaky-move-bound/verify.py
```

Expected output:

```text
PASS: package hashes, source extraction, full target substitution and dependency pin
PASS: 8 orientations, 8 final-reply controls, earlier collisions, duplicate claims and six-cell lower-bound sanity
Finite controls are not a strategy proof or a Comparator receipt.
```

On your own GitHub Actions runner with elan installed, append `--lean`.
It stages a temporary project with Lean 4.34.1, the full verifier dependency
manifest, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Only the four imported modules and their dependency closures are cached.
The initial full-Mathlib cache attempt exhausted runner storage before
compiling the statement; narrower imports preserve every model definition.
It compiles the model, target and `Controls.lean`, checks the zero-bound
refutation, the six-cell count, and a **conditional** baseline adapter.
The adapter proves only that the original 21-move proposition has exactly
the target's type at 21; its hypothesis is not an axiom or a proof of Bound 21.
Lean is never run on the local office machine.

Package hashes cover every other package file; MANIFEST.json excludes itself
to avoid self-reference. Challenge hashes are separate. Package and challenge
files use LF; the existing dependency manifest is compared after LF
normalization so Windows checkout line endings do not alter its identity.

Open obligations: a positive baseline proof; a formal bridge from the existing
inductive theorem to this policy model; full monotonicity/legal continuation;
maintainer model and licensing review; controller/profile/form changes;
Comparator statement-mutation tests and exact allowed-axiom enforcement.
The zero-bound check and finite tests do not discharge these obligations.
No production receipt, improved move bound, novelty, optimality or changed
site evidence level is claimed.

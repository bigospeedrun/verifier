# Snaky Maker-move bound: proposed trusted statement

Board: https://bigospeedrun.com/other/snaky

`BigOSpeedrun.Snaky.Bound n` is a natural-number bound on Maker's own
claims on the infinite square board, including the winning claim. Smaller
values are better. A future controller should admit only nonnegative
integers (reduced rational denominator 1), with no rounding.

The model uses integer pairs, the exact six-cell Snaky and all eight square
symmetries plus arbitrary translations. Maker moves first. Each legal move
claims one fresh cell; Breaker only blocks. One Maker policy is chosen before
the universal Breaker sequence. No restriction to 17x17 or any finite support
is allowed. There is no runtime or arithmetic cost parameter.

`Model.lean` extracts OpenAI's definition block byte for byte from
`lean/ComparatorChallenges/SnakyTwentyOne.lean` at commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a` (Apache-2.0).
The only changes are an attribution header, four narrower Mathlib imports,
omission of the unproved theorem, and closure of the OAI namespace.
Every definition is unchanged. The entire original file is archived unchanged
in the accompanying research package. It contains `sorry` and is never imported.
`Statement.lean` retains the full original theorem conclusion with 21 replaced
by n and its penultimate state 20 replaced by n-1.

The play function records a dummy Breaker claim after the last Maker claim.
That final reply is deliberately unrestricted: Maker's last state cannot
depend on it, and final disjointness uses Breaker's state after n-1 replies.
Legality is required for every earlier reply. At n=0, the target is false.
Global freshness also ensures exactly n distinct Maker claims. Winning earlier
is allowed: on the infinite board the strategy can continue claiming fresh
cells without losing its completed shape until the nominated bound.

Use Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
with all dependencies in the verifier's `profiles/lake-manifest.json`.
The package's `Controls.lean` tests the zero bound and the definitional
21-move adapter. The adapter is conditional and proves no positive bound.

Example future target: `Race.bound : BigOSpeedrun.Snaky.Bound 19`.
No verifier profile, target generator, record gate or direct submission route
is enabled by this contribution. Maintainers must review this model, prove the
bridge from existing inductive game proofs, validate legal continuation, and
run Comparator mutations and the allowed-axiom audit before enabling it.
The existing independent 19-move audit concerns `Snaky.PlaneBlackWinsIn`, a
different representation; no equivalence is assumed here.

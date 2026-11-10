# 3-SAT: trusted statement

`VerifierStatement.lean` defines `BigOSpeedrun.ThreeSat.SolvedInTime (α : ℚ)` for
[the 3-SAT board](https://bigospeedrun.com/3sat). The bound is the exponent `α` in
`(n + m)^O(1) · 2^(n / (log n)^(α − o(1)))`; larger is better. For a reduced
rational `p/q`, the target is:

```lean
theorem Race.bound : BigOSpeedrun.ThreeSat.SolvedInTime ((p : ℚ) / q) := by
  -- Supply the proof.
```

The maintainers wrote this statement (verifier#192 asked for the route). It follows
[docs/new-statements.md](../../docs/new-statements.md). No 3-SAT bound is claimed here.

## Model

The board model: a CNF formula on `n` variables with `m` clauses, each clause an OR of at
most three literals; decide whether some assignment satisfies every clause. Time counts
bit operations, up to `(n + m)^O(1)` factors. The score `α` means: for every fixed
`ε > 0`, time at most `(n + m)^O(1) · 2^(n / (log n)^(α − ε))` for all large `n`.

| Problem page | `VerifierStatement.lean` |
| --- | --- |
| CNF on `n` variables, at most three literals per clause | `F : SAT.CNF (Fin n)` with `SAT.WidthAtMost 3 F` (OpenAI's definitions) |
| Decide whether some assignment satisfies every clause | `answer = true ↔ Satisfiable F`, with `Satisfiable F := ∃ a, SAT.CNF.eval a F = true` |
| Standard encoding of the formula | `Encoding.encodeCNF F` (OpenAI's encoding: `n` in unary, then the sorted clauses) |
| Bit operations, multitape Turing machine | `Computation.PrimitiveMachine`: a deterministic machine with finitely many states and tapes over `Option Bool`; one step reads one tape head and moves or writes on that tape |
| One algorithm for all `n` and `m` | `machine` and `d` come before `ε`, `n` and `F` |
| `(n + m)^O(1)` | `(bits + 1)^d`, `bits = Encoding.formulaBitLength F` |
| `2^(n / (log n)^(α − ε))` for every `ε > 0`, all large `n` | `∀ ε : ℚ, 0 < ε → ∃ K`, bound `K · (bits + 1)^d · 2^(n / (log₂(n + 2))^(α − ε))` for every `n` |
| Halts on every run | `HaltsWith`: a trace of exactly `time` steps to a halting state that holds the verdict |

Decisions a reviewer should check:

- **No hypothesis.** The target assumes nothing. In particular it does not assume the
  Exponential Time Hypothesis (ETH). Both rows at `1/2` on the board refute ETH; a target
  of the form "ETH implies …" would be provable for every `α` from those proofs.
- **Deterministic machines only.** The board also allows randomized algorithms with
  success probability at least `2/3`. A deterministic algorithm qualifies on the board,
  so every proof of this target is a valid claim. A randomized algorithm cannot use this
  route.
- **Encoding size.** `encodeCNF` writes each literal in unary, so `bits` is `O(n + m·n)`.
  Clauses form a `Finset` of `Finset`s: a formula has no repeated clause, so
  `m ≤ (2n + 1)^3` and `bits` is polynomial in `n`. The factor `(bits + 1)^d` therefore is
  `(n + m)^O(1)` in both directions, and it cannot hide an exponential factor.
- **Logarithm.** `log₂(n + 2) ≥ 1` for every `n`, so no case divides by zero or takes a
  power of a number below 1. For large `n` this changes nothing, since
  `log₂(n + 2) / log₂ n → 1`. The constant `K` absorbs small `n`.
- **Time.** `HaltsWith` asks for a trace of `machine.step` of exactly `time` steps that ends
  in the state `Sum.inl answer`. A halted machine has no next step, so `time` is the full
  running time. The verdict is the halting state; no output tape is read.
- **Range.** The controller must accept only reduced rationals `p/q` with `q > 0` and
  `0 ≤ p/q ≤ 100` (the board maximum). `α = 0` is exhaustive search: the bound
  `2^(n · (log₂(n + 2))^ε)` is at least `2^n`. A larger `α` is not known to be false (that
  would separate P from NP), as on every algorithm board. The statement is for attained
  bounds.

## Difference from the upstream comparator target

OpenAI's comparator challenge `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`
(openai/math at `7ef5c0cc`, `lean/ComparatorChallenges/SubexponentialSAT.lean`) states, for
each width `k ≥ 2`, one machine that counts and decides every width-`k` formula within
`C · (bits + 1)^d · 2^(A · n · (ln ln(n + 16))^2 / √ln(n + 16))` steps, with a space bound.
It has a fixed rate and cannot take `α` as a parameter. The adapter reuses only OpenAI's
definitions (lines 1 to 128 of that file), not its runtime definitions or its theorem.
From that theorem with `k = 3`, a proof of this target at `α = 1/2` needs: the trace of
`locatedStep` projected to a trace of `machine.step`, `0 < count F ↔ Satisfiable F`, and the
inequality between the two time bounds.

Anthropic's row uses another machine model (Mathlib's `Turing.FinTM2`) and Lean `v4.33.1`.
This route does not take that model. A refile of that proof needs a simulation between the
two machine models and a port to Lean `v4.34.1`. The maintainers add a second route in that
model only when someone brings an Anthropic refile with a working bridge.

## Submission

Two layouts work:

- Copy `VerifierStatement.lean` byte for byte below `Submission/` (for example as
  `Submission/ThreeSatStatement.lean`), import it, and prove `Race.bound`.
- A proof built on OpenAI's library (where the same definitions live) imports that library
  and copies only the namespace `BigOSpeedrun.ThreeSat` of `Statement.lean`. Comparator
  checks that every definition the target uses is the same as in this statement.

## Toolchain

Lean `leanprover/lean4:v4.34.1` with the Mathlib pin of `profiles/lake-manifest.json`
(Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`), the pin of openai/math at `7ef5c0cc`.

## Provenance and license

`SubexponentialSATDefinitions.lean` is lines 1 to 128 of
`lean/ComparatorChallenges/SubexponentialSAT.lean` of openai/math at
`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, byte for byte (Apache-2.0; hashes in
`provenance.json`). `Statement.lean` is new, written by the Big O Speedrun maintainers with
AI assistance (Claude Opus 5.5 in Claude Code), Apache-2.0. See `NOTICE`.

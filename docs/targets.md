# Fixed targets

The entry point is `Submission.lean`, with theorem `Race.bound`. For a PR,
this file lives in its new submissions folder; for an issue, at the source
repository root. The verifier stages the chosen folder as the project root.
Extra modules must be below `Submission/`; import them with `Submission.Name`.
Copy needed proof sources there and update their import paths. The verifier
supplies pinned Mathlib, Lean, and build files. It does not use submitted Lake
files, fetch submitted dependencies, or run submitted setup scripts.

For 3SUM and APSP, use Lean `leanprover/lean4:v4.33.1` and the Mathlib pin in
`profiles/anthropic-lake-manifest.json`. Copy our unchanged `EndStatement.lean`
into `Submission/EndStatement.lean` in the proof repository. Import it from
`Submission.lean`. Its namespace remains `EndStatement`.

For a bound `p/q`, prove one of these targets:

```lean
import Submission.EndStatement

theorem Race.bound : EndStatement.ThreeSum.SolvedInTime ((p : Rat) / q) := by
  -- Supply the proof.
```

For APSP, replace `ThreeSum` with `APSP`. Replace `p` and `q` with the exact
numerator and positive denominator. The controller builds its target from our
unchanged statement file; it does not trust the submitted statement copy.

For DFT, use Lean `leanprover/lean4:v4.34.1` and the Mathlib pin in
`profiles/lake-manifest.json`. Keep OpenAI's `OAI.PowerSaving.DFTProgram`
definitions unchanged. For saving `p/q`, export:

```lean
open OAI.PowerSaving Filter Asymptotics

theorem Race.bound : ∃ order solve W, DFTProgram order solve W ∧
    (fun n : ℕ => (W n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) * (Real.log (n : ℝ)) ^
        (1 - (p : ℝ) / q)) := by
  -- Supply the proof.
```

The DFT target covers all positive lengths and complex vectors in the exact
scalar/index RAM. Root-order selection, preparation, and polynomial bounds
are included. This is an operation-count model.

The historical `dft233` entry point is retained only for local receipt tests
and the existing manual verifier. The public issue form always uses
`Race.bound`. It accepts no entry-point, dependency, or toolchain override.

For average sensitivity (issue route only), use Lean `leanprover/lean4:v4.33.1` and
the Mathlib pin in `profiles/anthropic-lake-manifest.json`. The trusted statement is
`challenges/average-sensitivity/VerifierStatement.lean`: OpenAI's unchanged
`Model.lean` followed by `Statement.lean`. Keep those definitions unchanged in your
sources (namespaces `OAI.LeanBlast.GotsmanLinial` and `BigOSpeedrun.AverageSensitivity`),
and for a coefficient `p/q` export:

```lean
theorem Race.bound : BigOSpeedrun.AverageSensitivity.Bound ((p : ℚ) / q) := by
  -- Supply the proof.
```

`Bound C` states AS(sign p) ≤ C d √n for every real polynomial p of total degree at
most d in n variables, 1 ≤ d ≤ n, with sign(0) = 1. A smaller C is better.

## Subset Sum

Issue route only. Use Lean `leanprover/lean4:v4.34.1` and the Mathlib pin in
`profiles/lake-manifest.json` (the DFT pin). The trusted statement is
`challenges/subset-sum/Statement.lean`, namespace `BigOSpeedrun.SubsetSum`. Copy it
unchanged into your sources (for example `Submission/Statement.lean`) and, for an
exponent `p/q`, export:

```lean
import Submission.Statement

theorem Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime ((p : Rat) / q) := by
  -- Supply the proof.
```

`SolvedInTime α` states a randomized word-RAM algorithm that runs in time
`O(2^(α n))` on every random outcome, for every polynomial bound on the input bit
length, and is correct with probability at least 2/3. A smaller `α` is better. The
classic Horowitz-Sahni bound `O*(2^(n/2))` is attained as `O(2^(n/2))` under this
statement (a sum fits in one word; merge-built sorted half-sums and a two-pointer scan),
so a proof of 1/2 ties the classical baseline. A proof above 1/2 runs and is listed
while it matches or beats the best Lean Verified bound on the board. Only a
Lean Verified row may be above the classic bound: a Claimed row above 1/2 is not listed. See [the statement README](../challenges/subset-sum/README.md) for the
model.

## Catalan's constant

Issue route only. Use Lean `leanprover/lean4:v4.34.1` and the Mathlib pin in
`profiles/lake-manifest.json` (the DFT pin). The trusted statement is
`challenges/catalan/Statement.lean`, namespace `BigOSpeedrun.Catalan`. For an
exponent bound `p/q`, export:

```lean
theorem Race.bound : BigOSpeedrun.Catalan.Bound ((p : ℚ) / q) := by
  -- Supply the proof.
```

For an integer bound, write `q = 1`, for example `((1091 : ℚ) / 1)`. `Bound r` says
that `r ≥ 0` and that for every real `s > r`, for all large `b` and every integer `a`,
`b^(-s) < |G - a/b|`. A smaller `r` is better. See
[the statement README](../challenges/catalan/README.md) for the quantifiers.

A Catalan proof is large, so it runs as a
[split build](execution.md#split-build-for-large-proofs). Only the final result is
posted. Nanoda can end incomplete (time or memory limit); that does not prevent Lean Verified.

[Convert a proof repository to the Submission layout](convert-layout.md) explains how
to move an existing proof (for example, Sean Litsey's Catalan repository) into the
layout that the verifier reads.

## Snaky

Issue route only. Use Lean `leanprover/lean4:v4.34.1` and the Mathlib pin in
`profiles/lake-manifest.json` (the DFT pin). The trusted statement is
`challenges/other-snaky/VerifierStatement.lean`, namespace `BigOSpeedrun.Snaky`. It
imports only four Mathlib modules. Copy it byte for byte into your sources (for
example `Submission/SnakyStatement.lean`), and for a whole number `n`, export:

```lean
import Submission.SnakyStatement

theorem Race.bound : BigOSpeedrun.Snaky.Bound n := by
  -- Supply the proof.
```

`Bound n` says that one Maker policy wins Snaky on the infinite board `ℤ × ℤ` within
`n` own moves, the winning move included, against every legal Breaker sequence. The
policy must give a fresh cell on every state. A smaller `n` is better. The bound is a
whole number: the form refuses a fraction. Do not change the copied file: Comparator
compares every definition that the theorem uses, and a changed definition (for
example a moved cell of the shape) is a statement mismatch. See
[the statement README](../challenges/other-snaky/README.md) for the rules.

## Heilbronn triangle

Issue route only. Use Lean `leanprover/lean4:v4.34.1` and the Mathlib pin in
`profiles/lake-manifest.json` (the DFT pin). The trusted statement is
`challenges/heilbronn-triangle/VerifierStatement.lean`, namespace
`BigOSpeedrun.HeilbronnTriangle`. It imports `Mathlib`. Copy it byte for byte into
your sources (for example `Submission/HeilbronnStatement.lean`), and for a reduced
saving `p/q` with `0 < p/q ≤ 5/6`, export:

```lean
import Submission.HeilbronnStatement

theorem Race.bound : BigOSpeedrun.HeilbronnTriangle.Bound ((p : ℚ) / q) := by
  -- Supply the proof.
```

`Bound η` says that there are a real `c > 0` and an `N` such that for every
`n ≥ N`, some `n` distinct points in the closed unit square have every triangle
(on three distinct points) of area at least `c n^(-2+η)`. A larger saving is
better. The form refuses `0`: it is the classical bound, already proved. Each
integer of the bound can have up to 300 digits (40 on the other problems), so a
saving such as `1/(100000·K)` with its 237-digit denominator can be filed. The
verifier does not stage `OAI.Geometry.HeilbronnTriangle.Definitions`, so a port of
OpenAI's proof tree must import the copied file. Do not change the copied file:
Comparator compares every definition that the theorem uses, and a changed
definition (for example the area of a triangle) is a statement mismatch. See
[the statement README](../challenges/heilbronn-triangle/README.md).

## Directed shortest paths

Issue route only. Use Lean
`leanprover/lean4:v4.34.1` and the pins in `profiles/lake-manifest.json`. The
trusted statement is `challenges/directed-sssp/VerifierStatement.lean`, namespace
`BigOSpeedrun.DirectedSSSP`. It imports `Frontier.CostModel` from
[bigospeedrun/c-hd-proof](https://github.com/bigospeedrun/c-hd-proof) (directory
`formal/lean`) at the commit pinned in `profiles/direct.json`. The verifier stages
that fork's `Frontier` modules for every run, so your sources can import any of
them (for example `Frontier.CHD.Final`), but must not contain a `Frontier` root.
Copy the statement byte for byte into your sources (for example
`Submission/SsspStatement.lean`), and for the exponents of your row export:

```lean
import Submission.SsspStatement

theorem Race.bound : BigOSpeedrun.DirectedSSSP.Bound ((a : ℚ) / 1) ((b₁ : ℚ) / b₂) ... := by
  -- Supply the proof.
```

The verifier writes five reduced rationals `((p : ℚ) / q)`, in the order `a`, `b`,
`a'`, `b'`, `c'` (with `/ 1` for an integer). A row says "with at most D(n)
edges, the time is O(T(n))", with `D(n) = n^a·⌊⌊log₂ n⌋^b⌋` and
`T(n) = n^a'·(ln n)^b'·(ln ln n)^c'`. The Bound field of the form is `D ; T` in
one normal form, for example `n log^3/4 ; n log^11/12`; see
[the statement README](../challenges/directed-sssp/README.md) for the grammar and
the ranges.

Comparison. For these functions, `f = O(g)` exactly when the exponent tuple of
`f` is at most that of `g` in lexicographic order. `D` is compared by `(a, b)`
and `T` by `(a', b', c')`. The statement's `Validation.lean` proves the two facts
that the gate uses (`weaker_time`, `cover_sparser`).

`T` must be below `n·D`: the second clause of `Bound` already gives
`C·(n+1)(m+1)` for every graph, so a row with `T ≥ n·D` adds nothing, and the
form refuses it (verifier #134).

Gate. A submission runs when its `T` is strictly below the best Lean Verified
`T` at its `D`: the best `T` of the Lean Verified rows whose `D` is at least as
dense, and, at or below n log^(3/4) n, the time of Vals AI's proven line at that
`D`. So at or below n log^(3/4) n, a new row must beat Vals AI's proven line at its
density. That row's Lean theorem bounds the time by
`Tchd = n + m + m·log(2 + m/n) + m^(1/3)·(n log n)^(2/3)` (up to constant factors)
for every `m` up to that cap; the line is a chart line of the Vals AI row
(`chart.lines` in the site's board data). A tie starts no run. With no Lean
Verified bound at `D`, every bound of the form runs. Claimed rows, the paper rows
(functions of `m` and `n`) and the classical bound never gate (Nil rulings
2026-10-20 and 2026-11-02).

The classical bound, Dijkstra with Fibonacci heaps, is `O(m + n log n)`, that is
`T_classic(D) = max(D, n log n)`. It is a line on the board only.

SSSP runs use about 14 GB of the 15 GB runner memory; import only the fork modules
your proof needs. A run that hits the memory limit ends incomplete; it is not a verdict on the proof.

## Bounded prime gaps

Issue route only (opened 2026-11-07). It runs as a split build (two jobs). Use
Lean `leanprover/lean4:v4.33.1` and the Mathlib pin in `profiles/anthropic-lake-manifest.json`.
The trusted statement is `challenges/prime-gaps/Statement.lean`, namespace
`BigOSpeedrun.PrimeGaps`. It imports three Mathlib modules. Copy it byte for byte into your
sources (for example `Submission/PrimeGapsStatement.lean`), and for a whole number `B`, export:

```lean
import Submission.PrimeGapsStatement

theorem Race.bound : BigOSpeedrun.PrimeGaps.Bound B := by
  -- Supply the proof.
```

`Bound B` says that infinitely often two consecutive primes differ by at most `B`
(`H₁ ≤ B`). A smaller `B` is better; the form refuses a fraction. See
[the statement README](../challenges/prime-gaps/README.md).

The verifier stages two pinned libraries for every run, so your sources can import them but
must not contain their roots: PrimeNumberTheoremAnd (the kimihiro64 fork at
`0f15a38c619298b5cd786d39a84dd4bb8997324c`, root `PrimeNumberTheoremAnd`) and LeanArchitect
(`d9013cc08bd2b5483e837368dfa4cc7ead92a5c2`, root `Architect`), as in
kimihiro64/bombieri-vinogradov. Put every other library you use (for example Axiom Math's
PrimeGapsLib or the Bombieri-Vinogradov theorem) under `Submission/`, with imports renamed to
`Submission.*`. Your modules build with `autoImplicit = false` and
`maxSynthPendingDepth = 3` (Axiom Math's PrimeGapsLib options). A `.json` file inside
`Submission/` is staged as data (at most 1 MB each; Axiom Math's certificate is one); no other
file type is staged.

## 3-SAT

Not open yet: the maintainer smoke on the check chain runs first (task 07840cc3, verifier #192).
Issue route only. It runs on the check chain (`runner` `github-chain`: up to four build jobs,
then the kernel check in up to five segments). Use Lean `leanprover/lean4:v4.34.1` and the
Mathlib pin in `profiles/lake-manifest.json`. The trusted statement is
`challenges/3sat/Statement.lean`, namespace `BigOSpeedrun.ThreeSat`. Its definitions of the
formula, the encoding and the machine are OpenAI's (openai/math at `7ef5c0cc`,
`lean/ComparatorChallenges/SubexponentialSAT.lean`, lines 1 to 128). Copy the statement into
your sources (for example `Submission/ThreeSatStatement.lean`), and for a reduced rational
`p/q`, export:

```lean
import Submission.ThreeSatStatement

theorem Race.bound : BigOSpeedrun.ThreeSat.SolvedInTime ((p : ℚ) / q) := by
  -- Supply the proof.
```

`SolvedInTime α` says that one deterministic machine decides 3-SAT within
`K · (bits + 1)^d · 2^(n / (log₂(n + 2))^(α − ε))` steps for every `ε > 0`. A larger `α` is
better (0 to 100). See [the statement README](../challenges/3sat/README.md).

The sources have two roots, `OAI` and `Submission`. Put OpenAI's modules under `OAI/`, unchanged
(their module names start with `OAI.`), and your own modules under `Submission/`. Your copy of
the statement then imports the OpenAI modules that define these names
(`OAI.Algorithms.SubexponentialSAT.BinaryArithmetic`, `.SAT`, `.Encoding` and `.Computation`)
instead of `SubexponentialSATDefinitions`, since two modules cannot define the same name. The
check compares every definition that the statement uses with the challenge.

## Integer factoring

Closed to issues and PRs. A maintainer can rerun Isaac Rudich and Louis-Martin
Rousseau's proof of score 0 (time `N^o(1)`) against their unchanged statement in
`challenges/integer-factoring/Challenge.lean`, with Lean `leanprover/lean4:v4.35.0`.
See [the statement README](../challenges/integer-factoring/README.md).

A maintainer can also rerun 1337isnot1337's claimed proof of score 1/2 (time
`2^O(n/√log n)`, their `Factoring.SqrtLogLogConjecture`) against the same statement with
one appended theorem, in `challenges/integer-factoring-sqrtlog/Challenge.lean`, with Lean
`leanprover/lean4:v4.33.1`. See [its README](../challenges/integer-factoring-sqrtlog/README.md).
There is no `Race.bound` target for other scores yet.

## Zeta zeros on the critical line

Closed to issues and PRs. A maintainer can rerun Anthropic's proof of
`κ* ≥ 3/2 − cot(1/√2)/√2` (their theorem
`montgomery_taylor_simple_on_critical_line_mult_cumulative`, from anthropics/formal-math
`zeta23`) against their unchanged statement in `challenges/critical-line-zeros/Challenge.lean`,
with Lean `leanprover/lean4:v4.33.0-rc2`. See
[the statement README](../challenges/critical-line-zeros/README.md). There is no `Race.bound`
target yet.

## Van der Waerden numbers

Closed to issues and PRs. A maintainer can rerun OpenAI's proof of
`W_r(k) > k^{k ⌊log₂ r⌋/100000}` (their theorem `OAI.QuantitativeVanDerWaerden.uniform_lower_bound`, from
openai/math `lean/OAI/Combinatorics/ProgressionColoring`) against their unchanged statement in
`challenges/van-der-waerden/Challenge.lean`, with Lean `leanprover/lean4:v4.34.1`. See
[the statement README](../challenges/van-der-waerden/README.md). There is no `Race.bound` target yet.

Integer multiplication has no trusted statement in this gate.

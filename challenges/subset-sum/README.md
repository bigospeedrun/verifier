# Subset Sum: time exponent α in O(2^(α·n))

Problem page: https://bigospeedrun.com/subset-sum

This is a NEW trusted statement (no upstream source), authored by MultiAgency
(`darkhipo`), Apache-2.0, contributed under this repository's license. The
machine model is modeled on `challenges/3sum-apsp/EndStatement.lean`
(Anthropic PBC, Apache-2.0): the deterministic instruction set is copied
verbatim; one instruction (`rand`) is added to express the page's randomized
programs.

## The claim shape

`SubsetSumStatement.SubsetSum.SolvedInTime (α : Rat)` asserts: there is ONE
uniform program `P` and a step bound `T : Nat → Nat` with `T(n) = O(2^(α·n))`
(`BigOExp`) such that for every fixed `c`, every `n ≥ 2` and every instance
`x` with maximum input/target bit length `b ≤ n^c`, running `P` on `x` at the
page's word width `w = ⌈4(n + b + log₂(n+2))⌉`:

- halts within `T(n)` steps on EVERY random outcome (the time bound is
  worst-case over the random tape, as the page requires), and
- outputs the correct verdict with probability ≥ 2/3 over the uniform random
  tape.

A deterministic program (one containing no `rand`) reads no tape, so its
correctness probability is 1 and the classical Horowitz–Sahni bound
`O*(2^(n/2))` is covered by any attained `α > 1/2`.

Parameter: `α` is the time exponent, range `0 ≤ α ≤ 1`, SMALLER is better.
`Race.bound` asserts `SolvedInTime` at the submitted exact rational.

## The model

- `Instr`: `one`, `add`, `sub`, `mul`, `load`, `store`, `bltz`, `accept`,
  `reject` — byte-identical semantics to `EndStatement.Instr` — plus
  `rand i` (`[i] := ρ r`, drawing the `r`-th independent uniform word, `r`
  being the number of steps executed so far).
- Cost: one instruction = one operation; `exec` counts steps, so every
  executed instruction (including `rand`, comparison-via-`bltz`, indirect
  `load`/`store`) costs 1.
- Randomness: the tape `ρ : Nat → BitVec W` supplies independent uniform
  `W`-bit words. A `t`-step run reads at most the first `t` tape words, so
  the probability is the counting measure on `Fin t → BitVec W` (all
  `2^(W·t)` prefixes equally likely; `Finset.univ.filter ... |>.card` over
  that type). No measure theory is needed.
- Initial memory: `n` in cell 0, the input words after it, 0 elsewhere
  (`loadWords`, as in `EndStatement`).
- Inputs: positive integers `a₁ … aₙ`, nonnegative target `t` (a subtype).
  `yes`: `∃ mask : Finset (Fin n), ∑ i ∈ mask, a i = t` — repeats among the
  `aᵢ` and the empty subset are allowed, positions are used at most once.

## Deviations from the page (for review)

1. **Omitted operations.** The page also lists division, remainder, bitwise
   operations and shifts as costed operations. This statement omits them, as
   the trusted 3SUM/APSP statement does. The omission is a WEAKENING of the
   machine (programs may simulate those operations from `add`/`sub`/`mul`/
   `bltz` at higher cost), so any bound proved here is also a bound in the
   page's model.
2. **Word width.** The page writes `w = ⌈4(n + b + log₂(n+2))⌉`. `wordWidth`
   uses floor-`log₂` (`Nat.log2`) and natural-number arithmetic, under which
   the argument of the ceiling is already an integer. For `n ≥ 2` the two
   readings differ by at most a constant that `BigOExp` absorbs.
3. **`n ≥ 2`.** The page introduces `b` for `n ≥ 2`; the master quantifier
   requires `2 ≤ n` (as `BigOExp` does).
4. **`c`-independence.** The page requires that the program does not depend
   on `c`; accordingly `P` and `T` are chosen OUTSIDE the `∀ c` (unlike the
   3SUM/APSP statement's `∀ κ, ∃ P` shape).

## Build

Lean `leanprover/lean4:v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` — identical to the pin in
`profiles/anthropic-lake-manifest.json`. `Statement.lean` imports only
Mathlib and proves nothing.

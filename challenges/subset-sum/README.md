# Subset Sum: proposed trusted statement

`Statement.lean` defines `BigOSpeedrun.SubsetSum.SolvedInTime (α : Rat)` for
[the Subset Sum board](https://bigospeedrun.com/subset-sum). The bound is the
exponent `α` in `O(2^(α n))`; smaller is better. For a reduced rational `p/q`,
the target is:

```lean
import Submission.Statement

theorem Race.bound : BigOSpeedrun.SubsetSum.SolvedInTime ((p : Rat) / q) := by
  -- Supply the proof.
```

Public submissions for this problem are not enabled. This is a proposal for
maintainer review, as [docs/new-statements.md](../../docs/new-statements.md)
describes. No Subset Sum bound is claimed.

## Model

The model is Section 1.1 of «Subset Sum in Time O(2^0.49n)» (OpenAI,
4 October 2026,
[subset-sum.pdf](https://github.com/openai/math/blob/main/preprints/Subset-Sum-in-Time-2-power-0-49n-October-4-2026/subset-sum.pdf)),
which the problem page states. The file imports nothing and proves nothing,
in the style of the trusted 3SUM and APSP statement.

| Problem page | `Statement.lean` |
| --- | --- |
| Positive integers `a₁..aₙ`, target `t ≥ 0`, `n ≥ 2`; repeats and the empty subset allowed | `Instance n` with `pos`; `2 ≤ n` in `SolvedInTime`; `Instance.yes` ranges over all `S : Fin n → Bool` |
| `b` = maximum bit length of the inputs and target, at least 1 | `Instance.bits = ⌊log₂ max{t, aᵢ}⌋ + 1` |
| `w = ⌈4(n + b + log₂(n + 2))⌉` | `wordLength n b = 4(n + b) + ⌊log₂((n + 2)⁴ − 1)⌋ + 1` |
| Reads, writes, indirect addressing, comparison, `+ − × / %`, bitwise operations, shifts: one operation each | One `Instr` each; one step each in `exec` |
| Independent uniform `w`-bit random word: one operation; one-way randomness | `rand` reads the next word of `ρ` once and costs one step |
| One finite program for all `n`, `b`; no advice or tables; all preprocessing and input access charged | `P : List Instr` before every quantifier; memory holds only the input; every step counted |
| Halts on every run; correct with probability at least 2/3 on each input | `Correct`: a horizon `t`, every run halts within `t`, and at least `2/3` of the `2^(w t)` equally likely random prefixes give the right verdict |
| For every fixed `c` and `b ≤ n^c`, every random outcome costs `O(2^(α n))`; the program does not depend on `c` | `∀ c, ∃ T, BigO T α ∧ ∀ x, bits ≤ n^c → ∀ ρ, halts within T n`; `P` is chosen before `c` |

Decisions a reviewer should check:

- **Ceilings.** For `M ≥ 2`, `⌈log₂ M⌉ = ⌊log₂(M − 1)⌋ + 1`, and for `m ≥ 1`,
  `⌈log₂(1 + m)⌉ = ⌊log₂ m⌋ + 1`. The package's `verify.py` checks both
  identities with exact integer arithmetic on a range of values.
- **Words.** Words are unsigned `BitVec w`. Addition, subtraction and
  multiplication wrap modulo `2^w`; division by zero gives 0; remainder by
  zero gives the dividend; a shift by `w` or more bits gives 0. The paper
  allows an operation a constant number of `w`-bit outputs and charges
  multiword arithmetic per word; the high word of a sum or product takes a
  constant number of these instructions, so operation counts agree up to a
  constant factor.
- **Comparison.** Only `blt` (unsigned less-than branch) is provided.
  Equality and the other comparisons take two `blt` instructions.
- **Input memory.** The paper puts the input in read-only memory. Here the
  input is in ordinary memory, which the program may overwrite; this does not
  change what a program can compute or its cost.
- **Horizon.** `Correct` asks for one horizon `t` per input within which
  every run halts. A program that halts on every execution has such a horizon
  by König's lemma, since each random word has finitely many values. Within
  `t` steps a run reads at most `t` random words, so counting the
  `2^(w t)` prefixes of length `t` gives the exact probability.
- **Thresholds.** The paper's `N_c` are absorbed by the constant `K` of
  `BigO`: for each `n` only finitely many inputs have `b ≤ n^c`, and each
  halts within some horizon, so `T n` can be chosen for the finitely many
  `n < N_c`.
- **Direct addresses.** Instruction operands are natural numbers. A finite
  program names finitely many cells; it does not depend on `n` or `b`.
- **Range.** The controller must accept only reduced rationals `p/q` with
  `q > 0` and `0 ≤ p/q ≤ 1`. A negative `p` makes `α.num.toNat = 0`, and
  `q = 0` normalizes to `0`; both turn the claim into `O(1)`, which no
  program can meet, but the gate should reject them rather than rely on
  that. The classic
  `O*(2^(n/2))` of Horowitz and Sahni has a polynomial factor and is a
  strict frontier, not an attained value of this statement; the first
  attained values below `1/2` are the paper's `0.49` and the current
  claim's `0.4877`. The statement is for attained bounds.

## Toolchain

Lean `leanprover/lean4:v4.33.1`. The statement imports nothing. A submission
may use the Mathlib pin of the existing 3SUM and APSP profile,
`profiles/anthropic-lake-manifest.json` (Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`), or no dependency at all.

## Provenance and license

New statement, written for this proposal by fringewidth with AI assistance
(Claude Fable 5.1 in Claude Code), Apache-2.0. The instruction set and
execution function follow the shape of Anthropic's `EndStatement.lean`
(Apache-2.0, unchanged in `challenges/3sum-apsp/`). The quoted model text is
from the OpenAI paper named above. Credits are in `NOTICE.md` of the
research package under `auto-research/lean-statements/`.

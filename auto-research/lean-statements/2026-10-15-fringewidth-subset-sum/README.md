# Subset Sum: trusted statement for the randomized word RAM

**Status:** proposed statement. No Subset Sum bound is claimed.

**Hypothesis:** the Subset Sum board model (Section 1.1 of OpenAI's «Subset
Sum in Time O(2^0.49n)») can be written as one self-contained Lean file with
the exponent as a parameter, in the style of the trusted 3SUM and APSP
statement, with no imports and no placeholders.

**Result:** `challenges/subset-sum/Statement.lean` defines
`BigOSpeedrun.SubsetSum.SolvedInTime (α : Rat)`: one finite program of a
randomized word RAM with the paper's word length, correct with probability
at least 2/3 and halting on every run for every input with `n ≥ 2`, and for
every fixed `c` a bound `O(2^(α n))` on every random outcome for inputs with
`b ≤ n^c`. `challenges/subset-sum/README.md` compares it clause by clause with
the problem page and lists every modeling decision.

## Validation result

Lean 4.33.1 compiled the statement and `code/Checks.lean` on the
contributor's machine with no errors or warnings. The checks establish:

- exact rational substitution: `49/100` and `4877/10000` give the expected
  numerator and denominator, and `BigO T (49/100)` unfolds to
  `∃ K, ∀ n ≥ 2, T n ^ 100 ≤ K * 2 ^ (49 n)`;
- a hypothesis at `49/100` is rejected by the elaborator as a proof at `1/2`
  or at `4877/10000`;
- `SolvedInTime.mono`: a smaller exponent implies every larger one, for all
  rationals, proved from the integer form of `BigO`;
- `accept_correct`: the program `[accept]` satisfies `Correct` on the
  instance `n = 2, a = (1, 1), t = 0`, which the empty subset solves;
- `reject_not_correct`: the program `[reject]` does not satisfy `Correct`
  on that instance, for any horizon;
- executable checks of the semantics with 4-bit and 8-bit words: a program
  that tests `a₁ + a₂ = t` accepts, rejects, runs out of fuel, and wraps
  modulo `2^w` as expected; a program that reads one random word accepts on
  exactly 8 of the 16 possible first words, and reads the second word from
  the second base-`2^w` digit; `wordLength` and `bits` give the hand-computed
  values.

All six audited declarations depend only on `propext`, `Classical.choice`
and `Quot.sound`. `evidence/lean-checks.txt` is the output.

## Reproduce

From the repository root:

```sh
python3 auto-research/lean-statements/2026-10-15-fringewidth-subset-sum/verify.py
```

Expected output:

```text
PASS: package manifest, challenge hashes, unchanged 3SUM/APSP statement and profile pins, ceiling identities
```

With Lean `leanprover/lean4:v4.33.1` on `PATH` (or `elan`), add `--lean`.
This compiles the statement and the checks with warnings as errors in a
temporary directory, and compares every `#eval` and `#print axioms` line
with the expected output. The final lines are:

```text
PASS: Lean statement, rational substitution, wrong-bound elaboration check, monotonicity, correct and incorrect program, executable semantics, allowed axioms
SCOPE: statement validation only; no production Comparator receipt and no Subset Sum bound
```

The script runs Lean only in a fresh temporary directory on the two files;
it uses no submission build hooks and no network.

## Model comparison and vacuity review

The table in `challenges/subset-sum/README.md` maps each clause of the problem
page to the Lean definition. The statement avoids these weak forms:

- choosing the program after the input, after `c`, or after the random words
  (`P` is the outermost existential);
- counting correctness over a chosen subset of outcomes (the count runs
  over all `2^(w t)` equally likely prefixes);
- a time bound that only holds with probability (`∀ ρ` inside the bound);
- a word length or bit length that differs from the paper by rounding (both
  ceilings are exact integer identities, checked by `verify.py`);
- an instance set without the positivity, `n ≥ 2` and empty-subset rules.

What the checks do not establish: that the known algorithms satisfy the
statement. A proof of the Horowitz–Sahni fallback at any `α > 1/2`, or of
the paper's `0.49`, is a proof submission, not part of a statement package.
A finite check is not an asymptotic proof.

## Selection and current state

OS randomness gave seed **18**, which assigns the lean-statements track.
Three candidates and their decisions are in `data/inputs.json`. The site's
chat-knowledge.json (updated 2026-10-15T11:17:52Z, `data/subset-sum-record.json`)
lists one Claimed row at `4877/10000` and no Human Verified or Lean Verified
row. There were no earlier packages in this track at base commit
`51489ee2ac82596a41375e92ea8108814f931242`; the open PRs were the DFT proof
#10 and the matrix statement #11 from this account; no issue or PR concerned
Subset Sum. OpenAI's repository has no Comparator challenge for the time
result; its `LowSpaceSubsetSum` development is the separate low-space result
with a different word width. Discord was not accessed.

## Scope and remaining work

This adds a reviewable target and its checks. Maintainers need to review the
modeling decisions listed in the challenge README (wraparound words, `blt`
only, writable input memory, the uniform horizon, absorbed thresholds), add
the profile, target generator, form option and record gate, and run their
Comparator mutation tests. Nothing outside the two new folders changes.

`MANIFEST.json` hashes every other package file and excludes itself.
`data/challenge-hashes.json` hashes the two new challenge files and pins the
unchanged 3SUM/APSP statement and profile files that the toolchain note
refers to. No package code runs in the production verifier.

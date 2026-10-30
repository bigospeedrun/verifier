# Integer factoring: one machine in time 2^O(n / √log n)

This is the statement of the [Integer Factoring board](https://bigospeedrun.com/integer-factoring)
at score 1/2. `Challenge.lean` is Rudich and Rousseau's `Challenge.lean` from
[IsaacRudich/SubexponentialDeterministicFactoring](https://github.com/IsaacRudich/SubexponentialDeterministicFactoring)
commit `c91cc3f4947caca8977e81a5d14244f73b5ae2b1`, byte for byte (the same file as
[../integer-factoring](../integer-factoring/README.md)), with one theorem added at the end:

```lean
theorem IntegerFactoring.HalfAppendix.sqrtLogLog_factoring : Factoring.SqrtLogLogConjecture := by
  sorry
```

`Factoring.SqrtLogLogConjecture` is their definition, unchanged:

```lean
def SqrtLogLogConjecture : Prop :=
  ∃ C : ℕ, FactoringInTime (fun n => C * 2 ^ (C * n / (Nat.sqrt (Nat.log 2 n) + 1)))
```

One Mathlib `TM2ComputableInTime encodeNat encodeNat Nat.minFac` machine, with every stack
alphabet finite, outputs the smallest prime factor of every `N` in binary within
`C · 2^(C·n / (⌊√⌊log₂ n⌋⌋ + 1))` steps on inputs of `n` bits. That is time
`2^(n / (log n)^(1/2 − o(1)))`, score 1/2 on the board. The machine model is the same as in
[../integer-factoring](../integer-factoring/README.md).

The added theorem has the name of the claimed proof, in
[1337isnot1337/integer-factoring](https://github.com/1337isnot1337/integer-factoring)
`formal-appendix/HalfTheorem.lean`, so that the claimed commit can be checked as it is.
Only this theorem is a target. `Factoring.subexponentialRate` keeps its `sorry` here and is
not a target. See [provenance.json](provenance.json) for the Git blob and SHA-256 values.

## Run

This profile is closed to issues and PRs. Only a maintainer can run it, with the
`Verify a Lean proof` workflow on GitHub Actions:

- `repo_url`: `https://github.com/1337isnot1337/integer-factoring`
- `commit`: `e91442d3162cae7f775e008efb2ea998c4478344`
- `challenge_file`: `challenges/integer-factoring-sqrtlog/Challenge.lean`
- `theorem_names`: `IntegerFactoring.HalfAppendix.sqrtLogLog_factoring`
- `lean_toolchain`: `leanprover/lean4:v4.33.1`

The run builds the import closure of `HalfTheorem` (574 modules) from four pinned sources. It
does not use their Lake files, scripts or compiled objects:

- the submission, folder `formal-appendix` (91 modules), and the same commit's folder `formal`
  (`HalfPad`, `HalfPrefix`);
- Rudich and Rousseau at `c91cc3f4`: `Challenge`, the statement module that the proof imports,
  and `FactoringAux`;
- [anthropics/formal-math](https://github.com/anthropics/formal-math) at
  `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, six folders of `eth/proof` (404 modules), with the
  Lean options of their lakefile: `autoImplicit = false`, `relaxedAutoImplicit = false`,
  `exponentiation.threshold = 2048` and `pp.unicode.fun = true`.

The other sources use Lean's default options, as their own builds do (`auto_implicit`). The
options change only how the sources elaborate. Comparator still compares the elaborated
statement with this challenge.

Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` are the pins of
anthropics/formal-math `eth`: [profiles/anthropic-lake-manifest.json](../../profiles/anthropic-lake-manifest.json)
has the same package revisions. The tools are in
[profiles/anthropic-tools.json](../../profiles/anthropic-tools.json), as for the other v4.33.1 profiles.

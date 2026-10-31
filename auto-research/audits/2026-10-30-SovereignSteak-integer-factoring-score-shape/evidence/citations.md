# Cited lines

All quotations are from
`IsaacRudich/SubexponentialDeterministicFactoring` commit
`c91cc3f4947caca8977e81a5d14244f73b5ae2b1` (Apache-2.0), except the
verifier copy of `Challenge.lean`, which that repository's
`provenance.json` records as byte-identical. Hashes are in
`../data/source-pins.json`.

`FactoringAux/UniParams.lean` defines the level count. `K0u` is 48.
`Kb` itself is in `FactoringAux/EngineGroup.lean`:

```lean
def Kb (K0 : ℕ) : ℕ → ℕ
  | 0 => K0
  | d + 1 => (3 * Kb K0 d ^ 8) * (3 * Kb K0 d ^ 8)

def Gs (K0 d : ℕ) : ℕ := 3 * Kb K0 d ^ 8
```

`Kb_succ` rewrites the step as `9 * Kb K0 d ^ 16`. `ellOf n` is the
largest `ℓ ≤ n` reached with `Kb 48 ℓ ^ 40 ≤ n`.

`FactoringAux/EngineRate.lean` states the sharp one-step inequality.
The file header calls the decay "about `11/12` per level":

```lean
theorem N_next (K G lam : ℕ) (hGK : K ≤ G) :
    12 * K * (K ^ 2 * Lnext K G lam) ≤ (11 * K + 24) * (G ^ 4 * lam) + 24 * K * G ^ 4
```

`FactoringAux/EngineCostRate.lean` stores a looser step, for `K ≥ 48`:

```lean
theorem N_step (K G lam : ℕ) (hK : 48 ≤ K) (hGK : K ≤ G) :
    24 * (K ^ 2 * Lnext K G lam) ≤ 23 * (G * G * (G * G) * lam) + 48 * (G * G * (G * G))
```

The same file proves `(2 ^ sOf n) ^ 4 ≤ 4 * n + 4` for every `n`
(`S_le_n`). `FactoringAux/EngineCostFinal.lean` defines the widths the
chain actually carries:

```lean
def Ntn (K0 ℓ n : ℕ) : ℕ := 720 * (2 ^ sOf n) ^ 4 + 306 * (Gs K0 ℓ * (2 ^ sOf n) ^ 3)
def W0n (K0 ℓ n : ℕ) : ℕ := 23 ^ ℓ * Ntn K0 ℓ n / 24 ^ ℓ + 1 + 2 * ℓ * Gm4 K0 ℓ
```

`FactoringAux/UniExp.lean` turns those widths into an `o(n)` exponent
only past an explicit level cutoff. `ev_W` takes the witness
`45451759374148`. `small_zC` sets `D = 80696 * k` and calls
`ev_W0 (2 * k * 24 ^ D)`. On the branch `d + 1 ≤ D` it extends the
decay exponent from `d` up to `D`:

```lean
have hND : N ≤ 24 ^ D * W0n K0u ℓ n := by
```

The chain lemma it calls, `chainMax_le` in
`FactoringAux/UniExpChain.lean`, assumes the tight relation
`23 ^ (d + 1) * N ≤ 24 ^ (d + 1) * W0` at the real depth `d`.

`FactoringAux/EngineCostMain.lean`:

```lean
theorem mainE_cost_le {K0 ℓ n k : ℕ} (hK : 2 ≤ K0) (R : MainReq V K0 ℓ n) (hkn : k < n) (hA : ∀ a j, A a j ≤ 1) :
    cost (envNK n k) A (mainE K0 ℓ) ≤ (64 * (V + 1) ^ 3) ^ (24 * ℓ + 84) := by
```

`FactoringAux/UniMain.lean` sets `V = 2 ^ (16 * Z n + 127)` and concludes
`Aux.subexponentialRate`. `FactoringAux/UniFinal.lean` says how that
cost becomes a machine time: `S n = 200 (n + 1) ^ 3 (B n + 1)`,
`T n = Q (n + k₀ + S n + 1) ^ 2`, and `M.time n ≤ c (T n + n + 1) ^ 3`.
`uni_time_le` packages this as "an engine bound at `24k` gives a machine
bound at `k`".

The statement under audit, from `Challenge.lean`:

```lean
theorem subexponentialRate :
    ∃ M : FactoringMachine, ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ,
      FactorsWithin M (fun n => C * 2 ^ (n / k)) := by
  sorry

def SqrtLogLogConjecture : Prop :=
  ∃ C : ℕ, FactoringInTime (fun n => C * 2 ^ (C * n / (Nat.sqrt (Nat.log 2 n) + 1)))
```

`Solution.lean` proves `subexponentialRate` by `Aux.subexponentialRate`
and leaves `SqrtLogLogConjecture` as the same proposition.

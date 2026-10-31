# Audit: the integer-factoring theorem is score 0

`Factoring.subexponentialRate` is the score-0 statement on the integer-factoring board, and the proof's own level cutoff is what keeps it there. A faster exponent is visible in the width formulas, and it is conditional on using those formulas at the level count the machine actually reaches. This package does not prove that reading and does not claim a new bound.

Hypothesis: the proved machine already has board score `α > 0`. It does not. The checked arithmetic is in `verify.py`.

The record under audit is Isaac Rudich and Louis-Martin Rousseau, `IsaacRudich/SubexponentialDeterministicFactoring` commit `c91cc3f4947caca8977e81a5d14244f73b5ae2b1`, Claimed, score 0. The verifier pins that statement in `challenges/integer-factoring/` at base commit `30d083a9e07f737fc890a49e03bd55348a33ce09`. Quoted lines and file hashes are in `evidence/citations.md` and `data/source-pins.json`.

## How the board scores a factoring time

The input length is `n` bits, with `N = 2^n` up to the usual encoding. Time `2^{(c+ε) n}` for every `ε > 0` and all large `n` scores `-c`. Time `2^{ε n}` for every `ε > 0` scores `0`. Time `2^{n / (log n)^{α-ε}}` for every `ε > 0` scores `α > 0`. A constant factor in front of the exponential, and a `b^{O(1)}` gap between a multitape Turing machine and a word RAM, disappear into `ε`. The base of `log` disappears the same way.

## Finding A. The proved statement is score 0

The theorem is one machine such that for every `k ≥ 1` there is a constant `C_k` with time at most `C_k · 2^{n/k}`. For every `ε > 0` the choice `k > 1/ε` gives time `2^{ε n}` for all large `n`, after `C_k` is absorbed. That is score 0. One fixed `k` is the negative score `-1/k`: it misses every smaller `ε`, and `(log n)^α` eventually exceeds that fixed `k`, so it also misses every positive score.

The proof reaches `∀k` by cutting the input range in two (`small_bound` in `FactoringAux/UniExp.lean`). Below `n < Kb(X)^40` the value of the exponent is summed into a finite constant. At and above that point it uses `k · f(ℓ, n) ≤ n`. For the chain exponent, `small_zC` builds that `X` from two gates:

- `ev_W` is stated only for `ℓ ≥ 45451759374148`. It is where `Wn ≤ 2882 n` is proved.
- `D` is set to `80696 · k`, with `80696 = 2 · 14 · 2882`, and `ev_W0` is called at `2 · k · 24^D`. The inequality that call needs is `(24/23)^ℓ ≥ 4 · 2882 · k · 24^{80696 k}`. At `k = 1` this is `ℓ ≥ 6026032`. The linear coefficient is `80696 · ln 24 / ln(24/23) ≈ 6.0258 · 10^6`, and the script checks that the full demand stays above `6 · 10^6 · k` for `k` in `{1, 2, 5, 20}`.

`ellOf(n)` only grows like `log log n`. The group recurrence is `Kb(0) = 48` and `Kb(d+1) = 9 · Kb(d)^16`, and `ellOf(n)` is the largest `ℓ` with `Kb(ℓ)^40 ≤ n`. So `16^ℓ` is on the order of `log n`, and `ℓ` is on the order of `log log n`. An `Ω(k)` demand for levels supplies `k = O(log log n)` at best, and `(log n)^ε = 16^{Θ(ε ℓ)}` grows exponentially in `ℓ` while that budget is linear in `ℓ`. The script checks the optimistic budget `k ≤ ℓ / 6026032` against `(log n)^ε` on every bucket with `ℓ ≤ 11`, and checks that past the analytic minimum the gap keeps widening. That budget ignores the absolute `ev_W` floor, so it is larger than anything `small_zC` actually supplies.

This is a gap in a sufficient condition. It is not a lower bound on the algorithm. `chainMax_le` already assumes the tight relation `23^{d+1} N ≤ 24^{d+1} W0` at the real depth `d`. The low branch of `small_zC` replaces that depth by `D = 80696 k` and uses `N ≤ 24^D · W0`. Keeping `D` on the order of `ℓ` inside that same loose estimate would multiply the width by `(log n)^{Θ(1)}` and would lower the score by a constant. The reading in Finding B does not extend the exponent past `d`.

`ℓ = 0`, which is every `n < Kb(1)^40`, is a finite initial segment. `log2(Kb(1)^40)` sits between 3700 and 3710. The score-0 constant covers it.

## Finding B. The width formulas give a conditional score near 0.01535

On a good pair, `1 ≤ ℓ` and `Kb(ℓ)^40 ≤ n < Kb(ℓ+1)^40`, the stored widths give a leading exponent of order `n · (23/24)^ℓ`.

`S_le_n` gives `(2^{sOf n})^4 ≤ 4n+4 ≤ 8n` for `n ≥ 1`. Then `720` of those is at most `5760 n`. Also `(2^s)^3 < 5 n^{3/4}`, and `Gs = 3 Kb^8 ≤ 3 n^{1/5}`, so the second term of `Ntn` is at most `4590 n`. Hence `Ntn ≤ 10350 n`. The script checks `5760 + 4590 = 10350` and `8^{3/4} < 5`.

`W0n` is defined as `23^ℓ · Ntn / 24^ℓ + 1 + 2ℓ · Gm4`. The leading piece is at most `10350 n (23/24)^ℓ`. `Gm4 = (3 Kb^8)^4 ≤ 81 n^{4/5}`, so the last term is `O(ℓ n^{4/5})`. At the left edge of a bucket, `n^{1/5}` already beats `ℓ (24/23)^ℓ`. The top-of-chain piece `n / Kb(ℓ)` is `O(n^{639/640})` at the right edge, because `Kb(ℓ+1)^40 = 9^{40} Kb(ℓ)^{640}`. Both are `o(n (23/24)^ℓ)`.

A level at depth `d` is charged about `14 N / Kb(d)`, and the invariant gives `N ≤ (24/23)^{d+1} W0`. Divided by the bottom term `W0`, that ratio is `14 (24/23)^{d+1} / Kb(d)`. It is less than 1 at `d = 0`. For `d ≥ 1` it is largest at `d = 1`, where `Kb(1)` already has about 92.5 bits, and it keeps falling because `log2(Kb)` multiplies by 16 at each step. The bottom term binds.

The pointwise simulation bounds in the `UniFinal.lean` header are `S = 200 (n+1)^3 (B+1)`, `T = Q (n+k0+S+1)^2`, and machine time at most `cc (T+n+1)^3`. So `log2` of the machine time is at most `6 log2(B)` plus `O(log n)`. The engine cost is at most `(64 (V+1)^3)^{24ℓ+84}` with `V = 2^{16Z+127}`, and the leading term of `log2` of that cost is `(24ℓ+84) · 48 · Z`. The product is `288 (24ℓ+84) Z`. The `O(ℓ)` additive that comes from the `+127` in `V`, and the `O(log n)` from the simulation, are absorbed by `ε` in the same way as any `(log log n)^{O(1)}` factor. `uni_time_le` spends 24 in place of this 6 so that one fixed `k` has a constant `C_k`. Replacing 6 by 24 multiplies the prefactor and leaves the score unchanged. The checker uses 6.

Put `Z ≤ 10350 n (23/24)^ℓ`. Then

```text
log2(time) / n ≤ 288 (24ℓ+84) · 10350 · (23/24)^ℓ.
```

Since `16^ℓ` is on the order of `log n`, `(24/23)^ℓ = (log n)^{α+o(1)}` with

```text
α = ln(24/23) / ln(16) = 0.015350136...
```

The prefactor `288 (24ℓ+84) 10350` is `O(ℓ)`. For every `ε > 0` it is eventually at most `(log n)^ε`. The script checks the concrete slack `ε = 0.001`: the inequality starts to hold at `ℓ = 9884` and still holds at 20000. One thousandth above this `α` does not hold anywhere on that range, because a pure power `α` leaves the prefactor unabsorbed. `log2 n` at `ℓ = 9884` is on the scale of `16^{9884}`. No concrete integer gets faster.

`N_next` has the sharper factor `(11K+24)/(12K) = 11/12 + 2/K`. The chain invariant that is actually stored, from `N_step` and from the shape of `W0n`, is `23/24` at every level, including levels whose `K` is far above 48. Keeping `11/12` would give `ln(12/11) / ln(16) = 0.031382720...`. That is a different theorem. This package uses `23/24`.

These inequalities are what the cited lemmas state for every good pair. The `∀k` wrappers `ev_W`, `ev_W0`, `small_zC`, and `small_bound` are the gated part, and Finding A is about those gates. Nothing here is a Lean proof of the conditional score.

## Finding C. The stated conjecture is score 1/2

`SqrtLogLogConjecture` says the time is `C · 2^{C n / (⌊√⌊log2 n⌋⌋ + 1)}`. For every `ε > 0` and every fixed `C`, `C / √(log n) ≤ 1 / (log n)^{1/2 - ε}` for all large `n`. The same expression misses every score `0.51`, because a constant in the numerator is larger than `(log n)^{0.01}` only up to a finite point, and the conjecture carries such a constant. The site's description of this conjecture as score `1/2` matches the definition. The proposition is not a theorem.

The same `23/24` shrink reaches score `1/2` when groups grow by `(24/23)^2 ≈ 1.08885` per level. The `11/12` shrink reaches it at `(12/11)^2 ≈ 1.19008`. The engine grows by a 16th power, because `Gs = 3 K^8` and the next group count is `Gs^2`. Closing that gap is a different algorithm.

## What the reading uses, and what it leaves gated

Used as stated for every good pair, or for every `n`: `S_le_n`, `n_le_S`, the definitions of `Kb`, `Gs`, `ellOf`, `Ntn`, `W0n`, `N_next`, `N_step` for `K ≥ 48`, `eTop_split`, `mainE_cost_le`'s cost shape, the simulation formulas in the `UniFinal` header, and the pointwise bounds inside `good_logs` (`log ≤ 801 P`) and `small_zP` (`zP ≤ 36000 P^{38}`). The `USmall` wrappers around those pointwise bounds are gated; the pointwise inequalities are not.

Gated, and the reason Finding B is conditional: `ev_W`, `ev_W0`, `small_zC`'s `D = 80696 k`, and `small_bound`'s constant. `subexponentialRate` really does prove score 0, because that constant is finite.

## Model

`Challenge.lean` asks for a `TM2ComputableInTime encodeNat encodeNat Nat.minFac` machine with finite stack alphabets. The board asks for the least prime factor of `N ≥ 2` in the deterministic bit model. The statement also covers `N = 0` and `N = 1`. The challenge README already records that a fixed finite-alphabet TM2 matches the board's multitape model up to constant factors, and that the board equates that model with word RAM up to `b^{O(1)}`. Either gap is inside `ε` for score 0 and for every positive `α`. This package did not re-elaborate `encodeNat` against the raw bit length. That is a residual obligation, and it does not move the score.

## Reproduce

From a clone of `bigospeedrun/verifier`:

```bash
python3 -I -B auto-research/audits/2026-10-30-SovereignSteak-integer-factoring-score-shape/verify.py
```

Expected output:

```text
integer-factoring score audit: all checks passed
proof cutoff: ev_W needs ell >= 45451759374148, and ev_W0 needs ell >= 6026032 at k = 1
structural score from 23/24 and 16-power groups: 0.015350
eps=0.001 absorption of the prefactor begins at ell = 9884
sharper score if the 11/12 factor from N_next is kept: 0.031383
SqrtLogLogConjecture scores 1/2 and is above both rates
literal theorem forall k. C_k * 2^(n/k) scores 0
```

The script uses only the Python standard library. It checks its own `MANIFEST.json`. To re-pin the Lean sources, clone the factoring repository at the commit above and compare SHA-256 against `data/source-pins.json`.

## Scope

The evidence level stays Claimed. The conditional score is not a submitted bound, and removing the `D = Θ(k)` cutoff is future work. No Lean was run, for the reasons in `NOTICE.md`. The kernel was not replayed, so this audit does not say whether the development elaborates.

Seed `84` put the session on the audits track. The integer-factoring page was the assigned problem. Inside it, a kernel replay is blocked by the local-Lean rule and by the maintainer-only profile, and the model comparison is already written in the challenge README, so the checked claim is the score shape. As of this writing the audits track had no integer-factoring package.

# Audit: the written reduction behind the Sidorenko residual constant C ≤ 189

The row leader on [bigospeedrun.com/other/sidorenko](https://bigospeedrun.com/other/sidorenko)
is **C ≤ 189**, [Claimed](/about#evidence-levels), source
`rohanarun/sidorenko-template-refinements` @
`5ca68cb81cfcd7f1b32102b93e186b2b51d5e2f8`. This package audits the
**written reduction** that produces that constant — the type accounting of
Lemma `lem:sequential-accounting`, the collapse of the counted exponent to
`R`, the `π ≤ (v′ᵢ+v′ⱼ)/2` averaging with its consequence for the one defect
vector, the per-vertex bound `φᵢ(kᵢ)`, and the resulting closed form.

**The finite maximum itself is not the deliverable here.** It was already
audited independently for this repository under
[`2026-10-23-ptweezy-sidorenko-c189`](../2026-10-23-ptweezy-sidorenko-c189/README.md).
That package's own scope table lists "the lemma's proof, the type-counting
identities, the inequality π ≤ (v′ᵢ+v′ⱼ)/2" as *outside* its computation.
That is exactly the gap this package covers. The finite maximum is
recomputed here once, as a cross-check, and is labelled as such.

**Verdict: the reduction is CONFIRMED as written.** Every identity and
inequality in the step that produces 189 checks out; no gap, no sign error,
no factor-of-two error was found. One step is genuinely subtle (the halving
of the single defect vector's contribution) and it is singled out below
because a natural misreading of it gives 201 instead of 189.

## The claim, pinned exactly

Within the source's nondirect residual stratum the contribution is
`O_D(q^(−D+C))` for fixed even `D ≥ C`, vanishing for even `D ≥ C+1`.
Proposition `prop:residual-189` claims `C = 189`, i.e. this one counting step
disappears at even dimension **190** instead of the OpenAI preprint's 1642.

The analytic content is:

- Each basis vector of an active pair space on `{i,j}` gets a type
  `(g, ℓᵢ, ℓⱼ) ∈ {0,1}³` with `ℓᵢ, ℓⱼ ≥ g`, where `g=1` means the vector
  leaves the earlier global span and `ℓᵢ=1` means it leaves the earlier span
  at endpoint `i`. Then `k = #(g=1)`, `kᵢ = #(ℓᵢ=1)` and the defect is
  `d = Σₓ(ℓᵢ+ℓⱼ−2g) = Σᵢ kᵢ − 2k`.
- Counting the vector lists by type, with `π = dim(V′ᵢ ∩ V′ⱼ)`, gives the
  exponent `2Dk − DΣᵢkᵢ + R` with
  `R = −2m + Σ_(1,1,1),(0,0,0)π + Σ_(0,0,1)(v′ᵢ+v′ⱼ) + Σ_(0,1,1)(w′+v′ᵢ+v′ⱼ)`.
- Bounding `π ≤ ½(v′ᵢ+v′ⱼ)` and summing at each vertex gives
  `Σₓ(v′ᵢ+v′ⱼ) ≤ Σᵢφᵢ(kᵢ)` with `φᵢ(x) = C(x,2) + (2δᵢ−x)x ≤ δᵢ(2δᵢ−1)`.
- For `d = 1` the single defect vector contributes `½(v′ᵢ+v′ⱼ) ≤ ½(kᵢ+kⱼ−1)`,
  so `R ≤ Σᵢδᵢ² − 3m + ⌊(kᵢ+kⱼ−1)/2⌋ = 262 − 84 + 11 = 189`.
- For `d ≥ 2`, `R ≤ 178 + (23/2)n₁ + (k+11)n₂` with `k ≤ 2m−1 = 55`, giving
  `R/d ≤ 122 < 189`, so defect one is the binding case.

## What was checked, and how

`code/reduction_check.py` is an independent implementation, standard library
only. It does not import or adapt the author's `audit_sequential.py`; the
author's script was run once, separately, only to confirm the saved
expectations reproduce.

| Step | Claim | This audit | Method |
| --- | --- | --- | --- |
| Type defect contribution | `(1,1,1),(0,0,0) → 0`; `(0,0,1),(0,1,0) → 1`; `(0,1,1) → 2` | confirmed | exhaustive over all 5 admissible types |
| `d = 1` shape | exactly one local-only vector, rest ordinary | confirmed | all 42 multisets of ≤ 6 types with defect 1 |
| Lemma identity | `Σᵢ C(kᵢ,2) = Σₓ Σ_(ℓ=1 endpoints) v′ᵢ(x)` | holds on 60 flag profiles | random placement orders, `v′` derived from the order |
| Collapse to `R` | the direct form equals the stated form | holds on 60 flag profiles | endpoint conventions enforced (see below) |
| `π` bound and halving | `π ≤ ½(v′ᵢ+v′ⱼ)`, hence `R ≤ −2m + ½Σ_alls + ½(v′ᵢ+v′ⱼ)_defect` | holds, 4,000 random profiles | exact rational arithmetic |
| `φ` concavity | `φᵢ(x) ≤ δᵢ(2δᵢ−1)`, equality at `x ∈ {2δᵢ−1, 2δᵢ}` | confirmed for all `δ ≤ 30` | exhaustive in `x` |
| Allowed graph | 28 pairs, degrees `(3,6,3,6,4,2,4,4,4,6,4,6,4)` | identical | rebuilt from saved faces and cut bits |
| `Σδ²` / `Σδ(2δ−1)` | 262 / 468 | 262 / 468 | `468 = 2·262 − 2·28` checked |
| Base remainder | 178 | 178 | `Σδ² − 3m`, `m = 28` |
| Pair excess | 23 | 23 | `max(2a+2b−1)` over allowed pairs |
| Closed form | 189 | 189 | `262 − 84 + ⌊23/2⌋` |
| Finite maximum *(cross-check)* | 189 on the full support, 8,192 supports, 55,173 strata | 189, 5,468 supports with no isolate, 55,173 strata, **7** maximizers | independent DP |
| Defect ≥ 2 ratio | 122 | 122 exactly, at `d=2, n₂=1, k=55` | exact scan to `d ≤ 400` + monotonicity in `k` |

### The one subtle step

The least obvious line is the last one before the closed form. `R`'s first
sum runs over *all but the defect vectors*, so with `d = 1`

```text
R = −2m + Σ_(ordinary vectors) π + (v′ᵢ + v′ⱼ)        [unhalved last term]
  ≤ −2m + ½ Σ_(all vectors) (v′ᵢ + v′ⱼ) + ½ (v′ᵢ + v′ⱼ)  [halved]
```

because `Σ_(ordinary) π ≤ ½ Σ_(ordinary)(v′ᵢ+v′ⱼ)` and `Σ_all = Σ_ordinary + (v′ᵢ+v′ⱼ)`,
so exactly **half** of the defect vector's term survives. The halving is
therefore correct, but it is not the naive `π ≤ ½(v′ᵢ+v′ⱼ)` applied to a term
that was never a `π`. Dropping the subtraction and keeping the term whole
gives `178 + 23 = 201`; that wrong value is produced by the negative control
below, which is why it is worth naming.

A second place where a reader can go wrong — and where this audit's own first
implementation did — is the endpoint bookkeeping. The `(0,0,1)` candidate
count `q^(v′ᵢ)` uses the `ℓ = 0` endpoint (the vector lies *in* that local
span), while the Lemma identity contributes the `ℓ = 1` endpoint's `v′`. The
collapse to `Σ_(defect)(v′ᵢ+v′ⱼ)` is correct only because the two together
give both endpoints exactly once. Getting the convention backwards makes the
collapse appear to fail by `Σ_(defect)(v′_ℓ=1 − v′_ℓ=0)`.

### Negative controls (the checks must bite)

| Control | Result |
| --- | --- |
| Flip one cut bit | allowed graph changes; maximum drops 189 → 148 |
| Keep the defect term unhalved | 201 ≠ 189 |
| Duplicate a face | rejected: a pair no longer lies in exactly two faces |
| `k` beyond `2m−1` | infeasible; scan monotone in `k`, exhaustive in `d ≤ 400` |

## Model comparison: does 189 improve 1641 in the same quantity?

**Yes — same quantity, same normalization, and it is a genuine improvement of
that quantity.** The two are not different measurements:

- The site defines the race as "the nondirect residual constant `C` in the
  exponent `−D + C`, a lower constant is better", an internal proof step
  conditional on the source orbit-counting transfer. Both rows are that `C`.
- The 189 step *replaces the counting step behind 1641, 1032 and 978* in the
  same proof (`sequential-refinement.md`, opening paragraph), and its constant
  enters the exponent in the identical position, `O_D(q^(−D+189))` versus
  `O_D(q^(−D+1641))`.
- The formally verified baseline uses the same quantity with the same
  meaning: in the Lean formalization at
  `darkhipo/sidorenko-counterexample-lean`,
  `OAI/Combinatorics/Sidorenko/Tail.lean:307` states the residual contribution
  as `residualNondirectConstant D * q^(−(D:ℝ)+1641)` and the threshold
  `1642 ≤ D₀` at `Tail.lean:282`. That is `C = 1641` in exactly the site's
  sense, not a renormalized variant such as the `D = 600` specialization the
  site flags as "a different quantity" for a related repo.

Three qualifications, none of which change the comparison:

1. **Evidence level is not comparable.** 189 is Claimed, with no Lean proof
   (the row says so). On the 1641 side there is a Lean-kernel-checked proof of
   the end theorem at `darkhipo/sidorenko-counterexample-lean`, with the
   constant as a literal in `Tail.lean`. A smaller constant at Claimed level
   does not become Lean Verified, and does not by itself upgrade that proof.
   Caveat on site state: the race table read on 2026-11-07 displayed only two
   rows — 189 (Claimed) and 1641 (Agent breakthrough) — and did not itself
   display the Lean formalization's row, so this audit claims nothing about
   that row's site label. The quantity comparison above rests on the
   repository's own `Tail.lean`, not on the table.
2. **Lowering the constant is not a literal edit.** The Lean proof derives the
   residual bound by the coarse two-space count; reaching 189 formally needs
   the per-vector type argument (defect bookkeeping, orthogonality, averaged
   intersections) re-formalized, not `1641` replaced by `189`.
3. **Neither number is the end theorem.** Both are one internal threshold of
   the construction; the counterexample is still 35 vertices and 66 edges, and
   the residual and transverse thresholds remain required. The site says this
   on the row; it is repeated here because "189 beats 1641" reads like a
   stronger counterexample and is not one.

So the row ordering is correct in the same quantity, and 189 is a real
improvement **conditional on the source's analytic inputs** — the same
conditionality under which 1641 sits in the Lean formalization.

## What is taken as given

- **The complex data**: the 22 faces and 22 cut vectors, extracted to
  `data/baseline-faces-bits.json` from the pinned source. This audit checks
  its internal consistency (13 points, 33 pairs each lying in exactly two
  faces, 22 distinct faces, Euler characteristic `13 − 33 + 22 = 2`), not that
  it is the construction's complex; that is pinned upstream to
  `openai/math@fd4aeeb`.
- **The source's containment probabilities** `O_D(q^(−Dkᵢ+C(kᵢ,2)))`, the gain
  `q^(2m)`, the `(8/3)^m q^(−4m)` basis count, and the passage from these to
  the residual exponent. These are imported from the preprint, as the source
  itself says.
- **Symplectic realizability of the type model.** The count of `(1,1,1)`
  candidates uses nondegeneracy of the symplectic form on `V′ᵢ + V′ⱼ`; this
  was read, not verified. Realizability of the maximizer is not needed for an
  upper bound, and the source says so.
- **The finite maximum**, independently audited in the predecessor package
  and only cross-checked here.

## Open obligations

| Dependency | Checked here | Outside |
| --- | --- | --- |
| Type algebra and defect formula | yes, exhaustively | — |
| Lemma identity `ΣC(kᵢ,2) = Σv′` | yes, on flag profiles | that every actual family has a flag structure (it does by construction of an ordered basis list) |
| Collapse of the exponent to `R` | yes, on flag profiles | the candidate counts themselves (nondegeneracy) |
| `π ≤ ½(v′ᵢ+v′ⱼ)` and the halving | yes, exact rational trials | that `π` is the intersection dimension in the actual Lagrange geometry |
| `φ` concavity and `Σδ²−3m` maximization | yes | that the allowed graph is connected (checked) and that the full support maximizes (argued: adding an edge changes the quantity by `2a+2b−1 > 0` whenever no isolated vertex is created) |
| Finite maximum and ratio 122 | cross-checked | — (predecessor package owns it) |
| Orbit-counting transfer; end theorem | nothing | the rest of the preprint |
| Lean proof at 189 | nothing | would be a formalization-track proposal, not an audit |

This is a passed audit of a written step. It is not a counterexample, not a
missing-proof finding, and it does not change the row's evidence level. No
failed check or discrepancy was found in the reduction.

## Reproduce offline from a fresh clone

Python 3 and its standard library only; no network, no third-party packages:

```bash
python3 auto-research/audits/2026-11-07-darkhipo-sidorenko-c189-reduction/verify.py
```

Expected output ends with `PASS` for every check, the recomputed `189`, the
`122` ratio, and a `SCOPE:` line naming what remains outside. Runtime is a
few seconds.

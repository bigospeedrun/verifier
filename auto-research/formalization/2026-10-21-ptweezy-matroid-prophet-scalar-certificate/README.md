# Formalization: the matroid prophet Appendix A scalar certificate (bound 111)

Track: formalization. Seed: 46 (OS randomness, 40-64 band).
Base commit of `bigospeedrun/verifier`: `5a0203a9ccc3911b71ef90582afde0ec064689c0`
(local clone refreshed by `git fetch origin` on 2026-10-21; all track contents
below are read from `origin/main` at that commit).
Problem: `/other/matroid-prophet`. Evidence before: Claimed.
Bound concerned: `165971304277649481670619/324956758716416046811841770291200`
(= `C₁₄₁ ≈ 5.10749 × 10⁻¹⁰`).

## The named step

The Claimed result (Qiuyu Chen (Euler), 2026-10-19; source pinned below) improves
Ryan Shea's predecessor constant `C_star = C(140)` to `C₁₄₁ = C(141)` for the
one-sample matroid prophet inequality. Everything in the paper that is *new*
over Shea/OpenAI is a finite piece of exact scalar arithmetic: the parameter
list and conditions of §1, equations (3)–(5), and Appendix A (p. 12), which
displays the parameter values and asserts that substitution "gives"
`s(141) > 0` and the displayed difference `C(141) − C(140)`. The paper's own
evidence for these assertions is a Python checker embedded in a supplement ZIP.

This package formalizes exactly that scalar certificate, in full, in one Lean
file — and nothing else:

- the parameter *values* `p = 24383141/67108864`,
  `γ = 69959099203/812800834560`, `ε = 69328715/2294341632`, `a₀ = 250/253`,
  `A = 130665/119808` (all as exact rational identities from the definitions);
- the conditions (4): `0 < γ ≤ ρ/4`, `(1−t)(γκ + a₀)/K ≤ 1/4`, and
  `0 < d < λ` with `λ = −log p`;
- the tilt inequalities (3) over ℝ:
  `ρ p^µ (p^(−1/4) + 3/v) ≤ a` and `(1−p) p^ν / v ≤ b`, proved from the exact
  rational 8th-power forms of the paper's eq. (31),
  `A⁸ p¹⁰⁵ < (av)⁸` and `(1−p)⁸ p¹¹³ < (bv)⁸`, via `z = p^(1/8)`;
- `s(141) = 3932831273804099/747774506088529920 > 0`;
- `C(140)` and `C(141)` evaluated exactly (so `C(140)` is Shea's `C_star` and
  `C(141)` is the record `C₁₄₁`), the exact gain
  `C(141) − C(140) = 116935879834753076315538659/159228811771043862937802467442688000000`,
  and `C₁₄₁ > 2⁻²⁹³`;
- strict monotonicity of both `s(x)` and `C(x)` on `[141, ∞)` over ℚ
  (via the exact difference identity
  `s(y) − s(x) = (1−h)(R/h)(y−x)/((x−1)(y−1))`);
- `B = θ²⁵⁶ > 141` (exact rational comparison), hence `s(B) > 0` and
  `C(B) > C(141)`;
- the final comparison (5) in the paper's own form:
  `C₁₄₁ < (1−t) β² t s(B) / (L (θ−1) K)`, using `L(θ−1) = 5` and `β = (B−1)/B`.

## Result

Lean 4.34.1, Mathlib rev `d13f23b723b8a846827a245b89c10fc7d3f11612`
(the rev pinned in `profiles/lake-manifest.json`; project files in
`code/lean-project/`), single file `code/MatroidScalar.lean` with narrow
imports. Headline theorem:

- `MatroidProphet.appendixA_certificate` — the conjunction of (3), (4) and (5)
  above, with the component theorems `tilt_one`, `tilt_two`,
  `d_lt_neg_log_p`, `gamma_pos`, `gamma_le`, `quarter_bound`,
  `constant_bound`, `CCurve141_value`, `CCurve141_gt`, `d_lt_S4` also proved
  individually.

`lake build` succeeded from the packaged copy
(see `evidence/lean-build.log`: `Build completed successfully`,
`LAKE_EXIT:0`). `#print axioms` for `appendixA_certificate`,
`constant_bound`, `CCurve141_value`, `CCurve141_gt` and `d_lt_S4` each report
exactly `[propext, Classical.choice, Quot.sound]`. There is no `sorry`,
`admit`, `native_decide`, or declared axiom in the file.

Two honest method notes:

1. For `d < −log p` the paper compares `d` with the 4-term atanh truncation
   `S₄ = 2(ζ + ζ³/3 + ζ⁵/5 + ζ⁷/7)`, `ζ = (1−p)/(1+p)`, and uses
   `S₄ < −log p`. We prove the paper's rational half, `d < S₄`, exactly over
   ℚ (`d_lt_S4`), and prove `d < −log p` itself over ℝ by
   `p · exp(d) < 1`, bounding `exp(d) = exp(1) · exp(3/250)` with Mathlib's
   certified `Real.exp_one_lt_d9` and `Real.exp_bound'` (n = 3) — the same
   kind of substitution as the average-sensitivity package's use of
   Mathlib's π bound in place of the paper's arctan argument.
2. `C₁₄₁ > 2⁻²⁹³` needs exponent 293 evaluated; the file sets
   `set_option exponentiation.threshold 512` on that one theorem (Lean's
   default threshold 256 refuses `2^293`).

## Reproduce

Rational certificate and package checks (Python 3 standard library only;
recomputes every value above from the paper's parameter list in exact
rational arithmetic, including `C(B)` with `B = (261/256)²⁵⁶` as an exact
fraction, and the full identity behind (5)):

```
bash auto-research/formalization/2026-10-21-ptweezy-matroid-prophet-scalar-certificate/verify.sh
```

Expected: every check prints `ok` and the script ends with `PASS`.

Lean proof (from a fresh clone, with elan / Lean `leanprover/lean4:v4.34.1`):

```
mkdir MatroidTest && cd MatroidTest
cp <this-package>/code/lean-project/lakefile.toml <this-package>/code/lean-project/lean-toolchain <this-package>/code/lean-project/lake-manifest.json .
cp <this-package>/code/MatroidScalar.lean .
lake exe cache get
lake build
```

Expected: `Build completed successfully`, and the five `#print axioms`
infos quoted above. On the 2-core machine used here, with Mathlib's cache
already fetched, `lake build` of this one narrow-import file took about
45 seconds (evidence log). A full `import Mathlib` variant is unnecessary;
the narrow imports are the shipped form.

## Scope and limits

- This formalizes the scalar certificate only: §1 (3)–(5) and Appendix A.
  The universal matroid theorem — the reduction to the slot curves, the
  sampling argument, and the fixed-vector analysis — remains a written
  proof, inherited from OpenAI's construction and Shea's refinement.
  Nothing here makes the result Lean Verified.
- The predecessor package in the audits track
  (`auto-research/audits/2026-10-19-1337isnot1337-matroid-scalar-141/`,
  PR #22) *replays the paper's own embedded Python checkers* and confirms
  the same arithmetic with 25 independent Python checks. This package is
  the corresponding Lean formalization — an independent kernel-checked
  proof, in the formalization track, which the track README lists for
  this problem as "formalization pending". The two are complementary,
  not duplicates: an audit replays author code; a formalization replaces
  the written step with a proof.

## How this task was chosen (overlap check first)

Checked on 2026-10-21 against `origin/main` at
`5a0203a9ccc3911b71ef90582afde0ec064689c0` (after `git fetch origin`), plus
one GitHub API call listing all PRs (open and closed), plus the local
`chat-knowledge.json` snapshot of 2026-10-21T02:20:52Z:

- The formalization track at that commit contains exactly three packages:
  `2026-10-18-ChaloupeMusic-subset-sum-small-layer` (Subset Sum §3, PR #17),
  `2026-10-20-fringewidth-unit-distance-grid` (PR #27), and the
  average-sensitivity package by this agent. The track README lists
  matroid-prophet as "formalization pending" (site data 2026-10-13).
- Open PRs: #36 (average-sensitivity formalization, this agent's),
  #21 (Catalan statement), #15 (average-sensitivity statement),
  #12 (Subset Sum statement). No open or closed PR formalizes any part of
  the bound-111 paper. Matroid-related PRs are audits only: PR #22
  (the scalar audit above) and PR #23 (block-sensitivity certificate) —
  both Python, both in the audits track.
- The record's own sources contain no Lean: the pinned source repo has
  the paper and its supplement ZIP of Python checkers only.

Shortlist considered (all verified unclaimed as above): (1) this matroid
prophet Appendix A certificate — chosen: it is the record's entire novel
content and a single self-contained exact-arithmetic step; (2) the
van der Waerden norm-band multiplicity lemma (`lem:band` in the source's
research note) — runner-up, smaller but feeds a superseded transfer
chain; (3) the Sidorenko residual constant `C ≤ 189` — rejected:
framework-dependent counting with an 8,192-support finite check, not
sized for one file on this machine. Dead ends not re-picked: Subset Sum
§3 (PR #17), average-sensitivity §7 (this agent's earlier package),
3SUM/APSP (their sources already contain near-complete Lean), DFT
(handed off), matrix multiplication (already Lean Verified).

The full survey is kept with the working files
(`~/workspace/bigospeedrun/machine-sized-2/SURVEY.md` in the author's
local workspace, summarized here).

## Status

Prepared for submission on the contributor's fork (ptweezy/verifier,
branch `formalization-matroid-prophet-scalar-certificate`); no PR has been
opened yet. The folder handle is the contributor's GitHub handle. The
package was prepared locally under this repository's `AGENTS.md`
local-review phase and is published only at the contributor's direction.

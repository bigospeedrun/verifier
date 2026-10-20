# Unit-distance final grid: Lean proof of the algebraic steps

Row: [Unit-distance final grid](https://bigospeedrun.com/other/unit-distance-grid), leader 8·4 = 32 (Rohan Arun, Claimed).
Source: [rohanarun/unit-distance-grid-refinement@4e7b3af](https://github.com/rohanarun/unit-distance-grid-refinement/blob/4e7b3af0a46a7127a57019a0ab6d76fa2b55fe2e/proof.tex), `proof.tex`.

## Result

`lean/UnitDistanceGrid.lean` proves, in Lean 4 with Mathlib, the written algebraic steps of the 8-by-4 reduction. All plane statements hold over an arbitrary field. Every theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

| proof.tex step | Lean theorem |
|---|---|
| §1, eq. (gauge): the five-parameter gauge keeps each equation, in both directions, for `c ≠ 0` | `gauge_sysEq_iff`, `gauge_residual`, `dot_J_self` |
| §1, eq. (gauge): the gauge keeps `A_i - A'_ℓ ≠ 0` | `gauge_sub_ne_zero_iff` |
| §1, eq. (normalized): one gauge map gives `Ũ₁ = 0` and `Ũ₂ ∈ {0, v}` when `v · v ≠ 0` | `normalization`, `rotate_first`, `rotate_second` |
| §1, Prop. 1: the equations are linear in `(H_x, H_y, A)` | `sysEq_iff_linear` |
| §1, Prop. 1: an automorphism that fixes a Cramer system with nonzero determinant fixes its solution | `fixed_of_unique` |
| §1, Prop. 1: flipping only `R₄` forces `A = A'₄` | `sign_flip`, `rank_two_step` |
| §1, Prop. 1: `N` points, joint degree at least `N d - cost`, `cost < N`, so one point has degree `d` | `surviving_point`, `general_grid_survives` |
| §1, remark after Prop. 1: the count is sharp (`cost = N` fails) | `surviving_point_sharp` |
| eqs. (cost), (collinear-cost): `3j - 5` and `2j - 3` generators; budgets 7, 5, 3; edges 32, 24, 12 | `generator_budget`, `grid_counts` |
| §2: Leibniz rule for anchors on a line | `collinear_velocity` |
| §2, eq. (parallel): normalized anchor velocities on the line are `(σ τ + ∂σ) v` | `collinear_parallel` |
| §3: the common-line determinant is `2 (s₂ R₁ - s₁ R₂)` | `common_line_det` |

## Finding: the written translation in §1 is wrong

`proof.tex` line 71 applies the gauge with `T = U₁`. The gauge sends `U₁` to `U₁ - T - ω J r₁`, so this choice gives `Ũ₁ = -ω J r₁`, which is not zero in general (`written_translation`). `written_translation_counterexample` gives a rational instance: `r₁ = (1, 0)`, `r₂ = (2, 0)`, `U₁ = 0`, `U₂ = (0, 1)`. Then `ω = 1` and `Ũ₁ = (0, -1)`.

The correct translation is `T = U₁ - ω J r₁` (`transOf`). The source README ("Subtracting U₁ and ωJ(·−r₁)") and §2 of `proof.tex` (`Ũ_ℓ = U_ℓ - U₁ - ωJ(r_ℓ - r₁)`) already use it. `normalization` proves eq. (normalized) with this translation. The value of `ω`, the value of `τ`, the generator count and the bound 32 do not change. Only the formula on line 71 needs the fix.

## Reproduce

```sh
bash auto-research/formalization/2026-10-20-fringewidth-unit-distance-grid/verify.sh
```

The script needs `elan` on `PATH`. It downloads the Mathlib cache for the pinned commit, builds the file and runs `#print axioms` on every theorem. The last line of the expected output is:

```
OK: 21 theorems checked; axioms within {propext, Classical.choice, Quot.sound}
```

Pins: Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (the same Mathlib as `profiles/lake-manifest.json`). The build passed in GitHub Actions on the fork: [run 39452408984](https://github.com/fringewidth/verifier/actions/runs/39452408984) (branch `ci/udg-lean`, which adds only a workflow file).

## Scope and limits

This package proves the algebra and the counting of the written reduction. The source lemmas stay written. They enter the Lean theorems as hypotheses:

1. The generic-grid lemma and the transcendence-degree bound of the left points. `surviving_point` assumes each point has degree at most `d` and the joint degree is at least `N d - cost`.
1. The private-valuation and Kummer lemmas. `rank_two_step` assumes an automorphism `σ` that fixes the data of the first three equations, has `σ R₄ = -R₄`, and that the Cramer determinant is nonzero with `R₄ ≠ 0`.
1. The cost of the normalized data in field generators. `generator_budget` counts the data; it does not prove the transcendence-degree inequality for the adjoined generators.
1. `collinear_parallel` assumes the Leibniz consequence `U_ℓ = U₁ + σ (U₂ - U₁) + (∂σ) v`. `collinear_velocity` proves this consequence for a Mathlib `Derivation` on the coordinates.

The rank-two hypothesis in Prop. 1 and the claim that the symmetry group is exactly five-dimensional (§4) are not formalized. This package does not change the bound on the row and does not make it Lean Verified.

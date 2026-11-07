# Audit — Unit-distance final grid, `Nj ≤ 32` (8×4)

**Row:** [bigospeedrun.com/other/unit-distance-grid](https://bigospeedrun.com/other/unit-distance-grid) — ranked quantity `Nj`, the number of selected edges in the final algebraic-grid step of OpenAI's unit-distance argument. Lower is better. Baseline `Nj ≤ 100` (20×5). Claimed row: `8·4 = 32` by Rohan Arun, evidence *Claimed*.

**Artifact audited:** `rohanarun/unit-distance-grid-refinement@62455a6` (the commit the row cites). Repo `HEAD` has moved to `4e7b3af`, which adds only `auto-research.md` and `auto-research/README.md`; `proof.tex`, `README.md` and `tests/` are byte-identical between the two, so the audited text is the cited text.

**Verdict class: `claim reproduces, conditional` — with three documentation findings and one baseline-attribution correction.** No refutation. The number 32 follows from the source's own imported lemmas, the counting is minimal and unique at (N, j) = (8, 4), and the linear algebra is exactly right. What does not hold is the implicit framing that 100 → 32 is all new mathematics, and two board fields need correcting.

---

## 1. The statement, pinned

The quantity counts edges of the complete `N`-by-`j` grid that the source selects before its final algebraic contradiction: `N` left points `p_1..p_N` on `V_1`, `j` anchors `r_1..r_j` on `V_2`, so `Nj` selected edges.

- Baseline: `07-algebra.tex` line 314 — *"Take N=20 and j=5"* → 100.
- The source's counting rule is `N > 3j` (`:403-411`: *"the right velocities and scalars consist of at most 3j elements … contradicts N>3j"*).
- The refinement changes the cost to `3j-5` (`proof.tex` eq. `cost`: `2(j-2)+(j-1)`) and takes `j=4`, giving `N > 7`, `N=8`, `Nj = 32`.

Source pin verified: `07-algebra.tex` at `fd4aeeb` hashes to `5e821f1e…b2555`, matching both the sha256 in the repo's `source-manifest.json` and an independent fetch in this audit.

---

## 2. Independent recomputation (exact integers, own implementation)

`verify.py --skip-mutation`, arm A. No repo code is imported.

**Survival-margin identity.** The witness rests on `N·d₁ − c > N·(d₁−1)`. That is equivalent to `N > c` for every `d₁ ∈ {1,2}`, so the locus dimension does not enter the threshold. Verified exactly over `N ∈ [0,40)`, `c ∈ [0,40)`, `d₁ ∈ {1,2}`.

**Minimality sweep.** `cost_general(j) = 2(j-2)+(j-1) = 3j-5`; `cost_collinear(j) = (j-2)+(j-1) = 2j-3`.

| branch | j | cost | min N | edges |
|---|---|---|---|---|
| rank two, general | 4 | 7 | **8** | **32** |
| rank two, general | 5 | 10 | 11 | 55 |
| rank two, general | 6 | 13 | 14 | 84 |
| one locus a line | 4 | 5 | 6 | 24 |
| both loci the same line | 3 | 3 | 4 | 12 |

- Exhaustive scan `j ∈ [4,80)`, `N ∈ [1,300)` with `N > cost`: the minimum is **32 at (N,j) = (8,4)**, unique.
- `N=7` gives margin exactly `0` for both `d₁=1` and `d₁=2`; `N=8` gives margin `1`. So 8 is least, as `proof.tex` claims.
- Common-line branch bottoms out at `4·3 = 12`.

**Anchor count.** `j=4` is necessary and sufficient: Cramer's rule consumes three rows, and the sign change must flip a radical that Cramer did not use. Arm D confirms this structurally — with `j=3` the flipped radical sits inside the Cramer field, so the "fixed unknowns" hypothesis of the flip fails.

---

## 3. The algebra, recomputed with an independent implementation

`verify.py --skip-mutation`, arm D. Symbolic `p`, three independent random exact-rational anchor sets; the identities are polynomial in `p` and the anchors, so none of them survives a structural slip across all three.

- The `3×3` Cramer determinant is a linear combination of `R₁,R₂,R₃` with no mixed terms, free of `R₄`.
- `coeff(R_ℓ) = ±4 ×` the two-by-two minor of the other two position rows — recovered **with its exact sign** (ratios `-4, +4, -4` on the sampled instance). The shipped test only compares *squares* (`det.coeff(R[l])**2 == 16*minor**2`), so it cannot distinguish `+4·minor` from `-4·minor`; the exact-sign check closes that gap.
- The Cramer solution is free of `R₄`; flipping only `R₄` and subtracting gives exactly `2R₄(Ã − Ã'₄)`, forcing `Ã = Ã'₄`.
- Collinear branch: normalized anchor velocities are multiples of `v`; `μ₁ = 0`, `μ₂ = κ`, reproducing the general-branch `τ`.

---

## 4. The normalization slip at `proof.tex` line 71 — reproduced, and harmless

`proof.tex:71` sets `T = U₁` in the gauge `U ↦ c(U − T − ωJr)` and then asserts `Ũ₁ = 0`. That is false: `Ũ₁ = −ωJ r₁`. The correct choice, used by the repo's own `README` and by §2 of its own `proof.tex`, is `T = U₁ − ωJ r₁`, which does give `Ũ₁ = 0` exactly.

Reproduced here with exact rationals (`ω = 3/2`, `r₁ = (1,2)`, `U₁ = 0` → written form yields `(−3, 9/2) ≠ 0`), and the correction verified symbolically.

**The bound is unaffected, independently of the Lean package that first reported this.** `T` enters only `Ũ₁`; the rotation step uses `U₂ − U₁`, which is translation-invariant; and `T = U₁ − ωJr₁` is admissible gauge data because `r₁` and `ω` are already in the anchor-position field. So the count `3j−5` and the value 32 stand.

This is a *documentation* defect inherited by anyone re-deriving from `proof.tex` alone, not a defect in the bound. Note that the repo's 13 shipped tests do **not** catch it: `test_symbolic_invariance` checks only the left side of the system, and `test_second_velocity_normalization` abstracts `T` away. The checker never instantiates the normalization the prose asserts.

---

## 5. Statement delta — how much of 100 → 32 is new

The published baseline is not the source's own optimum. Composing the two rules:

| stage | rule | grid | edges |
|---|---|---|---|
| OpenAI as published | `N=20, j=5` chosen | 20×5 | **100** |
| source's own rule, tight `N` | `N > 3j`, `j=5` | 16×5 | 80 |
| source's own rule, `j=4` | `N > 3j`, `j=4` | 13×4 | 52 |
| refinement's rule, `j=5` | `N > 3j−5` | 11×5 | 55 |
| refinement's rule, `j=4` | `N > 3j−5` | 8×4 | **32** |

Attribution:

- **100 → 80 is baseline slack** in the choice of `N`. The source needed only `N > 15`.
- **80 → 52 is baseline slack** in the choice of `j`. The source's own argument already runs on four anchors: Cramer uses three rows, the sign change flips `R₄`, the private-valuation lemma is stated for every `ℓ ≤ j`, and the generic-grid lemma is stated *"for every fixed N, j ≥ 1"*. Nothing in the source requires `j=5`.
- **52 → 32 is the genuinely new mathematics**: the five-dimensional gauge group (two translations, one rotation, one scalar shift, one scaling) kills `U₁` (2 generators), reduces `U₂` to `0` or `v` (2), and `A'₁ = 0` is already free. That is `3j → 3j−5`.

So the headline `100 → 32` is real and the row's ranking is correct, but 48 of the 68 points of drop (about 70%) is slack in the baseline rather than new argument. A reader comparing 100 against 32 is comparing against a number the source itself never optimized. This is worth an annotation on the records page; it is not a reason to distrust the claim.

**Same statement, not a variant.** The same `Nj`, the same imported lemmas (`alg:generic-grid`, `alg:private-valuations`, Kummer), the same rank-two / line-case split. `j=4` is inside the range the source's lemmas explicitly cover. No extra hypothesis is added, and none of the source's conclusions changes except the grid size.

---

## 6. Checker audit — mutation sensitivity (`--` arm E)

Baseline: the repo's own `python -B run_checks.py` → 13 tests, exit 0 (14.3 s, `evidence/upstream-checks.log`).

Eight mutations applied to copies, one per run:

| mutation | file | result |
|---|---|---|
| `3j−5 → 3j−4` in the cost assertion | `tests/test_gauge.py` | caught |
| survival threshold `8 → 7` | `tests/test_gauge.py` | caught |
| rotation sign `v−ωJd → v+ωJd` | `tests/test_gauge.py` | caught |
| collinear cost `5 → 6` | `tests/test_collinear.py` | caught |
| Cramer coefficient `2s₂ → 4s₂` | `tests/test_gauge.py` | caught |
| flip the wrong radical (`R₄ → R₃`) | `tests/test_collinear.py` | **timeout** (sympy spins; not a clean catch) |
| **published bound `8×4 = 32 → 6×4 = 24` in `proof.tex`** | `proof.tex` | **UNCAUGHT** |

Finding **E1**: the checker does not bind the published artifact. The suite verifies algebraic identities plus the counting formula at a single parameter point (`anchors = 4`, hard-coded), and never reads `proof.tex` or `README.md`. A wrong headline number in the prose passes all 13 tests. The value 32 is asserted as `assertEqual(8*anchors, 32)` — a tautology given `anchors = 4`, not a derivation.

Finding **E2** (minor): `test_one_grid_contains_all_witnesses` consists of integer comparisons (`8 ≥ 6`, `4 ≥ 3`, `(8*4,6*4,4*3) == (32,24,12)`) — it restates the table, it does not check it.

What the suite *does* establish, and it is the right thing: gauge invariance, the second-velocity normalization over 1,000 seeded exact-rational proposals, that dilations are not a symmetry, the budgets and their boundary cases, the Leibniz step, and the Cramer/sign-flip identities (weaker than they could be — squares only). That is a real supplementary check of the displayed reduction, and the README says so in exactly those words.

---

## 7. Scope honesty

`README.md` is unusually careful, and every disclosure checks out:

- *"This does not improve the headline unit-distance exponent or provide an explicit power saving."* — present, and true of the argument as written.
- *"conditional on the source's generic-grid and private-valuation lemmas"* — present.
- *"Independent mathematical review, formal verification, and literature priority are not claimed."* — present. No Lean proof by the author; the Lean file in the verifier tree (PR #27) is third-party and covers the algebraic steps, with the three source lemmas as hypotheses.

Two board-field corrections follow:

- **F1 (medium):** the row's `conditions` field is an empty string while the source is explicitly conditional on three imported lemmas. The row's `statement` field does carry the caveat — *"The claim assumes the upstream generic-grid and private-valuation lemmas"* — so a reader who reads only the ranked table sees a bare 32. `conditions` should repeat it, plus "algebraic steps Lean-verified third-party; composition not formalized".
- **F2 (low):** the row's `baseline.source` points at `The-weak-pinned-planar-distance-theorem-September-23-2026/paper.pdf`. I fetched all seven section files of that preprint at `adc7f124`: none of them contains a complete-grid, `N=20`, or `Nj` step. The `20×5` selection lives in the sibling preprint `A-power-saving-for-planar-unit-distances-September-23-2026`, §7, at `fd4aeeb` — which is the one the repo cites. The baseline pointer should be repointed.

---

## 8. What this audit does not establish

- No Lean. The composition (source lemmas ⇒ 32) is not formalized by anyone; PR #27 formalizes the algebra with those lemmas as hypotheses.
- No verification of the source's own asymptotic machinery (generic-grid extraction, negligible-height passage, private valuations, Kummer). Those are taken as hypotheses, exactly as the row states.
- No literature-priority claim. Whether `j=4` was noticed earlier is not addressed here.
- Arm D's algebra checks use symbolic `p` against three random exact-rational anchor sets, not a fully symbolic anchor family. A contradiction would have been found; a proof it is not. Combined with PR #27's kernel-checked version, the risk is low.

---

## Reproduce

From this package directory:

```
pip install sympy==1.14.0
git clone https://github.com/rohanarun/unit-distance-grid-refinement repo
git -C repo checkout 62455a6
python3 -B verify.py --skip-mutation   # arms A,B,C,D,F: ~2 s
python3 -B verify.py                   # adds the mutation arm: ~5 min
```

`verify.py` writes `evidence/independent-recompute.json` and exits 0 iff arms A–D and F reproduce. The mutation arm reports; it does not gate, because its purpose is to *measure* the checker, not to be the checker. The audited clone is read only; the mutation arm works on temporary copies.

Arms A, B, C (partly) and F are standard library only. Arm D needs `sympy`. Findings are printed at the end of the run and collected in `data/findings.json`, with the recommended record-page annotations.

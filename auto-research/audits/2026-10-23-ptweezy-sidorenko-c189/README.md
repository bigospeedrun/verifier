# Audit: the Sidorenko nondirect residual constant C ≤ 189

The finite computation behind the Sidorenko row leader's residual constant
recomputes exactly. An independent implementation, written from the
source's written definitions, rebuilds the 28-pair allowed graph from the
saved faces and cut bits, re-derives the degree sequence
`(3, 6, 3, 6, 4, 2, 4, 4, 4, 6, 4, 6, 4)`, and exhausts all **8,192**
supports and **55,173** relaxed defect-one strata in exact integer
arithmetic. The maximum relaxed remainder is

```text
189 = 262 - 84 + floor(23/2),
```

attained only on the full support, at spans 49 through 55, with every
local dimension at or one below full rank — matching the source's closed
form. The defect ≥ 2 ratio bound is exactly **122**. So the finite maximum
behind `C ≤ 189` is **confirmed exactly**: the relaxed maximum equals 189,
neither less (the bound would be improvable by this count) nor more (the
claimed bound would fail). The source's sequential counting argument that
reduces the residual exponent to this finite maximum, the upstream
orbit-counting transfer, and the Sidorenko counterexample itself remain
outside this computation. This package supplies no Lean proof and does
not change the site's evidence level.

## Pins and selection

- Verifier base: `106c0f1b12f14c2dc735e7c35636e94a382fe858`.
- Claim source: [`rohanarun/sidorenko-template-refinements` at
  `5ca68cb81cfcd7f1b32102b93e186b2b51d5e2f8`](https://github.com/rohanarun/sidorenko-template-refinements/tree/5ca68cb81cfcd7f1b32102b93e186b2b51d5e2f8),
  `sequential-refinement.md` and `proof.tex` (section "Sequential basis
  count for the nondirect residual", Lemma `lem:sequential-accounting`,
  Proposition `prop:residual-189`). Per-file SHA-256 pins are in
  `data/source-pins.json`.
- Site snapshot: the [Sidorenko row](https://bigospeedrun.com/other/sidorenko)
  read 2026-10-23 lists the bound **189** as rank 1, **Claimed**, dated
  Oct 9, with proof scope "No Lean proof is supplied", and describes the
  quantity as "the nondirect residual constant C in the exponent −D + C …
  an internal proof step, conditional on transfer within the source
  orbit-counting argument". The OpenAI baseline on the row is 1641.
- Overlap check (2026-10-23, via the GitHub connector at the base commit):
  the audits track on main contains only the two 1337isnot1337 packages
  (block-sensitivity, matroid); no open or closed pull request and no
  issue in the verifier mentions Sidorenko; the code search hits are the
  track READMEs listing the row. No other audit of this constant exists
  or is in flight.

## The claim, pinned exactly

The quantity is the nondirect **residual constant** `C`: within the
source's nondirect residual stratum, the contribution is
`O_D(q^(−D + C))` for fixed even `D ≥ C`, and the stratum vanishes for
even `D ≥ C + 1`. Proposition `prop:residual-189` claims `C = 189` is
achievable (so `C ≤ 189` for the optimal constant). The counting reduces
the exponent, for defect `d = Σᵢ kᵢ − 2k`, to `−Dd + R`, where the finite
content of the claim — the part this audit recomputes — is:

- Let the 13-point complex have faces and 3-bit cut vectors as saved in
  the source's `experiments/original-baseline.json`. A pair `{i, j}` is
  **allowed** when it lies in exactly two faces whose cut vectors differ
  in exactly one coordinate. The allowed graph has 28 pairs and the
  degree sequence above, and is connected.
- With `φᵢ(x) = C(x, 2) + (2δᵢ − x)x` (δᵢ the active degree), a **relaxed
  defect-one stratum** is a support `S` whose induced allowed subgraph has
  a pair and no isolated vertex, a span `k ≥ 2`, and local dimensions
  `2 ≤ kᵢ ≤ min(k, 2δᵢ)` with `Σᵢ kᵢ = 2k + 1`. Its relaxed remainder is
  `⌊( max Σᵢ φᵢ(kᵢ) + pair_excess ) / 2⌋ − 2m`, where `m` is the number of
  active pairs in `S` and `pair_excess` is the maximum of
  `min(k, 2δₐ) + min(k, 2δ_b) − 1` over active pairs `{a, b}`.
- **Finite claim:** the maximum of the relaxed remainder over all
  supports and spans is exactly 189 (= `Σᵢ δᵢ² − 3m + ⌊23/2⌋`
  `= 262 − 84 + 11`), attained only on the full support; and the
  defect ≥ 2 analogue `R ≤ 178 + (23/2) n₁ + (k + 11) n₂` (with
  `d = n₁ + 2n₂`, `k ≤ 55`) gives `R/d ≤ 122 < 189`, so defect one is
  the binding case.

The reduction itself — the sequential accounting lemma, the inequality
`π ≤ (v′ᵢ + v′ⱼ)/2`, the per-vertex bound `Σₓ v′ᵢ(x) ≤ φᵢ(kᵢ)`, and the
passage from the strata bound to the exponent — is a written argument in
the source (it replaces the counting step behind the earlier constants
1641, 1032 and 978). This audit covers the finite computation only,
exactly as the block-certificate audit covers that paper's equation (12):
a faithful, independent, exact recomputation of the finite maximum the
written argument delegates to enumeration.

## What is taken as given

- **The complex data**: the 22 triangular faces and 22 cut vectors in
  `data/baseline-faces-bits.json`, extracted from the pinned source file
  above (SHA-256 of the original file recorded in `data/source-pins.json`).
  The audit checks this data's internal consistency before counting: it
  is a closed triangulated sphere (every pair of points sharing a face
  lies in exactly two faces; 33 such pairs; Euler characteristic
  `13 − 33 + 22 = 2`), and the file's own redundant `pair_separations`
  record agrees with the faces and bits on all 33 pairs. That the data is
  the complex of the source's construction is upstream's assertion, not
  re-derived here; the original complex table is pinned in the source
  repo to `openai/math@fd4aeeb`.
- **The written reduction** described above (source's proof), inspected
  to extract the finite claim, not formally verified.

Everything downstream of the faces and bits — the allowed graph, degrees,
the identity `Σᵢ δᵢ(2δᵢ − 1) = 468 = 2·262 − 2·28`, the closed form, all
55,173 stratum values, the maximum and its attainment set, and the ratio
bound — is re-derived by this package's own code.

## Method

`code/sidorenko_audit.py` is an independent implementation (standard
library only), written from the definitions above. It does not run,
import, or adapt the author's `audit_sequential.py`. Each stratum's local
maximum `max Σᵢ φᵢ(kᵢ)` is computed by an integer dynamic program and
independently certified two further ways — a marginal-gain greedy
allocation (exact because `φ(d, ·)` has nonincreasing integer marginal
gains `2d − x − 1`) and a Lagrangian dual bound minimized over integer
`λ` — with brute-force enumeration of all compositions wherever the
composition count is small. The scan over spans `k ∈ [2, 2m]` is complete:
feasibility forces `2k + 1 ≤ Σᵢ min(k, 2δᵢ) ≤ 4m`, so `k ≤ 2m − 1` in
every feasible stratum. Before the full run, the implementation is
validated on hand-computed small graphs (the path on three vertices has
exactly one feasible stratum, remainder 2, matching its closed form; a
single pair admits none; a triangle is brute-forced directly), on the
per-vertex concavity bound for all degrees ≤ 30, and on 4,000 random
small allocation instances (47,979 brute-force comparisons). During the
audit run reported in `evidence/audit-results.json`, all 55,173 strata
were covered by triple-checked allocation values (10,326 distinct
`(items, total)` problems, 2,900 of them also brute-forced), with no
disagreement. Total wall time was 46.5 s on a 2-core machine, including
controls.

As a final cross-check, the author's own `audit_sequential.py` was run
once, separately, during the preparation of this audit: it reproduced the
author's saved `experiments/sequential-expected.json` exactly, and the
independent recomputation agrees with it on every reported field (allowed
pairs, degrees, 468, 178, 23, 189, 8,192, 5,468, 55,173, the seven
maximizers, and the ratio 122). The author's script is not part of this
package and is not run by its verifier.

## Results

| Quantity | Source | This audit |
| --- | --- | --- |
| Allowed pairs | 28 | 28 (identical list) |
| Degree sequence | (3,6,3,6,4,2,4,4,4,6,4,6,4) | identical |
| `Σᵢ δᵢ²` | 262 | 262 |
| `Σᵢ δᵢ(2δᵢ − 1)` | 468 | 468 |
| Base remainder | 178 | 178 |
| Max pair excess | 23 | 23 |
| Closed form | 189 | 189 |
| Supports scanned / without isolates | 8,192 / 5,468 | 8,192 / 5,468 |
| Relaxed defect-one strata | 55,173 | 55,173 |
| Finite maximum | 189 | **189** |
| Attained at | full support, spans 49–55 | full support only, spans 49–55 (7 strata, local φ sum 468, pair excess 23) |
| Defect ≥ 2 ratio bound | 122 | 122 exactly (attained at d = 2, n₂ = 1, k = 55); also verified for all d ≤ 100,000 |

**Verdict: `C ≤ 189` CONFIRMED for the finite computation.** No
discrepancy, in any field, was found.

## Reproduce offline from a fresh clone

From the repository root, with Python 3 and its standard library only:

```bash
python3 -I -B auto-research/audits/2026-10-23-ptweezy-sidorenko-c189/verify.py
```

Expected output:

```text
PASS: input complex consistent (13 points, 22 faces, closed surface, Euler characteristic 2, separations agree)
PASS: allowed graph rebuilt: 28 pairs, degrees (3, 6, 3, 6, 4, 2, 4, 4, 4, 6, 4, 6, 4), connected
PASS: closed form 262 - 84 + floor(23/2) = 189
PASS: 8192 supports scanned, 5468 without isolates, 55173 relaxed defect-one strata exhausted
PASS: finite maximum 189 attained only on the full support (spans [49, 50, 51, 52, 53, 54, 55]), matching the closed form
PASS: allocation agreement (dynamic program = greedy = dual certificate on 10326 distinct problems; brute force on 2900 of them plus 47979 random small instances)
PASS: defect >= 2 ratio bound 122 exactly (author's grid and extension to d <= 100000)
PASS: negative controls (wrong bound 190, flipped cut bit, dropped face, changed graph)
SCOPE: finite computation only; the sequential counting argument, the orbit-counting transfer and the counterexample theorem remain outside, and the evidence level remains Claimed
```

Validated with Python 3.12.3. The verifier re-runs the full enumeration
(about a minute on two cores), checks the package inventory against
`MANIFEST.json`, and runs the negative controls: an expected maximum of
190 is rejected by the comparison, a flipped cut bit (with the redundant
separations updated to match) changes the allowed graph, a dropped face
is rejected by the input consistency checks, and the stratum count is
sensitive to the graph (path vs triangle). No floating-point arithmetic
is used anywhere in the package; the only divisions are exact integer
floor divisions and `Fraction` ratios.

## Open obligations and interpretation

| Dependency | What this audit checks | What remains outside the computation |
| --- | --- | --- |
| Faces and cut bits (baseline data) | Internal consistency: closed triangulated sphere, χ = 2, separations record agrees on all 33 pairs | That this is the source construction's complex (pinned upstream to `openai/math@fd4aeeb`) |
| Sequential accounting lemma (source) | The finite definitions extracted from it match the enumeration's domain (defect, spans, caps `min(k, 2δᵢ)`, `kᵢ ≥ 2`) | The lemma's proof, the type-counting identities, the inequality `π ≤ (v′ᵢ + v′ⱼ)/2` |
| Relaxation to the finite maximum | Exact recomputation of the maximum, its attainment set, and the ratio bound, by three independent allocation methods | That no stratum outside the relaxed domain (e.g. other activity data) contributes |
| Orbit-counting transfer (source) | Nothing | The passage from this residual bound to the counterexample with 35 vertices and 66 edges |
| Proposition `prop:residual-189` | Its delegated finite computation, in full | The proposition as a whole, and the remaining dimension thresholds of the full construction |

This finding is **neither a counterexample nor a missing-proof finding**:
it is a passed audit of the finite computation. It does not certify the
analytic argument, does not supply a Lean proof, and does not by itself
change the row's evidence level. No failed check, discrepancy, or
impossibility result was found in this finite scope.

See `NOTICE.md` for credits, license, and AI assistance. Publication
remains a separate maintainer review step; this is an audit package, not
a proof submission.

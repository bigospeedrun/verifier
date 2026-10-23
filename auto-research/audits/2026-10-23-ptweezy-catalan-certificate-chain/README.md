# Audit: the Catalan-exponent certificate chain behind μ(G) < 2401.741

The full finite-certificate chain behind the certified bound **μ(G) <
2401.741** for the irrationality exponent of Catalan's constant
re-derives at certification standard. Every finite or numerical link
was recomputed by an independent implementation — exact rational
arithmetic for the algebraic links, two-sided interval enclosures for
the analytic ones — and the final assembly, float-only in the source,
was redone in interval arithmetic. The rigorous enclosure obtained is

```text
mu(G) <= 2401.7409911295751174   (enclosure width below 1e-18),
```

which is `< 2401.741` with slack `8.87e-6`. Per link: the design
arithmetic, the structural checks (6,174 counting-identity cases; the
23-prime valuation table, computed by two independent methods), the
(C3) nonvanishing (three methods, plus the paper's published Table 1
reproduced exactly as a positive control), the exact loss integral
`4825/2` (with the two independent exact controls `8609/2` and
`17114`), and the (C4) real-place certificate for both witness files
(margins `0.0025290538493618046…` and `0.0021839479954266481…`, both
strictly positive) all **re-derive**. One presentation discrepancy,
stated exactly in §6: the source README's headline `mu(G) < 2401.74`
is **not** supported by its own certified value `2401.740991131532`
(it exceeds `2401.74` by `9.91e-4`); the supported decimal bounds are
`< 2401.741` and `< 2402`. The written theorems that consume the
finite chain (the general design theorem and the minor/exponent
machinery) are taken as given, as is standard for this track; the
~2100 figure and the equilibrium ceiling are measurements, not part
of the certified chain, and are recorded as such.

## Pins and selection

- Verifier base: `106c0f1b12f14c2dc735e7c35636e94a382fe858`.
- Audited package: [`fringewidth/catalan-exponent` at
  `0e4877172b313a04da51c972ac91348f071b8481`](https://github.com/fringewidth/catalan-exponent/tree/0e4877172b313a04da51c972ac91348f071b8481)
  — design `(36, 6, 2, 3, 2)`, its `README.md`, `RESULT.json`, and the
  saved scripts and outputs under
  `certificates/cert_36_6_2_3_2/`. Per-file SHA-256 pins for every
  bundled input are in `data/SOURCES.json`.
- Written source: [`MarcosCarreira/catalan-designs` at
  `ec231b32f94cc3ec6a3e61b717b264f8382bb4ac`](https://github.com/MarcosCarreira/catalan-designs/tree/ec231b32f94cc3ec6a3e61b717b264f8382bb4ac)
  (the commit the audited package itself pins), in particular
  `paper/catalan_design_extension.tex`: definitions `def:det`,
  `def:fixed`, `def:loss`, `def:upper`; Theorem `thm:main`; Corollary
  `xcor:massminors`; Theorem `xthm:exponent`; Table 1. (That repo's
  newer HEAD advertises a version-2 claim μ(G) < 2294; it is not the
  audited object and was not used.)
- Site snapshot: the [Catalan row](https://bigospeedrun.com/other/catalan)
  read 2026-10-23 lists Carreira at rank 10 with `< 2715` (Claimed,
  "no Lean proof is supplied", "the estimate near 2100 comes from
  measurements, not a proved bound"), and its Relevant repos line
  credits the audited package: "Carreira's theorem with a smaller
  design gives μ(G) < 2401.741; search and certification by Claude."
  All Catalan rows are Claimed.
- Overlap check (2026-10-23, via the GitHub connector at the base
  commit): the audits folder on main contains only the two
  1337isnot1337 packages and this track's own Sidorenko audit is a
  pull request, not merged; open PRs are #52, #51 (Sidorenko audit),
  #50, #21, #12. PR #21 is a lean-*statement* for Catalan's exponent
  — a different lane, not an audit. No Catalan audit exists or is in
  flight; code and issue searches for "catalan" return only the track
  READMEs and the matroid package.

## The claim, pinned exactly

Catalan's constant is `G = sum_{k>=0} (-1)^k / (2k+1)^2`. Its
irrationality exponent `μ(G)` is the infimum of the exponents `μ`
such that `|G - p/q| < q^{-μ}` has only finitely many rational
solutions; a certified upper bound on `μ(G)` is in particular a proof
that `G` is irrational. The audited claim is the exponent bound
obtained by instantiating Carreira's minor bound (Corollary
`xcor:massminors`) and exponent theorem (`xthm:exponent`) at the
design `(n0, b0, q0, g0, h0) = (36, 6, 2, 3, 2)`:

```text
mu(G) < 2401.741.
```

`2401.741` is a decimal threshold, not an interval endpoint produced
by the computation: the source's own assembled value is the float
`mu_upper = 2401.740991131532` (its `RESULT.json`), which clears the
threshold by only `8.87e-6`, so a rigorous re-derivation has to
produce an actual enclosure below `2401.741`, not just reproduce the
float. This audit's enclosure is
`[2401.7409911295751173, 2401.7409911295751174]`.

The chain, as an explicit list of links. The design satisfies the
paper's four conditions (C1)–(C4) of Theorem `thm:main`; (C4) supplies
a certified margin `γ > 0`; the minor bound and exponent theorem then
assemble `γ` into `μ(G)`. With `α = (b0+q0)/n0 = 2/9`,
`γg = g0/n0 = 1/12`, `γq = q0/n0 = 1/18`, `η = h0/n0 = 1/18`,
`ν = 1 − γg = 11/12`, and `Σκ = sup X + sup Y` for the functions of
`def:upper`:

- **L1 — design arithmetic.** Derived quantities
  `a0=8, L0=44, C0=47, H0=49, A0=14`; (C1) `2g0 = 6 < 35 = n0−1`;
  (C2) `2b0 = 12 < 49 = H0`; certification prime `P = 53`, the
  smallest prime `> H0`; the Jha Lemma 4.3 instantiation hypotheses
  (`n = 36N ≥ 48` for `N ≥ 2`; `D* = 30N − 1 ∈ (0, n]`).
- **L2 — structural checks.** The Lemma 3.3 counting identity
  `R0 = R` for the scaled designs `N = 1..60` and every prime
  `H/2 < p ≤ H`; row supports in `[A0, H0−1]`; the `ζ(2)` coefficient
  of every raw entry exactly `0`; and the end-to-end per-prime
  valuation check at `N = 1` with hypothetical value `G = 1/3`:
  `−v_p(det Δ₁) ≤ D_L(p)` for `2√H0 < p ≤ H0`, `v_p ≥ 0` for
  `H0 < p < H0 + 60`.
- **L3 — (C3) nonvanishing.** The fixed rational matrix `B`
  (`def:fixed`, `(n0+1) × n0`); `det B0`, `det(B0+B1)`, `det(B0−B1)`
  all nonzero over ℚ, via denominators with primes `≤ H0 < P` and the
  paper's elimination rule mod `P`.
- **L4 — the lower constant `F_low`.**
  `F_low = −(1/n0²)∫₀^{H0} D_L − (1/2 + δ/2 + δ²/8)·log 2` with
  `δ = (q0+g0+h0)/n0 = 7/36` and `D_L` the piecewise-linear loss of
  `def:loss`; the finite content is the exact integral `∫ D_L`.
- **L5 — (C4) the real-place certificate.** Two exact-rational
  witness files (trial sequences `p^(κ), v^(κ)` and `λ^(κ)`,
  `κ ∈ {2, 1}`) and the rigorous bounds
  `U_κ = (−1+α+γg)·log 2 + κ‖p‖² + ‖v‖²/2 + sup X + sup Y
        < F_low`, i.e. margins `γ = F_low − max(U₁, U₂) > 0`. The
  witnesses are data; their float-optimisation provenance is not
  soundness-bearing.
- **L6 — assembly.** `ρ₁ = (2−α−γg)·log 2 − Σ₂ + 2·log 2`
  (case-1 coefficient; `Σ₂` at its *lower* bound), the second-case
  coefficient `(2−α−γg)·log 2 − Σ₁ − λ⁽¹⁾(1−2γg) + (3/2)·log 2 ≤ ρ₁`
  together with `U₁ − U₂ ≤ 0` (case 1 dominates on `[0,1]`),
  `ρ₂ = ρ₁ + (η+γq)·log 2 + ν·log(1+√2)`, and
  `μ(G) ≤ ρ₂·(ν/γ + n0)` with `γ` at its certified *lower* bound
  (`μ` decreases in `γ`).

## Verdicts

| link | verdict |
|---|---|
| L1 design arithmetic, (C1), (C2), prime, hypotheses | **RE-DERIVED (exact)** |
| L2 structural: counting identity, supports, ζ(2), valuations | **RE-DERIVED (exact)** |
| L3 (C3): B, determinants, pivots, Table 1 control | **RE-DERIVED (exact)** |
| L4 integral of `D_L` | **RE-DERIVED (exact)** |
| L4 `F_low` value | **RE-DERIVED (rigorous enclosure)** |
| witness files as data | **TAKEN-AS-GIVEN (named, consistency-checked)** |
| witness generation (float optimisation) | **MEASURED-ONLY** (not soundness-bearing) |
| L5 (C4): `U_κ`, suprema, norms, margins | **RE-DERIVED (rigorous enclosure)** |
| L6 assembly to `μ(G)` | **RE-DERIVED (rigorous enclosure)** |
| Theorem `thm:main`, Props. 3.4/6.1 as generalised, Corollary `xcor:massminors`, Theorem `xthm:exponent`, Jha's lemmas | **TAKEN-AS-GIVEN (written mathematics, named)** |
| equilibrium ceiling `0.00262`; the ~2100 measurement | **MEASURED-ONLY** (context, not in the chain) |
| source README headline `mu(G) < 2401.74` | **DISCREPANCY** (presentation only; §6) |

Chain verdict: **the certified bound μ(G) < 2401.741 is confirmed** —
every finite/numerical link re-derived at certification standard,
with the written mathematics above taken as given.

## Per-link results

**L1.** All arithmetic checks pass exactly. The claimant's saved
certification modulus is `53` (in `cat_cert4_new_out.json`),
agreeing with the audit's determination; the claimant's
`RESULT.json` records the prime as `null` (§6).

**L2.** Counting identity: **6,174** `(N, p)` cases, **0** failures.
Row supports inside `[14, 48]` for rows `0..35`. `ζ(2)` coefficients:
**0** in all **1,406** raw entries (rows `0..36`, shared with L3).
Valuations of the single exact determinant `det Δ₁ ≠ 0` at the **23**
primes `17 ≤ p ≤ 109`: every bound holds, the bound `−D_L(p)` is
attained exactly at 5 primes (`p = 17, 31, 37, 41, 47`), all
`v_p = 0` above `H0`; a fraction-free p-adic elimination
independently reproduces every valuation. All 23 rows agree with the
claimant's saved table.

**L3.** `B` was rebuilt from `def:fixed` (binomial assembly; the
successive-difference assembly agrees entry for entry). Largest
denominator prime **47** `≤ H0 = 49 < 53`. (C3) three ways: (a) the
paper's elimination rule mod 53 — all 36 pivots nonzero for each
`σ ∈ {0, 1, −1}` (swaps `(19,20)`, `(14,15)`, `(12,13)`), matching
the claimant's saved pivots exactly; (b) exact rational determinants
(Bareiss), all nonzero (`|det|` of order `10^127`, `10^139`,
`10^143`); (c) full rank 36 mod 59, 61, 67 as well. Positive control:
the preprint design `(48, 7, 4, 4, 2)` mod 101 reproduces the paper's
**Table 1 exactly — all 144 pivots and the swaps `(30,31)`, `(45,46)`
at `σ = +1`** — with `ζ(2)` failures 0/2,548 and largest denominator
prime 61 ≤ 65. This control is what pins the `M⁰/Z⁰` recipe (the
claimant's implementation of the preprint's Eqs. (14), (16), (17);
the preprint itself is not among the pinned sources) to published
data.

**L4.** Exact integrals by an independent breakpoint integrator
(every linear piece verified at three interior rational points;
168 point checks for the audited design): `∫D_L = ` **4825/2** for
`(36,6,2,3,2)`; controls **8609/2** for `(48,7,4,4,2)` (the
claimant's pre-registered control value) and **17114** for
`(96,15,6,8,5)` (implied by the paper's printed
`F_low = −8557/4608 − (44521/73728)·log 2`, whose rational parts the
audit also reproduces exactly). Hence the rigorous enclosure
`F_low ∈ [−2.2787356822795735606, −2.2787356822795735606]`
(width `6e-61`; `F_low = −4825/2592 − (6241/10368)·log 2`). The
claimant's printed lower endpoint agrees with this enclosure to
`2.2e-20` — its own 20-digit print rounding.

**L5.** Both witness files validated as data (design header, exact
`|z| < 1` for every tail base, conjugation closure, coefficient
counts 72 and 46 per sequence, denominators dividing `10^20`,
`λ⁽²⁾ = 0`, `λ⁽¹⁾ ≥ 0`; 80/80 and 54/54 checks). The certificate was
then rebuilt from `def:upper`: exact derivative numerators over
`ℚ(i)` (degrees `(A_X, Q_X, A_Y, Q_Y) = (131, 116, 73, 58)` for the
edges file at `κ=2`, matching the saved degrees everywhere);
Descartes/VCA isolation of **all** stationary points (edges: X 34,
Y 37 at `κ=2`; X 32, Y 37 at `κ=1`; opt: 31/23 and 19/21 — all
matching the saved counts), refined to brackets of width `2^-50`;
two-sided sup enclosures at 60-digit interval precision
(mean-value allowances `≤ 4.2e-22`, enclosure widths `< 1e-30`);
closed-form-vs-numerical derivative agreement `≤ 5.2e-42`
(numdiff) and `≤ 2.5e-148` (closed form); dense-grid controls pass.
Results (upper endpoints; the audit's enclosures are two-sided and
agree with the claimant's saved endpoints to `≤ 5e-20`, their print
rounding):

```text
edges certificate:  U_2 <= -2.2812647361289353652   (margin-bearing)
                    U_1 <= -2.4192376465502577698
                    gamma = 0.0025290538493618046...
opt certificate:    U_2 <= -2.2809196302750002088
                    U_1 <= -2.4188005162167882565
                    gamma = 0.0021839479954266481...
```

Both margins are strictly positive with rigorous lower bounds, so
`(C4)` holds for both certificates; the edges certificate (larger
margin) is the one the assembly uses. Two-sided `Σ` bounds come from
the pointwise ends of the same enclosures
(`Σ₂ ∈ [−2.5819075722983992776, …]`, `Σ₁ ∈
[−2.9926646333664426519, …]`), with no fudge factor anywhere; the
source's convention `Σ = (sup upper sums) − 1e-12` was checked to be
a valid, weaker lower bound (its values lie `1.000e-12` below the
audit's `Σ` lower bounds, consistent with the certified allowances
`≤ 4.2e-22`).

**L6.** Interval assembly (all inputs the audit's own enclosures;
`λ⁽¹⁾ = 4156881441966137/1525878906250000` exact):

```text
rho1   <= 5.1427013227004194485
second-case coefficient <= 2.9366732753160505478 <= rho1   (dominance holds)
U_1 - U_2 <= -0.13797291042132240461 < 0
rho2   <= 6.0276434641972167004
mu(G)  <= rho2 * (nu/gamma + 36) <= 2401.7409911295751174 < 2401.741.
```

As a consistency check on the reading of the source's assembly, the
source's own float computation (`mu_cert.py`/`package.py` formulas,
the claimant's printed inputs) was reproduced in floats and returns
its `RESULT.json` values **exactly** (`rho1 5.14270132270142`,
second `2.936673275317051`, `rho2 6.027643464198217`,
`mu 2401.740991131532`; difference `0.0`). The rigorous values sit
below the float ones by `≈1.000e-12` in `ρ₁`, the second coefficient
and `ρ₂` (the source's `Σ − 1e-12` convention) and by `2.0e-9` in
`μ` (additionally the source's `γ` is the 12-digit rounded-down
margin) — the float assembly is mildly conservative throughout, and
the claim survives its replacement by enclosures.

## Discrepancies and documentation defects (exact statements)

1. **Headline bound.** The audited package's README headline reads
   "mu(G) < 2401.74". Its own certified value (and this audit's
   enclosure) is `2401.7409911…`, which exceeds `2401.74` by
   `9.91e-4`. The statement `mu(G) < 2401.74` is therefore **not
   supported**; `mu(G) < 2401.741` (the site line and the task's
   claim) and the README's own secondary statement `mu(G) < 2402`
   are supported. Presentation only; no number in the chain is
   affected.
2. **`RESULT.json` prime field.** The claimant's `RESULT.json`
   records `"prime": null`; the modulus actually used is `53`,
   recorded in `cat_cert4_new_out.json` and confirmed by this audit.
3. **Stale template text in `cat_cert4_new.py` / its table.** The
   script's docstring and the generated `cat_cert4_new_table.tex`
   caption describe the design `(96,15,6,8,5)` and pivots in
   `F_131`; the fringe run's actual parameters are `(36,6,2,3,2)`
   mod 53, and the table's printed pivot values are indeed the
   mod-53 ones (all `≤ 52`, matching this audit's computation).
   Text only.
4. **`scripts/certify.py` is not runnable in the fringe layout**:
   it reads sources from `../src/new_design`, a directory the
   fringe repository does not contain. The runnable artifacts are
   the parametrised scripts inside `certificates/cert_36_6_2_3_2/`
   (used for the cross-check below).
5. **Equilibrium gate E1.** The claimant's saved equilibrium run
   for this design ends with `GATE_FAILS = 1`: gate E1 failed
   marginally (fine-minus-coarse dual `−5.30e-06`, tolerance
   `−5e-06`). The README's "certifiable-gap ceiling 0.00262" comes
   from that run's bracket `[0.0025290538…, 0.0026200509…]`. The
   equilibrium computation is a float diagnostic, not a link in
   the certified chain; the certified margin
   `0.0025290538493618046…` lies inside the bracket, and nothing in
   the chain depends on the bracket or on gate E1.

## Taken as given, and measured-only items

Taken as given (written mathematics, named; the audit verifies the
finite computations that instantiate them, not the proofs):
Theorem `thm:main` — that (C1)–(C4) imply the irrationality argument
of the OpenAI preprint goes through for a general design — including
Propositions 3.4 and 6.1 of the preprint in the generalised form
used here (the claimant's certifier prints the same scope note:
this generalisation "still needs a written proof" as a separate
write-up; the paper's §2 supplies the design-by-design verification
argument, which this audit does not re-verify); the `M⁰/Z⁰` arrays
as the claimant's implementation of the preprint's Eqs. (14), (16),
(17) — pinned instead by the Table 1 control, the `ζ(2)`
cancellation, and cross-method determinants (L3); Corollary
`xcor:massminors` and Theorem `xthm:exponent`, including their
asymptotic hypotheses (`N ≥ N_ε`, primes `p > 4H0`), whose
instantiation arithmetic is checked in L1; Jha's Lemmas 4.1–4.5
machinery as replaced by the paper's Lemmas `xlem:schur`,
`xlem:hardy`, `xlem:far`. The design itself is an input: the
45-minute float search that found it (1,352 designs in the source's
`search_results.jsonl`) is not part of the chain — any design
satisfying (C1)–(C4) would do.

Measured-only: the witnesses' generation by float optimisation
(grid suprema and L-BFGS-B in the source's tail scripts; the
outputs are exact-rational data and only the data is consumed);
the equilibrium bracket and ceiling `0.00262` (float FISTA dual
computation; §6.5); and the ~2100 figure (the source's Observation
37 determinant measurements near `G`), which the source itself
flags as measurement, not a proved bound.

## Method and controls

The audit's code (`code/`) is an independent implementation from
the written definitions in the paper: Gaussian-rational polynomial
arithmetic, an exact breakpoint integrator for `D_L` that
constructs each linear piece symbolically and verifies it at three
interior rational points, the `def:fixed` binomial assembly of `B`,
Bareiss determinants, a fraction-free p-adic valuation, a
Descartes/VCA root isolator, and mpmath interval arithmetic at 60
digits with two-sided sup enclosures. Controls: the paper's
Table 1 (positive control for the whole `B` construction); the two
independent exact integral controls (`8609/2`, `17114`); every
valuation by two methods; every determinant against the mod-prime
pivot rule; derivative numerators against numerical
differentiation and against independently written closed-form
derivatives; certified suprema against 200,000-point float grids;
and the source's float assembly reproduced exactly. As a final
cross-check, the claimant's own parametrised scripts were run
fresh in a scratch copy on this machine: all gates pass
(`GATE_FAILS = 0` for the structural, (C3) and (C4) scripts) and
their regenerated outputs are identical to the packaged saved
outputs (`evidence/claimant_crosscheck.json`). They are not an
input to any audit computation.

Coverage totals: 6,174 counting-identity cases; 23 valuation
primes (two methods each); 144/144 Table 1 pivots; 1,406 + 2,548
`ζ(2)` entries; for (C3), 6 pivot patterns, 6 exact determinants
and 21 modular ranks, plus 1 exact determinant and 23 p-adic
valuations for L2; 531 exact piece-point checks for the three
`D_L` integrals; 4 (witness, κ) certificates comprising 234
isolated stationary points, 4 derivative cross-check suites
(40 point checks), and 4 dense-grid controls; the full audit
runs in about 90 seconds on a 2-core box
(`evidence/run_log.txt`, `evidence/per_link_results.json`).

## Reproduce

```text
python3 -I -B auto-research/audits/2026-10-23-ptweezy-catalan-certificate-chain/verify.py
```

`verify.py` checks the package manifest and the data pins, re-runs
the entire audit from the bundled data (about 100 seconds), compares
the headline values against `evidence/per_link_results.json`, and
runs negative controls (a wrong expected bound, a tampered
`λ⁽²⁾`, a tampered witness coefficient, a wrong-design integral,
and a tampered `B` entry must each be detected). This package
supplies no Lean proof and does not change the site's evidence
level, which remains Claimed.

# Audit — binary polynomial multiplication over F2, `O(n log^{1301/1302} n)`, exponent chain and finite certificates

Row: **binary-polynomial-multiplication** — **`O(n log^{1301/1302} n)`** [Claimed],
Árpád Csizmadia (arpcs), [arpcs/finite-field-polynomial-multiplication](https://github.com/arpcs/finite-field-polynomial-multiplication)
@ `e85bc1f6ca0ec9c13281c94b6a3e88ec2cdb4fc5` (2026-11-01 19:52 PDT = the row's
"Nov 1, 7:52 PM PT" to the minute). Claim shape: `κ = 1/1302` in
`O(n log^{1-κ} n)` bit time on a deterministic Turing machine with a fixed finite
alphabet and a fixed finite number of one-dimensional tapes, all `2n-1` product
bits emitted, every transition charged (paper's Theorem 1 = `thm:main`, version 0.2.1).

**VERDICT: EXPONENT CHAIN AND FINITE CERTIFICATES VERIFIED — the paper's whole
exponent chain is reproduced in exact rational arithmetic from its own fixed
parameters, every monotonicity step runs in the safe direction, `g = 1/(2-t)` is
verified to be the exact balance optimum rather than an assertion, and both finite
certificate probes regenerate their published expected outputs byte-for-byte on a
non-Windows machine. No defect found in the arithmetic. Two notes for the records
page: (i) the row is *conservative* — the parameters support `κ ≈ 7.6834e-4` and the
rank-moment threshold is `N* = 1299`, while the row claims `1/1302`; (ii) the two
finite probes are the only machine-checkable artifacts in the package and they are
**Windows-only as shipped**: probe 1 fails closed (exit 2) and probe 2 does not even
compile off Windows, so a reviewer must apply the disclosed substitutions in `code/`
to check them. What this audit does NOT do: it does not verify the all-size proof,
which remains a written, unrefereed proof with no Lean formalization.**

Independence: Csizmadia is not the auditor. The auditor has no board row on this
problem. This is a community-lane audit in the shape of merged precedent
#97 / #102 / #124 / #138 / #177.

## Why this row is worth an audit

The row is the current leader on a problem where the tracked quantity is a
**Turing-machine log-exponent**, and its headline constant `1/1302` looks like a
rounding artifact. The audit question is therefore exact and narrow: *does the
paper's own fixed-parameter chain actually deliver `1301/1302`, or is the constant
asserted?* The known failure class is a flipped inequality that type-checks while
proving nothing, so every step below is tested for direction, not only for value.

## Checklist

| # | Item | Verdict | Evidence |
|---|---|---|---|
| 1 | Artifact pin | **PASS** | `e85bc1f6ca0ec` = the board's Nov 1 19:52 PDT timestamp; `CLAIM.json` declares `paper.pdf` sha256 `38a52af4…dac5` and the file at the pin hashes to exactly that (`evidence/pin.txt`). Upstream HEAD moved to `d95b709a` but does not touch `papers/03-best-binary`. |
| 2 | Statement ↔ board row | **PASS** | Theorem 1 (main.tex:118) states `O(n log^{1-1/1302}(n+2))` for *every* `n ≥ 1` on one machine with fixed finite alphabet / fixed finite sequential tapes, charging input+output conversion, setup, movement, restoration and all `2n-1` coefficients. `CLAIM.json` `problem.model` / `problem.cost` / `uniformity` match the problem page field by field (`evidence/board_statement.txt`). |
| 3 | The constant's origin | **PASS (found)** | `s0 = 1-1/1300` is not free: it is the threshold of the finite strict rank-moment inequality `Σ P_r r^{s0} < Σ T_k k^{s0}`. Independently recomputed threshold: holds at `N* = 1299`, fails at `1298`. So the `1300` is a rank count taken just above its own threshold. |
| 4 | Exponent chain, exact | **PASS** | Full chain recomputed as `Fraction`s (`verify.py` part A, 15 checks): `s0 = 1299/1300`, `u0 = 1300/1301`, `z = 3379999/3382600`, `d = 2601/3382600`, `t = z+d³ = 38673890304413527801/38703650883976000000`, `g = 1/(2-t) = 38703650883976000000/38733411463538472199`, `κ = 1-g = 29760579562472199/38733411463538472199 ≈ 7.6834387775e-4`. |
| 5 | Direction of every step | **PASS** | `u0-z = 1/3382600` exactly; `d = 2601/3382600` so `d³ < 1300^-3` reduces to `2601·1300 = 3381300 < 3382600` (true); `1300^-3 ≪ 1/3382600` by a factor 649; hence `t < u0` with 650 corrective units of slack; `2-u0 > 0`, so `t < u0 ⟹ 1/(2-t) < 1/(2-u0) = 1301/1302`. The reciprocal step is the only direction-sensitive one and it is not flipped. |
| 6 | The claim's direction | **PASS, conservative** | `g < 1301/1302` and therefore `κ > 1/1302`: the row asserts *less* than its parameters deliver (unused margin 0.038%). The failure class to exclude — a claimed `κ` larger than `1-g` — is excluded. Note the two distinct statements: at the paper's own `s0 = 1-1/1300`, `κ = 7.6834e-4 < 1/1301`, so `1/1301` would be false *as written*; but at the moment inequality's true threshold `s0 = 1-1/1299` the chain gives `κ = 7.6893e-4 ≈ 1/1300.5 > 1/1301`, so a **stronger row is reachable by changing one digit**. |
| 7 | Balance law `g = 1/(2-t)` | **PASS** | main.tex:338 sets `a = ⌈L^{1/(2-t)}⌉` to balance `O(V L a^{t-1})` against `O(V a)`. Substituting gives `L·a^{t-1} = a = L^{1/(2-t)}` exactly; both terms land on `L^g`. Perturbing the exponent is strictly worse, so `g` is the minimiser, not an upper bound chosen for convenience (`verify.py` part D). |
| 8 | Finite certificate, recomputed | **PASS** | `verify.py` part B reimplements the author's own directed dyadic scheme (2^48, outward rounding, 48 atanh terms + proved tail) in Python and reproduces every published number exactly: 10 per-rank interval rows, `paid_upper = 46549475589303981235`, `target_lower = 46549523863948677520`, `moment_den = 10133099161583616 = 36·2^48`, `strict_gap = 48274644696285 > 0`. A 120-digit true-value check gives relative margin `+1.037e-6`, so the sign is not a rounding artifact. |
| 9 | Certificate probes, executed | **PASS with substitution** | `bash code/reproduce_probes.sh <pinned paper dir>`: as shipped, probe 1 compiles under `clang++ -Wall -Wextra -Werror` and **refuses to run (exit 2)**; probe 2 **fails to compile** (`ExitProcess` undeclared, then `windows.h` not found). With the two disclosed POSIX substitutions both run in ~0.4 s and produce **byte-identical** output: 2012 bytes / sha256 `1811280d…f6e2` and 65933 bytes / sha256 `190900f9…1dc2`. The published expected outputs are not fabricated. |
| 10 | Scope honesty | **PASS (matches row notes)** | `CLAIM.json`: `independent_human_review: false`, `end_to_end_formal_proof_supplied: false`, `asymptotic_theorem_certified_by_finite_tests: false`, certificates cover "…and strict rank moment only", AI assistance "substantial" via OpenAI Codex. The row's proof-scope note on the site says the same. No inflation found. |
| 11 | Model comparison vs the `2^-38` row | **PASS, same quantity** | Both rows are the same author, repo, machine and cost measure, and both use the *same* balance law: the predecessor at main.tex:976 fixes `ε = 2^-36`, `γ = 1/(1+ε) = 1/(2-(1-ε))` and claims `δ = 2^-38`. Only the interchange exponent `t` changes (`1-ε` there, `z+d³` here). `κ` ratio `1/1302 ÷ 2^-38 = 2.1112e8`. The improvement is apples-to-apples — and, being one author and one lineage, is **not** independent corroboration. |

## The exponent derivation, recomputed end to end

```
s0 = 1 - 1/1300 = 1299/1300          finite rank moment holds here (threshold N*=1299)
u0 = 1300/1301                       = 1/(2-s0), first balance pass
z  = (s0+u0)/2 = 3379999/3382600     two movement bootstraps -> midpoint exponent
d  = 1 - z     = 2601/3382600
t  = z + d^3                         the pessimism term: d^3 > 0 makes t worse
     = 38673890304413527801/38703650883976000000
      t < u0  because d^3 < 1300^-3 < u0-z = 1/3382600   (slack factor 650)
g  = 1/(2-t) = 38703650883976000000/38733411463538472199  = the balance optimum
      g < 1/(2-u0) = 1301/1302
kappa = 1-g  = 29760579562472199/38733411463538472199 ~ 7.6834387775e-4  >  1/1302
```

Three things this chain establishes, and one it does not.

- The `1300` is **computed**: it is where `Σ P_r r^{s0} < Σ T_k k^{s0}` stops
  holding (`N* = 1299`, fails at `1298`). The exponent is a rank count, not a
  tuning knob.
- At the paper's chosen `s0 = 1-1/1300`, `1301/1302` is the **tight rung of the
  `1/k` ladder**: `κ = 7.6834e-4 < 1/1301 = 7.6864e-4`, so `1/1301` would be
  false *as written*. Rounding down to `1/1302` is exactly right for that
  parameter — not lazy. (But see D2: at the true threshold the row is one rung
  short of what is reachable.)
- The `+d³` correction is **pessimistic** (it weakens the bound) and still
  `650×` inside the gap it must not exceed — so the chain is not delicate.

## Discrepancies and notes — none invalidate the row

- **D1 — the finite certificates are Windows-only as shipped.** This is the one
  finding a records-page reader should know. `checks/bounded_chirp_process_limits.hpp`
  installs a Win32 job object and is a no-op elsewhere; both probes **fail closed**
  when it cannot be installed (probe 1 `return 2`; probe 2 a static `EarlyGuard`
  calling `ExitProcess(2)`). Independently, probe 2's transitive include of
  `four_bank_five_stage_word_bounded_20261030.cpp` does `#include <windows.h>` and
  `<psapi.h>` unconditionally, for a `guard()` function probe 2 never calls
  (`(void)&guard`). Consequence: **no Linux, WSL or macOS reviewer can reproduce the
  only machine-checkable artifacts in this package without editing them.** The
  substitution needed is 30 lines and is in `code/windows-guard-posix/`. Suggest the
  author move both probes to a `#ifdef _WIN32` guard plus a POSIX `rlimit` branch,
  or ship a Linux CI runner; that would make the certificates checkable by the
  community lane by default.
- **D2 — the row is one rung short of what its own certificate licenses.** The
  moment inequality holds at `s0 = 1-1/1299` (holds, gap `+7.89e-2`), not only at the
  paper's `1300`. Running the *same* chain at `N = 1299` gives
  `κ = 29646335589512201/38555076544413512201 = 7.6893468375e-4 ≈ 1/1300.5`, which is
  **greater than `1/1301`** — so a `κ = 1/1301` row (log exponent `1300/1301`) is
  supportable by changing one digit, and would be strictly stronger. With the
  parameter actually used, `1/1302` remains the tight integer rung. The published
  value is thus conservative in the safe direction by about one unit of the
  denominator. Reported as a note, not a defect — understating is not an error, and
  the row should not be changed on this audit's say-so.
- **D3 — notation collision inside the paper.** `θ` denotes the log exponent in
  main.tex (`θ = g`) and simultaneously the density defect `1 - D'/α'` in
  `appendices/outer.tex:417`. Both are legitimate and the contexts are disjoint,
  but a reader grepping `\theta` will conflate them. Suggest renaming one.
- **D4 — the absorption gap is `2.94e-7` in the exponent of `log N`, not of
  `log log N`.** `COST_LEDGER.txt` asserts "all remaining fixed secondary
  logarithms fit this gap". This is sound *only* if every secondary factor is a
  fixed power of `log log N` (or smaller), because `(log N)^δ` absorbs any fixed
  power of `log log N` for any `δ > 0`, but absorbs no positive power of `log N`.
  Spot-checks in `main.tex` and `appendices/outer.tex` show the right shape
  (`N·(log L0)^A`, i.e. `N·(log log N)^A`), and no counterexample was found — but
  this audit did not exhaustively scan every appendix for a stray `(log N)^C`.
  Recorded as an open obligation, not as a defect.

## Model comparison

The problem page tracks `κ` in a **worst-case deterministic Turing machine**
running time with a fixed number of tapes and a fixed alphabet, charging every
transition. `CLAIM.json` `problem.*` matches that description field by field, and
Theorem 1 repeats the machine restriction in the statement itself rather than in
prose. There is no switch to bilinear, algebraic or circuit complexity anywhere in
the claim (`evidence/board_statement.txt` has the side-by-side text). Two ways a row
usually weakens silently were checked and do not apply: the output is all `2n-1`
bits including zeros, and input copying / head returns / erasure are charged.

Against row 2 (`2^-38`, same author): same quantity, same machine, same balance
law, `κ` larger by `2.1112e8`. The audit confirms the *direction and comparability*
of the improvement; it cannot corroborate the mathematics, since both rows are one
author, one repository and one derivation lineage.

## Honest limits

This audit certifies **the exponent arithmetic and the finite certificates**. It
does **not** verify the all-size proof: the construction (paired Fourier phase
operators, mixed-rank job composition, the seed-derived interchange machine,
the native endpoint tensor and the CRT outer reduction) was read for the steps that
feed the exponent — `lem:movement`, `lem:endpoint`, the ordinary transfer, and the
parameter chain — but the appendices' tape-level simulations (A–G, ~160 kB of
`tex`) were **not** independently re-derived, and no simulation of the machine was
written. A gap in those appendices would not be caught here.

Specifically not covered, stated plainly:

- **The all-size theorem.** No formalization exists (`No Lean proof is supplied` on
  the site; `end_to_end_formal_proof_supplied: false` in `CLAIM.json`), and no
  independent human review has taken place. The row is Claimed and stays Claimed.
- **The recursive cost substitution.** That the outer recursion's log exponent *is*
  `θ = g` was checked at the balance step (`g = 1/(2-t)` is the exact optimum of the
  stated exchange cost) and at the absorption step, but the induction that carries
  `θ` through every appendix boundary was not re-proved.
- **The certificate logic.** Reproducing the output byte-for-byte proves the
  published numbers are real and compiler-independent; it does **not** prove the
  probe's own algebra is a correct model of the five-stage bank word or the
  rectangle partition. The probes' internal `need()` assertions are trusted.
- **The four other finite statements** (root geometry, binary fitting, five-stage
  bank identity, orthogonal rectangle partition) are covered only by probe 2's
  byte-identical reproduction, not by an independent re-derivation.

## Reproduce

```bash
# 1. the exponent chain + certificate arithmetic, stdlib only, ~1 s
python3 verify.py --expected-dir <pinned>/papers/03-best-binary/versions/0.2.1/checks/expected
# want: "checks run: 31 ; failures: 0" and "RESULT: PASS"

# 2. the two C++ probes, including the as-shipped Windows-only failure
bash code/reproduce_probes.sh <pinned>/papers/03-best-binary/versions/0.2.1
# want: exit 2 + "REFUSED: required job unavailable" (as shipped),
#       then BYTE_IDENTICAL twice (with the disclosed substitutions)
```

## File guide

| Path | Contents |
|---|---|
| `NOTICE.md` | attribution, independence statement, AI-assistance disclosure |
| `RESULT.json` | machine-readable verdict, pins, key numbers |
| `MANIFEST.json` | `{"algorithm":"sha256","sha256":{path:digest}}` for every file |
| `verify.py` | exact exponent chain, certificate recomputation, threshold search, balance law (31 checks self-contained, 36 against the author's file) |
| `code/reproduce_probes.sh` | builds and runs both C++ probes, as shipped and with substitutions |
| `code/windows-guard-posix/` | the two disclosed POSIX substitutions (rlimit guard, declarations-only Win32 stubs) |
| `evidence/pin.txt` | audited commit, file hashes, statement locations |
| `evidence/board_statement.txt` | board text vs `CLAIM.json`, field by field |
| `evidence/verify_output.txt` | full output of `verify.py` (31 checks self-contained, 36 with `--expected-dir`) |
| `evidence/probe_reproduction.txt` | as-shipped refusal + both byte-identical runs |
| `evidence/moment_threshold.txt` | the rank-moment scan that locates `N* = 1299` |

## This PR

**Title:** `Audit: exponent chain + finite certificates for the binary polynomial O(n log^{1301/1302} n) row (csizmadia @ e85bc1f6)`

Opened in the community audit lane per #97 / #102 / #124 / #138 / #177. Maintainers
may use this to annotate the row; suggested annotations are in `RESULT.json`
`records_page_annotations`.

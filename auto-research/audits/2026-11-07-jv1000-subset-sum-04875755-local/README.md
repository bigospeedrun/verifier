# Independent audit of the subset-sum 0.4875755 row (jv1000 @ 6026da70, rev8g)

**Verdict:** independently verified numerics — all 33 certified margins reproduce; the claim
remains conditional on the OpenAI + Base non-numerical lemmas exactly as the board row records.
No corrections needed to the board row.

- **Audited:** `jv1000/subset-sum` @ `6026da70f13d677b630cb1afd8fb10ee7a7f6010`
  (Theorem 1: conditional O(2^(0.4875755 n)), T = 0.4875754036; board exact score
  975151/2000000 = 0.4875755 > T, so the row value is valid).
- **Auditor:** MultiAgency agent (darkhipo), 2026-11-06/07; see `NOTICE.md` for independence
  and attribution.
- **What this audit is:** reproduction of the certified numerics at the pinned commit,
  perturbation tests proving the checker detects corruptions, and a from-scratch third
  recomputation sharing no code with the audited implementation. It is not a re-derivation
  of the inherited non-numerical lemmas (OpenAI + Base), which stay conditional premises.

## 1. Reproduction, exactly as instructed

`python3 -I certify_base.py candidate_base.json` in `exponent-2026/lab_notebook`
(python-flint 0.9.0 under `python3 -I`). Exit 0 in ~2.8 s, `all_pass: true`, all 33 margins
positive. Tightest: B3 8.12e-7, M1 1.3154e-6, C4 1.31567e-6, M2 1.4940e-6;
`T_ball = 0.4875754036`. Matches the paper's §8 table (rev8g, lines 389–408) value for value.
Raw output: `evidence/repro_run1.json`.

## 2. Perturbation tests (checker-failure detection)

The checker must reject corrupted parameters, not just accept good ones. Perturbed inputs are
in `evidence/perturb/`; outcomes:

| Perturbation | Outcome |
| --- | --- |
| rc[0] +1e-3 (`perturb_rc0.json`) | M1 margin −1.42e-5 — **detected** (moment path) |
| tau0 −1e-6 (`p_tau0_down_1e6.json`) | C5, eps0, M1, M2 negative — **detected** |
| tau0 −1e-5 (`p_tau0_down_1e5.json`) | 7 conditions negative — **detected** |
| gamma +1e-5 (`p_gamma_up_1e5.json`) | C1, eps0 negative — **detected** (scalar path) |
| tau0 +1e-9 (`perturb_tau0_benign.json`) | passes (benign control — checker is not a constant rejector) |
| tau0 −1e-7 (`perturb_tau0_down.json`) | passes; verified genuinely feasible (M1 margin 1.32e-6; d(log2 M1)/d(tau0) = p ≈ 8.46, so M1 first fails near −1.55e-7) |

Failure sets match analytically predicted sensitivities in all arms.

## 3. Independent recomputation, zero shared code

`verify.py` (this directory) recomputes **all 33 margins** from `candidate_base.json` using
only the stdlib `decimal` module at prec 60 (π via Machin, trig via Taylor series) — no flint,
no mpmath, no code shared with `certify_base.py`. Output: `evidence/independent_recompute.txt`.

- All 33 margins reproduce to 18 significant digits (worst relative difference 0.0).
- log2 M1 = 0.5162683258512851504377 and log2 M2 = 0.5162681472646696863911 — both inside the
  certified arb balls (±2.24e-21 / ±1.17e-21). q0 = 0.370835089416291 exact; U*, W* match.
- Doubled resolution (N_in = 512): log2 M1 / log2 M2 unchanged at 20 digits, as §8 claims.

## 4. Second in-repo implementation agrees

`astra_round8/interval_core.py` (mpmath interval arithmetic, dps 50, own FFT, "no supplied
numerical code used"): `moments_base_4096.json` stores the log2 M1 lower bound
0.51626832585128515043776… — same 20 digits. Three independent computations agree
(flint arb / mpmath iv / decimal).

## 5. Provenance

`sha256sum -c MANIFEST_5.sha256` → 465/465 OK at the pinned HEAD; `candidate_base.json` and
`certify_base.py` pinned unchanged since MANIFEST_2/3; `.ots` OpenTimestamps sidecars present.

## Scope check vs board model

- **Model:** paper §2 states the OpenAI paper's word-RAM model (success ≥ 2/3, b ≤ n^c,
  constant depends on c) — the board's model; Theorem 1 adds halting on every execution. The
  per-random-outcome time bound is inherited from the assumed OpenAI word-RAM accounting
  lemma, which the board row already lists among the unverified inherited lemmas.
- **Arithmetic:** tau0 + 20ε = 0.4875752036 + 2e-7 = 0.4875754036 (paper line 403); the 20ε
  slack is backed by the certified B3 condition (8.12e-7 < 1.5e-6). 0.4875755 > T, so
  O(2^(0.4875755 n)) is valid; board exact score 975151/2000000 = 0.4875755.
- **Conditionality:** Theorem 1 assumes only the non-numerical lemmas of OpenAI and Base — the
  same dependency structure the board records for the 0.487676 and 0.4876723 rows. The paper
  discloses the sine-extension of Base's filter lemmas as inherited/re-derived work, and
  discloses that ζ = 1e-8, guard = 1e8 push Base's Proposition P cutoff to n > 1e8 (Chebyshev
  term small only for n ~ 1e17) — constants are huge, and this is stated.
- **No Lean proof, not peer reviewed** — consistent with the row's Claimed level.

## Hardcoded-literal audit

- The certifier reads only raw parameters (tau0, eta, mu, a, gamma, l, kappa, p, q_m, eps,
  zeta, guard, rc, sc, n_terms) from the JSON. The JSON's `floating_margins` / `floating_T`
  display fields are never read by any certifier path.
- T is computed (tau0 + 20ε), not a literal. Reference constants (418.36 cap, JoshuaQFEX
  0.48767595, Base 0.48769) appear only in comparison outputs.
- rho_f/rho_c rules are literals in the script (eta − 1.5e-6, −1e-6) that match the JSON's
  declared rule strings and the paper table; a rule drift between JSON and script would not be
  caught automatically (minor hardening suggestion only).
- Certifier defaults N_in=256, c=32, β=0.1, σ=0.3 are load-bearing and live in the script, not
  the JSON or the §8 table; the quoted run command exercises them correctly.

## Honest limits

- The non-numerical lemmas of the OpenAI paper and of Base's written proof were **not**
  re-derived; the verdict is conditional on them exactly as claimed.
- The audited repo's per-round snapshot manifests and timestamps pin provenance; the audit
  checked integrity at HEAD (465/465) but did not verify the OpenTimestamps attestations
  against the Bitcoin calendar.
- The numerical verdict covers `candidate_base.json` as pinned; the paper's other certified
  points (0.4894616, Theorem 3's 0.4873407528 pending statement [S]) were out of scope.

## Reproduce

```
pip install python-flint
git checkout 6026da70f13d677b630cb1afd8fb10ee7a7f6010
cd exponent-2026/lab_notebook && python3 -I certify_base.py candidate_base.json
# third implementation (stdlib only, no flint):
python3 ../../auto-research/audits/2026-11-07-jv1000-subset-sum-04875755-local/verify.py candidate_base.json
```

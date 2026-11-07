# NOTICE

**Row audited:** subset-sum O(2^(0.4875755 n)) [Claimed] — Jennifer Voitle (jv1000),
`jv1000/subset-sum` @ `6026da70f13d677b630cb1afd8fb10ee7a7f6010` (2026-11-06, rev8g).

**Audit performed by:** an independent agent of the MultiAgency swarm (account `darkhipo`),
2026-11-06/07, in the community audit lane per merged precedent #97 (DFT), #102 (3SUM),
#124 (3SUM local replay), #138 (C-HD local replay), #177 (Catalan local replay).
jv1000 is not the auditor. The auditor holds **no** subset-sum board line of their own and
contributed nothing to the audited repository, so this audit has no competitive stake in its
outcome. (The auditor's prior contact with the subset-sum challenge is board infrastructure
only: trusted-statement PR #88, closed, which verifies the Lean statement, not any bound.)

**Attribution (from the audited repo's own disclosures, verified present):**
- Mathematics, paper (rev8g) and numerical certificate: Jennifer Voitle (jv1000).
  The repo states the work is AI-assisted under the author's direction; per-round snapshot
  manifests (`MANIFEST_*.sha256`, 465 files OK at HEAD) and OpenTimestamps `.ots` sidecars
  pin provenance.
- The algorithm is Base's (A. Kapila, `PROOF_0.4877`, commit `44c34961`) with a single
  asymmetric filter at new parameters; the certificate inherits the non-numerical lemmas of
  the OpenAI subset-sum preprint (isolation, alias lemmas, word-RAM accounting) and of
  Base's written proof. These inherited lemmas are conditional premises of the claim,
  disclosed as such in the paper and on the board row — the audit does not re-derive them.
- Prior conditional rows the paper compares against: J. Wharton 0.487676, Y. Bills 0.4876723
  (the Bills certification of the 430 Base moment premises was also used as a cross-reference).

**Honest limits of this audit:** the numerics are the audited object, and they were verified
by reproduction (flint arb), perturbation failure-detection, and a from-scratch third
recomputation (stdlib `decimal`, zero shared code). The non-numerical lemmas of OpenAI and
Base were **not** re-derived and are carried as conditional premises exactly as the board row
already records. No Lean proof exists for this row; it is not peer reviewed; both facts are
consistent with the row's Claimed level.

**Contact for corrections:** open an issue on `bigospeedrun/verifier` referencing this directory.

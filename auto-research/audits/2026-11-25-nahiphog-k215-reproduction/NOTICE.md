# Notice

## Sources (fetched by verify.py, pinned)

- VladimirReshetnikov/ProveIt, commit `66ce3c04bbc691d753a31a1615d97a93edbf5309`,
  `Computability/BusyBeaver/Research/ZFC/candidate-k215/`: `k215.tm`, `k215.native.tm`, `sites215.json`,
  `canonicalization.json`, and with `--upstream` the checker files under `verification/code/`.
  These files are not redistributed here; their licences and attribution are in the source's
  `NOTICE.md` and `licenses/`.

## Credits

K215 and its proofs are the work of Vladimir Reshetnikov and the ProveIt contributors, building on
Elliot Glazer (K230, compact theory K; K215-PA), Mira-Cult and mira-emmy (254/253), Jeff Ketchersid
(Coq pipeline), Andrew James Wade (register-machine compiler), Rohan Ridenour, Johannes Riebel and
Stefan O'Rear (NQL lineage). This package adds only an independent reproduction, measurements and
negative search results.

## Code

All code under `code/` and `verify.py` was written for this audit and is released under the MIT
License. It does not copy code from ProveIt; the upstream checker is downloaded and run unchanged only
with `--upstream`.

## AI assistance

The code, the searches and this text were produced by an AI agent (Kiro, using an Anthropic Claude
model) working for the package's submitter, who reviewed the result. The search runs and their logs
are recorded in the submitter's lab notebook.

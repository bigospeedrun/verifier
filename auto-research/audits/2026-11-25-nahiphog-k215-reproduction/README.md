# Audit: independent reproduction of K215 (Busy Beaver / ZFC, 215 states), with negative results

Row: [Busy Beaver independence from ZFC](https://bigospeedrun.com/other/busy-beaver-zfc), leader
`N_ZFC ≤ 215` (Vladimir Reshetnikov, K215, evidence Claimed).
Source pinned: VladimirReshetnikov/ProveIt `66ce3c04bbc691d753a31a1615d97a93edbf5309`,
`Computability/BusyBeaver/Research/ZFC/candidate-k215`.

## Hypothesis

The published K215 table and source are what the K215 README says they are, and the row's runtime
evidence can be reproduced on a fresh machine by code that does not reuse the author's checker.

## Result

PASS. `python3 verify.py` (standard library only, about 1 minute) checks:

| Check | Result |
|---|---|
| SHA-256 of `k215.tm`, `k215.native.tm`, `sites215.json` | match the published hashes; a canonical rewrite of the dense table is byte-identical |
| Native and dense tables | the same machine under `canonicalization.json`: lockstep for 20,000 steps |
| Shape | 215 working states, 430 rows, no undefined row, one halt label |
| Blank start | after exactly 95,714 steps: dense state 83, head −8, 95 one cells; registers show one value 4 (physical index 6) and eight zeros; 40 spares, all of value 1 |
| Concrete sweep of the 6,176 guarded site cases (code written from the frame rules) | 12,352 random cases (two per case), 0 failures, all 430 rows used, 6 to 858 steps |
| Source | 202 distinct subtrees (23 leaf kinds), as stated |
| Mutation control | skipping zero-counter state 50 (row `(34,0) → 75`) fails all 144 cases of the 37 sites with a run of six zeros and none of 6,104 other cases |

`python3 verify.py --upstream` also replays the author's `validate_native.py` unchanged:
`UNIVERSAL_MATHEMATICAL_PASS`, 6,176 of 6,176 cases (Windows 11, Python 3.13, about 5 minutes; give the
checker absolute paths, otherwise it writes no report).

## State roles (measured, `verify.py`)

| Quantity | Value |
|---|---|
| States that read an internal program-counter bit (decoder states), from dispatcher native 84 | 165, hosting 179 internal nodes; 15 are shared by two nodes |
| Other states | 50 |
| Engine rows (executed after decoding, other than re-decoding the current prefix) | 185 of 430 |
| Decoder states that are engine jump targets | 60 |
| Decoder states with no engine row, no helper row and no engine entry | 100 |
| States used only during the blank start | 0 |

The zero counter (states 2, 3, 5, 9, 15, 23, 34, 50, 75) costs one state per unit of the source's
maximum zero run; the mutation control above shows the exact dependence.

## Negative results (what did not give 214)

These are search results, not lower bounds.

| Search | Scale | Result |
|---|---|---|
| Exact bisimulation quotient | K215 and the other 50 distinct 215-state tables in machine or primary folders of `candidate-k215/alternatives` | no mergeable pair |
| Delete one state Y, send every edge into Y to X, give X its own or Y's row for each read symbol | all 184,040 candidates on K215; positive control with a planted duplicate state is found | 0 survivors (`data/foldsearch-summary.json`) |
| Source rotations, closed factors | 8 cores, up to 8 × 1,500 s per setting | 202 subtrees at zero run 6; 205 at zero run 5 (matches ProveIt's `zero5`); 215 at zero run 4 |
| Source rotations with CC operand re-tagging | same | 201 subtrees reachable, graph checked equal to K215 by two resolvers |
| Allocating those 201-subtree sources onto K215 (incremental and MILP allocators) | | at best 222 states: about 50 free decoder states are freed, but 14 to 18 engine-bound decoder states stay and cannot host new nodes |
| Source search scored by estimated state change against the machine | K215 and four other substrates (conditional-marker, context-returns shallow, mp-first-transfer, zero-spare-mp-first), 64 runs | never below 215; at zero run 5 the best estimate is +23 |

The source-search and allocator code is in the author's working tree (not in this package); its
outputs and logs are described in the notebook cited in NOTICE.md.

The fold search can be rerun from this package (about 1 hour on 8 cores):
`cd code && python3 -m bbzfc.foldsearch --table ../cache/k215.tm --sites ../cache/sites215.json --workers 8 --out ../evidence/foldsearch.json`
(after `verify.py` has filled `cache/`).

## Scope and limits

- Concrete random cases are a test, not the author's quantified symbolic proof; the upstream checker
  replay supplies that proof at the author's level (ordinary mathematics, not a proof-assistant kernel).
- No Lean or Rocq build was run (7.8 GB of RAM here). The external Lean/Rocq endpoints and Glazer's
  K215-PA receipt were not rerun.
- Nothing here addresses the calculus calibration or the internal PA endpoint; those are taken as the
  row states them.
- The negative results cover only the move sets described.

## Open obligations

None for this audit. A Lean or Rocq rebuild of the K215 endpoints on a larger machine would extend it.

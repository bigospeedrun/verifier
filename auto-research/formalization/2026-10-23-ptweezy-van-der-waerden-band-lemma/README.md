# Formalization: the van der Waerden norm-band multiplicity lemma (`lem:band`)

Track: formalization. Seed: 56 (OS randomness, 40-64 band).
Base commit of `bigospeedrun/verifier`: `106c0f1b12f14c2dc735e7c35636e94a382fe858`
(local clone at that commit; all track contents below are read from it).
Problem: `/other/van-der-waerden`. Evidence before: Claimed.
Bound concerned: `1/9` (the row's current leader, DaysSky 2026-10-12; see the
scope section for exactly which step of that author's chain this package
formalizes).

## The named step

The Claimed van der Waerden result bounds the coefficient `c` in
`W_r(k) > k^{ck⌊log₂ r⌋}`. Its construction groups points into keys
comprising a coordinate box and an integer squared-norm band; the
construction's affinity and separation lemmas put the points of a fixed
key on a real affine line, at mutual distance at least one, and the
released multiplicity lemma bounds the number of occurrences of one key
by four. DaysSky's research note "Two refinements of the October 2026
OpenAI math release" (`research-note.tex`, section "A sharper norm-band
multiplicity") improves that multiplicity bound from four to two:

> **Lemma `lem:band`.** Let points on a real affine line be pairwise
> separated by distance at least one. At most two of them can have
> squared norms in a single half-open interval `[m, m+1)`.

The note's proof (five lines): use signed arclength `t` from the nearest
point of the line to the origin, so the squared norm is `t² + C` for a
fixed `C ≥ 0`. If three points were in the band, two of their parameters
would share a sign class, `(−∞, 0)` or `[0, ∞)`; writing their absolute
values as `0 ≤ u < v`, the separation gives `v − u ≥ 1`, whence
`v² − u² = (v − u)(v + u) ≥ 1` — but two numbers in `[m, m+1)` differ by
less than one, a contradiction.

This package formalizes exactly that lemma, in full, in one Lean file —
and nothing else. The lemma is load-bearing in the note: it is invoked
at four places in its parameter transfers (`research-note.tex` lines
79, 140, 213, 275), and the repository's own progress record credits
the "two-point band lemma" with the chain's first step (conditional
`c = 1/200`, then `1/193`, then the note's sharpened region with explicit
`c = 1/25` and supremum `1/24`).

## Result

Lean 4.34.1, Mathlib rev `d13f23b723b8a846827a245b89c10fc7d3f11612`
(the rev pinned in `profiles/lake-manifest.json`; project files in
`code/lean-project/`), single file `code/BandLemma.lean` with narrow
imports (`Mathlib.Analysis.InnerProductSpace.Basic`, plus the `linarith`
tactic). 234 lines including the documentation header.

The line is parameterized exactly as in the note: in a real inner
product space `E`, points `a + t • u` with `‖u‖ = 1` and `⟪a, u⟫_ℝ = 0`,
so `a` is the line's nearest point to the origin and `t` is signed
arclength. The file proves the parameterization facts
`‖a + t • u‖ ^ 2 = ‖a‖ ^ 2 + t ^ 2` (`norm_sq_add_smul`, the note's
"`t² + C`") and `dist (a + t • u) (a + s • u) = |t − s|`
(`dist_add_smul`), and then the lemma in three forms:

- `VanDerWaerden.card_le_two_of_band` — the pure real core: a finite
  set of reals, pairwise at least `1` apart, has at most two members
  whose squares lie in `[m, m + 1)`. Its proof is the note's: the pair
  step `one_le_abs_sq_sub_of_same_class`, the sign pigeonhole
  `same_class_pair`, combined in `band_pair_absurd`.
- `VanDerWaerden.band_three_points` — the note's proof in its exact
  shape: no three distinct points of the line, pairwise at distance
  at least `1`, have all squared norms in one band.
- `VanDerWaerden.band_card_le_two` — the lemma in the arclength
  parameterization, and `VanDerWaerden.points_band_card_le_two` — the
  lemma as stated in the note, for a finite set of points of `E` lying
  on the affine line.

`lake build` succeeded from the packaged copy (see
`evidence/lean-build.log`: `Build completed successfully`,
`LAKE_EXIT:0`). `#print axioms` for `card_le_two_of_band`,
`band_three_points`, `band_card_le_two` and `points_band_card_le_two`
each report exactly `[propext, Classical.choice, Quot.sound]`. There is
no `sorry`, `admit`, `native_decide`, or declared axiom in the file.

One formulation note, stated plainly: the note says "at most two of
them" of an unspecified collection of points. This package formalizes
that as a statement about finite families (`Finset.card ≤ 2` of the
points in the band) — the standard reading, and the one the note's own
proof uses, since the proof is a contradiction from three points; that
three-point form is proved verbatim as `band_three_points`, so the
finite-family statement is exactly equivalent in content to the note's
argument. The ambient space is an arbitrary real inner product space
rather than the note's coordinate space: the lemma uses nothing but
the inner-product geometry of one line, and the coordinate case is the
special case `E = ℝ^d`. No hypothesis of the note is strengthened or
dropped: `C ≥ 0` in the note is `‖a‖ ^ 2 ≥ 0` here, automatic.

## Reproduce

Package checks (Python 3 standard library only; exact rational sanity
checks of the proof's arithmetic core on a finite grid — the key-step
identity `v² − u² = (v − u)(v + u) ≥ 1` for same-sign separated pairs,
the band width fact, and an exhaustive check of the lemma over the
grid `{k/2 : −6 ≤ k ≤ 6}` — plus integrity checks that the packaged
Lean file states the theorems above, contains no `sorry`/`admit`, and
that the recorded build log shows success with exactly the allowed
axioms; the proof itself is the Lean file):

```
bash auto-research/formalization/2026-10-23-ptweezy-van-der-waerden-band-lemma/verify.sh
```

Expected: every check prints `ok` and the script ends with `PASS`.

Lean proof (from a fresh clone, with elan / Lean `leanprover/lean4:v4.34.1`):

```
mkdir BandTest && cd BandTest
cp <this-package>/code/lean-project/lakefile.toml <this-package>/code/lean-project/lean-toolchain <this-package>/code/lean-project/lake-manifest.json .
cp <this-package>/code/BandLemma.lean .
lake exe cache get
lake build
```

Expected: `Build completed successfully`, and the four `#print axioms`
infos quoted above. On the 2-core machine used here, with Mathlib's
cache already fetched, `lake build` of this one narrow-import file took
about 39 seconds (evidence log). A full `import Mathlib` variant is
unnecessary; the narrow imports are the shipped form.

## Scope and limits

- This formalizes `lem:band` only. Everything around it stays written:
  the source construction's affinity and separation lemmas (which place
  one key's points on a line, at mutual distance at least one), the
  note's parameter transfers that consume the lemma (propositions
  `prop:region` and `prop:short`), its run lemmas, and the whole
  upstream van der Waerden argument. Nothing here makes the result
  Lean Verified.
- In particular, the row's current leader `c = 1/9` (DaysSky,
  2026-10-12) is obtained in the same repository by counting
  short-period runs instead of label words; its run lemmas do not use
  `lem:band`. The lemma formalized here belongs to the note's earlier
  label-word chain (`c = 1/200` → `1/193` → `1/25`), which shares the
  construction framework with the leader. The package claims the lemma,
  not the leader's bound.
- The lemma is stated for one affine line in a real inner product
  space; the note's application additionally needs the points of a key
  to *be* on such a line with the stated separation, which is the
  upstream affinity/separation step, out of scope here.

## How this task was chosen (overlap check first)

Checked on 2026-10-23 against `bigospeedrun/verifier` at
`106c0f1b12f14c2dc735e7c35636e94a382fe858`, the site row, and fresh
clones of both source repositories:

- The formalization track README at that commit lists
  van-der-waerden under "Other bounds rows with no Lean proof", and no
  van-der-waerden folder exists in any of the four auto-research
  tracks on main. The track on main holds exactly: subset-sum
  small-layer (PR #17), unit-distance grid (PR #27), average-sensitivity
  (PR #36), matroid prophet (PR #42).
- Open PRs at the check: exactly two — #21 (Catalan statement) and
  #12 (Subset Sum statement), both lean-statements, neither touches
  van der Waerden; no closed PR mentions it either.
- The site row's proof scope: "No Lean proof is supplied; an open pull
  request adds partial Lean for selected steps" — that pull request is
  in the upstream OpenAI construction repository and concerns other
  steps; the row also notes "the exact audit checks the parameter
  margins, not these lemmas".
- Source repositories cloned and inspected 2026-10-23:
  `DaysSky/van-der-waerden-refinement` at
  `54ac9715fceab938ca77d5980c36ab691765a04d` and
  `rohanarun/van-der-waerden-refinement` at
  `63bef9ca996786a41169de4a0c3d6b3b47b0fe96` — zero `.lean` files in
  either. The note itself states
  (research-note.tex, §1): "The parameter transfer below has been
  audited in source; it has not been formalized in Lean."
- This lemma was the runner-up of the author's 2026-10-21
  formalization hunt (behind the matroid prophet certificate, PR #42);
  its unclaimed status was re-verified end to end today.

## Status

Prepared locally under this repository's `AGENTS.md` local-review
phase; not yet placed on any fork and no PR has been opened. The
folder handle is the contributor's GitHub handle. The package is
published only at the contributor's direction.

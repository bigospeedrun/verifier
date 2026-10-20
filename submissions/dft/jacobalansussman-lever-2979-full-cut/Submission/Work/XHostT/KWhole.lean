import Submission.Work.XHostT.TSchedK
import Submission.Work.XHostT.KGlue

/-!
# (key: bridge-host-cross) The whole-table host check from its parts

`TableOK ct rt resT NC R NK` is the conclusion of p-a3's `table_sound` (Work/XHostT/TSchedK.lean), named: every slot
`q < R` of every call `k < NC` is hosted at a host index below `224 NK`, inside the window of its host kind; at most one
slot of a call per host; and every host's residual load plus its remainder is the rank of its kind.

`tableOK_of_KOK`: the range fact `KOK .. 0 NK` (assembled from part modules by `KOK.one` / `KOK.app`,
Work/XHostT/KGlue.lean) and the global count fact (the counts sum to `NC * R`) give `TableOK`.
Written by p-hostck (wht45/lever, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

namespace OAI.PowerSaving.XHostT.K
open Finset

/-- the conclusion of `table_sound`: the decoded table is a valid cross-replica host schedule. -/
def TableOK (ct rt : CT) (resT NC R NK : ℕ) : Prop :=
    (∀ k < NC, ∀ q < R, rowAt (ct.get k).1 q < 224 * NK ∧
        (winOf ct (rowAt (ct.get k).1 q / 224)).1 ≤ (ct.get k).2.1 ∧
        (ct.get k).2.1 ≤ (winOf ct (rowAt (ct.get k).1 q / 224)).2) ∧
    (∀ k < NC, ∀ q < R, ∀ q' < R, rowAt (ct.get k).1 q = rowAt (ct.get k).1 q' → q = q') ∧
    (∀ i < 224 * NK, (∑ x ∈ (range NC ×ˢ range R).filter (fun x => rowAt (ct.get x.1).1 x.2 = i),
        resAt resT (ct.get x.1).2.2 x.2) + remAt rt i = rkN (i / 224 % 9))

/-- **the whole table from its parts**: all host kinds checked (as ranges) and the counts summing to `NC * R`. -/
theorem tableOK_of_KOK {ct rt : CT} {resT NC R NK : ℕ} (cK : ℕ → ℕ) (hK : KOK ct rt resT NC R cK 0 NK)
    (hsum : ((List.range NK).map cK).sum = NC * R) : TableOK ct rt resT NC R NK :=
  table_sound cK (fun κ hκ => hK κ (Nat.zero_le κ) hκ) hsum

end OAI.PowerSaving.XHostT.K

#print axioms OAI.PowerSaving.XHostT.K.tableOK_of_KOK

import Submission.Work.XHostT.KCheck

/-!
# (key: heads-first #2979) The head count of a kernel host table, the computable side (core Lean, no Mathlib)

p-a3's kernel table format (Work/XHostT/KCheck.lean): the remainder tree `rt` has one leaf per host kind
`κ = 9 ρ + c` (replica `ρ`, window kind `c`), packing the remainders of its 224 bins (side `s`, class `t`: bin
`112 s + t`) in 6 bits each.  `cntKind rt v c n` is the number of bins of window kind `c` in the replicas
`0 .. n - 1` whose remainder is `v`; for the head count of #2979 (`c = 4`, the A4 windows, `v = 48`, `n = 74`) the data
fact is `cntKind rt 48 4 74 = 16086`, one `decide +kernel` on the table (74 leaves x 224 fields).  What it means for
the host schedule is proved in Work/XHostT/HF/Inst2979.lean (`I2979.card_rem_eq`, `I2979.headBins_card`).
Written by x-inst (wht45/lever2979, 19 Oct 2026), in the style of p-hostck's KHistC; prepared with assistance from
Claude.  No `sorry`.
-/

namespace OAI.PowerSaving.XHostT.I2979

/-- field `b` (6 bits) of a packed remainder leaf. -/
def fld (x b : Nat) : Nat := (x >>> (6 * b)) &&& 63

/-- the number of fields `b < m` of `x` equal to `v`. -/
def cntF (x v : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => cntF x v m + (bif Nat.beq (fld x m) v then 1 else 0)

/-- the number of bins of window kind `c` of the replicas `0 .. n - 1` whose remainder is `v`. -/
def cntKind (rt : K.CT) (v c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cntKind rt v c n + cntF (rt.get (9 * n + c)).1 v 224

end OAI.PowerSaving.XHostT.I2979

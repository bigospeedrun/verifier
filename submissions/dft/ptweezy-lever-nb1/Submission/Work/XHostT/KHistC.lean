import Submission.Work.XHostT.KCheck

/-!
# (key: bridge-host-cross) Global facts of a kernel host table, the computable side (core Lean, no Mathlib)

Counting and membership over the packed remainder leaves of a table (`rt`, p-a3's KCheck format: leaf `κ` packs the
remainders of the 224 bins of host kind `κ`, 6 bits each), over a RANGE of kinds `a, a + 1, ..., a + n - 1`, so that a
table's global facts can be cut into small chunks decided in parallel (module `Glob<j>` of a table); and the residual
sums of a provider.  What they mean is proved in Work/XHostT/KHist.lean.
Written by p-hostck (wht45/lever, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

namespace OAI.PowerSaving.XHostT.K

/-- field `b` (6 bits) of a packed leaf. -/
def fld6 (x b : Nat) : Nat := (x >>> (6 * b)) &&& 63

/-- the number of fields `b < m` of `x` equal to `v`. -/
def cntB (x v : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => cntB x v m + (bif Nat.beq (fld6 x m) v then 1 else 0)

/-- the number of bins of the host kinds `a .. a + n - 1` with remainder `v`. -/
def cntR (rt : CT) (v a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cntR rt v a n + cntB (rt.get (a + n)).1 v 224

/-- every field `b < m` of `x` lies in `V`. -/
def inB (x : Nat) (V : List Nat) : Nat → Bool
  | 0 => true
  | m + 1 => inB x V m && V.contains (fld6 x m)

/-- every remainder of the host kinds `a .. a + n - 1` lies in `V`. -/
def inR (rt : CT) (V : List Nat) (a : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => inR rt V a n && inB (rt.get (a + n)).1 V 224

/-- the residual sum of provider `p` over the slots `q < m`. -/
def resS (resT p : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => resS resT p m + resAt resT p m

end OAI.PowerSaving.XHostT.K

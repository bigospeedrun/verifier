import Submission.Work.XHostT.KHistC

/-!
# (key: bridge-host-cross) Per-kind counters of a kernel host table (core Lean, no Mathlib)

Next to p-hostck's range counters (Work/XHostT/KHistC.lean): `cntK rt v c n` counts the bins of host kind `c` (both
sides, all 112 classes) of the replicas `0 .. n - 1` whose remainder is `v` (host kind `κ = 9 ρ + c` is leaf `κ` of
`rt`); `resGE resT p v m` checks that every residual of provider `p`, slots `q < m`, is at least `v`; `resEqP resT m`
checks that the two providers' residuals agree on the slots `q < m`.  What they mean: Work/XHostT/KHead.lean.
x-tables (wht45/lever2979, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

namespace OAI.PowerSaving.XHostT.K

/-- the number of bins of host kind `c` of the replicas `ρ < n` with remainder `v`. -/
def cntK (rt : CT) (v c : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cntK rt v c n + cntB (rt.get (9 * n + c)).1 v 224

/-- every residual of provider `p` on the slots `q < m` is at least `v`. -/
def resGE (resT p v : Nat) : Nat → Bool
  | 0 => true
  | m + 1 => resGE resT p v m && Nat.ble v (resAt resT p m)

/-- the residuals of providers 0 and 1 agree on the slots `q < m`. -/
def resEqP (resT : Nat) : Nat → Bool
  | 0 => true
  | m + 1 => resEqP resT m && Nat.beq (resAt resT 0 m) (resAt resT 1 m)

end OAI.PowerSaving.XHostT.K

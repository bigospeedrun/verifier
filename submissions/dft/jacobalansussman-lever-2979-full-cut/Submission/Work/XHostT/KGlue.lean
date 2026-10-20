import Submission.Work.XHostT.KCheck

/-!
# (key: bridge-host-cross) Glue of the kernel host-table check: host-kind ranges assembled from parts (core Lean)

The kernel checker `chkPieceCount` (Work/XHostT/KCheck.lean, p-a3) is run as ONE `decide +kernel` theorem per host
kind `κ`, each in a part module that imports only the checker and the table's data.  This file says how the parts are
put together WITHOUT re-running anything:

* `KOK ct rt resT NC R cK a b`: every host kind `a ≤ κ < b` passes the check with record count `cK κ` (for some
  streams);
* `KOK.one`: one checked kind is the range `[a, a + 1)`;
* `KOK.app`: adjacent ranges `[a, b)` and `[b, c)` give `[a, c)`;
* `KOK.nil`: the empty range.

A part module proves `KOK .. a b` for its range by a chain of `KOK.app`; the whole-table module combines the parts'
ranges in a balanced tree (term mode, no evaluation) and hands `KOK .. 0 NK` to `table_sound` (Work/XHostT/KWhole.lean).
The counts `cK` are data (a search tree in the table's Calls module); a wrong count only makes a part fail.
Written by p-hostck (wht45/lever, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

namespace OAI.PowerSaving.XHostT.K

/-- every host kind `a ≤ κ < b` passes the kernel check with record count `cK κ`. -/
def KOK (ct rt : CT) (resT NC R : Nat) (cK : Nat → Nat) (a b : Nat) : Prop :=
  ∀ κ, a ≤ κ → κ < b → ∃ bs rs : List Nat, chkPieceCount ct rt resT NC R κ 1 bs rs = some (cK κ)

theorem KOK.nil {ct rt : CT} {resT NC R : Nat} {cK : Nat → Nat} (a : Nat) : KOK ct rt resT NC R cK a a := by
  intro κ h1 h2
  exact absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl a)

/-- one checked host kind. -/
theorem KOK.one {ct rt : CT} {resT NC R : Nat} {cK : Nat → Nat} {a b : Nat} (hb : a + 1 = b) (bs rs : List Nat)
    (h : chkPieceCount ct rt resT NC R a 1 bs rs = some (cK a)) : KOK ct rt resT NC R cK a b := by
  intro κ h1 h2
  have e : κ = a := by omega
  subst e
  exact ⟨bs, rs, h⟩

/-- two adjacent ranges. -/
theorem KOK.app {ct rt : CT} {resT NC R : Nat} {cK : Nat → Nat} {a b c : Nat}
    (h1 : KOK ct rt resT NC R cK a b) (h2 : KOK ct rt resT NC R cK b c) : KOK ct rt resT NC R cK a c := by
  intro κ ha hc
  by_cases hb : κ < b
  · exact h1 κ ha hb
  · exact h2 κ (by omega) hc

/-- the counts of a table: the record count of host kind `κ` is the first field of the leaf `κ` of a search tree. -/
def cntOf (cntT : CT) (κ : Nat) : Nat := (cntT.get κ).1

end OAI.PowerSaving.XHostT.K

#print axioms OAI.PowerSaving.XHostT.K.KOK.one
#print axioms OAI.PowerSaving.XHostT.K.KOK.app

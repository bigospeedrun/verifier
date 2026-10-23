import Submission.Work.P3.Ctrl4
import Submission.Work.P4L.Roles
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L, part 8: the eight main roles of one port, as data of the controller

`P4Ctrl.S8 R` holds the eight main roles `x0 y0 .. x3 y3` of one port (Work/P3/Ctrl4).  Here: reading and writing a
role by its kind `i : R8` (`get`, `set`), the four kinds of controller events as maps of `S8 R` (`callF`/`callB` one
native call on a pair; `win` an idle window; `gate` a bridge; `swap` a signed exchange), and `ctrlW_eq`: the generated
controller `P4Ctrl.ctrl` IS the composition of these events in the order of the P4-L word.  No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving
namespace P4L
open P4Ctrl

section
variable {R : Type*} [CommRing R]

/-- read a role (in the namespace of `P4Ctrl.S8`, so that `u.get` works). -/
def _root_.OAI.PowerSaving.P4Ctrl.S8.get (u : S8 R) : R8 → R
  | .x0 => u.x0 | .y0 => u.y0 | .x1 => u.x1 | .y1 => u.y1
  | .x2 => u.x2 | .y2 => u.y2 | .x3 => u.x3 | .y3 => u.y3

/-- write a role. -/
def _root_.OAI.PowerSaving.P4Ctrl.S8.set (u : S8 R) : R8 → R → S8 R
  | .x0, v => { u with x0 := v } | .y0, v => { u with y0 := v }
  | .x1, v => { u with x1 := v } | .y1, v => { u with y1 := v }
  | .x2, v => { u with x2 := v } | .y2, v => { u with y2 := v }
  | .x3, v => { u with x3 := v } | .y3, v => { u with y3 := v }

/-- one forward native call on the pair `(x, y)`: `y += qi x`, then the stage transform `d` on the pair. -/
def callF (x y : R8) (d qi : R) (u : S8 R) : S8 R :=
  (u.set x (d * u.get x)).set y (d * (u.get y + qi * u.get x))

/-- one backward native call on the pair `(x, y)`: `x -= q y`, then the stage transform `d` on the pair. -/
def callB (x y : R8) (d q : R) (u : S8 R) : S8 R :=
  (u.set x (d * (u.get x - q * u.get y))).set y (d * u.get y)

/-- an idle window of the pair `(x, y)`: both roles times `m`. -/
def win (x y : R8) (m : R) (u : S8 R) : S8 R :=
  (u.set x (m * u.get x)).set y (m * u.get y)

/-- a bridge gate: role `dst` += `c` role `src`. -/
def gate (dst src : R8) (c : R) (u : S8 R) : S8 R := u.set dst (u.get dst + c * u.get src)

/-- the signed exchange of the pair `(x, y)`: `(x, y) ↦ (y, -x)`. -/
def swap (x y : R8) (u : S8 R) : S8 R :=
  (u.set x (u.get y)).set y (-u.get x)

/-- **the controller, event by event in the order of the P4-L word.** -/
def ctrlW (d : Fin 9 → R) (q qi : R) (u : S8 R) : S8 R :=
  let u := callF .x0 .y0 (d 0) qi u
  let u := callB .x0 .y0 (d 1) q u
  let u := win .x1 .y1 (d 0 * d 1) u
  let u := gate .x0 .x1 1 u
  let u := gate .y1 .y0 (-1) u
  let u := callF .x0 .y0 (d 2) qi u
  let u := win .x1 .y1 (d 2) u
  let u := gate .x0 .x1 (-1) u
  let u := gate .y1 .y0 1 u
  let u := callB .x1 .y1 (d 3) q u
  let u := win .x2 .y2 (d 0 * d 1 * d 2 * d 3) u
  let u := gate .x1 .x2 1 u
  let u := gate .y2 .y1 (-1) u
  let u := callF .x1 .y1 (d 4) qi u
  let u := win .x2 .y2 (d 4) u
  let u := gate .x1 .x2 (-1) u
  let u := gate .y2 .y1 1 u
  let u := callB .x2 .y2 (d 5) q u
  let u := gate .x2 .x3 1 u
  let u := gate .y3 .y2 (-1) u
  let u := callF .x2 .y2 (d 6) qi u
  let u := win .x3 .y3 (d 6) u
  let u := gate .x2 .x3 (-1) u
  let u := gate .y3 .y2 1 u
  let u := callB .x3 .y3 (d 7) q u
  let u := callF .x3 .y3 (d 8) qi u
  let u := win .x2 .y2 (d 7 * d 8) u
  let u := gate .x3 .x2 1 u
  let u := gate .y2 .y3 (-1) u
  let u := gate .x2 .x1 1 u
  let u := gate .y1 .y2 (-1) u
  let u := gate .x1 .x0 1 u
  let u := gate .y0 .y1 (-1) u
  let u := swap .x0 .y0 u
  let u := swap .x1 .y1 u
  let u := swap .x2 .y2 u
  let u := swap .x3 .y3 u
  u

/-- **the event form is the generated controller** (`P4Ctrl.ctrl`, whose `ctrl_diag` is the boundary
factorisation). -/
theorem ctrlW_eq (d : Fin 9 → R) (q qi : R) (u : S8 R) : ctrlW d q qi u = ctrl d q qi u := by
  simp only [ctrlW, ctrl, callF, callB, win, gate, swap, S8.get, S8.set]

end

end P4L
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P4L.ctrlW_eq

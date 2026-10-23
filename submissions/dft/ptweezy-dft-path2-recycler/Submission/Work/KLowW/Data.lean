import Submission.Work.GCert.Data.Raw

/-!
# (key: p-warpchk) Warp events in a word certificate (`gcert/1w`): the data (core Lean only)

p-warpchk, round wht45/lever, 19 Oct 2026.  A phase of an extended certificate is a list of EVENTS:

* `.g gate`          an ordinary gate of `gcert/1` (`GXD.Gate`): its registers climb to its frame, then its adds;
* `.sc f r co`       `r` climbs to the frame `f`, then `r := co * r` (the hub's `scale`, `co ≠ 0`);
* `.w r a f0 f1`     a WARP (the hub's monomial logical reference change `K_G^{±1}`, PR2226): register `r` moves from
                     the frame `f0` to the frame `f1`, `G f0 = f1` for `a > 0` (`G = wt[a-1]`), `G⁻¹ f0 = f1` for
                     `a < 0`; its content is multiplied by the free letter `K a`;
* `.za r f`          a private ZERO BUFFER `r` is allocated: content `0`, frame `f` (the hub's `zero_buffer alloc`);
* `.zf r`            the zero buffer `r` is freed: content `0`;
* `.dn r f`          `r` climbs DOWN to the frame `f` contained in its frame (one block of rank `dim - dim f`; the
                     hub's centre steps: a centre copy goes down to the levels of its cut targets).

The warp table `wt : List WOp`: entry `a - 1` = op id `a`, the images of the `h` unit vectors under `G` and `G⁻¹`
(bit masks; bit `q` = coordinate `q`, the convention of the frame table).

Signed op ids are `Int`; the kernel reads them through `opAbs`, `opPos`, `opNe0` (`Int.rec`, no `Int` order).
No `sorry`.
-/

namespace KLW
open GXD

/-- one operator of the warp table: the images of the unit vectors under `G` and under `G⁻¹` -/
structure WOp where
  G : List Nat
  Gi : List Nat
  deriving Repr

/-- one event of an extended phase -/
inductive WEv where
  | g (gate : Gate)
  | sc (frame r : Nat) (co : Co)
  | w (r : Nat) (op : Int) (f0 f1 : Nat)
  | za (r f : Nat)
  | zf (r : Nat)
  | dn (r f : Nat)
  deriving Repr

/-- the warp gate of the brief: `(register, signed op id, f0, f1)` -/
def WEv.ofWarp (x : Nat × Int × Nat × Nat) : WEv := .w x.1 x.2.1 x.2.2.1 x.2.2.2

/-- `|a|` -/
noncomputable def opAbs (a : Int) : Nat := Int.rec (motive := fun _ => Nat) (fun n => n) (fun n => Nat.succ n) a
/-- `0 < a` -/
noncomputable def opPos (a : Int) : Bool := Int.rec (motive := fun _ => Bool) (fun n => !(Nat.beq n 0)) (fun _ => false) a
/-- `a ≠ 0` -/
noncomputable def opNe0 (a : Int) : Bool := Int.rec (motive := fun _ => Bool) (fun n => !(Nat.beq n 0)) (fun _ => true) a

/-- the table entry of a signed op id (default: empty) -/
noncomputable def opOf (wt : List WOp) (a : Int) : WOp := wt.getD (opAbs a - 1) ⟨[], []⟩

end KLW

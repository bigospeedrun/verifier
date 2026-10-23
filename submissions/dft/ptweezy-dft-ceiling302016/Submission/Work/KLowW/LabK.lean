import Submission.Work.GCert.Labels.Def
import Submission.Work.KLowW.Data

/-!
# (key: p-warpchk) The label check of an extended phase: kernel terms (core Lean only)

* `colK cols m`        the GF(2) image of the mask `m` under the columns `cols` (XOR of the columns of its bits);
* `imgK h hm cols Pa Pb n`   for every digit `p < n` of the packed basis `Pa`: the image of digit `p` lies in the
                       span of the digits of `Pb` (one packed elimination `elimT` each, selector `1`);
* `trK h hm o ca cb`   `G` maps the frame `ca` INTO `cb` and `G⁻¹` maps `cb` INTO `ca` (so `G ca = cb`);
* `transK`             the frame transport of a warp: `G f0 = f1` (`a > 0`) or `G f1 = f0` (`a < 0`);
* `invK`, `wtK`        every table entry: `G * G⁻¹ = 1` and `G⁻¹ * G = 1` on the unit vectors;
* `evK`                one event: gates and scales as `gcert/1` (`gateK`), warps (current frame `= f0`, transport,
                       new frame `f1`), zero buffers (any frame, no climb), climbs DOWN (`f` inside the current
                       frame: one packed elimination; rank `dim - dim f`);
* `segW p wt evs S S' rs`   the replay of a list of events from `S`: ends at `S'`, block ranks `rs`.

Soundness: `Work.KLowW.LabSound`.  No `sorry`.
-/

namespace KLW
open SSC GXD GLab

/-- the image of the mask `m` under the columns `cols` (column `i` = image of unit vector `i`) -/
noncomputable def colK : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun c _ ih m => Nat.xor (Nat.mul (Nat.land m 1) c) (ih (Nat.shiftRight m 1)))

/-- the images (masked to `h` bits) of the digits `p < n` of `Pa` lie in the span of the digits of `Pb` -/
noncomputable def imgK (h hm : Nat) (cols : List Nat) (Pa Pb : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun p ih => guard (elimT h hm 1 Pb (Nat.land (colK cols (digK h hm Pa p)) hm)) ih)

/-- `G` maps the frame of the code `ca` into the frame of `cb`, `G⁻¹` maps `cb` into `ca` -/
noncomputable def trK (h hm : Nat) (o : WOp) (ca cb : Nat) : Bool :=
  guard (imgK h hm o.G (Nat.shiftRight ca (Nat.add 8 h)) (Nat.shiftRight cb (Nat.add 8 h)) h)
    (imgK h hm o.Gi (Nat.shiftRight cb (Nat.add 8 h)) (Nat.shiftRight ca (Nat.add 8 h)) h)

/-- the frame transport of a warp with op of sign `pos` from the code `c0` to `c1` -/
noncomputable def transK (h hm : Nat) (o : WOp) (pos : Bool) (c0 c1 : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (trK h hm o c1 c0) (trK h hm o c0 c1) pos

/-- `cols * cols'` is the identity on the unit vectors `i < n` -/
noncomputable def invK (hm : Nat) (cols cols' : List Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => guard (Nat.beq (Nat.land (colK cols (cols'.getD i 0)) hm) (Nat.pow 2 i)) ih)

/-- **the warp table**: every entry has `h` columns each way and is a pair of mutually inverse maps of `F_2^h` -/
noncomputable def wtK (h : Nat) (wt : List WOp) : Bool :=
  forceN (Nat.sub (Nat.pow 2 h) 1) fun hm =>
  List.rec (motive := fun _ => Bool) true
    (fun o _ ih => guard (Nat.beq o.G.length h) <| guard (Nat.beq o.Gi.length h) <|
      guard (invK hm o.G o.Gi h) (guard (invK hm o.Gi o.G h) ih)) wt

/-- **one event** (see the file header) -/
noncomputable def evK (p : GLab.Par) (wt : List WOp) (hm hh sh O : Nat) (e : WEv) (S : Trie) (rs : List Nat)
    (k : Trie → List Nat → Bool) : Bool :=
  WEv.rec (motive := fun _ => Bool)
    (fun g => gateK p hm hh sh O g S rs k)
    (fun f r _ => gateK p hm hh sh O (.out f r [] []) S rs k)
    (fun r a f0 f1 => guard (Nat.ble (Nat.succ r) p.n) <|
      S.getK r fun cur => guard (Nat.beq cur f0) <| guard (opNe0 a) <|
      guard (Nat.ble (opAbs a) wt.length) <|
      p.tab.getK f0 fun c0 => p.tab.getK f1 fun c1 =>
      guard (transK p.h hm (opOf wt a) (opPos a) c0 c1) (k (S.set r f1) rs))
    (fun r f => guard (Nat.ble (Nat.succ r) p.n) (k (S.set r f) rs))
    (fun r => guard (Nat.ble (Nat.succ r) p.n) (k S rs))
    (fun r f => guard (Nat.ble (Nat.succ r) p.n) <|
      S.getK r fun cur => p.tab.getK cur fun ca => p.tab.getK f fun cb =>
      guard (Nat.ble (Nat.succ (Nat.land cb 255)) (Nat.land ca 255)) <|
      guard (elimT p.h hm O (Nat.shiftRight ca sh) (Nat.shiftRight cb sh)) <|
      List.rec (motive := fun _ => Bool) false
        (fun r0 rs' _ => guard (Nat.beq r0 (Nat.sub (Nat.land ca 255) (Nat.land cb 255))) (k (S.set r f) rs')) rs) e

noncomputable def evsK (p : GLab.Par) (wt : List WOp) (hm hh sh O : Nat) :
    List WEv → Trie → List Nat → (Trie → List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → List Nat → (Trie → List Nat → Bool) → Bool)
    (fun S rs k => k S rs)
    (fun e _ ih S rs k => evK p wt hm hh sh O e S rs fun S1 rs1 => ih S1 rs1 k)

/-- **the label replay of one segment of events** -/
noncomputable def segW (p : GLab.Par) (wt : List WOp) (evs : List WEv) (S S' : Trie) (rs : List Nat) : Bool :=
  guard (Nat.ble 1 p.h) <|
  forceN (Nat.sub (Nat.pow 2 p.h) 1) fun hm =>
  forceN (Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1) hm) fun O =>
  guard (Nat.beq (Nat.mul O hm) (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1))
    (evsK p wt hm (Nat.mul p.h p.h) (Nat.add 8 p.h) O evs S rs fun S1 rs1 =>
      guard (Trie.beqK S1 S') (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rs1))

end KLW

import Submission.Work.KLowW.Data
import Submission.Work.SharedSumChecker.Check

/-!
# (key: p-warpchk) The scalar check of an extended phase: the hub's FREE WARP ALGEBRA replay (core Lean only)

As the hub's `bw_transport.py` / `bw_emit.check_local`: the content of every register is a ROW, a finite formal
combination of keys `(source register, warp word)` with rational coefficients, replayed literally:

* a key is ONE number `s + N * c`, `s < N` the source register, `c` the CODE of the warp word
  (`code [] = 0`, `code (a :: w) = enc a + B * code w`, `enc (+n) = 2n`, `enc (-(n+1)) = 2n+1`);
* a coefficient is an integer `z`, meaning `z / D`;
* a row is a list of `(key, z)`; `insK` (sorted insert, merging equal keys), `mergeK` (sorted merge), `scaleK`
  (times `± num / den`, EXACT: every product must be divisible by `den`), `warpK` (prepend the letter `a` to every
  word, cancelling a leading `-a`: the hub's `warp_row`);
* the rows of all registers sit in a binary trie `RT` (depth `d`).

`evS q o e R k`: one event in orientation `o` (`false` forward, `true` backward = the hub's `dual`: `t += c s` becomes
`s += -c t`, `scale a/b` becomes `scale b/a`; warps and zero buffers are the same events).
`scalW q o evs R R'`: the replay of a segment from the row trie `R` ends at `R'` (structural equality).

Soundness: `Work.KLowW.ScalSound`.  No `sorry`.
-/

namespace KLW
open SSC GXD

/-- a row: `(key, coefficient)`; the content is `∑ coefficient / D • key` -/
abbrev Row := List (Nat × Int)

/-- binary trie of rows (key bits from the least significant) -/
inductive RT where
  | leaf (row : Row)
  | node (l r : RT)

/-- the trie of depth `d` with empty rows -/
def RT.mk : Nat → RT
  | 0 => .leaf []
  | d+1 => .node (RT.mk d) (RT.mk d)

noncomputable def RT.getK (t : RT) : Nat → (Row → Bool) → Bool :=
  RT.rec (motive := fun _ => Nat → (Row → Bool) → Bool)
    (fun v key k => Nat.rec (motive := fun _ => Bool) (k v) (fun _ _ => false) key)
    (fun _ _ gl gr key k => Bool.rec (gr (Nat.shiftRight key 1) k) (gl (Nat.shiftRight key 1) k)
      (Nat.beq (Nat.land key 1) 0)) t

noncomputable def RT.set (t : RT) : Nat → Row → RT :=
  RT.rec (motive := fun _ => Nat → Row → RT) (fun _ _ v => .leaf v)
    (fun l r sl sr key v => Bool.rec (.node l (sr (Nat.shiftRight key 1) v))
      (.node (sl (Nat.shiftRight key 1) v) r) (Nat.beq (Nat.land key 1) 0)) t

/-- a trie of depth exactly `d` -/
noncomputable def RT.wfK : RT → Nat → Bool :=
  RT.rec (motive := fun _ => Nat → Bool) (fun _ d => Nat.beq d 0)
    (fun _ _ a b d => Nat.rec (motive := fun _ => Bool) false (fun m _ => guard (a m) (b m)) d)

/-- `z = 0` -/
noncomputable def izero (z : Int) : Bool := Int.rec (motive := fun _ => Bool) (fun n => Nat.beq n 0) (fun _ => false) z

/-- equality of rows -/
noncomputable def rowEq : Row → Row → Bool :=
  List.rec (motive := fun _ => Row → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => guard (Nat.beq x.1 y.1) (guard (izero (x.2 - y.2)) (ih ys))) b)

/-- structural equality of row tries -/
noncomputable def RT.beqK : RT → RT → Bool :=
  RT.rec (motive := fun _ => RT → Bool)
    (fun x t' => RT.rec (motive := fun _ => Bool) (fun x' => rowEq x x') (fun _ _ _ _ => false) t')
    (fun _ _ el er t' => RT.rec (motive := fun _ => Bool) (fun _ => false)
      (fun l' r' _ _ => guard (el l') (er r')) t')

/-- sorted insert of `(k, c)` (`c ≠ 0`), merging an equal key -/
noncomputable def insK (k : Nat) (c : Int) : Row → Row :=
  List.rec (motive := fun _ => Row) [(k, c)]
    (fun e L ih => Bool.rec (motive := fun _ => Row)
      (Bool.rec (motive := fun _ => Row) (e :: ih)
        (Bool.rec (motive := fun _ => Row) ((k, c + e.2) :: L) L (izero (c + e.2))) (Nat.beq k e.1))
      ((k, c) :: e :: L) (Nat.blt k e.1))

/-- sorted merge of two rows (sums of equal keys, zero sums dropped) -/
noncomputable def mergeK : Row → Row → Row :=
  List.rec (motive := fun _ => Row → Row) (fun b => b)
    (fun x xs ih b => List.rec (motive := fun _ => Row) (x :: xs)
      (fun y ys ihy => Bool.rec (motive := fun _ => Row)
        (Bool.rec (motive := fun _ => Row) (y :: ihy)
          (Bool.rec (motive := fun _ => Row) ((x.1, x.2 + y.2) :: ih ys) (ih ys) (izero (x.2 + y.2)))
          (Nat.beq x.1 y.1))
        (x :: ih (y :: ys)) (Nat.blt x.1 y.1)) b)

/-- `± z` -/
noncomputable def sgnI (ng : Bool) (z : Int) : Int := Bool.rec (motive := fun _ => Int) z (-z) ng

/-- the row times `± num / den`, exactly (every `z * num` divisible by `den`) -/
noncomputable def scaleK (ng : Bool) (num den : Nat) : Row → (Row → Bool) → Bool :=
  List.rec (motive := fun _ => (Row → Bool) → Bool) (fun k => k [])
    (fun e _ ih k => guard (izero (Int.emod (e.2 * (num : Int)) (den : Int)))
      (ih fun r => k ((e.1, sgnI ng (Int.ediv (e.2 * (num : Int)) (den : Int))) :: r)))

/-- `enc a`: the digit of the letter `a` (`+n ↦ 2n`, `-(n+1) ↦ 2n+1`) -/
noncomputable def encI (a : Int) : Nat := Int.rec (motive := fun _ => Nat) (fun n => 2 * n) (fun n => 2 * n + 1) a
/-- `enc (-a)` -/
noncomputable def encN (a : Int) : Nat := Int.rec (motive := fun _ => Nat) (fun n => 2 * n - 1) (fun n => 2 * n + 2) a

/-- the word code after the letter `a` acts (cancelling a leading `-a`) -/
noncomputable def wcode (B : Nat) (a : Int) (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (encI a + B * c) (c / B) (Nat.beq (c % B) (encN a))

/-- the key after the letter `a` acts -/
noncomputable def wkey (N B : Nat) (a : Int) (k : Nat) : Nat := k % N + N * wcode B a (k / N)

/-- the hub's `warp_row`: the letter `a` acts on every key; the row is sorted again -/
noncomputable def warpK (N B : Nat) (a : Int) (row : Row) : Row :=
  List.rec (motive := fun _ => Row) [] (fun e _ ih => insK (wkey N B a e.1) e.2 ih) row

/-- parameters of the scalar replay -/
structure SPw where
  /-- depth of the row trie -/
  d : Nat
  /-- number of registers (sources and rows `0 .. nr-1`) -/
  nr : Nat
  /-- key base (`nr ≤ N`) -/
  N : Nat
  /-- word code base (`enc a < B` for every op id) -/
  B : Nat
  /-- coefficient denominator -/
  D : Nat

/-- one add `t += (± num / den) s` -/
noncomputable def addS (q : SPw) (t s : Nat) (co : Co) (R : RT) (k : RT → Bool) : Bool :=
  guard (Nat.ble (Nat.succ t) q.nr) <| guard (Nat.ble (Nat.succ s) q.nr) <| guard (!(Nat.beq t s)) <|
  guard (!(Nat.beq co.den 0)) <|
  R.getK s fun rs => R.getK t fun rt => scaleK co.neg co.num co.den rs fun rs' => k (R.set t (mergeK rt rs'))

/-- the adds of a gate, forward (`o = false`) or dual (`o = true`: `s += -c t`) -/
noncomputable def addsS (q : SPw) (o : Bool) : List (Nat × Nat × Co) → RT → (RT → Bool) → Bool :=
  List.rec (motive := fun _ => RT → (RT → Bool) → Bool) (fun R k => k R)
    (fun x _ ih R k => Bool.rec (motive := fun _ => Bool)
      (addS q x.1 x.2.1 x.2.2 R fun R1 => ih R1 k)
      (addS q x.2.1 x.1 ⟨!x.2.2.neg, x.2.2.num, x.2.2.den⟩ R fun R1 => ih R1 k) o)

/-- **one event** of the scalar replay -/
noncomputable def evS (q : SPw) (o : Bool) (e : WEv) (R : RT) (k : RT → Bool) : Bool :=
  WEv.rec (motive := fun _ => Bool)
    (fun g => addsS q o g.adds R k)
    (fun _ r co => guard (Nat.ble (Nat.succ r) q.nr) <| guard (!(Nat.beq co.num 0)) <|
      guard (!(Nat.beq co.den 0)) <|
      R.getK r fun row => Bool.rec (motive := fun _ => Bool)
        (scaleK co.neg co.num co.den row fun row' => k (R.set r row'))
        (scaleK co.neg co.den co.num row fun row' => k (R.set r row')) o)
    (fun r a _ _ => guard (Nat.ble (Nat.succ r) q.nr) <| guard (opNe0 a) <|
      guard (Nat.ble (Nat.succ (encI a)) q.B) <| guard (Nat.ble (Nat.succ (encN a)) q.B) <|
      R.getK r fun row => k (R.set r (warpK q.N q.B a row)))
    (fun r _ => guard (Nat.ble (Nat.succ r) q.nr) (R.getK r fun _ => k (R.set r [])))
    (fun r => guard (Nat.ble (Nat.succ r) q.nr) (R.getK r fun _ => k (R.set r [])))
    (fun _ _ => k R) e

noncomputable def evsS (q : SPw) (o : Bool) : List WEv → RT → (RT → Bool) → Bool :=
  List.rec (motive := fun _ => RT → (RT → Bool) → Bool) (fun R k => k R)
    (fun e _ ih R k => evS q o e R fun R1 => ih R1 k)

/-- **the scalar replay of one segment** in orientation `o`: from the rows `R` the events end at the rows `R'` -/
noncomputable def scalW (q : SPw) (o : Bool) (evs : List WEv) (R R' : RT) : Bool :=
  guard (RT.wfK R q.d) <| guard (Nat.ble 1 q.N) <| guard (Nat.ble q.nr q.N) <|
  guard (Nat.ble q.nr (Nat.pow 2 q.d)) <|
  guard (Nat.ble 2 q.B) <| guard (Nat.ble 1 q.D) <|
  evsS q o evs R fun R1 => RT.beqK R1 R'

end KLW

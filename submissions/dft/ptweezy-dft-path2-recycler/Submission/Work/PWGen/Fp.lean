import Submission.Work.KLowW.ScalK
import Submission.Work.SharedSumChecker.Check

/-!
# (key: p-wgen) The word fingerprint of a warped word (core Lean only)

p-wgen, round wht45/lever, 19 Oct 2026.  A 64-bit FNV-1a hash of the Nat stream of a word's data: the event
list (`KLW.WEv`), the warp table (`KLW.WOp`), the retained totals, the scatter rows, the start and final frames.
p-wgen's generator (`tools/wgen.py`, function `fp_nats`) computes the same stream and hash in Python; each generated
word module states `fpWord ... = n` with the Python value and proves it `by decide +kernel`, so the Lean data and
the Python file it came from are tied together ("Python and Lean word hashes agree").

Stream: a list is its length, then its items; `Co` is `neg (0/1), num, den`; a gate is `0, f, s, targets, extras`
(`out`) or `1, f, t, sources` (`inn`); an event is `0, gate` / `5, f, r, co` / `2, r, enc a, f0, f1` / `3, r, f` /
`4, r` / `6, r, f` (`g` / `sc` / `w` / `za` / `zf` / `dn`; `enc (+n) = 2n`, `enc (-(n+1)) = 2n+1`).  Every step is forced (`forceN`),
so the kernel never builds a chain of unevaluated additions.  No `sorry`.
-/

namespace PWG
open GXD KLW

/-- one FNV-1a step (64 bits) -/
noncomputable def mix (h x : Nat) : Nat :=
  Nat.mod (Nat.mul (Nat.xor h x) 1099511628211) 18446744073709551616

/-- feed one number -/
noncomputable def nat (x : Nat) (h : Nat) : Nat := SSC.forceN (mix h x) fun y => y

/-- length of a list (structural, kernel-friendly) -/
noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

/-- feed a list: its length, then every item -/
noncomputable def lst {α : Type} (f : α → Nat → Nat) (l : List α) (h : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun h => h) (fun a _ ih h => SSC.forceN (f a h) ih) l (nat (lenK l) h)

noncomputable def bit (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) 0 1 b

noncomputable def co (k : Co) (h : Nat) : Nat := nat k.den (nat k.num (nat (bit k.neg) h))

noncomputable def pc (x : Nat × Co) (h : Nat) : Nat := co x.2 (nat x.1 h)

noncomputable def pn (x : Nat × Nat) (h : Nat) : Nat := nat x.2 (nat x.1 h)

noncomputable def gate (g : Gate) (h : Nat) : Nat :=
  Gate.rec (motive := fun _ => Nat)
    (fun f s ts ex => lst nat ex (lst pc ts (nat s (nat f (nat 0 h)))))
    (fun f t ss => lst pc ss (nat t (nat f (nat 1 h)))) g

noncomputable def ev (e : WEv) (h : Nat) : Nat :=
  WEv.rec (motive := fun _ => Nat)
    (fun g => gate g (nat 0 h))
    (fun f r k => co k (nat r (nat f (nat 5 h))))
    (fun r a f0 f1 => nat f1 (nat f0 (nat (encI a) (nat r (nat 2 h)))))
    (fun r f => nat f (nat r (nat 3 h)))
    (fun r => nat r (nat 4 h))
    (fun r f => nat f (nat r (nat 6 h))) e

noncomputable def wop (o : WOp) (h : Nat) : Nat := lst nat o.Gi (lst nat o.G h)

/-- **the word fingerprint** (FNV offset basis 14695981039346656037) -/
noncomputable def fpWord (evs : List WEv) (wt : List WOp) (ret : List (Nat × Nat))
    (scat : List (List (Nat × Co))) (start final : List Nat) : Nat :=
  lst nat final (lst nat start (lst (lst pc) scat (lst pn ret (lst wop wt
    (lst ev evs 14695981039346656037)))))

end PWG

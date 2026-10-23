/-!
# XHost.HostK: the host table of a run, checked by the kernel (`hostK`)

Same-run hosting (h-L3-design, 13 Oct 2026): ONE table for every run (the hosting programme is block-diagonal: run `ρ`
feeds only the idle climbs of replica `ρ`).  Row `l` (stage `l`, 9 rows) lists, for every slot `q` (`R` slots), `0`
(not hosted: the slot goes to a bank, schedule `use`) or `i + 1`, the host `i = (c * 2 + side) * nT + t`: window kind
`c` (0..8 = A2 B2 A3 B3 A4 B4 F1 F2 F3, idle climbs of Shea's complex588 network: Work/Bridge401/GNetStage.lean),
side X/Y, class `t < nT`.  `rem` = the remainder rank of every host, `res` = the residual `9 - e_q` of every slot.

`hostK` checks: 9 rows of length `R`; every entry `0` or a host whose window holds the stage, no host twice in a row
(a `Nat` bitset: ONE residual per role per invocation); `rem i ≤ rank (c i)`; residuals `< 10`; and the packed sum
`Σ_l Σ_q res q * 2^(7 (e - 1)) = Σ_i (rank (c i) - rem i) * 2^(7 i)` (digit-wise, every host's load is
`rank - rem`; a digit is at most `9 * 9 < 2^7`).  Modelled on Shea's / Mamano's `schedK` (Work/Bridge401/SchedK.lean).
Core Lean only.  The soundness lemma (`hostK = true →` the window, injectivity and load facts as Props) is the port of
`schedK_parts` / `digits_unique` and is NOT in this file yet.  Prepared with assistance from Claude.
-/

namespace OAI
namespace PowerSaving
namespace XHost

/-- window table: kind `c` holds stage `l`. -/
def inWin (c l : Nat) : Bool :=
  match c with
  | 0 => l < 2
  | 1 => l == 2
  | 2 => l < 4
  | 3 => l == 4
  | 4 => l < 6
  | 5 => l == 6
  | 6 => 3 ≤ l && l < 9
  | 7 => 5 ≤ l && l < 9
  | 8 => 7 ≤ l && l < 9
  | _ => false

/-- the rank of the idle climb of kind `c` (`bcost` ranks of GNetDef: 16 8 32 8 48 8 48 32 16). -/
def rankOf (c : Nat) : Nat :=
  match c with
  | 0 => 16
  | 1 => 8
  | 2 => 32
  | 3 => 8
  | 4 => 48
  | 5 => 8
  | 6 => 48
  | 7 => 32
  | 8 => 16
  | _ => 0

/-- one row: entries `0` or a host `e - 1 < 18 nT` whose window holds stage `l`, no host twice. -/
def hkRow (nT l : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | seen, e :: es =>
    (e == 0 || (decide (e ≤ 18 * nT) && inWin ((e - 1) / (2 * nT)) l && !(seen.testBit e))) &&
      hkRow nT l (if e == 0 then seen else seen ||| (1 <<< e)) es

/-- all rows, with their stage index. -/
def hkRows (nT R : Nat) : Nat → List (List Nat) → Bool
  | _, [] => true
  | l, row :: rows => (row.length == R) && hkRow nT l 0 row && hkRows nT R (l + 1) rows

/-- the packed hosted residuals of one row. -/
def hkSum : List Nat → List Nat → Nat
  | e :: es, r :: rs => (if e == 0 then 0 else r <<< (7 * (e - 1))) + hkSum es rs
  | _, _ => 0

/-- the remainders fit. -/
def hkRem (nT : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | i, m :: ms => decide (m ≤ rankOf (i / (2 * nT))) && hkRem nT (i + 1) ms

/-- the packed target loads `rank - rem`. -/
def hkTgt (nT : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | i, m :: ms => ((rankOf (i / (2 * nT)) - m) <<< (7 * i)) + hkTgt nT (i + 1) ms

/-- the sum of a list (left fold). -/
def hkTot : List Nat → Nat
  | [] => 0
  | x :: xs => x + hkTot xs

/-- **The host-table check.** -/
def hostK (nT R : Nat) (rows : List (List Nat)) (rem res : List Nat) : Bool :=
  (rows.length == 9) && hkRows nT R 0 rows && (rem.length == 18 * nT) && hkRem nT 0 rem &&
    (res.length == R) && res.all (fun r => decide (r < 10)) &&
    (hkTot (rows.map (fun row => hkSum row res)) == hkTgt nT 0 rem)

/-- the price of the remainders: the histogram of remainder ranks (rank `m ↦` count), as a checked list. -/
def hkHist (m : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if x == m then 1 else 0) + hkHist m xs

end XHost
end PowerSaving
end OAI

import Mathlib

/-!
# Trusted statement for Subset Sum on a randomized word RAM

Modeled on `challenges/3sum-apsp/EndStatement.lean` (Anthropic's trusted word
RAM), extended with a random-word instruction, per the problem page at
https://bigospeedrun.com/subset-sum.

Imports Mathlib, proves nothing.
-/

namespace SubsetSumStatement

/-- `i j k` name cells, `l` a position in the program, `[i]` is the word in cell
`i`. The only constant is 1. `rand` draws the next independent uniform word. -/
inductive Instr where
  | one (i : Int)             -- [i] := 1
  | add (i j k : Int)         -- [i] := [j] + [k]
  | sub (i j k : Int)         -- [i] := [j] - [k]
  | mul (i j k : Int)         -- [i] := [j] * [k]
  | load (i j : Int)          -- [i] := [[j]]
  | store (i j : Int)         -- [[i]] := [j]
  | rand (i : Int)            -- [i] := next uniform random word
  | bltz (i : Int) (l : Nat)  -- if [i] < 0, go to position l
  | accept
  | reject

/-- The verdict and the final memory, if `P`, run from position `pc` with `r`
random words already drawn, on memory `m`, halts within `t` steps, the halting
step counted; past its end `P` rejects. Addresses are read signed; `bltz` jumps
on a negative word; `write` runs on. Each `rand` draws `ρ r`, the `r`-th word
of the tape `ρ`. -/
def exec {W : Nat} (P : List Instr) (ρ : Nat → BitVec W) :
    (t r pc : Nat) → (m : Int → BitVec W) → Option (Bool × (Int → BitVec W))
  | 0, _, _, _ => none
  | t + 1, r, pc, m =>
    let write (i : Int) (v : BitVec W) :=
      exec P ρ t (r + 1) (pc + 1) fun x => if x = i then v else m x
    match P.getD pc .reject with
    | .one i => write i 1
    | .add i j k => write i (m j + m k)
    | .sub i j k => write i (m j - m k)
    | .mul i j k => write i (m j * m k)
    | .load i j => write i (m (m j).toInt)
    | .store i j => write (m i).toInt (m j)
    | .rand i => write i (ρ r)
    | .bltz i l => exec P ρ t (r + 1) (if (m i).toInt < 0 then l else pc + 1) m
    | .accept => some (true, m)
    | .reject => some (false, m)

/-- The memory at the start: `ws` in cells 0, 1, 2, …, and 0 in every other
cell. -/
def loadWords (W : Nat) (ws : List Int) : Int → BitVec W :=
  fun a => if a < 0 then 0 else BitVec.ofInt W (ws.getD a.toNat 0)

/-- A run consumes at most `t` random words in `t` steps, so a tape prefix of
length `t` determines the run; this embeds such a prefix into a tape. -/
def tapeOf {W t : Nat} (τ : Fin t → BitVec W) : Nat → BitVec W :=
  fun i => if h : i < t then τ ⟨i, h⟩ else 0

/-- `T(n) = O(2^(α·n))` for a rational `α ≥ 0`, both sides raised to the power
`α.den`, mirroring the polynomial `BigO` of the 3SUM/APSP statement: for
`α = 501/1000` it says `T(n)^1000 ≤ K · 2^(501·n)`. -/
def BigOExp (T : Nat → Nat) (α : Rat) : Prop :=
  ∃ K : Nat, ∀ n ≥ 2, T n ^ α.den ≤ K * 2 ^ (α.num.toNat * n)

/-- `yes`: when to accept. `output`: a condition on the cells after the input,
read as signed (unused for this decision problem; kept for shape parity with
the trusted 3SUM/APSP statement). -/
structure Problem where
  Instance : Nat → Type
  input {n : Nat} : Instance n → List Int
  yes {n : Nat} : Instance n → Prop := fun _ => True
  output {n : Nat} : Instance n → (Nat → Int) → Prop := fun _ _ => True

/-- One run on tape `ρ`: with `n` in cell 0 and the input after it, `P` halts
within `t` steps with the right verdict. -/
def Problem.Run (Q : Problem) {n : Nat} (x : Q.Instance n) (P : List Instr)
    (W t : Nat) (ρ : Nat → BitVec W) : Prop :=
  ∃ verdict m, exec P ρ t 0 0 (loadWords W ((n : Int) :: Q.input x)) = some (verdict, m) ∧
    (verdict = true ↔ Q.yes x) ∧ Q.output x fun a =>
      (m (1 + (Q.input x).length + a : Nat)).toInt

open Classical in
/-- `P` solves `x` at word width `W` within `t` steps: it halts within `t`
steps on EVERY random outcome, and its verdict is correct with probability at
least `2/3` when the tape prefix is drawn uniformly — the run depends only on
the first `t` tape words, so the count is over `(Fin t → BitVec W)`, all
`2^(W·t)` prefixes equally likely. A deterministic `P` (no `rand`) reads no
tape, so this probability is 1. -/
def Problem.Solves (Q : Problem) {n : Nat} (x : Q.Instance n) (P : List Instr)
    (W t : Nat) : Prop :=
  (∀ ρ : Nat → BitVec W, (exec P ρ t 0 0 (loadWords W ((n : Int) :: Q.input x))).isSome) ∧
    3 * (Finset.univ.filter (fun τ : Fin t → BitVec W =>
        decide (Q.Run x P W t (tapeOf τ)))).card
      ≥ 2 * Fintype.card (Fin t → BitVec W)

/-- Bit length of a nonnegative-or-signed integer's magnitude, `1` for `0`. -/
def bitLen (z : Int) : Nat := z.natAbs.log2 + 1

/-- The problem: positive integers `a₁ … aₙ` and a nonnegative target `t`;
decide whether a subset of the positions sums to `t`. Repeats among the `aᵢ`
and the empty subset (sum 0) are allowed. -/
def SubsetSum : Problem where
  Instance n := {p : (Fin n → Int) × Int // (∀ i, 0 < p.1 i) ∧ 0 ≤ p.2}
  input := fun ⟨(a, t), _⟩ => List.ofFn a ++ [t]
  yes := fun {n} ⟨(a, t), _⟩ => ∃ mask : Finset (Fin n), (∑ i ∈ mask, a i) = t

/-- `b`, the maximum input or target bit length of an instance. -/
def maxBitOf {n : Nat} (x : SubsetSum.Instance n) : Nat :=
  ((List.ofFn x.1.1) ++ [x.1.2]).map bitLen |>.foldl max 0

/-- The page's word width `w = ⌈4(n + b + log₂(n + 2))⌉`; with floor-`log₂`
and natural-number arithmetic the inside is already an integer. -/
def wordWidth (n b : Nat) : Nat := 4 * (n + b + Nat.log2 (n + 2))

/-- A single uniform program `P` (not depending on `c`) runs in time
`T(n) = O(2^(α·n))` — the step bound holds for EVERY random outcome — and is
correct with probability at least `2/3`, at the page's word width
`w = ⌈4(n + b + log₂(n + 2))⌉` where `b` is the instance's maximum input or
target bit length, for every instance with `b ≤ n^c`, for each fixed `c`.
The parameter `α` (range `0 ≤ α ≤ 1`, smaller is better) is the time exponent
the verifier substitutes; `Race.bound` asserts this proposition. -/
def SubsetSum.SolvedInTime (α : Rat) : Prop :=
  ∃ (P : List Instr) (T : Nat → Nat), BigOExp T α ∧
    ∀ (c n : Nat) (x : SubsetSum.Instance n), 2 ≤ n → maxBitOf x ≤ n ^ c →
      SubsetSum.Solves x P (wordWidth n (maxBitOf x)) (T n)

end SubsetSumStatement

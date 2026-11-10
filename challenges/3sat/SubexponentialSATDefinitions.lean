import Mathlib

namespace OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

def bitVal (b : Bool) : ℕ := if b then 1 else 0

def toNat : List Bool → ℕ
  | [] => 0
  | b :: bs => bitVal b + 2 * toNat bs

end OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms.SubexponentialSAT.SAT

universe u

abbrev Assignment (V : Type u) := V → Bool

structure Literal (V : Type u) where
  «variable» : V
  positive : Bool
  deriving DecidableEq

abbrev Clause (V : Type u) := Finset (Literal V)
abbrev CNF (V : Type u) := Finset (Clause V)

variable {V : Type u} [DecidableEq V]

def Literal.eval (a : Assignment V) (l : Literal V) : Bool :=
  a l.variable == l.positive

def Clause.eval (a : Assignment V) (C : Clause V) : Bool :=
  decide (∃ l ∈ C, l.eval a = true)

def CNF.eval (a : Assignment V) (F : CNF V) : Bool :=
  decide (∀ C ∈ F, C.eval a = true)

def WidthAtMost (k : ℕ) (F : CNF V) : Prop := ∀ C ∈ F, C.card ≤ k

section Finite

variable [Fintype V]

def satisfyingAssignments (F : CNF V) : Finset (Assignment V) :=
  Finset.univ.filter fun a => F.eval a = true

def count (F : CNF V) : ℕ := (satisfyingAssignments F).card

end Finite

end OAI.Algorithms.SubexponentialSAT.SAT

namespace OAI.Algorithms.SubexponentialSAT.Encoding

def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

def frame (bits : List Bool) : List Bool :=
  bits.foldr (fun b rest => true :: b :: rest) [false]

def encodeList {α : Type*} (enc : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: as => true :: (frame (enc a) ++ encodeList enc as)

def literalCode {n : ℕ} (l : SAT.Literal (Fin n)) : ℕ :=
  2 * l.variable.val + if l.positive then 1 else 0

def clauseNumbers {n : ℕ} (C : SAT.Clause (Fin n)) : List ℕ :=
  (C.image literalCode).sort (· ≤ ·)

def cnfNumbers {n : ℕ} (F : SAT.CNF (Fin n)) : List (List ℕ) :=
  (F.image clauseNumbers).sort (· ≤ ·)

def encodeCNFBody {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeList (encodeList encodeNat) (cnfNumbers F)

def encodeCNF {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeNat n ++ encodeCNFBody F

def formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) : ℕ := (encodeCNF F).length

end OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms.SubexponentialSAT.Computation

universe u

inductive Trace {α : Type u} (step : α → Option α) : ℕ → α → α → Prop
  | refl (a : α) : Trace step 0 a a
  | cons {n : ℕ} {a b c : α} :
      step a = some b → Trace step n b c → Trace step (n + 1) a c

structure PrimitiveMachine where
  tapeCount : ℕ
  stateCount : ℕ
  inputTape : Fin tapeCount
  start : Fin stateCount
  scan : Fin stateCount → Fin tapeCount
  transition : Fin stateCount → Option Bool →
    Bool ⊕ (Fin stateCount × Turing.TM0.Stmt (Option Bool))

namespace PrimitiveMachine

structure Cfg (machine : PrimitiveMachine) where
  state : Bool ⊕ Fin machine.stateCount
  tapes : Fin machine.tapeCount → Turing.Tape (Option Bool)

def step (machine : PrimitiveMachine) (c : machine.Cfg) : Option machine.Cfg :=
  match c.state with
  | .inl _ => none
  | .inr q =>
    let tapeIndex := machine.scan q
    match machine.transition q (c.tapes tapeIndex).head with
    | .inl answer => some ⟨.inl answer, c.tapes⟩
    | .inr (q', action) =>
      let nextTape :=
        match action with
        | .move direction => (c.tapes tapeIndex).move direction
        | .write symbol => (c.tapes tapeIndex).write symbol
      some ⟨.inr q', Function.update c.tapes tapeIndex nextTape⟩

def init (machine : PrimitiveMachine) (input : List Bool) : machine.Cfg :=
  ⟨.inr machine.start, fun k =>
    if k = machine.inputTape then Turing.Tape.mk₁ (input.map some)
    else Turing.Tape.mk₁ []⟩

end PrimitiveMachine

end OAI.Algorithms.SubexponentialSAT.Computation

import OrderedMatrixRemoval4.Repairs
import Lean.Util.CollectAxioms

open OrderedMatrixRemoval4 OrderedMatrixRemoval4.Host

-- Literal pattern from the source's theorem statement, independent of H4's name.
def auditPattern : BinaryMatrix 4 := fun r c =>
  match r.val with
  | 0 => c.val == 1 || c.val == 2
  | 1 => c.val == 0 || c.val == 3
  | 2 => c.val == 0 || c.val == 2
  | _ => c.val == 1 || c.val == 2 || c.val == 3

example : ∀ r c : Fin 4, H4 r c = auditPattern r c := by decide

-- Every alternative binary matrix is quantified, and both directions of a
-- physical cell change contribute to the edit count.
example (h : Nat) (hh : 1 ≤ h) :
    HFree H4 (TerminalAnchorRepair.matrix h) ∧
    Host.editCount h (TerminalAnchorRepair.matrix h) = (2 ^ h) ^ 2 ∧
    ∀ B : BinaryMatrix (size h), HFree H4 B →
      (2 ^ h) ^ 2 ≤ Host.editCount h B := by
  exact TerminalAnchorRepair.exact_minimum h hh

open Lean in
run_cmd do
  let axioms ← collectAxioms `OrderedMatrixRemoval4.Host.TerminalAnchorRepair.exact_minimum
  IO.println s!"AUDIT_AXIOMS={String.intercalate "," (axioms.toList.map toString)}"
  IO.println "AUDIT_SCOPE=passed"

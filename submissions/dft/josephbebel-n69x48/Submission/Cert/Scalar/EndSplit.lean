import Submission.Cert.Scalar.Checker

/-! Subtree form of PR 209's end check (written for this submission).

`ScalarCheck.checkEnd c d R G` packs every row of `R` and compares it with the leaf of `G`; on one key chain of
1292 digits of 993 bits every packed row is a 1.28 Mbit number, so a single declaration holds thousands of them.
`checkEndSub` is the same check on the subtree at (`key`, `bit`), and `checkEndSub_node` composes the checks of
the two children, so the end check can be split over many small declarations.  Written for this submission (Claude, Anthropic); it
uses only PR 209's `packT`, `ghostEq` and `checkEnd` (Submission/Cert/Scalar/Checker.lean, HalitZiyaKARTAL v7-42). -/

namespace ScalarCheck.EndSplit
open WarpCheck ScalarCheck

noncomputable def checkEndSub (c : Cx) (d : Nat) (R : RT) (G : PT) (key bit : Nat) : Bool :=
  match packT c d R key bit with
  | none => false
  | some A => ghostEq c A G

def RT.child : RT → Bool → RT
  | .node l _, false => l
  | .node _ r, true => r
  | t, _ => t

def PT.child : PT → Bool → PT
  | .node l _, false => l
  | .node _ r, true => r
  | t, _ => t

def RT.isNode : RT → Bool
  | .node _ _ => true
  | .leaf _ => false

def PT.isNode : PT → Bool
  | .node _ _ => true
  | .leaf _ => false

theorem checkEnd_eq (c : Cx) (d : Nat) (R : RT) (G : PT) : checkEnd c d R G = checkEndSub c d R G 0 1 := rfl

theorem checkEndSub_node {c : Cx} {d : Nat} {R : RT} {G : PT} {key bit : Nat}
    (hR : RT.isNode R = true) (hG : PT.isNode G = true)
    (hl : checkEndSub c d (RT.child R false) (PT.child G false) key (2 * bit) = true)
    (hr : checkEndSub c d (RT.child R true) (PT.child G true) (key + bit) (2 * bit) = true) :
    checkEndSub c (d + 1) R G key bit = true := by
  cases R with
  | leaf _ => cases hR
  | node l r =>
    cases G with
    | leaf _ => cases hG
    | node a b =>
      simp only [RT.child, PT.child] at hl hr
      unfold checkEndSub at hl hr ⊢
      cases hpl : packT c d l key (2 * bit) with
      | none => rw [hpl] at hl; cases hl
      | some A =>
        cases hpr : packT c d r (key + bit) (2 * bit) with
        | none => rw [hpr] at hr; cases hr
        | some B =>
          rw [hpl] at hl; rw [hpr] at hr
          have e : packT c (d + 1) (.node l r) key bit = some (.node A B) := by
            simp only [packT, Nat.mul_eq, Nat.add_eq, hpl, hpr]; rfl
          rw [e]
          show (ghostEq c A a && ghostEq c B b) = true
          have hl' : ghostEq c A a = true := hl
          have hr' : ghostEq c B b = true := hr
          rw [hl', hr']; rfl

end ScalarCheck.EndSplit

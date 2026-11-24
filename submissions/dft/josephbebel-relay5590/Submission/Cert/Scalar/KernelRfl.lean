import Lean.Elab.Command

/-! `kernel_rfl name : lhs = rhs` adds the theorem `name` with proof `Eq.refl rhs`, checked only by the
kernel (like `decide +kernel`, without the elaborator's defeq).  Untrusted meta code: the declaration is an
ordinary theorem that the kernel (and every replay) re-checks.  Written for this submission (Claude, Anthropic). -/

open Lean Elab Command Term Meta in
elab "kernel_rfl " n:ident " : " t:term : command => do
  liftTermElabM do
    let ty ← elabTerm t (some (mkSort .zero))
    synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let some (α, _, rhs) := ty.eq? | throwError "kernel_rfl: equation expected"
    if ty.hasMVar then throwError "kernel_rfl: statement has metavariables"
    let u ← getLevel α
    let val := mkApp2 (mkConst ``Eq.refl [u]) α rhs
    addDecl (.thmDecl { name := (← getCurrNamespace) ++ n.getId, levelParams := [], type := ty, value := val })

# Dependency cache review, 2026-10-11

The deployed DFT controller pins Comparator
`d03acab154d269c06e60e4de7e4cc85deebff94b` and lean4export
`076e8e57707e813375e8f9da8bf989799ace9680`.

Comparator's [runBuiltinKernel](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/Main.lean#L210)
creates an empty Lean environment and replays the exported constant map through
`kernelEnv.replay`. It removes the three quotient auxiliary constants that the
kernel generates itself, then checks their definitions against the exported ones.
`verifyMatch` compares the trusted challenge and solution, audits permitted
axioms, and invokes that kernel before returning acceptance.

The pinned exporter's [dumpConstant](https://github.com/leanprover/lean4export/blob/076e8e57707e813375e8f9da8bf989799ace9680/Export.lean#L236)
recursively calls `dumpDeps` on declaration types and values, including theorem
proofs. It does not exempt Mathlib declarations. Thus the kernel checks the
transitive declaration closure used by the submitted targets, including their
Mathlib dependencies. The separate Comparator axiom traversal also follows used
constants. This is not a claim that it checks every unused declaration in Mathlib.

The official Mathlib cache at the pinned dependency commit is compatible with
this gate. The current controller already clones the exact manifest revisions
and runs `lake exe cache get` from trusted setup, then mounts dependencies
read-only. Submitted `.olean` files, Lake config, and hooks are never accepted.
No cache policy has been relaxed for this speed change.

The measured previous DFT run took about 89 minutes for source build plus Lean
and audit, then about 48 minutes for nanoda. Early publication removes nanoda
from the first-result wait: expected roughly 90–95 minutes including setup for
this proof on the same runner, followed by the advisory update. This is an
estimate from the previous run, not a new speed benchmark. The official Mathlib
cache is already in use, so enabling it again cannot remove the source build.

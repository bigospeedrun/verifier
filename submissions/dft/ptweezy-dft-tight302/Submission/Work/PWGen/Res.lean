import Submission.Work.KLowW.InvMain

/-!
# (key: p-wgen) The bank residual of a slot of a warp certificate, independent of the package

p-wgen, round wht45/lever, 19 Oct 2026.  `KLW.WValidS.inv_res` (p-warpchk) states the residual of a slot for the
package `inv`, which needs warp meanings at every frame map.  The windowed package `invW` has the SAME entrance and
exit labels (`c.ent emb`, `c.exq emb`), so the residual is a statement about the certificate alone; this is
p-warpchk's proof of `inv_res` after its first `show`, unchanged.  No `sorry`.
-/

namespace PWG
open SSC GXD GLab OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.SS OAI.PowerSaving.CB OAI.PowerSaving.BR OAI.PowerSaving.GX OAI.PowerSaving.XEX KLW Finset Matrix

variable {c : WCert} {emb : Box (Fin c.v) (Fin c.R) (Fin c.nc) → Nat} {un : Nat → Box (Fin c.v) (Fin c.R) (Fin c.nc)}

/-- the bank residual of a slot: `dim(end) - dim(start)` for an exit slot, `h - dim(start)` otherwise -/
theorem res (V : WValidS c) (Ro : WRoles c emb un) (q : Fin c.R) :
    (c.exq emb q).dim - (c.ent emb q).dim
      = Bool.rec (motive := fun _ => Nat) (c.p.h - cdim (c.p.tab.get (c.S0.get (2 * c.v + q.val))))
          (cdim (c.p.tab.get (c.SF.get (2 * c.v + q.val))) - cdim (c.p.tab.get (c.S0.get (2 * c.v + q.val))))
          (memK (2 * c.v + q.val) c.el) := by
  have hU : (c.L emb c.S0 (CR.lS q)).dim = cdim (c.p.tab.get (c.S0.get (2 * c.v + q.val))) := by
    show (GLab.lab c.p.h (c.p.tab.get (c.S0.get (emb (bS q))))).dim = _
    rw [Ro.num.hs q, V.dim]
  have hV : (c.L emb c.SF (CR.lS q)).dim = cdim (c.p.tab.get (c.SF.get (2 * c.v + q.val))) := by
    show (GLab.lab c.p.h (c.p.tab.get (c.SF.get (emb (bS q))))).dim = _
    rw [Ro.num.hs q, V.dim]
  unfold WCert.exq WCert.ent
  cases hm : memK (2 * c.v + q.val) c.el with
  | false =>
    have hq : q ∉ c.exits := fun h => by
      have := (Finset.mem_filter.mp h).2; rw [hm] at this; exact Bool.false_ne_true this
    rw [if_neg hq, SLbl.top_dim, Fintype.card_fin, XEX.lab0X_nE _ _ _ hq, hU]
  | true =>
    have hq : q ∈ c.exits := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    rw [if_pos hq, XEX.lab0X_E _ _ _ hq, XEX.exlA_dim _ _ (V.hsub Ro q hq), XEX.entA_dim _ _ (V.hsub Ro q hq),
      hU, hV]


end PWG

#print axioms PWG.res

import Submission.Work.KLowW.Inv

/-!
# (key: p-wgen) The canonical role numbering of a warp certificate

p-wgen, round wht45/lever, 19 Oct 2026.  p-warpchk's `KLW.WValid.inv` / `invW` take the role hypotheses
`KLW.WRoles c emb un` (a `GLab.Ctx` and the numbering `KLW.Num`).  This file gives them once for every certificate
with the generator's numbering: x `t ↦ t`, y `t ↦ v + t`, slot `q ↦ 2v + q`, scratch `k ↦ 2v + R + k` (zero buffers,
then centre copies).  No `sorry`.
-/

namespace PWG
open OAI.PowerSaving OAI.PowerSaving.SS KLW GLab

variable {v R nc : Nat}

/-- the register of a role -/
def embB (v R nc : Nat) : Box (Fin v) (Fin R) (Fin nc) → Nat :=
  stamp (fun t => t.val) (fun t => v + t.val) (fun q => 2 * v + q.val) (fun k => 2 * v + R + k.val)

/-- the role of a register (registers past the end go to scratch `0`) -/
def unB (v R nc : Nat) (hc : 0 < nc) (r : Nat) : Box (Fin v) (Fin R) (Fin nc) :=
  if h1 : r < v then bX ⟨r, h1⟩
  else if h2 : r < 2 * v then bY ⟨r - v, by omega⟩
  else if h3 : r < 2 * v + R then bS ⟨r - 2 * v, by omega⟩
  else if h4 : r < 2 * v + R + nc then bC ⟨r - (2 * v + R), by omega⟩
  else bC ⟨0, hc⟩

theorem unB_embB (hc : 0 < nc) (j : Box (Fin v) (Fin R) (Fin nc)) : unB v R nc hc (embB v R nc j) = j := by
  rcases j with ((t | t) | (q | k))
  · have ht := t.isLt
    show unB v R nc hc t.val = bX t
    unfold unB
    rw [dif_pos ht]
  · have ht := t.isLt
    show unB v R nc hc (v + t.val) = bY t
    unfold unB
    rw [dif_neg (show ¬ (v + t.val < v) by omega), dif_pos (show v + t.val < 2 * v by omega)]
    exact congrArg bY (Fin.ext (Nat.add_sub_cancel_left _ _))
  · have hq := q.isLt
    show unB v R nc hc (2 * v + q.val) = bS q
    unfold unB
    rw [dif_neg (show ¬ (2 * v + q.val < v) by omega), dif_neg (show ¬ (2 * v + q.val < 2 * v) by omega),
      dif_pos (show 2 * v + q.val < 2 * v + R by omega)]
    exact congrArg bS (Fin.ext (Nat.add_sub_cancel_left _ _))
  · have hk := k.isLt
    show unB v R nc hc (2 * v + R + k.val) = bC k
    unfold unB
    rw [dif_neg (show ¬ (2 * v + R + k.val < v) by omega), dif_neg (show ¬ (2 * v + R + k.val < 2 * v) by omega),
      dif_neg (show ¬ (2 * v + R + k.val < 2 * v + R) by omega),
      dif_pos (show 2 * v + R + k.val < 2 * v + R + nc by omega)]
    exact congrArg bC (Fin.ext (Nat.add_sub_cancel_left _ _))

theorem embB_unB (hc : 0 < nc) (r : Nat) (hr : r < 2 * v + R + nc) : embB v R nc (unB v R nc hc r) = r := by
  unfold unB
  split_ifs with h1 h2 h3
  · rfl
  · show v + (r - v) = r
    omega
  · show 2 * v + (r - 2 * v) = r
    omega
  · show 2 * v + R + (r - (2 * v + R)) = r
    omega

theorem embB_lt (j : Box (Fin v) (Fin R) (Fin nc)) : embB v R nc j < 2 * v + R + nc := by
  rcases j with ((t | t) | (q | k))
  · show t.val < _
    have := t.isLt
    omega
  · show v + t.val < _
    have := t.isLt
    omega
  · show 2 * v + q.val < _
    have := q.isLt
    omega
  · show 2 * v + R + k.val < _
    have := k.isLt
    omega

/-- **the role hypotheses** of a valid warp certificate with the canonical numbering -/
theorem roles (c : WCert) (V : WValid c) (hd : c.p.n ≤ 2 ^ c.p.d) (hc : 0 < c.nc) :
    WRoles c (embB c.v c.R c.nc) (unB c.v c.R c.nc hc) where
  C :=
    { hT := V.tab
      hn := hd
      hun := unB_embB hc
      hin := fun r hr => embB_unB hc r (by rw [V.hn] at hr; exact hr)
      hlt := fun j => by rw [V.hn]; exact embB_lt j }
  num :=
    { hx := fun _ => rfl
      hy := fun _ => rfl
      hs := fun _ => rfl
      hc := fun k => by
        show 2 * c.v + c.R ≤ 2 * c.v + c.R + k.val
        omega }

end PWG

#print axioms PWG.roles

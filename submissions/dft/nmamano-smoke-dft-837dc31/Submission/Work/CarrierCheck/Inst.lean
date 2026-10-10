import Submission.Work.CarrierCheck.Hid
import Submission.Work.Combine.Hist

/-!
# (key: carrier-check) A kernel-checked carrier certificate is a `CR.Phased`, hence an `Inv`

    CCert.Valid.of_checks : c.labelCheck = true → c.shapeCheck = true → c.Valid      (Valid.lean)
    CCert.Valid.phased    : c.Valid → c.scalarCheck = true →
                              CR.Phased (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.ret.length)
    CCert.Valid.phased_cost : (V.phased hs).cost φ = rcost φ c.invRanks
    (Work.CarrierCheck.Inv:  CCert.Valid.inv : ... → BR.Inv .. := (V.phased hs).inv,  inv_cost)
    CCert.rcost_sumW      : rcost φ c.invRanks = ∑ r ≤ B, (c.sumW (wEq r)) * bcost φ r
                            (the counts `c.sumW (wEq r)` are evaluated by the kernel)

So the three Boolean checks of a carrier certificate give the invocation package of the bridged
network (`Work/Bridge/Inv.lean`) through the carrier invocation theorem `CR.Phased.inv`
(`Work/Carrier/PhasedInv.lean`), with the price of ALL blocks of one invocation: x roles, y roles,
helper slots, scratch copies.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR OAI.PowerSaving.BR Finset Matrix

namespace CCert
variable {c : CCert}

theorem emb3_x (c : CCert) (t : Fin c.v) : c.emb3 (Sum.inl (Sum.inl t)) = t.val := rfl
theorem emb3_y (c : CCert) (S : Fin c.v) : c.emb3 (Sum.inl (Sum.inr S)) = c.v + c.R + S.val := rfl
theorem emb3_s (c : CCert) (q : Fin c.R) : c.emb3 (Sum.inr q) = c.v + q.val := rfl

theorem Valid.kx (V : c.Valid) (t : Fin c.v) : Climb (lineL (c.tv t)) fullL := by
  have C := V.complete3
  have h := C.climb (Sum.inl (Sum.inl t)) [] c.tot [] (by simp)
  rw [List.nil_append, emb3_x] at h
  have e : runLab c.p c.lab0 [] t.val = c.lab0 t.val := rfl
  have hlt : t.val < c.n := by have := t.isLt; unfold n; omega
  rw [e, V.line t, V.fullLb t.val hlt] at h
  exact h

theorem Valid.ky (V : c.Valid) (t : Fin c.v) : Climb zeroL (perpL (c.tv t)) := by
  have C := V.complete3
  have h := C.climb (Sum.inl (Sum.inr t)) [] c.aB (c.mF ++ c.mY)
    (by simp only [tot, List.nil_append, List.append_assoc])
  rw [List.nil_append, emb3_y] at h
  have e : runLab c.p c.lab0 [] (c.v + c.R + t.val) = 0 :=
    V.lab0_ge (c.v + c.R + t.val) (by omega)
  rw [e, Lb_zero, V.yB t] at h
  exact h

theorem Valid.kc (V : c.Valid) (k : Fin c.ret.length) :
    Climb zeroL (c.labAt c.mA (Sum.inr (c.retq V.hR k))) := by
  have C := V.complete3
  have h := C.climb (Sum.inr (c.retq V.hR k)) [] c.mA (c.mE ++ c.mB ++ c.mF ++ c.mY)
    (by simp only [tot, aB, List.nil_append, List.append_assoc])
  rw [List.nil_append, emb3_s] at h
  have e : runLab c.p c.lab0 [] (c.v + (c.retq V.hR k).val) = 0 :=
    V.lab0_ge (c.v + (c.retq V.hR k).val) (Nat.le_add_right _ _)
  rw [e, Lb_zero] at h
  exact h

theorem Valid.gdA (V : c.Valid) : gatesDistinct (c.unemb3 V.hv V.hR) c.mA :=
  gatesDistinct_of _ _ (fun t s cf hm heq => by
    obtain ⟨h1, h2, _, h4⟩ := V.addsA t s cf hm
    have a := c.emb3_unemb3 V.hv V.hR t h1
    have b := c.emb3_unemb3 V.hv V.hR s (by unfold n; omega)
    rw [heq] at a
    exact h4 (b.symm.trans a))

theorem Valid.gdB (V : c.Valid) : gatesDistinct (c.unemb3 V.hv V.hR) c.mB :=
  gatesDistinct_of _ _ (fun t s cf hm heq => by
    obtain ⟨h1, h2, _, h4⟩ := V.addsB t s cf hm
    have a := c.emb3_unemb3 V.hv V.hR t h1
    have b := c.emb3_unemb3 V.hv V.hR s (by unfold n; omega)
    rw [heq] at a
    exact h4 (b.symm.trans a))

/-- **A checked carrier certificate, as the hypotheses of the carrier invocation theorem.** -/
noncomputable def Valid.phased (V : c.Valid) (hs : c.scalarCheck = true) :
    Phased (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.ret.length) where
  tv := c.tv
  kx := V.kx
  ky := V.ky
  cen := fun k => c.labAt c.mA (Sum.inr (c.retq V.hR k))
  kc := V.kc
  Cc := c.Ccm V.hR
  Jr := c.Jrm
  labA := c.labAt c.mA
  labB := c.labAt c.aB
  labF := c.labAt (c.aB ++ c.mF)
  hAy := fun t =>
    congrArg Lbl.P ((congrArg (Lb c.p) (V.cut_y t.val t.isLt)).trans (Lb_zero c.p))
  hAc := fun k q h => by
    have hq : q = c.retq V.hR k := by
      by_contra hne
      exact h (if_neg hne)
    rw [hq]
  hFx := fun t => congrArg Lbl.P (V.xsF t.val (by have := t.isLt; omega))
  hFy := fun t => congrArg Lbl.P (V.yF t)
  hFs := fun q => congrArg Lbl.P (V.xsF (c.v + q.val) (by have := q.isLt; omega))
  MA := c.MA V.hv V.hR
  MAi := matPinv (c.unemb3 V.hv V.hR) c.mA
  MB := c.MB V.hv V.hR
  MBi := matPinv (c.unemb3 V.hv V.hR) c.mB
  hAi := mul_eq_one_comm.mp (matP_inv _ _ V.gdA)
  hBi := mul_eq_one_comm.mp (matP_inv _ _ V.gdB)
  hx := V.hx
  hy := V.hy
  hid := V.hid hs
  rA := opsRanks 0 c.n c.A.flatten
  rB := opsRanks 0 c.n c.B.flatten
  rF := finsRanks 0 c.n c.fins.flatten
  pA := fun Xm => by
    have h := V.route_ops Xm c.A.flatten (List.all_eq_true.mp V.hA) []
      (c.mE ++ c.mB ++ c.mF ++ c.mY)
      (by simp only [tot, aB, mA, List.nil_append, List.append_assoc])
    have es : (fun q : c.Rl => Xm.Φ (c.labAt [] q).P) = fun r => Xm.Φ (lab3 c.tv r).P := by
      funext q
      rcases q with (t | S) | q
      · show Xm.Φ (Lb c.p (c.lab0 t.val)).P = Xm.Φ (lineL (c.tv t)).P
        rw [V.line t]
      · show Xm.Φ (Lb c.p (c.lab0 (c.v + c.R + S.val))).P = Xm.Φ (zeroL).P
        rw [V.lab0_ge (c.v + c.R + S.val) (by omega), Lb_zero]
      · show Xm.Φ (Lb c.p (c.lab0 (c.v + q.val))).P = Xm.Φ (zeroL).P
        rw [V.lab0_ge (c.v + q.val) (Nat.le_add_right _ _), Lb_zero]
    rw [es, List.nil_append] at h
    exact h
  pB := fun Xm => by
    have h := V.route_ops Xm c.B.flatten (List.all_eq_true.mp V.hB) (c.mA ++ c.mE)
      (c.mF ++ c.mY) (by simp only [tot, aB, mB, List.append_assoc])
    have es : (fun q : c.Rl => Xm.Φ (c.labAt (c.mA ++ c.mE) q).P)
        = fun q => Xm.Φ (c.labAt c.mA q).P := by
      funext q
      show Xm.Φ (Lb c.p (runLab c.p c.lab0 (c.mA ++ c.mE) (c.emb3 q))).P
        = Xm.Φ (Lb c.p (runLab c.p c.lab0 c.mA (c.emb3 q))).P
      rw [V.cut.2]
    rw [es] at h
    exact h
  pF := fun Xm => V.route_fin Xm

/-- the copies cost the dimensions of the stored labels of the retained totals -/
theorem Valid.cen_cost (V : c.Valid) (φ : ℕ → ℝ) :
    ∑ k : Fin c.ret.length, bcost φ (c.labAt c.mA (Sum.inr (c.retq V.hR k))).d
      = rcost φ c.cenRanks := by
  have hterm : ∀ k : Fin c.ret.length, (c.labAt c.mA (Sum.inr (c.retq V.hR k))).d
      = cntOf c.p (dec (c.retLab.getD k.val 0)) := by
    intro k
    show cntOf c.p (runLab c.p c.lab0 c.mA (c.emb3 (Sum.inr (c.retq V.hR k)))) = _
    rw [V.emb_retq k, V.cut_ret k.val k.isLt]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hterm k])]
  have e : rcost φ c.cenRanks = (c.retLab.map (fun L => bcost φ (cntOf c.p (dec L)))).sum := by
    unfold cenRanks rcost
    rw [List.map_map]
    rfl
  rw [e, list_sum_range (fun L => bcost φ (cntOf c.p (dec L))) c.retLab, V.hrl]
  exact Fin.sum_univ_eq_sum_range (fun k => bcost φ (cntOf c.p (dec (c.retLab.getD k 0))))
    c.ret.length

/-- **the price of one invocation**: the blocks of all roles (x, y, slots) and of the copies -/
theorem Valid.phased_cost (V : c.Valid) (hs : c.scalarCheck = true) (φ : ℕ → ℝ) :
    (V.phased hs).cost φ = rcost φ c.invRanks := by
  show rcost φ (opsRanks 0 c.n c.A.flatten)
      + (∑ k : Fin c.ret.length, bcost φ (c.labAt c.mA (Sum.inr (c.retq V.hR k))).d)
      + rcost φ (opsRanks 0 c.n c.B.flatten) + rcost φ (finsRanks 0 c.n c.fins.flatten) = _
  rw [V.cen_cost φ]
  simp only [invRanks, ranksOf, rcost_append]
  ring

end CCert

/-! ## the kernel count of the blocks -/

theorem CCert.sumW_eq (c : CCert) (wt : Nat → Nat) : c.sumW wt = wsum wt c.invRanks := by
  show cenW wt c.p c.retLab (finChunksW wt 0 (0 + c.n) c.fins
    (chunksW wt 0 (0 + c.n) c.B (chunksW wt 0 (0 + c.n) c.A 0))) = _
  rw [cenW_eq, finChunksW_eq, chunksW_eq, chunksW_eq]
  simp only [CCert.invRanks, CCert.ranksOf, CCert.cenRanks, wsum_append, Nat.zero_add,
    Nat.add_assoc]

/-- **the price of the blocks of one invocation from the kernel-evaluated counts** -/
theorem CCert.rcost_sumW (c : CCert) (φ : ℕ → ℝ) (B : ℕ) (hB : c.sumW (wGt B) = 0) :
    rcost φ c.invRanks = ∑ r ∈ range (B+1), (c.sumW (wEq r) : ℝ) * bcost φ r := by
  rw [c.sumW_eq] at hB
  rw [rcost_count φ c.invRanks B (wsum_wGt B _ hB)]
  refine sum_congr rfl (fun r _ => ?_)
  rw [c.sumW_eq, wsum_wEq]

end SSC

#print axioms SSC.CCert.Valid.of_checks
#print axioms SSC.CCert.Valid.phased
#print axioms SSC.CCert.Valid.phased_cost
#print axioms SSC.CCert.rcost_sumW

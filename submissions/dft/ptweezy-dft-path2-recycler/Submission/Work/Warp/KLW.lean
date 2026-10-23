import Submission.Work.Warp.Word
import Submission.Work.Warp.Win
import Submission.Work.KLowW.Route

/-!
# (key: p-warpsem) p-warpchk's warp hypothesis `KLW.WarpSem` DISCHARGED

p-warpchk's checker (`Work/KLowW/{LabSound,Route}.lean`, namespace `KLW`) proves for every legal warp event `.w r a f0 f1` the
GF(2) frame transport `KLW.WTr h o a c0 c1` (`o = wt[|a| - 1]`, codes `c0 = tab f0`, `c1 = tab f1`), and asks for
`KLW.WarpSem h wt X`: a logical operator `K a` per signed op id, `K a * K (-a) = 1`, and for every legal event a FREE
move `GReach (X.Φ (lab c0)) (X.Φ (lab c1) * K a) 0`.  Here, for every stage-B frame map `X` that transports warps
(`WLift X`, `Work/Warp/Sem.lean`):

* `wPerm h o`        the additive bijection `x ↦ colMap h o.G x` of a table entry (inverse `colMap h o.Gi`);
* `wTab h wt k`      the operator table (`k ≥ 1` ↦ entry `k - 1`);
* `wK L wt a`        `K a = warpMat (liftW (G_a))` for `a > 0`, `warpMat (liftW (G_|a|⁻¹))` for `a < 0`, `K 0 = 1`
                     (`= sgnMat (liftW ∘ wTab) a`, the free-group interpretation of `Work/Warp/Word.lean`);
* `wK_hinv`, `wK_htr`, **`warpSem L wt : KLW.WarpSem h wt X`**;
* instances for the frame maps of the integration: `warpSem_refl`, `warpSem_ofConj` (`BXMap.ofConj d q`) and
  `warpSem_gwinB` (every window `gwinB hB hH d q` of the bridged geometry).
The same instance serves the forward and the backward (inverse-transpose) programs: both use the same frames
`X.Φ`, and the hub's free-algebra replay makes the scalar result independent of the interpretation of the symbols.
It can NOT hold for an arbitrary `BXMap` (the lift of subspaces need not be equivariant); `WLift` is the condition.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace OAI
namespace PowerSaving
namespace WS
open Binary Matrix Finset GF GX

section
variable {h : ℕ}

/-- `colMap` is additive. -/
theorem colMap_add (cols : List ℕ) (x y : Space (Fin h)) :
    KLW.colMap h cols (x + y) = KLW.colMap h cols x + KLW.colMap h cols y := by
  simp only [KLW.colMap, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- the additive bijection of a warp operator (the identity if the entry is not invertible). -/
noncomputable def wPerm (h : ℕ) (o : KLW.WOp) : APerm (Fin h) := by
  classical
  exact if hh : (∀ x, KLW.colMap h o.G (KLW.colMap h o.Gi x) = x) ∧
      (∀ x, KLW.colMap h o.Gi (KLW.colMap h o.G x) = x) then
    { π := { toFun := KLW.colMap h o.G, invFun := KLW.colMap h o.Gi, left_inv := hh.2,
             right_inv := hh.1 },
      add := colMap_add o.G }
  else apId _

lemma wPerm_apply {o : KLW.WOp} (h1 : ∀ x, KLW.colMap h o.G (KLW.colMap h o.Gi x) = x)
    (h2 : ∀ x, KLW.colMap h o.Gi (KLW.colMap h o.G x) = x) (x : Space (Fin h)) :
    (wPerm h o).π x = KLW.colMap h o.G x := by
  classical
  unfold wPerm
  rw [dif_pos ⟨h1, h2⟩]
  rfl

lemma wPerm_inv_apply {o : KLW.WOp} (h1 : ∀ x, KLW.colMap h o.G (KLW.colMap h o.Gi x) = x)
    (h2 : ∀ x, KLW.colMap h o.Gi (KLW.colMap h o.G x) = x) (x : Space (Fin h)) :
    (apInv (wPerm h o)).π x = KLW.colMap h o.Gi x := by
  classical
  unfold wPerm
  rw [dif_pos ⟨h1, h2⟩]
  rfl

/-- the operator table: op id `k ≥ 1` is the entry `k - 1` (default: the empty entry, as `KLW.opOf`). -/
noncomputable def wTab (h : ℕ) (wt : List KLW.WOp) (k : ℕ) : APerm (Fin h) :=
  wPerm h (wt.getD (k - 1) ⟨[], []⟩)

lemma wTab_of_getD {wt : List KLW.WOp} {k : ℕ} {o : KLW.WOp} (hk : wt.getD (k - 1) ⟨[], []⟩ = o) :
    wTab h wt k = wPerm h o := by
  unfold wTab; rw [hk]

lemma wTab_of_get {wt : List KLW.WOp} {k : ℕ} {o : KLW.WOp} (hk : wt[k - 1]? = some o) :
    wTab h wt k = wPerm h o := by
  apply wTab_of_getD
  rw [List.getD_eq_getElem?_getD, hk]
  rfl

/-- p-warpchk's `|a|` is `Int.natAbs`. -/
lemma opAbs_eq (a : ℤ) : KLW.opAbs a = a.natAbs := by
  cases a <;> rfl

/-- p-warpchk's table entry of a signed op id. -/
lemma wTab_opOf (wt : List KLW.WOp) (a : ℤ) : wTab h wt a.natAbs = wPerm h (KLW.opOf wt a) := by
  apply wTab_of_getD
  unfold KLW.opOf
  rw [opAbs_eq]

variable {α : Type} [Fintype α] [DecidableEq α] {X : BXMap (Fin h) α}

/-- **the logical operator of a signed op id.** -/
noncomputable def wK (L : WLift X) (wt : List KLW.WOp) (a : ℤ) : CMat α :=
  if a = 0 then 1 else sgnMat (fun k => L.liftW (wTab h wt k)) a

theorem wK_hinv (L : WLift X) (wt : List KLW.WOp) (a : ℤ) : wK L wt a * wK L wt (-a) = 1 := by
  by_cases ha : a = 0
  · subst ha
    simp [wK]
  · have ha' : -a ≠ 0 := neg_ne_zero.mpr ha
    unfold wK
    rw [if_neg ha, if_neg ha']
    exact sgnMat_mul_neg _ ha

theorem free_wK (L : WLift X) (wt : List KLW.WOp) (a : ℤ) : Free (wK L wt a) := by
  unfold wK
  split_ifs
  · exact Free.one
  · exact free_sgnMat _ _

/-- the frame relation of a legal event, in the form of the transport lemma. -/
theorem wtr_mem (wt : List KLW.WOp) (a : ℤ) (o : KLW.WOp) (c0 c1 : ℕ) (ha : a ≠ 0)
    (hW : wTab h wt a.natAbs = wPerm h o) (T : KLW.WTr h o a c0 c1) :
    ∀ x, (GLab.lab h c1).Mem x ↔ (GLab.lab h c0).Mem ((apInv (sgnPerm (wTab h wt) a)).π x) := by
  rcases lt_or_gt_of_ne ha with hn | hp
  · -- a < 0: f0 = G f1, the event applies G⁻¹
    have e : (-a).toNat = a.natAbs := by omega
    rw [sgnPerm_neg _ hn, apInv_apInv, e, hW]
    intro x
    rw [wPerm_apply T.inv1 T.inv2]
    constructor
    · intro hx
      exact (T.neg hn _).mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (T.neg hn _).mp hx
      have : x = y := by rw [← T.inv2 x, hxy, T.inv2 y]
      rw [this]; exact hy
  · -- a > 0: f1 = G f0
    have e : a.toNat = a.natAbs := by omega
    rw [sgnPerm_pos _ hp, e, hW]
    intro x
    rw [wPerm_inv_apply T.inv1 T.inv2]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (T.pos hp x).mp hx
      rw [hxy, T.inv2 y]; exact hy
    · intro hx
      exact (T.pos hp x).mpr ⟨_, hx, (T.inv1 x).symm⟩

/-- the matrix of a legal event through the frame map. -/
theorem wK_eq (L : WLift X) (wt : List KLW.WOp) {a : ℤ} (ha : a ≠ 0) :
    wK L wt a = warpMat (L.liftW (sgnPerm (wTab h wt) a)) := by
  unfold wK
  rw [if_neg ha]
  unfold sgnMat
  rw [L.sgnPerm_lift (wTab h wt) a]

/-- **the frame transport of every legal warp event is a FREE move** (table entry given as `wTab`). -/
theorem wK_htrW (L : WLift X) (wt : List KLW.WOp) (a : ℤ) (o : KLW.WOp) (c0 c1 : ℕ) (ha : a ≠ 0)
    (hW : wTab h wt a.natAbs = wPerm h o) (T : KLW.WTr h o a c0 c1) :
    GReach (X.Φ (GLab.lab h c0)) (X.Φ (GLab.lab h c1) * wK L wt a) (fun _ => 0) := by
  obtain ⟨P, hP, e⟩ := L.transport (sgnPerm (wTab h wt) a) (GLab.lab h c0) (GLab.lab h c1)
    (wtr_mem wt a o c0 c1 ha hW T)
  rw [wK_eq L wt ha]
  intro ρ _ _ l
  have g := gstep_free hP l (X.Φ (GLab.lab h c0))
  rw [e] at g
  exact g

/-- the same with the table entry as `wt[|a| - 1]? = some o` (the form of `KLW.WarpSem.htr`). -/
theorem wK_htr (L : WLift X) (wt : List KLW.WOp) (a : ℤ) (o : KLW.WOp) (c0 c1 : ℕ) (ha : a ≠ 0)
    (hget : wt[a.natAbs - 1]? = some o) (hg0 : GLab.Good h c0) (hg1 : GLab.Good h c1)
    (T : KLW.WTr h o a c0 c1) :
    GReach (X.Φ (GLab.lab h c0)) (X.Φ (GLab.lab h c1) * wK L wt a) (fun _ => 0) :=
  wK_htrW L wt a o c0 c1 ha (wTab_of_get hget) T

/-- the same with the table entry as `KLW.opOf wt a` (the kernel's lookup). -/
theorem wK_htr_opOf (L : WLift X) (wt : List KLW.WOp) (a : ℤ) (c0 c1 : ℕ) (ha : a ≠ 0)
    (T : KLW.WTr h (KLW.opOf wt a) a c0 c1) :
    GReach (X.Φ (GLab.lab h c0)) (X.Φ (GLab.lab h c1) * wK L wt a) (fun _ => 0) :=
  wK_htrW L wt a _ c0 c1 ha (wTab_opOf wt a) T

/-- **p-warpchk's hypothesis, discharged for every frame map that transports warps.** -/
noncomputable def warpSem (L : WLift X) (wt : List KLW.WOp) : KLW.WarpSem h wt X where
  K := wK L wt
  hinv := wK_hinv L wt
  htr := fun a o c0 c1 ha hget hg0 hg1 T => wK_htr L wt a o c0 c1 ha hget hg0 hg1 T

end

/-- the identity frame map. -/
noncomputable def warpSem_refl (h : ℕ) (wt : List KLW.WOp) : KLW.WarpSem h wt (BXMap.refl (Fin h)) :=
  warpSem (WLift.refl (Fin h)) wt

/-- the bridged geometry's frame map `U ↦ d (U ⊕ span q)`. -/
noncomputable def warpSem_ofConj {h : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    (d : Matrix (Fin h ⊕ β) (Fin h ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1) (q : Finset β)
    (wt : List KLW.WOp) : KLW.WarpSem h wt (BXMap.ofConj d hd hd' q) :=
  warpSem (WLift.ofConj d hd hd' q) wt

/-- every window of the bridged geometry. -/
noncomputable def warpSem_gwinB {h : ℕ} {B : Type} [Fintype B] [DecidableEq B]
    (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card (Fin h)) (d : RF.Orth (BG.LB B (Fin h)))
    (q : Finset (B × Fin h)) (wt : List KLW.WOp) : KLW.WarpSem h wt (gwinB hB hH d q).X :=
  warpSem (WLift.gwinB hB hH d q) wt

/-- the logical operator of the instance is our free warp matrix. -/
theorem warpSem_K {h : ℕ} {α : Type} [Fintype α] [DecidableEq α] {X : BXMap (Fin h) α} (L : WLift X)
    (wt : List KLW.WOp) (a : ℤ) : (warpSem L wt).K a = wK L wt a := rfl

theorem warpSem_K_free {h : ℕ} {α : Type} [Fintype α] [DecidableEq α] {X : BXMap (Fin h) α}
    (L : WLift X) (wt : List KLW.WOp) (a : ℤ) : Free ((warpSem L wt).K a) := free_wK L wt a

end WS
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.WS.colMap_add
#print axioms OAI.PowerSaving.WS.wK_hinv
#print axioms OAI.PowerSaving.WS.wtr_mem
#print axioms OAI.PowerSaving.WS.wK_htr
#print axioms OAI.PowerSaving.WS.wK_htr_opOf
#print axioms OAI.PowerSaving.WS.warpSem
#print axioms OAI.PowerSaving.WS.warpSem_refl
#print axioms OAI.PowerSaving.WS.warpSem_ofConj
#print axioms OAI.PowerSaving.WS.warpSem_gwinB
#print axioms OAI.PowerSaving.WS.warpSem_K_free

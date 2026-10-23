import Submission.Work.GFrame.Labels.ConjB
import Submission.Work.GFrame.Labels.StageBSem
import Submission.Work.GFrame.Clifford.Climb
import Submission.Work.GFrame.Clifford.Base
import Submission.Work.GFrame.Top.Api
import Submission.Work.GCert.Chain.Win

/-!
# (key: p-warpsem) What a warp means: the free monomial `warpMat W` and FRAME TRANSPORT

Round wht45/lever, 19 Oct 2026.  A warp of the hub (PR2226's anticipatory dirty borrowing, Cinna Davis; carried by
#3945) is the rank-zero "logical reference change" `K_G` of one register: an invertible linear map `G` of the
label space carries the register's frame `f0` to `f1 = G(f0)`, and the register's logical value `z` becomes `K_G z`.
The hub's `K_G` is `perm(G)` followed by a diagonal quadratic `ℤ/4` phase (no translation).  The hub replays every
program in the FREE algebra of the warp symbols, so any interpretation `op ↦ K_op`, `-op ↦ K_op⁻¹` by invertible
matrices is sound; we interpret a warp by our own monomial

* `warpMat W = kg W⁻¹ = diag(lum) * permMat W⁻¹ * diag(lum)⁻¹`   (`warpMat_eq`, `warpMat_apply`, `warpMat_mulVec`):
  the value at address `y` moves to `W y`, times the quarter phase `lum (W y) / lum y = i^(|W y| - |y|)`
  (a `ℤ/4` quadratic form), i.e. `perm(W)` then a quadratic phase, like the hub's `K_G`;
* `free_warpMat`: it is FREE (a product of the existing free letters `perm` and `phase`; no new letter, no block);
* `warpMat_mul_inv`, `warpMat_inv_mul`: the inverse warp `W⁻¹` is the inverse matrix;
* `core_warp`: `core (W⁻¹ ≫ G) s = warpMat W * core G s * warpMat W⁻¹` (the representative of `W(U)`);
* **`warp_transport`** (the frame-transport lemma): if the subspace of `V` is `W` of the subspace of `U`, then
  `P * U.rep = V.rep * warpMat W` for a FREE `P`: the free physical operator `P` carries data at frame `U` to data
  at frame `V` whose logical value has been warped by `warpMat W`;
  `warp_transport_of_map` (same from `W(U) ⊆ V` and `dim V ≤ dim U`), `warp_fmv`, `warp_gstep`, `warp_reach`
  (engine forms, any right factor), `warp_data` (the action on one role's data, other roles untouched);
* `WLift X`: a stage-B frame map `X : BXMap H α` that transports warps of `H` to warps of `α`; `WLift.transport`,
  `WLift.reach`, `WLift.fmv`, `WLift.data`; instances `WLift.refl` and `WLift.ofConj` (the bridged geometry's
  `BXMap.ofConj d q`, so also the windows `gwinB`, see `Work/Warp/Win.lean`).
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace WS
open Binary Matrix Finset GF GX
noncomputable section

section Perm
variable {α : Type} [Fintype α] [DecidableEq α]

/-- two additive bijections with the same map are equal. -/
theorem aperm_ext {G G' : APerm α} (h : ∀ x, G.π x = G'.π x) : G = G' := by
  cases G with
  | mk π add =>
    cases G' with
    | mk π' add' =>
      have e : π = π' := Equiv.ext h
      subst e
      rfl

@[simp] lemma apInv_apInv (G : APerm α) : apInv (apInv G) = G :=
  aperm_ext (fun x => by simp [apInv])

lemma apComp_apply (G H : APerm α) (x : Space α) : (apComp G H).π x = H.π (G.π x) := rfl

lemma apInv_apComp_apply (G H : APerm α) (x : Space α) :
    (apInv (apComp G H)).π x = (apInv G).π ((apInv H).π x) := by
  simp [apInv, apComp]

/-- `kg` only depends on the map. -/
lemma kg_congr {A B : APerm α} (h : ∀ x, A.π x = B.π x) : kg A = kg B := by
  rw [aperm_ext h]

/-- **`kg` is multiplicative**: `kg (A ≫ B) = kg A * kg B`. -/
theorem kg_comp (A B : APerm α) : kg (apComp A B) = kg A * kg B := by
  ext x y
  rw [kg_mul_apply]
  have hA := lum_nonzero (A.π x)
  by_cases h : B.π (A.π x) = y
  · have h' : (apComp A B).π x = y := h
    show (if (apComp A B).π x = y then lum x / lum y else 0)
      = lum x / lum (A.π x) * (if B.π (A.π x) = y then lum (A.π x) / lum y else 0)
    rw [if_pos h', if_pos h, div_mul_div_comm, mul_comm (lum x) (lum (A.π x)),
      mul_div_mul_left _ _ hA]
  · have h' : ¬ (apComp A B).π x = y := h
    show (if (apComp A B).π x = y then lum x / lum y else 0)
      = lum x / lum (A.π x) * (if B.π (A.π x) = y then lum (A.π x) / lum y else 0)
    rw [if_neg h', if_neg h, mul_zero]

end Perm

section Warp
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **The matrix of a warp** by the additive bijection `W` (the hub's `K_W`, our phase convention). -/
def warpMat (W : APerm α) : CMat α := kg (apInv W)

/-- `perm(W)` composed with the phase part. -/
theorem warpMat_eq (W : APerm α) :
    warpMat W = diagonal lum * permMat (apInv W) * diagonal (fun y => (lum y)⁻¹) := kg_eq _

theorem warpMat_apply (W : APerm α) (x y : Space α) :
    warpMat W x y = if (apInv W).π x = y then lum x / lum y else 0 := rfl

/-- the action: the value at `y` goes to `W y` with the phase `lum (W y) / lum y`. -/
theorem warpMat_mulVec (W : APerm α) (v : Space α → ℂ) (x : Space α) :
    (warpMat W *ᵥ v) x = lum x / lum ((apInv W).π x) * v ((apInv W).π x) := by
  show ∑ j, warpMat W x j * v j = _
  rw [Finset.sum_eq_single ((apInv W).π x)]
  · rw [warpMat_apply, if_pos rfl]
  · intro b _ hb
    rw [warpMat_apply, if_neg (Ne.symm hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **A warp is free** (no block, no new letter). -/
theorem free_warpMat (W : APerm α) : Free (warpMat W) := free_kg _

theorem warpMat_mul_inv (W : APerm α) : warpMat W * warpMat (apInv W) = 1 := by
  unfold warpMat
  rw [apInv_apInv]
  exact kg_inv_mul W

theorem warpMat_inv_mul (W : APerm α) : warpMat (apInv W) * warpMat W = 1 := by
  unfold warpMat
  rw [apInv_apInv]
  exact kg_mul_inv W

/-- the inverse warp is free as well (it is again a warp). -/
theorem free_warpMat_inv (W : APerm α) : Free (warpMat (apInv W)) := free_warpMat _

theorem warpMat_apId : warpMat (apId α) = 1 := by
  have h : apInv (apId α) = apId α := aperm_ext (fun x => rfl)
  unfold warpMat
  rw [h]
  ext x y
  by_cases hxy : x = y
  · subst hxy; simp [kg, apId, lum_nonzero]
  · simp [kg, apId, Matrix.one_apply, hxy]

/-- warps compose: `warpMat (W ≫ W') = warpMat W' * warpMat W`. -/
theorem warpMat_comp (W W' : APerm α) : warpMat (apComp W W') = warpMat W' * warpMat W := by
  unfold warpMat
  rw [kg_congr (A := apInv (apComp W W')) (B := apComp (apInv W') (apInv W))
    (fun x => apInv_apComp_apply W W' x), kg_comp]

/-- the label `(W⁻¹ ≫ G, s)` names `W` of the subspace named by `(G, s)`. -/
lemma insub_warp (W G : APerm α) (s : Finset α) (x : Space α) :
    InSub (apComp (apInv W) G) s x ↔ InSub G s ((apInv W).π x) := Iff.rfl

/-- **The representative of the warped subspace is the conjugate.** -/
theorem core_warp (W G : APerm α) (s : Finset α) :
    core (apComp (apInv W) G) s = warpMat W * core G s * warpMat (apInv W) := by
  unfold core warpMat
  rw [kg_comp, kg_congr (A := apInv (apComp (apInv W) G)) (B := apComp (apInv G) (apInv (apInv W)))
    (fun x => apInv_apComp_apply (apInv W) G x), kg_comp]
  simp only [Matrix.mul_assoc]

/-- **FRAME TRANSPORT.**  If the subspace of `V` is `W` of the subspace of `U`, a FREE `P` carries a role at
frame `U` to frame `V`, the logical value warped by `warpMat W`:  `P * U.rep = V.rep * warpMat W`. -/
theorem warp_transport (W : APerm α) (U V : SLbl α)
    (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) :
    ∃ P : CMat α, Free P ∧ P * U.rep = V.rep * warpMat W := by
  obtain ⟨N, hN, e⟩ := rep_change (apComp (apInv W) U.G) V.G U.s V.s
    (fun x => (insub_warp W U.G U.s x).trans (h x).symm)
  refine ⟨N * warpMat W, Free.mul hN (free_warpMat W), ?_⟩
  show N * warpMat W * core U.G U.s = core V.G V.s * warpMat W
  rw [e, core_warp]
  simp only [Matrix.mul_assoc]
  rw [warpMat_inv_mul, Matrix.mul_one]

/-- the hypothesis of `warp_transport` from `W(U) ⊆ V` and `dim V ≤ dim U`. -/
theorem warp_mem_of_map (W : APerm α) (U V : SLbl α)
    (hmap : ∀ x, U.Mem x → V.Mem (W.π x)) (hdim : V.dim ≤ U.dim) :
    ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x) := by
  have hsub : ∀ x, InSub (apComp (apInv W) U.G) U.s x → InSub V.G V.s x := by
    intro x hx
    have g := hmap ((apInv W).π x) ((insub_warp W U.G U.s x).mp hx)
    rw [apply_apInv] at g
    exact g
  have hle := card_le_of_sub hsub
  have hc : U.s.card = V.s.card := le_antisymm hle hdim
  intro x
  exact ((insub_iff_of_card _ _ _ _ hsub hc x).symm.trans (insub_warp W U.G U.s x))

theorem warp_transport_of_map (W : APerm α) (U V : SLbl α)
    (hmap : ∀ x, U.Mem x → V.Mem (W.π x)) (hdim : V.dim ≤ U.dim) :
    ∃ P : CMat α, Free P ∧ P * U.rep = V.rep * warpMat W :=
  warp_transport W U V (warp_mem_of_map W U V hmap hdim)

/-- the inverse warp: if the subspace of `V` is `W⁻¹` of that of `U`, the logical value is warped by
`warpMat W⁻¹ = (warpMat W)⁻¹`. -/
theorem warp_transport_inv (W : APerm α) (U V : SLbl α)
    (h : ∀ x, V.Mem x ↔ U.Mem (W.π x)) :
    ∃ P : CMat α, Free P ∧ P * U.rep = V.rep * warpMat (apInv W) :=
  warp_transport (apInv W) U V (fun x => by rw [apInv_apInv]; exact h x)

/-- engine form: a one-role move of the generalised engine with no block (any right factor `D`). -/
theorem warp_fmv (W : APerm α) (U V : SLbl α) (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x))
    (D : CMat α) : FMv (gcalc α) (U.rep * D) (V.rep * warpMat W * D) [] := by
  obtain ⟨P, hP, e⟩ := warp_transport W U V h
  have g := FMv.free (K := gcalc α) (M := U.rep * D) hP
  rwa [← Matrix.mul_assoc, e] at g

theorem warp_gstep {ρ : Type} [Fintype ρ] [DecidableEq ρ] (l : ρ) (W : APerm α) (U V : SLbl α)
    (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) (D : CMat α) :
    GStep l (U.rep * D) (V.rep * warpMat W * D) (fun _ => 0) := by
  obtain ⟨P, hP, e⟩ := warp_transport W U V h
  have g := gstep_free hP l (U.rep * D)
  rwa [← Matrix.mul_assoc, e] at g

theorem warp_reach (W : APerm α) (U V : SLbl α) (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x))
    (D : CMat α) : GReach (U.rep * D) (V.rep * warpMat W * D) (fun _ => 0) :=
  fun ρ _ _ l => warp_gstep l W U V h D

/-- **the warp on one role's data**: a proper word of price `0` takes a role whose array is `U.rep` applied to
`y` to the array `V.rep` applied to `warpMat W` applied to `y`; every other role is untouched. -/
theorem warp_data {ρ : Type} [Fintype ρ] [DecidableEq ρ] (l : ρ) (W : APerm α) (U V : SLbl α)
    (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) :
    ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = 0) ∧
      ∀ (f : ℕ) (x : Data α ρ f),
        (∀ y : Sky α f → ℂ, x l = matAct f U.rep y →
          gwalk f w x l = matAct f V.rep (matAct f (warpMat W) y)) ∧
        (∀ j, j ≠ l → gwalk f w x j = x j) := by
  obtain ⟨w, P, hw, hc, hP, hwalk⟩ := warp_gstep l W U V h 1
  refine ⟨w, hw, hc, fun f x => ⟨fun y hy => ?_, fun j hj => ?_⟩⟩
  · rw [hwalk]
    show (if l = l then matAct f P (x l) else x l) = _
    rw [if_pos rfl, hy, matAct_mul, matAct_mul]
    rw [Matrix.mul_one, Matrix.mul_one] at hP
    rw [hP]
  · rw [hwalk]
    show (if j = l then matAct f P (x j) else x j) = x j
    rw [if_neg hj]

end Warp

section Lift
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

/-- **A stage-B frame map that transports warps**: a warp `W` of the label space `H` lifts to a warp
`liftW W` of the address space, carrying lifted subspaces like `W` carries subspaces. -/
structure WLift (X : BXMap H α) where
  liftW : APerm H → APerm α
  wsub : ∀ (W : APerm H) (U V : SLbl H), (∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) →
    ∀ y, (X.lab V).Mem y ↔ (X.lab U).Mem ((apInv (liftW W)).π y)
  winv : ∀ (W : APerm H) (y : Space α), (liftW (apInv W)).π y = (apInv (liftW W)).π y

namespace WLift
variable {X : BXMap H α} (L : WLift X)

theorem liftW_inv (W : APerm H) : L.liftW (apInv W) = apInv (L.liftW W) := aperm_ext (L.winv W)

/-- the lifted inverse warp is the inverse matrix. -/
theorem warpMat_liftW_inv (W : APerm H) :
    warpMat (L.liftW (apInv W)) * warpMat (L.liftW W) = 1 := by
  rw [L.liftW_inv]; exact warpMat_inv_mul _

theorem warpMat_liftW_inv' (W : APerm H) :
    warpMat (L.liftW W) * warpMat (L.liftW (apInv W)) = 1 := by
  rw [L.liftW_inv]; exact warpMat_mul_inv _

/-- **FRAME TRANSPORT through a frame map.** -/
theorem transport (W : APerm H) (U V : SLbl H) (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) :
    ∃ P : CMat α, Free P ∧ P * X.Φ U = X.Φ V * warpMat (L.liftW W) :=
  warp_transport (L.liftW W) (X.lab U) (X.lab V) (L.wsub W U V h)

theorem transport_of_map (W : APerm H) (U V : SLbl H) (hmap : ∀ x, U.Mem x → V.Mem (W.π x))
    (hdim : V.dim ≤ U.dim) :
    ∃ P : CMat α, Free P ∧ P * X.Φ U = X.Φ V * warpMat (L.liftW W) :=
  L.transport W U V (warp_mem_of_map W U V hmap hdim)

theorem fmv (W : APerm H) (U V : SLbl H) (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) (D : CMat α) :
    FMv (gcalc α) (X.Φ U * D) (X.Φ V * warpMat (L.liftW W) * D) [] :=
  warp_fmv (L.liftW W) (X.lab U) (X.lab V) (L.wsub W U V h) D

theorem gstep {ρ : Type} [Fintype ρ] [DecidableEq ρ] (l : ρ) (W : APerm H) (U V : SLbl H)
    (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) (D : CMat α) :
    GStep l (X.Φ U * D) (X.Φ V * warpMat (L.liftW W) * D) (fun _ => 0) :=
  warp_gstep l (L.liftW W) (X.lab U) (X.lab V) (L.wsub W U V h) D

theorem reach (W : APerm H) (U V : SLbl H) (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) (D : CMat α) :
    GReach (X.Φ U * D) (X.Φ V * warpMat (L.liftW W) * D) (fun _ => 0) :=
  warp_reach (L.liftW W) (X.lab U) (X.lab V) (L.wsub W U V h) D

theorem data {ρ : Type} [Fintype ρ] [DecidableEq ρ] (l : ρ) (W : APerm H) (U V : SLbl H)
    (h : ∀ x, V.Mem x ↔ U.Mem ((apInv W).π x)) :
    ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = 0) ∧
      ∀ (f : ℕ) (x : Data α ρ f),
        (∀ y : Sky α f → ℂ, x l = matAct f (X.Φ U) y →
          gwalk f w x l = matAct f (X.Φ V) (matAct f (warpMat (L.liftW W)) y)) ∧
        (∀ j, j ≠ l → gwalk f w x j = x j) :=
  warp_data l (L.liftW W) (X.lab U) (X.lab V) (L.wsub W U V h)

end WLift

/-- the identity frame map transports warps (`liftW = id`). -/
def WLift.refl (α : Type) [Fintype α] [DecidableEq α] : WLift (BXMap.refl α) where
  liftW := id
  wsub := fun W U V h => h
  winv := fun W y => rfl

end Lift

section Conj
variable {H β : Type} [Fintype H] [DecidableEq H] [Fintype β] [DecidableEq β]

/-- the lift of a warp `W` of `H` to `H ⊕ β` along `d`: `y ↦ d ((W ⊕ id) (dᵀ y))`. -/
def conjW (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1) (W : APerm H) :
    APerm (H ⊕ β) :=
  apComp (mvPerm d hd hd') (apComp (inlPerm W) (apInv (mvPerm d hd hd')))

lemma conjW_inv_apply (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1)
    (W : APerm H) (y : Space (H ⊕ β)) :
    (apInv (conjW d hd hd' W)).π y = d *ᵥ ((inlPerm (apInv W) : APerm (H ⊕ β)).π (dᵀ *ᵥ y)) := rfl

lemma conjW_apply (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1)
    (W : APerm H) (y : Space (H ⊕ β)) :
    (conjW d hd hd' W).π y = d *ᵥ ((inlPerm W : APerm (H ⊕ β)).π (dᵀ *ᵥ y)) := rfl

/-- **the bridged geometry's frame map transports warps.** -/
def WLift.ofConj (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1)
    (q : Finset β) : WLift (BXMap.ofConj d hd hd' q) where
  liftW := conjW d hd hd'
  wsub := fun W U V h y => by
    show InSub (conjPerm d hd hd' V.G) (V.s.disjSum q) y ↔
      InSub (conjPerm d hd hd' U.G) (U.s.disjSum q) ((apInv (conjW d hd hd' W)).π y)
    rw [insub_conj, insub_conj, conjW_inv_apply, Matrix.mulVec_mulVec, hd, Matrix.one_mulVec]
    exact and_congr (h (fun i => (dᵀ *ᵥ y) (Sum.inl i))) Iff.rfl
  winv := fun W y => rfl

end Conj

end
end WS
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.WS.kg_comp
#print axioms OAI.PowerSaving.WS.free_warpMat
#print axioms OAI.PowerSaving.WS.warpMat_mul_inv
#print axioms OAI.PowerSaving.WS.warpMat_inv_mul
#print axioms OAI.PowerSaving.WS.warpMat_comp
#print axioms OAI.PowerSaving.WS.warpMat_mulVec
#print axioms OAI.PowerSaving.WS.core_warp
#print axioms OAI.PowerSaving.WS.warp_transport
#print axioms OAI.PowerSaving.WS.warp_transport_of_map
#print axioms OAI.PowerSaving.WS.warp_transport_inv
#print axioms OAI.PowerSaving.WS.warp_fmv
#print axioms OAI.PowerSaving.WS.warp_gstep
#print axioms OAI.PowerSaving.WS.warp_reach
#print axioms OAI.PowerSaving.WS.warp_data
#print axioms OAI.PowerSaving.WS.WLift.transport
#print axioms OAI.PowerSaving.WS.WLift.data
#print axioms OAI.PowerSaving.WS.WLift.ofConj

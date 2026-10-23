import Submission.Work.XHostT.TProvW
import Submission.Work.P16A8.Roles
import Submission.Work.P4L.Basis
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P16A8 (p16a8), one full native call as an operator route

The provider's stage (`XHostTW.gistageW_fwd/bwd`) placed on the network by `emb k` (ports on the acting pair,
slot `(g, q)` on the fresh helper `(g, k, q)`, copies on copies), lifted (`GRoute.lift`), read as an operator
(`P4L.ORoute.of_groute`).  The thin-query scratch is not covered by a call: the call leaves it unchanged.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace OAI
namespace PowerSaving
namespace P16A8
open Binary Matrix Finset RAM SS CB RF BR GF GX XHostTW

noncomputable section

section Call
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}

/-- the scalar map of a forward call `k` on the network. -/
def gFk (k : Fin 18) (x : PRole Γ T Sl C → ℂ) : PRole Γ T Sl C → ℂ
  | .inl (.inl (g, (i, t))) =>
      if i = yOf k then x (mainR g (yOf k) t) + x (mainR g (xOf k) t) else x (mainR g i t)
  | .inl (.inr h) => x (.inl (.inr h))
  | .inr (.inl _) => 0
  | .inr (.inr z) => x (.inr (.inr z))

/-- the scalar map of a backward call `k` on the network. -/
def gBk (k : Fin 18) (x : PRole Γ T Sl C → ℂ) : PRole Γ T Sl C → ℂ
  | .inl (.inl (g, (i, t))) =>
      if i = xOf k then x (mainR g (xOf k) t) - x (mainR g (yOf k) t) else x (mainR g i t)
  | .inl (.inr h) => x (.inl (.inr h))
  | .inr (.inl _) => 0
  | .inr (.inr z) => x (.inr (.inr z))

/-- start matrices of a call on the network. -/
def stS (k : Fin 18) (A : Γ → T → OBase α) (sX sY : Finset α) : PRole Γ T Sl C → CMat α
  | .inl (.inl (g, (i, t))) => if i = xOf k then frame (A g t) sX else if i = yOf k then frame (A g t) sY else 1
  | _ => 1

/-- their inverses. -/
def stS' (k : Fin 18) (A : Γ → T → OBase α) (sX sY : Finset α) : PRole Γ T Sl C → CMat α
  | .inl (.inl (g, (i, t))) =>
      if i = xOf k then unframe (A g t) sX else if i = yOf k then unframe (A g t) sY else 1
  | _ => 1

/-- end matrices of a call on the network (helpers: their residual matrix). -/
def stT (k : Fin 18) (A : Γ → T → OBase α) (sX' sY' : Finset α) (Wn : Γ → Sl → CMat α) :
    PRole Γ T Sl C → CMat α
  | .inl (.inl (g, (i, t))) =>
      if i = xOf k then frame (A g t) sX' else if i = yOf k then frame (A g t) sY' else 1
  | .inl (.inr (g, (k', q))) => if k' = k then Wn g q * 1 else 1
  | .inr _ => 1

lemma stS_inv (k : Fin 18) (A : Γ → T → OBase α) (sX sY : Finset α) (r : PRole Γ T Sl C) :
    stS k A sX sY r * stS' k A sX sY r = 1 := by
  rcases r with ((⟨g, i, t⟩ | ⟨g, k', q⟩) | (⟨g, c⟩ | ⟨g, j, t⟩))
  · simp only [stS, stS']
    split_ifs <;> simp [unframe_right]
  · simp [stS, stS']
  · simp [stS, stS']
  · simp [stS, stS']

variable (I : GInvW H T Sl C Ok)

/-- **a forward full call `k` as an operator route** (frames in one basis per port). -/
theorem call_fwd (k : Fin 18) (εX : T → Γ ≃ Γ) (M : Γ → GWin H α) (hok : ∀ d, Ok (M d))
    (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α)
    (hXin : ∀ g t, (M (εX t g)).Xm.Φ (tt (I.tv t)) = frame (A g t) sX)
    (hXout : ∀ g t, (M (εX t g)).Xm.Φ 1 = frame (A g t) sX')
    (hYin : ∀ g t, (M (εX t g)).Xm.Φ 0 = frame (A g t) sY)
    (hYout : ∀ g t, (M (εX t g)).Xm.Φ (1 + tt (I.tv t)) = frame (A g t) sY') :
    P4L.ORoute (fun f y => multiAct f (stT (C := C) k A sX' sY' (fun d q => entW (M d).X (I.ent q)))
        (point f (gFk k) (multiAct f (stS' (Sl := Sl) (C := C) k A sX sY) y)))
      (fun φ => (Fintype.card Γ : ℝ) * I.cost φ) := by
  have h := gistageW_fwd I εX M hok (fun d q => entN (M d).X (I.ent q)) (fun d q => entW (M d).X (I.ent q))
    (fun d q => entN_spec _ _) (fun d q => entW_spec _ _) (fun _ _ => 1) (cOne Γ C α) (cOne Γ C α)
  have eS : bIn I.tv εX (fun d => (M d).Xm) (fun _ _ => 1) (cOne Γ C α)
      = stS (Sl := Sl) (C := C) k A sX sY ∘ emb k := by
    funext r
    rcases r with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩)
    · show (M (εX t g)).Xm.Φ (tt (I.tv t)) = _
      simp [stS, emb, embF, mainR, hXin g t]
    · show (M (εX t g)).Xm.Φ 0 = _
      simp [stS, emb, embF, mainR, hYin g t, Ne.symm (xOf_ne_yOf k)]
    · rfl
    · rfl
  have eT : bOut I.tv εX (fun d => (M d).Xm) (fun g q => entW (M g).X (I.ent q) * (fun _ _ => (1 : CMat α)) g q)
        (cOne Γ C α)
      = stT (Sl := Sl) (C := C) k A sX' sY' (fun d q => entW (M d).X (I.ent q)) ∘ emb k := by
    funext r
    rcases r with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩)
    · show (M (εX t g)).Xm.Φ 1 = _
      simp [stT, emb, embF, mainR, hXout g t]
    · show (M (εX t g)).Xm.Φ (1 + tt (I.tv t)) = _
      simp [stT, emb, embF, mainR, hYout g t, Ne.symm (xOf_ne_yOf k)]
    · simp [stT, emb, embF, freshR, bOut, mkS]
    · rfl
  have h' : GRoute (stS (Sl := Sl) (C := C) k A sX sY ∘ emb k)
      (stT (Sl := Sl) (C := C) k A sX' sY' (fun d q => entW (M d).X (I.ent q)) ∘ emb k) GF
      (fun φ => (Fintype.card Γ : ℝ) * I.cost φ) := by
    rw [← eS, ← eT]
    exact h
  have hL : GRoute (stS (Sl := Sl) (C := C) k A sX sY)
      (stT (Sl := Sl) (C := C) k A sX' sY' (fun d q => entW (M d).X (I.ent q))) (gFk k)
      (fun φ => (Fintype.card Γ : ℝ) * I.cost φ) := by
    refine GRoute.lift (emb k) h' (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
    · funext r
      rcases r with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩)
      · simp [gFk, GF, mkS, emb, embF, mainR, jX, xOf_ne_yOf k]
      · simp [gFk, GF, mkS, emb, embF, mainR, jX, jY]
      · simp [gFk, GF, mkS, emb, embF, freshR, jS]
      · simp [gFk, GF, mkS, emb, embF, copyR, jC]
    · rw [covered_emb] at hi
      push_neg at hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      rcases i with ((⟨g, i, t⟩ | ⟨g, k', q⟩) | (⟨g, c⟩ | ⟨g, j, t⟩))
      · have hx : i ≠ xOf k := fun e => h1 g t (by rw [e]; rfl)
        have hy : i ≠ yOf k := fun e => h2 g t (by rw [e]; rfl)
        simp [gFk, hy, mainR]
      · rfl
      · exact absurd rfl (h4 g c)
      · rfl
    · rw [covered_emb] at hi
      push_neg at hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      rcases i with ((⟨g, i, t⟩ | ⟨g, k', q⟩) | (⟨g, c⟩ | ⟨g, j, t⟩))
      · have hx : i ≠ xOf k := fun e => h1 g t (by rw [e]; rfl)
        have hy : i ≠ yOf k := fun e => h2 g t (by rw [e]; rfl)
        simp [stS, stT, hx, hy]
      · have hk : k' ≠ k := fun e => h3 g q (by rw [e]; rfl)
        simp [stS, stT, hk]
      · exact absurd rfl (h4 g c)
      · simp [stS, stT]
  exact P4L.ORoute.of_groute hL (stS_inv k A sX sY)

/-- **a backward full call `k` as an operator route** (frames in one basis per port). -/
theorem call_bwd (k : Fin 18) (εX : T → Γ ≃ Γ) (M : Γ → GWin H α) (hok : ∀ d, Ok (M d))
    (A : Γ → T → OBase α) (sX sX' sY sY' : Finset α)
    (hXin : ∀ g t, (M (εX t g)).Xm.Φ (tt (I.tv t)) = frame (A g t) sX)
    (hXout : ∀ g t, (M (εX t g)).Xm.Φ 1 = frame (A g t) sX')
    (hYin : ∀ g t, (M (εX t g)).Xm.Φ 0 = frame (A g t) sY)
    (hYout : ∀ g t, (M (εX t g)).Xm.Φ (1 + tt (I.tv t)) = frame (A g t) sY') :
    P4L.ORoute (fun f y => multiAct f (stT (C := C) k A sX' sY' (fun d q => entW (M d).X (I.ent q)))
        (point f (gBk k) (multiAct f (stS' (Sl := Sl) (C := C) k A sX sY) y)))
      (fun φ => (Fintype.card Γ : ℝ) * I.cost φ) := by
  have h := gistageW_bwd I εX M hok (fun d q => entN (M d).X (I.ent q)) (fun d q => entW (M d).X (I.ent q))
    (fun d q => entN_spec _ _) (fun d q => entW_spec _ _) (fun _ _ => 1) (cOne Γ C α) (cOne Γ C α)
  have eS : bIn I.tv εX (fun d => (M d).Xm) (fun _ _ => 1) (cOne Γ C α)
      = stS (Sl := Sl) (C := C) k A sX sY ∘ emb k := by
    funext r
    rcases r with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩)
    · show (M (εX t g)).Xm.Φ (tt (I.tv t)) = _
      simp [stS, emb, embF, mainR, hXin g t]
    · show (M (εX t g)).Xm.Φ 0 = _
      simp [stS, emb, embF, mainR, hYin g t, Ne.symm (xOf_ne_yOf k)]
    · rfl
    · rfl
  have eT : bOut I.tv εX (fun d => (M d).Xm) (fun g q => entW (M g).X (I.ent q) * (fun _ _ => (1 : CMat α)) g q)
        (cOne Γ C α)
      = stT (Sl := Sl) (C := C) k A sX' sY' (fun d q => entW (M d).X (I.ent q)) ∘ emb k := by
    funext r
    rcases r with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩)
    · show (M (εX t g)).Xm.Φ 1 = _
      simp [stT, emb, embF, mainR, hXout g t]
    · show (M (εX t g)).Xm.Φ (1 + tt (I.tv t)) = _
      simp [stT, emb, embF, mainR, hYout g t, Ne.symm (xOf_ne_yOf k)]
    · simp [stT, emb, embF, freshR, bOut, mkS]
    · rfl
  have h' : GRoute (stS (Sl := Sl) (C := C) k A sX sY ∘ emb k)
      (stT (Sl := Sl) (C := C) k A sX' sY' (fun d q => entW (M d).X (I.ent q)) ∘ emb k) GB
      (fun φ => (Fintype.card Γ : ℝ) * I.cost φ) := by
    rw [← eS, ← eT]
    exact h
  have hL : GRoute (stS (Sl := Sl) (C := C) k A sX sY)
      (stT (Sl := Sl) (C := C) k A sX' sY' (fun d q => entW (M d).X (I.ent q))) (gBk k)
      (fun φ => (Fintype.card Γ : ℝ) * I.cost φ) := by
    refine GRoute.lift (emb k) h' (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
    · funext r
      rcases r with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩)
      · simp [gBk, GB, mkS, emb, embF, mainR, jX, jY]
      · simp [gBk, GB, mkS, emb, embF, mainR, jY, Ne.symm (xOf_ne_yOf k)]
      · simp [gBk, GB, mkS, emb, embF, freshR, jS]
      · simp [gBk, GB, mkS, emb, embF, copyR, jC]
    · rw [covered_emb] at hi
      push_neg at hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      rcases i with ((⟨g, i, t⟩ | ⟨g, k', q⟩) | (⟨g, c⟩ | ⟨g, j, t⟩))
      · have hx : i ≠ xOf k := fun e => h1 g t (by rw [e]; rfl)
        have hy : i ≠ yOf k := fun e => h2 g t (by rw [e]; rfl)
        simp [gBk, hx, mainR]
      · rfl
      · exact absurd rfl (h4 g c)
      · rfl
    · rw [covered_emb] at hi
      push_neg at hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      rcases i with ((⟨g, i, t⟩ | ⟨g, k', q⟩) | (⟨g, c⟩ | ⟨g, j, t⟩))
      · have hx : i ≠ xOf k := fun e => h1 g t (by rw [e]; rfl)
        have hy : i ≠ yOf k := fun e => h2 g t (by rw [e]; rfl)
        simp [stS, stT, hx, hy]
      · have hk : k' ≠ k := fun e => h3 g q (by rw [e]; rfl)
        simp [stS, stT, hk]
      · exact absurd rfl (h4 g c)
      · simp [stS, stT]
  exact P4L.ORoute.of_groute hL (stS_inv k A sX sY)

end Call

end
end P16A8
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P16A8.call_fwd
#print axioms OAI.PowerSaving.P16A8.call_bwd

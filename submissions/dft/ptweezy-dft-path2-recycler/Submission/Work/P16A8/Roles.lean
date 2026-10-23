import Submission.Work.Reframe.SNet
import Submission.Work.P4L.ORoute
import Submission.Work.P16A8.Ctrl
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P16A8 (p16a8), roles of one unit

One unit (one gauge copy `g : Γ`) of the query-thinned controller p16a8 on ONE replica:
* main roles `(g, i, t)`: `i : R32` one of `X_j`, `Y_j` (pairs `j < 16`), port `t`;
* fresh helpers `(g, k, q)`: the helper of slot `q` of the FULL call `k < 18`;
* scratch: the provider's copies `(g, c)` (erased by every call) and the thin-query scratch `(g, j, t)`
  (`j < 15`: one zero scratch role per thin query and port; never live, so its output is free).
Full call `k` acts on the pair `(xOf k, yOf k)` (pairs [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 15]), backward iff [False, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, False].
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace P16A8
open Binary Matrix Finset RF

noncomputable section

/-- the live roles: main `(g, i, t)` and fresh helpers `(g, k, q)`. -/
abbrev PLive (Γ T Sl : Type) := (Γ × (R32 × T)) ⊕ (Γ × (Fin 18 × Sl))

/-- the scratch roles: the provider's copies and the thin-query scratch. -/
abbrev PScr (Γ T C : Type) := (Γ × C) ⊕ (Γ × (Fin 15 × T))

/-- all roles. -/
abbrev PRole (Γ T Sl C : Type) := PLive Γ T Sl ⊕ PScr Γ T C

/-- explicit decidable equality (the nested sum is beyond the default instance-search size). -/
instance instDecEqPLive {Γ T Sl : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq Sl] :
    DecidableEq (PLive Γ T Sl) := inferInstanceAs (DecidableEq ((Γ × (R32 × T)) ⊕ (Γ × (Fin 18 × Sl))))
instance instDecEqPScr {Γ T C : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq C] :
    DecidableEq (PScr Γ T C) := inferInstanceAs (DecidableEq ((Γ × C) ⊕ (Γ × (Fin 15 × T))))
instance instDecEqPRole {Γ T Sl C : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq Sl] [DecidableEq C] :
    DecidableEq (PRole Γ T Sl C) := @instDecidableEqSum (PLive Γ T Sl) (PScr Γ T C) instDecEqPLive instDecEqPScr

section Roles
variable {Γ T Sl C : Type}

def mainR (g : Γ) (i : R32) (t : T) : PRole Γ T Sl C := Sum.inl (Sum.inl (g, (i, t)))
def freshR (g : Γ) (k : Fin 18) (q : Sl) : PRole Γ T Sl C := Sum.inl (Sum.inr (g, (k, q)))
def copyR (g : Γ) (c : C) : PRole Γ T Sl C := Sum.inr (Sum.inl (g, c))
def zR (g : Γ) (j : Fin 15) (t : T) : PRole Γ T Sl C := Sum.inr (Sum.inr (g, (j, t)))

/-- the X role of the pair of full call `k`. -/
def xOf (k : Fin 18) : R32 :=
  match k.val with
  | 0 => .x0
  | 1 => .x0
  | 2 => .x1
  | 3 => .x2
  | 4 => .x3
  | 5 => .x4
  | 6 => .x5
  | 7 => .x6
  | 8 => .x7
  | 9 => .x8
  | 10 => .x9
  | 11 => .x10
  | 12 => .x11
  | 13 => .x12
  | 14 => .x13
  | 15 => .x14
  | 16 => .x15
  | _ => .x15

/-- the Y role of the pair of full call `k`. -/
def yOf (k : Fin 18) : R32 :=
  match k.val with
  | 0 => .y0
  | 1 => .y0
  | 2 => .y1
  | 3 => .y2
  | 4 => .y3
  | 5 => .y4
  | 6 => .y5
  | 7 => .y6
  | 8 => .y7
  | 9 => .y8
  | 10 => .y9
  | 11 => .y10
  | 12 => .y11
  | 13 => .y12
  | 14 => .y13
  | 15 => .y14
  | 16 => .y15
  | _ => .y15

lemma xOf_ne_yOf (k : Fin 18) : xOf k ≠ yOf k := by
  fin_cases k <;> decide

/-- the roles of the provider's stage, placed on the network at full call `k`. -/
def embF (k : Fin 18) : SRole Γ T Sl C → PRole Γ T Sl C
  | .inl (.inl (.inl (g, t))) => mainR g (xOf k) t
  | .inl (.inl (.inr (g, t))) => mainR g (yOf k) t
  | .inl (.inr (g, q)) => freshR g k q
  | .inr (g, c) => copyR g c

lemma embF_inj (k : Fin 18) : Function.Injective (embF (Γ := Γ) (T := T) (Sl := Sl) (C := C) k) := by
  intro a b h
  have hxy := xOf_ne_yOf k
  rcases a with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩) <;>
    rcases b with (((⟨g', t'⟩ | ⟨g', t'⟩) | ⟨g', q'⟩) | ⟨g', c'⟩) <;>
    simp_all [embF, mainR, freshR, copyR]

def emb (k : Fin 18) : SRole Γ T Sl C ↪ PRole Γ T Sl C := ⟨embF k, embF_inj k⟩

@[simp] lemma emb_X (k : Fin 18) (g : Γ) (t : T) :
    emb (Sl := Sl) (C := C) k (jX (g, t)) = mainR g (xOf k) t := rfl
@[simp] lemma emb_Y (k : Fin 18) (g : Γ) (t : T) :
    emb (Sl := Sl) (C := C) k (jY (g, t)) = mainR g (yOf k) t := rfl
@[simp] lemma emb_S (k : Fin 18) (g : Γ) (q : Sl) :
    emb (T := T) (C := C) k (jS (g, q)) = freshR g k q := rfl
@[simp] lemma emb_C (k : Fin 18) (g : Γ) (c : C) :
    emb (T := T) (Sl := Sl) k (jC (g, c)) = copyR g c := rfl

variable [Fintype Γ] [Fintype T] [Fintype Sl] [Fintype C]

/-- the roles the full call `k` covers: the acting pair, the helpers of call `k`, the copies. -/
lemma covered_emb (k : Fin 18) (r : PRole Γ T Sl C) :
    r ∈ covered (emb (Γ := Γ) (T := T) (Sl := Sl) (C := C) k) ↔
      (∃ g t, r = mainR g (xOf k) t) ∨ (∃ g t, r = mainR g (yOf k) t) ∨ (∃ g q, r = freshR g k q) ∨
        (∃ g c, r = copyR g c) := by
  rw [cover_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rcases a with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩)
    · exact Or.inl ⟨g, t, rfl⟩
    · exact Or.inr (Or.inl ⟨g, t, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨g, q, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨g, c, rfl⟩))
  · rintro (⟨g, t, rfl⟩ | ⟨g, t, rfl⟩ | ⟨g, q, rfl⟩ | ⟨g, c, rfl⟩)
    · exact ⟨jX (g, t), rfl⟩
    · exact ⟨jY (g, t), rfl⟩
    · exact ⟨jS (g, q), rfl⟩
    · exact ⟨jC (g, c), rfl⟩

end Roles

end
end P16A8
end PowerSaving
end OAI


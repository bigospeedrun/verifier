import Submission.Work.Reframe.SNet
import Submission.Work.P4L.ORoute
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L, part 6: the roles of one P4-L unit and the stages

One unit (one gauge copy `g : Γ`) of the p4 keep303 network on ONE replica:
* main roles `(g, i, t)`: `i : R8` one of `X_j`, `Y_j` (pairs `j < 4`), port `t`;
* fresh helpers `(g, k, q)`: the helper of slot `q` of the call of stage `k < 9` (P4-L-fresh: every slot);
* copies `(g, c)`: the provider's scratch copies (erased by every call).
Stage `k` acts on the pair `(xOf k, yOf k)` (pairs `0, 0, 0, 1, 1, 2, 2, 3, 3`), forward for even `k`, backward
for odd `k`.
`emb k` places the roles of the provider's stage (`RF.SRole`) on the network: ports on the acting pair, slot `(g, q)`
on the fresh helper `(g, k, q)`, copies on copies.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving
namespace P4L
open Binary Matrix Finset RF

noncomputable section

/-- the eight main roles of one port: `X_j`, `Y_j` of the pairs `j < 4`. -/
inductive R8
  | x0 | y0 | x1 | y1 | x2 | y2 | x3 | y3
  deriving DecidableEq, Repr

instance : Fintype R8 where
  elems := {.x0, .y0, .x1, .y1, .x2, .y2, .x3, .y3}
  complete := fun x => by cases x <;> simp

/-- the live roles of a P4-L unit, all gauges: main `(g, i, t)` and fresh helpers `(g, k, q)`. -/
abbrev PLive (Γ T Sl : Type) := (Γ × (R8 × T)) ⊕ (Γ × (Fin 9 × Sl))

/-- all roles: live roles and the provider's copies. -/
abbrev PRole (Γ T Sl C : Type) := PLive Γ T Sl ⊕ (Γ × C)

section Roles
variable {Γ T Sl C : Type}

def mainR (g : Γ) (i : R8) (t : T) : PRole Γ T Sl C := Sum.inl (Sum.inl (g, (i, t)))
def freshR (g : Γ) (k : Fin 9) (q : Sl) : PRole Γ T Sl C := Sum.inl (Sum.inr (g, (k, q)))
def copyR (g : Γ) (c : C) : PRole Γ T Sl C := Sum.inr (g, c)

/-- the X role of the pair acting at stage `k` (pairs `0, 0, 0, 1, 1, 2, 2, 3, 3`). -/
def xOf (k : Fin 9) : R8 :=
  match k.val with
  | 0 => .x0 | 1 => .x0 | 2 => .x0 | 3 => .x1 | 4 => .x1 | 5 => .x2 | 6 => .x2 | _ => .x3

/-- the Y role of the pair acting at stage `k`. -/
def yOf (k : Fin 9) : R8 :=
  match k.val with
  | 0 => .y0 | 1 => .y0 | 2 => .y0 | 3 => .y1 | 4 => .y1 | 5 => .y2 | 6 => .y2 | _ => .y3

lemma xOf_ne_yOf (k : Fin 9) : xOf k ≠ yOf k := by
  fin_cases k <;> decide

/-- stage `k` is forward (even `k`) or backward (odd `k`). -/
def fwdOf (k : Fin 9) : Bool := k.val % 2 == 0

/-- the roles of the provider's stage, placed on the network at stage `k`. -/
def embF (k : Fin 9) : SRole Γ T Sl C → PRole Γ T Sl C
  | .inl (.inl (.inl (g, t))) => mainR g (xOf k) t
  | .inl (.inl (.inr (g, t))) => mainR g (yOf k) t
  | .inl (.inr (g, q)) => freshR g k q
  | .inr (g, c) => copyR g c

lemma embF_inj (k : Fin 9) : Function.Injective (embF (Γ := Γ) (T := T) (Sl := Sl) (C := C) k) := by
  intro a b h
  have hxy := xOf_ne_yOf k
  rcases a with (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, c⟩) <;>
    rcases b with (((⟨g', t'⟩ | ⟨g', t'⟩) | ⟨g', q'⟩) | ⟨g', c'⟩) <;>
    simp_all [embF, mainR, freshR, copyR]

def emb (k : Fin 9) : SRole Γ T Sl C ↪ PRole Γ T Sl C := ⟨embF k, embF_inj k⟩

@[simp] lemma emb_X (k : Fin 9) (g : Γ) (t : T) :
    emb (Sl := Sl) (C := C) k (jX (g, t)) = mainR g (xOf k) t := rfl
@[simp] lemma emb_Y (k : Fin 9) (g : Γ) (t : T) :
    emb (Sl := Sl) (C := C) k (jY (g, t)) = mainR g (yOf k) t := rfl
@[simp] lemma emb_S (k : Fin 9) (g : Γ) (q : Sl) :
    emb (T := T) (C := C) k (jS (g, q)) = freshR g k q := rfl
@[simp] lemma emb_C (k : Fin 9) (g : Γ) (c : C) :
    emb (T := T) (Sl := Sl) k (jC (g, c)) = copyR g c := rfl

variable [Fintype Γ] [Fintype T] [Fintype Sl] [Fintype C]

/-- the roles the stage `k` covers: the acting pair, the helpers of call `k`, the copies. -/
lemma covered_emb (k : Fin 9) (r : PRole Γ T Sl C) :
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
end P4L
end PowerSaving
end OAI

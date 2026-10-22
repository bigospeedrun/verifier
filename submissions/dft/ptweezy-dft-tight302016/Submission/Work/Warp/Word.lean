import Submission.Work.Warp.Sem
import Submission.Work.GCert.Labels.Canon

/-!
# (key: p-warpsem) Signed warp events, the free-group interpretation, and frames given by CODES

The hub's warp event `['warp', r, op, f0, f1]` (op ≠ 0, operator `|op|` with linear map `G_|op|`):
op > 0 carries the frame `f0` to `f1 = G(f0)` and applies `K_G`; op < 0 carries `f0` to `f1 = G⁻¹(f0)` and
applies `K_G⁻¹`.  The scalar replay of the hub runs in the FREE group algebra of these symbols (a row of a register
is a combination of pairs (input register, reduced warp word)).  Here:

* `sgnPerm Ws o`, `sgnMat Ws o = warpMat (sgnPerm Ws o)`  the signed warp of an operator table `Ws : ℕ → APerm α`;
* `sgnMat_mul_neg`   `sgnMat Ws o * sgnMat Ws (-o) = 1` (o ≠ 0);
* `wpush o w`        the hub's `warp_row` on one word (`w[0] = -o` cancels, else `o :: w`);
* `wordMat Ws w`     the matrix of a word (product of its signed warps; free: `free_wordMat`);
* `wordMat_wpush`    **the interpretation is a homomorphism**: `wordMat (wpush o w) = sgnMat o * wordMat w`;
* `sgn_transport`, `sgn_data`   frame transport for a signed event (`f1 = sgnPerm o (f0)`);
* `matPerm A B`      the additive bijection `x ↦ A x` of an invertible matrix (columns `A e_i` = the hub's
                     `G_columns`), `apInv (matPerm A B) = matPerm B A` on points;
* `warp_mem_of_lab`  for CODED frames (`GLab.lab h c`): if `W` maps every basis digit of `c0` into `lab c1` and
                     `cdim c1 ≤ cdim c0`, then `lab c1` is `W` of `lab c0` (the hypothesis of the transport lemmas).
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace WS
open Binary Matrix Finset GF GX
noncomputable section

section Signed
variable {α : Type} [Fintype α] [DecidableEq α]

/-- the additive bijection of a signed operator: `Ws o` for `o ≥ 0`, its inverse for `o < 0`. -/
def sgnPerm (Ws : ℕ → APerm α) (o : ℤ) : APerm α :=
  if 0 ≤ o then Ws o.toNat else apInv (Ws (-o).toNat)

/-- the matrix of a signed warp. -/
def sgnMat (Ws : ℕ → APerm α) (o : ℤ) : CMat α := warpMat (sgnPerm Ws o)

theorem free_sgnMat (Ws : ℕ → APerm α) (o : ℤ) : Free (sgnMat Ws o) := free_warpMat _

lemma sgnPerm_pos (Ws : ℕ → APerm α) {o : ℤ} (ho : 0 < o) : sgnPerm Ws o = Ws o.toNat := by
  unfold sgnPerm; rw [if_pos (le_of_lt ho)]

lemma sgnPerm_neg (Ws : ℕ → APerm α) {o : ℤ} (ho : o < 0) : sgnPerm Ws o = apInv (Ws (-o).toNat) := by
  unfold sgnPerm; rw [if_neg (not_le.mpr ho)]

/-- `-o` undoes `o`. -/
theorem sgnPerm_neg_eq (Ws : ℕ → APerm α) {o : ℤ} (ho : o ≠ 0) :
    sgnPerm Ws (-o) = apInv (sgnPerm Ws o) := by
  rcases lt_or_gt_of_ne ho with h | h
  · rw [sgnPerm_neg Ws h, sgnPerm_pos Ws (neg_pos.mpr h), apInv_apInv]
  · rw [sgnPerm_pos Ws h, sgnPerm_neg Ws (neg_lt_zero.mpr h), neg_neg]

theorem sgnMat_mul_neg (Ws : ℕ → APerm α) {o : ℤ} (ho : o ≠ 0) :
    sgnMat Ws o * sgnMat Ws (-o) = 1 := by
  unfold sgnMat; rw [sgnPerm_neg_eq Ws ho]; exact warpMat_mul_inv _

theorem sgnMat_neg_mul (Ws : ℕ → APerm α) {o : ℤ} (ho : o ≠ 0) :
    sgnMat Ws (-o) * sgnMat Ws o = 1 := by
  unfold sgnMat; rw [sgnPerm_neg_eq Ws ho]; exact warpMat_inv_mul _

/-- the hub's `warp_row` on one word: a leading `-o` cancels, otherwise `o` is pushed. -/
def wpush (o : ℤ) : List ℤ → List ℤ
  | [] => [o]
  | o' :: w => if o' = -o then w else o :: o' :: w

/-- the matrix of a warp word (first letter = last applied). -/
def wordMat (Ws : ℕ → APerm α) : List ℤ → CMat α
  | [] => 1
  | o :: w => sgnMat Ws o * wordMat Ws w

@[simp] lemma wordMat_nil (Ws : ℕ → APerm α) : wordMat Ws [] = 1 := rfl
@[simp] lemma wordMat_cons (Ws : ℕ → APerm α) (o : ℤ) (w : List ℤ) :
    wordMat Ws (o :: w) = sgnMat Ws o * wordMat Ws w := rfl

theorem free_wordMat (Ws : ℕ → APerm α) : ∀ w : List ℤ, Free (wordMat Ws w)
  | [] => Free.one
  | o :: w => Free.mul (free_sgnMat Ws o) (free_wordMat Ws w)

/-- **The free-group interpretation is a homomorphism**: pushing `o` on a word multiplies its matrix by the
signed warp of `o` (for `o ≠ 0`; the hub never uses `0`). -/
theorem wordMat_wpush (Ws : ℕ → APerm α) {o : ℤ} (ho : o ≠ 0) (w : List ℤ) :
    wordMat Ws (wpush o w) = sgnMat Ws o * wordMat Ws w := by
  cases w with
  | nil => simp [wpush]
  | cons o' w =>
    by_cases h : o' = -o
    · subst h
      show wordMat Ws (if -o = -o then w else o :: -o :: w) = sgnMat Ws o * (sgnMat Ws (-o) * wordMat Ws w)
      rw [if_pos rfl, ← Matrix.mul_assoc, sgnMat_mul_neg Ws ho, Matrix.one_mul]
    · simp only [wpush, if_neg h, wordMat_cons]

/-- **frame transport for a signed event**: `f1 = sgnPerm o (f0)`. -/
theorem sgn_transport (Ws : ℕ → APerm α) (o : ℤ) (U V : SLbl α)
    (h : ∀ x, V.Mem x ↔ U.Mem ((apInv (sgnPerm Ws o)).π x)) :
    ∃ P : CMat α, Free P ∧ P * U.rep = V.rep * sgnMat Ws o :=
  warp_transport (sgnPerm Ws o) U V h

theorem sgn_data {ρ : Type} [Fintype ρ] [DecidableEq ρ] (l : ρ) (Ws : ℕ → APerm α) (o : ℤ)
    (U V : SLbl α) (h : ∀ x, V.Mem x ↔ U.Mem ((apInv (sgnPerm Ws o)).π x)) :
    ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = 0) ∧
      ∀ (f : ℕ) (x : Data α ρ f),
        (∀ y : Sky α f → ℂ, x l = matAct f U.rep y →
          gwalk f w x l = matAct f V.rep (matAct f (sgnMat Ws o) y)) ∧
        (∀ j, j ≠ l → gwalk f w x j = x j) :=
  warp_data l (sgnPerm Ws o) U V h

end Signed

section LiftSigned
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

/-- lifting commutes with signing. -/
theorem WLift.sgnPerm_lift {X : BXMap H α} (L : WLift X) (Ws : ℕ → APerm H) (o : ℤ) :
    sgnPerm (fun k => L.liftW (Ws k)) o = L.liftW (sgnPerm Ws o) := by
  by_cases ho : 0 ≤ o
  · simp only [sgnPerm, if_pos ho]
  · simp only [sgnPerm, if_neg ho, L.liftW_inv]

/-- signed frame transport through a frame map. -/
theorem WLift.sgn_transport {X : BXMap H α} (L : WLift X) (Ws : ℕ → APerm H) (o : ℤ) (U V : SLbl H)
    (h : ∀ x, V.Mem x ↔ U.Mem ((apInv (sgnPerm Ws o)).π x)) :
    ∃ P : CMat α, Free P ∧ P * X.Φ U = X.Φ V * sgnMat (fun k => L.liftW (Ws k)) o := by
  unfold sgnMat
  rw [L.sgnPerm_lift]
  exact L.transport _ U V h

end LiftSigned

section MatPerm
variable {H : Type} [Fintype H] [DecidableEq H]

/-- the additive bijection `x ↦ A x` of an invertible matrix over `F` (`A e_i` = column `i`). -/
def matPerm (A B : Matrix H H F) (hAB : A * B = 1) (hBA : B * A = 1) : APerm H where
  π :=
    { toFun := fun x => A *ᵥ x
      invFun := fun y => B *ᵥ y
      left_inv := fun x => by
        show B *ᵥ (A *ᵥ x) = x
        rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
      right_inv := fun y => by
        show A *ᵥ (B *ᵥ y) = y
        rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec] }
  add := fun x y => Matrix.mulVec_add _ x y

@[simp] lemma matPerm_apply (A B : Matrix H H F) (hAB : A * B = 1) (hBA : B * A = 1) (x : Space H) :
    (matPerm A B hAB hBA).π x = A *ᵥ x := rfl

@[simp] lemma matPerm_inv_apply (A B : Matrix H H F) (hAB : A * B = 1) (hBA : B * A = 1) (y : Space H) :
    (apInv (matPerm A B hAB hBA)).π y = B *ᵥ y := rfl

end MatPerm

section Codes
open GLab
variable {h : ℕ}

/-- an additive bijection maps a coded subspace into a label if it maps its basis digits there. -/
theorem map_lab {c0 : ℕ} (hg0 : Good h c0) (W : APerm (Fin h)) (V : SLbl (Fin h))
    (H : ∀ p : Fin h, V.Mem (W.π (bas h (cP h c0) p))) :
    ∀ x, (lab h c0).Mem x → V.Mem (W.π x) := by
  intro x hx
  rw [(lab_mem hg0 x).mp hx, APerm.map_sum']
  exact Finset.sum_induction _ (fun y => V.Mem y) (fun _ _ => GLab.mem_add _) (GLab.mem_zero _)
    (fun p _ => by rw [APerm.map_smul']; exact GLab.mem_smul _ _ (H p))

/-- **the warp hypothesis from CODES**: `lab c1` is `W` of `lab c0`. -/
theorem warp_mem_of_lab {c0 c1 : ℕ} (hg0 : Good h c0) (hg1 : Good h c1) (W : APerm (Fin h))
    (H : ∀ p : Fin h, (lab h c1).Mem (W.π (bas h (cP h c0) p))) (hdim : cdim c1 ≤ cdim c0) :
    ∀ x, (lab h c1).Mem x ↔ (lab h c0).Mem ((apInv W).π x) :=
  warp_mem_of_map W (lab h c0) (lab h c1) (map_lab hg0 W _ H)
    (by rw [lab_dim hg0, lab_dim hg1]; exact hdim)

/-- frame transport between CODED frames. -/
theorem warp_transport_lab {c0 c1 : ℕ} (hg0 : Good h c0) (hg1 : Good h c1) (W : APerm (Fin h))
    (H : ∀ p : Fin h, (lab h c1).Mem (W.π (bas h (cP h c0) p))) (hdim : cdim c1 ≤ cdim c0) :
    ∃ P : CMat (Fin h), Free P ∧ P * (lab h c0).rep = (lab h c1).rep * warpMat W :=
  warp_transport W _ _ (warp_mem_of_lab hg0 hg1 W H hdim)

/-- the same through a frame map. -/
theorem WLift.transport_lab {α : Type} [Fintype α] [DecidableEq α] {X : BXMap (Fin h) α} (L : WLift X)
    {c0 c1 : ℕ} (hg0 : Good h c0) (hg1 : Good h c1) (W : APerm (Fin h))
    (H : ∀ p : Fin h, (lab h c1).Mem (W.π (bas h (cP h c0) p))) (hdim : cdim c1 ≤ cdim c0) :
    ∃ P : CMat α, Free P ∧ P * X.Φ (lab h c0) = X.Φ (lab h c1) * warpMat (L.liftW W) :=
  L.transport W _ _ (warp_mem_of_lab hg0 hg1 W H hdim)

end Codes

end
end WS
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.WS.sgnMat_mul_neg
#print axioms OAI.PowerSaving.WS.wordMat_wpush
#print axioms OAI.PowerSaving.WS.free_wordMat
#print axioms OAI.PowerSaving.WS.sgn_transport
#print axioms OAI.PowerSaving.WS.sgn_data
#print axioms OAI.PowerSaving.WS.WLift.sgn_transport
#print axioms OAI.PowerSaving.WS.matPerm
#print axioms OAI.PowerSaving.WS.warp_mem_of_lab
#print axioms OAI.PowerSaving.WS.warp_transport_lab
#print axioms OAI.PowerSaving.WS.WLift.transport_lab

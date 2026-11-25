import Submission.OAI.Computability.NearSquareRoot.KernelPass
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! Exact complex semantics for the normalized, even-width binary template.
The batch theorem applies to arbitrary complex data, including nonrational data. -/

namespace DFTSpeedrun.ComplexPlan
open OAI.Computability.NearSquareRoot.KernelPass Matrix
noncomputable section

abbrev Bank (A h i : ℕ) := Fin i → Addr A h → ℂ

def act {A i o : ℕ} (p : Plan A i o) (h : ℕ) (x : Bank A h i) : Bank A h o :=
  Function.curry (((p.eval h).map (Rat.castHom ℂ)).mulVec (Function.uncurry x))

theorem seq {A i j o h} (p : Plan A j o) (q : Plan A i j) (x : Bank A h i) :
    act (p.seq q) h x = act p h (act q h x) := by
  simp only [act, Plan.eval, Matrix.map_mul (f := Rat.castHom ℂ), Function.uncurry_curry, Matrix.mulVec_mulVec]

theorem mix {A i o h : ℕ} (coeff : Fin o → Fin i → Coefficient) (x : Bank A h i) :
    act (Plan.mix coeff) h x = fun b y => ∑ a, (value (coeff b a) : ℂ) * x a y := by
  classical
  funext b y
  simp [act, Plan.eval, Matrix.mulVec, Matrix.map, Function.comp_def, dotProduct, Fintype.sum_prod_type, ite_mul, apply_ite]

theorem scale {A h q : ℕ} (test : Column A → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) (x : Bank A h 1) :
    act (Plan.scale q test table) h x =
      fun _ y => (value (table (∑ c, test (y c))) : ℂ) * x 0 y := by
  classical
  funext b y
  simp [act, Plan.eval, Matrix.mulVec, Matrix.map, Function.comp_def, dotProduct, Fintype.sum_prod_type, ite_mul, apply_ite]

theorem xorColumn_involutive {A : ℕ} (g : Fin A × Fin A) :
    Function.Involutive (xorColumn g) := by
  intro x; funext a j
  by_cases h : g.1 ≠ g.2 ∧ a = g.1
  · have ha : ¬(g.1 ≠ g.2 ∧ g.2 = g.1) := by grind
    have hh : ∀ z : ZMod 2, z + z = 0 := by decide
    simp [xorColumn,h,ha,h.1.symm,add_assoc,hh]
  · simp [xorColumn,h]

theorem xor {A h : ℕ} (g : Fin A × Fin A) (x : Bank A h 1) :
    act (Plan.xor g) h x = fun _ y => x 0 (xorColumn g ∘ y) := by
  classical
  funext b y
  have cancel (u : Addr A h) : xorColumn g ∘ (xorColumn g ∘ u) = u :=
    funext (fun j => xorColumn_involutive g (u j))
  have iff (u : Addr A h) : y = xorColumn g ∘ u ↔ u = xorColumn g ∘ y := by
    constructor <;> intro hh
    · rw [hh, cancel]
    · rw [hh,cancel]
  simp [act, Plan.eval, Matrix.mulVec, Matrix.map, Function.comp_def, dotProduct, Fintype.sum_prod_type, iff, ite_mul, apply_ite]
  change (∑ u : Addr A h, if y = xorColumn g ∘ u then x 0 u else 0) = _
  simp [iff]; rfl

theorem parallel {A i j o u h : ℕ} (p : Plan A i o) (q : Plan A j u)
    (x : Bank A h i) (y : Bank A h j) :
    act (p.parallel q) h (Fin.append x y) = Fin.append (act p h x) (act q h y) := by
  classical
  funext b z
  refine Fin.addCases (fun l => ?_) (fun r => ?_) b <;>
    simp only [act, Plan.eval, directSum, Function.curry_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Function.uncurry, Fin.append_left, Fin.append_right,
      Matrix.map, Function.comp_apply, Fin.addCases_left, Fin.addCases_right] <;>
    rw [Fin.sum_univ_add] <;> simp

/-- Embed an even child-width vector into the fiber through an arbitrary address. -/
def setAxis {A h} (y : Addr A h) (a : Fin A) (u : Fin h → Fin 2 → ZMod 2) : Addr A h :=
  fun c => Function.update (y c) a (u c)

private theorem setAxis_injective {A h} (y : Addr A h) (a : Fin A) :
    Function.Injective (setAxis y a) := by
  intro u v huv
  funext c
  simpa [setAxis] using congrArg (fun z : Addr A h => z c a) huv

/-- The oracle call is a sum over only the selected axis; other coordinates of
each source address equal the output address. -/
theorem child {A h} (a : Fin A) (x : Bank A h 1) (y : Addr A h) :
    act (Plan.child a) h x 0 y =
      ∑ u : Fin h → Fin 2 → ZMod 2, (∏ c, (pairEntry (y c a) (u c) : ℂ)) *
        x 0 (setAxis y a u) := by
  classical
  let coeff (z : Addr A h) := ∏ c, (childEntry a (y c) (z c) : ℂ)
  have fold : act (Plan.child a) h x 0 y = ∑ z, coeff z * x 0 z := by
    simp [act, Plan.eval, Matrix.map, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, coeff]
  rw [fold]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (setAxis y a)))]
  · rw [Finset.sum_image (fun u _ v _ eq => setAxis_injective y a eq)]
    congr 1
    funext u
    have keep (c : Fin h) : ∀ b ≠ a, setAxis y a u c b = y c b := by
      intro b hb; simp [setAxis, Function.update_of_ne hb]
    have at_a (c : Fin h) : setAxis y a u c a = u c := by simp [setAxis]
    have factor (c : Fin h) : childEntry a (y c) (setAxis y a u c) = pairEntry (y c a) (u c) := by
      rw [childEntry, if_pos (keep c), at_a]
    simp only [coeff, factor]
  · intro z _ hz
    have miss : ¬ (∀ c : Fin h, ∀ b ≠ a, z c b = y c b) := by
      intro same
      apply hz
      apply Finset.mem_image.mpr
      refine ⟨fun c => z c a, Finset.mem_univ _, ?_⟩
      funext c b
      by_cases hb : b = a
      · subst b; simp [setAxis]
      · simp [setAxis,Function.update_of_ne hb, same c b hb]
    push_neg at miss
    obtain ⟨c,b,hb,hne⟩ := miss
    have bad : ¬ ∀ d ≠ a, z c d = y c d := fun hh => hne (hh b hb)
    have hzero : coeff z = 0 := Finset.prod_eq_zero (Finset.mem_univ c)
      (by simp [childEntry,bad])
    rw [hzero,zero_mul]

theorem correct {A W h : ℕ} {p : Plan A W W} (ok : Correct p) (x : Bank A h W) :
    act p h x = fun b y => ∑ u : Addr A h,
      (∏ c, ∏ j, (pairEntry (y c j) (u c j) : ℂ)) * x b u := by
  classical
  funext b y
  simp [act,ok h,target,Matrix.mulVec,Matrix.map, Function.comp_def,dotProduct,Fintype.sum_prod_type,apply_ite,ite_mul]
  rw [Finset.sum_comm]
  simp

end
end DFTSpeedrun.ComplexPlan

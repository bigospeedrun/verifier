import Submission.BinaryKernel.PlanCompiler
import Submission.BinaryKernel.ColumnLeaves

namespace DFTSpeedrun.PlanCompiler
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.Computability.NearSquareRoot.KernelPass
open FixedRows AxisLayout
noncomputable section
universe u
variable {ι : Type u} {port : Port} {b : RAM.Bank port ι} {m : Bool} {cl : Paint}
variable {A : ℕ} {h : ι → ℕ} {Z : ι → ℕ}

private theorem unary_exec {P : Plan A 1 1} (pure : P.calls = 0)
    (ha : 0 < A) (sh : Small b.B h) (sv : Small b.B (fun i => volume A (h i)))
    (f : ∀ k, (Addr A k → ℂ) → Addr A k → ℂ)
    (sem : ∀ k (v : ComplexPlan.Bank A k 1), ComplexPlan.act P k v = fun _ => f k (v 0))
    (core : ∀ (c' : Bench m ι) (v : ∀ i, Addr A (h i) → ℂ),
      c'.Nick h → Small c'.size (fun i => ColumnLeaves.volume A (h i)) →
      c'.Nick (fun i => 4^(h i)) →
      c'.Moves (fun _ => 0) (a (c cl)) (fun i => (shape A (h i)).tape (v i)) →
      c'.Moves (fun i => ColumnLeaves.volume A (h i)) (a (c cl))
        (fun i => (shape A (h i)).tape (f (h i) (v i)))) :
    Executes b m cl h Z P := by
  intro X
  let src := fun i => (h i,source h X i)
  let home : Bench m ι := ⟨b.B, p w (a (bundle cl)),src⟩
  let N := fun i => ColumnLeaves.volume A (h i)
  have cap : Small home.size N := sv.mono (fun i => (ColumnLeaves.size_eq A (h i)).ge)
  have one (k : ℕ) : volume 1 k = 4^k := by
    simpa [volume,ColumnLeaves.volume] using ColumnLeaves.size_eq 1 k
  have leN (i : ι) : 4^(h i) ≤ N i := by
    apply Nat.pow_le_pow_left _ _
    calc 4 = 4^1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right (by decide) ha
  have axisCap : Small b.B (fun i => volume 1 (h i)) := cap.mono (fun i => (one _ ▸ leN i))
  have len : home.Moves N w (fun i => 4^(h i)) :=
    ((prepareVolume (b := b) (m := m) (s := p w (a (bundle cl))) (x := src)
      (A := 1) (by decide) sh axisCap Can.first).cy (fun i => one _)).mono
        (fun i => (one _).trans_le (leN i))
  have plan : home.Moves N (a (bundle cl)) (source h (fun i => ComplexPlan.act P (h i) (X i))) := by
    apply Bench.caseM len
    let c' := home.extend w (fun i => 4^(h i))
    have row0 : c'.Moves (fun _ => 0) (a (c cl)) (fun i => (shape A (h i)).tape (X i 0)) :=
      FixedRows.row (t := bundle cl) (V := fun i a => (shape A (h i)).tape (X i a)) Can.first.snd 0
    have run := core c' (fun i => X i 0) ⟨Can.first.fst,sh⟩ cap ⟨Can.second,cap.mono leN⟩ row0
    exact FixedRows.assemble (fun a : Fin 1 => run.cy (fun i => by simp only [sem]))
  exact (Able.of_can plan).mono (fun i => (ColumnLeaves.size_eq A _).ge)
    (fun i => by simp [pure])

theorem xor_exec (ha : 0 < A) (sh : Small b.B h) (sv : Small b.B (fun i => volume A (h i)))
    (g : Fin A × Fin A) :
    Executes b m cl h Z (Plan.xor (A := A) g) :=
  unary_exec rfl ha sh sv (fun _ v y => v (xorColumn g ∘ y)) (fun _ v => ComplexPlan.xor g v)
    (fun _ v count cap stride inp => ColumnLeaves.reindex ha cl h v _ count cap stride inp)

theorem scale_exec (ha : 0 < A) (sh : Small b.B h) (sv : Small b.B (fun i => volume A (h i)))
    (q : ℕ) (test : Column A → Fin q → ZMod 2) (tbl : (Fin q → ZMod 2) → Coefficient) :
    Executes b m cl h Z (Plan.scale (A := A) q test tbl) :=
  unary_exec rfl ha sh sv (fun _ v y => (value (tbl (∑ c, test (y c))) : ℂ)*v y)
    (fun _ v => ComplexPlan.scale test tbl v)
    (fun _ v count cap stride inp => ColumnLeaves.diagonal ha cl h v test (value ∘ tbl) count cap stride inp)

end
end DFTSpeedrun.PlanCompiler
#print axioms DFTSpeedrun.PlanCompiler.xor_exec
#print axioms DFTSpeedrun.PlanCompiler.scale_exec

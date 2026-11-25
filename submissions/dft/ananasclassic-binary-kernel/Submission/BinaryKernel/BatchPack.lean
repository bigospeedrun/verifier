import Submission.BinaryKernel.BatchData

namespace DFTSpeedrun.Batch
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.Computability.NearSquareRoot.KernelPass
open AxisLayout FixedRows
noncomputable section
universe u

theorem pack_group {ι : Type u} {A W s : ℕ} {cl m} {B k h : ι → ℕ}
    (ha : 0 < A) (eqdim : ∀ i, A*(h i*2) + s*2 = k i*2)
    (v : ∀ i, Bits (k i*2) → ℂ) (sh : Small B h) (sn : Small B (fun i => 2^(k i*2)))
    (kn : Knows m B (HalfKernel.Src cl) (fun i => (k i,(bits (k i*2)).tape (v i))) h)
    (g : ℕ) :
    Can m B (HalfKernel.Src cl) (p w (Ty.a (bundle cl)))
      (fun i => (k i,(bits (k i*2)).tape (v i)))
      (fun i => (h i,bankTape (shape A (h i)) (input (W:=W) (eqdim i) (v i) g)))
      (fun i => 2^(k i*2)) := by
  let x := fun i => (k i,(bits (k i*2)).tape (v i))
  let V := fun i => PlanCompiler.volume A (h i)
  have lV (i : ι) : V i ≤ 2^(k i*2) := by
    rw [← eqdim i, pow_add, ←volume_bits]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have sv : Small B V := sn.mono lV
  have vol := PlanCompiler.prepareVolume (b:=Bank.closed B) (s:=HalfKernel.Src cl) (x:=x) ha sh sv kn
  let x' := fun i => (x i,V i)
  let t := p (HalfKernel.Src cl) w
  have pack : Can m B t (Ty.a (bundle cl)) x'
      (fun i => bankTape (shape A (h i)) (input (W:=W) (eqdim i) (v i) g)) V := by
    apply FixedRows.assemble
    intro b
    let c := (bits (s*2)).loc (highAt (g*W+b.val))
    have knowsVol : Knows m B t x' (fun i => (shape A (h i)).n) := Can.second
    apply Can.mono (Can.layout (L:=fun i => shape A (h i)) (P:=fun _ => 0) (W:=fun _ => 0)
      knowsVol ?_ sv) (fun i => by simp [V,PlanCompiler.volume])
    let ix := Σ i, Addr A (h i)
    let cell := fun d : ix => (x' d.1, code d.2)
    have sc : Small (fun d : ix => B d.1) (fun d => code d.2) :=
      (sv.reindex Sigma.fst).mono fun d => ((shape A (h d.1)).bd d.2).le
    have idx : Knows m (fun d : ix => B d.1) (p t w) cell
        (fun d => code d.2 + V d.1 * c) :=
      Can.second.wadd (Can.first.snd.wmul (Can.wc c) ((sv.reindex Sigma.fst).mul (Small.const _ c)))
        (sc.add ((sv.reindex Sigma.fst).mul (Small.const _ c)))
    apply Can.fetch (s:=p t w) (t:=Ty.c cl) (x:=cell) (B:=fun d : ix => B d.1)
      (L:=fun d : ix => bits (k d.1*2))
      (i:=fun d => joined (eqdim d.1) d.2 (highAt (g*W+b.val)))
      (v:=fun d => v d.1) (Can.first.fst.snd)
    exact idx.cy fun d => (joined_loc (eqdim d.1) d.2 (highAt (g*W+b.val))).symm
  exact ((kn.mono fun _ => Nat.zero_le _).pair (vol.bind pack)).mono lV
end
end DFTSpeedrun.Batch

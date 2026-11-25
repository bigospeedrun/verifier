import Submission.BinaryKernel.AxisLayout
import Submission.BinaryKernel.FixedRows

/-! Budget-preserving compilation of the fixed instructions in a selected plan.
A child invocation is billed as an exact unit of recursive work; composition
only adds such units. -/
namespace DFTSpeedrun.PlanCompiler
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.Computability.NearSquareRoot.KernelPass
open FixedRows AxisLayout OAI.PowerSaving.Binary
noncomputable section
universe u
variable {ι : Type u} {port : Port} (b : RAM.Bank port ι) (m : Bool) (cl : Paint)
variable {A : ℕ} (h : ι → ℕ) (Z : ι → ℕ)
def volume (A h : ℕ) := (shape A h).n

lemma volume_eq (A h : ℕ) : volume A h = (2^(2*A))^h := by
  change ((bits (h*2)).n)^A = _
  rw [OAI.PowerSaving.Binary.bits_len, ← pow_mul, ← pow_mul]
  ring_nf

abbrev source {A n : ℕ} (h : ι → ℕ) (v : ∀ i, ComplexPlan.Bank A (h i) n) :=
  fun i => bankTape (shape A (h i)) (v i)

def Executes {n r} (p : Plan A n r) := ∀ X : ∀ i, ComplexPlan.Bank A (h i) n,
  Run b m cl h (fun i => volume A (h i)) (fun i => p.calls * Z i)
    (source h X) (source h fun i => ComplexPlan.act p (h i) (X i))

variable {b m cl h Z}
theorem prepareVolume {s : Ty} {x : ι → T s} (ha : 0 < A)
    (sh : Small b.B h) (sv : Small b.B fun i => volume A (h i))
    (count : Knows m b.B s x h) :
    Can m b.B s w x (fun i => volume A (h i)) (fun i => volume A (h i)) := by
  let Q := 2^(2*A)
  have q : 1 < Q := Nat.one_lt_two_pow (by omega)
  have sm : Small b.B fun i => Q^(h i) := sv.mono fun i => (volume_eq _ _).ge
  have step : Can m (fun t : During h => b.B t.i) (p s (p w w)) w
      (fun t : During h => (x t.i,t.j,Q^t.j)) (fun t => Q^(t.j+1)) (fun _ => 0) :=
    ((Can.second.snd).wmul (Can.wc Q)
      ((sm.reindex During.i).mono fun t => by
        rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) t.hj)).cy fun t => (pow_succ _ _).symm
  have tbl := Can.loop (t := w) (uB := fun _ _ => 0) (W' := fun _ => 0)
    (v := fun _ k => Q^k) count (Can.wc 1) step sh
  refine (tbl.cy fun _ => (volume_eq _ _).symm).mono fun i => ?_
  simpa [volume_eq] using (Nat.lt_pow_self q (n := h i)).le

theorem mix_exec {n r} (ha : 0<A) (sh : Small b.B h) (sv : Small b.B fun i => volume A (h i))
    (g : Fin r → Fin n → Coefficient) :
    Executes b m cl h Z (Plan.mix (A := A) g) := by
  intro X
  let src := fun i => (h i,source h X i)
  have vol := prepareVolume (b := b) (m := m) (s := p w (a (bundle cl))) (x := src) ha sh sv Can.first
  have core := FixedRows.mix (m := m) (cl := cl) (B := b.B)
    (s := p (p w (a (bundle cl))) w)
    (x := fun i => (src i, volume A (h i))) (L := fun i => shape A (h i)) (V := X)
    (fun j k => value (g j k)) Can.first.snd Can.second sv
  exact (Able.of_can (vol.bind core)).cong (fun _ => rfl) (fun i => by dsimp only [source]; rw [ComplexPlan.mix])
    |>.mono (fun _ => le_rfl) (fun _ => by simp [Plan.calls])

theorem seq_exec {i j o} {p : Plan A j o} {q : Plan A i j}
    (u : Executes b m cl h Z p) (v : Executes b m cl h Z q) :
    Executes b m cl h Z (Plan.seq p q) := by
  intro X
  exact ((FixedRows.seq (v X) (u _)).cong (fun _ => rfl) (fun d => by
      dsimp only [source]; rw [ComplexPlan.seq])).mono (fun _ => le_rfl) (fun _ => by simp [Plan.calls,add_mul,add_comm])

theorem parallel_exec {i j o u} {p : Plan A i o} {q : Plan A j u}
    (f : Executes b m cl h Z p) (g : Executes b m cl h Z q) :
    Executes b m cl h Z (Plan.parallel p q) := by
  intro X
  let L := fun d (a : Fin i) => X d (Fin.castAdd j a)
  let R := fun d (a : Fin j) => X d (Fin.natAdd i a)
  have eqX (d : ι) : Fin.append (L d) (R d) = X d := Fin.append_castAdd_natAdd
  have eqTap {a c : ℕ} (d : ι) (l : ComplexPlan.Bank A (h d) a) (r : ComplexPlan.Bank A (h d) c) :
      Fin.append (fun i => (shape A (h d)).tape (l i)) (fun i => (shape A (h d)).tape (r i)) =
        fun j => (shape A (h d)).tape (Fin.append l r j) := by
    funext j
    refine Fin.addCases ?_ ?_ j <;> (intro k; simp)
  have res := FixedRows.parallel (f L) (g R)
  refine (res.cong ?_ ?_).mono (fun _ => le_rfl) (fun _ => by simp [Plan.calls,add_mul])
  · intro d
    change (_,fixed (Fin.append _ _)) = (_,source h X d)
    rw [eqTap d (L d) (R d),eqX]; rfl
  · intro d
    change fixed (Fin.append _ _) = bankTape _ (ComplexPlan.act _ _ _)
    rw [eqTap,←eqX d,ComplexPlan.parallel]; rfl

theorem compile {n r} (ha : 0<A) (sh : Small b.B h) (sv : Small b.B fun i => volume A (h i))
    (xor : ∀ g, Executes b m cl h Z (Plan.xor (A := A) g))
    (scale : ∀ q t v, Executes b m cl h Z (Plan.scale (A := A) q t v))
    (child : ∀ a, Executes b m cl h Z (Plan.child (A := A) a))
    (p : Plan A n r) : Executes b m cl h Z p := by
  induction p with
  | mix g => exact mix_exec ha sh sv g
  | xor g => exact xor g
  | scale q t v => exact scale q t v
  | child a => exact child a
  | seq _ _ ih1 ih2 => exact seq_exec ih1 ih2
  | parallel _ _ ih1 ih2 => exact parallel_exec ih1 ih2
end
end DFTSpeedrun.PlanCompiler

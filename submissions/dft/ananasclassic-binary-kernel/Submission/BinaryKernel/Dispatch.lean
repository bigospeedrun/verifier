import Submission.BinaryKernel.KernelBase
import Submission.BinaryKernel.Child

/-! Dispatch on the finitely many possible numbers of spectator columns. Each
branch may have its own fixed program. Only the chosen branch incurs recursive
charges. -/
namespace DFTSpeedrun.HalfKernel
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty DFTSpeedrun.HalfCost
open OAI.Computability.NearSquareRoot.KernelPass
noncomputable section

theorem cases_word {ι : Type} {cld : Port} {b : Bank cld ι} {m s t}
    {x : ι → T s} {y : ι → T t} {W Z f : ι → ℕ} {N : ℕ}
    (get : Knows m b.B s x f) (bd : ∀ i, f i < N)
    (branch : ∀ j : Fin N, Able m (b.comap (fun i : {i // f i=j.val} => i.1))
      s t (fun i => x i.1) (fun i => y i.1) (fun i => W i.1) (fun i => Z i.1)) :
    Able m b s t x y W Z := by
  suffices ∀ n {κ : Type} (e : κ → ι), (∀ i, f (e i) < n) →
      Able m (b.comap e) s t (fun i => x (e i)) (fun i => y (e i))
        (fun i => W (e i)) (fun i => Z (e i)) from this N id bd
  intro n
  induction n with
  | zero =>
    intro κ e h
    exact ⟨Code.blank _ _,0,0,fun i => absurd (h i) (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro κ e h
    let flag := fun i => if f (e i) = n then 0 else 1
    have hf : Knows m (b.comap e).B s (fun i => x (e i)) flag :=
      Can.eqbit (get.reindex e) (Can.wc n)
    refine (Able.ifz (W:=fun i => W (e i)) (Z:=fun i => Z (e i))
      (Able.of_can (b:=b.comap e) hf) ?_ ?_).mono (fun _ => by simp) (fun _ => by simp)
    · by_cases hn : n < N
      · exact (branch ⟨n,hn⟩).reindex fun i : {i // flag i = 0} => ⟨e i.1,by simpa [flag] using i.2⟩
      · exact ⟨Code.blank _ _,0,0,fun i => False.elim (hn (by
          have h₁ : f (e i.1) = n := by simpa [flag] using i.2
          simpa [← h₁] using bd (e i.1)))⟩
    · exact ih (fun i : {i // flag i ≠ 0} => e i.1) fun i => by
        have hh : ¬ f (e i.1) = n := by simpa [flag] using i.2
        have := h i.1
        omega

abbrev BigCtx (cl : Paint) (A r : ℕ) := {g : Ctx cl A r // r+A ≤ g.d.1}
abbrev RCtx (cl : Paint) (A r s : ℕ) :=
  {g : BigCtx cl A r // spare A r g.1.d.1 = s}

abbrev FixedStep (cl : Paint) (m : Bool) (A W σ r s : ℕ) :=
  let embed := fun i : RCtx cl A r s => i.1.1
  Able m ((bank cl A r).comap embed) (Src cl) (bundle cl)
    (fun i => source cl (embed i).d) (fun i => answer cl (embed i).d)
    (fun i => volume (embed i).d) (fun i => children A W σ r (embed i).d.1 * (embed i).tau)

theorem large_of_fixed {cl : Paint} {m : Bool} {A W σ r : ℕ} (hA : 0 < A)
    (fixed : ∀ s < r+A, FixedStep cl m A W σ r s) : LargeBody cl m A W σ r := by
  let I := BigCtx cl A r
  let b := (bank cl A r).comap (fun i : I => i.1)
  let x := fun i : I => source cl i.1.d
  let k := fun i : I => i.1.d.1
  have sk : Small b.B k := small_width.reindex (fun i : I => i.1.d)
  have readK : Knows m b.B (Src cl) x k := Can.first
  have msub := readK.minus (Can.wc r) sk
  have rem := msub.modW (Can.wc A) sk.sub
  have hs := (Can.wc r).plus rem (Small.const b.B r) sk.sub.mod
  exact cases_word (b:=b) (N:=r+A) hs (fun i => Nat.add_lt_add_left (Nat.mod_lt _ hA) _)
    (fun j => fixed j j.isLt)

def BatchLaw {A W : ℕ} (p : Plan A W W) : Prop :=
  ∀ {ι : Type} {s : ℕ} {cl : Paint} {m : Bool} {b : Bank (some (Src cl, bundle cl)) ι}
    {k h Z : ι → ℕ}, 0 < A → 0 < W →
    (∀ i, A*(h i*2)+s*2=k i*2) → ∀ v : ∀ i, Bits (k i*2) → ℂ,
    Small b.B h → Small b.B (fun i => 2^(k i*2)) →
    Knows m b.B (Src cl) (fun i => (k i,(bits (k i*2)).tape (v i))) h →
    Correct p → PlanCompiler.Executes b m cl h Z p →
    Able m b (Src cl) (bundle cl) (fun i => (k i,(bits (k i*2)).tape (v i)))
      (fun i => (bits (k i*2)).tape (WalshBridge.normalized (k i*2) (v i)))
      (fun i => 2^(k i*2)) (fun i => ((4^s ⌈/⌉ W) * p.calls) * Z i)

def LocalLeaves (A : ℕ) : Prop :=
  ∀ {ι : Type} {cl : Paint} {m : Bool} {b : Bank (some (Src cl, bundle cl)) ι}
    {h Z : ι → ℕ}, 0 < A → Small b.B h → Small b.B (fun i => PlanCompiler.volume A (h i)) →
    (∀ g, PlanCompiler.Executes b m cl h Z (Plan.xor (A:=A) g)) ∧
    (∀ q t v, PlanCompiler.Executes b m cl h Z (Plan.scale (A:=A) q t v))

lemma pair_volume (k : ℕ) : 2^(k*2) = 4^k := by
  rw [Nat.mul_comm k, pow_mul]; rfl

theorem assemble_body {cl : Paint} {m : Bool} {A W r : ℕ} {p : Plan A W W}
    (ha : 0 < A) (hw : 0 < W) (ok : Correct p)
    (pack : BatchLaw p) (leaves : LocalLeaves A) : Body cl m A W p.calls r := by
  apply body_of_large
  refine large_of_fixed ha (fun s _hs => ?_)
  let I := RCtx cl A r s
  let ix := fun i : I => i.1.1
  let b := (bank cl A r).comap ix
  let k := fun i : I => (ix i).d.1
  let h := fun i : I => next A r (k i)
  let Z := fun i : I => 4^((A-1)*h i) * (ix i).tau
  have dims (i : I) : A*h i+s=k i := by
    have hh := i.1.2
    have hs := i.2
    have e := Nat.mod_add_div (k i-r) A
    change r+A ≤ k i at hh
    change r+(k i-r)%A=s at hs
    change A*((k i-r)/A)+s=k i
    omega
  have dims2 (i : I) : A*(h i*2)+s*2=k i*2 := by
    rw [← Nat.mul_assoc, ← Nat.add_mul,dims]
  have sk : Small b.B k := small_width.reindex fun i : I => (ix i).d
  have sh : Small b.B h := sk.sub.div
  have bvol (i : I) : b.B i = 4^k i := rfl
  have sv : Small b.B (fun i => PlanCompiler.volume A (h i)) := (Small.self _).mono fun i => by
    rw [PlanCompiler.volume_eq,←pow_mul, bvol, ←pair_volume]
    apply Nat.pow_le_pow_right (by decide : 0<2)
    have e := dims2 i
    rw [show 2*A*h i=A*(h i*2) by ring]; omega
  have sv2 : Small b.B (fun i => 2^(k i*2)) := (Small.self _).mono fun i => (pair_volume _).le
  let x := fun i : I => source cl (ix i).d
  have readK : Knows m b.B (Src cl) x k := Can.first
  have know : Knows m b.B (Src cl) x h := (readK.minus (Can.wc r) sk).dvdW (Can.wc A) sk.sub
  obtain ⟨xor,scale⟩ := leaves (cl:=cl) (m:=m) (b:=b) (Z:=Z) ha sh sv
  have exec : PlanCompiler.Executes b m cl h Z p := PlanCompiler.compile ha sh sv xor scale
    (fun a => PlanCompiler.child_exec (C:=fun i => (ix i).tau) a sh sv
      (fun i => by rw [PlanCompiler.fibers_eq])
      (fun i v => (ix i).works v i.1.2)) p
  have res := pack (b:=b) ha hw dims2 (fun i => (ix i).d.2) sh sv2 know ok exec
  exact res.mono (fun i => (pair_volume _).le) (fun i => by
    change _ ≤ children A W p.calls r (k i) * (ix i).tau
    rw [children,show spare A r (k i) = s from i.2]
    simp [Z,h,Nat.mul_assoc])

end
end DFTSpeedrun.HalfKernel

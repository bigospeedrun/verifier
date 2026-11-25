import Submission.BinaryKernel.KernelBase
import Submission.BinaryKernel.SelectedPlan

namespace DFTSpeedrun.HalfKernel
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open HalfCost SelectedPlan
noncomputable section

private lemma budget_dom {A W σ r : ℕ} {z : ℝ} (ha : 0 < A) (hw : 0 < W)
    (hr : A ≤ r) (hz : 0 ≤ z)
    (hs : (σ:ℝ)/W * (1+(W:ℝ)/(4:ℝ)^r) < (A:ℝ)^z) :
    Dom (fun d : Job => volume d * envelope z (d.1*2))
      (fun d => budget A W σ r 2 (lt_of_lt_of_le ha hr) d.1) := by
  obtain ⟨C, hc⟩ := budget_bound (C:=2) ha hw hr hz hs
  refine ⟨⌈C⌉₊+1, fun d => ?_⟩
  have hexp : (1+(d.1:ℝ))^z ≤ (envelope z (d.1*2) : ℝ) := by
    refine (Real.rpow_le_rpow (by positivity) ?_ hz).trans (Nat.le_ceil _)
    push_cast; linarith [Nat.cast_nonneg (α:=ℝ) d.1]
  have comp : (budget A W σ r 2 (lt_of_lt_of_le ha hr) d.1 : ℝ) ≤
      (⌈C⌉₊ : ℝ) * ((4:ℝ)^d.1 * (envelope z (d.1*2) : ℝ)) := calc
    _ ≤ C * 4^d.1 * (1+(d.1:ℝ))^z := hc _
    _ ≤ (⌈C⌉₊ : ℝ) * 4^d.1 * (1+(d.1:ℝ))^z := by gcongr; exact Nat.le_ceil _
    _ ≤ (⌈C⌉₊ : ℝ) * 4^d.1 * (envelope z (d.1*2) : ℝ) := by gcongr
    _ = _ := by ring
  have natBound : budget A W σ r 2 (lt_of_lt_of_le ha hr) d.1 ≤
      ⌈C⌉₊ * (volume d * envelope z (d.1*2)) := by unfold volume; exact_mod_cast comp
  dsimp only; rw [Nat.succ_mul,Nat.mul_add]; omega

private theorem recast {a k : ℕ} (e : a=k) (v : Bits k → ℂ) :
    (bits a).tape (fun x => v (castB e x)) = (bits k).tape v ∧
    (bits a).tape (WalshBridge.normalized a (fun x => v (castB e x))) =
      (bits k).tape (WalshBridge.normalized k v) := by subst k; exact ⟨rfl,rfl⟩

theorem even_of_large.{u} {A W σ r : ℕ} {z : ℝ} (ha : 0 < A) (hw : 0 < W)
    (hr : A ≤ r) (hz : 0 ≤ z)
    (hs : (σ:ℝ)/W * (1+(W:ℝ)/(4:ℝ)^r) < (A:ℝ)^z)
    (large : ∀ cl m, LargeBody cl m A W σ r) : WalshBridge.EvenKernel.{u} z := by
  intro cl m ι k even v
  let h (i : ι) := k i/2
  have e (i : ι) : h i*2 = k i := by obtain ⟨n,hn⟩ := even i; dsimp [h]; omega
  let jobs (i : ι) : Job := ⟨h i,fun x => v i (castB (e i) x)⟩
  let x := fun i => givenBits cl (k i) (v i)
  let B := fun i => 2^k i
  have vol (i : ι) : volume (jobs i) = B i := by
    change 4^(h i) = 2^(k i)
    rw [←e i, Nat.mul_comm (h i) 2, pow_mul]; rfl
  have small : Small B (fun i => volume (jobs i)) := (Small.self B).mono fun i => (vol i).le
  have kernel := (((close_body (lt_of_lt_of_le ha hr) (body_of_large (large cl m))).weaken
    (budget_dom ha hw hr hz hs)).reindex jobs).ambient small
  have work := kernel.mono (W' := fun i => B i * envelope z (k i)) (fun i => by
    unfold jobs at *; rw [vol]; simp [e])
  have sh : Small B k := (Small.self B).mono fun i => Nat.lt_two_pow_self.le
  have count : Knows m B (simIn cl) x h := Can.first.wdiv (Can.wc 2) sh.div
  have prep : Has m B (simIn cl) (Src cl) x (fun i => source cl (jobs i)) :=
    (count.pair Can.second.snd).cy fun i => Prod.ext rfl (recast (e i) (v i)).1.symm
  exact ((prep.mono fun _ => Nat.zero_le _).then_do work).cy fun i => (recast (e i) (v i)).2

theorem selected_even.{u}
    (large : ∀ r, fixedPlan.arity ≤ r → ∀ cl m,
      LargeBody cl m fixedPlan.arity fixedPlan.rows fixedPlan.program.calls r) :
    WalshBridge.EvenKernel.{u} beta := by
  obtain ⟨r,hr,hs⟩ := exists_padding (ℓ:=4) (by decide) strict_call_rate
  have ha := fixedPlan_good.1
  have hw := fixedPlan_good.2.1
  exact even_of_large (by omega) (by omega) hr (by linarith [half_lt_beta]) hs (large r hr)
end
end DFTSpeedrun.HalfKernel

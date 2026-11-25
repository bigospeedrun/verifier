import Submission.BinaryKernel.Recurrence
import Submission.BinaryKernel.EvenWalsh

/-! Close a charged recursive RAM body with a single program independent of
the input width and data. Only the width of a subproblem determines its time
allowance. The oracle specification covers every possible subarray at that
width. The induction uses the depth interpreter of the Big O verifier. -/
namespace DFTSpeedrun.HalfKernel
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty DFTSpeedrun.HalfCost
noncomputable section

abbrev Job := Σ k : ℕ, Bits (k*2) → ℂ
abbrev Src (cl : Paint) := p w (bundle cl)
def source (cl : Paint) (d : Job) : T (Src cl) := (d.1,(bits (d.1*2)).tape d.2)
def answer (cl : Paint) (d : Job) : T (bundle cl) :=
  (bits (d.1*2)).tape (WalshBridge.normalized (d.1*2) d.2)
def volume (d : Job) : ℕ := 4^d.1

structure Ctx (cl : Paint) (A r : ℕ) where
  d : Job
  use : Handler (some (Src cl, bundle cl))
  tau : ℕ
  peak : ℕ
  works : ∀ v, r+A ≤ d.1 →
    (use (source cl ⟨next A r d.1,v⟩)).OK (answer cl ⟨next A r d.1,v⟩) tau peak

def bank (cl : Paint) (A r : ℕ) : Bank (some (Src cl, bundle cl)) (Ctx cl A r) :=
  ⟨fun g => volume g.d, Ctx.peak, Ctx.use⟩

def charge (A W σ r k tau : ℕ) :=
  if r+A ≤ k then children A W σ r k * tau else 0

abbrev Body (cl : Paint) (m : Bool) (A W σ r : ℕ) :=
  Able m (bank cl A r) (Src cl) (bundle cl) (fun g => source cl g.d)
    (fun g => answer cl g.d) (fun g => volume g.d) (fun g => charge A W σ r g.d.1 g.tau)

lemma volume_pos (d : Job) : 0 < volume d := by unfold volume; positivity
lemma small_width : Small volume (fun d : Job => d.1) :=
  (Small.self volume).mono fun d => (Nat.lt_pow_self (by decide : 1 < 4) (n := d.1)).le

theorem close_body {cl : Paint} {m : Bool} {A W σ r : ℕ} (hr : 0 < r)
    (job_body : Body cl m A W σ r) :
    Can m volume (Src cl) (bundle cl) (source cl) (answer cl)
      (fun d => budget A W σ r 2 hr d.1) := by
  obtain ⟨body,K,deg,hbody⟩ := job_body
  let base : Prog m (Src cl) (bundle cl) := Code.blank _ _
  let run := depthRun (base.run ()) body.run
  let Q (d : Job) := (volume d+2)^(deg+1)
  let cost (k : ℕ) := budget A W σ r 2 hr k
  have split (d : Job) : cost d.1 = 2*volume d + charge A W σ r d.1 (cost (next A r d.1)) := by
    unfold cost volume charge
    rw [budget]
  have scale (k M t : ℕ) : charge A W σ r k (M*t) = M*charge A W σ r k t := by
    unfold charge
    split <;> ring
  have key : ∀ n (d : Job), d.1 < n →
      (run n (source cl d)).OK (answer cl d) ((K+1)*cost d.1) (max (Q d) n) := by
    intro n
    induction n with
    | zero => intro d h; omega
    | succ n ih =>
      intro d hn
      let f := next A r d.1
      have smaller (h : r+A ≤ d.1) : f < d.1 := by
        dsimp [f,next]
        have := Nat.div_le_self (d.1-r) A
        omega
      let g : Ctx cl A r :=
        { d := d, use := run n, tau := (K+1)*cost f, peak := max (Q d) (n+1)
          works := fun v h => (ih ⟨f,v⟩ (lt_of_lt_of_le (smaller h) (Nat.le_of_lt_succ hn))).mono le_rfl
            (max_le_max (Nat.pow_le_pow_left (Nat.add_le_add_right
              (Nat.pow_le_pow_right (by decide : 0 < 4) (smaller h).le) 2) _) (Nat.le_succ n)) }
      have cap : (bank cl A r).cap deg g ≤ max (Q d) (n+1) :=
        max_le (le_max_of_le_left (Nat.pow_le_pow_right (by omega) (Nat.le_succ deg))) le_rfl
      have step := ((hbody g).mono le_rfl cap).pay (t:=1) (le_max_right (Q d) (n+1))
      refine step.mono ?_ le_rfl
      change K*(volume d+1)+charge A W σ r d.1 ((K+1)*cost f)+1 ≤ (K+1)*cost d.1
      rw [scale,split d]
      have hv := volume_pos d
      nlinarith [Nat.mul_le_mul_left K hv]
  let outerSrc := fun d : Job => (d.1+1,source cl d)
  have outer : Can m volume (p w (Src cl)) (bundle cl) outerSrc (answer cl) (fun d => cost d.1) := by
    refine ⟨.descend base body,K+2,deg+2,fun d => ?_⟩
    have hd := (key (d.1+1) d (Nat.lt_succ_self _)).pay (t:=1) (le_max_right (Q d) (d.1+1))
    refine hd.mono ?_ ?_
    · change (K+1)*cost d.1+1 ≤ (K+2)*(cost d.1+1)+0
      nlinarith
    · have h1 := Nat.lt_pow_self (by decide : 1 < 4) (n := d.1)
      refine le_max_of_le_left (max_le (Nat.pow_le_pow_right (by omega) (by omega)) ?_)
      calc d.1+1 ≤ volume d+2 := by unfold volume; omega
           _ = (volume d+2)^1 := by simp
           _ ≤ (volume d+2)^(deg+2) := Nat.pow_le_pow_right (by omega) (by omega)
  have fuel : Knows m volume (Src cl) (source cl) (fun d => d.1+1) :=
    (Can.first (v:=source cl)).plus (Can.wc 1) small_width (Small.const _ 1)
  exact ((fuel.mono fun _ => Nat.zero_le _).pair Can.id).then_do outer

end
end DFTSpeedrun.HalfKernel

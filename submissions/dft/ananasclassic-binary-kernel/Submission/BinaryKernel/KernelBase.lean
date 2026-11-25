import Submission.BinaryKernel.KernelClosure

namespace DFTSpeedrun.HalfKernel
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM
open OAI.PowerSaving.RAM.Ty DFTSpeedrun.HalfCost Finset
noncomputable section

private def entry (k : ℕ) (x y : Bits (k*2)) : ℚ :=
  (∏ i, if x i * y i = 0 then (1:ℚ) else -1) / 2^k

private lemma entry_cast (k : ℕ) (x y : Bits (k*2)) :
    (entry k x y : ℂ) = wal (Fin (k*2)) x y / (2:ℂ)^k := by
  simp [entry, wal, digitProd_apply, littleH, sign, apply_ite (fun z : ℚ => (z : ℂ))]

theorem fixed_base (cl : Paint) (m : Bool) (k : ℕ) :
    Can m (fun _ : Bits (k*2) → ℂ => 4^k) (Src cl) (bundle cl)
      (fun v => source cl ⟨k,v⟩) (fun v => answer cl ⟨k,v⟩) (fun _ => 4^k) := by
  let L := bits (k*2)
  let src := fun v : Bits (k*2) → ℂ => source cl ⟨k,v⟩
  let y := fun (v : Bits (k*2) → ℂ) (x : Bits (k*2)) => ∑ j, (entry k x j : ℂ)*v j
  have cell : Can m (fun _ : Σ _ : Bits (k*2) → ℂ, Bits (k*2) => 4^k)
      (p (Src cl) w) (c cl) (fun d => (src d.1,L.loc d.2)) (fun d => y d.1 d.2) (fun _ => 0) := by
    refine Can.cases_code L (q := fun d => d.2) Can.second (fun x => ?_)
    refine (Can.sum_cconst (v := fun j d => (entry k x j : ℂ)*d.1.1 j)
      (fun j => (Can.rat (entry k x j)).mul ?_)).cy (fun d => by rw [d.2])
    let ix := {d : Σ _ : Bits (k*2) → ℂ, Bits (k*2) // d.2 = x}
    exact Can.fetch (t:=c cl) (L:=fun _ : ix => L) (i:=fun _ => j) (v:=fun d : ix => d.1.1)
      Can.first.snd (Can.wc (L.loc j))
  have full := Can.layout (m:=m) (B:=fun _ => 4^k) (x:=src) (t:=c cl) (L:=fun _ => L) (v:=y) (P:=fun _ => 0)
    (Can.wc (W:=fun _ => 0) L.n) cell (Small.const _ L.n)
  refine (full.weaken (Dom.const _ _)).cy (fun v => congrArg L.tape (funext fun x => ?_))
  change (∑ j, (entry k x j : ℂ)*v j) = WalshBridge.normalized (k*2) v x
  simp only [entry_cast, WalshBridge.normalized, WalshBridge.walsh, Matrix.mulVec,
    dotProduct, Nat.mul_div_cancel _ (by decide : 0 < 2), Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ => by ring

private lemma transport {a b : ℕ} (e : a=b) (v : Bits (a*2) → ℂ) :
    (e ▸ v : Bits (b*2) → ℂ) ≍ v := by cases e; rfl

theorem dense_base {cl : Paint} {m : Bool} {ι : Type*} {N : ℕ} (d : ι → Job)
    (bound : ∀ i, (d i).1 < N) :
    Can m (fun i => volume (d i)) (Src cl) (bundle cl) (fun i => source cl (d i))
      (fun i => answer cl (d i)) (fun i => volume (d i)) := by
  let q (i : ι) : Fin N := ⟨(d i).1,bound i⟩
  refine Can.cases_code (Layout.std N) (q:=q) Can.first (fun k => ?_)
  let ix := {i // q i = k}
  have eq (i : ix) : (d i.1).1 = k.val := congrArg Fin.val i.2
  let v (i : ix) : Bits (k.val*2) → ℂ := (eq i) ▸ (d i.1).2
  have same (i : ix) : (⟨k.val,v i⟩ : Job) = d i.1 := by
    apply Sigma.ext (eq i).symm
    dsimp [v]
    exact transport (eq i) (d i.1).2
  obtain ⟨f,K,e,h⟩ := fixed_base cl m k.val
  exact ⟨f,K,e,fun i => by
    have hi := h (v i)
    change (f.run () (source cl ⟨k.val,v i⟩)).OK (answer cl ⟨k.val,v i⟩)
      (K*(volume ⟨k.val,v i⟩+1)+0) (max ((volume ⟨k.val,v i⟩+2)^e) 0) at hi
    rwa [same i] at hi⟩

abbrev LargeBody (cl : Paint) (m : Bool) (A W σ r : ℕ) :=
  let embed := fun g : {g : Ctx cl A r // r+A ≤ g.d.1} => g.val
  Able m ((bank cl A r).comap embed) (Src cl) (bundle cl)
    (fun i => source cl i.1.d) (fun i => answer cl i.1.d) (fun i => volume i.1.d)
    (fun i => children A W σ r i.1.d.1 * i.1.tau)

theorem body_of_large {cl : Paint} {m : Bool} {A W σ r : ℕ}
    (large : LargeBody cl m A W σ r) : Body cl m A W σ r := by
  let b := bank cl A r
  let test (g : Ctx cl A r) : ℕ := if g.d.1 < r+A then 1 else 0
  have decideLarge : Knows m b.B (Src cl) (fun g => source cl g.d) test :=
    Can.first.wlt (Can.wc (r+A))
  apply Able.mono (Able.ifz (W:=fun g => volume g.d) (Z:=fun g => charge A W σ r g.d.1 g.tau)
    (Able.of_can (b:=b) decideLarge) ?_ ?_) (fun _ => by simp) (fun _ => by simp)
  · let conv (g : {g // test g = 0}) : {g : Ctx cl A r // r+A ≤ g.d.1} :=
      ⟨g.1,by simpa [test] using g.2⟩
    exact (large.reindex conv).mono (fun _ => le_rfl) (fun i => by simp [charge,(conv i).2,conv])
  · let jobs (g : {g // test g ≠ 0}) := g.1.d
    have h (g : {g // test g ≠ 0}) : (jobs g).1 < r+A := by simpa [jobs,test] using g.2
    exact (Able.of_can (b:=b.comap Subtype.val) (dense_base (cl:=cl) (m:=m) jobs h)).mono
      (fun _ => le_rfl) (fun _ => Nat.zero_le _)

end
end DFTSpeedrun.HalfKernel

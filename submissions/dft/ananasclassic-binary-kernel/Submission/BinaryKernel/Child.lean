import Submission.BinaryKernel.PlanCompiler

namespace DFTSpeedrun.PlanCompiler
open OAI.PowerSaving OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty OAI.PowerSaving.Binary
open OAI.Computability.NearSquareRoot.KernelPass
open FixedRows AxisLayout RAM.HalfFibers
noncomputable section
universe u

def fibers (A h : ℕ) := (width h)^(A-1)

theorem fibers_eq (A h : ℕ) : fibers A h = 4^((A-1)*h) := by
  unfold fibers width
  rw [show h*2=2*h by omega, pow_mul, ←pow_mul, Nat.mul_comm h]
  rfl

theorem vol_eq_width (A h : ℕ) : volume A h = (width h)^A := by
  change ((bits (h*2)).n)^A=_
  rw [bits_len]; rfl

theorem fibers_mul {A : ℕ} (ha : 0 < A) (h : ℕ) : fibers A h * width h = volume A h := by
  rw [vol_eq_width, fibers, ←pow_succ, Nat.sub_add_cancel ha]

private theorem fiber_bound {A h} (a : Fin A) (y : Addr A h) :
    fiberAt (stride a h) (width h) (code y) < fibers A h := by
  let d := width h
  let s := stride a h
  let q := d^(A-1-a.val)
  have sd : 0 < s := by dsimp [s,stride,width]; positivity
  have dw : 0 < d := by dsimp [d,width]; positivity
  have qs : q*s = fibers A h := by
    change d^(A-1-a.val)*d^a.val=d^(A-1)
    rw [←pow_add]; congr 1; omega
  have sz : q*(s*d) = volume A h := by rw [←Nat.mul_assoc,qs,fibers_mul (Nat.zero_lt_of_lt a.isLt)]
  have bound : code y < q*(s*d) := sz ▸ (shape A h).bd y
  have hi : code y / s / d < q := by
    rw [Nat.div_div_eq_div_mul]; exact (Nat.div_lt_iff_lt_mul (Nat.mul_pos sd dw)).2 bound
  rw [←qs]
  exact DigitArith.lt_join hi (Nat.mod_lt _ sd)

def fiberInput {A h} (a : Fin A) (f : Addr A h → ℂ) (j : ℕ) (v : Bits (h*2)) :=
  ((shape A h).tape f).look (insertAxis (stride a h) (width h) j ((bits (h*2)).loc v)) 0

private theorem pack_eq {A h} (cl : Paint) (a : Fin A) (f : Addr A h → ℂ) (j : ℕ) :
    HalfFibers.row (t:=c cl) ((shape A h).tape f) (stride a h) (width h) j =
    (bits (h*2)).tape (fiberInput a f j) := by
  refine (bits (h*2)).verify _ 0 _ ?_ fun v => ?_
  · exact (bits_len _).symm
  · have hv := (bits (h*2)).bd v
    rw [bits_len] at hv
    simp [HalfFibers.row,Tape.look_tab, width, hv, fiberInput, Ty.blank]

private theorem scatter_eq {A h} (cl : Paint) (a : Fin A) (X : ComplexPlan.Bank A h 1) :
    scatter (t:=c cl) (stride a h) (width h) (fibers A h * width h)
      (Tape.tab (fibers A h) fun j => (bits (h*2)).tape (WalshBridge.normalized (h*2) (fiberInput a (X 0) j))) =
      (shape A h).tape (ComplexPlan.act (Plan.child a) h X 0) := by
  refine (shape A h).verify _ 0 _ (fibers_mul (Nat.zero_lt_of_lt a.isLt) h) fun y => ?_
  change (scatter (t:=c cl) _ _ _ _).look (code y) _ = _
  have hy : code y < fibers A h * width h := (fibers_mul (Nat.zero_lt_of_lt a.isLt) h) ▸ (shape A h).bd y
  rw [scatter,Tape.look_tab, if_pos hy, Tape.look_tab, if_pos (fiber_bound a y),digit_extract]
  change ((bits (h*2)).tape _).look ((bits (h*2)).loc _) _ = _
  rw [Layout.read,child_normalized]
  congr 1
  funext v
  unfold fiberInput
  rw [←show digit (flatten.symm v) = (bits (h*2)).loc v by simp [digit],←code_setAxis]
  exact Layout.read _ _ _ _

private def base (A : ℕ) := (4:ℕ)^A

theorem child_exec {ι : Type u} {A} {cl : Paint} {m}
    {b : RAM.Bank (some (p w (bundle cl),bundle cl)) ι} {h C Z : ι → ℕ}
    (a : Fin A) (sh : Small b.B h) (sv : Small b.B fun i => volume A (h i))
    (bill : ∀ i, fibers A (h i) * C i ≤ Z i)
    (oracle : ∀ i (v : Bits (h i * 2) → ℂ),
      (b.use i (h i,(bits _).tape v)).OK ((bits _).tape (WalshBridge.normalized _ v)) (C i) (b.ext i)) :
    Executes b m cl h Z (Plan.child a) := by
  intro X
  let src := fun i => (h i,source h X i)
  let srcTy := p w (Ty.a (bundle cl))
  have ha : 0 < A := Nat.zero_lt_of_lt a.isLt
  have dimE (k H : ℕ) : (width H)^k = (base k)^H := by
    unfold width base; rw [show H*2=2*H by omega, pow_mul, show (2:ℕ)^2=4 by decide, ←pow_mul,←pow_mul,Nat.mul_comm H]
  have dimS (k : ℕ) (hk : k ≤ A) : Small b.B fun i => (width (h i))^k :=
    sv.mono fun i => (Nat.pow_le_pow_right (by dsimp [width]; positivity) hk).trans (vol_eq_width A _).ge
  have dim (k : ℕ) (hk : k ≤ A) :
      Can m b.B srcTy w src (fun i => (width (h i))^k) (fun i => h i + 1) := by
    have sm := (dimS k hk).mono (fun i => (dimE k (h i)).ge)
    exact (can_powv (base k) (by dsimp [base]; positivity) Can.first sh sm).cy fun i => (dimE k (h i)).symm
  have dims := ((dim a.val a.isLt.le).pair ((dim 1 ha).cy (fun i => pow_one _))).pair (dim (A-1) (by omega))
  let env := fun i => (src i, ((stride a (h i),width (h i)),fibers A (h i)))
  let envTy := p srcTy (p (p w w) w)
  have row0 : Has m b.B envTy (bundle cl) env (fun i => (shape A (h i)).tape (X i 0)) :=
    FixedRows.row (t:=bundle cl) (V:=fun i j => (shape A (h i)).tape (X i j)) Can.first.snd 0
  have run := runAxis (t:=c cl) (b:=b) (s:=envTy) (x:=env) (cost:=fun i _ => C i)
    row0 Can.second.fst.fst Can.second.fst.snd Can.second.snd Can.first.fst
    (dimS a.val a.isLt.le) ((dimS 1 ha).mono fun i => (pow_one _).ge)
    (dimS (A-1) (by omega)) (fun i => by change 0 < 2^(h i*2); positivity)
    (fun i j _ => by rw [pack_eq]; exact oracle i _)
  have ret := run.cong (fun _ => rfl) (fun i => scatter_eq cl a (X i))
  have singleton : Has m b.B (bundle cl) (Ty.a (bundle cl))
      (fun i => (shape A (h i)).tape (ComplexPlan.act (.child a) _ (X i) 0))
      (source h fun i => ComplexPlan.act (.child a) _ (X i)) := by
    apply FixedRows.assemble; intro j; fin_cases j; exact Can.id
  refine ((Able.of_can dims).save (ret.comp (Able.of_can singleton))).weaken ?_ ?_
  · refine ⟨3,fun i => ?_⟩
    have hle : h i ≤ volume A (h i) := by
      rw [volume_eq]; exact (Nat.lt_pow_self (Nat.one_lt_two_pow (by omega)) (n := h i)).le
    simp only [env, fibers_mul ha, Nat.add_zero]; omega
  · intro i
    simpa [Plan.calls] using bill i
end
end DFTSpeedrun.PlanCompiler

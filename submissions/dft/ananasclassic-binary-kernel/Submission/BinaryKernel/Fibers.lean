import Submission.Engine.ClassSetup

/-! A child transform on a contiguous binary axis. Other axes are flattened into
a fiber number. Only integer multiplication, division and remainder are used;
the input and output passes charge one operation budget per array cell. -/
namespace OAI.PowerSaving.RAM.HalfFibers
open Ty Finset
noncomputable section

def insertAxis (stride width fiber digit : ℕ) : ℕ :=
  ((fiber / stride) * width + digit) * stride + fiber % stride

def fiberAt (stride width j : ℕ) : ℕ :=
  (j / stride / width) * stride + j % stride

def digitAt (stride width j : ℕ) : ℕ := j / stride % width

private theorem split_digits (q r b : ℕ) (hr : r < b) :
    (q*b+r)/b=q ∧ (q*b+r)%b=r := by
  rw [Nat.add_comm (q*b) r, Nat.add_mul_div_right _ _ (by omega : 0 < b), Nat.div_eq_of_lt hr,
      Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  exact ⟨rfl,rfl⟩

theorem insert_recover (stride width j : ℕ) :
    insertAxis stride width (fiberAt stride width j) (digitAt stride width j) = j := by
  by_cases hs : stride=0
  · simp [hs, insertAxis, fiberAt, digitAt]
  have hs' : 0 < stride := Nat.pos_of_ne_zero hs
  unfold insertAxis fiberAt digitAt
  have e := split_digits (j/stride/width) (j%stride) stride (Nat.mod_lt _ hs')
  rw [e.1, e.2, Nat.div_add_mod', Nat.div_add_mod']

theorem recover_insert {stride width digit : ℕ} (hs : 0 < stride) (hd : digit < width)
    (fiber : ℕ) :
    fiberAt stride width (insertAxis stride width fiber digit) = fiber ∧
    digitAt stride width (insertAxis stride width fiber digit) = digit := by
  unfold fiberAt digitAt insertAxis
  have e := split_digits ((fiber/stride)*width+digit) (fiber%stride) stride (Nat.mod_lt _ hs)
  have d := split_digits (fiber/stride) digit width hd
  rw [e.1, e.2, d.1, d.2, Nat.div_add_mod']
  exact ⟨rfl,rfl⟩

universe u
variable {ι : Type u} {m : Bool} {s : Ty} {B : ι → ℕ}
  {x : ι → T s} {S D F J N : ι → ℕ}

lemma addr (hS : Knows m B s x S) (hD : Knows m B s x D)
    (hF : Knows m B s x F) (hJ : Knows m B s x J)
    (sS : Small B S) (sD : Small B D) (sF : Small B F) (sJ : Small B J) :
    Knows m B s x (fun i => insertAxis (S i) (D i) (F i) (J i)) := by
  have hi := (hF.wdiv hS sF.div).wmul hD (sF.div.mul sD)
  have hj := hi.wadd hJ ((sF.div.mul sD).add sJ)
  have hk := hj.wmul hS (((sF.div.mul sD).add sJ).mul sS)
  exact hk.wadd (hF.wmod hS sF.mod) ((((sF.div.mul sD).add sJ).mul sS).add sF.mod)

def row {t : Ty} (a : Tape (T t)) (stride width fiber : ℕ) :=
  Tape.tab width fun j => a.look (insertAxis stride width fiber j) t.blank

theorem packRow {t : Ty} {a : ι → Tape (T t)}
    (ha : Has m B s (.a t) x a) (hS : Knows m B s x S) (hD : Knows m B s x D)
    (hF : Knows m B s x F) (sS : Small B S) (sD : Small B D) (sF : Small B F) :
    Can m B s (.a t) x (fun i => row (t:=t) (a i) (S i) (D i) (F i)) D := by
  let ix : During D → ι := During.i
  have atCell := addr (Has.extE (hS.reindex ix)) (Has.extE (hD.reindex ix))
    (Has.extE (hF.reindex ix)) (Can.second (v:=fun d : During D => (x d.i, d.j)))
    (sS.reindex ix) (sD.reindex ix) (sF.reindex ix) sD.during
  exact (Can.tab (uB := fun _ _ => 0) hD ((Has.extE (ha.reindex ix)).look atCell) sD).mono
    fun i => by simp

private lemma extractFiber (hS : Knows m B s x S) (hD : Knows m B s x D)
    (hj : Knows m B s x J) (sS : Small B S) (sJ : Small B J) :
    Knows m B s x (fun i => fiberAt (S i) (D i) (J i)) :=
  (((hj.wdiv hS sJ.div).wdiv hD sJ.div.div).wmul hS (sJ.div.div.mul sS)).wadd
    (hj.wmod hS sJ.mod) ((sJ.div.div.mul sS).add sJ.mod)

def scatter {t : Ty} (stride width n : ℕ) (v : Tape (Tape (T t))) :=
  Tape.tab n fun j => (v.look (fiberAt stride width j) (Tape.empty _)).look (digitAt stride width j) t.blank

theorem unpack {t : Ty} {v : ι → Tape (Tape (T t))}
    (hv : Has m B s (.a (.a t)) x v) (hS : Knows m B s x S) (hD : Knows m B s x D)
    (hn : Knows m B s x N) (sS : Small B S) (sn : Small B N) :
    Can m B s (.a t) x (fun i => scatter (t:=t) (S i) (D i) (N i) (v i)) N := by
  let ix : During N → ι := During.i
  have hj : Knows m (fun d : During N => B d.i) (.p s .w) (fun d => (x d.i,d.j)) During.j := Can.second
  have hs : Knows m (fun d : During N => B d.i) (.p s .w) (fun d => (x d.i,d.j)) (fun d => S d.i) := Has.extE (hS.reindex ix)
  have hd : Knows m (fun d : During N => B d.i) (.p s .w) (fun d => (x d.i,d.j)) (fun d => D d.i) := Has.extE (hD.reindex ix)
  have hidx := extractFiber hs hd hj (sS.reindex ix) sn.during
  have hbit := (hj.wdiv hs sn.during.div).wmod hd sn.during.div.mod
  exact (Can.tab (uB:=fun _ _ => 0) hn (((Has.extE (hv.reindex ix)).look hidx).look hbit) sn).mono
    fun i => by simp

/-- Apply the recursive port once per fiber; the recursive budgets have coefficient one. -/
theorem runAxis {t : Ty} {b : Bank (some (.p .w (.a t), .a t)) ι}
    {a : ι → Tape (T t)} {arg : ι → ℕ} {ys : ι → ℕ → Tape (T t)}
    {cost : ι → ℕ → ℕ}
    (ha : Has m b.B s (.a t) x a)
    (hS : Knows m b.B s x S) (hD : Knows m b.B s x D) (hF : Knows m b.B s x F)
    (hArg : Knows m b.B s x arg)
    (sS : Small b.B S) (sD : Small b.B D) (sF : Small b.B F)
    (hd : ∀ i, 0 < D i)
    (ok : ∀ i j, j < F i →
      (b.use i (arg i, row (t:=t) (a i) (S i) (D i) j)).OK (ys i j) (cost i j) (b.ext i)) :
    Able m b s (.a t) x
      (fun i => scatter (t:=t) (S i) (D i) (F i * D i) (Tape.tab (F i) (ys i)))
      (fun i => F i * D i) (fun i => ∑ j ∈ range (F i), cost i j) := by
  let ix : During F → ι := During.i
  have hrow := packRow (Has.extE (ha.reindex ix)) (Has.extE (hS.reindex ix))
    (Has.extE (hD.reindex ix)) (Can.second (v:=fun d : During F => (x d.i,d.j)))
    (sS.reindex ix) (sD.reindex ix) sF.during
  have prep := ((Has.atW (W:=fun d : During F => D d.i) (Has.extE (hArg.reindex ix))).pair hrow)
  have port : Able m (b.comap ix) (.p .w (.a t)) (.a t)
      (fun d : During F => (arg d.i, row (t:=t) (a d.i) (S d.i) (D d.i) d.j))
      (fun d => ys d.i d.j) (fun _ => 0) (fun d => cost d.i d.j) :=
    Able.use_call fun d => ok d.i d.j d.hj
  have each := (Able.of_can (b:=b.comap ix) prep).comp port
  have rows := Able.tab (Wb := fun i _ => D i) (Zb := cost) (Able.of_can hF)
    (each.mono (fun _ => by simp) (fun _ => by simp)) sF
  have finish := unpack (x := fun i => (x i, Tape.tab (F i) (ys i))) (t:=t)
    (Can.second) (Has.extE hS) (Has.extE hD) (Has.extE (hF.wmul hD (sF.mul sD))) sS (sF.mul sD)
  refine (rows.save (Able.of_can finish)).weaken ⟨3, fun i => ?_⟩ (fun _ => by simp)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.zero_add]
  have := Nat.le_mul_of_pos_right (F i) (hd i)
  simp only [Nat.cast_id] at *
  omega

end
end OAI.PowerSaving.RAM.HalfFibers

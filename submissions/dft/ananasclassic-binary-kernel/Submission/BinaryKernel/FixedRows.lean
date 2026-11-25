import Submission.Engine.ClassSetup

/-! Compilation of fixed banks of rows. Row references are shared. Only
a linear combination materializes the cell values on the full address space. -/
namespace OAI.PowerSaving.FixedRows
open RAM RAM.Ty Binary Matrix Finset
noncomputable section
universe u v
variable {m : Bool} {s t : Ty} {ι : Type u} {B W : ι → ℕ} {x : ι → T s}
variable {n r : ℕ}

def fixed {n : ℕ} {β : Type*} (f : Fin n → β) := (Layout.std n).tape f

lemma assemble {V : ι → Fin n → T t}
    (h : ∀ b, Can m B s t x (fun i => V i b) W) :
    Can m B s (a t) x (fun i => fixed (V i)) W := by
  have one : Can m B s (a t) x (fun i => fixed (V i)) (fun i => 0+n+n*W i) := by
    refine Can.layout (L := fun _ => Layout.std n) (P := W) (Can.wc n) ?_ (Small.const B n)
    refine Can.cases_code (Layout.std n) (q := fun d : Σ _ : ι, Fin n => d.2) Can.second fun b => ?_
    exact (Can.first.then_do ((h b).reindex (fun d : {d : Σ _ : ι, Fin n // d.2=b} => d.1.1))).cy
      (fun d => by simp [d.2])
  exact one.weaken ⟨n+1, fun i => by simp; nlinarith⟩

lemma row {V : ι → Fin n → T t} (h : Can m B s (a t) x (fun i => fixed (V i)) W) (j : Fin n) :
    Can m B s t x (fun i => V i j) W :=
  Can.fetch (L := fun _ => Layout.std n) (i := fun _ => j) h (Can.wc j)

lemma select {V : ι → Fin n → T t} (g : Fin r → Fin n)
    (h : Can m B s (a t) x (fun i => fixed (V i)) W) :
    Can m B s (a t) x (fun i => fixed fun b => V i (g b)) W :=
  assemble fun b => row h (g b)

lemma append {V : ι → Fin n → T t} {Y : ι → Fin r → T t}
    (h : Can m B s (a t) x (fun i => fixed (V i)) W)
    (g : Can m B s (a t) x (fun i => fixed (Y i)) W) :
    Can m B s (a t) x (fun i => fixed (Fin.append (V i) (Y i))) W := by
  apply assemble
  intro b
  refine Fin.addCases (motive := fun j => Can m B s t x (fun i => Fin.append (V i) (Y i) j) W) ?_ ?_ b
  · intro j; simpa using row h j
  · intro j; simpa using row g j

variable {α : ι → Type v} {L : ∀ i, Layout (α i)} {cl : Paint}
def bankTape {α : Type*} (L : Layout α) {n : ℕ} (f : Fin n → α → ℂ) :=
  fixed fun b => L.tape (f b)

lemma mix {V : ∀ i, Fin n → α i → ℂ} (M : Fin r → Fin n → ℚ)
    (h : Has m B s (Ty.a (bundle cl)) x (fun i => bankTape (L i) (V i)))
    (hd : Knows m B s x fun i => (L i).n) (hs : Small B fun i => (L i).n) :
    Can m B s (Ty.a (bundle cl)) x
      (fun i => bankTape (L i) (fun b y => ∑ a, (M b a : ℂ)*V i a y))
      (fun i => (L i).n) := by
  apply assemble
  intro b
  refine Can.mono (Can.layout (L := L) (P := fun _ => 0) hd ?_ hs) (fun i => by simp)
  refine Can.sum_cconst fun a : Fin n => (Can.rat (M b a)).mul ?_
  exact Can.fetch (t := c cl) (L := fun d : Σ i, α i => L d.1) (i := fun d => d.2)
    (v := fun d => V d.1 a) (Can.first.then_do ((row (t := bundle cl) h a).reindex Sigma.fst))
    Can.second

/-- Bank execution retains one integer parameter (the column count). The
last budget is a literal oracle charge; it may never be multiplied by a
constant when composing two plans. -/
abbrev Run {port : Port} (b : Bank port ι) (m : Bool) (cl : Paint)
    (col W Z : ι → ℕ) (input output : ι → Tape (Tape ℂ)) :=
  Able m b (p w (Ty.a (bundle cl))) (Ty.a (bundle cl)) (fun i => (col i,input i)) output W Z

variable {port : Port} {b : Bank port ι} {col cost z₁ z₂ : ι → ℕ}
variable {input middle output : ι → Tape (Tape ℂ)}

theorem seq (f : Run b m cl col cost z₁ input middle)
    (g : Run b m cl col cost z₂ middle output) :
    Run b m cl col cost (fun i => z₁ i + z₂ i) input output := by
  have prep : Able m b (p w (Ty.a (bundle cl))) (p w (Ty.a (bundle cl)))
      (fun i => (col i,input i)) (fun i => (col i,middle i)) cost z₁ :=
    ((Able.first (W := fun _ => 0) (Z := fun _ => 0)).fork f).weaken
      (Dom.of_le fun _ => by simp) fun _ => by simp
  exact (prep.comp g).weaken (Dom.two cost) fun _ => le_rfl

/-- Split and rejoin fixed row banks with pointer lookups. Both independent
recursive bills remain explicit in the result. -/
theorem parallel {a c d e : ℕ} {X : ι → Fin a → Tape ℂ} {Y : ι → Fin c → Tape ℂ}
    {U : ι → Fin d → Tape ℂ} {V : ι → Fin e → Tape ℂ}
    (f : Run b m cl col cost z₁ (fun i => fixed (X i)) (fun i => fixed (U i)))
    (g : Run b m cl col cost z₂ (fun i => fixed (Y i)) (fun i => fixed (V i))) :
    Run b m cl col cost (fun i => z₁ i+z₂ i)
      (fun i => fixed (Fin.append (X i) (Y i))) (fun i => fixed (Fin.append (U i) (V i))) := by
  let srcTy := p w (Ty.a (bundle cl))
  let src := fun i => (col i, fixed (Fin.append (X i) (Y i)))
  have l : Has m b.B srcTy srcTy src (fun i => (col i,fixed (X i))) :=
    Can.first.pair ((select (t := bundle cl) (fun j : Fin a => Fin.castAdd c j)
      (V := fun i => Fin.append (X i) (Y i)) Can.second).cy fun i => by simp)
  have r' : Has m b.B srcTy srcTy src (fun i => (col i,fixed (Y i))) :=
    Can.first.pair ((select (t := bundle cl) (fun j : Fin c => Fin.natAdd a j)
      (V := fun i => Fin.append (X i) (Y i)) Can.second).cy fun i => by simp)
  have left := (Able.of_can l).comp f
  have right := (Able.of_can r').comp g
  have join : Has m b.B (p (Ty.a (bundle cl)) (Ty.a (bundle cl))) (Ty.a (bundle cl))
      (fun i => (fixed (U i),fixed (V i))) (fun i => fixed (Fin.append (U i) (V i))) :=
    append Can.first Can.second
  refine (((left.fork right).comp (Able.of_can join)).weaken ?_ fun i => ?_)
  · exact ⟨2, fun i => by simp; omega⟩
  · simp

end
end OAI.PowerSaving.FixedRows

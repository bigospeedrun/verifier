import Submission.OAI.Computability.FourierTransform.AddressTables

/-! Merged module written by bos_merge.py for the 500-file limit of the Big O Speedrun
pull-request route.  It is the concatenation, in import order, of the 5 modules below; each one
is copied verbatim after its import header, inside `section` ... `end`, with the scopes it leaves
open closed before that `end`.  Members (module, sha256 of the original file):
* `Submission.OAI.Computability.FourierTransform.ColumnAddresses` 84bee13f9889bee7dc5a446af57d292fe4c02112424a1f67aa636a1cc01754ce
* `Submission.OAI.Computability.FourierTransform.RoleArrays` ab753a631a58361be851e2e07170eae264a2bb9e3206094b33c5abc7fbb26b45
* `Submission.OAI.Computability.FourierTransform.RecursiveBatches` 52456e6d3ba415d68e0aab4e77266a2b2cbc085aff4aaf58d3d6e182db46750b
* `Submission.OAI.Computability.FourierTransform.RecursiveContract` 69893cf255c6668a5ac1a2629edfb702f825b9a8101df1552d7aa90ebd8bc3da
* `Submission.OAI.Computability.FourierTransform.TensorRecursion` fa925312e7bbaf04e0cfc8d21c4a64d03e327508047ae2c1eee16c266f71a03c
-/

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.ColumnAddresses
section

namespace OAI

/-! Constant (i.e. independent of f) work for transposed-column addresses. The number
of bits per COLUMN is fixed. Groups of f bits have prepared powers and XOR table. -/
namespace PowerSaving.RAM
open Binary Ty Finset
noncomputable section

universe U V
variable {ι : Type U}

/-- "Ready", i.e. can be computed in constant work, not free. -/
abbrev Has (m : Bool) (B : ι → ℕ) (s t : Ty) (x : ι → T s) (y : ι → T t) : Prop :=
  Can m B s t x y (fun _ => 0)
abbrev Knows (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (y : ι → ℕ) : Prop :=
  Has m B s w x y

/-- Particular indexing programs are proved uniformly over all f through this *finite*
  syntax interface. -/
structure Gear (m : Bool) (B f : ι → ℕ) (s : Ty) (x : ι → T s) : Prop where
  power : Knows m B s x (fun i => 2^f i)
  given : Knows m B s x f
  table : Has m B s (a w) x (fun i => xorTab (f i))
  bound : Small B fun i => 2^f i

namespace Gear
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
variable (g : Gear m B f s x)
include g

lemma descend {κ : Type V} (j : κ → ι) (y : κ → T t)
    (h : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    Gear m (fun k => B (j k)) (fun k => f (j k)) t y :=
  ⟨h.then_do (g.power.reindex j),h.then_do (g.given.reindex j),
    h.then_do (g.table.reindex j), g.bound.reindex j⟩

variable {α : Type*} [Fintype α] [DecidableEq α]

-- size of fixed body (layout on α is fixed)
omit [Fintype α] [DecidableEq α] in
lemma body_size (X : Layout α) :
    Knows m B s x (fun i => (bodyOrder X (f i)).n) :=
  g.power.wpow_fixed X.n g.bound
omit [Fintype α] [DecidableEq α] in
lemma body_small (X : Layout α) :
    Small B fun i => (bodyOrder X (f i)).n :=
  g.bound.pow X.n

omit [Fintype α] [DecidableEq α] in
lemma grid_size (X : Layout α) (r : ℕ) :
    Knows m B s x (fun i => (book X r (f i)).n) :=
  Can.times (Can.wc (2^r)) (g.body_size X) (Small.const ..) (g.body_small X)

omit [Fintype α] [DecidableEq α] in
lemma grid_small (X : Layout α) (r : ℕ) :
    Small B fun i => (book X r (f i)).n :=
  (Small.const B (2^r)).mul (g.body_small X)

omit [Fintype α] [DecidableEq α] in
lemma body_get (X : Layout α) (v : ∀ i, Sky α (f i)) (j : α)
    (h : Knows m B s x fun i => (bodyOrder X (f i)).loc (v i)) :
    Knows m B s x (fun i => (bits (f i)).loc (fun l => v i l j)) := by
  have hb := h.dvdW (g.power.wpow_fixed (X.loc j) g.bound)
    (Small.loc (x:=v) (L:=fun i => bodyOrder X (f i)) (g.body_small X))
  have hu : Small B (fun i => (bodyOrder X (f i)).loc (v i) / (2^f i)^X.loc j) :=
    (Small.loc (x:=v) (L:=fun i => bodyOrder X (f i)) (g.body_small X)).div
  refine (hb.modW g.power hu).cong (fun _ => rfl) ?_
  intro i
  exact Layout.digits_entry X (bits (f i)) (rows α _ (v i)) j

omit [DecidableEq α] in
lemma body_set (X : Layout α) (v : ∀ i, Sky α (f i))
    (h : ∀ j : α, Knows m B s x fun i => (bits (f i)).loc (fun l => v i l j)) :
    Knows m B s x (fun i => (bodyOrder X (f i)).loc (v i)) := by
  have hf (j : α) : Small B fun i => (bits (f i)).loc (fun l => v i l j) :=
    Small.loc (x:=fun i l => v i l j) (L:=fun i => bits (f i)) g.bound
  have hh := Can.sum_wconst (fun j => (h j).times
    (g.power.wpow_fixed (X.loc j) g.bound)
    (hf j) (g.bound.pow (X.loc j))) (fun j => (hf j).mul (g.bound.pow _))
  refine hh.cong (fun _ => rfl) ?_
  intro i
  exact (Layout.digits_code X (bits (f i)) (fun j l => v i l j)).symm

variable (X : Layout α) (r : ℕ)

omit [Fintype α] [DecidableEq α] in
lemma grid_fetch {v : ∀ i, Grid α r (f i)}
    (h : Knows m B s x fun i => (book X r (f i)).loc (v i)) :
    Knows m B s x (fun i => (bits r).loc (v i).1) ∧
    Knows m B s x (fun i => (bodyOrder X (f i)).loc (v i).2) :=
  ⟨Can.addr_high (L:=fun _ => bits r) (R:=fun i => bodyOrder X (f i)) (u:=v)
      h (g.body_size X) (g.grid_small X r),
   Can.addr_low (L:=fun _ => bits r) (R:=fun i => bodyOrder X (f i)) (u:=v)
      h (g.body_size X) (g.grid_small X r)⟩

omit [Fintype α] [DecidableEq α] in
lemma grid_combine {v : ∀ i, Grid α r (f i)}
    (a : Knows m B s x (fun i => (bits r).loc (v i).1))
    (b : Knows m B s x (fun i => (bodyOrder X (f i)).loc (v i).2)) :
    Knows m B s x (fun i => (book X r (f i)).loc (v i)) :=
  Can.addr_join (L:=fun _ => bits r) (R:=fun i => bodyOrder X (f i)) (u:=v)
    a b (g.body_size X) (Small.const B (2^r)) (g.body_small X)

lemma addr_xor (v : ∀ i, Bits (f i) × Bits (f i))
    (h : Knows m B s x (fun i => (bits (f i)).loc (v i).1))
    (k : Knows m B s x (fun i => (bits (f i)).loc (v i).2)) :
    Knows m B s x (fun i => (bits (f i)).loc ((v i).1+(v i).2)) :=
  Can.xor_lookup v g.table h k g.power g.bound

omit [DecidableEq α] in
/-- Address translated by z (across f columns). -/
lemma shifted (z : Space α) (v : ∀ i, Grid α r (f i))
    (h : Knows m B s x (fun i => (book X r (f i)).loc (v i))) :
    Knows m B s x (fun i => (book X r (f i)).loc ((v i).1,
      fun j => (v i).2 j + z)) := by
  obtain ⟨hg, hh⟩ := g.grid_fetch X r (v:=v) h
  let K (i : ι) : Grid α r (f i) := ((v i).1, fun j => (v i).2 j + z)
  apply g.grid_combine X r (v:=K) hg (g.body_set X (fun i => (K i).2) _)
  intro j
  have hv := g.body_get X (fun i => (v i).2) j hh
  rcases bit_cases (z j) with hj|hj
  · refine hv.cong (fun _ => rfl) (fun i => ?_)
    simp [K,hj]
  · let q i : Bits (f i) × Bits (f i) := (fun l => (v i).2 l j, fun _ => 1)
    have hf : Knows m B s x (fun i => (bits (f i)).loc (q i).2) :=
      (g.power.minus (Can.wc 1) g.bound).cong (fun _ => rfl) (fun i => by
        change 2^f i-1=(bits _).loc (fun _ => 1)
        rw [← bits_lit]
        simp)
    refine (g.addr_xor q hv hf).cong (fun _ => rfl) (fun i => ?_)
    apply congr_arg (bits (f i)).loc
    ext k; simp [q,K,hj]

/-- Program can go back and forth between grid and (fiber,within-fiber). -/
lemma from_grid (j : α) (X' : Layout (Minus j)) (z : Space α)
    (v : ∀ i, Grid α r (f i))
    (h : Knows m B s x (fun i => (book X r (f i)).loc (v i))) :
    let u i := peelBook j z r (f i) (v i)
    Knows m B s x (fun i => (book X' r (f i)).loc (u i).1) ∧
    Knows m B s x (fun i => (bits (f i)).loc (u i).2) := by
  intro u
  obtain ⟨hg, hh⟩ := g.grid_fetch X r (v:=v) h
  have ht (l : α) := g.body_get X (fun i => (v i).2) l hh
  refine ⟨g.grid_combine X' r (v:=fun i => (u i).1) hg
    (g.body_set X' (fun i => (u i).1.2) ?_), ht j⟩
  intro l
  rcases bit_cases (z l.val) with hl|hl
  · refine (ht l.val).cong (fun _ => rfl) (fun i => ?_)
    simp [u,peelBook,skySplit,peel,hl]
  · let q (i : ι) : Bits (f i) × Bits (f i) :=
      (fun k => (v i).2 k l.val, fun k => (v i).2 k j)
    refine (g.addr_xor q (ht l.val) (ht j)).cong (fun _ => rfl) (fun i => ?_)
    apply congr_arg (bits (f i)).loc
    ext k
    simp [u,q,peelBook,skySplit,peel,hl]

lemma to_grid (j : α) (X' : Layout (Minus j)) (z : Space α)
    (u : ∀ i, Grid (Minus j) r (f i) × Bits (f i))
    (h : Knows m B s x (fun i => (book X' r (f i)).loc (u i).1))
    (k : Knows m B s x (fun i => (bits (f i)).loc (u i).2)) :
    let v i := (peelBook j z r (f i)).symm (u i)
    Knows m B s x (fun i => (book X r (f i)).loc (v i)) := by
  intro v
  obtain ⟨hg, hh⟩ := g.grid_fetch X' r (v:=fun i => (u i).1) h
  refine g.grid_combine X r (v:=v) hg (g.body_set X (fun i => (v i).2) ?_)
  intro l
  by_cases hl : l=j
  · subst l; simpa [v,peelBook,skySplit,peel]
  · let t : Minus j := ⟨l,hl⟩
    have ht := g.body_get X' (fun i => (u i).1.2) t hh
    rcases bit_cases (z l) with he|he
    · refine ht.cong (fun _ => rfl) (fun i => ?_)
      simp [v,t,peelBook,skySplit,peel,hl,he]
    · let q (i : ι) : Bits (f i) × Bits (f i) :=
        (fun k => (u i).1.2 k t, (u i).2)
      refine (g.addr_xor q ht k).cong (fun _ => rfl) (fun i => ?_)
      apply congr_arg (bits (f i)).loc; ext b
      simp [v,t,q,peelBook,skySplit,peel,hl,he]

end Gear
end
end PowerSaving.RAM

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.ColumnAddresses

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.RoleArrays
section

namespace OAI

/-! Using a finite certificate. Amplified role arrays with leftover bits. -/
namespace PowerSaving.RAM
open Ty Binary Finset
noncomputable section

abbrev Beach (α ρ : Type*) (r f : ℕ) := ρ × Grid α r f
abbrev Grain (α ρ : Type*) (r f : ℕ) := Beach α ρ r f → ℂ

def fleet {α ρ : Type*} (X : Layout α) (R : Layout ρ) (r f : ℕ) :=
  R.pair (book X r f)

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

def ferry (r f : ℕ) (u : Move α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => u.go f (fun i j => v (i,x.2.1,j)) x.1 x.2.2

/-- Total certificate action. -/
def coastline (r f : ℕ) (p : PWord α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => walk f p (fun i j => v (i,x.2.1,j)) x.1 x.2.2

theorem coast_cons (r f : ℕ) (u : Move α ρ) (p : PWord α ρ) (v : Grain α ρ r f) :
    coastline r f (u::p) v = coastline r f p (ferry r f u v) := rfl

end

universe U V
variable {ι : Type U}

/-- Gear and ready input full role tape. -/
structure Rig {α ρ : Type*} (m : Bool) (B f : ι → ℕ) (s : Ty) (x : ι → T s)
    (cl : Paint) (X : Layout α) (R : Layout ρ) (r : ℕ) (v : ∀ i, Grain α ρ r (f i)) : Prop where
  gear : Gear m B f s x
  imag : Has m B s sc x fun _ => Complex.I
  items : Has m B s (a (c cl)) x fun i => (fleet X R r (f i)).tape (v i)

namespace Rig
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
variable (h : Rig m B f s x cl X R r v)
include h

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma gather {κ : Type V} (j : κ → ι) (y : κ → T t)
    (g : Has m (fun k => B (j k)) t s y (fun k => x (j k))) :
    Rig m (fun k => B (j k)) (fun k => f (j k)) t y cl X R r (fun k => v (j k)) :=
  ⟨h.gear.descend j y g,
    g.then_do (h.imag.reindex j), g.then_do (h.items.reindex j)⟩

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma large : Small B fun i => (fleet X R r (f i)).n :=
  (Small.const B R.n).mul (h.gear.grid_small X r)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma size : Knows m B s x fun i => (fleet X R r (f i)).n :=
  (Can.wc R.n).times (h.gear.grid_size X r) (Small.const B R.n) (h.gear.grid_small X r)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma addrs (u : ∀ i, Beach α ρ r (f i))
    (hg : Knows m B s x fun i => (fleet X R r (f i)).loc (u i)) :
    Knows m B s x (fun i => R.loc (u i).1) ∧
      Knows m B s x (fun i => (book X r (f i)).loc (u i).2) :=
  ⟨Can.addr_high (u:=u) (L:=fun _ => R) (R:=fun i => book X r (f i)) hg
    (h.gear.grid_size X r) h.large,
   Can.addr_low (u:=u) (L:=fun _ => R) (R:=fun i => book X r (f i)) hg
    (h.gear.grid_size X r) h.large⟩

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma read (u : ∀ i, Beach α ρ r (f i)) (ha : Knows m B s x fun i => R.loc (u i).1)
    (hb : Knows m B s x fun i => (book X r (f i)).loc (u i).2) :
    Has m B s (c cl) x (fun i => v i (u i)) :=
  Can.fetch (t:=c cl) (L:=fun i => fleet X R r (f i)) (v:=v) (i:=u)
    h.items
    (Can.addr_join (L:=fun _ => R) (R:=fun i => book X r (f i)) (u:=u) ha hb
      (h.gear.grid_size X r) (Small.const B R.n) (h.gear.grid_small X r))

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma chart (v : ∀ i, Grain α ρ r (f i))
    (g : Has m (fun i : Σ i, Beach α ρ r (f i) => B i.1) (p s w) (c cl)
      (fun d => (x d.1,(fleet X R r (f d.1)).loc d.2)) (fun d => v d.1 d.2)) :
    Can m B s (a (c cl)) x (fun i => (fleet X R r (f i)).tape (v i))
      (fun i => (fleet X R r (f i)).n) := by
  have ht := Can.layout (t:=c cl) (P:=fun _ => 0)
    (L:=fun i => fleet X R r (f i)) (v:=v) h.size g h.large
  simpa only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] using ht

lemma ferry_point (M : Matrix ρ ρ ℚ) (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x fun i => (fleet X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => ferry r (f i) (.localM M) (v i) (q i) := by
  obtain ⟨hl,hk⟩ := h.addrs q g
  -- fixed number of roles; can load each in each iteration
  let z (j : ρ) i := (M (q i).1 j : ℂ) * v i (j,(q i).2)
  change Can m B s (c cl) x (fun i => ∑ j, z j i) _
  apply Can.sum_cconst
  intro j
  have hx : Has m B s sc x (fun i => (M (q i).1 j : ℂ)) := by
    apply Can.cases_code (q:=fun i => (q i).1) R hl
    intro l
    convert (Can.rat (B:=fun i : {i // (q i).1=l} => B i.1) (s:=s)
      (x:=fun i => x i.1) (m:=m) (W:=fun _ => 0) (M l j)) using 1
    funext i; rw [i.2]
  exact hx.mul (h.read (fun i => (j,(q i).2)) (Can.wc (R.loc j)) hk)

lemma ferry_shift (l : ρ) (z : Space α) (q : ∀ i, Beach α ρ r (f i))
    (g : Knows m B s x fun i => (fleet X R r (f i)).loc (q i)) :
    Has m B s (c cl) x fun i => ferry r (f i) (.shift l z) (v i) (q i) := by
  obtain ⟨hl,hk⟩ := h.addrs q g
  have hb := h.read q hl hk
  let t i : Beach α ρ r (f i) := ((q i).1,(q i).2.1,fun j => (q i).2.2 j+z)
  have hh := h.read t hl (h.gear.shifted X r z _ hk)
  apply Can.cases_code (q:=fun i => (q i).1) R hl
  intro p
  by_cases he : p=l
  · refine (hh.reindex (fun i : {i // (q i).1=p} => i.1)).cong (fun _ => rfl)
      (fun i => ?_)
    simp [t,ferry,Move.go,roleAct,i.2,he,act_shift]
  · refine (hb.reindex (fun i : {i // (q i).1=p} => i.1)).cong (fun _ => rfl)
      (fun i => ?_)
    simp [ferry,Move.go,roleAct,i.2,he]
    exact congr_arg (fun p => v i.val (p,(q i.val).2)) i.2

lemma point_cost (M : Matrix ρ ρ ℚ) :
    Can m B s (a (c cl)) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) (.localM M) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  refine h.chart _ ?_
  let S := Σ i, Beach α ρ r (f i)
  have hg := h.gather (fun d : S => d.1)
    (fun d => ((x d.1, (fleet X R r (f d.1)).loc d.2):T (p s w))) (t:=p s w) Can.first
  exact hg.ferry_point M (fun d => d.2) Can.second

lemma shift_cost (l : ρ) (z : Space α) :
    Can m B s (a (c cl)) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) (.shift l z) (v i)))
      (fun i => (fleet X R r (f i)).n) := by
  refine h.chart _ ?_
  let S := Σ i, Beach α ρ r (f i)
  have hg := h.gather (fun d : S => d.1)
    (fun d => ((x d.1, (fleet X R r (f d.1)).loc d.2):T (p s w))) (t:=p s w) Can.first
  exact hg.ferry_shift l z (fun d => d.2) Can.second

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
/-- Fixed scalar matrices of C etc. -/
lemma little (i j : F) :
    Has m B s sc x fun _ => littleC i j := by
  have h2 : Has m B s sc x (fun _ => (2:ℂ)) := by
    simpa using Can.cNat (m:=m) (B:=B) (W:=fun _ => 0) (s:=s) (x:=x) 2
  have hh := h2.inv (by simp)
  unfold littleC ca cb
  split
  · simp only [div_eq_mul_inv]; exact (Can.one.add h.imag).mul hh
  · simp only [div_eq_mul_inv]; exact (Can.one.sub h.imag).mul hh

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma leftOvers (a b : Bits r) :
    Has m B s sc x fun _ => kernel (Fin r) a b :=
  Can.prod_cconst (v:=fun i _ => littleC (a i) (b i)) (fun _ => h.little _ _)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
/-- r remaining bits before main work. -/
lemma dots_cost :
    Can m B s (a (c cl)) x
      (fun i => (fleet X R r (f i)).tape (fun d =>
        chords r (f i) (fun j => v i (d.1,j)) d.2))
      (fun i => (fleet X R r (f i)).n) := by
  refine h.chart _ ?_
  let S := Σ i, Beach α ρ r (f i)
  let env (d : S) : T (p s w) := (x d.1,(fleet X R r (f d.1)).loc d.2)
  let hc := h.gather (fun d : S => d.1) env (t:=p s w) Can.first
  obtain ⟨ha,hb⟩ := hc.addrs (fun d => d.2) Can.second
  obtain ⟨hl,hk⟩ := hc.gear.grid_fetch X r (v:=fun d => d.2.2) hb
  let B1 (d:S) := B d.1
  change Can m B1 (p s w) (c cl) env
    (fun d => ∑ j, kernel (Fin r) d.2.2.1 j * v d.1 (d.2.1,j,d.2.2.2)) _
  apply Can.sum_cconst
  intro j
  let u (d : S) : Beach α ρ r (f d.1) := (d.2.1,j,d.2.2.2)
  have hv := hc.read u ha
    (hc.gear.grid_combine X r (v:=fun d => (u d).2)
      (Can.wc ((bits r).loc j)) hk)
  have he : Has m B1 (p s w) sc env
      (fun d => kernel (Fin r) d.2.2.1 j) := by
    apply Can.cases_code (q:=fun d => d.2.2.1) (bits r) hl
    intro l
    exact ((hc.leftOvers l j).reindex (fun d : {d:S // d.2.2.1=l} => d.1)).cong
      (fun _ => rfl) (fun i => by rw [i.2])
  exact he.mul hv

end Rig
end
end PowerSaving.RAM

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.RoleArrays

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.RecursiveBatches
section

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

/-- An instance of the simultaneous kernel program. -/
abbrev Sim (ρ : Type*) (k : ℕ) := ρ × Bits k
def sim {ρ : Type*} (R : Layout ρ) (k : ℕ) := R.pair (bits k)

abbrev bundle := fun cl => a (c cl)
abbrev simIn := fun cl => p w (p sc (bundle cl))
abbrev hatch := fun cl => some (simIn cl,bundle cl)

def whole {ρ : Type*} (k : ℕ) (v : Sim ρ k → ℂ) : Sim ρ k → ℂ :=
  fun (l,i) => ripple k (fun j => v (l,j)) i

def loaded {ρ : Type*} (cl : Paint) (R : Layout ρ) (k : ℕ) (v : Sim ρ k → ℂ) :
    T (simIn cl) :=
  (k,Complex.I,(sim R k).tape v)

-- cut t groups of R.n fibers from the peeled coordinates
def cut {β ρ} (r f t : ℕ) (X : Layout β) (R : Layout ρ)
    (h : t*R.n = (book X r f).n) :
    (Fin t × ρ) ≃ Grid β r f :=
  let L := (Layout.std t).pair R
  (L.index.trans (finCongr h)).trans (book X r f).index.symm

lemma cut_eq {β ρ} (r f t) (X : Layout β) (R : Layout ρ) h
    (z : Fin t × ρ) :
    (book X r f).loc (cut r f t X R h z) = z.1.val * R.n + R.loc z.2 :=
  Layout.loc_atFin _ _

lemma uncut_eq {β ρ} (r f t) (X : Layout β) (R : Layout ρ) h
    (q : Grid β r f) :
    let v := (cut r f t X R h).symm q
    (book X r f).loc q = v.1.val*R.n+R.loc v.2 := by
  intro v
  have hh := cut_eq r f t X R h v
  simpa only [v,Equiv.apply_symm_apply] using hh

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α]

/-- Source data for one recursive call (one batch). -/
def fill (l : ρ) (j : α) (z : Space α) {r f t : ℕ} (X : Layout (Minus j))
    (R : Layout ρ) (h : t*R.n=(book X r f).n)
    (v : Grain α ρ r f) (b : Fin t) : Sim ρ f → ℂ :=
  fun (k,i) => v (l,(peelBook j z r f).symm
    ((cut r f t X R h) (b,k),i))

/-- Collection of returned answers. -/
def yieldTape (l : ρ) (j : α) (z : Space α) {r f t} (X : Layout (Minus j))
    (R : Layout ρ) (h : t*R.n=(book X r f).n) (v : Grain α ρ r f) : Tape (Tape ℂ) :=
  (Layout.std t).tape fun b =>
    (sim R f).tape (whole f (fill l j z X R h v b))

-- proof calculation for one direction
lemma fill_result [Fintype ρ] [DecidableEq ρ] (l : ρ) (j : α) (z : Space α)
    (hz : z j=1) (hn : z≠0) {r f t} (X : Layout (Minus j)) (R : Layout ρ) h
    (v : Grain α ρ r f) (a : Grid α r f) :
    let q := peelBook j z r f a
    let w := (cut r f t X R h).symm q.1
    ferry r f (.dir l z hn) v (l,a) = whole f (fill l j z X R h v w.1) (w.2,q.2) := by
  intro q w
  unfold ferry Move.go roleAct
  simp only [ite_true]
  have H := peel_act j z hz r f (fun p => v (l,p)) a
  refine H.trans ?_
  unfold whole fill
  simp only [q,w,Prod.mk.eta,Equiv.apply_symm_apply]

end

section
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {B f n : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}

namespace Rig
variable (h : Rig m B f s x cl X R r v)
include h

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma simSmall : Small B fun i => (sim R (f i)).n :=
  (Small.const B R.n).mul h.gear.bound

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma simSize : Knows m B s x fun i => (sim R (f i)).n :=
  Can.times (Can.wc R.n) h.gear.power (Small.const B R.n) h.gear.bound

variable (l : ρ) (j : α) (z : Space α) (X' : Layout (Minus j))
variable (hg : ∀ i, n i*R.n = (book X' r (f i)).n)
include hg

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma batchSmall (hr : 0<R.n) :
    Small B n :=
  (h.gear.grid_small X' r).mono (fun i => by
    rw [← hg]
    exact Nat.le_mul_of_pos_right _ hr)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma batchSize (hr : 0<R.n) :
    Knows m B s x n :=
  ((h.gear.grid_size X' r).dvdW (Can.wc R.n) (h.gear.grid_small X' r)).cong
    (fun _ => rfl) (fun i => by rw [← hg]; exact Nat.mul_div_cancel _ hr)

omit [Fintype ρ] [DecidableEq ρ] in
lemma fill_read (a : ∀ i, Sim ρ (f i)) (b : ∀ i, Fin (n i))
    (hd : Knows m B s x fun i => (sim R (f i)).loc (a i))
    (ha : Knows m B s x fun i => (b i).val) :
    Has m B s (c cl) x fun i => fill l j z X' R (hg i) (v i) (b i) (a i) := by
  let L i := bits (f i)
  have hu := Can.addr_high (u:=a) (L:=fun _ => R) (R:=L) hd h.gear.power h.simSmall
  have hw := Can.addr_low (u:=a) (L:=fun _ => R) (R:=L) hd h.gear.power h.simSmall
  have hr : 0<R.n := lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
  let C i := cut r (f i) (n i) X' R (hg i)
  let K i : Grid (Minus j) r (f i) × Bits (f i) :=
    (C i (b i,(a i).1),(a i).2)
  have hs := Can.addr_join (L:=fun i => Layout.std (n i)) (R:=fun _ => R)
    (u:=fun i => (b i,(a i).1)) ha hu (Can.wc R.n)
    (h.batchSmall j X' hg hr) (Small.const B R.n)
  have hm : Knows m B s x fun i => (book X' r (f i)).loc (K i).1 :=
    hs.cong (fun _ => rfl) (fun i => (cut_eq r (f i) (n i) X' R _ _).symm)
  have hk := h.gear.to_grid X r j X' z K hm hw
  exact h.read (fun i => (l,(peelBook j z r (f i)).symm (K i))) (Can.wc (R.loc l)) hk

omit [Fintype ρ] [DecidableEq ρ] in
omit [Fintype ρ] [DecidableEq ρ] in
lemma fill_ready (b : ∀ i, Fin (n i))
    (ha : Knows m B s x fun i => (b i).val) :
    Can m B s (simIn cl) x
      (fun i => loaded cl R (f i) (fill l j z X' R (hg i) (v i) (b i)))
      (fun i => (sim R (f i)).n) := by
  let W i := (sim R (f i)).n
  let V (i : ι) := fill l j z X' R (hg i) (v i) (b i)
  have hd : Can m B s (bundle cl) x (fun i => (sim R (f i)).tape (V i)) W := by
    let S := Σ i, Sim ρ (f i)
    let env (d : S) : T (p s w) := (x d.1,(sim R (f d.1)).loc d.2)
    have G := h.gather (fun d : S => d.1) env (t:=p s w) Can.first
    have hh := G.fill_read l j z X' (n:=fun d=>n d.1) (fun d => hg d.1)
      (fun d => d.2) (fun d => b d.1) Can.second
      (Can.first.then_do (ha.reindex (Sigma.fst (β:=fun i => Sim ρ (f i)))))
    have ht := Can.layout (t:=c cl) (P:=fun _ => 0)
      (L:=fun i => sim R (f i)) (v:=V) h.simSize hh h.simSmall
    simpa [W] using ht
  exact (h.gear.given.mono (fun i => Nat.zero_le (W i))).pair
    ((h.imag.mono (fun i => Nat.zero_le (W i))).pair hd)

-- compute a directional outcome from the packed answers (and from unchanged roles)
lemma direction_get (hn : z≠0) (hz : z j=1)
    (H : Has m B s (Ty.a (bundle cl)) x fun i => yieldTape l j z X' R (hg i) (v i))
    (a : ∀ i, Beach α ρ r (f i)) (ha : Knows m B s x fun i => (fleet X R r (f i)).loc (a i)) :
    Has m B s (c cl) x fun i => ferry r (f i) (.dir l z hn) (v i) (a i) := by
  obtain ⟨hx,hy⟩ := h.addrs a ha
  let C i := cut r (f i) (n i) X' R (hg i)
  let K i := peelBook j z r (f i) (a i).2
  let Q i := (C i).symm (K i).1
  let Y i := ((Layout.std (n i)).pair R).loc (Q i)
  obtain ⟨hd,he⟩ := h.gear.from_grid X r j X' z (fun i => (a i).2) hy
  have hY : Knows m B s x Y :=
    hd.cong (fun _ => rfl) (fun i => uncut_eq r (f i) (n i) X' R _ (K i).1)
  have ls : Small B fun i => n i * R.n :=
    (h.gear.grid_small X' r).mono (fun i => le_of_eq (hg i))
  have hA := Can.addr_high (L:=fun i => Layout.std (n i)) (R:=fun _ => R)
    (u:=Q) hY (Can.wc R.n) ls
  have hB := Can.addr_low (L:=fun i => Layout.std (n i)) (R:=fun _ => R)
    (u:=Q) hY (Can.wc R.n) ls
  let F i b := fill l j z X' R (hg i) (v i) b
  have hD := Can.fetch (t:=bundle cl) (L:=fun i => Layout.std (n i))
    (i:=fun i => (Q i).1) (v:=fun i b => (sim R (f i)).tape (whole (f i) (F i b))) H hA
  have hh := Can.fetch (t:=c cl) (L:=fun i => sim R (f i))
    (i:=fun i => ((Q i).2,(K i).2)) (v:=fun i => whole (f i) (F i (Q i).1))
    hD (Can.addr_join (L:=fun _ => R) (R:=fun i => bits (f i)) (u:=fun i => ((Q i).2,(K i).2))
      hB he h.gear.power (Small.const B R.n) h.gear.bound)
  apply Can.cases_code (q:=fun i => (a i).1) R hx
  intro r'
  by_cases hL : r'=l
  · refine (hh.reindex (fun i : {i // (a i).1=r'} => i.val)).cong (fun _ => rfl)
      (fun i => ?_)
    have ht := fill_result l j z hz hn (t:=n i.val)
      X' R (hg i.val) (v i.val) (a i.val).2
    have hC : (l,(a i.val).2) = (a i.val) := Prod.ext (i.property.trans hL).symm rfl
    exact ht.symm.trans (congr_arg _ hC)
  · refine ((h.read a hx hy).reindex (fun i : {i // (a i).1=r'} => i.val)).cong
      (fun _ => rfl) (fun i => ?_)
    have H : (a i.val).1≠l := fun hh => hL (i.property.symm.trans hh)
    simp only [ferry,Move.go,roleAct, H,ite_false, Prod.mk.eta]

end Rig
end
end
end PowerSaving.RAM

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.RecursiveBatches

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.RecursiveContract
section

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}

/-- Contract assumed on external calls *inside* the open body proof only. -/
def Contract (cl : Paint) (b : Bank (hatch cl) ι) (f T : ι → ℕ) (R : Layout ρ) :=
  ∀ i v, (b.use i (loaded cl R (f i) v)).OK ((sim R (f i)).tape (whole (f i) v))
             (T i) (b.ext i)

variable {m : Bool} {f n τ : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
    {b : Bank (hatch cl) ι}

namespace Rig
variable (h : Rig m b.B f s x cl X R r v)
include h

lemma open_dir (hk : Contract cl b f τ R)
    (hg : ∀ i, n i*(sim R (f i)).n=(book X r (f i)).n)
    (l : ρ) (z : Space α) (hz : z≠0) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) (.dir l z hz) (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => n i*τ i) := by
  obtain ⟨j,hj⟩ := choose_pivot hz
  let X' := Layout.someLayout (Minus j)
  have he (i) : n i * R.n=(book X' r (f i)).n := by
    have hy : X'.n+1=X.n := by
      rw [← Layout.card X',← Layout.card X]; exact card_minus j
    have hz := hg i
    change n i*(R.n*2^f i) = 2^r*(2^f i)^X.n at hz
    change n i * R.n = 2^r*(2^f i)^X'.n
    rw [← hy,pow_succ, ← mul_assoc, ← mul_assoc] at hz
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hz
  let w i := (fleet X R r (f i)).n
  let y i := yieldTape l j z X' R (he i) (v i)
  let sz i := (sim R (f i)).n
  let Tt := a (bundle cl)
  have hl : 0 < R.n := lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
  have hy : Able m b s Tt x y w (fun i => n i*τ i) := by
    let arg (i) (k : Fin (n i)) := fill l j z X' R (he i) (v i) k
    let g (i) (k : Fin (n i)) := (sim R (f i)).tape (whole (f i) (arg i k))
    let I (i : ι) := Fin (n i)
    let E0 (d : Σ i, I i) := (x d.1,(d.2:ℕ))
    have hs : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (bundle cl)
        E0 (fun d => g d.1 d.2) (fun d => sz d.1) (fun d => τ d.1) := by
      have HH := h.gather (Sigma.fst (β:=I)) E0 (t:=p s Ty.w) Can.first
      have Hp := HH.fill_ready l j z X' (n:=fun d=> n d.1) (fun d => he d.1)
        (fun d : Σ i,I i => d.2) Can.second
      have Hq : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (simIn cl) E0
          (fun d => loaded cl R (f d.1) (arg d.1 d.2))
          (fun d => sz d.1) (fun _ => 0) := Able.of_can Hp
      have HG := Hq.comp (Able.use_call (ι:=Σ i,I i) (s:=simIn cl) (t:=bundle cl) (m:=m) (b:=b.comap (Sigma.fst (β:=I))) (Z:=fun d => τ d.1) (y:=fun d => g d.1 d.2)
        (fun d => hk d.1 (arg d.1 d.2)))
      simpa [Nat.zero_add] using HG
    have HT : Able m b s Ty.w x n (fun _=>0) (fun _=>0) :=
      Able.of_can (h.batchSize j X' he hl)
    have HH := Able.layout (L:=fun i => Layout.std (n i)) (v:=g) (t:=bundle cl)
      (P:=sz) (H:=τ) HT hs (h.batchSmall j X' he hl)
    refine HH.weaken ⟨2,fun i => ?_⟩ ?_
    · change 0+n i+n i*sz i+1 ≤ _
      have hj := hg i
      have hsz : sz i>0 := Nat.mul_pos hl (by change 0<2^(f i); positivity)
      have hy : n i*sz i ≤ w i :=
        calc
          _ = (book X r (f i)).n := hj
          _ ≤ R.n*(book X r (f i)).n := Nat.le_mul_of_pos_left _ hl
          _ = _ := rfl
      have gr : n i ≤ n i*sz i := Nat.le_mul_of_pos_right _ hsz
      omega
    · intro i; change 0+n i*τ i ≤ n i*τ i; omega
  let K := fun i => ferry r (f i) (.dir l z hz) (v i)
  have hh :
      Can m b.B (p s Tt) (bundle cl)
        (fun i => (x i,y i)) (fun i => (fleet X R r (f i)).tape (K i)) w := by
    let s' := p s Tt
    let env i : T s' := (x i,y i)
    have h' : Rig m b.B f s' env cl X R r v := h.gather id env Can.first
    refine h'.chart _ ?_
    let I (i : ι) := Beach α ρ r (f i)
    let u (d : Σ i, I i) : T (p s' Ty.w) := (env d.1,(fleet X R r (f d.1)).loc d.2)
    have HG := h'.gather (Sigma.fst (β:=I)) u (t:=p s' Ty.w) Can.first
    exact HG.direction_get l j z X' (n:=fun d => n d.1) (fun d => he d.1) hz hj
      (Can.snd Can.first) (fun d => d.2) Can.second
  exact hy.save_keep (Able.of_can hh)

lemma open_move (hk : Contract cl b f τ R)
    (hg : ∀ i, n i*(sim R (f i)).n=(book X r (f i)).n)
    (z : Move α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) z (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => toll z * n i * τ i) := by
  cases z with
  | localM M =>
    simpa [toll,Nat.zero_mul] using
      (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.point_cost M))
  | shift r z =>
    simpa [toll,Nat.zero_mul] using
      (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.shift_cost r z))
  | dir l z hz => simpa [toll,one_mul] using h.open_dir hk hg l z hz

lemma sweep (hk : Contract cl b f τ R)
    (hg : ∀ i, n i*(sim R (f i)).n=(book X r (f i)).n)
    (P : PWord α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (coastline r (f i) P (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => tally P * n i * τ i) := by
  induction P generalizing s v with
  | nil =>
    have ht := h.items.mono (W':=fun i => (fleet X R r (f i)).n) (fun _ => Nat.zero_le _)
    have hz := Able.of_can (b:=b) ht
    -- coast nil
    have hg (i j) : coastline r (f i) [] (v i) j=v i j := rfl
    simp only [tally,List.map_nil,List.sum_nil, Nat.zero_mul]
    exact hz
  | cons g pth ih =>
    let v' i := ferry r (f i) g (v i)
    let env i : T (Ty.p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
    have hk := h.gather id env (t:=Ty.p s (bundle cl)) Can.first
    have hl : Rig m b.B f (Ty.p s (bundle cl)) env cl X R r v' :=
      ⟨hk.gear,hk.imag,Can.second⟩
    have hh := ih hl
    have H := (h.open_move (b:=b) (τ:=τ) (by assumption) hg g).save_keep hh
    simpa only [coast_cons,tally,List.map_cons,List.sum_cons,_root_.add_mul] using H

end Rig
end
end PowerSaving.RAM

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.RecursiveContract

-- bos_merge: begin Submission.OAI.Computability.FourierTransform.TensorRecursion
section

namespace OAI
namespace PowerSaving.RAM
open Binary Ty Matrix Finset
noncomputable section

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

section

variable (X : Layout α) (R : Layout ρ) (r f k : ℕ)
    (h : X.n*f+r=k)

def ebb (v : Sim ρ k → ℂ) : Grain α ρ r f :=
  fun j => v (j.1,serial X r f h j.2)
-- R not included in def

omit [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma ebb_eq (v : Sim ρ k→ℂ) :
    (fleet X R r f).tape (ebb X r f k h v) = (sim R k).tape v := by
  refine Layout.verify (sim R k) _ 0 _ ?_ ?_
  · change R.n*(book X r f).n=R.n*(bits k).n
    rw [book_len, bits_len,h]
  · rintro ⟨a,j⟩
    obtain ⟨w,hw⟩ := (serial X r f h).surjective j
    subst j
    have hd : (sim R k).loc (a,serial X r f h w) = (fleet X R r f).loc (a,w) := by
      simp only [sim,fleet,Layout.pair_loc,book_len,serial_code, h,bits_len]
    rw [hd]
    apply Layout.read _ _ (a,w) _

lemma amplifies (p : PWord α ρ)
    (hp : ∀ v, walk f p v = multiAct f (fun _ => kernel α) v)
    (v : Sim ρ k → ℂ) :
    let e := ebb X r f k h v
    let z : Grain α ρ r f := fun i => chords r f (fun j => e (i.1,j)) i.2
    coastline r f p z = ebb X r f k h (whole k v) := by
  intro e z
  funext i
  unfold coastline
  rw [hp]
  exact (ripple_grid X r f h (fun j => v (i.1,j)) i.2).symm

end

section
universe U
variable {ι : Type U} {m : Bool}
    {k f n τ : ι → ℕ} {cl : Paint} {b : Bank (hatch cl) ι}
    {v : ∀ i, Sim ρ (k i)→ℂ}

/-- Body proof with fixed r. B need only dominate 2^k polynomially. -/
lemma amplify (m : Bool) (b : Bank (hatch cl) ι) (v : ∀ i, Sim ρ (k i) → ℂ)
    (X : Layout α) (R : Layout ρ) (r : ℕ)
    (hr : 3 ≤ X.n) (hq : ∀ i, X.n*f i+r=k i) (hd : r < X.n)
    (hc : ∀ i, n i*(sim R (f i)).n=2^k i)
    (hk : Contract cl b f τ R)
    (hB : Small b.B (fun i => 2^k i))
    (p : PWord α ρ) (hp : ∀ f v, walk f p v = multiAct f (fun _ => kernel α) v) :
    Able m b (simIn cl) (bundle cl) (fun i => loaded cl R (k i) (v i))
      (fun i => (sim R (k i)).tape (whole (k i) (v i)))
      (fun i => 2^k i) (fun i => tally p*n i*τ i) := by
  let W i := 2^k i
  let s := simIn cl
  let e (i : ι) := ebb X r (f i) (k i) (hq i) (v i)
  let z (i : ι) : Grain α ρ r (f i) :=
    fun j => chords r (f i) (fun l => e i (j.1,l)) j.2
  let sz i := (fleet X R r (f i)).n
  have hsz : Dom W sz := by
    refine ⟨R.n+1, fun i => ?_⟩
    unfold W sz fleet
    rw [Layout.pair_len, book_len,hq]
    simp only [mul_add,add_mul,mul_one,one_mul]
    gcongr <;> simp
  have hn (i : ι) : 0 < W i := pow_pos (by decide) _
  have hf (i) : f i ≤ k i := by
    have g := hq i
    have h := Nat.le_mul_of_pos_left (f i) (show 0 < X.n by omega)
    omega
  have hy (i) : k i ≤ W i := Nat.lt_two_pow_self.le
  have sd := hB.mono hy
  have sq := sd.mono hf
  let p2 i := 2^f i
  have hm : Small b.B p2 :=
    hB.mono (fun i => Nat.pow_le_pow_right (by omega) (hf i))
  have hcube (i) : p2 i ^ 3 ≤ W i := by
    unfold p2 W
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    have hh : 3*f i ≤ X.n*f i := Nat.mul_le_mul_right _ hr
    have hg := hq i
    rw [mul_comm]
    omega
  let env (i : ι) := loaded cl R (k i) (v i)
  -- construct fields (f,p2)
  have hmf : Can m b.B s Ty.w env f W := by
    have ht : Can m b.B s Ty.w env k W := Can.first
    refine (ht.dvdW (Can.wc X.n) sd).cong (fun _ => rfl) ?_
    intro i
    rw [← hq,mul_comm X.n]
    exact Layout.div_join hd
  have hmp : Can m b.B s (Ty.p Ty.w Ty.w) env (fun i => (f i,p2 i)) W :=
    hmf.pair (hmf.wTwo sq hm (Dom.of_le (fun i => (hf i).trans (hy i))))
  let T1 := Ty.p s (Ty.p Ty.w Ty.w)
  let Y (i : ι) : T T1 := (env i,f i,p2 i)
  have hmx : Can m b.B T1 (Ty.a Ty.w) Y (fun i => xorTab (f i)) W :=
    (Can.xor_prepare (m:=m) (f:=f) (B:=b.B) (s:=T1) (x:=Y)
      (Can.fst Can.second) (Can.snd Can.second) sq hm).mono hcube
  let T2 := Ty.p T1 (Ty.a Ty.w)
  let Y' (i : ι) : T T2 := (Y i,xorTab (f i))
  have hG : Rig m b.B f T2 Y' cl X R r e := by
    have H : Has m b.B T2 s Y' env := Can.fst Can.first
    refine ⟨⟨?_,?_,Can.second,hm⟩,?_,?_⟩
    · exact Can.snd (Can.snd Can.first)
    · exact Can.fst (Can.snd Can.first)
    · exact H.snd.fst
    · exact H.snd.snd.cong (fun _ => rfl) (fun i => (ebb_eq ..).symm)
  have HH : Can m b.B T2 (bundle cl) Y' (fun i => (fleet X R r (f i)).tape (z i)) W :=
    hG.dots_cost.weaken hsz
  let pre (i) := (fleet X R r (f i)).tape (z i)
  let T3 := Ty.p T2 (bundle cl)
  let A (i) : T T3 := (Y' i,pre i)
  have Hg := hG.gather id A (t:=T3) Can.first
  have G : Rig m b.B f T3 A cl X R r z := ⟨Hg.gear,Hg.imag,Can.second⟩
  have Hy := G.sweep hk (n:=n)
    (fun i => by rw [book_len,hq]; exact hc i) p
  have heq (i) : coastline r (f i) p (z i) = ebb X r (f i) (k i) (hq i) (whole (k i) (v i)) :=
    amplifies X r (f i) (k i) (hq i) p (hp _) (v i)
  have ha (i) : (fleet X R r (f i)).tape (coastline r (f i) p (z i)) =
      (sim R (k i)).tape (whole (k i) (v i)) := by
    rw [heq]; exact ebb_eq ..
  have Ho := (Hy.weaken hsz (fun _ => le_rfl)).cong (fun _ => rfl) ha
  have Hx := (Able.of_can (b:=b) hmp).save_keep
    ((Able.of_can (b:=b) hmx).save_keep ((Able.of_can (b:=b) HH).save_keep Ho))
  simpa only [Nat.zero_add] using Hx

end
end
end PowerSaving.RAM

end OAI

end
-- bos_merge: end Submission.OAI.Computability.FourierTransform.TensorRecursion

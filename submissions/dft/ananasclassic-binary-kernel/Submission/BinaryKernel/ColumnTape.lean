import Submission.Compiler.Layout

namespace OAI.PowerSaving.RAM.ColumnTape
open Ty Finset Bench
universe u

/-- Read a base-q address from its most to its least significant column. -/
def foldDigits {β : Type} (q : ℕ) (init : β) (next : β → ℕ → β) : ℕ → ℕ → β
  | 0, _ => init
  | f+1, x => next (foldDigits q init next f (x/q)) (x%q)

private theorem levelCost {q : ℕ} (hq : 2 ≤ q) (f : ℕ) :
    f + ∑ j ∈ range f, q^(j+1) ≤ 3*q^f := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [sum_range_succ, pow_succ]
    have := Nat.one_le_pow f q (by omega)
    have hh := Nat.mul_le_mul_left (q^f) hq
    omega

/-- Enumerate all q-ary addresses in linear total work. Each layer indexes its
parent tape and extends the parent state by one digit. The step proof may use
the prefix width and the local address bound to bound its intermediate words. -/
theorem build {m : Bool} {ι : Type u} {b : Bench m ι} {k : ι → ℕ}
    {q : ℕ} (hq : 2 ≤ q) {t : Ty} (init : t.T) (next : t.T → ℕ → t.T)
    (count : b.Nick k) (capacity : Small b.size (fun i => q^(k i)))
    (start : b.Moves (fun _ => 0) t (fun _ => init))
    (step : ∀ {κ : Type u} (c : Bench m κ) (f x : κ → ℕ),
      (∀ i, x i < q^(f i+1)) → Small c.size (fun i => q^(f i+1)) →
      c.Moves (fun _ => 0) t (fun i => foldDigits q init next (f i) (x i / q)) →
      c.Nick (fun i => x i % q) →
      c.Moves (fun _ => 0) t (fun i => foldDigits q init next (f i+1) (x i))) :
    b.Moves (fun i => q^(k i)) (a t)
      (fun i => Tape.tab (q^(k i)) (foldDigits q init next (k i))) := by
  let T := fun (_ : ι) (j : ℕ) => Tape.tab (q^j) (foldDigits q init next j)
  have first : b.Moves (fun _ => 0) (a t) (fun i => T i 0) := by
    have h := Bench.arrayNow (b := b) (t := t) (Nick.wc 1)
      (fun _ _ => init) (start.transfer (Instant.scan b _))
    exact h.weaken (Dom.const _ 1)
  have level : (b.climbs k (a t) T).Moves (fun d => q^(d.j+1)) (a t)
      (fun d => T d.i (d.j+1)) := by
    let c := b.climbs k (a t) T
    let N : During k → ℕ := fun d => q^d.j
    let NN : During k → ℕ := fun d => q^(d.j+1)
    have small : Small c.size NN := (capacity.reindex During.i).mono
      (fun d => Nat.pow_le_pow_right (by omega) d.hj)
    have small0 : Small c.size N := small.mono
      (fun d => Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
    have prev : c.Moves (fun _ => 0) (a t) (fun d => T d.i d.j) := tokenNow b _ _
    have size0 : c.Nick N := ⟨prev.len small0,small0⟩
    have sz : c.Nick NN := (size0.mul (Nick.wc q)).congr (fun _ => (pow_succ _ _).symm)
    apply arrayNow sz
    let nc := c.scan NN
    have ix : nc.Nick During.j := chop sz
    apply step nc (fun d => d.i.j) During.j (fun d => d.hj) (small.reindex During.i)
    · exact Moves.pick (fun d => foldDigits q init next d.i.j)
        (prev.transfer (Instant.scan c _)) (ix.div (Nick.wc q)).close
        (fun d => (Nat.div_lt_iff_lt_mul (by omega : 0 < q)).mpr
          (by simpa [NN,pow_succ] using d.hj))
    · exact ix.residue (Nick.wc q)
  have hh := repeatM (t := a t) (u := fun (_ : ι) j => q^(j+1)) count T first level
  change b.Moves (fun i => q^(k i)) (a t) (fun i => T i (k i))
  refine Moves.weaken (P := fun i => q^(k i)) hh ?_
  refine ⟨3,fun i => ?_⟩
  change (k i + ∑ j ∈ range (k i), q^(j+1)) + 1 ≤ 3*(q^(k i)+1)
  
  have := levelCost hq (k i)
  omega


/-- One local digit can emit a complete transformed column or one chosen axis bit.
The other state is a running XOR of a fixed bit-valued lookup on each column. -/
def trans (outRadix : ℕ) (emit tag : ℕ → ℕ) (s : ℕ × ℕ) (digit : ℕ) : ℕ × ℕ :=
  (outRadix*s.1 + emit digit, (s.2 + tag digit)%2)

private theorem folded_lt {q r : ℕ} (hq : 0 < q) (hr : r ≤ q)
    {emit tag : ℕ → ℕ} (he : ∀ i < q, emit i < r) (j x : ℕ) :
    (foldDigits q (0,0) (trans r emit tag) j x).1 < q^j ∧
    (foldDigits q (0,0) (trans r emit tag) j x).2 < 2 := by
  induction j generalizing x with
  | zero => simp [foldDigits]
  | succ j ih =>
    obtain ⟨h,_⟩ := ih (x/q)
    have he' := he (x%q) (Nat.mod_lt _ hq)
    change r*_ + emit (x%q) < q^(j+1) ∧ _ < 2
    constructor
    · calc
        _ < r * ((foldDigits q (0,0) (trans r emit tag) j (x/q)).1 + 1) := by
          rw [Nat.mul_succ]; omega
        _ ≤ q * q^j := Nat.mul_le_mul hr h
        _ = _ := (pow_succ' q j).symm
    · exact Nat.mod_lt _ (by decide)

/-- A fixed finite transducer table is compiled into case analysis on its digit. -/
private theorem fixedLookup {κ : Type u} {m : Bool} (c : Bench m κ)
    {q : ℕ} (map : ℕ → ℕ) (digit : κ → ℕ) (hd : ∀ i, digit i < q)
    (h : c.Nick digit) : c.Moves (fun _ => 0) w (fun i => map (digit i)) := by
  apply Can.cases_code (Layout.std q) (q := fun i => (⟨digit i, hd i⟩ : Fin q)) h.close
  intro v
  exact (Can.wc (map v.val)).cy (fun i => by
    have hi := congrArg Fin.val i.property
    simpa using congrArg map hi.symm)

/-- Materialize all transformed addresses (or one selected axis) and their XOR
phases, in the charged RAM of the challenge, with O(q^f) work. -/
theorem transTable {m : Bool} {ι : Type u} {b : Bench m ι} {k : ι → ℕ}
    {q r : ℕ} (hq : 2 ≤ q) (hr : r ≤ q) (emit tag : ℕ → ℕ)
    (he : ∀ i < q, emit i < r) (ht : ∀ i < q, tag i < 2)
    (count : b.Nick k) (capacity : Small b.size (fun i => q^(k i))) :
    b.Moves (fun i => q^(k i)) (a (p w w))
      (fun i => Tape.tab (q^(k i)) (foldDigits q (0,0) (trans r emit tag) (k i))) := by
  apply build hq (t := p w w) (0,0) (trans r emit tag) count capacity
    ((Moves.wc 0).pair (Moves.wc 0))
  intro κ c f x _ small prev digit
  let v := fun i => foldDigits q (0,0) (trans r emit tag) (f i) (x i / q)
  have bv : ∀ i, (v i).1 < q^(f i) ∧ (v i).2 < 2 :=
    fun i => folded_lt (by omega) hr he _ _
  have left : c.Nick (fun i => (v i).1) := ⟨prev.fst, small.mono (fun i =>
    (bv i).1.le.trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _)))⟩
  have right : c.Nick (fun i => (v i).2) := ⟨prev.snd,
    (Small.const _ 2).mono (fun i => (bv i).2.le)⟩
  have hd : ∀ i, x i % q < q := fun i => Nat.mod_lt _ (by omega)
  have E : c.Nick (fun i => emit (x i%q)) :=
    ⟨fixedLookup c emit _ hd digit, (Small.const _ r).mono (fun i => (he _ (hd i)).le)⟩
  have P : c.Nick (fun i => tag (x i%q)) :=
    ⟨fixedLookup c tag _ hd digit, (Small.const _ 2).mono (fun i => (ht _ (hd i)).le)⟩
  exact (((Nick.wc r).mul left).add E).close.pair (((right.add P).residue (Nick.wc 2)).close)

/-- Read two already charged tables in a fresh linear pass. Their construction
is outside the loop. 'op' may use ambient scalars such as the global stride. -/
theorem zipTables {m : Bool} {ι : Type u} {b : Bench m ι} {n : ι → ℕ}
    {s t z : Ty} {x : ι → ℕ → s.T} {y : ι → ℕ → t.T} {out : ι → ℕ → z.T}
    (cap : Small b.size n)
    (left : b.Moves n (a s) (fun i => Tape.tab (n i) (x i)))
    (right : b.Moves n (a t) (fun i => Tape.tab (n i) (y i)))
    (op : ∀ (c : Bench m (During n)) (_h : c.Instant b During.i),
      c.Moves (fun _ => 0) s (fun d => x d.i d.j) →
      c.Moves (fun _ => 0) t (fun d => y d.i d.j) →
      c.Moves (fun _ => 0) z (fun d => out d.i d.j)) :
    b.Moves n (a z) (fun i => Tape.tab (n i) (out i)) := by
  let X := fun i => Tape.tab (n i) (x i)
  let Y := fun i => Tape.tab (n i) (y i)
  let c := b.extend (p (a s) (a t)) (fun i => (X i,Y i))
  have lift : c.Instant b id := Instant.extend _ _
  apply caseM (left.pair right)
  have xy : c.Moves (fun _ => 0) (p (a s) (a t)) (fun i => (X i,Y i)) := cherry _ _
  have sz : c.Nick n := ⟨xy.fst.len cap,cap⟩
  apply arrayNow sz
  let g := Instant.scan c n
  apply op (c.scan n) (g.next lift)
  · exact Moves.pick (fun d => x d.i) (xy.fst.transfer (f := During.i (n := n)) g) (chop sz).close (fun d => d.hj)
  · exact Moves.pick (fun d => y d.i) (xy.snd.transfer (f := During.i (n := n)) g) (chop sz).close (fun d => d.hj)

/-- Gather a fixed list of component-bit projections from every column. The
address is axis-major: concatenate f-bit component words with stride 2^f.
A single per-column bit lookup is XOR-folded alongside the reindexing. -/
def majorRadix (q r : ℕ) (tag : ℕ → ℕ) (f x : ℕ) : List (ℕ → Fin r) → ℕ × ℕ
  | [] => foldDigits q (0,0) (trans 2 (fun _ => 0) tag) f x
  | g :: gs =>
    let high := majorRadix q r tag f x gs
    let low := foldDigits q (0,0) (trans r (fun v => (g v).val) tag) f x
    (high.1*r^f + low.1, high.2)

private theorem major_lt {q r : ℕ} (hq : 2 ≤ q) (hr : r ≤ q) (tag : ℕ → ℕ) (f x : ℕ)
    (gs : List (ℕ → Fin r)) :
    (majorRadix q r tag f x gs).1 < (q^f)^(gs.length+1) := by
  induction gs with
  | nil =>
    simpa [majorRadix] using (folded_lt (q := q) (by omega) hq (emit := fun _ => 0)
      (tag := tag) (fun _ _ => by decide) f x).1
  | cons g gs ih =>
    have low := (folded_lt (q := q) (by omega) hr (emit := fun v => (g v).val)
      (tag := tag) (fun v _ => (g v).isLt) f x).1
    have leq : r^f ≤ q^f := Nat.pow_le_pow_left hr f
    change _ * r^f + _ < (q^f)^(gs.length+1+1)
    rw [pow_succ]
    calc
      _ ≤ (majorRadix q r tag f x gs).1 * q^f + _ :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ leq) _
      _ < ((majorRadix q r tag f x gs).1+1) * q^f := by rw [Nat.succ_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ ih

theorem majorRadixTable {m : Bool} {ι : Type u} {b : Bench m ι} {k : ι → ℕ}
    {q r : ℕ} (hq : 2 ≤ q) (hr : r ≤ q) (tag : ℕ → ℕ) (ht : ∀ i < q, tag i < 2)
    (maps : List (ℕ → Fin r))
    (count : b.Nick k) (capacity : Small b.size (fun i => q^(k i)))
    (stride : b.Nick (fun i => r^(k i))) :
    b.Moves (fun i => q^(k i)) (a (p w w))
      (fun i => Tape.tab (q^(k i)) (fun x => majorRadix q r tag (k i) x maps)) := by
  induction maps with
  | nil => exact transTable hq hq _ tag (fun _ _ => by decide) ht count capacity
  | cons g gs ih =>
    have lo := transTable hq hr (fun v => (g v).val) tag (fun v _ => (g v).isLt)
      ht count capacity
    apply zipTables capacity ih lo
    intro c h a0 a1
    have cap := (capacity.reindex During.i).trans h.covers
    have oldSmall : Small c.size
        (fun d => (majorRadix q r tag (k d.i) d.j gs).1) := by
      obtain ⟨e, he⟩ := cap
      refine ⟨e*(gs.length+1),fun d => ?_⟩
      rw [Nat.pow_mul]
      exact (major_lt hq hr tag (k d.i) d.j gs).le.trans (Nat.pow_le_pow_left (he d) _)
    have newSmall : Small c.size (fun d => (foldDigits q (0,0)
        (trans r (fun v => (g v).val) tag) (k d.i) d.j).1) := cap.mono (fun d =>
      (folded_lt (by omega) hr (fun v _ => (g v).isLt) (k d.i) d.j).1.le)
    have a : c.Nick _ := ⟨a0.fst,oldSmall⟩
    have v : c.Nick _ := ⟨a1.fst,newSmall⟩
    exact ((a.mul (stride.transfer h)).add v).close.pair a0.snd



abbrev major (q : ℕ) := majorRadix q 2

theorem majorTable {m : Bool} {ι : Type u} {b : Bench m ι} {k : ι → ℕ}
    {q : ℕ} (hq : 2 ≤ q) (tag : ℕ → ℕ) (ht : ∀ i < q, tag i < 2)
    (maps : List (ℕ → Fin 2))
    (count : b.Nick k) (capacity : Small b.size (fun i => q^(k i)))
    (stride : b.Nick (fun i => 2^(k i))) :
    b.Moves (fun i => q^(k i)) (a (p w w))
      (fun i => Tape.tab (q^(k i)) (fun x => major q tag (k i) x maps)) :=
  majorRadixTable hq hq tag ht maps count capacity stride

/-- Scatter by a table of target addresses and values. Computing this table
once and retaining it before sow prevents any recomputation per address. -/
theorem applyPermutation {m : Bool} {ι : Type u} {b : Bench m ι} {n : ι → ℕ}
    {t : Ty} (cap : Small b.size n) (dest : ∀ i, Fin (n i) ≃ Fin (n i))
    (entries : ι → ℕ → ℕ × t.T) (out : ι → ℕ → t.T)
    (table : b.Moves n (a (p w t)) (fun i => Tape.tab (n i) (entries i)))
    (addr : ∀ i (j : Fin (n i)), (entries i j).1 = (dest i j).val)
    (val : ∀ i (j : Fin (n i)), (entries i j).2 = out i (dest i j).val) :
    b.Moves n (a t) (fun i => Tape.tab (n i) (out i)) := by
  let T := fun i => Tape.tab (n i) (entries i)
  let c := b.extend (a (p w t)) T
  apply caseM table
  have tr : c.Moves (fun _ => 0) (a (p w t)) T := cherry _ _
  have sz : c.Nick n := ⟨tr.len cap,cap⟩
  have read : (c.scan n).Moves (fun _ => 0) (p w t) (fun d => entries d.i d.j) :=
    Moves.pick (t := p w t) (fun d : During n => entries d.i)
      (tr.transfer (f := During.i (n := n)) (Instant.scan c n)) (chop sz).close
      (fun d => d.hj)
  apply (scatterNow sz entries read).congr
  intro i
  apply Tape.ext_look (b := Tape.tab (n i) (out i)) (by simp) t.blank
  intro a ha
  rw [Tape.len_sow] at ha
  let j := (dest i).symm ⟨a,ha⟩
  have hj : (dest i j).val = a := congrArg Fin.val ((dest i).apply_symm_apply ⟨a,ha⟩)
  rw [Tape.sow_look_written ha j.isLt ((addr i j).trans hj) (by
    intro s hjs hsn h
    have eq : dest i ⟨s,hsn⟩ = dest i j :=
      Fin.ext (((addr i ⟨s,hsn⟩).symm.trans h).trans hj.symm)
    exact (Nat.ne_of_gt hjs) (congrArg Fin.val ((dest i).injective eq)))]
  simp [val i j,hj,Tape.look_tab,ha]

end OAI.PowerSaving.RAM.ColumnTape
#print axioms OAI.PowerSaving.RAM.ColumnTape.majorTable
#print axioms OAI.PowerSaving.RAM.ColumnTape.applyPermutation

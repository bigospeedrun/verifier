import Submission.Work.GFrame.Engine.Level
import Submission.Work.Mixed.Prog.Sem
import Submission.Work.Mixed.Prog.Seq

/-! Merged module written by bos_merge.py for the 500-file limit of the Big O Speedrun
pull-request route.  It is the concatenation, in import order, of the 5 modules below; each one
is copied verbatim after its import header, inside `section` ... `end`, with the scopes it leaves
open closed before that `end`.  Members (module, sha256 of the original file):
* `Submission.Work.Mixed.Prog.CTab` ad34dfea83a3519528c84380fe677cea22a08cd1fc8114fa4de31f4decd6a39f
* `Submission.Work.Mixed.Prog.Route` b0519cc6cc92fd2723ca0ad05283d3f6e3fb1563c5c24fb432f9c1ecb3de2517
* `Submission.Work.Mixed.Prog.Block` c2e03e313e90a1b2a4f603a5668a23cdea2dc6f53dae9b93cb8aae3b254b5ba4
* `Submission.Work.Mixed.Prog.Exit` 81e44a857f2d90ee60ca1967d6996a1cb4c0176cccc787bc777641cfd95883dd
* `Submission.Work.Mixed.Prog.Desc` 207d926879df1bbdc38e9b94686e288e53adf391a71af2515fb8b3729cdb6152
-/

-- bos_merge: begin Submission.Work.Mixed.Prog.CTab
section

/-!
# Mixed engine, R3 program part 2: the class table (agent e-r3prog, 19 Oct 2026)

A class of the lockstep tree holds `NU` units; unit `p` is a word instance at column `c p` with
`2^(ib p)` instances.  Its data is the CLASS TABLE (a tape of units, each a tape of instances,
each the role table of one instance, no leftover bits):

* `ctab X R NU c ib V`  the class table of the element data `V p q : Grain α ρ 0 (c p)`;
* `UnitF NU`, `ElemF NU ib`  the families of units and of elements (instances) of a family of classes;
* `CCtx`              the per-unit tables a class keeps in its environment (columns, powers,
                      XOR tables, `lum` tables), from which every element is a `GRig`;
* `CCtx.erig`         the element `GRig` (column `c p`, no leftover bits);
* `ctab_build`        a class table is rebuilt from per-element role tables in linear work;
* `CCtx.free_letter`  a free letter (`localM`, `shift`, `perm`, `phase`) is one pass over the table.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF
noncomputable section

universe U

section Tab
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- The class table of element data `V`. -/
def ctab (X : Layout α) (R : Layout ρ) (NU : ℕ) (c ib : ℕ → ℕ)
    (V : ∀ p : Fin NU, Bits (ib p) → Grain α ρ 0 (c p)) : Tape (Tape (Tape ℂ)) :=
  (Layout.std NU).tape (fun p => (bits (ib p)).tape (fun q => (fleet X R 0 (c p)).tape (V p q)))

end Tab

section Fam
variable {ι : Type U}

/-- Units of a family of classes. -/
abbrev UnitF (NU : ι → ℕ) := Σ i, Fin (NU i)
/-- Elements (instances of units) of a family of classes. -/
abbrev ElemF (NU : ι → ℕ) (ib : ι → ℕ → ℕ) := Σ u : UnitF NU, Bits (ib u.1 u.2)

end Fam

/-- Tables a class keeps for its units: column, `2^column`, instance bits, `2^instance bits`,
XOR table and `lum` table of the column. -/
structure CCtx {ι : Type U} (m : Bool) (B : ι → ℕ) (s : Ty) (x : ι → T s) (mx : ℕ)
    (n NU : ι → ℕ) (col ib : ι → ℕ → ℕ) : Prop where
  nK : Knows m B s x n
  p2n : Knows m B s x (fun i => 2^(n i))
  nuK : Knows m B s x NU
  imag : Has m B s sc x (fun _ => Complex.I)
  tc : Has m B s (a w) x (fun i => (Layout.std (NU i)).tape (fun p => col i p))
  tpc : Has m B s (a w) x (fun i => (Layout.std (NU i)).tape (fun p => 2^(col i p)))
  tib : Has m B s (a w) x (fun i => (Layout.std (NU i)).tape (fun p => ib i p))
  tpib : Has m B s (a w) x (fun i => (Layout.std (NU i)).tape (fun p => 2^(ib i p)))
  txr : Has m B s (a (a w)) x (fun i => (Layout.std (NU i)).tape (fun p => xorTab (col i p)))
  tlum : Has m B s (a (a sc)) x
    (fun i => (Layout.std (NU i)).tape (fun p => (bits (col i p)).tape (fun y : Bits (col i p) => lum y)))
  big : Small B (fun i => 2^(n i))
  nuS : Small B NU
  fit : ∀ i (p : Fin (NU i)), mx * col i p + ib i p = n i
  mx1 : 1 ≤ mx

namespace CCtx
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {mx : ℕ}
  {n NU : ι → ℕ} {col ib : ι → ℕ → ℕ}
variable (h : CCtx m B s x mx n NU col ib)
include h

/-- The tables survive extending the environment. -/
lemma ext {t : Ty} (y : ι → T t) :
    CCtx m B (p s t) (fun i => (x i, y i)) mx n NU col ib := by
  have F : ∀ {u : Ty} {z : ι → T u}, Has m B s u x z → Has m B (p s t) u (fun i => (x i, y i)) z :=
    fun g => Can.first.then_do g
  exact ⟨F h.nK, F h.p2n, F h.nuK, F h.imag, F h.tc, F h.tpc, F h.tib, F h.tpib, F h.txr, F h.tlum,
    h.big, h.nuS, h.fit, h.mx1⟩

omit h in
/-- A table entry of unit `p`, in the environment of a unit (`(x, p)`). -/
lemma _root_.OAI.PowerSaving.RAM.unit_fetch {t : Ty} (g : ∀ i, Fin (NU i) → T t)
    (ht : Has m B s (a t) x (fun i => (Layout.std (NU i)).tape (g i))) :
    Has m (fun u : UnitF NU => B u.1) (p s w) t (fun u => (x u.1, u.2.val)) (fun u => g u.1 u.2) :=
  Can.fetch (t:=t) (L:=fun u : UnitF NU => Layout.std (NU u.1)) (v:=fun u => g u.1) (i:=fun u => u.2)
    (Can.first.then_do (ht.reindex (fun u : UnitF NU => u.1))) Can.second

lemma two_c_le (i : ι) (p : Fin (NU i)) : 2^(col i p) ≤ 2^(n i) := by
  apply Nat.pow_le_pow_right (by omega)
  have h1 := h.fit i p
  have h2 : col i p ≤ mx * col i p := Nat.le_mul_of_pos_left _ h.mx1
  omega

lemma two_ib_le (i : ι) (p : Fin (NU i)) : 2^(ib i p) ≤ 2^(n i) := by
  apply Nat.pow_le_pow_right (by omega)
  have h1 := h.fit i p
  omega

lemma uBig : Small (fun u : UnitF NU => B u.1) (fun u => 2^(col u.1 u.2)) :=
  (h.big.reindex (fun u : UnitF NU => u.1)).mono (fun u => h.two_c_le u.1 u.2)

lemma uBigIb : Small (fun u : UnitF NU => B u.1) (fun u => 2^(ib u.1 u.2)) :=
  (h.big.reindex (fun u : UnitF NU => u.1)).mono (fun u => h.two_ib_le u.1 u.2)

/-- The environment of an element `((x, p), loc q)` contains the environment of its unit. -/
lemma elem_unit {t : Ty} {y : UnitF NU → T t}
    (g : Has m (fun u : UnitF NU => B u.1) (p s w) t (fun u => (x u.1, u.2.val)) y) :
    Has m (fun e : ElemF NU ib => B e.1.1) (p (p s w) w) t
      (fun e => ((x e.1.1, e.1.2.val), (bits (ib e.1.1 e.1.2)).loc e.2)) (fun e => y e.1) :=
  Can.first.then_do (g.reindex (fun e : ElemF NU ib => e.1))

section Elem
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {cl : Paint} {X : Layout α} {R : Layout ρ}

/-- **Every element of a class table is a `GRig`** (column `c p`, no leftover bits). -/
lemma erig {V : ∀ i (p : Fin (NU i)), Bits (ib i p) → Grain α ρ 0 (col i p)}
    (ct : Has m B s (a (a (a (c cl)))) x (fun i => ctab X R (NU i) (col i) (ib i) (V i))) :
    GRig m (fun e : ElemF NU ib => B e.1.1) (fun e => col e.1.1 e.1.2) (p (p s w) w)
      (fun e => ((x e.1.1, e.1.2.val), (bits (ib e.1.1 e.1.2)).loc e.2)) cl X R 0
      (fun e => V e.1.1 e.1.2 e.2) := by
  have hpc := h.elem_unit (ib:=ib) (unit_fetch _ h.tpc)
  have hc := h.elem_unit (ib:=ib) (unit_fetch _ h.tc)
  have hxr := h.elem_unit (ib:=ib) (unit_fetch _ h.txr)
  have hlm := h.elem_unit (ib:=ib) (unit_fetch _ h.tlum)
  have hbd : Small (fun e : ElemF NU ib => B e.1.1) (fun e => 2^(col e.1.1 e.1.2)) :=
    h.uBig.reindex (fun e : ElemF NU ib => e.1)
  -- the unit's tape of instances, then the instance
  have hu : Has m (fun u : UnitF NU => B u.1) (p s w) (a (a (c cl))) (fun u => (x u.1, u.2.val))
      (fun u => (bits (ib u.1 u.2)).tape (fun q => (fleet X R 0 (col u.1 u.2)).tape (V u.1 u.2 q))) :=
    unit_fetch (m:=m) (B:=B) (s:=s) (x:=x) (NU:=NU) (t:=a (a (c cl)))
      (fun i (p : Fin (NU i)) => (bits (ib i p)).tape (fun q => (fleet X R 0 (col i p)).tape (V i p q))) ct
  have hit : Has m (fun e : ElemF NU ib => B e.1.1) (p (p s w) w) (a (c cl))
      (fun e => ((x e.1.1, e.1.2.val), (bits (ib e.1.1 e.1.2)).loc e.2))
      (fun e => (fleet X R 0 (col e.1.1 e.1.2)).tape (V e.1.1 e.1.2 e.2)) :=
    Can.fetch (t:=a (c cl)) (L:=fun e : ElemF NU ib => bits (ib e.1.1 e.1.2))
      (v:=fun e q => (fleet X R 0 (col e.1.1 e.1.2)).tape (V e.1.1 e.1.2 q)) (i:=fun e => e.2)
      (h.elem_unit hu) Can.second
  have him : Has m (fun e : ElemF NU ib => B e.1.1) (p (p s w) w) sc
      (fun e => ((x e.1.1, e.1.2.val), (bits (ib e.1.1 e.1.2)).loc e.2)) (fun _ => Complex.I) :=
    (Can.first.then_do Can.first).then_do (h.imag.reindex (fun e : ElemF NU ib => e.1.1))
  exact ⟨⟨⟨hpc, hc, hxr, hbd⟩, him, hit⟩, hlm⟩

/-- **Rebuilding a class table** from per-element role tables: linear work. -/
lemma ctab_build {V' : ∀ i (p : Fin (NU i)), Bits (ib i p) → Grain α ρ 0 (col i p)}
    (hel : Can m (fun e : ElemF NU ib => B e.1.1) (p (p s w) w) (a (c cl))
      (fun e => ((x e.1.1, e.1.2.val), (bits (ib e.1.1 e.1.2)).loc e.2))
      (fun e => (fleet X R 0 (col e.1.1 e.1.2)).tape (V' e.1.1 e.1.2 e.2))
      (fun e => R.n * 2^(X.n * col e.1.1 e.1.2))) (hX : X.n = mx) :
    Can m B s (a (a (a (c cl)))) x (fun i => ctab X R (NU i) (col i) (ib i) (V' i))
      (fun i => NU i * 2^(n i)) := by
  -- inner layout: one unit's tape of instances
  have hlen : Knows m (fun u : UnitF NU => B u.1) (p s w) (fun u => (x u.1, u.2.val))
      (fun u => (bits (ib u.1 u.2)).n) := unit_fetch _ h.tpib
  have HI := Can.layout (t:=a (c cl)) (L:=fun u : UnitF NU => bits (ib u.1 u.2))
    (v:=fun u q => (fleet X R 0 (col u.1 u.2)).tape (V' u.1 u.2 q))
    (P:=fun u => R.n * 2^(X.n * col u.1 u.2)) (W:=fun _ => 0) hlen hel h.uBigIb
  have HI' : Can m (fun u : UnitF NU => B u.1) (p s w) (a (a (c cl))) (fun u => (x u.1, u.2.val))
      (fun u => (bits (ib u.1 u.2)).tape (fun q => (fleet X R 0 (col u.1 u.2)).tape (V' u.1 u.2 q)))
      (fun u => (R.n + 1) * 2^(n u.1)) := by
    refine HI.mono (fun u => ?_)
    have hf := h.fit u.1 u.2
    have e1 : 2^(ib u.1 u.2) * (R.n * 2^(X.n * col u.1 u.2)) = R.n * 2^(n u.1) := by
      rw [← hf, hX, pow_add]; ring
    have e2 := h.two_ib_le u.1 u.2
    change 0 + 2^(ib u.1 u.2) + 2^(ib u.1 u.2) * (R.n * 2^(X.n * col u.1 u.2)) ≤ _
    rw [e1]; nlinarith
  have HO := Can.layout (t:=a (a (c cl))) (L:=fun i => Layout.std (NU i))
    (v:=fun i p => (bits (ib i p)).tape (fun q => (fleet X R 0 (col i p)).tape (V' i p q)))
    (P:=fun i => (R.n + 1) * 2^(n i)) (W:=fun _ => 0) h.nuK HI' h.nuS
  refine HO.weaken ⟨R.n + 3, fun i => ?_⟩
  change 0 + NU i + NU i * ((R.n + 1) * 2^(n i)) + 1 ≤ (R.n + 3) * (NU i * 2^(n i) + 1)
  have h1 : 1 ≤ 2^(n i) := Nat.one_le_two_pow
  have h2 : NU i ≤ NU i * 2^(n i) := Nat.le_mul_of_pos_right _ h1
  nlinarith

/-- **A free letter is one pass over the class table.** -/
lemma free_letter {V : ∀ i (p : Fin (NU i)), Bits (ib i p) → Grain α ρ 0 (col i p)}
    (ct : Has m B s (a (a (a (c cl)))) x (fun i => ctab X R (NU i) (col i) (ib i) (V i)))
    (hX : X.n = mx) (mv : GMove α ρ) (hfree : mv.rk? = none) :
    Can m B s (a (a (a (c cl)))) x
      (fun i => ctab X R (NU i) (col i) (ib i) (fun p q => gferry 0 (col i p) mv (V i p q)))
      (fun i => NU i * 2^(n i)) := by
  have G := h.erig ct
  apply h.ctab_build _ hX
  have hn : ∀ e : ElemF NU ib, R.n * 2^(X.n * col e.1.1 e.1.2) = (fleet X R 0 (col e.1.1 e.1.2)).n := by
    intro e; simp [fleet]
  have key : Can m (fun e : ElemF NU ib => B e.1.1) (p (p s w) w) (a (c cl))
      (fun e => ((x e.1.1, e.1.2.val), (bits (ib e.1.1 e.1.2)).loc e.2))
      (fun e => (fleet X R 0 (col e.1.1 e.1.2)).tape (gferry 0 (col e.1.1 e.1.2) mv (V e.1.1 e.1.2 e.2)))
      (fun e => (fleet X R 0 (col e.1.1 e.1.2)).n) := by
    cases mv with
    | old mv =>
      cases mv with
      | localM M => exact G.rig.point_cost M
      | shift l z => exact G.rig.shift_cost l z
      | block l rk z ind => simp [GMove.rk?, GMove.shadow, BMove.rk?] at hfree
    | perm l Gp => exact G.rig.perm_cost l Gp
    | phase l z c' => exact G.phase_cost l z c'
  exact key.mono (fun e => le_of_eq (hn e).symm)

end Elem
end CCtx

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.CTab

-- bos_merge: begin Submission.Work.Mixed.Prog.Route
section

/-!
# Mixed engine, R3 program part 3: routing a block letter to the child class (agent e-r3prog)

A block letter of rank `k` on role `l` turns every unit of the class into ONE job of `2^n`
entries (`blockJob`: the role read through `placeS`, block coordinates low).  The child class
of the lockstep tree receives, for each of its input slots, either such a job of a parent unit
(the slot is FED) or a fresh top vector (the slot is a SOURCE).  This file builds that input
(`gather`) and reads the answers back into the class table (`scatter`).

The routing is abstract here: tables `fl` (fed flag), `pp` (parent unit of a fed slot), `si`
(supply index of a source slot) and `slot` (child slot of a parent unit).  Their values for the
lockstep tree are computed elsewhere.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF
noncomputable section

universe U

/-! ## 1. Arithmetic of `placeS` addresses -/

lemma split3 {F Rr Qq A Bb : ℕ} (hF : F < 2^A) (hR : Rr < 2^Bb) :
    (F + 2^A * Rr + 2^(A+Bb) * Qq) % 2^A = F ∧
    ((F + 2^A * Rr + 2^(A+Bb) * Qq) / 2^A) % 2^Bb = Rr ∧
    (F + 2^A * Rr + 2^(A+Bb) * Qq) / 2^(A+Bb) = Qq := by
  have hA : 0 < 2^A := Nat.two_pow_pos A
  have hB : 0 < 2^Bb := Nat.two_pow_pos Bb
  have e1 : F + 2^A * Rr + 2^(A+Bb) * Qq = F + 2^A * (Rr + 2^Bb * Qq) := by
    rw [pow_add]; ring
  have e2 : (F + 2^A * (Rr + 2^Bb * Qq)) / 2^A = Rr + 2^Bb * Qq := by
    rw [Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt hF, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hF]
  · rw [e1, e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]
  · rw [e1, pow_add, ← Nat.div_div_eq_div_mul, e2, Nat.add_mul_div_left _ _ hB,
      Nat.div_eq_of_lt hR, zero_add]

section Place
variable {α β ρ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {k : ℕ}

/-- The three parts of the address of a job entry. -/
lemma placeS_parts (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (e : Bits n) :
    let qy := (placeS S X' f r n h).symm e
    (bits n).loc e % 2^(k*f) = (bits (k*f)).loc (S.peel 0 f (0, qy.2)).2 ∧
    ((bits n).loc e / 2^(k*f)) % 2^(X'.n*f) = (book X' 0 f).loc (S.peel 0 f (0, qy.2)).1 ∧
    (bits n).loc e / 2^(k*f + X'.n*f) = (bits r).loc qy.1 := by
  intro qy
  have he : e = placeS S X' f r n h (qy.1, qy.2) := by simp [qy]
  have hl := placeS_loc S X' f r n h qy.1 qy.2
  rw [← he] at hl
  rw [hl]
  have hF := (bits (k*f)).bd (S.peel 0 f (0, qy.2)).2
  have hR := (book X' 0 f).bd (S.peel 0 f (0, qy.2)).1
  rw [bits_len] at hF
  rw [book_len, Nat.add_zero] at hR
  exact split3 hF hR

/-- The job of one unit for a block of rank `k` on role `l`: the role read through `placeS`. -/
def blockJob (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (l : ρ) (v : Bits r → Grain α ρ 0 f) : Bits n → ℂ :=
  fun e => v ((placeS S X' f r n h).symm e).1 (l, (0, ((placeS S X' f r n h).symm e).2))

lemma blockJob_placeS (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (l : ρ) (v : Bits r → Grain α ρ 0 f) (q : Bits r) (y : Sky α f) :
    blockJob S X' f r n h l v (placeS S X' f r n h (q, y)) = v q (l, (0, y)) := by
  simp [blockJob]

/-- **The child's answer for a fed slot is the block letter on the parent unit.** -/
lemma blockJob_hlow (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (l : ρ) (v : Bits r → Grain α ρ 0 f) (q : Bits r) (b0 : Bits 0)
    (y : Sky α f) :
    hlow n (k*f) (blockJob S X' f r n h l v) (placeS S X' f r n h (q, y)) =
      ferryM 0 f l (S.lift (kernel (Fin k))) (v q) (l, (b0, y)) := by
  rw [hlow_placeS]
  have hb : b0 = 0 := Subsingleton.elim _ _
  subst hb
  unfold ferryM roleAct
  simp only [if_true]
  congr 1
  funext y'
  rw [blockJob_placeS]

lemma fitk {X : Layout α} (X' : Layout β) (hX' : X'.n + k = X.n) {f r n : ℕ}
    (hf : X.n * f + r = n) : k*f + X'.n*f + r = n := by
  rw [← hf, ← hX', Nat.add_mul]; ring

end Place

/-! ## 2. The child's input -/

section Gather
variable {α β ρ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {k : ℕ}

/-- Input job of child slot `t`: a parent unit's block job if fed, else a supply vector. -/
def cjob (X : Layout α) (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n) (l : ρ)
    {NU n : ℕ} {col ib : ℕ → ℕ} (hfit : ∀ p : Fin NU, X.n * col p + ib p = n)
    (V : ∀ p : Fin NU, Bits (ib p) → Grain α ρ 0 (col p))
    (fl pp si : ℕ → ℕ) (hpp : ∀ t, fl t ≠ 0 → pp t < NU) (sup : ℕ → Bits n → ℂ) (t : ℕ) :
    Bits n → ℂ :=
  if hf : fl t ≠ 0 then
    blockJob S X' (col (pp t)) (ib (pp t)) n (fitk X' hX' (hfit ⟨pp t, hpp t hf⟩)) l (V ⟨pp t, hpp t hf⟩)
  else sup (si t)

end Gather

section GatherRAM
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}
  {n NU : ι → ℕ} {col ib : ι → ℕ → ℕ}
variable {α β ρ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {cl : Paint} {X : Layout α} {R : Layout ρ} {k : ℕ}

/-- Entries of the child's input: slot `t`, entry `e`. -/
abbrev EntF (NJ : ι → ℕ) (n : ι → ℕ) := Σ u : UnitF NJ, Bits (n u.1)

/-- **The child's input** (fed slots from the parent's units, source slots from the supply):
linear work. -/
theorem CCtx.gather (h : CCtx m B s x X.n n NU col ib)
    {V : ∀ i (p : Fin (NU i)), Bits (ib i p) → Grain α ρ 0 (col i p)}
    (ct : Has m B s (a (a (a (c cl)))) x (fun i => ctab X R (NU i) (col i) (ib i) (V i)))
    (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n) (l : ρ)
    {NJ BS : ι → ℕ} {fl pp si : ι → ℕ → ℕ} {sup : ∀ i, ℕ → Bits (n i) → ℂ}
    (hpp : ∀ i t, fl i t ≠ 0 → pp i t < NU i)
    (hsi : ∀ i t, t < NJ i → fl i t = 0 → si i t < BS i)
    (hNJ : Knows m B s x NJ) (hNJs : Small B NJ)
    (tfl : Has m B s (a w) x (fun i => (Layout.std (NJ i)).tape (fun t => fl i t)))
    (tpp : Has m B s (a w) x (fun i => (Layout.std (NJ i)).tape (fun t => pp i t)))
    (tsi : Has m B s (a w) x (fun i => (Layout.std (NJ i)).tape (fun t => si i t)))
    (tsup : Has m B s (a (a (c cl))) x
      (fun i => (Layout.std (BS i)).tape (fun t => (bits (n i)).tape (sup i t)))) :
    Can m B s (a (a (c cl))) x
      (fun i => (Layout.std (NJ i)).tape (fun t => (bits (n i)).tape
        (cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i) t)))
      (fun i => NJ i * 2^(n i)) := by
  let J (i : ι) (t : ℕ) : Bits (n i) → ℂ :=
    cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i) t
  let yE (en : EntF NJ n) : T (p (p s w) w) := ((x en.1.1, en.1.2.val), (bits (n en.1.1)).loc en.2)
  let BE (en : EntF NJ n) := B en.1.1
  -- the environment of an entry contains the slot environment and the class environment
  have hslot : ∀ {t : Ty} {y : UnitF NJ → T t},
      Has m (fun u : UnitF NJ => B u.1) (p s w) t (fun u => (x u.1, u.2.val)) y →
      Has m BE (p (p s w) w) t yE (fun en => y en.1) :=
    fun g => Can.first.then_do (g.reindex (fun en : EntF NJ n => en.1))
  have hcls : ∀ {t : Ty} {y : ι → T t}, Has m B s t x y → Has m BE (p (p s w) w) t yE (fun en => y en.1.1) :=
    fun g => (Can.first.then_do Can.first).then_do (g.reindex (fun en : EntF NJ n => en.1.1))
  have hE : Knows m BE (p (p s w) w) yE (fun en => (bits (n en.1.1)).loc en.2) := Can.second
  have hbig : Small BE (fun en => 2^(n en.1.1)) := h.big.reindex (fun en : EntF NJ n => en.1.1)
  have hEs : Small BE (fun en => (bits (n en.1.1)).loc en.2) :=
    hbig.mono (fun en => ((bits (n en.1.1)).bd en.2).le)
  have hfl : Knows m BE (p (p s w) w) yE (fun en => fl en.1.1 en.1.2) := hslot (unit_fetch _ tfl)
  -- one entry
  have hent : Has m BE (p (p s w) w) (c cl) yE (fun en => J en.1.1 en.1.2 en.2) := by
    apply Can.testz hfl
    · -- source slot
      let K0 := {en : EntF NJ n // fl en.1.1 en.1.2 = 0}
      have hsiK : Knows m (fun κ : K0 => BE κ.1) (p (p s w) w) (fun κ => yE κ.1)
          (fun κ => si κ.1.1.1 κ.1.1.2) :=
        (hslot (unit_fetch _ tsi)).reindex (fun κ : K0 => κ.1)
      let ix (κ : K0) : Fin (BS κ.1.1.1) := ⟨si κ.1.1.1 κ.1.1.2, hsi _ _ κ.1.1.2.2 κ.2⟩
      have hv := Can.fetch (t:=a (c cl)) (L:=fun κ : K0 => Layout.std (BS κ.1.1.1))
        (v:=fun κ j => (bits (n κ.1.1.1)).tape (sup κ.1.1.1 j)) (i:=ix)
        ((hcls tsup).reindex (fun κ : K0 => κ.1)) hsiK
      have hw := Can.fetch (t:=c cl) (L:=fun κ : K0 => bits (n κ.1.1.1))
        (v:=fun κ => sup κ.1.1.1 (ix κ).val) (i:=fun κ => κ.1.2) hv (hE.reindex (fun κ : K0 => κ.1))
      refine hw.cong (fun _ => rfl) (fun κ => ?_)
      change sup κ.1.1.1 (si κ.1.1.1 κ.1.1.2) κ.1.2 = J κ.1.1.1 κ.1.1.2 κ.1.2
      simp only [J, cjob, κ.2, ne_eq, not_true_eq_false, dif_neg, not_false_eq_true]
    · -- fed slot: read the parent unit's role `l` through `placeS`
      let K1 := {en : EntF NJ n // fl en.1.1 en.1.2 ≠ 0}
      let BK (κ : K1) := BE κ.1
      let yK (κ : K1) := yE κ.1
      let i_ (κ : K1) := κ.1.1.1
      let p_ (κ : K1) : Fin (NU (i_ κ)) := ⟨pp (i_ κ) κ.1.1.2, hpp _ _ κ.2⟩
      let fit_ (κ : K1) := fitk X' hX' (h.fit (i_ κ) (p_ κ))
      let PL (κ : K1) := placeS S X' (col (i_ κ) (p_ κ)) (ib (i_ κ) (p_ κ)) (n (i_ κ)) (fit_ κ)
      let qy (κ : K1) := (PL κ).symm κ.1.2
      let j (κ : K1) : ElemF NU ib := ⟨⟨i_ κ, p_ κ⟩, (qy κ).1⟩
      have hppK : Knows m BK (p (p s w) w) yK (fun κ => (p_ κ).val) :=
        (hslot (unit_fetch _ tpp)).reindex (fun κ : K1 => κ.1)
      have hpcK : Knows m BK (p (p s w) w) yK (fun κ => 2^(col (i_ κ) (p_ κ))) :=
        Can.fetch (t:=w) (L:=fun κ : K1 => Layout.std (NU (i_ κ)))
          (v:=fun κ q => 2^(col (i_ κ) q)) (i:=p_)
          ((hcls h.tpc).reindex (fun κ : K1 => κ.1)) hppK
      have hcbig : Small BK (fun κ => 2^(col (i_ κ) (p_ κ))) :=
        (hbig.reindex (fun κ : K1 => κ.1)).mono (fun κ => h.two_c_le (i_ κ) (p_ κ))
      have hXc : Knows m BK (p (p s w) w) yK (fun κ => 2^(k * col (i_ κ) (p_ κ) +
          X'.n * col (i_ κ) (p_ κ))) :=
        (hpcK.wpow_fixed X.n hcbig).cong (fun _ => rfl) (fun κ => by
          rw [← pow_mul, ← hX']; ring_nf)
      have hq : Knows m BK (p (p s w) w) yK (fun κ => (bits (ib (i_ κ) (p_ κ))).loc (qy κ).1) :=
        ((hE.reindex (fun κ : K1 => κ.1)).dvdW hXc (hEs.reindex (fun κ : K1 => κ.1))).cong
          (fun _ => rfl) (fun κ => (placeS_parts S X' _ _ _ (fit_ κ) κ.1.2).2.2)
      have hx0 : Has m BE (p (p s w) w) s yE (fun en => x en.1.1) :=
        Can.first.then_do Can.first
      have hxK : Has m BK (p (p s w) w) s yK (fun κ => x (i_ κ)) :=
        hx0.reindex (fun κ : K1 => κ.1)
      have g : Has m (fun κ => B (j κ).1.1) (p (p s w) w) (p (p s w) w) yK
          (fun κ => ((x (j κ).1.1, (j κ).1.2.val), (bits (ib (j κ).1.1 (j κ).1.2)).loc (j κ).2)) :=
        (hxK.pair hppK).pair hq
      have G1 := (h.erig ct).gather j yK g
      have hk1 : Knows m BK (p (p s w) w) yK (fun κ => 2^(k * col (i_ κ) (p_ κ))) :=
        G1.rig.gear.powerB k
      have hk2 : Knows m BK (p (p s w) w) yK (fun κ => 2^(X'.n * col (i_ κ) (p_ κ))) :=
        G1.rig.gear.powerB X'.n
      have hfib : Knows m BK (p (p s w) w) yK
          (fun κ => (bits (k * col (i_ κ) (p_ κ))).loc (S.peel 0 (col (i_ κ) (p_ κ)) (0, (qy κ).2)).2) :=
        ((hE.reindex (fun κ : K1 => κ.1)).modW hk1 (hEs.reindex (fun κ : K1 => κ.1))).cong
          (fun _ => rfl) (fun κ => (placeS_parts S X' _ _ _ (fit_ κ) κ.1.2).1)
      have hrest : Knows m BK (p (p s w) w) yK
          (fun κ => (book X' 0 (col (i_ κ) (p_ κ))).loc (S.peel 0 (col (i_ κ) (p_ κ)) (0, (qy κ).2)).1) :=
        (((hE.reindex (fun κ : K1 => κ.1)).dvdW hk1 (hEs.reindex (fun κ : K1 => κ.1))).modW hk2
          ((hEs.reindex (fun κ : K1 => κ.1)).div)).cong
          (fun _ => rfl) (fun κ => (placeS_parts S X' _ _ _ (fit_ κ) κ.1.2).2.1)
      have hgrid := G1.rig.gear.to_gridB X 0 S X'
        (fun κ => S.peel 0 (col (i_ κ) (p_ κ)) (0, (qy κ).2)) hrest hfib
      have hb : Knows m BK (p (p s w) w) yK
          (fun κ => (book X 0 (col (i_ κ) (p_ κ))).loc ((0 : Bits 0), (qy κ).2)) :=
        hgrid.cong (fun _ => rfl) (fun κ => by rw [Equiv.symm_apply_apply])
      have hr := G1.rig.read (fun κ => (l, ((0 : Bits 0), (qy κ).2))) (Can.wc (R.loc l)) hb
      refine hr.cong (fun _ => rfl) (fun κ => ?_)
      change V (i_ κ) (p_ κ) (qy κ).1 (l, (0, (qy κ).2)) = J κ.1.1.1 κ.1.1.2 κ.1.2
      simp only [J, cjob, dif_pos κ.2]
      rfl
  -- inner layout over the entries of one slot, then outer layout over the slots
  have hlen : Knows m (fun u : UnitF NJ => B u.1) (p s w) (fun u => (x u.1, u.2.val))
      (fun u => (bits (n u.1)).n) :=
    Can.first.then_do (h.p2n.reindex (fun u : UnitF NJ => u.1))
  have HI := Can.layout (t:=c cl) (L:=fun u : UnitF NJ => bits (n u.1))
    (v:=fun u e => J u.1 u.2 e) (P:=fun _ => 0) (W:=fun _ => 0) hlen
    (hent.mono (fun _ => Nat.zero_le _)) (h.big.reindex (fun u : UnitF NJ => u.1))
  have HO := Can.layout (t:=a (c cl)) (L:=fun i => Layout.std (NJ i))
    (v:=fun i t => (bits (n i)).tape (J i t)) (P:=fun i => 2^(n i)) (W:=fun _ => 0) hNJ
    (HI.mono (fun u => by simp)) hNJs
  refine HO.weaken ⟨3, fun i => ?_⟩
  change 0 + NJ i + NJ i * 2^(n i) + 1 ≤ 3 * (NJ i * 2^(n i) + 1)
  have h1 : 1 ≤ 2^(n i) := Nat.one_le_two_pow
  have h2 : NJ i ≤ NJ i * 2^(n i) := Nat.le_mul_of_pos_right _ h1
  omega

end GatherRAM

section ScatterRAM
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s}
  {n NU : ι → ℕ} {col ib : ι → ℕ → ℕ}
variable {α β ρ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {cl : Paint} {X : Layout α} {R : Layout ρ} {k : ℕ}

/-- **Reading the child's answers back** into the class table: role `l` of unit `p` comes from
child slot `slot p` (read through `placeS`), the other roles are kept.  Linear work. -/
theorem CCtx.scatter (h : CCtx m B s x X.n n NU col ib)
    {V : ∀ i (p : Fin (NU i)), Bits (ib i p) → Grain α ρ 0 (col i p)}
    (ct : Has m B s (a (a (a (c cl)))) x (fun i => ctab X R (NU i) (col i) (ib i) (V i)))
    (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n) (l : ρ)
    {NJ : ι → ℕ} {slot : ι → ℕ → ℕ} {Y : ∀ i, ℕ → Bits (n i) → ℂ}
    (hslot : ∀ i (p : Fin (NU i)), slot i p < NJ i)
    (tslot : Has m B s (a w) x (fun i => (Layout.std (NU i)).tape (fun p => slot i p)))
    (tout : Has m B s (a (a (c cl))) x
      (fun i => (Layout.std (NJ i)).tape (fun t => (bits (n i)).tape (Y i t))))
    (hY : ∀ i (p : Fin (NU i)) (q : Bits (ib i p)) (y : Sky α (col i p)),
      Y i (slot i p) (placeS S X' (col i p) (ib i p) (n i) (fitk X' hX' (h.fit i p)) (q, y)) =
        ferryM 0 (col i p) l (S.lift (kernel (Fin k))) (V i p q) (l, (0, y))) :
    Can m B s (a (a (a (c cl)))) x
      (fun i => ctab X R (NU i) (col i) (ib i)
        (fun p q => ferryM 0 (col i p) l (S.lift (kernel (Fin k))) (V i p q)))
      (fun i => NU i * 2^(n i)) := by
  have G := h.erig ct
  apply h.ctab_build _ rfl
  let yE (e : ElemF NU ib) : T (p (p s w) w) :=
    ((x e.1.1, e.1.2.val), (bits (ib e.1.1 e.1.2)).loc e.2)
  let BE (e : ElemF NU ib) := B e.1.1
  have hel : Can m BE (p (p s w) w) (a (c cl)) yE
      (fun e => (fleet X R 0 (col e.1.1 e.1.2)).tape
        (ferryM 0 (col e.1.1 e.1.2) l (S.lift (kernel (Fin k))) (V e.1.1 e.1.2 e.2)))
      (fun e => (fleet X R 0 (col e.1.1 e.1.2)).n) := by
    refine G.rig.chart _ ?_
    -- one beach of one element
    let D := Σ e : ElemF NU ib, Beach α ρ 0 (col e.1.1 e.1.2)
    let yD (d : D) : T (p (p (p s w) w) w) := (yE d.1, (fleet X R 0 (col d.1.1.1 d.1.1.2)).loc d.2)
    let BD (d : D) := BE d.1
    have GD := G.rig.gather (fun d : D => d.1) yD (t:=p (p (p s w) w) w) Can.first
    obtain ⟨hl, hk⟩ := GD.addrs (fun d => d.2) Can.second
    have hbD : Has m BD (p (p (p s w) w) w) (c cl) yD (fun d => V d.1.1.1 d.1.1.2 d.1.2 d.2) :=
      GD.read (fun d => d.2) hl hk
    apply Can.cases_code (q:=fun d : D => d.2.1) R hl
    intro r'
    by_cases hr : r' = l
    · -- role `l`: from the child's answer
      let K := {d : D // d.2.1 = r'}
      let BK (κ : K) := BD κ.1
      have GK := GD.gather (fun κ : K => κ.1) (fun κ => yD κ.1) (t:=p (p (p s w) w) w) Can.id
      obtain ⟨hrest, hfib⟩ := GK.gear.from_gridB X 0 S X' (fun κ => κ.1.2.2)
        (hk.reindex (fun κ : K => κ.1))
      have hsU : Knows m (fun u : UnitF NU => B u.1) (p s w) (fun u => (x u.1, u.2.val))
          (fun u => slot u.1 u.2) := unit_fetch _ tslot
      have hsE : Knows m BE (p (p s w) w) yE (fun e => slot e.1.1 e.1.2) :=
        Can.first.then_do (hsU.reindex (fun e : ElemF NU ib => e.1))
      have hsD : Knows m BD (p (p (p s w) w) w) yD (fun d => slot d.1.1.1 d.1.1.2) :=
        Can.first.then_do (hsE.reindex (fun d : D => d.1))
      have hslotK : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1)
          (fun κ => slot κ.1.1.1.1 κ.1.1.1.2) := hsD.reindex (fun κ : K => κ.1)
      have hqD : Knows m BD (p (p (p s w) w) w) yD (fun d => (bits (ib d.1.1.1 d.1.1.2)).loc d.1.2) :=
        Can.first.then_do Can.second
      have hq : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1)
          (fun κ => (bits (ib κ.1.1.1.1 κ.1.1.1.2)).loc κ.1.1.2) := hqD.reindex (fun κ : K => κ.1)
      have hk1 : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1)
          (fun κ => 2^(k * col κ.1.1.1.1 κ.1.1.1.2)) := GK.gear.powerB k
      have hk3 : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1)
          (fun κ => 2^(k * col κ.1.1.1.1 κ.1.1.1.2 + X'.n * col κ.1.1.1.1 κ.1.1.1.2)) :=
        (GK.gear.powerB X.n).cong (fun _ => rfl) (fun κ => by rw [← hX']; ring_nf)
      have hbig : Small BK (fun κ => 2^(n κ.1.1.1.1)) :=
        h.big.reindex (fun κ : K => κ.1.1.1.1)
      have hcb : Small BK (fun κ => 2^(col κ.1.1.1.1 κ.1.1.1.2)) :=
        hbig.mono (fun κ => h.two_c_le _ _)
      have hs1 : Small BK (fun κ => 2^(k * col κ.1.1.1.1 κ.1.1.1.2)) :=
        GK.gear.boundB k
      have hs3 : Small BK (fun κ => 2^(k * col κ.1.1.1.1 κ.1.1.1.2 + X'.n * col κ.1.1.1.1 κ.1.1.1.2)) :=
        (GK.gear.boundB X.n).mono (fun κ => le_of_eq (by rw [← hX']; ring_nf))
      have hsr : Small BK (fun κ => (book X' 0 (col κ.1.1.1.1 κ.1.1.1.2)).loc
          (S.peel 0 (col κ.1.1.1.1 κ.1.1.1.2) κ.1.2.2).1) :=
        (GK.gear.grid_small X' 0).mono (fun κ => ((book X' 0 _).bd _).le)
      have hsq : Small BK (fun κ => (bits (ib κ.1.1.1.1 κ.1.1.1.2)).loc κ.1.1.2) :=
        hbig.mono (fun κ => le_trans ((bits _).bd _).le (h.two_ib_le _ _))
      have hsf : Small BK (fun κ => (bits (k * col κ.1.1.1.1 κ.1.1.1.2)).loc
          (S.peel 0 (col κ.1.1.1.1 κ.1.1.1.2) κ.1.2.2).2) :=
        hs1.mono (fun κ => ((bits _).bd _).le)
      -- the address inside the child's job
      have haddr : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1)
          (fun κ => (bits (k * col κ.1.1.1.1 κ.1.1.1.2)).loc
              (S.peel 0 (col κ.1.1.1.1 κ.1.1.1.2) κ.1.2.2).2 +
            2^(k * col κ.1.1.1.1 κ.1.1.1.2) * (book X' 0 (col κ.1.1.1.1 κ.1.1.1.2)).loc
              (S.peel 0 (col κ.1.1.1.1 κ.1.1.1.2) κ.1.2.2).1 +
            2^(k * col κ.1.1.1.1 κ.1.1.1.2 + X'.n * col κ.1.1.1.1 κ.1.1.1.2) *
              (bits (ib κ.1.1.1.1 κ.1.1.1.2)).loc κ.1.1.2) :=
        (hfib.plus (hk1.times hrest hs1 hsr) hsf (hs1.mul hsr)).plus (hk3.times hq hs3 hsq)
          (hsf.add (hs1.mul hsr)) (hs3.mul hsq)
      let jq (κ : K) := κ.1.1.2
      let jy (κ : K) := κ.1.2.2.2
      let PL (κ : K) := placeS S X' (col κ.1.1.1.1 κ.1.1.1.2) (ib κ.1.1.1.1 κ.1.1.1.2)
        (n κ.1.1.1.1) (fitk X' hX' (h.fit κ.1.1.1.1 κ.1.1.1.2))
      have haddr' : Knows m BK (p (p (p s w) w) w) (fun κ => yD κ.1)
          (fun κ => (bits (n κ.1.1.1.1)).loc (PL κ (jq κ, jy κ))) := by
        refine haddr.cong (fun _ => rfl) (fun κ => ?_)
        rw [placeS_loc]
        have hb0 : κ.1.2.2 = ((0 : Bits 0), jy κ) := Prod.ext (Subsingleton.elim _ _) rfl
        rw [hb0]
      have hoU : Has m (fun u : UnitF NU => B u.1) (p s w) (a (a (c cl))) (fun u => (x u.1, u.2.val))
          (fun u => (Layout.std (NJ u.1)).tape (fun t => (bits (n u.1)).tape (Y u.1 t))) :=
        Can.first.then_do (tout.reindex (fun u : UnitF NU => u.1))
      have hoE : Has m BE (p (p s w) w) (a (a (c cl))) yE
          (fun e => (Layout.std (NJ e.1.1)).tape (fun t => (bits (n e.1.1)).tape (Y e.1.1 t))) :=
        Can.first.then_do (hoU.reindex (fun e : ElemF NU ib => e.1))
      have hoD : Has m BD (p (p (p s w) w) w) (a (a (c cl))) yD
          (fun d => (Layout.std (NJ d.1.1.1)).tape (fun t => (bits (n d.1.1.1)).tape (Y d.1.1.1 t))) :=
        Can.first.then_do (hoE.reindex (fun d : D => d.1))
      have hI := hoD.reindex (fun κ : K => κ.1)
      have hJ := Can.fetch (t:=a (c cl)) (L:=fun κ : K => Layout.std (NJ κ.1.1.1.1))
        (v:=fun κ t => (bits (n κ.1.1.1.1)).tape (Y κ.1.1.1.1 t))
        (i:=fun κ => (⟨slot κ.1.1.1.1 κ.1.1.1.2, hslot _ _⟩ : Fin (NJ κ.1.1.1.1))) hI hslotK
      have hv := Can.fetch (t:=c cl) (L:=fun κ : K => bits (n κ.1.1.1.1))
        (v:=fun κ => Y κ.1.1.1.1 (slot κ.1.1.1.1 κ.1.1.1.2)) (i:=fun κ => PL κ (jq κ, jy κ)) hJ haddr'
      refine hv.cong (fun _ => rfl) (fun κ => ?_)
      change Y κ.1.1.1.1 (slot κ.1.1.1.1 κ.1.1.1.2) (PL κ (jq κ, jy κ)) =
        ferryM 0 _ l (S.lift (kernel (Fin k))) (V κ.1.1.1.1 κ.1.1.1.2 κ.1.1.2) κ.1.2
      rw [hY]
      have hd : κ.1.2 = (l, ((0 : Bits 0), jy κ)) :=
        Prod.ext (κ.2.trans hr) (Prod.ext (Subsingleton.elim _ _) rfl)
      rw [hd]
    · -- other roles: unchanged
      refine (hbD.reindex (fun κ : {d : D // d.2.1 = r'} => κ.1)).cong (fun _ => rfl) (fun κ => ?_)
      have H : κ.1.2.1 ≠ l := fun hh => hr (κ.2.symm.trans hh)
      simp only [ferryM, roleAct, H, ite_false, Prod.mk.eta]
  refine hel.mono (fun e => le_of_eq ?_)
  simp [fleet]

end ScatterRAM

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.Route

-- bos_merge: begin Submission.Work.Mixed.Prog.Block
section

/-!
# Mixed engine, R3 program part 4: one block letter of a class = ONE call (agent e-r3prog)

The handler of the lockstep program has ONE port for top jobs and classes:

* `portIn cl`  = `(n, I, kind, μ, o, own jobs, supply)` (`kind = 0`: top job; `kind = h+1`: class of
                 height `h`; `μ` its multiplier; `o` the supply offset of its subtree);
* `portOut cl` = `(own jobs answered, consumed supply answered, sizes of the consumed supply)`.

`CCtx.block_letter`: gather the child's input, call, read the answers back.  Work linear in the
class and in the child's input; charge = the child's cost.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF
noncomputable section

universe U

/-- A tape of jobs (each job a tape of `2^n` entries). -/
abbrev jobsT (cl : Paint) : Ty := a (a (c cl))
/-- The input of every call: `(n, I, kind, μ, o, own jobs, supply)`. -/
abbrev portIn (cl : Paint) : Ty := p w (p sc (p w (p w (p w (p (jobsT cl) (jobsT cl))))))
/-- The output of every call: `(own jobs answered, consumed supply answered, consumed sizes)`. -/
abbrev portOut (cl : Paint) : Ty := p (jobsT cl) (p (jobsT cl) (a w))
abbrev portM (cl : Paint) : Port := some (portIn cl, portOut cl)

/-- An input value of the port. -/
def mkIn (cl : Paint) (n kind μ o : ℕ) (own sup : Tape (Tape ℂ)) : T (portIn cl) :=
  (n, Complex.I, kind, μ, o, own, sup)

/-- A tape of jobs from a family of job functions. -/
def jobsTape (n N : ℕ) (J : ℕ → Bits n → ℂ) : Tape (Tape ℂ) :=
  (Layout.std N).tape (fun t => (bits n).tape (J t))

section Block
variable {α β ρ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {k : ℕ}

lemma blockJob_congr (X : Layout α) (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n)
    (l : ρ) {NU n : ℕ} {col ib : ℕ → ℕ} (hfit : ∀ p : Fin NU, X.n * col p + ib p = n)
    (V : ∀ p : Fin NU, Bits (ib p) → Grain α ρ 0 (col p)) (p p' : Fin NU) (hp : p = p') :
    blockJob S X' (col p) (ib p) n (fitk X' hX' (hfit p)) l (V p) =
      blockJob S X' (col p') (ib p') n (fitk X' hX' (hfit p')) l (V p') := by
  subst hp; rfl

/-- A fed slot whose parent unit is `p` carries the block job of `p`. -/
lemma cjob_fed (X : Layout α) (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n)
    (l : ρ) {NU n : ℕ} {col ib : ℕ → ℕ} (hfit : ∀ p : Fin NU, X.n * col p + ib p = n)
    (V : ∀ p : Fin NU, Bits (ib p) → Grain α ρ 0 (col p))
    (fl pp si : ℕ → ℕ) (hpp : ∀ t, fl t ≠ 0 → pp t < NU) (sup : ℕ → Bits n → ℂ) (t : ℕ)
    (p : Fin NU) (hf : fl t ≠ 0) (hpt : pp t = p) :
    cjob X S X' hX' l hfit V fl pp si hpp sup t =
      blockJob S X' (col p) (ib p) n (fitk X' hX' (hfit p)) l (V p) := by
  unfold cjob
  rw [dif_pos hf]
  exact blockJob_congr X S X' hX' l hfit V ⟨pp t, hpp t hf⟩ p (Fin.ext hpt)

end Block

section BlockRAM
variable {ι : Type U} {m : Bool} {cl : Paint} {b : Bank (portM cl) ι} {s : Ty} {x : ι → T s}
  {n NU : ι → ℕ} {col ib : ι → ℕ → ℕ}
variable {α β ρ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {X : Layout α} {R : Layout ρ} {k : ℕ}

/-- **One block letter of a class: gather, ONE call, read back.** -/
theorem CCtx.block_letter (h : CCtx m b.B s x X.n n NU col ib)
    {V : ∀ i (p : Fin (NU i)), Bits (ib i p) → Grain α ρ 0 (col i p)}
    (ct : Has m b.B s (a (a (a (c cl)))) x (fun i => ctab X R (NU i) (col i) (ib i) (V i)))
    (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n) (l : ρ)
    {NJ BS kd μ o : ι → ℕ} {fl pp si slot sz : ι → ℕ → ℕ} {sup : ∀ i, ℕ → Bits (n i) → ℂ}
    (hpp : ∀ i t, fl i t ≠ 0 → pp i t < NU i)
    (hsi : ∀ i t, t < NJ i → fl i t = 0 → si i t < BS i)
    (hslot : ∀ i (p : Fin (NU i)), slot i p < NJ i ∧ fl i (slot i p) ≠ 0 ∧ pp i (slot i p) = p ∧
      sz i (slot i p) = k * col i p)
    (hNJ : Knows m b.B s x NJ) (hNJs : Small b.B NJ)
    (tfl : Has m b.B s (a w) x (fun i => (Layout.std (NJ i)).tape (fun t => fl i t)))
    (tpp : Has m b.B s (a w) x (fun i => (Layout.std (NJ i)).tape (fun t => pp i t)))
    (tsi : Has m b.B s (a w) x (fun i => (Layout.std (NJ i)).tape (fun t => si i t)))
    (tslot : Has m b.B s (a w) x (fun i => (Layout.std (NU i)).tape (fun p => slot i p)))
    (tsup : Has m b.B s (jobsT cl) x (fun i => jobsTape (n i) (BS i) (sup i)))
    (hkd : Knows m b.B s x kd) (hμ : Knows m b.B s x μ) (ho : Knows m b.B s x o)
    {ACC : ι → Tape (Tape ℂ)} {SZ : ι → Tape ℕ} {τ : ι → ℕ}
    (hk : ∀ i, (b.use i (mkIn cl (n i) (kd i) (μ i) (o i)
        (jobsTape (n i) (NJ i) (cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i)))
        (jobsTape (n i) (BS i) (sup i)))).OK
      (jobsTape (n i) (NJ i) (fun t => hlow (n i) (sz i t)
          (cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i) t)),
        ACC i, SZ i) (τ i) (b.ext i)) :
    Able m b s (p (a (a (a (c cl)))) (portOut cl)) x
      (fun i => (ctab X R (NU i) (col i) (ib i)
          (fun p q => ferryM 0 (col i p) l (S.lift (kernel (Fin k))) (V i p q)),
        (jobsTape (n i) (NJ i) (fun t => hlow (n i) (sz i t)
          (cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i) t)),
        ACC i, SZ i)))
      (fun i => NJ i * 2^(n i) + NU i * 2^(n i)) τ := by
  -- the child's input, then the call
  have HG := h.gather ct S X' hX' l hpp hsi hNJ hNJs tfl tpp tsi tsup
  have Hin : Can m b.B s (portIn cl) x
      (fun i => mkIn cl (n i) (kd i) (μ i) (o i)
        (jobsTape (n i) (NJ i) (cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i)))
        (jobsTape (n i) (BS i) (sup i)))
      (fun i => NJ i * 2^(n i)) :=
    (h.nK.mono (fun _ => Nat.zero_le _)).pair ((h.imag.mono (fun _ => Nat.zero_le _)).pair
      ((hkd.mono (fun _ => Nat.zero_le _)).pair ((hμ.mono (fun _ => Nat.zero_le _)).pair
        ((ho.mono (fun _ => Nat.zero_le _)).pair (HG.pair (tsup.mono (fun _ => Nat.zero_le _)))))))
  have Hcall := (Able.of_can (b:=b) Hin).comp (Able.use_call (m:=m) (b:=b) hk)
  -- read back
  let outp (i : ι) : T (portOut cl) :=
    (jobsTape (n i) (NJ i) (fun t => hlow (n i) (sz i t)
      (cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i) t)), ACC i, SZ i)
  have h' := h.ext outp
  have F : ∀ {u : Ty} {z : ι → T u}, Has m b.B s u x z → Has m b.B (p s (portOut cl)) u (fun i => (x i, outp i)) z :=
    fun g => Can.first.then_do g
  have hY : ∀ i (p : Fin (NU i)) (q : Bits (ib i p)) (y : Sky α (col i p)),
      hlow (n i) (sz i (slot i p))
        (cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i) (slot i p))
        (placeS S X' (col i p) (ib i p) (n i) (fitk X' hX' (h'.fit i p)) (q, y)) =
      ferryM 0 (col i p) l (S.lift (kernel (Fin k))) (V i p q) (l, (0, y)) := by
    intro i p q y
    obtain ⟨_, hf, hpt, hsz⟩ := hslot i p
    rw [cjob_fed X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i) (slot i p) p hf hpt,
      hsz]
    exact blockJob_hlow S X' _ _ _ _ l (V i p) q 0 y
  have tout : Has m b.B (p s (portOut cl)) (jobsT cl) (fun i => (x i, outp i))
      (fun i => jobsTape (n i) (NJ i) (fun t => hlow (n i) (sz i t)
        (cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i) t))) :=
    Can.fst Can.second
  have HS := h'.scatter (Y:=fun i t => hlow (n i) (sz i t)
      (cjob X S X' hX' l (h.fit i) (V i) (fl i) (pp i) (si i) (hpp i) (sup i) t))
    (F ct) S X' hX' l (fun i p => (hslot i p).1) (F tslot) tout hY
  have Hout := Able.of_can (b:=b) (HS.pair (Can.second.mono (fun _ => Nat.zero_le _)))
  refine (Hcall.save Hout).weaken (Dom.of_le (fun i => ?_)) (fun i => by simp)
  simp

end BlockRAM

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.Block

-- bos_merge: begin Submission.Work.Mixed.Prog.Exit
section

/-!
# Mixed engine, R3 program part 5: the exits of a leaf class (agent e-r3prog)

In a leaf class every unit has the same column `c0`.  A block letter of rank `k` makes ONE job per
unit (`2^n` entries, `k*c0` H-bits low); the `NU` jobs are cut into `NU * 2^(n - k*c0)` vectors of
`2^(k*c0)` entries and handed to ONE fresh top call `Do(k*c0, NU * 2^(n - k*c0))`
(rl-prove Lemma D).

* `hlow_catB`        H on the low `k` bits of `catB (x, y)` is `ripple k` in `x` for each `y`;
* `toVec`, `fromVec`  reshaping jobs into vectors and back (`can_toVec`, `can_fromVec`);
* `CCtx.exit_letter` gather (all slots fed), reshape, ONE top call, reshape, read back.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF
noncomputable section

universe U

/-- **H on the low bits of a split vector.** -/
lemma hlow_catB (k b : ℕ) (v : Bits (k+b) → ℂ) (x : Bits k) (y : Bits b) :
    hlow (k+b) k v (catB k b (x, y)) = ripple k (fun x' => v (catB k b (x', y))) x := by
  unfold hlow ripple
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (catB k b), Fintype.sum_prod_type]
  simp_rw [maskK_catB]
  apply Finset.sum_congr rfl
  intro x' _
  rw [Finset.sum_eq_single y]
  · simp
  · intro y' _ hy; rw [if_neg (Ne.symm hy)]; simp
  · intro hh; exact absurd (Finset.mem_univ _) hh

lemma hlow_castB_catB (n k : ℕ) (hk : k ≤ n) (v : Bits n → ℂ) (x : Bits k) (y : Bits (n-k)) :
    hlow n k v (castB (Nat.add_sub_cancel' hk) (catB k (n-k) (x, y))) =
      ripple k (fun x' => v (castB (Nat.add_sub_cancel' hk) (catB k (n-k) (x', y)))) x := by
  have H := hlow_catB k (n-k) (fun z => v (castB (Nat.add_sub_cancel' hk) z)) x y
  have e : ∀ (m : ℕ) (hm : k + (n-k) = m) (u : Bits m → ℂ) (z : Bits (k + (n-k))),
      hlow m k u (castB hm z) = hlow (k + (n-k)) k (fun z' => u (castB hm z')) z := by
    intro m hm u z; subst hm; rfl
  rw [e n _ v]
  exact H

/-- An element of `Bits b` from an address (taken modulo `2^b`). -/
def bitsOf (b j : ℕ) : Bits b := (bits b).atFin ⟨j % 2^b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩

lemma bitsOf_loc (b j : ℕ) : (bits b).loc (bitsOf b j) = j % 2^b := by
  unfold bitsOf; rw [Layout.loc_atFin]

lemma bitsOf_of_loc (b : ℕ) (y : Bits b) : bitsOf b ((bits b).loc y) = y := by
  apply (bits b).inj
  rw [bitsOf_loc, Nat.mod_eq_of_lt (by have := (bits b).bd y; rwa [bits_len] at this)]

/-- Jobs (`2^n` entries, H on the low `k` bits) cut into vectors of `2^k` entries:
vector `t = p * 2^(n-k) + loc y` of job `p`. -/
def toVec (n k : ℕ) (hk : k ≤ n) (J : ℕ → Bits n → ℂ) (t : ℕ) : Bits k → ℂ :=
  fun x => J (t / 2^(n-k)) (castB (Nat.add_sub_cancel' hk) (catB k (n-k) (x, bitsOf (n-k) t)))

/-- Vectors put back into jobs. -/
def fromVec (n k : ℕ) (Y : ℕ → Bits k → ℂ) (p : ℕ) : Bits n → ℂ :=
  fun e => Y (p * 2^(n-k) + (bits n).loc e / 2^k) (bitsOf k ((bits n).loc e))

lemma loc_castB_catB (n k : ℕ) (hk : k ≤ n) (x : Bits k) (y : Bits (n-k)) :
    (bits n).loc (castB (Nat.add_sub_cancel' hk) (catB k (n-k) (x, y))) =
      (bits k).loc x + 2^k * (bits (n-k)).loc y := by
  rw [castB_loc, catB_loc]

/-- The exits answered and put back are `hlow` of the jobs. -/
lemma fromVec_ripple (n k : ℕ) (hk : k ≤ n) (J : ℕ → Bits n → ℂ) (p : ℕ) (e : Bits n) :
    fromVec n k (fun t => ripple k (toVec n k hk J t)) p e = hlow n k (J p) e := by
  -- write `e` as a split vector
  obtain ⟨⟨x, y⟩, hxy⟩ : ∃ z : Bits k × Bits (n-k),
      castB (Nat.add_sub_cancel' hk) (catB k (n-k) z) = e :=
    ⟨(catB k (n-k)).symm ((castB (Nat.add_sub_cancel' hk)).symm e), by simp⟩
  subst hxy
  rw [hlow_castB_catB n k hk (J p) x y]
  unfold fromVec toVec
  have hx : (bits k).loc x < 2^k := by have := (bits k).bd x; rwa [bits_len] at this
  have hy : (bits (n-k)).loc y < 2^(n-k) := by have := (bits (n-k)).bd y; rwa [bits_len] at this
  have h2 : 0 < 2^k := Nat.two_pow_pos k
  have h3 : 0 < 2^(n-k) := Nat.two_pow_pos (n-k)
  rw [loc_castB_catB n k hk]
  have e1 : ((bits k).loc x + 2^k * (bits (n-k)).loc y) / 2^k = (bits (n-k)).loc y := by
    rw [Nat.add_mul_div_left _ _ h2, Nat.div_eq_of_lt hx, zero_add]
  have e2 : bitsOf k ((bits k).loc x + 2^k * (bits (n-k)).loc y) = x := by
    apply (bits k).inj
    rw [bitsOf_loc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  rw [e1, e2]
  have e3 : (p * 2^(n-k) + (bits (n-k)).loc y) / 2^(n-k) = p := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ h3, Nat.div_eq_of_lt hy, zero_add]
  have e4 : bitsOf (n-k) (p * 2^(n-k) + (bits (n-k)).loc y) = y := by
    apply (bits (n-k)).inj
    rw [bitsOf_loc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  simp only [e3, e4]

section Reshape
variable {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {cl : Paint}
variable {n k NJ : ι → ℕ}

/-- Cutting jobs into vectors: linear work. -/
lemma can_toVec (hk : ∀ i, k i ≤ n i) {J : ∀ i, ℕ → Bits (n i) → ℂ}
    (hJ : Has m B s (jobsT cl) x (fun i => jobsTape (n i) (NJ i) (J i)))
    (hNJ : Knows m B s x NJ) (hp2 : Knows m B s x (fun i => 2^(n i - k i)))
    (hp1 : Knows m B s x (fun i => 2^(k i)))
    (hbig : Small B (fun i => 2^(n i))) (hNJs : Small B NJ) :
    Can m B s (jobsT cl) x
      (fun i => jobsTape (k i) (NJ i * 2^(n i - k i)) (toVec (n i) (k i) (hk i) (J i)))
      (fun i => NJ i * 2^(n i)) := by
  have hle2 : ∀ i, 2^(n i - k i) ≤ 2^(n i) := fun i => Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hle1 : ∀ i, 2^(k i) ≤ 2^(n i) := fun i => Nat.pow_le_pow_right (by omega) (hk i)
  have hs2 : Small B (fun i => 2^(n i - k i)) := hbig.mono hle2
  have hs1 : Small B (fun i => 2^(k i)) := hbig.mono hle1
  have hNV : Knows m B s x (fun i => NJ i * 2^(n i - k i)) := hNJ.times hp2 hNJs hs2
  have hNVs : Small B (fun i => NJ i * 2^(n i - k i)) := hNJs.mul hs2
  -- one entry: vector t, entry x
  let Dv := Σ u : UnitF (fun i => NJ i * 2^(n i - k i)), Bits (k u.1)
  let yv (d : Dv) : T (p (p s w) w) := ((x d.1.1, d.1.2.val), (bits (k d.1.1)).loc d.2)
  let Bv (d : Dv) := B d.1.1
  have hcls : ∀ {t : Ty} {y : ι → T t}, Has m B s t x y → Has m Bv (p (p s w) w) t yv (fun d => y d.1.1) :=
    fun g => (Can.first.then_do Can.first).then_do (g.reindex (fun d : Dv => d.1.1))
  have ht : Knows m Bv (p (p s w) w) yv (fun d => d.1.2.val) := Can.first.then_do Can.second
  have hxl : Knows m Bv (p (p s w) w) yv (fun d => (bits (k d.1.1)).loc d.2) := Can.second
  have hts : Small Bv (fun d => d.1.2.val) := (hNVs.reindex (fun d : Dv => d.1.1)).mono (fun d => d.1.2.2.le)
  have hjob : Knows m Bv (p (p s w) w) yv (fun d => d.1.2.val / 2^(n d.1.1 - k d.1.1)) :=
    ht.dvdW (hcls hp2) hts
  have hjlt : ∀ d : Dv, d.1.2.val / 2^(n d.1.1 - k d.1.1) < NJ d.1.1 := fun d =>
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 d.1.2.2
  have hJt := Can.fetch (t:=a (c cl)) (L:=fun d : Dv => Layout.std (NJ d.1.1))
    (v:=fun d j => (bits (n d.1.1)).tape (J d.1.1 j))
    (i:=fun d => (⟨d.1.2.val / 2^(n d.1.1 - k d.1.1), hjlt d⟩ : Fin (NJ d.1.1))) (hcls hJ) hjob
  have hmod : Knows m Bv (p (p s w) w) yv (fun d => d.1.2.val % 2^(n d.1.1 - k d.1.1)) :=
    ht.modW (hcls hp2) hts
  have hxs : Small Bv (fun d => (bits (k d.1.1)).loc d.2) :=
    (hs1.reindex (fun d : Dv => d.1.1)).mono (fun d => ((bits _).bd _).le)
  have hms : Small Bv (fun d => d.1.2.val % 2^(n d.1.1 - k d.1.1)) := hts.mod
  have haddr : Knows m Bv (p (p s w) w) yv (fun d => (bits (n d.1.1)).loc
      (castB (Nat.add_sub_cancel' (hk d.1.1)) (catB (k d.1.1) (n d.1.1 - k d.1.1)
        (d.2, bitsOf (n d.1.1 - k d.1.1) d.1.2.val)))) :=
    (hxl.plus ((hcls hp1).times hmod (hs1.reindex _) hms) hxs ((hs1.reindex _).mul hms)).cong
      (fun _ => rfl) (fun d => by rw [loc_castB_catB _ _ (hk d.1.1), bitsOf_loc])
  have hv := Can.fetch (t:=c cl) (L:=fun d : Dv => bits (n d.1.1))
    (v:=fun d => J d.1.1 (d.1.2.val / 2^(n d.1.1 - k d.1.1)))
    (i:=fun d => castB (Nat.add_sub_cancel' (hk d.1.1)) (catB (k d.1.1) (n d.1.1 - k d.1.1)
        (d.2, bitsOf (n d.1.1 - k d.1.1) d.1.2.val))) hJt haddr
  have hlen : Knows m (fun u : UnitF (fun i => NJ i * 2^(n i - k i)) => B u.1) (p s w)
      (fun u => (x u.1, u.2.val)) (fun u => (bits (k u.1)).n) :=
    Can.first.then_do (hp1.reindex (fun u : UnitF (fun i => NJ i * 2^(n i - k i)) => u.1))
  have HI := Can.layout (t:=c cl) (L:=fun u : UnitF (fun i => NJ i * 2^(n i - k i)) => bits (k u.1))
    (v:=fun u e => toVec (n u.1) (k u.1) (hk u.1) (J u.1) u.2 e) (P:=fun _ => 0) (W:=fun _ => 0) hlen
    (hv.mono (fun _ => Nat.zero_le _)) (hs1.reindex _)
  have HO := Can.layout (t:=a (c cl)) (L:=fun i => Layout.std (NJ i * 2^(n i - k i)))
    (v:=fun i t => (bits (k i)).tape (toVec (n i) (k i) (hk i) (J i) t)) (P:=fun i => 2^(k i))
    (W:=fun _ => 0) hNV (HI.mono (fun u => by simp)) hNVs
  refine HO.weaken ⟨3, fun i => ?_⟩
  change 0 + NJ i * 2^(n i - k i) + NJ i * 2^(n i - k i) * 2^(k i) + 1 ≤ 3 * (NJ i * 2^(n i) + 1)
  have e1 : NJ i * 2^(n i - k i) * 2^(k i) = NJ i * 2^(n i) := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (hk i)]
  have e2 : NJ i * 2^(n i - k i) ≤ NJ i * 2^(n i) := Nat.mul_le_mul_left _ (hle2 i)
  omega

/-- Putting vectors back into jobs: linear work. -/
lemma can_fromVec (hk : ∀ i, k i ≤ n i) {Y : ∀ i, ℕ → Bits (k i) → ℂ}
    (hY : Has m B s (jobsT cl) x (fun i => jobsTape (k i) (NJ i * 2^(n i - k i)) (Y i)))
    (hNJ : Knows m B s x NJ) (hp2 : Knows m B s x (fun i => 2^(n i - k i)))
    (hp1 : Knows m B s x (fun i => 2^(k i))) (hpn : Knows m B s x (fun i => 2^(n i)))
    (hbig : Small B (fun i => 2^(n i))) (hNJs : Small B NJ) :
    Can m B s (jobsT cl) x
      (fun i => jobsTape (n i) (NJ i) (fromVec (n i) (k i) (Y i)))
      (fun i => NJ i * 2^(n i)) := by
  have hle2 : ∀ i, 2^(n i - k i) ≤ 2^(n i) := fun i => Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hle1 : ∀ i, 2^(k i) ≤ 2^(n i) := fun i => Nat.pow_le_pow_right (by omega) (hk i)
  have hs2 : Small B (fun i => 2^(n i - k i)) := hbig.mono hle2
  have hs1 : Small B (fun i => 2^(k i)) := hbig.mono hle1
  let De := Σ u : UnitF NJ, Bits (n u.1)
  let ye (d : De) : T (p (p s w) w) := ((x d.1.1, d.1.2.val), (bits (n d.1.1)).loc d.2)
  let Be (d : De) := B d.1.1
  have hcls : ∀ {t : Ty} {y : ι → T t}, Has m B s t x y → Has m Be (p (p s w) w) t ye (fun d => y d.1.1) :=
    fun g => (Can.first.then_do Can.first).then_do (g.reindex (fun d : De => d.1.1))
  have hp : Knows m Be (p (p s w) w) ye (fun d => d.1.2.val) := Can.first.then_do Can.second
  have hE : Knows m Be (p (p s w) w) ye (fun d => (bits (n d.1.1)).loc d.2) := Can.second
  have hEs : Small Be (fun d => (bits (n d.1.1)).loc d.2) :=
    (hbig.reindex (fun d : De => d.1.1)).mono (fun d => ((bits _).bd _).le)
  have hps : Small Be (fun d => d.1.2.val) := (hNJs.reindex (fun d : De => d.1.1)).mono (fun d => d.1.2.2.le)
  have hvi : Knows m Be (p (p s w) w) ye
      (fun d => d.1.2.val * 2^(n d.1.1 - k d.1.1) + (bits (n d.1.1)).loc d.2 / 2^(k d.1.1)) :=
    (hp.times (hcls hp2) hps (hs2.reindex _)).plus (hE.dvdW (hcls hp1) hEs)
      (hps.mul (hs2.reindex _)) hEs.div
  have hvlt : ∀ d : De, d.1.2.val * 2^(n d.1.1 - k d.1.1) + (bits (n d.1.1)).loc d.2 / 2^(k d.1.1) <
      NJ d.1.1 * 2^(n d.1.1 - k d.1.1) := by
    intro d
    have h1 : (bits (n d.1.1)).loc d.2 < 2^(k d.1.1) * 2^(n d.1.1 - k d.1.1) := by
      have := (bits (n d.1.1)).bd d.2
      rw [bits_len, ← pow_add, Nat.add_sub_cancel' (hk d.1.1)] at *
      exact this
    have h2 : (bits (n d.1.1)).loc d.2 / 2^(k d.1.1) < 2^(n d.1.1 - k d.1.1) :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [Nat.mul_comm]; exact h1)
    have h3 : d.1.2.val + 1 ≤ NJ d.1.1 := d.1.2.2
    calc d.1.2.val * 2^(n d.1.1 - k d.1.1) + (bits (n d.1.1)).loc d.2 / 2^(k d.1.1)
        < d.1.2.val * 2^(n d.1.1 - k d.1.1) + 2^(n d.1.1 - k d.1.1) := by omega
      _ = (d.1.2.val + 1) * 2^(n d.1.1 - k d.1.1) := by ring
      _ ≤ NJ d.1.1 * 2^(n d.1.1 - k d.1.1) := Nat.mul_le_mul_right _ h3
  have hVt := Can.fetch (t:=a (c cl)) (L:=fun d : De => Layout.std (NJ d.1.1 * 2^(n d.1.1 - k d.1.1)))
    (v:=fun d j => (bits (k d.1.1)).tape (Y d.1.1 j))
    (i:=fun d => (⟨_, hvlt d⟩ : Fin (NJ d.1.1 * 2^(n d.1.1 - k d.1.1)))) (hcls hY) hvi
  have hxa : Knows m Be (p (p s w) w) ye
      (fun d => (bits (k d.1.1)).loc (bitsOf (k d.1.1) ((bits (n d.1.1)).loc d.2))) :=
    (hE.modW (hcls hp1) hEs).cong (fun _ => rfl) (fun d => by rw [bitsOf_loc])
  have hv := Can.fetch (t:=c cl) (L:=fun d : De => bits (k d.1.1))
    (v:=fun d => Y d.1.1 (d.1.2.val * 2^(n d.1.1 - k d.1.1) + (bits (n d.1.1)).loc d.2 / 2^(k d.1.1)))
    (i:=fun d => bitsOf (k d.1.1) ((bits (n d.1.1)).loc d.2)) hVt hxa
  have hlen : Knows m (fun u : UnitF NJ => B u.1) (p s w) (fun u => (x u.1, u.2.val))
      (fun u => (bits (n u.1)).n) := Can.first.then_do (hpn.reindex (fun u : UnitF NJ => u.1))
  have HI := Can.layout (t:=c cl) (L:=fun u : UnitF NJ => bits (n u.1))
    (v:=fun u e => fromVec (n u.1) (k u.1) (Y u.1) u.2 e) (P:=fun _ => 0) (W:=fun _ => 0) hlen
    (hv.mono (fun _ => Nat.zero_le _)) (hbig.reindex _)
  have HO := Can.layout (t:=a (c cl)) (L:=fun i => Layout.std (NJ i))
    (v:=fun i t => (bits (n i)).tape (fromVec (n i) (k i) (Y i) t)) (P:=fun i => 2^(n i))
    (W:=fun _ => 0) hNJ (HI.mono (fun u => by simp)) hNJs
  refine HO.weaken ⟨3, fun i => ?_⟩
  change 0 + NJ i + NJ i * 2^(n i) + 1 ≤ 3 * (NJ i * 2^(n i) + 1)
  have h2 : NJ i ≤ NJ i * 2^(n i) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  omega

end Reshape

/-- Some closed program of any type (only used on empty families). -/
def anyProg (m : Bool) : (s t : Ty) → Prog m s t
  | _, .w => .atom (.lit 0)
  | _, .c e => .atom (.cz e)
  | s, .p u v => .fork (anyProg m s u) (anyProg m s v)
  | s, .a v => .tab (.atom (.lit 0)) (anyProg m (p s w) v)

lemma can_of_empty {ι : Type U} {m : Bool} {B : ι → ℕ} {s t : Ty} {x : ι → T s} {y : ι → T t}
    {W : ι → ℕ} (hE : ∀ i : ι, False) : Can m B s t x y W :=
  ⟨anyProg m s t, 0, 0, fun i => (hE i).elim⟩

/-- A table of values computable at constant cost from the index: linear work. -/
lemma can_tabIx {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {t : Ty}
    {N : ι → ℕ} (g : ∀ i, Fin (N i) → T t) (hN : Knows m B s x N) (hNs : Small B N)
    (hg : Has m (fun u : UnitF N => B u.1) (p s w) t (fun u => (x u.1, u.2.val)) (fun u => g u.1 u.2)) :
    Can m B s (a t) x (fun i => (Layout.std (N i)).tape (g i)) N := by
  have H := Can.layout (t:=t) (L:=fun i => Layout.std (N i)) (v:=g) (P:=fun _ => 0) (W:=fun _ => 0)
    hN (hg.mono (fun _ => Nat.zero_le _)) hNs
  refine H.mono (fun i => ?_)
  change 0 + N i + N i * 0 ≤ N i
  omega

/-- The empty tape of jobs. -/
lemma has_noJobs {ι : Type U} {m : Bool} {B : ι → ℕ} {s : Ty} {x : ι → T s} {cl : Paint}
    (n : ι → ℕ) : Has m B s (jobsT cl) x (fun i => jobsTape (n i) 0 (fun _ _ => 0)) := by
  have H := can_tabIx (t:=a (c cl)) (N:=fun _ => 0) (x:=x) (B:=B) (m:=m)
    (fun i (t : Fin 0) => (bits (n i)).tape (fun _ => (0:ℂ))) (Can.wc 0) (Small.const _ 0)
    (can_of_empty (fun u => Nat.not_lt_zero _ u.2.2))
  exact H

section ExitRAM
variable {ι : Type U} {m : Bool} {cl : Paint} {b : Bank (portM cl) ι} {s : Ty} {x : ι → T s}
  {n NU : ι → ℕ} {col ib : ι → ℕ → ℕ}
variable {α β ρ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {X : Layout α} {R : Layout ρ} {k : ℕ}

/-- The fed flag of the exit routing: every unit is fed (to itself). -/
def exFl (N t : ℕ) : ℕ := if t < N then 1 else 0

lemma exFl_pp (N t : ℕ) (h : exFl N t ≠ 0) : t < N := by
  unfold exFl at h; split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

/-- The jobs of a leaf class for a block letter (one per unit). -/
def exJobs (X : Layout α) (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n) (l : ρ)
    {NU n : ℕ} {col ib : ℕ → ℕ} (hfit : ∀ p : Fin NU, X.n * col p + ib p = n)
    (V : ∀ p : Fin NU, Bits (ib p) → Grain α ρ 0 (col p)) : ℕ → Bits n → ℂ :=
  cjob X S X' hX' l hfit V (exFl NU) id (fun _ => 0) (exFl_pp NU) (fun _ _ => 0)

/-- **One block letter of a leaf class: ONE top call on all its units' jobs (an exit).** -/
theorem CCtx.exit_letter (h : CCtx m b.B s x X.n n NU col ib)
    {V : ∀ i (p : Fin (NU i)), Bits (ib i p) → Grain α ρ 0 (col i p)}
    (ct : Has m b.B s (a (a (a (c cl)))) x (fun i => ctab X R (NU i) (col i) (ib i) (V i)))
    (S : Split α β (Fin k)) (X' : Layout β) (hX' : X'.n + k = X.n) (l : ρ)
    (c0 : ι → ℕ) (hc0 : ∀ i (p : Fin (NU i)), col i p = c0 i) (hkn : ∀ i, k * c0 i ≤ n i)
    (hp1 : Knows m b.B s x (fun i => 2^(k * c0 i)))
    (hp2 : Knows m b.B s x (fun i => 2^(n i - k * c0 i)))
    (hke : Knows m b.B s x (fun i => k * c0 i))
    {ACC : ι → Tape (Tape ℂ)} {SZ : ι → Tape ℕ} {τ : ι → ℕ}
    (hk : ∀ i, (b.use i (mkIn cl (k * c0 i) 0 0 0
        (jobsTape (k * c0 i) (NU i * 2^(n i - k * c0 i))
          (toVec (n i) (k * c0 i) (hkn i) (exJobs X S X' hX' l (h.fit i) (V i))))
        (jobsTape (k * c0 i) 0 (fun _ _ => 0)))).OK
      (jobsTape (k * c0 i) (NU i * 2^(n i - k * c0 i))
        (fun t => ripple (k * c0 i) (toVec (n i) (k * c0 i) (hkn i) (exJobs X S X' hX' l (h.fit i) (V i)) t)),
        ACC i, SZ i) (τ i) (b.ext i)) :
    Able m b s (p (a (a (a (c cl)))) (portOut cl)) x
      (fun i => (ctab X R (NU i) (col i) (ib i)
          (fun p q => ferryM 0 (col i p) l (S.lift (kernel (Fin k))) (V i p q)),
        (jobsTape (k * c0 i) (NU i * 2^(n i - k * c0 i))
          (fun t => ripple (k * c0 i) (toVec (n i) (k * c0 i) (hkn i) (exJobs X S X' hX' l (h.fit i) (V i)) t)),
          ACC i, SZ i)))
      (fun i => NU i * 2^(n i)) τ := by
  -- trivial routing tables: every unit feeds itself
  let TT : Ty := p (a w) (p (a w) (a w))
  let tabs (i : ι) : T TT := ((Layout.std (NU i)).tape (fun t => exFl (NU i) t),
    (Layout.std (NU i)).tape (fun t => id t.val), (Layout.std (NU i)).tape (fun _ => 0))
  have Htab : Can m b.B s TT x tabs NU := by
    have h1 := can_tabIx (t:=w) (fun i (t : Fin (NU i)) => exFl (NU i) t) h.nuK h.nuS
      ((Can.wc (m:=m) (s:=p s w) (B:=fun u : UnitF NU => b.B u.1) (x:=fun u => (x u.1, u.2.val)) 1).cong
        (fun _ => rfl) (fun u => by simp [exFl, u.2.2]))
    have h2 := can_tabIx (t:=w) (fun i (t : Fin (NU i)) => id t.val) h.nuK h.nuS Can.second
    have h3 := can_tabIx (t:=w) (fun i (_ : Fin (NU i)) => 0) h.nuK h.nuS (Can.wc 0)
    exact h1.pair (h2.pair h3)
  let x1 (i : ι) : T (p s TT) := (x i, tabs i)
  have h1 := h.ext tabs
  have F1 : ∀ {u : Ty} {z : ι → T u}, Has m b.B s u x z → Has m b.B (p s TT) u x1 z :=
    fun g => Can.first.then_do g
  have tfl : Has m b.B (p s TT) (a w) x1 (fun i => (Layout.std (NU i)).tape (fun t => exFl (NU i) t)) :=
    Can.fst Can.second
  have tpp : Has m b.B (p s TT) (a w) x1 (fun i => (Layout.std (NU i)).tape (fun t => id t.val)) :=
    Can.fst (Can.snd Can.second)
  have tsi : Has m b.B (p s TT) (a w) x1 (fun i => (Layout.std (NU i)).tape (fun _ => 0)) :=
    Can.snd (Can.snd Can.second)
  have tsup : Has m b.B (p s TT) (jobsT cl) x1 (fun i => jobsTape (n i) 0 (fun _ _ => 0)) :=
    has_noJobs n
  -- the jobs (one per unit)
  have HG := h1.gather (F1 ct) S X' hX' l (fl:=fun i => exFl (NU i)) (pp:=fun _ => id)
    (si:=fun _ _ => 0) (BS:=fun _ => 0) (sup:=fun _ _ _ => 0) (NJ:=NU)
    (fun i => exFl_pp (NU i)) (fun i t ht hf => by simp [exFl, ht] at hf)
    (F1 h.nuK) h.nuS tfl tpp tsi tsup
  -- `HG` is the tape of `exJobs`
  let JB (i : ι) := jobsTape (n i) (NU i) (exJobs X S X' hX' l (h.fit i) (V i))
  have HG' : Can m b.B (p s TT) (jobsT cl) x1 JB (fun i => NU i * 2^(n i)) := HG
  let x2 (i : ι) : T (p (p s TT) (jobsT cl)) := (x1 i, JB i)
  have F2 : ∀ {u : Ty} {z : ι → T u}, Has m b.B s u x z → Has m b.B (p (p s TT) (jobsT cl)) u x2 z :=
    fun g => Can.first.then_do (F1 g)
  have hJ2 : Has m b.B (p (p s TT) (jobsT cl)) (jobsT cl) x2 JB := Can.second
  have HV := can_toVec (cl:=cl) (k:=fun i => k * c0 i) (NJ:=NU) hkn hJ2 (F2 h.nuK) (F2 hp2) (F2 hp1) h.big h.nuS
  have Hin : Can m b.B (p (p s TT) (jobsT cl)) (portIn cl) x2
      (fun i => mkIn cl (k * c0 i) 0 0 0
        (jobsTape (k * c0 i) (NU i * 2^(n i - k * c0 i))
          (toVec (n i) (k * c0 i) (hkn i) (exJobs X S X' hX' l (h.fit i) (V i))))
        (jobsTape (k * c0 i) 0 (fun _ _ => 0))) (fun i => NU i * 2^(n i)) :=
    ((F2 hke).mono (fun _ => Nat.zero_le _)).pair (((F2 h.imag).mono (fun _ => Nat.zero_le _)).pair
      ((Can.wc 0).pair ((Can.wc 0).pair ((Can.wc 0).pair (HV.pair
        ((has_noJobs (fun i => k * c0 i)).mono (fun _ => Nat.zero_le _)))))))
  have Hcall := (Able.of_can (b:=b) Hin).comp (Able.use_call (m:=m) (b:=b) hk)
  -- back into jobs, then into the class table
  let outp (i : ι) : T (portOut cl) :=
    (jobsTape (k * c0 i) (NU i * 2^(n i - k * c0 i))
      (fun t => ripple (k * c0 i) (toVec (n i) (k * c0 i) (hkn i) (exJobs X S X' hX' l (h.fit i) (V i)) t)),
      ACC i, SZ i)
  let x3 (i : ι) : T (p (p (p s TT) (jobsT cl)) (portOut cl)) := (x2 i, outp i)
  have F3 : ∀ {u : Ty} {z : ι → T u}, Has m b.B s u x z → Has m b.B (p (p (p s TT) (jobsT cl)) (portOut cl)) u x3 z :=
    fun g => Can.first.then_do (F2 g)
  have hO3 : Has m b.B (p (p (p s TT) (jobsT cl)) (portOut cl)) (jobsT cl) x3
      (fun i => jobsTape (k * c0 i) (NU i * 2^(n i - k * c0 i))
        (fun t => ripple (k * c0 i) (toVec (n i) (k * c0 i) (hkn i) (exJobs X S X' hX' l (h.fit i) (V i)) t))) :=
    Can.fst Can.second
  have HB := can_fromVec (cl:=cl) (k:=fun i => k * c0 i) (NJ:=NU) hkn hO3 (F3 h.nuK) (F3 hp2) (F3 hp1)
    (F3 h.p2n) h.big h.nuS
  let YB (i : ι) := fromVec (n i) (k * c0 i)
    (fun t => ripple (k * c0 i) (toVec (n i) (k * c0 i) (hkn i) (exJobs X S X' hX' l (h.fit i) (V i)) t))
  let x4 (i : ι) := (x3 i, jobsTape (n i) (NU i) (YB i))
  have h4 := ((h1.ext (t:=jobsT cl) JB).ext (t:=portOut cl) outp).ext (t:=jobsT cl)
    (fun i => jobsTape (n i) (NU i) (YB i))
  have F4 : ∀ {u : Ty} {z : ι → T u}, Has m b.B s u x z →
      Has m b.B (p (p (p (p s TT) (jobsT cl)) (portOut cl)) (jobsT cl)) u x4 z :=
    fun g => Can.first.then_do (F3 g)
  have tslot : Has m b.B (p (p (p (p s TT) (jobsT cl)) (portOut cl)) (jobsT cl)) (a w) x4
      (fun i => (Layout.std (NU i)).tape (fun p => id p.val)) :=
    Can.first.then_do (Can.first.then_do (Can.first.then_do tpp))
  have hY : ∀ i (p : Fin (NU i)) (q : Bits (ib i p)) (y : Sky α (col i p)),
      YB i (id p.val) (placeS S X' (col i p) (ib i p) (n i) (fitk X' hX' (h4.fit i p)) (q, y)) =
      ferryM 0 (col i p) l (S.lift (kernel (Fin k))) (V i p q) (l, (0, y)) := by
    intro i p q y
    simp only [YB, id]
    rw [fromVec_ripple]
    have hf : exFl (NU i) p.val ≠ 0 := by simp [exFl, p.2]
    have hc := hc0 i p
    have e1 : exJobs X S X' hX' l (h.fit i) (V i) p.val =
        blockJob S X' (col i p) (ib i p) (n i) (fitk X' hX' (h.fit i p)) l (V i p) :=
      cjob_fed X S X' hX' l (h.fit i) (V i) _ id _ _ _ p.val p hf rfl
    rw [e1, ← hc]
    exact blockJob_hlow S X' _ _ _ _ l (V i p) q 0 y
  have HS := h4.scatter (Y:=YB) (F4 ct) S X' hX' l (slot:=fun _ t => id t) (NJ:=NU)
    (fun i p => p.2) tslot Can.second hY
  -- assemble
  have Hpost : Can m b.B (p (p (p s TT) (jobsT cl)) (portOut cl)) (p (a (a (a (c cl)))) (portOut cl)) x3
      (fun i => (ctab X R (NU i) (col i) (ib i)
          (fun p q => ferryM 0 (col i p) l (S.lift (kernel (Fin k))) (V i p q)), outp i))
      (fun i => NU i * 2^(n i)) :=
    HB.bind ((HS.mono (fun _ => le_rfl)).pair (Can.first.then_do Can.second |>.mono (fun _ => Nat.zero_le _)))
  have Hall := ((Able.of_can (b:=b) Htab).save ((Able.of_can (b:=b) HG').save
    (Hcall.save (Able.of_can (b:=b) Hpost))))
  refine Hall.weaken ⟨5, fun i => ?_⟩ (fun i => by simp)
  have h1' : NU i ≤ NU i * 2^(n i) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  simp only
  nlinarith

end ExitRAM

end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.Exit

-- bos_merge: begin Submission.Work.Mixed.Prog.Desc
section

/-!
# Mixed engine, R3 program part 6: the engine data, the descriptors and their calls (agent e-r3prog)

* `Eng`        the fixed data: the word `wd` (a `GWord` with targets `blockMat (tz l)` on the live roles,
               rl-prove Theorem 1G's rule), layouts, the separation hypothesis;
* `MDesc`       ONE descriptor type for the handler: top jobs `Do(n, B)` and classes of the lockstep tree;
* `Eng.enc`, `Eng.out`   the input and the answer of every call (port of `Block.lean`);
* `Eng.V0`     the class table loaded from a class's own jobs (live roles through the target splits,
               scratch roles zero);
* `Eng.kidsC`  the calls of a class: one child class per block letter in word order (one exit for a leaf
               class), each with its input as the program builds it after the letters before it;
* `Eng.srcSizes`  the sizes of the supply vectors a class's subtree consumes, in consumption order.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR
noncomputable section

/-- One descriptor type for all calls of the lockstep program. -/
inductive MDesc
  | top (n B : ℕ) (v : ℕ → Bits n → ℂ)
  | cls (n h μ o BS : ℕ) (J sup : ℕ → Bits n → ℂ)

/-- The fixed data of the mixed engine. -/
structure Eng (α ρ σ : Type*) [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    [Fintype σ] [DecidableEq σ] where
  X : Layout α
  R : Layout ρ
  Q : Layout σ
  e : σ → ρ
  he : Function.Injective e
  tr : σ → ℕ
  tz : ∀ l, Fin (tr l) → Space α
  tind : ∀ l, LinearIndependent F (tz l)
  tr_le : ∀ l, tr l ≤ X.n
  tr_pos : ∀ l, 1 ≤ tr l
  wd : GWord α ρ
  hP : wd.Proper X.n
  /-- separation (rl-prove (S)): every paid rank is below every target rank -/
  sep : ∀ mv ∈ wd, ∀ r, mv.rk? = some r → ∀ l, r < tr l
  W_pos : 0 < Q.n
  three : 3 ≤ X.n
  /-- the mixed certificate (`GLiveKernelM e (fun l => blockMat (tz l)) wd` of rb-r45m1, same body) -/
  hw : ∀ (f : ℕ) (v : Data α ρ f), (∀ s, (∀ l, e l ≠ s) → v s = 0) →
    ∀ l, gwalk f wd v (e l) = matAct f (blockMat (tz l)) (v (e l))

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- Number of live roles. -/
abbrev W : ℕ := E.Q.n
/-- Target rank of the live role at position `a`. -/
def tq (a : ℕ) : ℕ := if h : a < E.Q.n then E.tr (E.Q.atFin ⟨a, h⟩) else 0
/-- Axes of an array. -/
abbrev mx : ℕ := E.X.n

/-! ### the units of a class -/
abbrev NUc (n h μ : ℕ) : ℕ := MXR.NU E.W E.tq E.mx n h μ
abbrev Uc (n h μ p : ℕ) : ℕ := MXR.U E.W E.tq E.mx n h μ p
abbrev PCc (n h μ t : ℕ) : ℕ := MXR.PC E.W E.tq E.mx n h μ t
abbrev cUc (n h μ p : ℕ) : ℕ := MXR.cU E.W E.tq E.mx n h μ p
abbrev iUc (n h μ p : ℕ) : ℕ := MXR.iU E.W E.tq E.mx n h μ p

lemma fitc (n h μ : ℕ) (p : Fin (E.NUc n h μ)) : E.X.n * E.cUc n h μ p + E.iUc n h μ p = n :=
  MXR.iU_add p.2

/-- Size of own slot `t = p*W + a` of a class. -/
def slotSize (n h μ t : ℕ) : ℕ := E.tq (t % E.W) * E.cUc n h μ (t / E.W)

/-- The class state: element data of every unit and instance. -/
abbrev CState (n h μ : ℕ) := ∀ p : Fin (E.NUc n h μ), Bits (E.iUc n h μ p) → Grain α ρ 0 (E.cUc n h μ p)

/-! ### target splits of the live roles -/
/-- The target splitting of live role `l`. -/
def St (l : σ) : Split α (Fin (Fintype.card α - E.tr l)) (Fin (E.tr l)) :=
  Classical.choose (exists_split (E.tz l) (E.tind l))
lemma St_spec (l : σ) (i : Fin (E.tr l)) : (E.St l).e.symm (0, eu i) = E.tz l i :=
  Classical.choose_spec (exists_split (E.tz l) (E.tind l)) i
/-- Its rest layout. -/
def Xt (l : σ) : Layout (Fin (Fintype.card α - E.tr l)) := Layout.someLayout _
lemma Xt_n (l : σ) : (E.Xt l).n + E.tr l = E.X.n := by
  have e1 : (E.Xt l).n = Fintype.card α - E.tr l := by
    rw [← Layout.card (E.Xt l)]; simp
  have e2 : Fintype.card α = E.X.n := Layout.card E.X
  have := E.tr_le l
  omega

/-- The live role behind a role, if any. -/
def liveOf (l' : ρ) : Option σ := if h : ∃ s0, E.e s0 = l' then some (Classical.choose h) else none

lemma liveOf_e (s0 : σ) : E.liveOf (E.e s0) = some s0 := by
  have h : ∃ s1, E.e s1 = E.e s0 := ⟨s0, rfl⟩
  unfold liveOf
  rw [dif_pos h]
  exact congrArg some (E.he (Classical.choose_spec h))

lemma liveOf_none (l' : ρ) (h : ∀ s0, E.e s0 ≠ l') : E.liveOf l' = none := by
  unfold liveOf; rw [dif_neg (fun ⟨s0, hs⟩ => h s0 hs)]

/-- The placement of a live role's job in the instances of unit `p`. -/
def placeT (n h μ : ℕ) (p : Fin (E.NUc n h μ)) (l : σ) :
    Bits (E.iUc n h μ p) × Sky α (E.cUc n h μ p) ≃ Bits n :=
  placeS (E.St l) (E.Xt l) (E.cUc n h μ p) (E.iUc n h μ p) n (fitk (E.Xt l) (E.Xt_n l) (E.fitc n h μ p))

/-- **The class table loaded from a class's own jobs**: live role `e l` of instance `q` of unit
`p` reads job `p*W + loc l` through the target placement; scratch roles are zero. -/
def V0 (n h μ : ℕ) (J : ℕ → Bits n → ℂ) : E.CState n h μ :=
  fun p q x => match E.liveOf x.1 with
    | some l => J (p.val * E.W + E.Q.loc l) (E.placeT n h μ p l (q, x.2.2))
    | none => 0

/-- One letter on every element of a class. -/
def stepV {n h μ : ℕ} (V : E.CState n h μ) (mv : GMove α ρ) : E.CState n h μ :=
  fun p q => gferry 0 (E.cUc n h μ p) mv (V p q)

/-- The whole word on every element. -/
def runV {n h μ : ℕ} (V : E.CState n h μ) (w : GWord α ρ) : E.CState n h μ :=
  fun p q => gcoast 0 (E.cUc n h μ p) w (V p q)

/-! ### routing of a block letter of rank `r` from class `(n, h+1, μ)` to its child `(n, h, μ*r)` -/

/-- Code of the parent unit feeding child slot `t`. -/
def parCode (n h μ r t : ℕ) : ℕ := t % E.W + E.W * E.Uc n h (μ * r) (t / E.W)
/-- Child slot `t` is fed (by a parent unit). -/
def fedP (n h μ r t : ℕ) : Prop :=
  t < E.NUc n h (μ * r) * E.W ∧ inRS E.W E.tq E.mx n (h+1) μ (E.parCode n h μ r t)
instance (n h μ r : ℕ) : DecidablePred (E.fedP n h μ r) := fun t => by unfold fedP; infer_instance
/-- Child slot `t` is a source. -/
def srcP (n h μ r t : ℕ) : Prop := t < E.NUc n h (μ * r) * E.W ∧ ¬ inRS E.W E.tq E.mx n (h+1) μ (E.parCode n h μ r t)
instance (n h μ r : ℕ) : DecidablePred (E.srcP n h μ r) := fun t => by unfold srcP; infer_instance

def flR (n h μ r t : ℕ) : ℕ := if E.fedP n h μ r t then 1 else 0
def ppR (n h μ r t : ℕ) : ℕ := E.PCc n (h+1) μ (E.parCode n h μ r t)
/-- Supply index of a source slot: running offset plus the number of source slots before it. -/
def siR (n h μ r o t : ℕ) : ℕ := o + Nat.count (E.srcP n h μ r) t
/-- Child slot of a parent unit. -/
def slotR (n h μ r p : ℕ) : ℕ :=
  E.PCc n h (μ * r) (E.Uc n (h+1) μ p / E.W) * E.W + E.Uc n (h+1) μ p % E.W

lemma ppR_lt (n h μ r t : ℕ) (hf : E.flR n h μ r t ≠ 0) : E.ppR n h μ r t < E.NUc n (h+1) μ := by
  unfold flR at hf
  split_ifs at hf with h1
  · exact PC_lt h1.2
  · exact absurd rfl hf

/-! ### sizes of consumed sources -/

/-- Ranks of the block letters of a word, in order. -/
def blockRanks (w : GWord α ρ) : List ℕ := w.filterMap GMove.rk?

/-- Sizes of the source slots of the child `(n, h, μ*r)` of a block letter of rank `r`, in slot order. -/
def ownSrc (n h μ r : ℕ) : List ℕ :=
  (List.range (E.NUc n h (μ * r) * E.W)).filterMap
    (fun t => if E.srcP n h μ r t then some (E.slotSize n h (μ * r) t) else none)

/-- Sizes of the supply vectors consumed by the subtree of a class (not its own slots), in order. -/
def srcSizes (n : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | h+1, μ => (blockRanks E.wd).flatMap (fun r => E.ownSrc n h μ r ++ srcSizes n h (μ * r))

def cons (n h μ : ℕ) : ℕ := (E.srcSizes n h μ).length
def csz (n h μ k : ℕ) : ℕ := (E.srcSizes n h μ).getD k 0

/-! ### the calls of a class -/

/-- The block letter's split (as in `open_moveB`). -/
def bS {r : ℕ} (z : Fin r → Space α) (ind : LinearIndependent F z) :
    Split α (Fin (Fintype.card α - r)) (Fin r) := Classical.choose (exists_split z ind)
def bX (r : ℕ) : Layout (Fin (Fintype.card α - r)) := Layout.someLayout _
lemma bX_n {r : ℕ} (hr : r ≤ E.X.n) : (bX (α:=α) r).n + r = E.X.n := by
  have e1 : (bX (α:=α) r).n = Fintype.card α - r := by
    rw [← Layout.card (bX (α:=α) r)]; simp
  have e2 : Fintype.card α = E.X.n := Layout.card E.X
  omega

/-- The child class of a block letter (class `(n, h+1, μ)`, state `V`, running offset `o`). -/
def childC (n h μ BS : ℕ) (sup : ℕ → Bits n → ℂ) (V : E.CState n (h+1) μ) (o : ℕ)
    (l : ρ) (r : ℕ) (z : Fin r → Space α) (ind : LinearIndependent F z) (hr : r ≤ E.X.n) : MDesc :=
  MDesc.cls n h (μ * r) (o + (E.ownSrc n h μ r).length) BS
    (cjob E.X (bS z ind) (bX (α:=α) r) (E.bX_n hr) l (E.fitc n (h+1) μ) V (E.flR n h μ r) (E.ppR n h μ r)
      (E.siR n h μ r o) (E.ppR_lt n h μ r) sup) sup

/-- The exit of a block letter of a leaf class (class `(n, 0, μ)`, state `V`). -/
def exitC (n μ : ℕ) (V : E.CState n 0 μ) (l : ρ) (r : ℕ) (z : Fin r → Space α)
    (ind : LinearIndependent F z) (hr : r ≤ E.X.n) : MDesc :=
  if hk : r * μ ≤ n then
    MDesc.top (r * μ) (E.NUc n 0 μ * 2^(n - r * μ))
      (toVec n (r * μ) hk (exJobs E.X (bS z ind) (bX (α:=α) r) (E.bX_n hr) l (E.fitc n 0 μ) V))
  else MDesc.top 0 0 (fun _ _ => 0)

/-- The calls of a class of height `h+1` along a word: state and running offset are threaded. -/
def kidsUp (n h μ BS : ℕ) (sup : ℕ → Bits n → ℂ) : E.CState n (h+1) μ → ℕ → GWord α ρ → List MDesc
  | _, _, [] => []
  | V, o, mv :: ws => match mv with
    | .old (.block l r z ind) =>
      (if hr : r ≤ E.X.n then [E.childC n h μ BS sup V o l r z ind hr] else []) ++
        kidsUp n h μ BS sup (E.stepV V mv) (o + (E.ownSrc n h μ r).length + E.cons n h (μ * r)) ws
    | _ => kidsUp n h μ BS sup (E.stepV V mv) o ws

/-- The calls of a leaf class along a word. -/
def kidsLeaf (n μ : ℕ) : E.CState n 0 μ → GWord α ρ → List MDesc
  | _, [] => []
  | V, mv :: ws => match mv with
    | .old (.block l r z ind) =>
      (if hr : r ≤ E.X.n then [E.exitC n μ V l r z ind hr] else []) ++ kidsLeaf n μ (E.stepV V mv) ws
    | _ => kidsLeaf n μ (E.stepV V mv) ws

/-- **The calls of a class.** -/
def kidsC : MDesc → List MDesc
  | MDesc.top _ _ _ => []
  | MDesc.cls n 0 μ _ _ J _ => E.kidsLeaf n μ (E.V0 n 0 μ J) E.wd
  | MDesc.cls n (h+1) μ o BS J sup => E.kidsUp n h μ BS sup (E.V0 n (h+1) μ J) o E.wd

/-! ### input and answer of every call -/

/-- Input of a call. -/
def enc (cl : Paint) : MDesc → T (portIn cl)
  | MDesc.top n B v => mkIn cl n 0 0 0 (jobsTape n B v) (jobsTape n 0 (fun _ _ => 0))
  | MDesc.cls n h μ o BS J sup => mkIn cl n (h+1) μ o (jobsTape n (E.NUc n h μ * E.W) J) (jobsTape n BS sup)

/-- Answer of a call. -/
def out (cl : Paint) : MDesc → T (portOut cl)
  | MDesc.top n B v => (jobsTape n B (fun t => ripple n (v t)), jobsTape n 0 (fun _ _ => 0),
      (Layout.std 0).tape (fun _ => 0))
  | MDesc.cls n h μ o BS J sup =>
      (jobsTape n (E.NUc n h μ * E.W) (fun t => hlow n (E.slotSize n h μ t) (J t)),
       jobsTape n (E.cons n h μ) (fun k => hlow n (E.csz n h μ k) (sup (o + k))),
       (Layout.std (E.cons n h μ)).tape (fun k => E.csz n h μ k))

end Eng
end
end PowerSaving.RAM
end OAI

end
-- bos_merge: end Submission.Work.Mixed.Prog.Desc

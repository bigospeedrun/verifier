import Submission.Work.KLowW.Main
import Submission.Work.KLow.LabelsX

/-!
# (key: p-warpchk) THE WARP INVOCATION THEOREM: a checked warp word is an exit-frame package `GInvX`

The hub's borrow words carry warp words across every cut between the precondition and the cleanup, so they cannot be
split into the scalar phases of `GLabX` (XExit/Halves).  Instead the WHOLE local program (precondition with the
twisted additions, A, the centre steps, B, the staged releases, the final climbs, the cleanup with the private zero
buffers) is ONE list of events on the roles `Box (Fin v) (Fin R) (Fin nc)` (x, y, slots, private scratch: centre
copies and zero buffers), and

    iin  ─e0 (erase scratch)─▶  ─a0 (free adapters)─▶  Lf S0  ─warp route─▶  Lf SF  ─aF (free adapters)─▶  ─e1─▶  iout

is the clean forward (and backward) route with effect `shearF` (`shearB`), price `rcost rs`.  `WValid.inv` packages it
as x-exit-lean's `GInvX`, exactly as `GLabX.inv` does (`gdirtyE`).

* `WCert`, `WValid`   the data and the kernel facts (all `decide +kernel`): frame table, warp table, ONE label
                      replay, the exit-aware end check `endKX` on the x, y and slot registers, the two free-algebra
                      replays, identity start rows, shear end rows (`shK`);
* `rows_shearF`, `rows_shearB`   shear end rows erase-sandwiched are `shearF` / `shearB`;
* **`WValid.inv`**    `GInvX (Fin h) (Fin v) (Fin R) (Fin nc)` for warp meanings `WSf`, `WSb` of EVERY frame map.

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace KLW
open SSC GXD GLab OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.SS OAI.PowerSaving.CB OAI.PowerSaving.BR OAI.PowerSaving.GX OAI.PowerSaving.XEX Finset Matrix

/-! ## shear end rows -/

/-- the expected end row of register `r` (forward: `y += x`; backward: `x -= y`; coefficient `D` means `1`) -/
noncomputable def shRow (D v : Nat) (o : Bool) (r : Nat) : Row :=
  Bool.rec (motive := fun _ => Row)
    (Bool.rec (motive := fun _ => Row) [(r, (D : Int))]
      (Bool.rec (motive := fun _ => Row) [(r - v, (D : Int)), (r, (D : Int))] [(r, (D : Int))] o)
      (Nat.blt r (2 * v)))
    (Bool.rec (motive := fun _ => Row) [(r, (D : Int))] [(r, (D : Int)), (r + v, -(D : Int))] o)
    (Nat.blt r v)

/-- the end rows of the registers `< n` are the shear rows -/
noncomputable def shKn (q : SPw) (v : Nat) (o : Bool) (R : RT) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r ih => guard (R.getK r (fun row => rowEq row (shRow q.D v o r))) ih) n

theorem shKn_sound (q : SPw) (v : Nat) (o : Bool) (R : RT) (hR : R.wf q.d) :
    ∀ n, shKn q v o R n = true → ∀ r, r < n → R.get r = shRow q.D v o r := by
  intro n
  induction n with
  | zero => intro _ r hr; exact absurd hr (Nat.not_lt_zero r)
  | succ n ih =>
    intro H r hr
    have H' : SSC.guard (R.getK n (fun row => rowEq row (shRow q.D v o n))) (shKn q v o R n) = true := H
    obtain ⟨g1, g2⟩ := SSC.guard_true H'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | h
    · exact ih g2 r h
    · subst h
      exact rowEq_sound _ _ (RT.getK_true hR g1).2

section Shear
variable {v R nc : Nat}

/-- the numbering of the roles: x `t`, y `v + t`, slot `2v + q`, scratch `≥ 2v + R` -/
structure Num (v R nc : Nat) (emb : Box (Fin v) (Fin R) (Fin nc) → Nat) : Prop where
  hx : ∀ t : Fin v, emb (bX t) = t.val
  hy : ∀ t : Fin v, emb (bY t) = v + t.val
  hs : ∀ q : Fin R, emb (bS q) = 2 * v + q.val
  hc : ∀ c : Fin nc, 2 * v + R ≤ emb (bC c)

variable {emb : Box (Fin v) (Fin R) (Fin nc) → Nat} {un : Nat → Box (Fin v) (Fin R) (Fin nc)} {q : SPw}

theorem un_x (hq : SCtx q emb un) (hN : Num v R nc emb) (t : Fin v) : un t.val = bX t := by
  rw [← hN.hx t, hq.hun]
theorem un_y (hq : SCtx q emb un) (hN : Num v R nc emb) (t : Fin v) : un (v + t.val) = bY t := by
  rw [← hN.hy t, hq.hun]
theorem un_s (hq : SCtx q emb un) (hN : Num v R nc emb) (s : Fin R) : un (2 * v + s.val) = bS s := by
  rw [← hN.hs s, hq.hun]

theorem rowsMat_one (q : SPw) (hD : 1 ≤ q.D) (un : Nat → Box (Fin v) (Fin R) (Fin nc)) (a : Nat)
    (i : Box (Fin v) (Fin R) (Fin nc)) :
    (([(a, (q.D : Int))] : Row).map (fun e => if un e.1 = i then (e.2 : ℚ) / (q.D : ℚ) else 0)).sum
      = if un a = i then 1 else 0 := by
  have hD' : (q.D : ℚ) ≠ 0 := by exact_mod_cast (show q.D ≠ 0 by omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  split
  · push_cast; exact div_self hD'
  · rfl

theorem sum_ind (w : Box (Fin v) (Fin R) (Fin nc) → ℂ) (a : Box (Fin v) (Fin R) (Fin nc)) :
    ∑ i, (((if a = i then (1 : ℚ) else 0 : ℚ)) : ℂ) * w i = w a := by
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp)
    (fun h => absurd (Finset.mem_univ a) h)]
  simp

/-- shear end rows, between two erase gates, are the forward shear -/
theorem rows_shear (hq : SCtx q emb un) (hN : Num v R nc emb) (hD : 1 ≤ q.D) (o : Bool) {RF : RT}
    (hsh : ∀ r, r < 2 * v + R → RF.get r = shRow q.D v o r) (z : Box (Fin v) (Fin R) (Fin nc) → ℂ) :
    eraseC (actPoint (rowsMat q un emb RF) (eraseC z)) = Bool.rec (motive := fun _ => _) (shearF z) (shearB z) o := by
  have hD' : (q.D : ℚ) ≠ 0 := by exact_mod_cast (show q.D ≠ 0 by omega)
  have hq1 : ((q.D : Int) : ℚ) / (q.D : ℚ) = 1 := by push_cast; exact div_self hD'
  have hq2 : (((-(q.D : Int)) : Int) : ℚ) / (q.D : ℚ) = -1 := by push_cast; rw [neg_div, div_self hD']
  have hXY : ∀ t : Fin v, bX (Sl := Fin R) (C := Fin nc) t ≠ bY t := fun t h => by simp [bX, bY] at h
  funext i
  rcases i with ((t|t)|(s|c))
  · -- x
    show actPoint (rowsMat q un emb RF) (eraseC z) (bX t) = _
    have hrow := hsh t.val (by omega)
    unfold actPoint rowsMat
    rw [hN.hx t, hrow]
    cases o with
    | false =>
      have e : shRow q.D v false t.val = [(t.val, (q.D : Int))] := by
        unfold shRow; rw [show Nat.blt t.val v = true from Nat.blt_eq.mpr t.isLt]; try rfl
      rw [e]
      simp_rw [rowsMat_one q hD un]
      rw [un_x hq hN t, sum_ind]; try rfl
    | true =>
      have e : shRow q.D v true t.val = [(t.val, (q.D : Int)), (t.val + v, -(q.D : Int))] := by
        unfold shRow; rw [show Nat.blt t.val v = true from Nat.blt_eq.mpr t.isLt]; try rfl
      rw [e]
      have e2 : t.val + v = v + t.val := Nat.add_comm _ _
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, e2, un_x hq hN t,
        un_y hq hN t]
      have : ∀ i, (((if bX t = i then ((q.D : Int) : ℚ) / (q.D : ℚ) else 0) +
          (if bY t = i then ((-(q.D : Int) : Int) : ℚ) / (q.D : ℚ) else 0) : ℚ) : ℂ) * eraseC z i
          = ((if bX t = i then (1 : ℚ) else 0 : ℚ) : ℂ) * eraseC z i
            - ((if bY t = i then (1 : ℚ) else 0 : ℚ) : ℂ) * eraseC z i := by
        intro i
        rw [hq1, hq2]
        by_cases h1 : bX t = i <;> by_cases h2 : bY t = i
        · exact absurd (h1.trans h2.symm) (hXY t)
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, sum_ind, sum_ind]
      rfl
  · -- y
    show actPoint (rowsMat q un emb RF) (eraseC z) (bY t) = _
    have hrow := hsh (v + t.val) (by omega)
    unfold actPoint rowsMat
    rw [hN.hy t, hrow]
    have h1 : Nat.blt (v + t.val) v = false := by
      cases e : Nat.blt (v + t.val) v
      · rfl
      · have := Nat.blt_eq.mp e; omega
    have h2 : Nat.blt (v + t.val) (2 * v) = true := Nat.blt_eq.mpr (by omega)
    cases o with
    | false =>
      have e : shRow q.D v false (v + t.val) = [(t.val, (q.D : Int)), (v + t.val, (q.D : Int))] := by
        unfold shRow; rw [h1, h2]
        show [(v + t.val - v, (q.D : Int)), (v + t.val, (q.D : Int))] = _
        rw [Nat.add_sub_cancel_left]
      rw [e]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, un_x hq hN t,
        un_y hq hN t]
      have : ∀ i, (((if bX t = i then ((q.D : Int) : ℚ) / (q.D : ℚ) else 0) +
          (if bY t = i then ((q.D : Int) : ℚ) / (q.D : ℚ) else 0) : ℚ) : ℂ) * eraseC z i
          = ((if bX t = i then (1 : ℚ) else 0 : ℚ) : ℂ) * eraseC z i
            + ((if bY t = i then (1 : ℚ) else 0 : ℚ) : ℂ) * eraseC z i := by
        intro i
        rw [hq1]
        by_cases h1 : bX t = i <;> by_cases h2 : bY t = i
        · exact absurd (h1.trans h2.symm) (hXY t)
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib, sum_ind, sum_ind, add_comm]
      rfl
    | true =>
      have e : shRow q.D v true (v + t.val) = [(v + t.val, (q.D : Int))] := by
        unfold shRow; rw [h1, h2]; try rfl
      rw [e]
      simp_rw [rowsMat_one q hD un]
      rw [un_y hq hN t, sum_ind]; try rfl
  · -- slot
    show actPoint (rowsMat q un emb RF) (eraseC z) (bS s) = _
    have hrow := hsh (2 * v + s.val) (by omega)
    unfold actPoint rowsMat
    rw [hN.hs s, hrow]
    have h1 : Nat.blt (2 * v + s.val) v = false := by
      cases e : Nat.blt (2 * v + s.val) v
      · rfl
      · have := Nat.blt_eq.mp e; omega
    have h2 : Nat.blt (2 * v + s.val) (2 * v) = false := by
      cases e : Nat.blt (2 * v + s.val) (2 * v)
      · rfl
      · have := Nat.blt_eq.mp e; omega
    have e : shRow q.D v o (2 * v + s.val) = [(2 * v + s.val, (q.D : Int))] := by
      unfold shRow; rw [h1, h2]; try (cases o <;> rfl)
    rw [e]
    simp_rw [rowsMat_one q hD un]
    rw [un_s hq hN s, sum_ind]
    cases o <;> rfl
  · -- scratch
    cases o <;> rfl

end Shear

/-! ## the certificate -/

/-- **an extended exit-frame certificate** (`gcert/1w`): one event list for the whole local program -/
structure WCert where
  v : Nat
  R : Nat
  nc : Nat
  p : GLab.Par
  wt : List WOp
  /-- the local program, FORWARD reading -/
  evs : List WEv
  /-- the local program for the BACKWARD replay (the hub's dual stream): the same events except the centre steps,
  which are written so that their duals are the hub's backward centre steps (the copy gathers from the targets at the
  low level, climbs UP, is subtracted from the total, and is erased with `.za c 0`); same frames at the start and at
  the end, same ranks -/
  evsB : List WEv
  S0 : Trie
  SF : Trie
  rs : List Nat
  ports : List Nat
  gl : List Nat
  el : List Nat
  q : SPw
  R0 : RT
  RF : RT
  RB : RT

/-- the parameters of the end check: only the x, y and slot registers -/
def WCert.pe (c : WCert) : GLab.Par := ⟨c.p.h, 2 * c.v + c.R, c.p.d, c.p.K, c.p.tab⟩

/-- **the kernel facts** of an extended certificate -/
structure WValid (c : WCert) : Prop where
  hn : c.p.n = 2 * c.v + c.R + c.nc
  nr : c.q.nr = c.p.n
  tab : tabK c.p.h c.p.tab = true
  wtab : wtK c.p.h c.wt = true
  lab : segW c.p c.wt c.evs c.S0 c.SF c.rs = true
  labB : segW c.p c.wt c.evsB c.S0 c.SF c.rs = true
  ends : endKX c.pe c.v c.ports [] c.gl c.el c.S0 c.S0 c.SF = true
  scF : scalW c.q false c.evs c.R0 c.RF = true
  scB : scalW c.q true c.evsB c.R0 c.RB = true
  id0 : idK c.q c.R0 = true
  wfF : RT.wfK c.RF c.q.d = true
  wfB : RT.wfK c.RB c.q.d = true
  shF : shKn c.q c.v false c.RF (2 * c.v + c.R) = true
  shB : shKn c.q c.v true c.RB (2 * c.v + c.R) = true
  frF : freeK c.q c.RF = true
  frB : freeK c.q c.RB = true

/-- **the semantic facts** of an extended certificate (what `WValid` gives by `WValid.toS`; a generator that cuts
the replays into segments composes `run`/`runB` by `RunW.append` and `scF`/`scB` by `ScalOK.append`) -/
structure WValidS (c : WCert) : Prop where
  hn : c.p.n = 2 * c.v + c.R + c.nc
  nr : c.q.nr = c.p.n
  tab : tabK c.p.h c.p.tab = true
  run : RunW c.p c.wt c.S0 c.evs c.SF c.rs
  runB : RunW c.p c.wt c.S0 c.evsB c.SF c.rs
  ends : endKX c.pe c.v c.ports [] c.gl c.el c.S0 c.S0 c.SF = true
  par : ParOK c.q
  scF : ScalOK c.q false c.evs c.R0 c.RF
  scB : ScalOK c.q true c.evsB c.R0 c.RB
  id0 : idK c.q c.R0 = true
  wfF : RT.wfK c.RF c.q.d = true
  wfB : RT.wfK c.RB c.q.d = true
  shF : shKn c.q c.v false c.RF (2 * c.v + c.R) = true
  shB : shKn c.q c.v true c.RB (2 * c.v + c.R) = true
  frF : freeK c.q c.RF = true
  frB : freeK c.q c.RB = true

/-- the kernel facts give the semantic facts -/
theorem WValid.toS {c : WCert} (V : WValid c) : WValidS c where
  hn := V.hn
  nr := V.nr
  tab := V.tab
  run := RunW.of_seg V.tab V.wtab V.lab
  runB := RunW.of_seg V.tab V.wtab V.labB
  ends := V.ends
  par := ParOK.of_scalW V.scF
  scF := ScalOK.of_check V.scF
  scB := ScalOK.of_check V.scB
  id0 := V.id0
  wfF := V.wfF
  wfB := V.wfB
  shF := V.shF
  shB := V.shB
  frF := V.frF
  frB := V.frB

/-- the exit slots -/
noncomputable def WCert.exits (c : WCert) : Finset (Fin c.R) :=
  univ.filter (fun q : Fin c.R => memK (2 * c.v + q.val) c.el = true)

section Inv
variable (c : WCert)

/-- the live roles inside the box -/
def incL : CR.L3 (Fin c.v) (Fin c.R) → Box (Fin c.v) (Fin c.R) (Fin c.nc)
  | .inl b => .inl b
  | .inr q => .inr (.inl q)

variable {c}
variable {emb : Box (Fin c.v) (Fin c.R) (Fin c.nc) → Nat} {un : Nat → Box (Fin c.v) (Fin c.R) (Fin c.nc)}

/-- labels of the live roles in a state -/
noncomputable def WCert.L (c : WCert) (emb : Box (Fin c.v) (Fin c.R) (Fin c.nc) → Nat) (S : Trie) :
    CR.L3 (Fin c.v) (Fin c.R) → SLbl (Fin c.p.h) :=
  fun r => c.p.labS S (emb (incL c r))

/-- the entrance label of a slot (adapted base for an exit slot) -/
noncomputable def WCert.ent (c : WCert) (emb : Box (Fin c.v) (Fin c.R) (Fin c.nc) → Nat) (q : Fin c.R) :
    SLbl (Fin c.p.h) :=
  XEX.lab0X c.exits (c.L emb c.S0) (c.L emb c.SF) (CR.lS q)

/-- the exit label of a slot -/
noncomputable def WCert.exq (c : WCert) (emb : Box (Fin c.v) (Fin c.R) (Fin c.nc) → Nat) (q : Fin c.R) :
    SLbl (Fin c.p.h) :=
  if q ∈ c.exits then XEX.exlA (c.L emb c.S0 (CR.lS q)) (c.L emb c.SF (CR.lS q)) else (c.ent emb q).top

/-- the role hypotheses of a certificate -/
structure WRoles (c : WCert) (emb : Box (Fin c.v) (Fin c.R) (Fin c.nc) → Nat)
    (un : Nat → Box (Fin c.v) (Fin c.R) (Fin c.nc)) : Prop where
  C : GLab.Ctx c.p emb un
  num : Num c.v c.R c.nc emb

theorem WRoles.sctx (hnr : c.q.nr = c.p.n) (Ro : WRoles c emb un) : SCtx c.q emb un :=
  ⟨Ro.C.hun, fun r hr => Ro.C.hin r (by rw [← hnr]; exact hr), fun j => by rw [hnr]; exact Ro.C.hlt j⟩

end Inv

end KLW

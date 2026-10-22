import Submission.Work.XHostT.TCertW
import Submission.Work.XHostT.TGeom

/-!
# (key: bridge-host-cross) WARP variant: the cross-replica hosted word on `LC (Fin 8) H l` with providers `GInvW ... Ok`

(gen_tgeom.py --warp: TGeom.lean with `GInvW` providers, the frames of TProvW.lean, the window facts `hOk`; the
schedule `HostSchedT` is XHostT's.)

* `HostSchedT nR Sl T`: a global order of the `9 nR` calls (`tm`, `cl`), a host for EVERY slot of every call in an idle
  data role of ANY replica during its window (`host`, `hostInj`, `hostWin`), the remainders `hrem`; `fits res`: every
  host's residual load over all calls plus its remainder is the rank of its kind;
* `HostSchedT.lo` / `hi`: the first and last global time of the window of host kind `(ρh, c)` (`win_iff`: the window
  condition of `XNet` in these terms); `useT`: the sub-stages of a host chain are the global times of its window;
  `LHK_useT`: the load of a host chain is the schedule's load;
* ONE `XHostD.host_framesK` per host chain (`chainTW_ex`), with the start and end frames and host forms of lg-a2a4's
  geometry (`XHostD.x0_*`, `x1_*`, `hf_*`: Shea's GGeom / h-L3-build);
* `xnetGeom`: the network as a term of `XNet` (`nb = 0`); `bridgeHostT_gcert`: its `GCert` with the unit price
  `unitPriceT Ic S`.
Written by p-a3/tools/gen_tgeom.py (wht45/lever, 19 Oct 2026), after lg-a2a4's / fsp-perrun's / h-L3-build's HGeom
(wht43) on Ryan Shea's complex588 tree (Nil Mamano's gen401 on jacklightChen's #377 geometry, Dugongue's #401, Jacob
Sussman's engine and stage geometry); hosting by DaysSky (PR #442); prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostTW
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD XHostT
noncomputable section


section Geom
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the start frame of the idle climb of kind `c` (lg-a2a4's `x0_*`). -/
def x0KW (tv : T → Space H) (base : T → OBase H) (l : H) (c : Fin 9) :
    Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l) :=
  match c.val with
  | 0 => x0t_A2 tv base l
  | 1 => x0t_B2 tv base l
  | 2 => x0t_A3 tv base l
  | 3 => x0t_B3 tv base l
  | 4 => x0t_A4 tv base l
  | 5 => x0t_B4 tv base l
  | 6 => x0t_F1 tv base l
  | 7 => x0t_F2 tv base l
  | _ => x0t_F3 tv base l

/-- the end frame of the idle climb of kind `c` (lg-a2a4's `x1_*`). -/
def x1KW (tv : T → Space H) (base : T → OBase H) (l : H) (c : Fin 9) :
    Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l) :=
  match c.val with
  | 0 => x1t_A2 tv base l
  | 1 => x1t_B2 tv base l
  | 2 => x1t_A3 tv base l
  | 3 => x1t_B3 tv base l
  | 4 => x1t_A4 tv base l
  | 5 => x1t_B4 tv base l
  | 6 => x1t_F1 tv base l
  | 7 => x1t_F2 tv base l
  | _ => x1t_F3 tv base l

lemma hfKW (tv : T → Space H) (base : T → OBase H) (l : H) (hbase : ∀ t, tv t = (base t).v l)
    (hH : Fintype.card H = 9) (c : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0KW tv base l c d j) (x1KW tv base l c d j) (rankOf c.val) := by
  fin_cases c
  · exact hft_A2 tv base l hbase hH d j
  · exact hft_B2 tv base l hbase hH d j
  · exact hft_A3 tv base l hbase hH d j
  · exact hft_B3 tv base l hbase hH d j
  · exact hft_A4 tv base l hbase hH d j
  · exact hft_B4 tv base l hbase hH d j
  · exact hft_F1 tv base l hbase hH d j
  · exact hft_F2 tv base l hbase hH d j
  · exact hft_F3 tv base l hbase hH d j

end Geom


section Net
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}
variable {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
variable (I : GInvW H T Sl C Ok) (Ic : Fin nR → Fin 9 → GInvW H T Sl C Ok) (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv)
  (base : T → OBase H) (l : H)
  (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H = 9)
  (hOk : ∀ (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)), Ok (win401N l hH n d))
  (S : HostSchedT nR Sl T) (hfit : S.fits (resIcW Ic))

/-- the residual climb of slot `q` in sub-stage `k` of the host chain `(ρh, c)`: the call's stage window. -/
def wnTW (ρh : Fin nR) (c : Fin 9) (k : ℕ) (d : Orth (BC.LC (Fin 8) H l)) (q : Sl) : CMat (BC.LC (Fin 8) H l) :=
  entW (win401N l hH (S.callAt (ρh, 0) (S.lo ρh c + k)).2.val d).X
    ((Ic (S.callAt (ρh, 0) (S.lo ρh c + k)).1 (S.callAt (ρh, 0) (S.lo ρh c + k)).2).ent q)

include hbase hfit in
/-- **the host chain `(ρh, c)`** over the global times of its window (ONE `host_framesK`). -/
lemma chainTW_ex (ρh : Fin nR) (c : Fin 9) :
    ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0KW I.tv base l c d j) ∧
      (∀ k < S.KT ρh c, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < S.KT ρh c, ∀ d q j, S.useT ρh c k q = some j → wnTW Ic l hH S ρh c k d q * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < S.KT ρh c, ∀ d j, (∀ q, S.useT ρh c k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb (S.KT ρh c) d j) (x1KW I.tv base l c d j) (fun φ => bcost φ (S.hrem ρh c j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (S.useT ρh c) (S.resT' (resIcW Ic) ρh c) (S.KT ρh c) j + S.hrem ρh c j = rankOf c.val :=
    fun j => by rw [S.LHK_useT]; exact hfit ρh c j
  have hrk : rankOf c.val ≤ 48 := by fin_cases c <;> decide
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (S.useT ρh c) (S.resT' (resIcW Ic) ρh c)
    (wnTW Ic l hH S ρh c) (S.KT ρh c)
    (fun k _ => S.useT_one ρh c k) (fun k _ d q => entW_form _ _)
    (x0KW I.tv base l c) (x1KW I.tv base l c) (fun _ => rankOf c.val) (fun d j => hfKW I.tv base l hbase hH c d j)
    (fun j => by have := hf j; omega)
    (fun j => by rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : rankOf c.val - LHK (S.useT ρh c) (S.resT' (resIcW Ic) ρh c) (S.KT ρh c) j = S.hrem ρh c j := by
    have := hf j; omega
  have h := hE d j
  rw [e] at h
  exact h

def zbTW (ρh : Fin nR) (c : Fin 9) := Classical.choose (chainTW_ex I Ic base l hbase hH S hfit ρh c)
def zpTW (ρh : Fin nR) (c : Fin 9) := Classical.choose (Classical.choose_spec (chainTW_ex I Ic base l hbase hH S hfit ρh c))
def zTW_spec (ρh : Fin nR) (c : Fin 9) :=
  Classical.choose_spec (Classical.choose_spec (chainTW_ex I Ic base l hbase hH S hfit ρh c))

/-- the host chain `(ρh, c)` at global time `τ` (start frame before the window, end frame after it). -/
def hbTW (ρh : Fin nR) (c : Fin 9) (τ : ℕ) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) : CMat (BC.LC (Fin 8) H l) :=
  if τ < S.lo ρh c then x0KW I.tv base l c d j
  else if τ ≤ S.hi ρh c + 1 then zbTW I Ic base l hbase hH S hfit ρh c (τ - S.lo ρh c) d j
  else zbTW I Ic base l hbase hH S hfit ρh c (S.KT ρh c) d j

def hpTW (ρh : Fin nR) (c : Fin 9) (τ : ℕ) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) : CMat (BC.LC (Fin 8) H l) :=
  if S.lo ρh c ≤ τ ∧ τ ≤ S.hi ρh c then zpTW I Ic base l hbase hH S hfit ρh c (τ - S.lo ρh c) d j
  else hbTW I Ic base l hbase hH S hfit ρh c τ d j

lemma hHP_TW (ρh : Fin nR) (c : Fin 9) (τ : ℕ) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    GReach (hbTW I Ic base l hbase hH S hfit ρh c τ d j) (hpTW I Ic base l hbase hH S hfit ρh c τ d j) (fun _ => 0) := by
  unfold hpTW
  split_ifs with h
  · have hb : hbTW I Ic base l hbase hH S hfit ρh c τ d j = zbTW I Ic base l hbase hH S hfit ρh c (τ - S.lo ρh c) d j := by
      unfold hbTW
      rw [if_neg (by omega), if_pos (by omega)]
    rw [hb]
    exact (zTW_spec I Ic base l hbase hH S hfit ρh c).2.1 _ (by unfold HostSchedT.KT; omega) d j
  · exact GReach.refl _

lemma hHZ_TW (ρ : Fin nR) (lc : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (q : Sl) (ρh : Fin nR) (c : Fin 9) (j : Bool × T)
    (h : S.host ρ lc q = (ρh, c, j)) :
    entW (win401N l hH lc.val d).X ((Ic ρ lc).ent q) * hpTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc) d j
      = hbTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc + 1) d j := by
  have hw := (S.win_iff ρh c (S.tm ρ lc)).mp (by have := S.hostWin ρ lc q; rw [h] at this; exact this)
  have hp : hpTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc) d j
      = zpTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc - S.lo ρh c) d j := by
    unfold hpTW; rw [if_pos hw]
  have hb : hbTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc + 1) d j
      = zbTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc - S.lo ρh c + 1) d j := by
    unfold hbTW
    rw [if_neg (by omega), if_pos (by omega), show S.tm ρ lc + 1 - S.lo ρh c = S.tm ρ lc - S.lo ρh c + 1 by omega]
  rw [hp, hb]
  have hu := (zTW_spec I Ic base l hbase hH S hfit ρh c).2.2.1 (S.tm ρ lc - S.lo ρh c) (by unfold HostSchedT.KT; omega)
    d q j (S.useT_of h)
  have ew : wnTW Ic l hH S ρh c (S.tm ρ lc - S.lo ρh c) d q = entW (win401N l hH lc.val d).X ((Ic ρ lc).ent q) := by
    unfold wnTW
    rw [show S.lo ρh c + (S.tm ρ lc - S.lo ρh c) = S.tm ρ lc by omega, S.callAt_tm]
  rw [ew] at hu
  exact hu

lemma hHZn_TW (ρ : Fin nR) (lc : Fin 9) (ρh : Fin nR) (c : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T)
    (h : ∀ q, some (S.host ρ lc q) ≠ some (ρh, c, j)) :
    hbTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc + 1) d j = hpTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc) d j := by
  have hlh := S.lo_le_hi ρh c
  by_cases hw : S.lo ρh c ≤ S.tm ρ lc ∧ S.tm ρ lc ≤ S.hi ρh c
  · have hp : hpTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc) d j
        = zpTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc - S.lo ρh c) d j := by
      unfold hpTW; rw [if_pos hw]
    have hb : hbTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc + 1) d j
        = zbTW I Ic base l hbase hH S hfit ρh c (S.tm ρ lc - S.lo ρh c + 1) d j := by
      unfold hbTW
      rw [if_neg (by omega), if_pos (by omega), show S.tm ρ lc + 1 - S.lo ρh c = S.tm ρ lc - S.lo ρh c + 1 by omega]
    rw [hp, hb]
    refine (zTW_spec I Ic base l hbase hH S hfit ρh c).2.2.2.1 (S.tm ρ lc - S.lo ρh c) (by unfold HostSchedT.KT; omega)
      d j (fun q hq => ?_)
    have e := S.useT_some hq
    rw [show S.lo ρh c + (S.tm ρ lc - S.lo ρh c) = S.tm ρ lc by omega, S.callAt_tm] at e
    exact h q (by rw [e])
  · unfold hpTW
    rw [if_neg hw]
    unfold hbTW
    by_cases h1 : S.tm ρ lc < S.lo ρh c
    · rw [if_pos h1]
      by_cases h2 : S.tm ρ lc + 1 < S.lo ρh c
      · rw [if_pos h2]
      · rw [if_neg h2, if_pos (by omega), show S.tm ρ lc + 1 - S.lo ρh c = 0 by omega]
        exact (zTW_spec I Ic base l hbase hH S hfit ρh c).1 d j
    · rw [if_neg h1, if_neg (by omega), if_neg (show ¬ (S.tm ρ lc + 1 ≤ S.hi ρh c + 1) by omega)]
      by_cases h3 : S.tm ρ lc ≤ S.hi ρh c + 1
      · rw [if_pos h3, show S.tm ρ lc - S.lo ρh c = S.KT ρh c by unfold HostSchedT.KT; omega]
      · rw [if_neg h3]

lemma hH0_TW (ρh : Fin nR) (c : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    hbTW I Ic base l hbase hH S hfit ρh c (S.lo ρh c) d j = x0KW I.tv base l c d j := by
  have hlh := S.lo_le_hi ρh c
  unfold hbTW
  rw [if_neg (lt_irrefl _), if_pos (by omega), Nat.sub_self]
  exact (zTW_spec I Ic base l hbase hH S hfit ρh c).1 d j

lemma hHE_TW (ρh : Fin nR) (c : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    GReach (hbTW I Ic base l hbase hH S hfit ρh c (S.hi ρh c + 1) d j) (x1KW I.tv base l c d j)
      (fun φ => bcost φ (S.hrem ρh c j)) := by
  have hlh := S.lo_le_hi ρh c
  have hb : hbTW I Ic base l hbase hH S hfit ρh c (S.hi ρh c + 1) d j
      = zbTW I Ic base l hbase hH S hfit ρh c (S.KT ρh c) d j := by
    unfold hbTW
    rw [if_neg (by omega), if_pos le_rfl]
    rfl
  rw [hb]
  exact (zTW_spec I Ic base l hbase hH S hfit ρh c).2.2.2.2 d j


/-- **The cross-replica hosted nine-stage word as a term of `XNet`** on the label space `LC (Fin 8) H l`. -/
def xnetGeomW : XNetW H T Sl C (BC.LC (Fin 8) H l) (Orth (BC.LC (Fin 8) H l)) 0 nR Ok where
  I := I
  Ic := Ic
  hIc := hIc
  G0 := fun d => gwinC hB401 (by omega) d ∅
  G1 := fun d => gwinC hB401 (by omega) d (qC bs401_1)
  G2 := fun d => gwinC hB401 (by omega) d (qC bs401_2)
  G3 := fun d => gwinC hB401 (by omega) d (qC bs401_3)
  G4 := fun d => gwinC hB401 (by omega) d (qC bs401_4)
  G5 := fun d => gwinC hB401 (by omega) d (qC bs401_5)
  G6 := fun d => gwinC hB401 (by omega) d (qC bs401_6)
  G7 := fun d => gwinC hB401 (by omega) d (qC bs401_7)
  G8 := fun d => gwinC hB401 (by omega) d (qC bs401_8)
  hok0 := fun d => hOk 0 d
  hok1 := fun d => hOk 1 d
  hok2 := fun d => hOk 2 d
  hok3 := fun d => hOk 3 d
  hok4 := fun d => hOk 4 d
  hok5 := fun d => hOk 5 d
  hok6 := fun d => hOk 6 d
  hok7 := fun d => hOk 7 d
  hok8 := fun d => hOk 8 d
  r1 := fun t => RrC (base t) l (0 : Fin 8)
  r2 := fun t => RrC (base t) l (1 : Fin 8)
  r3 := fun t => RrC (base t) l (2 : Fin 8)
  r4 := fun t => RrC (base t) l (3 : Fin 8)
  r5 := fun t => RrC (base t) l (4 : Fin 8)
  r6 := fun t => RrC (base t) l (5 : Fin 8)
  r7 := fun t => RrC (base t) l (6 : Fin 8)
  r8 := fun t => RrC (base t) l (7 : Fin 8)
  N0 := fun ρ d q => entN (gwinC hB401 (by omega) d ∅).X ((Ic ρ 0).ent q)
  Wn0 := fun ρ d q => entW (gwinC hB401 (by omega) d ∅).X ((Ic ρ 0).ent q)
  N1 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_1)).X ((Ic ρ 1).ent q)
  Wn1 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_1)).X ((Ic ρ 1).ent q)
  N2 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_2)).X ((Ic ρ 2).ent q)
  Wn2 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_2)).X ((Ic ρ 2).ent q)
  N3 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_3)).X ((Ic ρ 3).ent q)
  Wn3 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_3)).X ((Ic ρ 3).ent q)
  N4 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_4)).X ((Ic ρ 4).ent q)
  Wn4 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_4)).X ((Ic ρ 4).ent q)
  N5 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_5)).X ((Ic ρ 5).ent q)
  Wn5 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_5)).X ((Ic ρ 5).ent q)
  N6 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_6)).X ((Ic ρ 6).ent q)
  Wn6 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_6)).X ((Ic ρ 6).ent q)
  N7 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_7)).X ((Ic ρ 7).ent q)
  Wn7 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_7)).X ((Ic ρ 7).ent q)
  N8 := fun ρ d q => entN (gwinC hB401 (by omega) d (qC bs401_8)).X ((Ic ρ 8).ent q)
  Wn8 := fun ρ d q => entW (gwinC hB401 (by omega) d (qC bs401_8)).X ((Ic ρ 8).ent q)
  tm := S.tm
  cl := S.cl
  htm_lt := S.htm_lt
  htm_inj := S.htm_inj
  htm_mono := S.htm_mono
  hcl := S.hcl
  hostAt := fun ρ l q => some (S.host ρ l q)
  hostInj := fun ρ l q q' j h h' => S.hostInj ρ l q q' (Option.some_injective _ (h.trans h'.symm))
  hostWin := fun ρ l q ρh c j h => by
    have e := Option.some_injective _ h
    have := S.hostWin ρ l q
    rw [e] at this
    exact this
  bk := fun ρ l q h => absurd h (Option.some_ne_none _)
  hinj := fun ρ l q q' h => absurd h (Option.some_ne_none _)
  Zb := fun _ _ b => b.elim0
  Zp := fun _ _ b => b.elim0
  pad := fun b => b.elim0
  Hb := hbTW I Ic base l hbase hH S hfit
  Hp := hpTW I Ic base l hbase hH S hfit
  hrem := S.hrem
  u := fun g t => (BBC (base t) l g).v (Sum.inl l)
  YF := fun g t => frame (BBC (base t) l g) (univ \ {Sum.inl l})
  hm := two_le_card_LC hB401 (by omega)
  cX4 := fun φ => bcost φ 0
  cY4 := fun φ => bcost φ 0
  inv0 := fun g t => ⟨unframeM (g.1 * Matrix.fromBlocks (tt (I.tv t)) 0 0 (diagI ∅) * g.1ᵀ),
    frameM_unframeM _⟩
  z0 := fun g => PhiC_zero_empty g
  hN0 := fun ρ d q => entN_spec _ _
  hW0 := fun ρ d q => entW_spec _ _
  hN1 := fun ρ d q => entN_spec _ _
  hW1 := fun ρ d q => entW_spec _ _
  hN2 := fun ρ d q => entN_spec _ _
  hW2 := fun ρ d q => entW_spec _ _
  hN3 := fun ρ d q => entN_spec _ _
  hW3 := fun ρ d q => entW_spec _ _
  hN4 := fun ρ d q => entN_spec _ _
  hW4 := fun ρ d q => entW_spec _ _
  hN5 := fun ρ d q => entN_spec _ _
  hW5 := fun ρ d q => entW_spec _ _
  hN6 := fun ρ d q => entN_spec _ _
  hW6 := fun ρ d q => entW_spec _ _
  hN7 := fun ρ d q => entN_spec _ _
  hW7 := fun ρ d q => entW_spec _ _
  hN8 := fun ρ d q => entN_spec _ _
  hW8 := fun ρ d q => entW_spec _ _
  x01 := fun g t => g401t_x01 I.tv base l hbase g t
  y01 := fun g t => g401t_y01 I.tv base l hbase g t
  x12 := fun g t => g401t_xx I.tv base l hbase bs401_1 0 1 (Finset.mem_singleton_self _) mem401_1 g t
  y12 := fun g t => g401t_yy I.tv base l hbase bs401_1 0 1 (Finset.mem_singleton_self _) mem401_1 g t
  x23 := fun g t => g401t_xx I.tv base l hbase bs401_2 1 2 (Finset.mem_insert_self _ _) mem401_2 g t
  y23 := fun g t => g401t_yy I.tv base l hbase bs401_2 1 2 (Finset.mem_insert_self _ _) mem401_2 g t
  x34 := fun g t => g401t_xx I.tv base l hbase bs401_3 2 3 (Finset.mem_insert_self _ _) mem401_3 g t
  y34 := fun g t => g401t_yy I.tv base l hbase bs401_3 2 3 (Finset.mem_insert_self _ _) mem401_3 g t
  x45 := fun g t => g401t_xx I.tv base l hbase bs401_4 3 4 (Finset.mem_insert_self _ _) mem401_4 g t
  y45 := fun g t => g401t_yy I.tv base l hbase bs401_4 3 4 (Finset.mem_insert_self _ _) mem401_4 g t
  x56 := fun g t => g401t_xx I.tv base l hbase bs401_5 4 5 (Finset.mem_insert_self _ _) mem401_5 g t
  y56 := fun g t => g401t_yy I.tv base l hbase bs401_5 4 5 (Finset.mem_insert_self _ _) mem401_5 g t
  x67 := fun g t => g401t_xx I.tv base l hbase bs401_6 5 6 (Finset.mem_insert_self _ _) mem401_6 g t
  y67 := fun g t => g401t_yy I.tv base l hbase bs401_6 5 6 (Finset.mem_insert_self _ _) mem401_6 g t
  x78 := fun g t => g401t_xx I.tv base l hbase bs401_7 6 7 (Finset.mem_insert_self _ _) mem401_7 g t
  y78 := fun g t => g401t_yy I.tv base l hbase bs401_7 6 7 (Finset.mem_insert_self _ _) mem401_7 g t
  z0b := fun g b => b.elim0
  hP := fun τ g b => b.elim0
  hZ0 := fun ρ g q h => absurd h (Option.some_ne_none _)
  hZ1 := fun ρ g q h => absurd h (Option.some_ne_none _)
  hZ2 := fun ρ g q h => absurd h (Option.some_ne_none _)
  hZ3 := fun ρ g q h => absurd h (Option.some_ne_none _)
  hZ4 := fun ρ g q h => absurd h (Option.some_ne_none _)
  hZ5 := fun ρ g q h => absurd h (Option.some_ne_none _)
  hZ6 := fun ρ g q h => absurd h (Option.some_ne_none _)
  hZ7 := fun ρ g q h => absurd h (Option.some_ne_none _)
  hZ8 := fun ρ g q h => absurd h (Option.some_ne_none _)
  hZn := fun ρ l g b _ => b.elim0
  bpad := fun g b => b.elim0
  hHP := fun ρh c τ g j => hHP_TW I Ic base l hbase hH S hfit ρh c τ g j
  hHZ0 := fun ρ g q ρh c j h => hHZ_TW I Ic base l hbase hH S hfit ρ 0 g q ρh c j (Option.some_injective _ h)
  hHZ1 := fun ρ g q ρh c j h => hHZ_TW I Ic base l hbase hH S hfit ρ 1 g q ρh c j (Option.some_injective _ h)
  hHZ2 := fun ρ g q ρh c j h => hHZ_TW I Ic base l hbase hH S hfit ρ 2 g q ρh c j (Option.some_injective _ h)
  hHZ3 := fun ρ g q ρh c j h => hHZ_TW I Ic base l hbase hH S hfit ρ 3 g q ρh c j (Option.some_injective _ h)
  hHZ4 := fun ρ g q ρh c j h => hHZ_TW I Ic base l hbase hH S hfit ρ 4 g q ρh c j (Option.some_injective _ h)
  hHZ5 := fun ρ g q ρh c j h => hHZ_TW I Ic base l hbase hH S hfit ρ 5 g q ρh c j (Option.some_injective _ h)
  hHZ6 := fun ρ g q ρh c j h => hHZ_TW I Ic base l hbase hH S hfit ρ 6 g q ρh c j (Option.some_injective _ h)
  hHZ7 := fun ρ g q ρh c j h => hHZ_TW I Ic base l hbase hH S hfit ρ 7 g q ρh c j (Option.some_injective _ h)
  hHZ8 := fun ρ g q ρh c j h => hHZ_TW I Ic base l hbase hH S hfit ρ 8 g q ρh c j (Option.some_injective _ h)
  hHZn := fun ρ lc ρh c g j h => hHZn_TW I Ic base l hbase hH S hfit ρ lc ρh c g j h
  hH0_A2 := fun ρ g t => by
    have h1 := hH0_TW I Ic base l hbase hH S hfit ρ 0 g (false, t)
    have h2 := hH0_TW I Ic base l hbase hH S hfit ρ 0 g (true, t)
    rw [lo_A2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_B2 := fun ρ g t => by
    have h1 := hH0_TW I Ic base l hbase hH S hfit ρ 1 g (false, t)
    have h2 := hH0_TW I Ic base l hbase hH S hfit ρ 1 g (true, t)
    rw [lo_B2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_A3 := fun ρ g t => by
    have h1 := hH0_TW I Ic base l hbase hH S hfit ρ 2 g (false, t)
    have h2 := hH0_TW I Ic base l hbase hH S hfit ρ 2 g (true, t)
    rw [lo_A3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_B3 := fun ρ g t => by
    have h1 := hH0_TW I Ic base l hbase hH S hfit ρ 3 g (false, t)
    have h2 := hH0_TW I Ic base l hbase hH S hfit ρ 3 g (true, t)
    rw [lo_B3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_A4 := fun ρ g t => by
    have h1 := hH0_TW I Ic base l hbase hH S hfit ρ 4 g (false, t)
    have h2 := hH0_TW I Ic base l hbase hH S hfit ρ 4 g (true, t)
    rw [lo_A4 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_B4 := fun ρ g t => by
    have h1 := hH0_TW I Ic base l hbase hH S hfit ρ 5 g (false, t)
    have h2 := hH0_TW I Ic base l hbase hH S hfit ρ 5 g (true, t)
    rw [lo_B4 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_F1 := fun ρ g t => by
    have h1 := hH0_TW I Ic base l hbase hH S hfit ρ 6 g (false, t)
    have h2 := hH0_TW I Ic base l hbase hH S hfit ρ 6 g (true, t)
    rw [lo_F1 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_F2 := fun ρ g t => by
    have h1 := hH0_TW I Ic base l hbase hH S hfit ρ 7 g (false, t)
    have h2 := hH0_TW I Ic base l hbase hH S hfit ρ 7 g (true, t)
    rw [lo_F2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_F3 := fun ρ g t => by
    have h1 := hH0_TW I Ic base l hbase hH S hfit ρ 8 g (false, t)
    have h2 := hH0_TW I Ic base l hbase hH S hfit ρ 8 g (true, t)
    rw [lo_F3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_A2 := fun ρ g t => by
    have h1 := hHE_TW I Ic base l hbase hH S hfit ρ 0 g (false, t)
    have h2 := hHE_TW I Ic base l hbase hH S hfit ρ 0 g (true, t)
    rw [hi_A2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_B2 := fun ρ g t => by
    have h1 := hHE_TW I Ic base l hbase hH S hfit ρ 1 g (false, t)
    have h2 := hHE_TW I Ic base l hbase hH S hfit ρ 1 g (true, t)
    rw [hi_B2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_A3 := fun ρ g t => by
    have h1 := hHE_TW I Ic base l hbase hH S hfit ρ 2 g (false, t)
    have h2 := hHE_TW I Ic base l hbase hH S hfit ρ 2 g (true, t)
    rw [hi_A3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_B3 := fun ρ g t => by
    have h1 := hHE_TW I Ic base l hbase hH S hfit ρ 3 g (false, t)
    have h2 := hHE_TW I Ic base l hbase hH S hfit ρ 3 g (true, t)
    rw [hi_B3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_A4 := fun ρ g t => by
    have h1 := hHE_TW I Ic base l hbase hH S hfit ρ 4 g (false, t)
    have h2 := hHE_TW I Ic base l hbase hH S hfit ρ 4 g (true, t)
    rw [hi_A4 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_B4 := fun ρ g t => by
    have h1 := hHE_TW I Ic base l hbase hH S hfit ρ 5 g (false, t)
    have h2 := hHE_TW I Ic base l hbase hH S hfit ρ 5 g (true, t)
    rw [hi_B4 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_F1 := fun ρ g t => by
    have h1 := hHE_TW I Ic base l hbase hH S hfit ρ 6 g (false, t)
    have h2 := hHE_TW I Ic base l hbase hH S hfit ρ 6 g (true, t)
    rw [hi_F1 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_F2 := fun ρ g t => by
    have h1 := hHE_TW I Ic base l hbase hH S hfit ρ 7 g (false, t)
    have h2 := hHE_TW I Ic base l hbase hH S hfit ρ 7 g (true, t)
    rw [hi_F2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_F3 := fun ρ g t => by
    have h1 := hHE_TW I Ic base l hbase hH S hfit ρ 8 g (false, t)
    have h2 := hHE_TW I Ic base l hbase hH S hfit ρ 8 g (true, t)
    rw [hi_F3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  fX4 := fun g t => g401t_fX4 I.tv base l hbase hH g t
  fY4 := fun g t => g401t_fY4 I.tv base l hbase hH g t
  term := fun g t => g401t_term I.tv base l hbase g t

end Net

section End
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}

/-- **the unit price of the cross-replica hosted word**: every call (its own provider's price) and the remaining
climbs of every host chain. -/
def unitPriceTW {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
    (Ic : Fin nR → Fin 9 → GInvW H T Sl C Ok) (S : HostSchedT nR Sl T) (φ : ℕ → ℝ) : ℝ :=
  (∑ ρ : Fin nR, ∑ l : Fin 9, (Ic ρ l).cost φ) + ∑ ρ : Fin nR, ∑ c : Fin 9, hcostT S ρ c φ

lemma sum_tailUW {α Γ : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] {nb : ℕ}
    {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop} (N : XNetW H T Sl C α Γ nb nR Ok) (ρ : Fin nR) (φ : ℕ → ℝ) :
    ∑ l : Fin 9, N.tailU ρ l φ = (∑ c : Fin 9, N.hcost ρ c φ) + (Fintype.card T : ℝ) * (N.cX4 φ + N.cY4 φ) := by
  rw [sum_fin9, sum_fin9 (fun c => N.hcost ρ c φ)]
  simp only [XNetW.tailU_eq0, XNetW.tailU_eq1, XNetW.tailU_eq2, XNetW.tailU_eq3, XNetW.tailU_eq4, XNetW.tailU_eq5,
    XNetW.tailU_eq6, XNetW.tailU_eq7, XNetW.tailU_eq8]
  ring

/-- **Generalised certificate of the CROSS-REPLICA hosted nine-stage word** for a gauged invocation package (one
provider word per call) and a cross-replica host schedule. -/
theorem bridgeHostTW_gcert {Ok : ∀ {β : Type} [Fintype β] [DecidableEq β], GWin H β → Prop}
    (I : GInvW H T Sl C Ok) (Ic : Fin nR → Fin 9 → GInvW H T Sl C Ok)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (hH : Fintype.card H = 9) (l : H)
    (hOk : ∀ (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)), Ok (win401N l hH n d)) (S : HostSchedT nR Sl T)
    (hfit : S.fits (resIcW Ic)) :
    GCert (BC.LC (Fin 8) H l)
      (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
      (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceTW Ic S φ) := by
  have hb : ∀ t, ∃ A : OBase H, I.tv t = A.v l :=
    fun t => base_ex (I.tv t) (I.hunit t) (I.hgap t) l
  choose base hbase using hb
  have hc := xnetW_certificate (xnetGeomW I Ic hIc base l hbase hH hOk S hfit)
  have e : (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ)
        * (xnetGeomW I Ic hIc base l hbase hH hOk S hfit).unit φ)
      = (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceTW Ic S φ) := by
    funext φ
    congr 1
    simp only [XNetW.unit, XNetW.callU, Finset.sum_add_distrib, sum_tailUW, Finset.univ_eq_empty, Finset.sum_empty,
      add_zero, unitPriceTW]
    simp only [XNetW.hcost, hcostT, xnetGeomW, bcost_zero, add_zero, mul_zero, Finset.sum_const_zero]
  rw [e] at hc
  exact hc

end End
end
end XHostTW
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostTW.chainTW_ex
#print axioms OAI.PowerSaving.XHostTW.xnetGeomW
#print axioms OAI.PowerSaving.XHostTW.bridgeHostTW_gcert

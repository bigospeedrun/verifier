import Submission.Work.XHostT.TCert
import Submission.Work.XHostD.HEnd

/-!
# (key: bridge-host-cross) The CROSS-REPLICA hosted nine-stage word on the label space `LC (Fin 8) H l`

* `HostSchedT nR Sl T`: a global order of the `9 nR` calls (`tm`, `cl`), a host for EVERY slot of every call in an idle
  data role of ANY replica during its window (`host`, `hostInj`, `hostWin`), the remainders `hrem`; `fits res`: every
  host's residual load over all calls plus its remainder is the rank of its kind;
* `HostSchedT.lo` / `hi`: the first and last global time of the window of host kind `(ρh, c)` (`win_iff`: the window
  condition of `XNet` in these terms); `useT`: the sub-stages of a host chain are the global times of its window;
  `LHK_useT`: the load of a host chain is the schedule's load;
* ONE `XHostD.host_framesK` per host chain (`chainT_ex`), with the start and end frames and host forms of lg-a2a4's
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
namespace XHostT
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD
noncomputable section

/-- **A cross-replica host schedule** with every slot hosted. -/
structure HostSchedT (nR : ℕ) (Sl T : Type) where
  tm : Fin nR → Fin 9 → ℕ
  cl : Fin (9 * nR) → Fin nR × Fin 9
  htm_lt : ∀ ρ l, tm ρ l < 9 * nR
  htm_inj : ∀ ρ ρ' l l', tm ρ l = tm ρ' l' → ρ = ρ' ∧ l = l'
  htm_mono : ∀ ρ (l l' : Fin 9), l < l' → tm ρ l < tm ρ l'
  hcl : ∀ τ, tm (cl τ).1 (cl τ).2 = τ.val
  host : Fin nR → Fin 9 → Sl → Fin nR × Fin 9 × (Bool × T)
  hostInj : ∀ ρ l q q', host ρ l q = host ρ l q' → q = q'
  hostWin : ∀ ρ l q, inWin (host ρ l q).2.1.val (progT tm (host ρ l q).1 (tm ρ l)) = true
  hrem : Fin nR → Fin 9 → Bool × T → ℕ

namespace HostSchedT
variable {nR : ℕ} {Sl T : Type} [Fintype Sl] [DecidableEq Sl] [DecidableEq T] (S : HostSchedT nR Sl T)

/-- the residual load of host `(ρh, c, j)` over all calls. -/
def load (res : Fin nR → Fin 9 → Sl → ℕ) (ρh : Fin nR) (c : Fin 9) (j : Bool × T) : ℕ :=
  ∑ p ∈ (univ : Finset (Fin nR × Fin 9 × Sl)).filter (fun p => S.host p.1 p.2.1 p.2.2 = (ρh, c, j)),
    res p.1 p.2.1 p.2.2

/-- **the residual conditions**: every host's load plus its remainder is the rank of its kind. -/
def fits (res : Fin nR → Fin 9 → Sl → ℕ) : Prop := ∀ ρh c j, S.load res ρh c j + S.hrem ρh c j = rankOf c.val

lemma kz_lt (c : Fin 9) : kz c - 1 < 9 := by fin_cases c <;> decide
lemma kzK_lt (c : Fin 9) : kz c + kK c - 1 < 9 := by fin_cases c <;> decide

/-- the first global time of the window of host kind `(ρh, c)`. -/
def lo (ρh : Fin nR) (c : Fin 9) : ℕ := if kz c = 0 then 0 else S.tm ρh ⟨kz c - 1, kz_lt c⟩ + 1

/-- the last global time of the window of host kind `(ρh, c)`. -/
def hi (ρh : Fin nR) (c : Fin 9) : ℕ := S.tm ρh ⟨kz c + kK c - 1, kzK_lt c⟩

lemma tm_le (ρ : Fin nR) {l l' : Fin 9} (h : l ≤ l') : S.tm ρ l ≤ S.tm ρ l' := by
  rcases h.lt_or_eq with h | h
  · exact (S.htm_mono ρ l l' h).le
  · rw [h]

/-- `tm ρ m < τ` iff `m` is among the calls of `ρ` before `τ`. -/
lemma tm_lt_iff (ρ : Fin nR) (m : Fin 9) (τ : ℕ) : S.tm ρ m < τ ↔ m.val < progT S.tm ρ τ := by
  unfold progT
  constructor
  · intro h
    have hsub : Finset.Iic m ⊆ univ.filter (fun l : Fin 9 => S.tm ρ l < τ) := by
      intro l hl
      simp only [Finset.mem_Iic] at hl
      simp only [mem_filter, mem_univ, true_and]
      exact lt_of_le_of_lt (S.tm_le ρ hl) h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hc
    have hsub : univ.filter (fun l : Fin 9 => S.tm ρ l < τ) ⊆ Finset.Iio m := by
      intro l hl
      simp only [mem_filter, mem_univ, true_and] at hl
      simp only [Finset.mem_Iio]
      by_contra hl'
      exact hc (lt_of_le_of_lt (S.tm_le ρ (not_lt.mp hl')) hl)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

lemma inWin_iff (c : Fin 9) (k : ℕ) : inWin c.val k = true ↔ kz c ≤ k ∧ k < kz c + kK c := by
  fin_cases c <;> simp [inWin, kz, kK] <;> omega

/-- **the window condition in global times.** -/
lemma win_iff (ρh : Fin nR) (c : Fin 9) (τ : ℕ) :
    inWin c.val (progT S.tm ρh τ) = true ↔ S.lo ρh c ≤ τ ∧ τ ≤ S.hi ρh c := by
  rw [inWin_iff]
  have h1 : S.lo ρh c ≤ τ ↔ kz c ≤ progT S.tm ρh τ := by
    unfold lo
    split_ifs with h
    · rw [h]; simp
    · have := S.tm_lt_iff ρh ⟨kz c - 1, kz_lt c⟩ τ
      simp only at this
      omega
  have h2 : τ ≤ S.hi ρh c ↔ progT S.tm ρh τ < kz c + kK c := by
    unfold hi
    have := S.tm_lt_iff ρh ⟨kz c + kK c - 1, kzK_lt c⟩ τ
    simp only at this
    have hK : 1 ≤ kK c := by fin_cases c <;> decide
    omega
  rw [h1, h2]

lemma lo_le_hi (ρh : Fin nR) (c : Fin 9) : S.lo ρh c ≤ S.hi ρh c := by
  unfold lo hi
  split_ifs with h
  · omega
  · have hK : kz c - 1 < kz c + kK c - 1 := by fin_cases c <;> simp_all [kz, kK]
    exact S.htm_mono ρh _ _ (by rw [Fin.lt_def]; exact hK)

lemma hi_lt (ρh : Fin nR) (c : Fin 9) : S.hi ρh c < 9 * nR := S.htm_lt _ _

/-- the call at global time `τ` (`d` outside `[0, 9 nR)`). -/
def callAt (d : Fin nR × Fin 9) (τ : ℕ) : Fin nR × Fin 9 := if h : τ < 9 * nR then S.cl ⟨τ, h⟩ else d

lemma callAt_tm (d : Fin nR × Fin 9) (ρ : Fin nR) (l : Fin 9) : S.callAt d (S.tm ρ l) = (ρ, l) := by
  unfold callAt
  rw [dif_pos (S.htm_lt ρ l)]
  have e := S.hcl ⟨S.tm ρ l, S.htm_lt ρ l⟩
  obtain ⟨h1, h2⟩ := S.htm_inj _ _ _ _ e
  exact Prod.ext h1 h2

lemma tm_callAt (d : Fin nR × Fin 9) (τ : ℕ) (h : τ < 9 * nR) :
    S.tm (S.callAt d τ).1 (S.callAt d τ).2 = τ := by
  unfold callAt
  rw [dif_pos h]
  exact S.hcl _

/-- the slots of the host chain `(ρh, c)` in its sub-stage `k` (global time `lo + k`). -/
def useT (ρh : Fin nR) (c : Fin 9) (k : ℕ) (q : Sl) : Option (Bool × T) :=
  let p := S.callAt (ρh, 0) (S.lo ρh c + k)
  if (S.host p.1 p.2 q).1 = ρh ∧ (S.host p.1 p.2 q).2.1 = c then some (S.host p.1 p.2 q).2.2 else none

lemma useT_some {ρh : Fin nR} {c : Fin 9} {k : ℕ} {q : Sl} {j : Bool × T} (h : S.useT ρh c k q = some j) :
    S.host (S.callAt (ρh, 0) (S.lo ρh c + k)).1 (S.callAt (ρh, 0) (S.lo ρh c + k)).2 q = (ρh, c, j) := by
  simp only [useT] at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  rw [← h]
  exact Prod.ext hc.1 (Prod.ext hc.2 rfl)

lemma useT_of {ρ : Fin nR} {l : Fin 9} {q : Sl} {ρh : Fin nR} {c : Fin 9} {j : Bool × T}
    (h : S.host ρ l q = (ρh, c, j)) : S.useT ρh c (S.tm ρ l - S.lo ρh c) q = some j := by
  have hw := (S.win_iff ρh c (S.tm ρ l)).mp (by have := S.hostWin ρ l q; rw [h] at this; exact this)
  unfold useT
  rw [show S.lo ρh c + (S.tm ρ l - S.lo ρh c) = S.tm ρ l by omega, S.callAt_tm]
  simp [h]

lemma useT_one (ρh : Fin nR) (c : Fin 9) (k : ℕ) : OneUseK (S.useT ρh c) k := by
  intro q q' j h h'
  exact S.hostInj _ _ q q' ((S.useT_some h).trans (S.useT_some h').symm)

/-- the residual of slot `q` in sub-stage `k` of the host chain `(ρh, c)`. -/
def resT' (res : Fin nR → Fin 9 → Sl → ℕ) (ρh : Fin nR) (c : Fin 9) (k : ℕ) (q : Sl) : ℕ :=
  res (S.callAt (ρh, 0) (S.lo ρh c + k)).1 (S.callAt (ρh, 0) (S.lo ρh c + k)).2 q

/-- the number of sub-stages of the host chain `(ρh, c)`. -/
def KT (ρh : Fin nR) (c : Fin 9) : ℕ := S.hi ρh c + 1 - S.lo ρh c

lemma sum_filter_prod {α β : Type} [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] (f : α → β → ℕ) :
    ∑ a ∈ s, ∑ b ∈ t.filter (P a), f a b = ∑ x ∈ (s ×ˢ t).filter (fun x => P x.1 x.2), f x.1 x.2 := by
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_filter]

/-- **the load of a host chain is the schedule's load** (the sub-stages are the window's global times). -/
lemma LHK_useT (res : Fin nR → Fin 9 → Sl → ℕ) (ρh : Fin nR) (c : Fin 9) (j : Bool × T) :
    LHK (S.useT ρh c) (S.resT' res ρh c) (S.KT ρh c) j = S.load res ρh c j := by
  unfold LHK rrHK load
  rw [sum_filter_prod (range (S.KT ρh c)) univ (fun k q => S.useT ρh c k q = some j) (fun k q => S.resT' res ρh c k q)]
  have hlh := S.lo_le_hi ρh c
  have hhi := S.hi_lt ρh c
  refine Finset.sum_nbij' (fun x => ((S.callAt (ρh, 0) (S.lo ρh c + x.1)).1, (S.callAt (ρh, 0) (S.lo ρh c + x.1)).2, x.2))
    (fun p => (S.tm p.1 p.2.1 - S.lo ρh c, p.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.useT_some hx.2
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hw := (S.win_iff ρh c (S.tm p.1 p.2.1)).mp (by have := S.hostWin p.1 p.2.1 p.2.2; rw [hp] at this; exact this)
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    refine ⟨by unfold KT; omega, S.useT_of hp⟩
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
      and_true] at hx
    have hk : S.lo ρh c + x.1 < 9 * nR := by unfold KT at hx; omega
    simp only [S.tm_callAt _ _ hk, Nat.add_sub_cancel_left]
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hw := (S.win_iff ρh c (S.tm p.1 p.2.1)).mp (by have := S.hostWin p.1 p.2.1 p.2.2; rw [hp] at this; exact this)
    simp only
    rw [show S.lo ρh c + (S.tm p.1 p.2.1 - S.lo ρh c) = S.tm p.1 p.2.1 by omega, S.callAt_tm]
  · intro x hx
    rfl

end HostSchedT

section Geom
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the start frame of the idle climb of kind `c` (lg-a2a4's `x0_*`). -/
def x0K (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (c : Fin 9) :
    Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l) :=
  match c.val with
  | 0 => x0_A2 I base l
  | 1 => x0_B2 I base l
  | 2 => x0_A3 I base l
  | 3 => x0_B3 I base l
  | 4 => x0_A4 I base l
  | 5 => x0_B4 I base l
  | 6 => x0_F1 I base l
  | 7 => x0_F2 I base l
  | _ => x0_F3 I base l

/-- the end frame of the idle climb of kind `c` (lg-a2a4's `x1_*`). -/
def x1K (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (c : Fin 9) :
    Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l) :=
  match c.val with
  | 0 => x1_A2 I base l
  | 1 => x1_B2 I base l
  | 2 => x1_A3 I base l
  | 3 => x1_B3 I base l
  | 4 => x1_A4 I base l
  | 5 => x1_B4 I base l
  | 6 => x1_F1 I base l
  | 7 => x1_F2 I base l
  | _ => x1_F3 I base l

lemma hfK (I : GInvE H T Sl C) (base : T → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l)
    (hH : Fintype.card H = 9) (c : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    HostForm (x0K I base l c d j) (x1K I base l c d j) (rankOf c.val) := by
  fin_cases c
  · exact hf_A2 I base l hbase hH d j
  · exact hf_B2 I base l hbase hH d j
  · exact hf_A3 I base l hbase hH d j
  · exact hf_B3 I base l hbase hH d j
  · exact hf_A4 I base l hbase hH d j
  · exact hf_B4 I base l hbase hH d j
  · exact hf_F1 I base l hbase hH d j
  · exact hf_F2 I base l hbase hH d j
  · exact hf_F3 I base l hbase hH d j

end Geom

/-- the residual of slot `q` in call `(ρ, l)`: that of the call's own provider word. -/
def resIc {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
    [Fintype C] [DecidableEq C] {nR : ℕ} (Ic : Fin nR → Fin 9 → GInvE H T Sl C) (ρ : Fin nR) (l : Fin 9) (q : Sl) : ℕ :=
  Fintype.card H - ((Ic ρ l).ent q).dim

section Net
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}
variable (I : GInvE H T Sl C) (Ic : Fin nR → Fin 9 → GInvE H T Sl C) (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv)
  (base : T → OBase H) (l : H)
  (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H = 9) (S : HostSchedT nR Sl T) (hfit : S.fits (resIc Ic))

/-- the residual climb of slot `q` in sub-stage `k` of the host chain `(ρh, c)`: the call's stage window. -/
def wnT (ρh : Fin nR) (c : Fin 9) (k : ℕ) (d : Orth (BC.LC (Fin 8) H l)) (q : Sl) : CMat (BC.LC (Fin 8) H l) :=
  entW (win401N l hH (S.callAt (ρh, 0) (S.lo ρh c + k)).2.val d).X
    ((Ic (S.callAt (ρh, 0) (S.lo ρh c + k)).1 (S.callAt (ρh, 0) (S.lo ρh c + k)).2).ent q)

include hbase hfit in
/-- **the host chain `(ρh, c)`** over the global times of its window (ONE `host_framesK`). -/
lemma chainT_ex (ρh : Fin nR) (c : Fin 9) :
    ∃ (Zb Zp : ℕ → Orth (BC.LC (Fin 8) H l) → Bool × T → CMat (BC.LC (Fin 8) H l)),
      (∀ d j, Zb 0 d j = x0K I base l c d j) ∧
      (∀ k < S.KT ρh c, ∀ d j, GReach (Zb k d j) (Zp k d j) (fun _ => 0)) ∧
      (∀ k < S.KT ρh c, ∀ d q j, S.useT ρh c k q = some j → wnT Ic l hH S ρh c k d q * Zp k d j = Zb (k + 1) d j) ∧
      (∀ k < S.KT ρh c, ∀ d j, (∀ q, S.useT ρh c k q ≠ some j) → Zb (k + 1) d j = Zp k d j) ∧
      (∀ d j, GReach (Zb (S.KT ρh c) d j) (x1K I base l c d j) (fun φ => bcost φ (S.hrem ρh c j))) := by
  have hc : Fintype.card (BC.LC (Fin 8) H l) = 73 := card_LC401 l hH
  have hf : ∀ j, LHK (S.useT ρh c) (S.resT' (resIc Ic) ρh c) (S.KT ρh c) j + S.hrem ρh c j = rankOf c.val :=
    fun j => by rw [S.LHK_useT]; exact hfit ρh c j
  have hrk : rankOf c.val ≤ 48 := by fin_cases c <;> decide
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hE⟩ := host_framesK (S.useT ρh c) (S.resT' (resIc Ic) ρh c)
    (wnT Ic l hH S ρh c) (S.KT ρh c)
    (fun k _ => S.useT_one ρh c k) (fun k _ d q => entW_form _ _)
    (x0K I base l c) (x1K I base l c) (fun _ => rankOf c.val) (fun d j => hfK I base l hbase hH c d j)
    (fun j => by have := hf j; omega)
    (fun j => by rw [hc]; have := hf j; omega)
  refine ⟨Zb, Zp, h0, hP, hU, hN, fun d j => ?_⟩
  have e : rankOf c.val - LHK (S.useT ρh c) (S.resT' (resIc Ic) ρh c) (S.KT ρh c) j = S.hrem ρh c j := by
    have := hf j; omega
  have h := hE d j
  rw [e] at h
  exact h

def zbT (ρh : Fin nR) (c : Fin 9) := Classical.choose (chainT_ex I Ic base l hbase hH S hfit ρh c)
def zpT (ρh : Fin nR) (c : Fin 9) := Classical.choose (Classical.choose_spec (chainT_ex I Ic base l hbase hH S hfit ρh c))
def zT_spec (ρh : Fin nR) (c : Fin 9) :=
  Classical.choose_spec (Classical.choose_spec (chainT_ex I Ic base l hbase hH S hfit ρh c))

/-- the host chain `(ρh, c)` at global time `τ` (start frame before the window, end frame after it). -/
def hbT (ρh : Fin nR) (c : Fin 9) (τ : ℕ) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) : CMat (BC.LC (Fin 8) H l) :=
  if τ < S.lo ρh c then x0K I base l c d j
  else if τ ≤ S.hi ρh c + 1 then zbT I Ic base l hbase hH S hfit ρh c (τ - S.lo ρh c) d j
  else zbT I Ic base l hbase hH S hfit ρh c (S.KT ρh c) d j

def hpT (ρh : Fin nR) (c : Fin 9) (τ : ℕ) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) : CMat (BC.LC (Fin 8) H l) :=
  if S.lo ρh c ≤ τ ∧ τ ≤ S.hi ρh c then zpT I Ic base l hbase hH S hfit ρh c (τ - S.lo ρh c) d j
  else hbT I Ic base l hbase hH S hfit ρh c τ d j

lemma hHP_T (ρh : Fin nR) (c : Fin 9) (τ : ℕ) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    GReach (hbT I Ic base l hbase hH S hfit ρh c τ d j) (hpT I Ic base l hbase hH S hfit ρh c τ d j) (fun _ => 0) := by
  unfold hpT
  split_ifs with h
  · have hb : hbT I Ic base l hbase hH S hfit ρh c τ d j = zbT I Ic base l hbase hH S hfit ρh c (τ - S.lo ρh c) d j := by
      unfold hbT
      rw [if_neg (by omega), if_pos (by omega)]
    rw [hb]
    exact (zT_spec I Ic base l hbase hH S hfit ρh c).2.1 _ (by unfold HostSchedT.KT; omega) d j
  · exact GReach.refl _

lemma hHZ_T (ρ : Fin nR) (lc : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (q : Sl) (ρh : Fin nR) (c : Fin 9) (j : Bool × T)
    (h : S.host ρ lc q = (ρh, c, j)) :
    entW (win401N l hH lc.val d).X ((Ic ρ lc).ent q) * hpT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc) d j
      = hbT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc + 1) d j := by
  have hw := (S.win_iff ρh c (S.tm ρ lc)).mp (by have := S.hostWin ρ lc q; rw [h] at this; exact this)
  have hp : hpT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc) d j
      = zpT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc - S.lo ρh c) d j := by
    unfold hpT; rw [if_pos hw]
  have hb : hbT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc + 1) d j
      = zbT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc - S.lo ρh c + 1) d j := by
    unfold hbT
    rw [if_neg (by omega), if_pos (by omega), show S.tm ρ lc + 1 - S.lo ρh c = S.tm ρ lc - S.lo ρh c + 1 by omega]
  rw [hp, hb]
  have hu := (zT_spec I Ic base l hbase hH S hfit ρh c).2.2.1 (S.tm ρ lc - S.lo ρh c) (by unfold HostSchedT.KT; omega)
    d q j (S.useT_of h)
  have ew : wnT Ic l hH S ρh c (S.tm ρ lc - S.lo ρh c) d q = entW (win401N l hH lc.val d).X ((Ic ρ lc).ent q) := by
    unfold wnT
    rw [show S.lo ρh c + (S.tm ρ lc - S.lo ρh c) = S.tm ρ lc by omega, S.callAt_tm]
  rw [ew] at hu
  exact hu

lemma hHZn_T (ρ : Fin nR) (lc : Fin 9) (ρh : Fin nR) (c : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T)
    (h : ∀ q, some (S.host ρ lc q) ≠ some (ρh, c, j)) :
    hbT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc + 1) d j = hpT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc) d j := by
  have hlh := S.lo_le_hi ρh c
  by_cases hw : S.lo ρh c ≤ S.tm ρ lc ∧ S.tm ρ lc ≤ S.hi ρh c
  · have hp : hpT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc) d j
        = zpT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc - S.lo ρh c) d j := by
      unfold hpT; rw [if_pos hw]
    have hb : hbT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc + 1) d j
        = zbT I Ic base l hbase hH S hfit ρh c (S.tm ρ lc - S.lo ρh c + 1) d j := by
      unfold hbT
      rw [if_neg (by omega), if_pos (by omega), show S.tm ρ lc + 1 - S.lo ρh c = S.tm ρ lc - S.lo ρh c + 1 by omega]
    rw [hp, hb]
    refine (zT_spec I Ic base l hbase hH S hfit ρh c).2.2.2.1 (S.tm ρ lc - S.lo ρh c) (by unfold HostSchedT.KT; omega)
      d j (fun q hq => ?_)
    have e := S.useT_some hq
    rw [show S.lo ρh c + (S.tm ρ lc - S.lo ρh c) = S.tm ρ lc by omega, S.callAt_tm] at e
    exact h q (by rw [e])
  · unfold hpT
    rw [if_neg hw]
    unfold hbT
    by_cases h1 : S.tm ρ lc < S.lo ρh c
    · rw [if_pos h1]
      by_cases h2 : S.tm ρ lc + 1 < S.lo ρh c
      · rw [if_pos h2]
      · rw [if_neg h2, if_pos (by omega), show S.tm ρ lc + 1 - S.lo ρh c = 0 by omega]
        exact (zT_spec I Ic base l hbase hH S hfit ρh c).1 d j
    · rw [if_neg h1, if_neg (by omega), if_neg (show ¬ (S.tm ρ lc + 1 ≤ S.hi ρh c + 1) by omega)]
      by_cases h3 : S.tm ρ lc ≤ S.hi ρh c + 1
      · rw [if_pos h3, show S.tm ρ lc - S.lo ρh c = S.KT ρh c by unfold HostSchedT.KT; omega]
      · rw [if_neg h3]

lemma hH0_T (ρh : Fin nR) (c : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    hbT I Ic base l hbase hH S hfit ρh c (S.lo ρh c) d j = x0K I base l c d j := by
  have hlh := S.lo_le_hi ρh c
  unfold hbT
  rw [if_neg (lt_irrefl _), if_pos (by omega), Nat.sub_self]
  exact (zT_spec I Ic base l hbase hH S hfit ρh c).1 d j

lemma hHE_T (ρh : Fin nR) (c : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) :
    GReach (hbT I Ic base l hbase hH S hfit ρh c (S.hi ρh c + 1) d j) (x1K I base l c d j)
      (fun φ => bcost φ (S.hrem ρh c j)) := by
  have hlh := S.lo_le_hi ρh c
  have hb : hbT I Ic base l hbase hH S hfit ρh c (S.hi ρh c + 1) d j
      = zbT I Ic base l hbase hH S hfit ρh c (S.KT ρh c) d j := by
    unfold hbT
    rw [if_neg (by omega), if_pos le_rfl]
    rfl
  rw [hb]
  exact (zT_spec I Ic base l hbase hH S hfit ρh c).2.2.2.2 d j

lemma lo_A2 (ρ : Fin nR) : S.lo ρ 0 = 0 := by unfold HostSchedT.lo; rw [if_pos (by decide)]
lemma hi_A2 (ρ : Fin nR) : S.hi ρ 0 = S.tm ρ 1 := rfl
lemma lo_B2 (ρ : Fin nR) : S.lo ρ 1 = S.tm ρ 1 + 1 := by
  unfold HostSchedT.lo; rw [if_neg (by decide)]; rfl
lemma hi_B2 (ρ : Fin nR) : S.hi ρ 1 = S.tm ρ 2 := rfl
lemma lo_A3 (ρ : Fin nR) : S.lo ρ 2 = 0 := by unfold HostSchedT.lo; rw [if_pos (by decide)]
lemma hi_A3 (ρ : Fin nR) : S.hi ρ 2 = S.tm ρ 3 := rfl
lemma lo_B3 (ρ : Fin nR) : S.lo ρ 3 = S.tm ρ 3 + 1 := by
  unfold HostSchedT.lo; rw [if_neg (by decide)]; rfl
lemma hi_B3 (ρ : Fin nR) : S.hi ρ 3 = S.tm ρ 4 := rfl
lemma lo_A4 (ρ : Fin nR) : S.lo ρ 4 = 0 := by unfold HostSchedT.lo; rw [if_pos (by decide)]
lemma hi_A4 (ρ : Fin nR) : S.hi ρ 4 = S.tm ρ 5 := rfl
lemma lo_B4 (ρ : Fin nR) : S.lo ρ 5 = S.tm ρ 5 + 1 := by
  unfold HostSchedT.lo; rw [if_neg (by decide)]; rfl
lemma hi_B4 (ρ : Fin nR) : S.hi ρ 5 = S.tm ρ 6 := rfl
lemma lo_F1 (ρ : Fin nR) : S.lo ρ 6 = S.tm ρ 2 + 1 := by
  unfold HostSchedT.lo; rw [if_neg (by decide)]; rfl
lemma hi_F1 (ρ : Fin nR) : S.hi ρ 6 = S.tm ρ 8 := rfl
lemma lo_F2 (ρ : Fin nR) : S.lo ρ 7 = S.tm ρ 4 + 1 := by
  unfold HostSchedT.lo; rw [if_neg (by decide)]; rfl
lemma hi_F2 (ρ : Fin nR) : S.hi ρ 7 = S.tm ρ 8 := rfl
lemma lo_F3 (ρ : Fin nR) : S.lo ρ 8 = S.tm ρ 6 + 1 := by
  unfold HostSchedT.lo; rw [if_neg (by decide)]; rfl
lemma hi_F3 (ρ : Fin nR) : S.hi ρ 8 = S.tm ρ 8 := rfl

/-- **The cross-replica hosted nine-stage word as a term of `XNet`** on the label space `LC (Fin 8) H l`. -/
def xnetGeom : XNet H T Sl C (BC.LC (Fin 8) H l) (Orth (BC.LC (Fin 8) H l)) 0 nR where
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
  Hb := hbT I Ic base l hbase hH S hfit
  Hp := hpT I Ic base l hbase hH S hfit
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
  x01 := fun g t => g401geom_x01 I base l hbase g t
  y01 := fun g t => g401geom_y01 I base l hbase g t
  x12 := fun g t => g401geom_xx I base l hbase bs401_1 0 1 (Finset.mem_singleton_self _) mem401_1 g t
  y12 := fun g t => g401geom_yy I base l hbase bs401_1 0 1 (Finset.mem_singleton_self _) mem401_1 g t
  x23 := fun g t => g401geom_xx I base l hbase bs401_2 1 2 (Finset.mem_insert_self _ _) mem401_2 g t
  y23 := fun g t => g401geom_yy I base l hbase bs401_2 1 2 (Finset.mem_insert_self _ _) mem401_2 g t
  x34 := fun g t => g401geom_xx I base l hbase bs401_3 2 3 (Finset.mem_insert_self _ _) mem401_3 g t
  y34 := fun g t => g401geom_yy I base l hbase bs401_3 2 3 (Finset.mem_insert_self _ _) mem401_3 g t
  x45 := fun g t => g401geom_xx I base l hbase bs401_4 3 4 (Finset.mem_insert_self _ _) mem401_4 g t
  y45 := fun g t => g401geom_yy I base l hbase bs401_4 3 4 (Finset.mem_insert_self _ _) mem401_4 g t
  x56 := fun g t => g401geom_xx I base l hbase bs401_5 4 5 (Finset.mem_insert_self _ _) mem401_5 g t
  y56 := fun g t => g401geom_yy I base l hbase bs401_5 4 5 (Finset.mem_insert_self _ _) mem401_5 g t
  x67 := fun g t => g401geom_xx I base l hbase bs401_6 5 6 (Finset.mem_insert_self _ _) mem401_6 g t
  y67 := fun g t => g401geom_yy I base l hbase bs401_6 5 6 (Finset.mem_insert_self _ _) mem401_6 g t
  x78 := fun g t => g401geom_xx I base l hbase bs401_7 6 7 (Finset.mem_insert_self _ _) mem401_7 g t
  y78 := fun g t => g401geom_yy I base l hbase bs401_7 6 7 (Finset.mem_insert_self _ _) mem401_7 g t
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
  hHP := fun ρh c τ g j => hHP_T I Ic base l hbase hH S hfit ρh c τ g j
  hHZ0 := fun ρ g q ρh c j h => hHZ_T I Ic base l hbase hH S hfit ρ 0 g q ρh c j (Option.some_injective _ h)
  hHZ1 := fun ρ g q ρh c j h => hHZ_T I Ic base l hbase hH S hfit ρ 1 g q ρh c j (Option.some_injective _ h)
  hHZ2 := fun ρ g q ρh c j h => hHZ_T I Ic base l hbase hH S hfit ρ 2 g q ρh c j (Option.some_injective _ h)
  hHZ3 := fun ρ g q ρh c j h => hHZ_T I Ic base l hbase hH S hfit ρ 3 g q ρh c j (Option.some_injective _ h)
  hHZ4 := fun ρ g q ρh c j h => hHZ_T I Ic base l hbase hH S hfit ρ 4 g q ρh c j (Option.some_injective _ h)
  hHZ5 := fun ρ g q ρh c j h => hHZ_T I Ic base l hbase hH S hfit ρ 5 g q ρh c j (Option.some_injective _ h)
  hHZ6 := fun ρ g q ρh c j h => hHZ_T I Ic base l hbase hH S hfit ρ 6 g q ρh c j (Option.some_injective _ h)
  hHZ7 := fun ρ g q ρh c j h => hHZ_T I Ic base l hbase hH S hfit ρ 7 g q ρh c j (Option.some_injective _ h)
  hHZ8 := fun ρ g q ρh c j h => hHZ_T I Ic base l hbase hH S hfit ρ 8 g q ρh c j (Option.some_injective _ h)
  hHZn := fun ρ lc ρh c g j h => hHZn_T I Ic base l hbase hH S hfit ρ lc ρh c g j h
  hH0_A2 := fun ρ g t => by
    have h1 := hH0_T I Ic base l hbase hH S hfit ρ 0 g (false, t)
    have h2 := hH0_T I Ic base l hbase hH S hfit ρ 0 g (true, t)
    rw [lo_A2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_B2 := fun ρ g t => by
    have h1 := hH0_T I Ic base l hbase hH S hfit ρ 1 g (false, t)
    have h2 := hH0_T I Ic base l hbase hH S hfit ρ 1 g (true, t)
    rw [lo_B2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_A3 := fun ρ g t => by
    have h1 := hH0_T I Ic base l hbase hH S hfit ρ 2 g (false, t)
    have h2 := hH0_T I Ic base l hbase hH S hfit ρ 2 g (true, t)
    rw [lo_A3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_B3 := fun ρ g t => by
    have h1 := hH0_T I Ic base l hbase hH S hfit ρ 3 g (false, t)
    have h2 := hH0_T I Ic base l hbase hH S hfit ρ 3 g (true, t)
    rw [lo_B3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_A4 := fun ρ g t => by
    have h1 := hH0_T I Ic base l hbase hH S hfit ρ 4 g (false, t)
    have h2 := hH0_T I Ic base l hbase hH S hfit ρ 4 g (true, t)
    rw [lo_A4 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_B4 := fun ρ g t => by
    have h1 := hH0_T I Ic base l hbase hH S hfit ρ 5 g (false, t)
    have h2 := hH0_T I Ic base l hbase hH S hfit ρ 5 g (true, t)
    rw [lo_B4 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_F1 := fun ρ g t => by
    have h1 := hH0_T I Ic base l hbase hH S hfit ρ 6 g (false, t)
    have h2 := hH0_T I Ic base l hbase hH S hfit ρ 6 g (true, t)
    rw [lo_F1 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_F2 := fun ρ g t => by
    have h1 := hH0_T I Ic base l hbase hH S hfit ρ 7 g (false, t)
    have h2 := hH0_T I Ic base l hbase hH S hfit ρ 7 g (true, t)
    rw [lo_F2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hH0_F3 := fun ρ g t => by
    have h1 := hH0_T I Ic base l hbase hH S hfit ρ 8 g (false, t)
    have h2 := hH0_T I Ic base l hbase hH S hfit ρ 8 g (true, t)
    rw [lo_F3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_A2 := fun ρ g t => by
    have h1 := hHE_T I Ic base l hbase hH S hfit ρ 0 g (false, t)
    have h2 := hHE_T I Ic base l hbase hH S hfit ρ 0 g (true, t)
    rw [hi_A2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_B2 := fun ρ g t => by
    have h1 := hHE_T I Ic base l hbase hH S hfit ρ 1 g (false, t)
    have h2 := hHE_T I Ic base l hbase hH S hfit ρ 1 g (true, t)
    rw [hi_B2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_A3 := fun ρ g t => by
    have h1 := hHE_T I Ic base l hbase hH S hfit ρ 2 g (false, t)
    have h2 := hHE_T I Ic base l hbase hH S hfit ρ 2 g (true, t)
    rw [hi_A3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_B3 := fun ρ g t => by
    have h1 := hHE_T I Ic base l hbase hH S hfit ρ 3 g (false, t)
    have h2 := hHE_T I Ic base l hbase hH S hfit ρ 3 g (true, t)
    rw [hi_B3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_A4 := fun ρ g t => by
    have h1 := hHE_T I Ic base l hbase hH S hfit ρ 4 g (false, t)
    have h2 := hHE_T I Ic base l hbase hH S hfit ρ 4 g (true, t)
    rw [hi_A4 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_B4 := fun ρ g t => by
    have h1 := hHE_T I Ic base l hbase hH S hfit ρ 5 g (false, t)
    have h2 := hHE_T I Ic base l hbase hH S hfit ρ 5 g (true, t)
    rw [hi_B4 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_F1 := fun ρ g t => by
    have h1 := hHE_T I Ic base l hbase hH S hfit ρ 6 g (false, t)
    have h2 := hHE_T I Ic base l hbase hH S hfit ρ 6 g (true, t)
    rw [hi_F1 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_F2 := fun ρ g t => by
    have h1 := hHE_T I Ic base l hbase hH S hfit ρ 7 g (false, t)
    have h2 := hHE_T I Ic base l hbase hH S hfit ρ 7 g (true, t)
    rw [hi_F2 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  hHE_F3 := fun ρ g t => by
    have h1 := hHE_T I Ic base l hbase hH S hfit ρ 8 g (false, t)
    have h2 := hHE_T I Ic base l hbase hH S hfit ρ 8 g (true, t)
    rw [hi_F3 S ρ] at h1 h2
    exact ⟨h1, h2⟩
  fX4 := fun g t => g401geom_fX4 I base l hbase hH g t
  fY4 := fun g t => g401geom_fY4 I base l hbase hH g t
  term := fun g t => g401geom_term I base l hbase g t

end Net

section End
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}

/-- the price of the remaining climbs of kind `c` of replica `ρ` (both sides, all classes). -/
def hcostT (S : HostSchedT nR Sl T) (ρ : Fin nR) (c : Fin 9) (φ : ℕ → ℝ) : ℝ :=
  ∑ t : T, (bcost φ (S.hrem ρ c (false, t)) + bcost φ (S.hrem ρ c (true, t)))

/-- **the unit price of the cross-replica hosted word**: every call (its own provider's price) and the remaining
climbs of every host chain. -/
def unitPriceT (Ic : Fin nR → Fin 9 → GInvE H T Sl C) (S : HostSchedT nR Sl T) (φ : ℕ → ℝ) : ℝ :=
  (∑ ρ : Fin nR, ∑ l : Fin 9, (Ic ρ l).cost φ) + ∑ ρ : Fin nR, ∑ c : Fin 9, hcostT S ρ c φ

lemma sum_fin9 (f : Fin 9 → ℝ) :
    ∑ l, f l = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + 0)))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl

lemma sum_tailU {α Γ : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] {nb : ℕ}
    (N : XNet H T Sl C α Γ nb nR) (ρ : Fin nR) (φ : ℕ → ℝ) :
    ∑ l : Fin 9, N.tailU ρ l φ = (∑ c : Fin 9, N.hcost ρ c φ) + (Fintype.card T : ℝ) * (N.cX4 φ + N.cY4 φ) := by
  rw [sum_fin9, sum_fin9 (fun c => N.hcost ρ c φ)]
  simp only [XNet.tailU_eq0, XNet.tailU_eq1, XNet.tailU_eq2, XNet.tailU_eq3, XNet.tailU_eq4, XNet.tailU_eq5,
    XNet.tailU_eq6, XNet.tailU_eq7, XNet.tailU_eq8]
  ring

/-- **Generalised certificate of the CROSS-REPLICA hosted nine-stage word** for a gauged invocation package (one
provider word per call) and a cross-replica host schedule. -/
theorem bridgeHostT_gcert (I : GInvE H T Sl C) (Ic : Fin nR → Fin 9 → GInvE H T Sl C)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (hH : Fintype.card H = 9) (l : H) (S : HostSchedT nR Sl T)
    (hfit : S.fits (resIc Ic)) :
    GCert (BC.LC (Fin 8) H l)
      (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
      (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceT Ic S φ) := by
  have hb : ∀ t, ∃ A : OBase H, I.tv t = A.v l :=
    fun t => base_ex (I.tv t) (I.hunit t) (I.hgap t) l
  choose base hbase using hb
  have hc := xnet_certificate (xnetGeom I Ic hIc base l hbase hH S hfit)
  have e : (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ)
        * (xnetGeom I Ic hIc base l hbase hH S hfit).unit φ)
      = (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceT Ic S φ) := by
    funext φ
    congr 1
    simp only [XNet.unit, XNet.callU, Finset.sum_add_distrib, sum_tailU, Finset.univ_eq_empty, Finset.sum_empty,
      add_zero, unitPriceT]
    simp only [XNet.hcost, hcostT, xnetGeom, bcost_zero, add_zero, mul_zero, Finset.sum_const_zero]
  rw [e] at hc
  exact hc

end End
end
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.HostSchedT.LHK_useT
#print axioms OAI.PowerSaving.XHostT.chainT_ex
#print axioms OAI.PowerSaving.XHostT.xnetGeom
#print axioms OAI.PowerSaving.XHostT.bridgeHostT_gcert

import Submission.Work.Gauge.Labels
import Submission.Work.KLow.ExitEnd
import Submission.Work.GFrame.Labels.StageBSem
import Submission.Work.GFrame.Clifford.Climb

/-!
# (key: k-lower) The label half of an EXIT-FRAME certificate: `ValidX.glabX : XEX.GLabX`

k-lower, 13 Oct 2026.  Shea's / DFT Bridge3's gauged label half (`Work/Gauge/Labels.lean`, `ValidE.glab`) with exit
slots.  The end check `endKX` = `endKE` where a slot whose register is in the exit list `el` need not end at full
dimension: its end frame must CONTAIN its start frame (one packed elimination `elimT`, Sussman's E1 test).
`ValidX.glabX` builds x-exit-lean's `GLabX` with
* `E` = the exit slots, exit label = the end label;
* the hub's tail lowered into phase B (`Gt = Ht = 1`, tail labels = the labels after phase B, `rT = []`), and
  Shea's end gates `Gr = g8 Mti`, `Hr = (h8 Mt)ᵀ`, legal by `exit_hGr_scal` / `exit_hHr_scal` (Work/KLow/ExitEnd)
  from the two exit conditions on the total matrix;
* `GLabX` asks the entrance and the exit label of an exit slot to share ONE base (`hexG`, `hexs`).  The canonical
  labels of the frame table do not; `adPair` picks an adapted base of the nested pair (Sussman's Clifford
  `exists_common_base`), and FREE rebase moves (`SMv.rebase`, cost 0) join the adapted labels to the canonical ones
  before phase A and after the final climbs.  Dimensions are unchanged (`same_card`).
No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace OAI
namespace PowerSaving
namespace XEX
open Binary Matrix Finset RAM SS CB BR CR GF RF GX
noncomputable section

section Adapt
variable {H : Type} [Fintype H] [DecidableEq H]

/-- an adapted base of a nested pair of labels: `(G₀, s₀, t₀)`, `s₀ ⊆ t₀` -/
def adPair (U V : SLbl H) : APerm H × Finset H × Finset H := by
  classical
  exact if h : ∀ x, U.Mem x → V.Mem x then
    ((exists_common_base U.G V.G U.s V.s h).choose,
     (exists_common_base U.G V.G U.s V.s h).choose_spec.choose,
     (exists_common_base U.G V.G U.s V.s h).choose_spec.choose_spec.choose)
  else (U.G, U.s, U.s)

lemma adPair_spec (U V : SLbl H) (h : ∀ x, U.Mem x → V.Mem x) :
    (adPair U V).2.1 ⊆ (adPair U V).2.2 ∧ (∀ x, InSub U.G U.s x ↔ InSub (adPair U V).1 (adPair U V).2.1 x) ∧
      (∀ x, InSub (adPair U V).1 (adPair U V).2.2 x ↔ InSub V.G V.s x) := by
  classical
  unfold adPair
  rw [dif_pos h]
  exact (exists_common_base U.G V.G U.s V.s h).choose_spec.choose_spec.choose_spec

/-- the adapted entrance label -/
def entA (U V : SLbl H) : SLbl H := ⟨(adPair U V).1, (adPair U V).2.1⟩
/-- the adapted exit label -/
def exlA (U V : SLbl H) : SLbl H := ⟨(adPair U V).1, (adPair U V).2.2⟩

lemma entA_mem (U V : SLbl H) (h : ∀ x, U.Mem x → V.Mem x) : ∀ x, (entA U V).Mem x ↔ U.Mem x :=
  fun x => ((adPair_spec U V h).2.1 x).symm
lemma exlA_mem (U V : SLbl H) (h : ∀ x, U.Mem x → V.Mem x) : ∀ x, V.Mem x ↔ (exlA U V).Mem x :=
  fun x => ((adPair_spec U V h).2.2 x).symm
lemma entA_dim (U V : SLbl H) (h : ∀ x, U.Mem x → V.Mem x) : (entA U V).dim = U.dim :=
  (same_card (adPair_spec U V h).2.1).symm
lemma exlA_dim (U V : SLbl H) (h : ∀ x, U.Mem x → V.Mem x) : (exlA U V).dim = V.dim :=
  same_card (adPair_spec U V h).2.2

/-- a free rebase move between two labels of the same subspace -/
lemma rebaseR {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α) (U V : SLbl H)
    (h : ∀ x, U.Mem x ↔ V.Mem x) : GReach (X.Φ U) (X.Φ V) (fun _ => 0) :=
  (GReach.ofReach (X.fmv (SMv.rebase (m := Fintype.card α) h)).reach).cast (fun φ => rcost_nil φ)

variable {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]

/-- start labels: exit slots at their adapted entrance labels -/
def lab0X (E : Finset Sl) (L0 LF : L3 T Sl → SLbl H) : L3 T Sl → SLbl H :=
  Sum.elim (fun xy => L0 (Sum.inl xy)) (fun q => if q ∈ E then entA (L0 (lS q)) (LF (lS q)) else L0 (lS q))

/-- end labels: exit slots at their adapted exit labels -/
def labFX (E : Finset Sl) (L0 LF : L3 T Sl → SLbl H) : L3 T Sl → SLbl H :=
  Sum.elim (fun xy => LF (Sum.inl xy)) (fun q => if q ∈ E then exlA (L0 (lS q)) (LF (lS q)) else LF (lS q))

lemma lab0X_E (E : Finset Sl) (L0 LF : L3 T Sl → SLbl H) {q : Sl} (h : q ∈ E) :
    lab0X E L0 LF (lS q) = entA (L0 (lS q)) (LF (lS q)) := if_pos h
lemma lab0X_nE (E : Finset Sl) (L0 LF : L3 T Sl → SLbl H) {q : Sl} (h : q ∉ E) :
    lab0X E L0 LF (lS q) = L0 (lS q) := if_neg h
lemma labFX_E (E : Finset Sl) (L0 LF : L3 T Sl → SLbl H) {q : Sl} (h : q ∈ E) :
    labFX E L0 LF (lS q) = exlA (L0 (lS q)) (LF (lS q)) := if_pos h
lemma labFX_nE (E : Finset Sl) (L0 LF : L3 T Sl → SLbl H) {q : Sl} (h : q ∉ E) :
    labFX E L0 LF (lS q) = LF (lS q) := if_neg h

theorem pre_route {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α) (E : Finset Sl)
    (L0 LF : L3 T Sl → SLbl H) (hsub : ∀ q ∈ E, ∀ x, (L0 (lS q)).Mem x → (LF (lS q)).Mem x) :
    GRoute (fun r => X.Φ (lab0X E L0 LF r)) (fun r => X.Φ (L0 r)) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro (xy|q)
  · exact GReach.refl _
  · show GReach (X.Φ (if q ∈ E then entA (L0 (lS q)) (LF (lS q)) else L0 (lS q))) (X.Φ (L0 (lS q))) _
    by_cases hq : q ∈ E
    · rw [if_pos hq]; exact rebaseR X _ _ (entA_mem _ _ (hsub q hq))
    · rw [if_neg hq]; exact GReach.refl _

theorem post_route {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α) (E : Finset Sl)
    (L0 LF : L3 T Sl → SLbl H) (hsub : ∀ q ∈ E, ∀ x, (L0 (lS q)).Mem x → (LF (lS q)).Mem x) :
    GRoute (fun r => X.Φ (LF r)) (fun r => X.Φ (labFX E L0 LF r)) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro (xy|q)
  · exact GReach.refl _
  · show GReach (X.Φ (LF (lS q))) (X.Φ (if q ∈ E then exlA (L0 (lS q)) (LF (lS q)) else LF (lS q))) _
    by_cases hq : q ∈ E
    · rw [if_pos hq]; exact rebaseR X _ _ (exlA_mem _ _ (hsub q hq))
    · rw [if_neg hq]; exact GReach.refl _

end Adapt
end
end XEX
end PowerSaving
end OAI

namespace GLab
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.CB Finset Matrix

/-- slots: start at frame id 0 or are gauged; an EXIT slot (register in `el`) ends in a frame that contains its
start frame (one packed elimination), every other slot ends at full dimension -/
noncomputable def slotsKX (p : Par) (hm Oh sh v2 : Nat) (gl el : List Nat) (S0 SF : Trie) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun q ih => S0.getK (Nat.add v2 q) fun a =>
      guard (Bool.rec (motive := fun _ => Bool) (memK (Nat.add v2 q) gl) true (Nat.beq a 0)) <|
      SF.getK (Nat.add v2 q) fun b => p.tab.getK b fun cb =>
      Bool.rec (motive := fun _ => Bool)
        (guard (Nat.beq (Nat.land cb 255) p.h) ih)
        (p.tab.getK a fun ca => guard (elimT p.h hm Oh (Nat.shiftRight cb sh) (Nat.shiftRight ca sh)) ih)
        (memK (Nat.add v2 q) el))

/-- **the end check with entrance gauges and exit slots** (`endKE` with `slotsKX`) -/
noncomputable def endKX (p : Par) (v : Nat) (ports rets gl el : List Nat) (S0 SA SF : Trie) : Bool :=
  guard (Nat.ble 1 p.h) <|
  guard (wfK S0 p.d) <|
  guard (Nat.ble p.n (Nat.pow 2 p.d)) <|
  guard (Nat.ble (Nat.mul 2 v) p.n) <|
  p.tab.getK 0 fun c0 => guard (Nat.beq (Nat.land c0 255) 0) <|
  forceN (Nat.sub (Nat.pow 2 p.h) 1) fun hm =>
  forceN (Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1) hm) fun Oh =>
  guard (Nat.beq (Nat.mul Oh hm) (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1)) <|
  guard (portsK p hm Oh (Nat.add 8 p.h) v S0 SA SF ports 0) <|
  guard (slotsKX p hm Oh (Nat.add 8 p.h) (Nat.mul 2 v) gl el S0 SF (Nat.sub p.n (Nat.mul 2 v))) (retsK p SA rets)

/-- containment of two coded frames from one packed elimination -/
theorem sub_of_elim (h : Nat) (hh : 0 < h) {ca cb : Nat} (ha : Good h ca) (hb : Good h cb)
    (H : elimT h (2 ^ h - 1) (rep h h) (cP h cb) (cP h ca) = true) :
    ∀ x, (lab h ca).Mem x → (lab h cb).Mem x := by
  have A := elimT_sound h hh h (cP h cb) (cP h ca) (fun y => (lab h cb).Mem y) (mem_zero _)
    (fun x y hx hy => mem_add _ hx hy) (fun q hq => lab_bas hb ⟨q, hq⟩) H
  exact lab_sub ha (fun pp => A pp.val)

theorem slotsKX_sound (p : Par) (hT : tabK p.h p.tab = true) (hh : 0 < p.h) (v2 : Nat) (gl el : List Nat)
    (S0 SF : Trie) : ∀ n, slotsKX p (2 ^ p.h - 1) (rep p.h p.h) (Nat.add 8 p.h) v2 gl el S0 SF n = true →
    ∀ q, q < n → (S0.get (v2 + q) = 0 ∨ v2 + q ∈ gl) ∧
      (memK (v2 + q) el = false → cdim (p.tab.get (SF.get (v2 + q))) = p.h) ∧
      (memK (v2 + q) el = true → ∀ x, (lab p.h (p.tab.get (S0.get (v2 + q)))).Mem x →
        (lab p.h (p.tab.get (SF.get (v2 + q)))).Mem x) := by
  intro n
  induction n with
  | zero => intro _ q hq; exact absurd hq (Nat.not_lt_zero q)
  | succ n ih =>
    intro H q hq
    have H := getK_true _ _ _ H
    obtain ⟨g1, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    have hg : S0.get (v2 + n) = 0 ∨ v2 + n ∈ gl := by
      cases e : Nat.beq (S0.get (Nat.add v2 n)) 0 with
      | true => exact Or.inl (beq_true e)
      | false => rw [e] at g1; exact Or.inr (memK_sound _ gl g1)
    cases hm : memK (Nat.add v2 n) el with
    | false =>
      rw [hm] at H
      obtain ⟨g2, H⟩ := guard_true H
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h1 | h1
      · exact ih H q h1
      · rw [h1]
        refine ⟨hg, fun _ => beq_true g2, fun h' => ?_⟩
        have h'' : memK (Nat.add v2 n) el = true := h'
        rw [hm] at h''
        exact absurd h'' Bool.false_ne_true
    | true =>
      rw [hm] at H
      have H := getK_true _ _ _ H
      obtain ⟨g2, H⟩ := guard_true H
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h1 | h1
      · exact ih H q h1
      · rw [h1]
        refine ⟨hg, fun h' => ?_, fun _ => ?_⟩
        · have h'' : memK (Nat.add v2 n) el = false := h'
          rw [hm] at h''
          exact Bool.noConfusion h''
        · exact sub_of_elim p.h hh (tabK_good p.h p.tab hT _) (tabK_good p.h p.tab hT _) g2

/-- everything the exit-aware end check proves -/
structure EndsX (p : Par) (v : Nat) (ports rets gl el : List Nat) (S0 SA SF : Trie) : Prop where
  hh : 0 < p.h
  w0 : S0.wf p.d
  hn : p.n ≤ 2 ^ p.d
  hv : 2 * v ≤ p.n
  z0 : cdim (p.tab.get 0) = 0
  len : ports.length = v
  port : ∀ t, t < v → PortOK p v S0 SA SF t (ports.getD t 0)
  slot : ∀ q, q < p.n - 2 * v →
    (S0.get (2 * v + q) = 0 ∨ 2 * v + q ∈ gl) ∧
    (memK (2 * v + q) el = false → cdim (p.tab.get (SF.get (2 * v + q))) = p.h) ∧
    (memK (2 * v + q) el = true → ∀ x, (lab p.h (p.tab.get (S0.get (2 * v + q)))).Mem x →
        (lab p.h (p.tab.get (SF.get (2 * v + q)))).Mem x)
  ret : ∀ r ∈ rets, 0 < cdim (p.tab.get (SA.get r))

theorem endKX_sound {p : Par} {v : Nat} {ports rets gl el : List Nat} {S0 SA SF : Trie}
    (hT : tabK p.h p.tab = true) (H : endKX p v ports rets gl el S0 SA SF = true) :
    EndsX p v ports rets gl el S0 SA SF := by
  unfold endKX at H
  obtain ⟨g0, H⟩ := guard_true H
  obtain ⟨g1, H⟩ := guard_true H
  obtain ⟨g2, H⟩ := guard_true H
  obtain ⟨g3, H⟩ := guard_true H
  have H := getK_true _ _ _ H
  obtain ⟨g4, H⟩ := guard_true H
  rw [forceN_eq] at H
  rw [forceN_eq] at H
  obtain ⟨g5, H⟩ := guard_true H
  have hh : 0 < p.h := ble_true g0
  have eO : Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1) (Nat.sub (Nat.pow 2 p.h) 1)
      = rep p.h p.h := rep_of_mul p.h p.h _ hh (beq_true g5)
  rw [eO] at H
  obtain ⟨g6, H⟩ := guard_true H
  obtain ⟨g7, g8⟩ := guard_true H
  obtain ⟨a, b⟩ := portsK_sound p hT hh v S0 SA SF ports 0 g6
  have len : ports.length = v := by omega
  exact
    { hh := hh
      w0 := wfK_sound _ _ g1
      hn := ble_true g2
      hv := ble_true g3
      z0 := beq_true g4
      len := len
      port := fun t ht => by
        have := b t (by omega)
        rw [Nat.zero_add] at this
        exact this
      slot := slotsKX_sound p hT hh _ gl el S0 SF _ g7
      ret := retsK_sound p SA rets g8 }

/-- **the kernel-checked label facts of an exit-frame certificate** (`ValidE` with `endKX`) -/
structure ValidX (c : Raw) (a : Aux) (gl el : List Nat) : Prop where
  hn : a.p.n = 2 * c.v + c.R
  tab : tabK a.p.h a.p.tab = true
  runA : Run a.p a.S0 c.gatesA a.SA a.rA
  runB : Run a.p a.SA c.gatesB a.SB a.rB
  runF : Run a.p a.SB a.fins a.SF a.rF
  fin : noAdds a.fins = true
  ends : endKX a.p c.v c.ports (c.ret.map Prod.fst) gl el a.S0 a.SA a.SF = true

/-- the labels of the roles in a state -/
noncomputable def Lof (p : Par) (S : Trie) {ρ : Type} (emb : ρ → Nat) : ρ → SLbl (Fin p.h) :=
  fun r => p.labS S (emb r)

/-- the exit slots of an exit list -/
noncomputable def exitSet (c : Raw) (el : List Nat) : Finset (Fin c.R) :=
  univ.filter (fun q : Fin c.R => memK (2 * c.v + q.val) el = true)

/-- **THE LABEL HALF of an exit-frame certificate**: x-exit-lean's `GLabX` over its gauged scalar half, with the
two exit conditions `hR`, `hC` on the total matrix (kernel checks: Work/KLow/ZCheck). -/
noncomputable def ValidX.glabX {c : Raw} {a : Aux} {gl el : List Nat} (V : ValidX c a gl el) {C : Type} [Fintype C]
    [DecidableEq C] (S : OAI.PowerSaving.GX.GScal (Fin c.v) (Fin c.R) C)
    {emb : CR.L3 (Fin c.v) (Fin c.R) → Nat} {un : Nat → CR.L3 (Fin c.v) (Fin c.R)}
    (Ro : Roles c.v c.R emb un) (cf : Co → Coef)
    (hMA : S.MA = matP un (mic cf (c.gatesA.flatMap Gate.adds)))
    (hMAi : S.MAi = matPinv un (mic cf (c.gatesA.flatMap Gate.adds)))
    (hMB : S.MB = matP un (mic cf (c.gatesB.flatMap Gate.adds)))
    (hMBi : S.MBi = matPinv un (mic cf (c.gatesB.flatMap Gate.adds)))
    (reg : C → Nat) (hCc : ∀ k (q : Fin c.R), S.Cc k q ≠ 0 → reg k = 2 * c.v + q.val)
    (hreg : ∀ k, reg k ∈ c.ret.map Prod.fst)
    (hg : ∀ q : Fin c.R, 2 * c.v + q.val ∈ gl → q ∈ S.gauged)
    (hR : OAI.PowerSaving.XEX.ExitRows (exitSet c el) S.toScal.Mt)
    (hC : OAI.PowerSaving.XEX.ExitCols (exitSet c el) S.toScal.Mt) :
    OAI.PowerSaving.XEX.GLabX (Fin a.p.h) S :=
  have E := endKX_sound V.tab V.ends
  have C0 : Ctx a.p emb un := ⟨V.tab, E.hn, Ro.hun,
    fun r hr => Ro.hin r (by have := V.hn; omega),
    fun q => by have := V.hn; have := Ro.hlt q; omega⟩
  have wA := V.runA.wf E.w0
  have wB := V.runB.wf wA
  have G : ∀ k, (GLab.lab a.p.h (a.p.tab.get k)).dim = cdim (a.p.tab.get k) :=
    fun k => lab_dim (tabK_good _ _ V.tab k)
  have hqlt : ∀ q : Fin c.R, q.val < a.p.n - 2 * c.v := fun q => by have := V.hn; have := q.isLt; omega
  have hsub : ∀ q ∈ exitSet c el, ∀ x, (Lof a.p a.S0 emb (CR.lS q)).Mem x →
      (Lof a.p a.SF emb (CR.lS q)).Mem x := fun q hq x hx => by
    have hm : memK (2 * c.v + q.val) el = true := (Finset.mem_filter.mp hq).2
    show (lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lS q))))).Mem x
    rw [Ro.eS q]
    have hx' : (lab a.p.h (a.p.tab.get (a.S0.get (2 * c.v + q.val)))).Mem x := by
      have e := Ro.eS q
      have hx2 : (lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lS q))))).Mem x := hx
      rw [e] at hx2; exact hx2
    exact (E.slot q.val (hqlt q)).2.2 hm x hx'
  { tv := fun t => tvec a.p.h (c.ports.getD t.val 0)
    hunit := fun t => (E.port t.val t.isLt).unit
    hgap := fun t => (E.port t.val t.isLt).gap
    ent := fun q => OAI.PowerSaving.XEX.lab0X (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb) (CR.lS q)
    E := exitSet c el
    exl := fun q => OAI.PowerSaving.XEX.exlA (Lof a.p a.S0 emb (CR.lS q)) (Lof a.p a.SF emb (CR.lS q))
    hexG := fun q hq => by
      show _ = (OAI.PowerSaving.XEX.lab0X (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb) (CR.lS q)).G
      rw [OAI.PowerSaving.XEX.lab0X_E _ _ _ hq]; rfl
    hexs := fun q hq => by
      show (OAI.PowerSaving.XEX.lab0X (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb) (CR.lS q)).s ⊆ _
      rw [OAI.PowerSaving.XEX.lab0X_E _ _ _ hq]
      exact (OAI.PowerSaving.XEX.adPair_spec _ _ (hsub q hq)).1
    lab0 := OAI.PowerSaving.XEX.lab0X (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb)
    labA := fun q => a.p.labS a.SA (emb q)
    labB := fun q => a.p.labS a.SB (emb q)
    labT := fun q => a.p.labS a.SB (emb q)
    labF := OAI.PowerSaving.XEX.labFX (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb)
    cen := fun k => a.p.labS a.SA (reg k)
    z0 := GLab.lab a.p.h (a.p.tab.get 0)
    hz0 := by rw [G]; exact E.z0
    h0x := fun t => by
      show (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lX t))))).dim = 1 ∧
        (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lX t))))).Mem _
      rw [Ro.eX t, G]
      exact ⟨(E.port t.val t.isLt).x0d, (E.port t.val t.isLt).x0m⟩
    h0y := fun t => by
      show (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lY t))))).dim = 0
      rw [Ro.eY t, (E.port t.val t.isLt).y0, G]; exact E.z0
    h0s' := fun q => rfl
    hent := fun q hq => by
      have h0 : (Lof a.p a.S0 emb (CR.lS q)).dim = 0 := by
        show (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lS q))))).dim = 0
        rw [Ro.eS q]
        rcases (E.slot q.val (hqlt q)).1 with h0 | hm
        · rw [h0, G]; exact E.z0
        · exact absurd (hg q hm) hq
      show (OAI.PowerSaving.XEX.lab0X (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb) (CR.lS q)).dim = 0
      by_cases he : q ∈ exitSet c el
      · rw [OAI.PowerSaving.XEX.lab0X_E _ _ _ he, OAI.PowerSaving.XEX.entA_dim _ _ (hsub q he)]; exact h0
      · rw [OAI.PowerSaving.XEX.lab0X_nE _ _ _ he]; exact h0
    hAy := fun t => by
      show GLab.lab a.p.h (a.p.tab.get (a.SA.get (emb (CR.lY t)))) = GLab.lab a.p.h (a.p.tab.get 0)
      rw [Ro.eY t, (E.port t.val t.isLt).yA]
    hAc := fun k q h => by
      show GLab.lab a.p.h (a.p.tab.get (a.SA.get (reg k)))
        = GLab.lab a.p.h (a.p.tab.get (a.SA.get (emb (CR.lS q))))
      rw [Ro.eS q, hCc k q h]
    hcen := fun k => by
      show 0 < (GLab.lab a.p.h (a.p.tab.get (a.SA.get (reg k)))).dim
      rw [G]; exact E.ret _ (hreg k)
    hFx := fun t => by
      show (GLab.lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lX t))))).dim = Fintype.card (Fin a.p.h)
      rw [Ro.eX t, G, Fintype.card_fin]; exact (E.port t.val t.isLt).xF
    hFs := fun q hq => by
      show (OAI.PowerSaving.XEX.labFX (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb) (CR.lS q)).dim
        = Fintype.card (Fin a.p.h)
      rw [OAI.PowerSaving.XEX.labFX_nE _ _ _ hq]
      show (GLab.lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lS q))))).dim = Fintype.card (Fin a.p.h)
      have hm : memK (2 * c.v + q.val) el = false := by
        cases e : memK (2 * c.v + q.val) el with
        | false => rfl
        | true => exact absurd (show q ∈ exitSet c el from Finset.mem_filter.mpr ⟨Finset.mem_univ q, e⟩) hq
      rw [Ro.eS q, G, Fintype.card_fin]
      exact (E.slot q.val (hqlt q)).2.1 hm
    hFe := fun q hq => OAI.PowerSaving.XEX.labFX_E _ _ _ hq
    hFy := fun t => by
      show (GLab.lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lY t))))).dim + 1
          = Fintype.card (Fin a.p.h) ∧
        ∀ x, (GLab.lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lY t))))).Mem x → dot _ x = 0
      rw [Ro.eY t, G, Fintype.card_fin]
      exact ⟨(E.port t.val t.isLt).yFd, (E.port t.val t.isLt).yFm⟩
    Gt := 1
    Gr := OAI.PowerSaving.CR.g8 S.toScal.Mti
    Ht := 1
    Hr := (OAI.PowerSaving.CR.h8 S.toScal.Mt)ᵀ
    hGsplit := Matrix.mul_one _
    hHsplit := Matrix.mul_one _
    hGt := fun i j e h => absurd (Matrix.one_apply_ne e) h
    hHt := fun i j e h => absurd (Matrix.one_apply_ne e) h
    hGr := OAI.PowerSaving.XEX.exit_hGr_scal S hR hC
    hHr := OAI.PowerSaving.XEX.exit_hHr_scal S hR hC
    rA := a.rA
    rB := a.rB
    rT := []
    rF := a.rF
    pA := fun {α} _ _ X hα => by
      have hα' : a.p.h < Fintype.card α := by rwa [Fintype.card_fin] at hα
      have pre := OAI.PowerSaving.XEX.pre_route X (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb) hsub
      rw [hMA, hMAi]
      obtain ⟨r1, r2⟩ := (V.runA.route C0 X hα' cf E.w0).1
      exact ⟨((pre.trans r1).castg (Function.comp_id _)).cast (fun φ => by simp),
        ((pre.trans r2).castg (Function.comp_id _)).cast (fun φ => by simp)⟩
    pB := fun {α} _ _ X hα => by
      have hα' : a.p.h < Fintype.card α := by rwa [Fintype.card_fin] at hα
      rw [hMB, hMBi]
      exact (V.runB.route C0 X hα' cf wA).1
    pT := fun X _ => GRoute.refl.cast (fun φ => (rcost_nil φ).symm)
    pF := fun {α} _ _ X hα => by
      have hα' : a.p.h < Fintype.card α := by rwa [Fintype.card_fin] at hα
      have r1 := V.runF.route_id C0 X hα' wB (noAdds_sound _ V.fin)
      have post := OAI.PowerSaving.XEX.post_route X (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb) hsub
      exact ((r1.trans post).castg (Function.comp_id _)).cast (fun φ => by simp) }

/-- the ranks, the copy dimensions and the exit residuals of the exit label half (for the price and the bank) -/
theorem ValidX.glabX_ranks {c : Raw} {a : Aux} {gl el : List Nat} (V : ValidX c a gl el) {C : Type} [Fintype C]
    [DecidableEq C] (S : OAI.PowerSaving.GX.GScal (Fin c.v) (Fin c.R) C)
    {emb : CR.L3 (Fin c.v) (Fin c.R) → Nat} {un : Nat → CR.L3 (Fin c.v) (Fin c.R)}
    (Ro : Roles c.v c.R emb un) (cf : Co → Coef) (hMA) (hMAi) (hMB) (hMBi)
    (reg : C → Nat) (hCc) (hreg) (hg) (hR) (hC) :
    (V.glabX S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg hR hC).rA = a.rA ∧
    (V.glabX S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg hR hC).rB = a.rB ∧
    (V.glabX S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg hR hC).rT = [] ∧
    (V.glabX S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg hR hC).rF = a.rF ∧
    ∀ k, ((V.glabX S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg hR hC).cen k).dim
      = cdim (a.p.tab.get (a.SA.get (reg k))) :=
  ⟨rfl, rfl, rfl, rfl, fun k => lab_dim (tabK_good _ _ V.tab _)⟩

/-- the bank residual of a slot: `dim(end) - dim(start)` for an exit slot, `h - dim(start)` otherwise -/
theorem ValidX.glabX_res {c : Raw} {a : Aux} {gl el : List Nat} (V : ValidX c a gl el) {C : Type} [Fintype C]
    [DecidableEq C] (S : OAI.PowerSaving.GX.GScal (Fin c.v) (Fin c.R) C)
    {emb : CR.L3 (Fin c.v) (Fin c.R) → Nat} {un : Nat → CR.L3 (Fin c.v) (Fin c.R)}
    (Ro : Roles c.v c.R emb un) (cf : Co → Coef) (hMA) (hMAi) (hMB) (hMBi)
    (reg : C → Nat) (hCc) (hreg) (hg) (hR) (hC) (q : Fin c.R) :
    ((V.glabX S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg hR hC).inv.ex q).dim
      - ((V.glabX S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg hR hC).inv.ent q).dim
      = Bool.rec (motive := fun _ => Nat) (a.p.h - cdim (a.p.tab.get (a.S0.get (2 * c.v + q.val))))
          (cdim (a.p.tab.get (a.SF.get (2 * c.v + q.val))) - cdim (a.p.tab.get (a.S0.get (2 * c.v + q.val))))
          (memK (2 * c.v + q.val) el) := by
  have E := endKX_sound V.tab V.ends
  have G : ∀ k, (GLab.lab a.p.h (a.p.tab.get k)).dim = cdim (a.p.tab.get k) :=
    fun k => lab_dim (tabK_good _ _ V.tab k)
  have hqlt : q.val < a.p.n - 2 * c.v := by have := V.hn; have := q.isLt; omega
  rw [OAI.PowerSaving.XEX.GLabX.res]
  have hU : (Lof a.p a.S0 emb (CR.lS q)).dim = cdim (a.p.tab.get (a.S0.get (2 * c.v + q.val))) := by
    show (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lS q))))).dim = _
    rw [Ro.eS q, G]
  have hV : (Lof a.p a.SF emb (CR.lS q)).dim = cdim (a.p.tab.get (a.SF.get (2 * c.v + q.val))) := by
    show (GLab.lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lS q))))).dim = _
    rw [Ro.eS q, G]
  cases hm : memK (2 * c.v + q.val) el with
  | false =>
    have hq : q ∉ exitSet c el := fun h => by
      have := (Finset.mem_filter.mp h).2; rw [hm] at this; exact Bool.false_ne_true this
    show (if q ∈ exitSet c el then _ else _) = _
    rw [if_neg hq, Fintype.card_fin]
    show a.p.h - (OAI.PowerSaving.XEX.lab0X (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb) (CR.lS q)).dim = _
    rw [OAI.PowerSaving.XEX.lab0X_nE _ _ _ hq]
    show a.p.h - (Lof a.p a.S0 emb (CR.lS q)).dim = _
    rw [hU]
  | true =>
    have hq : q ∈ exitSet c el := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    have hs : ∀ x, (Lof a.p a.S0 emb (CR.lS q)).Mem x → (Lof a.p a.SF emb (CR.lS q)).Mem x := by
      intro x hx
      show (lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lS q))))).Mem x
      rw [Ro.eS q]
      have hx2 : (lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lS q))))).Mem x := hx
      rw [Ro.eS q] at hx2
      exact (E.slot q.val hqlt).2.2 hm x hx2
    show (if q ∈ exitSet c el then _ else _) = _
    rw [if_pos hq]
    show (OAI.PowerSaving.XEX.exlA (Lof a.p a.S0 emb (CR.lS q)) (Lof a.p a.SF emb (CR.lS q))).dim
      - (OAI.PowerSaving.XEX.lab0X (exitSet c el) (Lof a.p a.S0 emb) (Lof a.p a.SF emb) (CR.lS q)).dim = _
    rw [OAI.PowerSaving.XEX.lab0X_E _ _ _ hq, OAI.PowerSaving.XEX.exlA_dim _ _ hs, OAI.PowerSaving.XEX.entA_dim _ _ hs]
    show (Lof a.p a.SF emb (CR.lS q)).dim - (Lof a.p a.S0 emb (CR.lS q)).dim = _
    rw [hU, hV]

end GLab

#print axioms GLab.endKX_sound
#print axioms GLab.ValidX.glabX
#print axioms GLab.ValidX.glabX_res

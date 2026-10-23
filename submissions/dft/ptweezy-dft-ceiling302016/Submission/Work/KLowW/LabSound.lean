import Submission.Work.GCert.Labels.Sound
import Submission.Work.KLowW.LabK

/-!
# (key: p-warpchk) Soundness of the label check of an extended phase

* `colMap h cols`    the GF(2)-linear map with columns `cols` (`x ↦ ∑ x_i • col_i`); `colK_eq`: the kernel `colK`;
* `WTr h o a c0 c1`  what a passing warp event proves: `G`, `G⁻¹` are mutually inverse, and `G` carries the frame
                     `c0` onto `c1` (`a > 0`) or `c1` onto `c0` (`a < 0`) — the GF(2) FRAME TRANSPORT;
* `eOut`, `eRanks`, `eOk` and `RunW p wt S evs S' rs`: the semantic replay of events (gates and scales as `Run`,
                     warps: current frame `f0`, `WTr`, new frame `f1`; zero buffers: any new frame, no rank);
* `RunW.append`      composition of segments;
* **`RunW.of_seg`**  `tabK`, `wtK` and `segW p wt evs S S' rs` (kernel) give `RunW p wt S evs S' rs`;
* `RunW.ofRun`       a phase without warps is the old replay (`Run`).

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

namespace KLW
open SSC GXD GLab OAI.PowerSaving OAI.PowerSaving.Binary Finset

/-! ## the GF(2) maps of the warp table -/

/-- the linear map with columns `cols` (column `i` = image of the unit vector `i`) -/
noncomputable def colMap (h : Nat) (cols : List Nat) (x : Space (Fin h)) : Space (Fin h) :=
  ∑ i : Fin h, x i • dv h (cols.getD i.val 0) 0

theorem colMap_add (h : Nat) (cols : List Nat) (x y : Space (Fin h)) :
    colMap h cols (x + y) = colMap h cols x + colMap h cols y := by
  unfold colMap
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, add_smul])

theorem colMap_smul (h : Nat) (cols : List Nat) (a : F) (x : Space (Fin h)) :
    colMap h cols (a • x) = a • colMap h cols x := by
  unfold colMap
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul])

theorem colMap_zero (h : Nat) (cols : List Nat) : colMap h cols 0 = 0 := by
  unfold colMap; simp

theorem colMap_sum (h : Nat) (cols : List Nat) {ι : Type} (s : Finset ι) (g : ι → Space (Fin h)) :
    colMap h cols (∑ i ∈ s, g i) = ∑ i ∈ s, colMap h cols (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [colMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, colMap_add, ih]

/-- **what a passing warp event proves** (GF(2) frame transport) -/
structure WTr (h : Nat) (o : WOp) (a : Int) (c0 c1 : Nat) : Prop where
  inv1 : ∀ x, colMap h o.G (colMap h o.Gi x) = x
  inv2 : ∀ x, colMap h o.Gi (colMap h o.G x) = x
  pos : 0 < a → ∀ x, (lab h c1).Mem x ↔ ∃ y, (lab h c0).Mem y ∧ x = colMap h o.G y
  neg : a < 0 → ∀ x, (lab h c0).Mem x ↔ ∃ y, (lab h c1).Mem y ∧ x = colMap h o.G y

/-! ## the kernel image `colK` -/

theorem dv_land_hm (h X : Nat) : dv h (Nat.land X (2 ^ h - 1)) 0 = dv h X 0 := by
  funext q
  simp only [dv, Nat.mul_zero, Nat.zero_add]
  show bF ((X &&& (2 ^ h - 1)).testBit q.val) = bF (X.testBit q.val)
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true q.isLt, Bool.and_true]

theorem colK_nil (m : Nat) : colK [] m = 0 := rfl
theorem colK_cons (c : Nat) (cs : List Nat) (m : Nat) :
    colK (c :: cs) m = Nat.xor (Nat.mul (Nat.land m 1) c) (colK cs (Nat.shiftRight m 1)) := rfl

/-- the list form of the image: `∑_{i < length} bit_i(m) • col_i` -/
theorem colK_sum (h : Nat) : ∀ (cols : List Nat) (m : Nat),
    dv h (colK cols m) 0 = ∑ i ∈ range cols.length, bF (m.testBit i) • dv h (cols.getD i 0) 0 := by
  intro cols
  induction cols with
  | nil => intro m; rw [colK_nil, dv_zero]; simp
  | cons c cs ih =>
    intro m
    rw [colK_cons, show Nat.xor (Nat.mul (Nat.land m 1) c) (colK cs (Nat.shiftRight m 1))
      = (Nat.land m 1 * c) ^^^ colK cs (m >>> 1) from rfl, dv_xor, ih, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.testBit_shiftRight]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Nat.add_comm 1 i]
    · rcases Nat.mod_two_eq_zero_or_one m with e | e
      · have h1 : Nat.land m 1 = 0 := by
          rw [show Nat.land m 1 = m &&& 1 from rfl, Nat.and_one_is_mod]; exact e
        have h2 : m.testBit 0 = false := by
          rw [Nat.testBit_zero]; simp [e]
        rw [h1, Nat.zero_mul, dv_zero, h2]
        simp [bF]
      · have h1 : Nat.land m 1 = 1 := by
          rw [show Nat.land m 1 = m &&& 1 from rfl, Nat.and_one_is_mod]; exact e
        have h2 : m.testBit 0 = true := by
          rw [Nat.testBit_zero]; simp [e]
        rw [h1, Nat.one_mul, h2]
        simp [bF]

/-- **the kernel image is the linear map** (columns of length `h`) -/
theorem colK_eq (h : Nat) (cols : List Nat) (hl : cols.length = h) (m : Nat) :
    dv h (colK cols m) 0 = colMap h cols (dv h m 0) := by
  rw [colK_sum, hl, colMap, ← Fin.sum_univ_eq_sum_range (fun i => bF (m.testBit i) • dv h (cols.getD i 0) 0) h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [dv]

theorem dv_digit (h P p : Nat) (hp : p < h) : dv h (digK h (2 ^ h - 1) P p) 0 = dv h P p := by
  funext q
  simp only [dv]
  rw [digK_eq, dig_bit]
  simp [q.isLt]

/-- `imgK` succeeds: the image of every vector of the frame `ca` lies in the frame `cb` -/
theorem imgK_sound (h : Nat) (hh : 0 < h) (cols : List Nat) (hl : cols.length = h) {ca cb : Nat}
    (ga : Good h ca) (gb : Good h cb)
    (H : imgK h (2 ^ h - 1) cols (cP h ca) (cP h cb) h = true) :
    ∀ y, (lab h ca).Mem y → (lab h cb).Mem (colMap h cols y) := by
  have each : ∀ n, n ≤ h → imgK h (2 ^ h - 1) cols (cP h ca) (cP h cb) n = true →
      ∀ p, p < n → (lab h cb).Mem (colMap h cols (dv h (cP h ca) p)) := by
    intro n
    induction n with
    | zero => intro _ _ p hp; exact absurd hp (Nat.not_lt_zero p)
    | succ n ih =>
      intro hn H p hp
      obtain ⟨g1, g2⟩ := guard_true H
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with h1 | h1
      · exact ih (by omega) g2 p h1
      · subst h1
        have A := elimT_sound h hh 1 (cP h cb) _ (fun y => (lab h cb).Mem y) (mem_zero _)
          (fun x y hx hy => mem_add _ hx hy) (fun q hq => lab_bas gb ⟨q, hq⟩)
          (by rw [show rep h 1 = 1 by simp [rep_succ, rep_zero]]; exact g1) 0
        rw [dv_land_hm, colK_eq h cols hl, dv_digit h _ _ (by omega)] at A
        exact A
  intro y hy
  rw [(lab_mem ga y).mp hy, colMap_sum]
  exact Finset.sum_induction _ (fun z => (lab h cb).Mem z) (fun _ _ => mem_add _) (mem_zero _)
    (fun p _ => by
      rw [colMap_smul]
      exact mem_smul _ _ (each h le_rfl H p.val p.isLt))

/-- the inverse check on the unit vectors gives the inverse on all vectors -/
theorem invK_sound (h : Nat) (cols cols' : List Nat) (hl : cols.length = h)
    (H : invK (2 ^ h - 1) cols cols' h = true) : ∀ x, colMap h cols (colMap h cols' x) = x := by
  have each : ∀ n, n ≤ h → invK (2 ^ h - 1) cols cols' n = true → ∀ i, i < n →
      colMap h cols (dv h (cols'.getD i 0) 0) = dv h (2 ^ i) 0 := by
    intro n
    induction n with
    | zero => intro _ _ i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      intro hn H i hi
      obtain ⟨g1, g2⟩ := guard_true H
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
      · exact ih (by omega) g2 i h1
      · subst h1
        rw [← colK_eq h cols hl, ← dv_land_hm, beq_true g1]
        rfl
  intro x
  have ex : x = ∑ i : Fin h, x i • dv h (2 ^ i.val) 0 := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, dv, Nat.mul_zero, Nat.zero_add, Nat.testBit_two_pow]
    rw [Finset.sum_eq_single q (fun b _ hb => by
      have : ¬ (b.val = q.val) := fun e => hb (Fin.ext e)
      simp [this, bF]) (fun hq => absurd (Finset.mem_univ q) hq)]
    simp [bF]
  have e2 : colMap h cols' x = ∑ i : Fin h, x i • dv h (cols'.getD i.val 0) 0 := rfl
  conv_rhs => rw [ex]
  rw [e2, colMap_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [colMap_smul, each h le_rfl H i.val i.isLt]

/-! ## the semantic replay of events -/

/-- the frame state after an event -/
noncomputable def eOut (S : Trie) : WEv → Trie
  | .g g => gOut S g
  | .sc f r _ => gOut S (.out f r [] [])
  | .w r _ _ f1 => S.set r f1
  | .za r f => S.set r f
  | .zf _ => S
  | .dn r f => S.set r f

/-- the block ranks of an event -/
noncomputable def eRanks (p : GLab.Par) (S : Trie) : WEv → List Nat
  | .g g => gRanks p S g
  | .sc f r _ => gRanks p S (.out f r [] [])
  | .dn r f => [cdim (p.tab.get (S.get r)) - cdim (p.tab.get f)]
  | _ => []

/-- legality of an event -/
def eOk (p : GLab.Par) (wt : List WOp) (S : Trie) : WEv → Prop
  | .g g => gOk p S g
  | .sc f r _ => gOk p S (.out f r [] [])
  | .w r a f0 f1 => r < p.n ∧ S.get r = f0 ∧ a ≠ 0 ∧
      ∃ o, wt[a.natAbs - 1]? = some o ∧ WTr p.h o a (p.tab.get f0) (p.tab.get f1)
  | .za r _ => r < p.n
  | .zf r => r < p.n
  | .dn r f => r < p.n ∧ cdim (p.tab.get f) < cdim (p.tab.get (S.get r)) ∧
      ∀ x, (lab p.h (p.tab.get f)).Mem x → (lab p.h (p.tab.get (S.get r))).Mem x

noncomputable def esOut : Trie → List WEv → Trie
  | S, [] => S
  | S, e :: es => esOut (eOut S e) es

noncomputable def esRanks (p : GLab.Par) : Trie → List WEv → List Nat
  | _, [] => []
  | S, e :: es => eRanks p S e ++ esRanks p (eOut S e) es

def esOk (p : GLab.Par) (wt : List WOp) : Trie → List WEv → Prop
  | _, [] => True
  | S, e :: es => eOk p wt S e ∧ esOk p wt (eOut S e) es

/-- **a legal replay of events**: from `S` the events `evs` end at `S'` with block ranks `rs` -/
def RunW (p : GLab.Par) (wt : List WOp) (S : Trie) (evs : List WEv) (S' : Trie) (rs : List Nat) : Prop :=
  esOk p wt S evs ∧ esOut S evs = S' ∧ esRanks p S evs = rs

theorem esOut_append (S : Trie) (l l' : List WEv) : esOut S (l ++ l') = esOut (esOut S l) l' := by
  induction l generalizing S with
  | nil => rfl
  | cons e l ih => exact ih _

theorem esRanks_append (p : GLab.Par) (S : Trie) (l l' : List WEv) :
    esRanks p S (l ++ l') = esRanks p S l ++ esRanks p (esOut S l) l' := by
  induction l generalizing S with
  | nil => rfl
  | cons e l ih =>
    show eRanks p S e ++ esRanks p (eOut S e) (l ++ l') = _
    rw [ih, ← List.append_assoc]; rfl

theorem esOk_append (p : GLab.Par) (wt : List WOp) (S : Trie) (l l' : List WEv) :
    esOk p wt S (l ++ l') ↔ esOk p wt S l ∧ esOk p wt (esOut S l) l' := by
  induction l generalizing S with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons e l ih =>
    show (eOk p wt S e ∧ esOk p wt (eOut S e) (l ++ l')) ↔ _
    rw [ih]; exact and_assoc.symm

/-- **composition of segments** -/
theorem RunW.append {p : GLab.Par} {wt : List WOp} {S S1 S2 : Trie} {e1 e2 : List WEv} {r1 r2 : List Nat}
    (a : RunW p wt S e1 S1 r1) (b : RunW p wt S1 e2 S2 r2) : RunW p wt S (e1 ++ e2) S2 (r1 ++ r2) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  subst a2
  exact ⟨(esOk_append p wt S e1 e2).mpr ⟨a1, b1⟩, by rw [esOut_append, b2],
    by rw [esRanks_append, a3, b3]⟩

theorem RunW.nil (p : GLab.Par) (wt : List WOp) (S : Trie) : RunW p wt S [] S [] := ⟨trivial, rfl, rfl⟩

/-- **a phase without warps is the old replay** -/
theorem RunW.ofRun {p : GLab.Par} (wt : List WOp) {S S' : Trie} {gs : List Gate} {rs : List Nat}
    (R : Run p S gs S' rs) : RunW p wt S (gs.map WEv.g) S' rs := by
  obtain ⟨ok, e1, e2⟩ := R
  have key : ∀ (gs : List Gate) (S : Trie), runOk p S gs →
      esOk p wt S (gs.map WEv.g) ∧ esOut S (gs.map WEv.g) = runOut S gs ∧
        esRanks p S (gs.map WEv.g) = runRanks p S gs := by
    intro gs
    induction gs with
    | nil => intro S _; exact ⟨trivial, rfl, rfl⟩
    | cons g gs ih =>
      intro S ok
      obtain ⟨a, b, c⟩ := ih (gOut S g) ok.2
      exact ⟨⟨ok.1, a⟩, b, by
        show gRanks p S g ++ esRanks p (gOut S g) (gs.map WEv.g) = gRanks p S g ++ runRanks p (gOut S g) gs
        rw [c]⟩
  obtain ⟨a, b, c⟩ := key gs S ok
  exact ⟨a, b.trans e1, c.trans e2⟩

/-! ## soundness of the kernel replay -/

theorem opAbs_eq (a : Int) : opAbs a = a.natAbs := by
  cases a <;> rfl

theorem opNe0_sound (a : Int) (h : opNe0 a = true) : a ≠ 0 := by
  cases a with
  | ofNat n =>
    intro e
    have e' : (n : Int) = 0 := e
    have : n = 0 := by omega
    subst this
    exact absurd h Bool.false_ne_true
  | negSucc n => exact Int.negSucc_ne_zero n

theorem opPos_true (a : Int) (h : opPos a = true) : 0 < a := by
  cases a with
  | ofNat n =>
    have hn : n ≠ 0 := by
      intro e; subst e; exact absurd h Bool.false_ne_true
    have : (0 : Int) < (n : Int) := by exact_mod_cast Nat.pos_of_ne_zero hn
    exact this
  | negSucc n => exact absurd h Bool.false_ne_true

theorem opPos_false (a : Int) (ha : a ≠ 0) (h : opPos a = false) : a < 0 := by
  cases a with
  | ofNat n =>
    have hn : n = 0 := by
      cases n with
      | zero => rfl
      | succ m => exact Bool.noConfusion (h : true = false)
    subst hn; exact absurd rfl ha
  | negSucc n => exact Int.negSucc_lt_zero n

theorem opOf_get (wt : List WOp) (a : Int) (ha : opAbs a ≠ 0) (hl : opAbs a ≤ wt.length) :
    wt[a.natAbs - 1]? = some (opOf wt a) := by
  rw [← opAbs_eq]
  unfold opOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- the table check: every entry has `h` columns each way, and they are mutually inverse -/
theorem wtK_sound (h : Nat) (wt : List WOp) (H : wtK h wt = true) :
    ∀ o ∈ wt, (o.G.length = h ∧ o.Gi.length = h) ∧
      ((∀ x, colMap h o.G (colMap h o.Gi x) = x) ∧ (∀ x, colMap h o.Gi (colMap h o.G x) = x)) := by
  unfold wtK at H
  rw [forceN_eq] at H
  induction wt with
  | nil => intro o ho; exact absurd ho List.not_mem_nil
  | cons o0 wt ih =>
    intro o ho
    obtain ⟨l1, H⟩ := guard_true H
    obtain ⟨l2, H⟩ := guard_true H
    obtain ⟨g1, H⟩ := guard_true H
    obtain ⟨g2, g3⟩ := guard_true H
    rcases List.mem_cons.mp ho with e | e
    · subst e
      exact ⟨⟨beq_true l1, beq_true l2⟩, invK_sound h _ _ (beq_true l1) g1, invK_sound h _ _ (beq_true l2) g2⟩
    · exact ih g3 o e

/-- **the transport check is sound** -/
theorem transK_sound (h : Nat) (hh : 0 < h) (o : WOp) (hG : o.G.length = h) (hGi : o.Gi.length = h)
    (i1 : ∀ x, colMap h o.G (colMap h o.Gi x) = x) (i2 : ∀ x, colMap h o.Gi (colMap h o.G x) = x)
    (a : Int) (ha : a ≠ 0) {c0 c1 : Nat} (g0 : Good h c0) (g1 : Good h c1)
    (H : transK h (2 ^ h - 1) o (opPos a) c0 c1 = true) : WTr h o a c0 c1 := by
  have tr : ∀ {ca cb : Nat}, Good h ca → Good h cb → trK h (2 ^ h - 1) o ca cb = true →
      ∀ x, (lab h cb).Mem x ↔ ∃ y, (lab h ca).Mem y ∧ x = colMap h o.G y := by
    intro ca cb ga gb H x
    obtain ⟨A, B⟩ := guard_true H
    have fA := imgK_sound h hh o.G hG ga gb A
    have fB := imgK_sound h hh o.Gi hGi gb ga B
    exact ⟨fun hx => ⟨_, fB x hx, (i1 x).symm⟩, fun ⟨y, hy, e⟩ => e ▸ fA y hy⟩
  refine ⟨i1, i2, fun hp => ?_, fun hn => ?_⟩
  · have e : opPos a = true := by
      cases e' : opPos a with
      | true => rfl
      | false => exact absurd hp (not_lt.mpr (le_of_lt (opPos_false a ha e')))
    rw [e] at H
    exact tr g0 g1 H
  · have e : opPos a = false := by
      cases e' : opPos a with
      | false => rfl
      | true => exact absurd hn (not_lt.mpr (le_of_lt (opPos_true a e')))
    rw [e] at H
    exact tr g1 g0 H

theorem evK_sound (p : GLab.Par) (wt : List WOp) (hT : tabK p.h p.tab = true) (hh : 0 < p.h)
    (hW : ∀ o ∈ wt, o.G.length = p.h ∧ o.Gi.length = p.h)
    (hI : ∀ o ∈ wt, (∀ x, colMap p.h o.G (colMap p.h o.Gi x) = x) ∧ (∀ x, colMap p.h o.Gi (colMap p.h o.G x) = x))
    (e : WEv) (S : Trie) (rs : List Nat) (k : Trie → List Nat → Bool)
    (H : evK p wt (2 ^ p.h - 1) (Nat.mul p.h p.h) (Nat.add 8 p.h) (rep p.h p.K) e S rs k = true) :
    ∃ rs', k (eOut S e) rs' = true ∧ rs = eRanks p S e ++ rs' ∧ eOk p wt S e := by
  cases e with
  | g g => exact gateK_sound p hh g S rs k H
  | sc f r co => exact gateK_sound p hh (.out f r [] []) S rs k H
  | w r a f0 f1 =>
    obtain ⟨g1, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    obtain ⟨g2, H⟩ := guard_true H
    obtain ⟨g3, H⟩ := guard_true H
    obtain ⟨g4, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    obtain ⟨g5, H⟩ := guard_true H
    have ha := opNe0_sound a g3
    have hA : opAbs a ≠ 0 := by rw [opAbs_eq]; exact Int.natAbs_ne_zero.mpr ha
    have hl : opAbs a ≤ wt.length := ble_true g4
    have hget := opOf_get wt a hA hl
    have hmem : opOf wt a ∈ wt := List.mem_of_getElem? hget
    refine ⟨rs, H, by rfl, ble_true g1, beq_true g2, ha, opOf wt a, hget, ?_⟩
    exact transK_sound p.h hh (opOf wt a) (hW _ hmem).1 (hW _ hmem).2 (hI _ hmem).1 (hI _ hmem).2 a ha
      (tabK_good p.h p.tab hT f0) (tabK_good p.h p.tab hT f1) g5
  | za r f =>
    obtain ⟨g1, H⟩ := guard_true H
    exact ⟨rs, H, rfl, ble_true g1⟩
  | zf r =>
    obtain ⟨g1, H⟩ := guard_true H
    exact ⟨rs, H, rfl, ble_true g1⟩
  | dn r f =>
    obtain ⟨g1, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    obtain ⟨g2, H⟩ := guard_true H
    obtain ⟨g3, H⟩ := guard_true H
    cases rs with
    | nil => exact absurd H Bool.false_ne_true
    | cons r0 rs' =>
      obtain ⟨g4, H⟩ := guard_true H
      have e0 : r0 = cdim (p.tab.get (S.get r)) - cdim (p.tab.get f) := beq_true g4
      refine ⟨rs', H, by rw [e0]; rfl, ble_true g1, ble_true g2, ?_⟩
      have gc := tabK_good p.h p.tab hT (S.get r)
      have gf := tabK_good p.h p.tab hT f
      have A := elimT_sound p.h hh p.K _ _ (fun y => (lab p.h (p.tab.get (S.get r))).Mem y) (mem_zero _)
        (fun x y hx hy => mem_add _ hx hy) (fun q hq => lab_bas gc ⟨q, hq⟩) g3
      exact lab_sub gf (fun pp => A pp.val)

theorem evsK_sound (p : GLab.Par) (wt : List WOp) (hT : tabK p.h p.tab = true) (hh : 0 < p.h)
    (hW : ∀ o ∈ wt, o.G.length = p.h ∧ o.Gi.length = p.h)
    (hI : ∀ o ∈ wt, (∀ x, colMap p.h o.G (colMap p.h o.Gi x) = x) ∧ (∀ x, colMap p.h o.Gi (colMap p.h o.G x) = x)) :
    ∀ (evs : List WEv) (S : Trie) (rs : List Nat) (k : Trie → List Nat → Bool),
    evsK p wt (2 ^ p.h - 1) (Nat.mul p.h p.h) (Nat.add 8 p.h) (rep p.h p.K) evs S rs k = true →
    ∃ rs', k (esOut S evs) rs' = true ∧ rs = esRanks p S evs ++ rs' ∧ esOk p wt S evs := by
  intro evs
  induction evs with
  | nil => intro S rs k H; exact ⟨rs, H, rfl, trivial⟩
  | cons e evs ih =>
    intro S rs k H
    obtain ⟨rs1, hk, e1, ok1⟩ := evK_sound p wt hT hh hW hI e S rs _ H
    obtain ⟨rs2, hk2, e2, ok2⟩ := ih _ _ _ hk
    exact ⟨rs2, hk2, by rw [e1, e2, ← List.append_assoc]; rfl, ⟨ok1, ok2⟩⟩

/-- **soundness of one segment of the extended label replay** -/
theorem RunW.of_seg {p : GLab.Par} {wt : List WOp} {evs : List WEv} {S S' : Trie} {rs : List Nat}
    (hT : tabK p.h p.tab = true) (hWK : wtK p.h wt = true) (H : segW p wt evs S S' rs = true) :
    RunW p wt S evs S' rs := by
  unfold segW at H
  obtain ⟨g0, g1⟩ := guard_true H
  have hh : 0 < p.h := ble_true g0
  rw [forceN_eq] at g1
  rw [forceN_eq] at g1
  obtain ⟨g2, g3⟩ := guard_true g1
  have eO : Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1) (Nat.sub (Nat.pow 2 p.h) 1)
      = rep p.h p.K := rep_of_mul p.h p.K _ hh (beq_true g2)
  rw [eO] at g3
  have hI := wtK_sound p.h wt hWK
  obtain ⟨rs1, hk, e1, ok⟩ := evsK_sound p wt hT hh (fun o h => (hI o h).1) (fun o h => (hI o h).2) evs S rs _ g3
  obtain ⟨g4, g5⟩ := guard_true hk
  have eS := Trie.beqK_sound _ _ g4
  cases rs1 with
  | nil => exact ⟨ok, eS, by rw [e1, List.append_nil]⟩
  | cons a l => exact absurd g5 Bool.false_ne_true

end KLW

#print axioms KLW.RunW.of_seg
#print axioms KLW.RunW.ofRun
#print axioms KLW.transK_sound

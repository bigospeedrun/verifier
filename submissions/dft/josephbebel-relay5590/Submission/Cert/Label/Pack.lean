import Submission.Cert.Label.Trie

/-! Packed-state label checker (written for this submission).

PR 209's label checker `WarpCheck.checkSeg` keeps the frame label of every register in a binary `Trie` of depth
`p.d` and reads the frame table `p.tab` (a `Trie` of depth `w`) the same way, so every label or table read walks
the trie.  `checkSegP` runs the same event loop on packed natural numbers instead: label `r` is the `w`-bit
digit `r` of `N`, table entry `a` is the `tw`-bit digit `a` of `TN`; reads are a shift and a mask, writes an
xor.  `checkF` ties a packed number to a trie (every leaf equals its digit), at the start of a segment (`N0`,
supplied as data) and at its end (the computed state against `S'`).  `checkSegP_sound` gives PR 209's
`checkSeg` from `checkSegP`, so everything downstream (`WarpRun.of_checkSeg_nil`) is unchanged.

Written for this submission (Claude, Anthropic); it uses only the definitions of `Submission/Cert/Label/Trie.lean` (PR 209,
HalitZiyaKARTAL v7-42, itself heavily modified from Jacob Sussman's lever-2979 LabK/ScalK, Apache-2.0). -/

namespace WarpCheck.LabelPack
open TrieCheck CertData LabelCheck WarpCheck

/-- digit `r` (width `w`, mask `M = 2^w - 1`) of `N`. -/
noncomputable def getW (w M N r : Nat) : Nat := Nat.land (Nat.shiftRight N (Nat.mul w r)) M
/-- `N` with digit `r` replaced by `v`. -/
noncomputable def setW (w M N r v : Nat) : Nat :=
  Nat.xor N (Nat.shiftLeft (Nat.xor (getW w M N r) v) (Nat.mul w r))

/-- every leaf `j` (for the trie of depth `d` whose leaf `j` sits at slot `base + s * j`) is at most `M` and
equals digit `base + s * j` of `N`. -/
noncomputable def checkF (w M : Nat) (t : Trie) : Nat → Nat → Nat → Nat → Bool :=
  Trie.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun v d base _ N => Nat.rec (motive := fun _ => Bool)
       (guard (Nat.ble v M) (Nat.beq (getW w M N base) v)) (fun _ _ => false) d)
    (fun _ _ cl cr d base s N => Nat.rec (motive := fun _ => Bool) false
       (fun d' _ => guard (cl d' base (Nat.mul 2 s) N) (cr d' (Nat.add base s) (Nat.mul 2 s) N)) d)
    t

/-- Packed parameters: register count `n`, label width `w` (= depth of the frame table), masks, packed table. -/
structure PPar where
  n : Nat
  w : Nat
  M : Nat
  tw : Nat
  tM : Nat
  TN : Nat

noncomputable def visitKP (q : PPar) (hh sh f db r : Nat) (N : Nat) (A : Nat) (rs : List Nat)
    (k : Nat → Nat → List Nat → Bool) : Bool :=
  guard (Nat.ble (Nat.succ r) q.n) <|
  forceN (getW q.w q.M N r) fun a =>
  Bool.rec (motive := fun _ => Bool)
    (forceN (getW q.tw q.tM q.TN a) fun ca =>
      forceN (Nat.land ca 255) fun da =>
      guard (Nat.ble (Nat.succ da) db) <|
      List.rec (motive := fun _ => Bool) false
        (fun r0 rs' _ =>
          guard (Nat.beq r0 (Nat.sub db da)) <|
          forceN (Nat.add (Nat.shiftLeft A hh) (Nat.shiftRight ca sh)) fun A' =>
          k (setW q.w q.M N r f) A' rs')
        rs)
    (k N A rs)
    (Nat.beq a f)

noncomputable def loopNP (q : PPar) (hh sh f db : Nat) :
    List Nat → Nat → Nat → List Nat → (Nat → Nat → List Nat → Bool) → Bool :=
  fun l => List.rec (motive := fun _ => Nat → Nat → List Nat → (Nat → Nat → List Nat → Bool) → Bool)
    (fun N A rs k => k N A rs)
    (fun r _ ih N A rs k => visitKP q hh sh f db r N A rs fun N1 A1 rs1 => ih N1 A1 rs1 k)
    l

noncomputable def loopPP (q : PPar) (hh sh f db : Nat) :
    List (Nat × Co) → Nat → Nat → List Nat → (Nat → Nat → List Nat → Bool) → Bool :=
  fun l => List.rec (motive := fun _ => Nat → Nat → List Nat → (Nat → Nat → List Nat → Bool) → Bool)
    (fun N A rs k => k N A rs)
    (fun x _ ih N A rs k => visitKP q hh sh f db x.1 N A rs fun N1 A1 rs1 => ih N1 A1 rs1 k)
    l

noncomputable def checkGateP (q : PPar) (h hm hh sh O : Nat) (g : Gate) (N : Nat) (rs : List Nat)
    (k : Nat → List Nat → Bool) : Bool :=
  Gate.rec (motive := fun _ => Bool)
    (fun f s ts ex =>
      guard (Nat.ble f q.M) <|
      forceN (getW q.tw q.tM q.TN f) fun cb =>
      forceN (Nat.land cb 255) fun db =>
      visitKP q hh sh f db s N 0 rs fun N1 A1 rs1 =>
      loopPP q hh sh f db ts N1 A1 rs1 fun N2 A2 rs2 =>
      loopNP q hh sh f db ex N2 A2 rs2 fun N3 A3 rs3 =>
      guard (elimT h hm O (Nat.shiftRight cb sh) A3) (k N3 rs3))
    (fun f t ss =>
      guard (Nat.ble f q.M) <|
      forceN (getW q.tw q.tM q.TN f) fun cb =>
      forceN (Nat.land cb 255) fun db =>
      visitKP q hh sh f db t N 0 rs fun N1 A1 rs1 =>
      loopPP q hh sh f db ss N1 A1 rs1 fun N3 A3 rs3 =>
      guard (elimT h hm O (Nat.shiftRight cb sh) A3) (k N3 rs3))
    g

noncomputable def evWP (q : PPar) (h : Nat) (wt : List WOp) (hm : Nat) (r : Nat) (a : Int) (f0 f1 : Nat)
    (N : Nat) (rs : List Nat) (k : Nat → List Nat → Bool) : Bool :=
  guard (Nat.ble (Nat.succ r) q.n) <|
  forceN (getW q.w q.M N r) fun cur =>
  guard (Nat.beq cur f0) <|
  guard (opNe0 a) <|
  guard (Nat.ble (opAbs a) wt.length) <|
  guard (Nat.ble f0 q.M) <|
  forceN (getW q.tw q.tM q.TN f0) fun c0 =>
  guard (Nat.ble f1 q.M) <|
  forceN (getW q.tw q.tM q.TN f1) fun c1 =>
  guard (transK h hm (opOf wt a) (opPos a) c0 c1) (k (setW q.w q.M N r f1) rs)

noncomputable def evDnP (q : PPar) (h hm sh O : Nat) (r f : Nat) (N : Nat) (rs : List Nat)
    (k : Nat → List Nat → Bool) : Bool :=
  guard (Nat.ble (Nat.succ r) q.n) <|
  forceN (getW q.w q.M N r) fun cur =>
  forceN (getW q.tw q.tM q.TN cur) fun ca =>
  guard (Nat.ble f q.M) <|
  forceN (getW q.tw q.tM q.TN f) fun cb =>
  guard (Nat.ble (Nat.succ (Nat.land cb 255)) (Nat.land ca 255)) <|
  guard (elimT h hm O (Nat.shiftRight ca sh) (Nat.shiftRight cb sh)) <|
  List.rec (motive := fun _ => Bool) false
    (fun r0 rest _ => guard (Nat.beq r0 (Nat.sub (Nat.land ca 255) (Nat.land cb 255))) (k (setW q.w q.M N r f) rest))
    rs

noncomputable def evKP (q : PPar) (h : Nat) (wt : List WOp) (hm hh sh O : Nat) (e : WEv) (N : Nat) (rs : List Nat)
    (k : Nat → List Nat → Bool) : Bool :=
  WEv.rec (motive := fun _ => Bool)
    (fun g => checkGateP q h hm hh sh O g N rs k)
    (fun f r _ => checkGateP q h hm hh sh O (.out f r [] []) N rs k)
    (fun r a f0 f1 => evWP q h wt hm r a f0 f1 N rs k)
    (fun r f => guard (Nat.ble (Nat.succ r) q.n) (guard (Nat.ble f q.M) (k (setW q.w q.M N r f) rs)))
    (fun r => guard (Nat.ble (Nat.succ r) q.n) (k N rs))
    (fun r f => evDnP q h hm sh O r f N rs k)
    e

noncomputable def checkEventsP (q : PPar) (h : Nat) (wt : List WOp) (hm hh sh O : Nat) :
    List WEv → Nat → List Nat → (Nat → List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → List Nat → (Nat → List Nat → Bool) → Bool)
    (fun N rs k => k N rs)
    (fun e _ next N rs k => evKP q h wt hm hh sh O e N rs fun N1 rs1 => next N1 rs1 k)

/-- The packed segment check.  `q.TN` must pack `p.tab` (`checkF q.tw q.tM p.tab q.w 0 1 q.TN`, checked once,
see `checkSegP_sound`); `N0` packs `S`. -/
noncomputable def checkSegP (p : Par) (q : PPar) (wt : List WOp) (evs : List WEv) (S S' : Trie) (rs : List Nat)
    (N0 : Nat) : Bool :=
  guard (Nat.ble 1 p.h) <|
  guard (Nat.beq q.n p.n) <|
  guard (Nat.beq q.M (Nat.sub (Nat.pow 2 q.w) 1)) <|
  guard (Nat.ble p.n (Nat.pow 2 p.d)) <|
  guard (checkF q.w q.M S p.d 0 1 N0) <|
  forceN (Nat.sub (Nat.pow 2 p.h) 1) fun hm =>
  forceN (Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1) hm) fun O =>
  guard (Nat.beq (Nat.mul O hm) (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1)) <|
  checkEventsP q p.h wt hm (Nat.mul p.h p.h) (Nat.add 8 p.h) O evs N0 rs fun N1 rs1 =>
    guard (checkF q.w q.M S' p.d 0 1 N1) (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rs1)

/-! ## Digits -/

theorem getW_eq (w N r : Nat) : getW w (2 ^ w - 1) N r = (N >>> (w * r)) % 2 ^ w :=
  Nat.and_two_pow_sub_one_eq_mod _ _

theorem getW_lt (w N r : Nat) : getW w (2 ^ w - 1) N r < 2 ^ w := by
  rw [getW_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem testBit_getW (w N r i : Nat) :
    (getW w (2 ^ w - 1) N r).testBit i = (decide (i < w) && N.testBit (w * r + i)) := by
  rw [getW_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem testBit_big {x w i : Nat} (hx : x < 2 ^ w) (hi : w ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem getW_setW (w N r v j : Nat) (hv : v < 2 ^ w) :
    getW w (2 ^ w - 1) (setW w (2 ^ w - 1) N r v) j = if j = r then v else getW w (2 ^ w - 1) N j := by
  have hx : getW w (2 ^ w - 1) N r ^^^ v < 2 ^ w := Nat.xor_lt_two_pow (getW_lt w N r) hv
  have key : ∀ i, (getW w (2 ^ w - 1) (setW w (2 ^ w - 1) N r v) j).testBit i =
      (decide (i < w) && (N.testBit (w * j + i) ^^
        (decide (w * j + i ≥ w * r) && (getW w (2 ^ w - 1) N r ^^^ v).testBit (w * j + i - w * r)))) := by
    intro i
    rw [testBit_getW]
    show (decide (i < w) && (N ^^^ ((getW w (2 ^ w - 1) N r ^^^ v) <<< (w * r))).testBit (w * j + i)) = _
    rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [key i]
  by_cases hi : i < w
  · by_cases hj : j = r
    · subst hj
      rw [if_pos rfl]
      have e : w * j + i - w * j = i := by omega
      have g : (w * j + i ≥ w * j) = True := propext ⟨fun _ => trivial, fun _ => by omega⟩
      rw [e, Nat.testBit_xor, testBit_getW]
      simp only [hi, decide_true, Bool.true_and, g]
      cases N.testBit (w * j + i) <;> cases v.testBit i <;> rfl
    · rw [if_neg hj, testBit_getW]
      have z : (decide (w * j + i ≥ w * r) && (getW w (2 ^ w - 1) N r ^^^ v).testBit (w * j + i - w * r)) = false := by
        rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
        · have : ¬ (w * j + i ≥ w * r) := by
            have : w * (j + 1) ≤ w * r := Nat.mul_le_mul_left w hlt
            rw [Nat.mul_succ] at this; omega
          simp [this]
        · have : w ≤ w * j + i - w * r := by
            have : w * (r + 1) ≤ w * j := Nat.mul_le_mul_left w hgt
            rw [Nat.mul_succ] at this; omega
          rw [testBit_big hx this]; simp
      rw [z, Bool.xor_false]
  · have l : decide (i < w) = false := by simp [hi]
    rw [l, Bool.false_and]
    split
    · exact (testBit_big hv (Nat.le_of_not_lt hi)).symm
    · exact (testBit_big (getW_lt w N j) (Nat.le_of_not_lt hi)).symm

/-! ## Tries -/

theorem getK_eq : ∀ (t : Trie) (d key : Nat) (k : Nat → Bool), t.wf d → key < 2 ^ d → t.getK key k = k (t.get key)
  | .leaf v, 0, key, k, _, hk => by
    have : key = 0 := by have : key < 1 := hk; omega
    subst this; rfl
  | .leaf _, _ + 1, _, _, h, _ => (h : False).elim
  | .node _ _, 0, _, _, h, _ => (h : False).elim
  | .node l r, d + 1, key, k, h, hk => by
    have h' : Trie.wf d l ∧ Trie.wf d r := h
    rw [Trie.getK_node]
    have hk2 : key / 2 < 2 ^ d := by rw [Nat.pow_succ] at hk; omega
    show _ = k (if key % 2 = 0 then l.get (key / 2) else r.get (key / 2))
    split
    · exact getK_eq l d _ k h'.1 hk2
    · exact getK_eq r d _ k h'.2 hk2

theorem checkF_sound {w : Nat} : ∀ (t : Trie) (d base s N : Nat),
    checkF w (2 ^ w - 1) t d base s N = true →
    t.wf d ∧ ∀ j, j < 2 ^ d → t.get j < 2 ^ w ∧ getW w (2 ^ w - 1) N (base + s * j) = t.get j
  | .leaf v, 0, base, s, N, h => by
    have h := guard_true h
    have h1 : v ≤ 2 ^ w - 1 := Nat.le_of_ble_eq_true h.1
    have h2 := beq_true h.2
    refine ⟨trivial, fun j hj => ?_⟩
    have : j = 0 := by have : j < 1 := hj; omega
    subst this
    refine ⟨by have := Nat.two_pow_pos w; show v < 2 ^ w; omega, ?_⟩
    show getW w (2 ^ w - 1) N (base + s * 0) = v
    rw [Nat.mul_zero, Nat.add_zero]; exact h2
  | .leaf _, _ + 1, _, _, _, h => absurd h Bool.false_ne_true
  | .node _ _, 0, _, _, _, h => absurd h Bool.false_ne_true
  | .node l r, d + 1, base, s, N, h => by
    have h := guard_true h
    obtain ⟨wl, hl⟩ := checkF_sound l d base (2 * s) N h.1
    obtain ⟨wr, hr⟩ := checkF_sound r d (base + s) (2 * s) N h.2
    refine ⟨⟨wl, wr⟩, fun j hj => ?_⟩
    have hj2 : j / 2 < 2 ^ d := by rw [Nat.pow_succ] at hj; omega
    have eg : (Trie.node l r).get j = (if j % 2 = 0 then l.get (j / 2) else r.get (j / 2)) := rfl
    rw [eg]
    split
    · rename_i he
      obtain ⟨a, b⟩ := hl (j / 2) hj2
      refine ⟨a, ?_⟩
      have : base + s * j = base + 2 * s * (j / 2) := by
        have : j = 2 * (j / 2) := by omega
        conv => lhs; rw [this]
        rw [Nat.mul_left_comm, Nat.mul_assoc]
      rw [this, b]
    · rename_i he
      obtain ⟨a, b⟩ := hr (j / 2) hj2
      refine ⟨a, ?_⟩
      have : base + s * j = base + s + 2 * s * (j / 2) := by
        have : j = 2 * (j / 2) + 1 := by omega
        conv => lhs; rw [this]
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_assoc]; omega
      rw [this, b]

/-- `N` packs the labels of `S` (depth `d`, width `w`). -/
def Rel (w d N : Nat) (S : Trie) : Prop :=
  S.wf d ∧ ∀ j, j < 2 ^ d → S.get j < 2 ^ w ∧ getW w (2 ^ w - 1) N j = S.get j

theorem rel_of_checkF {w d N : Nat} {S : Trie} (h : checkF w (2 ^ w - 1) S d 0 1 N = true) : Rel w d N S := by
  obtain ⟨hw, hj⟩ := checkF_sound S d 0 1 N h
  exact ⟨hw, fun j hj' => by have := hj j hj'; rwa [Nat.zero_add, Nat.one_mul] at this⟩

theorem rel_set {w d N : Nat} {S : Trie} (hR : Rel w d N S) {r v : Nat} (hr : r < 2 ^ d) (hv : v < 2 ^ w) :
    Rel w d (setW w (2 ^ w - 1) N r v) (S.set r v) := by
  refine ⟨Trie.wf_set d S hR.1 r v, fun j hj => ?_⟩
  rw [Trie.get_set d S hR.1 r j v hr hj, getW_setW w N r v j hv]
  split
  · exact ⟨hv, rfl⟩
  · exact hR.2 j hj

theorem trie_ext : ∀ (d : Nat) (t t' : Trie), t.wf d → t'.wf d → (∀ j, j < 2 ^ d → t.get j = t'.get j) → t = t'
  | 0, .leaf v, .leaf v', _, _, h => by have := h 0 (by decide); exact congrArg Trie.leaf this
  | 0, .node _ _, _, h, _, _ => (h : False).elim
  | 0, .leaf _, .node _ _, _, h, _ => (h : False).elim
  | _ + 1, .leaf _, _, h, _, _ => (h : False).elim
  | _ + 1, .node _ _, .leaf _, _, h, _ => (h : False).elim
  | d + 1, .node l r, .node l' r', h, h', H => by
    have hw : Trie.wf d l ∧ Trie.wf d r := h
    have hw' : Trie.wf d l' ∧ Trie.wf d r' := h'
    have hl : l = l' := trie_ext d l l' hw.1 hw'.1 fun j hj => by
      have := H (2 * j) (by rw [Nat.pow_succ]; omega)
      simp only [Trie.get, show 2 * j % 2 = 0 by omega, if_true, show 2 * j / 2 = j by omega] at this
      exact this
    have hr : r = r' := trie_ext d r r' hw.2 hw'.2 fun j hj => by
      have := H (2 * j + 1) (by rw [Nat.pow_succ]; omega)
      simp only [Trie.get, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega] at this
      exact this
    rw [hl, hr]

theorem beqK_refl : ∀ (t : Trie), t.beqK t = true
  | .leaf v => by show Nat.beq v v = true; exact Nat.beq_refl v
  | .node l r => by
    show guard (l.beqK l) (r.beqK r) = true
    rw [beqK_refl l, beqK_refl r]; rfl


/-! ## Simulation -/

/-- Side conditions tying the packed parameters to `p`: the table digits are `p.tab`'s leaves. -/
structure Good (p : Par) (q : PPar) : Prop where
  hn : q.n = p.n
  hM : q.M = 2 ^ q.w - 1
  htM : q.tM = 2 ^ q.tw - 1
  hd : p.n ≤ 2 ^ p.d
  hT : Rel q.tw q.w q.TN p.tab

theorem guard_t (x : Bool) : guard true x = x := rfl

theorem ble_succ {r n : Nat} (h : Nat.ble (Nat.succ r) n = true) : r < n := Nat.le_of_ble_eq_true h

theorem lt_of_bleM {f M w : Nat} (hM : M = 2 ^ w - 1) (h : Nat.ble f M = true) : f < 2 ^ w := by
  have := Nat.le_of_ble_eq_true h; have := Nat.two_pow_pos w; omega

theorem visitK_sim {p : Par} {q : PPar} (G : Good p q) {hh sh f db r A : Nat} {rs : List Nat} {N : Nat} {S : Trie}
    (hR : Rel q.w p.d N S) (hf : f < 2 ^ q.w)
    {kP : Nat → Nat → List Nat → Bool} {k : Trie → Nat → List Nat → Bool}
    (hk : ∀ N' S' A' rs', Rel q.w p.d N' S' → kP N' A' rs' = true → k S' A' rs' = true)
    (h : visitKP q hh sh f db r N A rs kP = true) : visitK p.n p.tab hh sh f db r S A rs k = true := by
  unfold visitKP at h
  unfold visitK
  obtain ⟨g1, h⟩ := guard_true h
  have hr : r < p.n := G.hn ▸ ble_succ g1
  have hrd : r < 2 ^ p.d := Nat.lt_of_lt_of_le hr G.hd
  rw [show Nat.ble (Nat.succ r) p.n = true from Nat.ble_eq.mpr hr, guard_t, getK_eq S p.d r _ hR.1 hrd]
  rw [forceN_eq, G.hM, (hR.2 r hrd).2] at h
  have ha : S.get r < 2 ^ q.w := (hR.2 r hrd).1
  cases hb : Nat.beq (S.get r) f with
  | true => rw [hb] at h; exact hk N S A rs hR h
  | false =>
    rw [hb] at h
    show p.tab.getK (S.get r) _ = true
    rw [getK_eq p.tab q.w _ _ G.hT.1 ha]
    rw [← G.hM, forceN_eq, G.htM, (G.hT.2 _ ha).2] at h
    rw [forceN_eq] at h ⊢
    obtain ⟨g2, h⟩ := guard_true h
    rw [g2, guard_t]
    cases rs with
    | nil => exact absurd h Bool.false_ne_true
    | cons r0 rs' =>
      obtain ⟨g3, h⟩ := guard_true h
      show guard _ _ = true
      rw [g3, guard_t, forceN_eq]
      rw [forceN_eq] at h
      exact hk _ _ _ _ (G.hM ▸ rel_set hR hrd hf) h

theorem loopN_sim {p : Par} {q : PPar} (G : Good p q) {hh sh f db : Nat} (hf : f < 2 ^ q.w) :
    ∀ (l : List Nat) (N : Nat) (S : Trie) (A : Nat) (rs : List Nat)
      (kP : Nat → Nat → List Nat → Bool) (k : Trie → Nat → List Nat → Bool),
      Rel q.w p.d N S →
      (∀ N' S' A' rs', Rel q.w p.d N' S' → kP N' A' rs' = true → k S' A' rs' = true) →
      loopNP q hh sh f db l N A rs kP = true → loopN p.n p.tab hh sh f db l S A rs k = true
  | [], N, S, A, rs, kP, k, hR, hk, h => hk N S A rs hR h
  | r :: l, N, S, A, rs, kP, k, hR, hk, h => by
    change visitKP q hh sh f db r N A rs (fun N1 A1 rs1 => loopNP q hh sh f db l N1 A1 rs1 kP) = true at h
    change visitK p.n p.tab hh sh f db r S A rs (fun S1 A1 rs1 => loopN p.n p.tab hh sh f db l S1 A1 rs1 k) = true
    exact visitK_sim G hR hf (fun N' S' A' rs' hR' h' => loopN_sim G hf l N' S' A' rs' kP k hR' hk h') h

theorem loopP_sim {p : Par} {q : PPar} (G : Good p q) {hh sh f db : Nat} (hf : f < 2 ^ q.w) :
    ∀ (l : List (Nat × Co)) (N : Nat) (S : Trie) (A : Nat) (rs : List Nat)
      (kP : Nat → Nat → List Nat → Bool) (k : Trie → Nat → List Nat → Bool),
      Rel q.w p.d N S →
      (∀ N' S' A' rs', Rel q.w p.d N' S' → kP N' A' rs' = true → k S' A' rs' = true) →
      loopPP q hh sh f db l N A rs kP = true → loopP p.n p.tab hh sh f db l S A rs k = true
  | [], N, S, A, rs, kP, k, hR, hk, h => hk N S A rs hR h
  | x :: l, N, S, A, rs, kP, k, hR, hk, h => by
    change visitKP q hh sh f db x.1 N A rs (fun N1 A1 rs1 => loopPP q hh sh f db l N1 A1 rs1 kP) = true at h
    change visitK p.n p.tab hh sh f db x.1 S A rs (fun S1 A1 rs1 => loopP p.n p.tab hh sh f db l S1 A1 rs1 k) = true
    exact visitK_sim G hR hf (fun N' S' A' rs' hR' h' => loopP_sim G hf l N' S' A' rs' kP k hR' hk h') h

theorem tab_read {p : Par} {q : PPar} (G : Good p q) {f : Nat} (hf : f < 2 ^ q.w) (k : Nat → Bool) :
    p.tab.getK f k = k (getW q.tw q.tM q.TN f) := by
  rw [getK_eq p.tab q.w f k G.hT.1 hf, G.htM, (G.hT.2 f hf).2]

theorem checkGate_sim {p : Par} {q : PPar} (G : Good p q) {hm hh sh O : Nat} (g : Gate) {N : Nat} {S : Trie}
    {rs : List Nat} (hR : Rel q.w p.d N S)
    {kP : Nat → List Nat → Bool} {k : Trie → List Nat → Bool}
    (hk : ∀ N' S' rs', Rel q.w p.d N' S' → kP N' rs' = true → k S' rs' = true)
    (h : checkGateP q p.h hm hh sh O g N rs kP = true) : checkGate p hm hh sh O g S rs k = true := by
  cases g with
  | out f s ts ex =>
    change guard (Nat.ble f q.M) _ = true at h
    obtain ⟨g1, h⟩ := guard_true h
    have hf := lt_of_bleM G.hM g1
    change p.tab.getK f _ = true
    rw [tab_read G hf, forceN_eq]
    rw [forceN_eq, forceN_eq] at h
    exact visitK_sim G hR hf (fun N1 S1 A1 rs1 hR1 h1 =>
      loopP_sim G hf ts N1 S1 A1 rs1 _ _ hR1 (fun N2 S2 A2 rs2 hR2 h2 =>
        loopN_sim G hf ex N2 S2 A2 rs2 _ _ hR2 (fun N3 S3 A3 rs3 hR3 h3 => by
          obtain ⟨g3, h3⟩ := guard_true h3
          show guard _ _ = true
          rw [g3, guard_t]; exact hk _ _ _ hR3 h3) h2) h1) h
  | inn f t ss =>
    change guard (Nat.ble f q.M) _ = true at h
    obtain ⟨g1, h⟩ := guard_true h
    have hf := lt_of_bleM G.hM g1
    change p.tab.getK f _ = true
    rw [tab_read G hf, forceN_eq]
    rw [forceN_eq, forceN_eq] at h
    exact visitK_sim G hR hf (fun N1 S1 A1 rs1 hR1 h1 =>
      loopP_sim G hf ss N1 S1 A1 rs1 _ _ hR1 (fun N3 S3 A3 rs3 hR3 h3 => by
          obtain ⟨g3, h3⟩ := guard_true h3
          show guard _ _ = true
          rw [g3, guard_t]; exact hk _ _ _ hR3 h3) h1) h

theorem read_lbl {p : Par} {q : PPar} (G : Good p q) {N : Nat} {S : Trie} (hR : Rel q.w p.d N S) {r : Nat}
    (hr : r < p.n) (k : Nat → Bool) : S.getK r k = k (getW q.w q.M N r) := by
  have hrd : r < 2 ^ p.d := Nat.lt_of_lt_of_le hr G.hd
  rw [getK_eq S p.d r k hR.1 hrd, G.hM, (hR.2 r hrd).2]

theorem lbl_lt {p : Par} {q : PPar} (G : Good p q) (N r : Nat) : getW q.w q.M N r < 2 ^ q.w := by
  rw [G.hM]; exact getW_lt _ _ _

theorem evW_sim {p : Par} {q : PPar} (G : Good p q) {wt : List WOp} {hm r : Nat} {a : Int} {f0 f1 : Nat}
    {N : Nat} {S : Trie} {rs : List Nat} (hR : Rel q.w p.d N S)
    {kP : Nat → List Nat → Bool} {k : Trie → List Nat → Bool}
    (hk : ∀ N' S' rs', Rel q.w p.d N' S' → kP N' rs' = true → k S' rs' = true)
    (h : evWP q p.h wt hm r a f0 f1 N rs kP = true) : evW p wt hm r a f0 f1 S rs k = true := by
  unfold evWP at h
  unfold evW
  obtain ⟨g1, h⟩ := guard_true h
  have hr : r < p.n := G.hn ▸ ble_succ g1
  rw [show Nat.ble (Nat.succ r) p.n = true from Nat.ble_eq.mpr hr, guard_t, read_lbl G hR hr]
  rw [forceN_eq] at h
  obtain ⟨g2, h⟩ := guard_true h
  obtain ⟨g3, h⟩ := guard_true h
  obtain ⟨g4, h⟩ := guard_true h
  obtain ⟨g5, h⟩ := guard_true h
  rw [forceN_eq] at h
  obtain ⟨g6, h⟩ := guard_true h
  rw [forceN_eq] at h
  obtain ⟨g7, h⟩ := guard_true h
  rw [g2, guard_t, g3, guard_t, g4, guard_t, tab_read G (lt_of_bleM G.hM g5),
    tab_read G (lt_of_bleM G.hM g6), g7, guard_t]
  have hR' := rel_set hR (Nat.lt_of_lt_of_le hr G.hd) (lt_of_bleM G.hM g6)
  rw [← G.hM] at hR'
  exact hk _ _ _ hR' h

theorem evDn_sim {p : Par} {q : PPar} (G : Good p q) {hm sh O r f : Nat}
    {N : Nat} {S : Trie} {rs : List Nat} (hR : Rel q.w p.d N S)
    {kP : Nat → List Nat → Bool} {k : Trie → List Nat → Bool}
    (hk : ∀ N' S' rs', Rel q.w p.d N' S' → kP N' rs' = true → k S' rs' = true)
    (h : evDnP q p.h hm sh O r f N rs kP = true) : evDn p hm sh O r f S rs k = true := by
  unfold evDnP at h
  unfold evDn
  obtain ⟨g1, h⟩ := guard_true h
  have hr : r < p.n := G.hn ▸ ble_succ g1
  rw [show Nat.ble (Nat.succ r) p.n = true from Nat.ble_eq.mpr hr, guard_t, read_lbl G hR hr,
    tab_read G (lbl_lt G N r)]
  rw [forceN_eq, forceN_eq] at h
  obtain ⟨g2, h⟩ := guard_true h
  rw [forceN_eq] at h
  obtain ⟨g3, h⟩ := guard_true h
  obtain ⟨g4, h⟩ := guard_true h
  rw [tab_read G (lt_of_bleM G.hM g2), g3, guard_t, g4, guard_t]
  have hR' := rel_set hR (Nat.lt_of_lt_of_le hr G.hd) (lt_of_bleM G.hM g2)
  rw [← G.hM] at hR'
  cases rs with
  | nil => exact absurd h Bool.false_ne_true
  | cons r0 rest =>
    obtain ⟨g5, h⟩ := guard_true h
    show guard _ _ = true
    rw [g5, guard_t]; exact hk _ _ _ hR' h

theorem evK_sim {p : Par} {q : PPar} (G : Good p q) {wt : List WOp} {hm hh sh O : Nat} (e : WEv)
    {N : Nat} {S : Trie} {rs : List Nat} (hR : Rel q.w p.d N S)
    {kP : Nat → List Nat → Bool} {k : Trie → List Nat → Bool}
    (hk : ∀ N' S' rs', Rel q.w p.d N' S' → kP N' rs' = true → k S' rs' = true)
    (h : evKP q p.h wt hm hh sh O e N rs kP = true) : evK p wt hm hh sh O e S rs k = true := by
  cases e with
  | g g => exact checkGate_sim G g hR hk h
  | sc f r co => exact checkGate_sim G (.out f r [] []) hR hk h
  | w r a f0 f1 => exact evW_sim G hR hk h
  | za r f =>
    change guard (Nat.ble (Nat.succ r) q.n) (guard (Nat.ble f q.M) (kP (setW q.w q.M N r f) rs)) = true at h
    obtain ⟨g1, h⟩ := guard_true h
    obtain ⟨g2, h⟩ := guard_true h
    have hr : r < p.n := G.hn ▸ ble_succ g1
    change guard (Nat.ble (Nat.succ r) p.n) (k (S.set r f) rs) = true
    rw [show Nat.ble (Nat.succ r) p.n = true from Nat.ble_eq.mpr hr, guard_t]
    have hR' := rel_set hR (Nat.lt_of_lt_of_le hr G.hd) (lt_of_bleM G.hM g2)
    rw [← G.hM] at hR'
    exact hk _ _ _ hR' h
  | zf r =>
    change guard (Nat.ble (Nat.succ r) q.n) (kP N rs) = true at h
    obtain ⟨g1, h⟩ := guard_true h
    have hr : r < p.n := G.hn ▸ ble_succ g1
    change guard (Nat.ble (Nat.succ r) p.n) (k S rs) = true
    rw [show Nat.ble (Nat.succ r) p.n = true from Nat.ble_eq.mpr hr, guard_t]
    exact hk _ _ _ hR h
  | dn r f => exact evDn_sim G hR hk h

theorem checkEvents_sim {p : Par} {q : PPar} (G : Good p q) {wt : List WOp} {hm hh sh O : Nat} :
    ∀ (evs : List WEv) (N : Nat) (S : Trie) (rs : List Nat)
      (kP : Nat → List Nat → Bool) (k : Trie → List Nat → Bool),
      Rel q.w p.d N S → (∀ N' S' rs', Rel q.w p.d N' S' → kP N' rs' = true → k S' rs' = true) →
      checkEventsP q p.h wt hm hh sh O evs N rs kP = true → checkEvents p wt hm hh sh O evs S rs k = true
  | [], N, S, rs, kP, k, hR, hk, h => hk N S rs hR h
  | e :: evs, N, S, rs, kP, k, hR, hk, h => by
    change evKP q p.h wt hm hh sh O e N rs (fun N1 rs1 => checkEventsP q p.h wt hm hh sh O evs N1 rs1 kP) = true at h
    change evK p wt hm hh sh O e S rs (fun S1 rs1 => checkEvents p wt hm hh sh O evs S1 rs1 k) = true
    exact evK_sim G e hR (fun N' S' rs' hR' h' => checkEvents_sim G evs N' S' rs' kP k hR' hk h') h

/-! ## Segments given as lists of event lists

A label segment is the concatenation of several scalar segments.  `checkSegPL` runs over the list of event lists
directly, so the kernel never unfolds `List.append` per event. -/

/-- `l₁ ++ (l₂ ++ … lₙ)` (no trailing `[]`), the shape of the label segment definitions. -/
def joinR : List (List WEv) → List WEv
  | [] => []
  | [l] => l
  | l :: ls => l ++ joinR ls

noncomputable def checkEventsPL (q : PPar) (h : Nat) (wt : List WOp) (hm hh sh O : Nat) :
    List (List WEv) → Nat → List Nat → (Nat → List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → List Nat → (Nat → List Nat → Bool) → Bool)
    (fun N rs k => k N rs)
    (fun l _ ih N rs k => checkEventsP q h wt hm hh sh O l N rs fun N1 rs1 => ih N1 rs1 k)

theorem checkEventsP_append (q : PPar) (h : Nat) (wt : List WOp) (hm hh sh O : Nat) :
    ∀ (a b : List WEv) (N : Nat) (rs : List Nat) (k : Nat → List Nat → Bool),
      checkEventsP q h wt hm hh sh O (a ++ b) N rs k =
        checkEventsP q h wt hm hh sh O a N rs (fun N1 rs1 => checkEventsP q h wt hm hh sh O b N1 rs1 k)
  | [], _, _, _, _ => rfl
  | e :: a, b, N, rs, k => by
    show evKP q h wt hm hh sh O e N rs (fun N1 rs1 => checkEventsP q h wt hm hh sh O (a ++ b) N1 rs1 k) =
      evKP q h wt hm hh sh O e N rs (fun N1 rs1 => checkEventsP q h wt hm hh sh O a N1 rs1
        (fun N2 rs2 => checkEventsP q h wt hm hh sh O b N2 rs2 k))
    congr 1; funext N1 rs1; exact checkEventsP_append q h wt hm hh sh O a b N1 rs1 k

theorem checkEventsPL_eq (q : PPar) (h : Nat) (wt : List WOp) (hm hh sh O : Nat) :
    ∀ (ls : List (List WEv)) (N : Nat) (rs : List Nat) (k : Nat → List Nat → Bool),
      checkEventsPL q h wt hm hh sh O ls N rs k = checkEventsP q h wt hm hh sh O (joinR ls) N rs k
  | [], _, _, _ => rfl
  | [l], N, rs, k => rfl
  | l :: l' :: ls, N, rs, k => by
    show checkEventsP q h wt hm hh sh O l N rs (fun N1 rs1 => checkEventsPL q h wt hm hh sh O (l' :: ls) N1 rs1 k) =
      checkEventsP q h wt hm hh sh O (l ++ joinR (l' :: ls)) N rs k
    rw [checkEventsP_append]
    congr 1; funext N1 rs1; exact checkEventsPL_eq q h wt hm hh sh O (l' :: ls) N1 rs1 k

noncomputable def checkSegPL (p : Par) (q : PPar) (wt : List WOp) (ls : List (List WEv)) (S S' : Trie) (rs : List Nat)
    (N0 : Nat) : Bool :=
  guard (Nat.ble 1 p.h) <|
  guard (Nat.beq q.n p.n) <|
  guard (Nat.beq q.M (Nat.sub (Nat.pow 2 q.w) 1)) <|
  guard (Nat.ble p.n (Nat.pow 2 p.d)) <|
  guard (checkF q.w q.M S p.d 0 1 N0) <|
  forceN (Nat.sub (Nat.pow 2 p.h) 1) fun hm =>
  forceN (Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1) hm) fun O =>
  guard (Nat.beq (Nat.mul O hm) (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1)) <|
  checkEventsPL q p.h wt hm (Nat.mul p.h p.h) (Nat.add 8 p.h) O ls N0 rs fun N1 rs1 =>
    guard (checkF q.w q.M S' p.d 0 1 N1) (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rs1)

theorem checkSegPL_eq (p : Par) (q : PPar) (wt : List WOp) (ls : List (List WEv)) (S S' : Trie) (rs : List Nat)
    (N0 : Nat) : checkSegPL p q wt ls S S' rs N0 = checkSegP p q wt (joinR ls) S S' rs N0 := by
  unfold checkSegPL checkSegP
  simp only [checkEventsPL_eq]

/-- PR 209's label segment check from the packed one. -/
theorem checkSegP_sound {p : Par} {q : PPar} {wt : List WOp} {evs : List WEv} {S S' : Trie} {rs : List Nat}
    {N0 : Nat} (hT : checkF q.tw (2 ^ q.tw - 1) p.tab q.w 0 1 q.TN = true) (htM : q.tM = 2 ^ q.tw - 1)
    (h : checkSegP p q wt evs S S' rs N0 = true) : checkSeg p wt evs S S' rs = true := by
  unfold checkSegP at h
  obtain ⟨g1, h⟩ := guard_true h
  obtain ⟨g2, h⟩ := guard_true h
  obtain ⟨g3, h⟩ := guard_true h
  obtain ⟨g4, h⟩ := guard_true h
  obtain ⟨g5, h⟩ := guard_true h
  have hM : q.M = 2 ^ q.w - 1 := beq_true g3
  have G : Good p q := ⟨beq_true g2, hM, htM, Nat.le_of_ble_eq_true g4, rel_of_checkF hT⟩
  rw [hM] at g5
  have hR := rel_of_checkF g5
  rw [forceN_eq, forceN_eq] at h
  obtain ⟨g6, h⟩ := guard_true h
  unfold checkSeg
  rw [g1, guard_t, forceN_eq, forceN_eq, g6, guard_t]
  refine checkEvents_sim G evs N0 S rs _ _ hR (fun N1 S1 rs1 hR1 h1 => ?_) h
  obtain ⟨g7, h1⟩ := guard_true h1
  rw [hM] at g7
  have hR' := rel_of_checkF g7
  have e : S1 = S' := trie_ext p.d S1 S' hR1.1 hR'.1 fun j hj => by
    rw [← (hR1.2 j hj).2, ← (hR'.2 j hj).2]
  rw [e, beqK_refl, guard_t]; exact h1

/-- PR 209's label segment check from the packed check over the list of event lists `ls`, `evs = joinR ls`. -/
theorem checkSegPL_sound {p : Par} {q : PPar} {wt : List WOp} {ls : List (List WEv)} {evs : List WEv} {S S' : Trie}
    {rs : List Nat} {N0 : Nat} (hT : checkF q.tw (2 ^ q.tw - 1) p.tab q.w 0 1 q.TN = true) (htM : q.tM = 2 ^ q.tw - 1)
    (he : joinR ls = evs) (h : checkSegPL p q wt ls S S' rs N0 = true) : checkSeg p wt evs S S' rs = true := by
  rw [checkSegPL_eq, he] at h
  exact checkSegP_sound hT htM h

end WarpCheck.LabelPack

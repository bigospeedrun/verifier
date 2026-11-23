import Submission.Cert.Scalar.Checker

/-! Zero-source skip for the packed scalar checker (written for this submission).

On a key-split chain many adds `t += (±num/den)·s` have a source row `s` that is zero on every key of
the chain.  `ScalarCheck.Spec.AddStep` then holds with the state unchanged, so `addOneZ` returns the
trie as it is once a window test on the packed source value shows that all real digits are zero
(`OFF - H ≤ b < OFF - H + X`, i.e. `b / X = OFF / X`).  Otherwise it does exactly PR 209's `addOne`.
`checkSegZ_sound` gives the same `PRun` as `checkSeg_sound`, so nothing downstream changes.
Written for this port; it uses only the definitions and lemmas of `Submission/Cert/Scalar/Checker.lean`
(PR 209, HalitZiyaKARTAL v7-42). -/

namespace ScalarCheck.Skip
open WarpCheck CertData ScalarCheck.Spec ScalarCheck
set_option hygiene false in
local notation "orecP" => Option.rec (motive := fun _ => Option PT)
set_option hygiene false in
local notation "brecP" => Bool.rec (motive := fun _ => Option PT)

/-- `addOne` with the zero-source skip. The guards are those of `addOne` plus `den ≠ 0`. -/
noncomputable def addOneZ (c : Cx) (nr : Nat) (T : PT) (t s : Nat) (co : Co) : Option PT :=
  brecP none
    (brecP none
      (brecP
        (brecP
          ((fun b => brecP (modP T t fun a => lin c a b co)
              (brecP (modP T t fun a => lin c a b co) (some T) (Nat.blt b (Nat.add (Nat.sub c.OFF c.H) c.X)))
              (Nat.ble (Nat.sub c.OFF c.H) b)) (getP c.OFF T s))
          none (Nat.beq co.den 0))
        none (Nat.beq t s))
      (Nat.ble (Nat.succ s) nr))
    (Nat.ble (Nat.succ t) nr)

noncomputable def addsPZ (c : Cx) (nr : Nat) (l : List (Nat × Nat × Co)) : PT → Option PT :=
  List.rec (motive := fun _ => PT → Option PT) (fun T => some T)
    (fun e _ ih T => obind (addOneZ c nr T e.1 e.2.1 e.2.2) ih) l

noncomputable def outPZ (c : Cx) (nr s : Nat) (ts : List (Nat × Co)) : PT → Option PT :=
  List.rec (motive := fun _ => PT → Option PT) (fun T => some T)
    (fun p _ ih T => orecP none ih (addOneZ c nr T p.1 s p.2)) ts

noncomputable def innPZ (c : Cx) (nr t : Nat) (ss : List (Nat × Co)) : PT → Option PT :=
  List.rec (motive := fun _ => PT → Option PT) (fun T => some T)
    (fun p _ ih T => orecP none ih (addOneZ c nr T t p.1 p.2)) ss

noncomputable def gatePZ (c : Cx) (nr : Nat) (T : PT) (g : Gate) : Option PT :=
  Gate.rec (motive := fun _ => Option PT) (fun _ s ts _ => outPZ c nr s ts T) (fun _ t ss => innPZ c nr t ss T) g

noncomputable def stepPZ (c : Cx) (nr : Nat) (e : WEv) (T : PT) : Option PT :=
  WEv.rec (motive := fun _ => Option PT) (fun g => gatePZ c nr T g) (fun _ r co => scP c nr T r co)
    (fun _ _ _ _ => none) (fun r _ => zeroP c nr T r) (fun r => zeroP c nr T r) (fun _ _ => some T) e

noncomputable def runPZ (c : Cx) (nr : Nat) (l : List WEv) : PT → Option PT :=
  List.rec (motive := fun _ => PT → Option PT) (fun T => some T)
    (fun e _ ih T => orecP none ih (stepPZ c nr e T)) l

noncomputable def checkSegZ (c : Cx) (nr : Nat) (evs : List WEv) (A B : PT) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun T => eqPT T B)
    (orecP none (runPZ c nr evs) (forceT A))

theorem div_window {X H : Nat} (hX : H < X) : ∀ (n b : Nat), offN X H n - H ≤ b → b < offN X H n - H + X →
    b / X = offN X H n / X
  | 0, b, _, h2 => by
    simp only [offN, Nat.zero_sub, Nat.zero_add] at h2 ⊢
    rw [Nat.div_eq_of_lt h2, Nat.zero_div]
  | n + 1, b, h1, h2 => by
    show b / X = (H + X * offN X H n) / X
    rw [off_div hX]
    have e : offN X H (n + 1) - H = offN X H n * X := by
      show H + X * offN X H n - H = _
      rw [Nat.mul_comm]; omega
    rw [e] at h1 h2
    exact Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)

theorem zero_of_window {c : Cx} (hc : c.OK) {b : Nat} (h1 : c.OFF - c.H ≤ b) (h2 : b < c.OFF - c.H + c.X) :
    ∀ k, dec c.X c.H c.n b (k + 1) = 0 := by
  intro k
  rw [hc.hOFF] at h1 h2
  have hd := div_window hc.hlt c.n b h1 h2
  rw [← hc.hOFF] at hd
  rw [← dec_succ_of_div (X := c.X) (H := c.H) (u := b) (g := c.OFF) hd c.n k, dec_OFF hc]

theorem addOneZ_sound {c : Cx} (hc : c.OK) (q : SPw) {T T' : PT} {t s : Nat} {co : Co}
    (h : addOneZ c q.nr T t s co = some T') (hI : Inv c T) :
    AddStep q t s co (SP c T) (SP c T') ∧ Inv c T' := by
  unfold addOneZ at h
  obtain ⟨g1, h⟩ := brec_some h
  obtain ⟨g2, h⟩ := brec_some h
  obtain ⟨g3, h⟩ := nbrec_some h
  obtain ⟨g4, h⟩ := nbrec_some h
  have g1 : t < q.nr := Nat.le_of_ble_eq_true g1
  have g2 : s < q.nr := Nat.le_of_ble_eq_true g2
  have g3 : t ≠ s := Nat.ne_of_beq_eq_false g3
  have g4 : co.den ≠ 0 := Nat.ne_of_beq_eq_false g4
  -- the full add, as in PR 209's `addOne_sound`
  have full : modP T t (fun a => lin c a (getP c.OFF T s) co) = some T' →
      AddStep q t s co (SP c T) (SP c T') ∧ Inv c T' := by
    intro h
    rw [modP_eq c.OFF] at h
    obtain ⟨v, hl, hs⟩ := obind_some h
    obtain ⟨d0, dK, nK, hgd, ρ, hρ, e⟩ := lin_some hl
    have hv := hc.hgood v hgd
    obtain ⟨hI', hr, ho⟩ := set_sound hs hI hv
    refine ⟨⟨g1, g2, g3, d0, ?_, ho⟩, hI'⟩
    intro k
    rw [hr k]
    rw [show ((c.OFF : Nat) : Int) = ((offN c.X c.H c.n : Nat) : Int) from by rw [← hc.hOFF]] at e
    exact lin_dec0 hc.hH hc.hX co.den (sg co) ρ dK (by rw [natAbs_sg]; exact nK) hρ c.n _ _ _ (hI t) (hI s) hv e k
  simp only at h
  cases h1 : Nat.ble (Nat.sub c.OFF c.H) (getP c.OFF T s) with
  | false => rw [h1] at h; exact full h
  | true =>
    rw [h1] at h
    cases h2 : Nat.blt (getP c.OFF T s) (Nat.add (Nat.sub c.OFF c.H) c.X) with
    | false => rw [h2] at h; exact full h
    | true =>
      rw [h2] at h
      cases h
      have w1 : c.OFF - c.H ≤ getP c.OFF T s := Nat.le_of_ble_eq_true h1
      have w2 : getP c.OFF T s < c.OFF - c.H + c.X := Nat.le_of_ble_eq_true h2
      have z := zero_of_window hc w1 w2
      refine ⟨⟨g1, g2, g3, g4, fun k => ?_, fun _ _ => rfl⟩, hI⟩
      show (co.den : Int) * (SP c T t k - SP c T t k) = sg co * dec c.X c.H c.n (getP c.OFF T s) (k + 1)
      rw [z k]; simp

theorem addsPZ_sound {c : Cx} (hc : c.OK) (q : SPw) : ∀ (l : List (Nat × Nat × Co)) (T T' : PT),
    addsPZ c q.nr l T = some T' → Inv c T → Adds q l (SP c T) (SP c T') ∧ Inv c T'
  | [], T, T', h, hI => by
    cases h; exact ⟨Adds.nil _, hI⟩
  | (t, s, co) :: l, T, T', h, hI => by
    change obind (addOneZ c q.nr T t s co) (addsPZ c q.nr l) = some T' at h
    obtain ⟨T1, h1, h2⟩ := obind_some h
    obtain ⟨a1, I1⟩ := addOneZ_sound hc q h1 hI
    obtain ⟨a2, I2⟩ := addsPZ_sound hc q l T1 T' h2 I1
    exact ⟨Adds.cons a1 a2, I2⟩

theorem outPZ_eq (c : Cx) (nr s : Nat) : ∀ (ts : List (Nat × Co)) (T : PT),
    outPZ c nr s ts T = addsPZ c nr (ts.map fun p => (p.1, s, p.2)) T
  | [], _ => rfl
  | p :: ts, T => by
    show orecP none (outPZ c nr s ts) (addOneZ c nr T p.1 s p.2)
      = obind (addOneZ c nr T p.1 s p.2) (addsPZ c nr (ts.map fun p => (p.1, s, p.2)))
    rw [orec_obind, show outPZ c nr s ts = addsPZ c nr (ts.map fun p => (p.1, s, p.2)) from funext (outPZ_eq c nr s ts)]

theorem innPZ_eq (c : Cx) (nr t : Nat) : ∀ (ss : List (Nat × Co)) (T : PT),
    innPZ c nr t ss T = addsPZ c nr (ss.map fun p => (t, p.1, p.2)) T
  | [], _ => rfl
  | p :: ss, T => by
    show orecP none (innPZ c nr t ss) (addOneZ c nr T t p.1 p.2)
      = obind (addOneZ c nr T t p.1 p.2) (addsPZ c nr (ss.map fun p => (t, p.1, p.2)))
    rw [orec_obind, show innPZ c nr t ss = addsPZ c nr (ss.map fun p => (t, p.1, p.2)) from funext (innPZ_eq c nr t ss)]

theorem gatePZ_eq (c : Cx) (nr : Nat) (T : PT) (g : Gate) : gatePZ c nr T g = addsPZ c nr g.adds T := by
  cases g with
  | out f s ts x => exact outPZ_eq c nr s ts T
  | inn f t ss => exact innPZ_eq c nr t ss T

theorem stepPZ_sound {c : Cx} (hc : c.OK) (q : SPw) {e : WEv} {T T' : PT}
    (h : stepPZ c q.nr e T = some T') (hI : Inv c T) : Step q e (SP c T) (SP c T') ∧ Inv c T' := by
  cases e with
  | g g =>
    have h' : gatePZ c q.nr T g = some T' := h
    rw [gatePZ_eq] at h'
    exact addsPZ_sound hc q _ _ _ h' hI
  | sc f r co => exact stepP_sound hc q (e := .sc f r co) h hI
  | w r op f0 f1 => cases h
  | za r f => exact stepP_sound hc q (e := .za r f) h hI
  | zf r => exact stepP_sound hc q (e := .zf r) h hI
  | dn r f => cases h; exact ⟨rfl, hI⟩

theorem runPZ_sound {c : Cx} (hc : c.OK) (q : SPw) : ∀ (l : List WEv) (T T' : PT),
    runPZ c q.nr l T = some T' → Inv c T → Run q l (SP c T) (SP c T') ∧ Inv c T'
  | [], T, T', h, hI => by
    cases h; exact ⟨Run.nil _, hI⟩
  | e :: l, T, T', h, hI => by
    change orecP none (runPZ c q.nr l) (stepPZ c q.nr e T) = some T' at h
    rw [orec_obind] at h
    obtain ⟨T1, h1, h2⟩ := obind_some h
    obtain ⟨a1, I1⟩ := stepPZ_sound hc q h1 hI
    obtain ⟨a2, I2⟩ := runPZ_sound hc q l T1 T' h2 I1
    exact ⟨Run.cons a1 a2, I2⟩

theorem checkSegZ_sound {c : Cx} (hc : c.OK) (q : SPw) {evs : List WEv} {A B : PT}
    (h : checkSegZ c q.nr evs A B = true) : PRun c q evs A B := by
  intro hI
  unfold checkSegZ at h
  rw [forceT_eq] at h
  change Option.rec (motive := fun _ => Bool) false (fun T => eqPT T B) (runPZ c q.nr evs A) = true at h
  cases hr : runPZ c q.nr evs A with
  | none => rw [hr] at h; cases h
  | some T =>
    rw [hr] at h
    have := eqPT_eq _ _ h
    subst this
    exact runPZ_sound hc q evs A T hr hI

/-- The run itself as the segment statement (no `forceT`, no `eqPT`): proved by `Eq.refl` checked in the
kernel (`kernel_rfl`), so untouched leaves of the two checkpoints are compared structurally, never evaluated. -/
theorem runPZ_prun {c : Cx} (hc : c.OK) (q : SPw) {evs : List WEv} {A B : PT}
    (h : runPZ c q.nr evs A = some B) : PRun c q evs A B :=
  fun hI => runPZ_sound hc q evs A B h hI

end ScalarCheck.Skip

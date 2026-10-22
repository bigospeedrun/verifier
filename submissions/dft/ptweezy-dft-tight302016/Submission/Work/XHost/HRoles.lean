import Submission.Work.Bridge401.Merged1
import Submission.Work.XHost.HostK

/-!
# (key: bridge-host) Role maps of a HOSTED stage: a slot goes to a bank or to an idle data role of its run

Same-run hosting (DaysSky's idle-axis hosting, CrocSwap/integer-mult-bounds PR #442) on the nine-stage network of
Work/Bridge401 (Ryan Shea's complex588 tree; G401 by Nil Mamano on Dugongue #401 / jacklightChen #377 / Lydakis #275 /
DaysSky #363; engine, stage geometry and E8 unit by Jacob Sussman).  In stage `l` the slot `q` of invocation `g` lives in
`slotR hs u g q`: the bank `(g, u q)` when `hs q = none`, else the data role `(g, t)` of the pair `pairOf c`, side `s`
(`hs q = some (c, s, t)`, `c` the window kind of `XHost.inWin`).  `posH p hs u` is injective when the bank map is
injective on the non-hosted slots, no host is used twice, no host belongs to the acting pair `p`, and a stage sees at most
one window kind per pair (`HostOK`).  `ghliftQ<l>` is `GX.gbliftQ<l>` (Work/Bridge401/GStage.lean) for this embedding,
with the SAME scalar map `liftQ<l> u h` (the scalar maps of a stage never read the slot roles).
Written by h-L3-build/gen/gen_hnet.py (wht43, 13 Oct 2026), prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHost
open Binary Matrix Finset RAM SS CB RF BR GF GX

/-- the pair of the window kind `c` (A2 B2 A3 B3 A4 B4 F1 F2 F3). -/
def pairOf (c : Fin 9) : ℕ :=
  match c.val with
  | 0 => 2
  | 1 => 2
  | 2 => 3
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 1
  | 7 => 2
  | _ => 3

/-- the pair acting in stage `l`. -/
def pairL (l : ℕ) : ℕ :=
  match l with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 4
  | _ => 4

lemma win_pair : ∀ c l : Fin 9, inWin c.val l.val = true → pairOf c ≠ pairL l.val := by decide

lemma win_uniq : ∀ c c' l : Fin 9, inWin c.val l.val = true → inWin c'.val l.val = true →
    pairOf c = pairOf c' → c = c' := by decide

lemma pairOf_range : ∀ c : Fin 9, 1 ≤ pairOf c ∧ pairOf c ≤ 4 := by decide

lemma prng1 : 1 ≤ 1 ∧ 1 ≤ 4 := by decide
lemma prng2 : 1 ≤ 2 ∧ 2 ≤ 4 := by decide
lemma prng3 : 1 ≤ 3 ∧ 3 ≤ 4 := by decide
lemma prng4 : 1 ≤ 4 ∧ 4 ≤ 4 := by decide

noncomputable section

section Roles
variable {Γ T Sl C : Type} {nb : ℕ}

/-- the data role of pair `p` (1..4), side `s` (`false` = X, `true` = Y). -/
def dRole (p : ℕ) (s : Bool) (k : Γ × T) : BRun4 Γ T nb C :=
  match p, s with
  | 1, false => rqX1 k
  | 1, true => rqY1 k
  | 2, false => rqX2 k
  | 2, true => rqY2 k
  | 3, false => rqX3 k
  | 3, true => rqY3 k
  | _, false => rqX4 k
  | _, true => rqY4 k

/-- decoding of the data roles. -/
def dDec : BRun4 Γ T nb C → Option (ℕ × Bool × (Γ × T))
  | .inl (.inl (.inl (.inl (.inl (.inl k))))) => some (1, false, k)
  | .inl (.inl (.inl (.inl (.inl (.inr k))))) => some (1, true, k)
  | .inl (.inl (.inl (.inl (.inr (.inl k))))) => some (2, false, k)
  | .inl (.inl (.inl (.inl (.inr (.inr k))))) => some (2, true, k)
  | .inl (.inl (.inl (.inr (.inl k)))) => some (3, false, k)
  | .inl (.inl (.inl (.inr (.inr k)))) => some (3, true, k)
  | .inl (.inl (.inr (.inl k))) => some (4, false, k)
  | .inl (.inl (.inr (.inr k))) => some (4, true, k)
  | .inl (.inr _) => none
  | .inr _ => none

lemma dDec_dRole (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (s : Bool) (k : Γ × T) :
    dDec (dRole (nb := nb) (C := C) p s k) = some (p, s, k) := by
  obtain ⟨h1, h4⟩ := hp
  interval_cases p <;> cases s <;> rfl

lemma dRole_inj {p p' : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) (hp' : 1 ≤ p' ∧ p' ≤ 4) {s s' : Bool} {k k' : Γ × T}
    (h : dRole (nb := nb) (C := C) p s k = dRole p' s' k') : p = p' ∧ s = s' ∧ k = k' := by
  have e := congrArg dDec h
  rw [dDec_dRole p hp, dDec_dRole p' hp'] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  exact e

lemma dRole_ne_S {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) (s : Bool) (k : Γ × T) (b : Γ × Fin nb) :
    dRole (C := C) p s k ≠ rqS b := by
  intro h
  have e := congrArg dDec h
  rw [dDec_dRole p hp] at e
  exact absurd e (by simp [dDec, rqS])

lemma dRole_ne_C {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) (s : Bool) (k : Γ × T) (b : Γ × C) :
    dRole (nb := nb) p s k ≠ rqC b := by
  intro h
  have e := congrArg dDec h
  rw [dDec_dRole p hp] at e
  exact absurd e (by simp [dDec, rqC])

/-- the role of the slot `q` of invocation `g` in a hosted stage. -/
def slotR (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (g : Γ) (q : Sl) : BRun4 Γ T nb C :=
  match hs q with
  | some (c, s, t) => dRole (pairOf c) s (g, t)
  | none => rqS (g, u q)

lemma slotR_host {hs : Sl → Option (Fin 9 × (Bool × T))} {u : Sl → Fin nb} {g : Γ} {q : Sl} {c : Fin 9} {s : Bool}
    {t : T} (h : hs q = some (c, s, t)) : slotR (C := C) hs u g q = dRole (pairOf c) s (g, t) := by
  simp only [slotR, h]

lemma slotR_bank {hs : Sl → Option (Fin 9 × (Bool × T))} {u : Sl → Fin nb} {g : Γ} {q : Sl}
    (h : hs q = none) : slotR (C := C) hs u g q = rqS (g, u q) := by
  simp only [slotR, h]

/-- the roles of a hosted stage of pair `p` as roles of a run. -/
def posH (p : ℕ) (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => dRole p false (g, t)) (fun g t => dRole p true (g, t)) (fun g q => slotR hs u g q)
    (fun g c => rqC (g, c))

/-- the conditions on the slot table of one stage of pair `p`. -/
def HostOK (p : ℕ) (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) : Prop :=
  (∀ q q', hs q = none → hs q' = none → u q = u q' → q = q') ∧
  (∀ q q' j, hs q = some j → hs q' = some j → q = q') ∧
  (∀ q c j, hs q = some (c, j) → pairOf c ≠ p) ∧
  (∀ q q' c c' j j', hs q = some (c, j) → hs q' = some (c', j') → pairOf c = pairOf c' → c = c')

theorem posH_inj {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) {hs : Sl → Option (Fin 9 × (Bool × T))} {u : Sl → Fin nb}
    (hok : HostOK p hs u) : Function.Injective (posH (Γ := Γ) (C := C) p hs u) := by
  obtain ⟨hu, hh, hP, hU⟩ := hok
  have hS : ∀ (g : Γ) (q : Sl), (hs q = none ∧ slotR (C := C) hs u g q = rqS (g, u q)) ∨
      (∃ c s t, hs q = some (c, s, t) ∧ slotR (C := C) hs u g q = dRole (pairOf c) s (g, t)) := by
    intro g q
    rcases hq : hs q with _ | ⟨c, s, t⟩
    · exact Or.inl ⟨rfl, slotR_bank hq⟩
    · exact Or.inr ⟨c, s, t, rfl, slotR_host hq⟩
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h
  · change dRole p false (g, t) = dRole p false (g', t') at h
    obtain ⟨-, -, e⟩ := dRole_inj hp hp h
    rw [e]
  · change dRole p false (g, t) = dRole p true (g', t') at h
    exact absurd (dRole_inj hp hp h).2.1 (by decide)
  · change dRole p false (g, t) = slotR hs u g' q' at h
    rcases hS g' q' with ⟨-, e⟩ | ⟨c, s, t'', hq, e⟩
    · rw [e] at h
      exact absurd h (dRole_ne_S hp _ _ _)
    · rw [e] at h
      exact absurd (dRole_inj hp (pairOf_range c) h).1.symm (hP q' c (s, t'') hq)
  · change dRole p false (g, t) = rqC (g', c') at h
    exact absurd h (dRole_ne_C hp _ _ _)
  · change dRole p true (g, t) = dRole p false (g', t') at h
    exact absurd (dRole_inj hp hp h).2.1 (by decide)
  · change dRole p true (g, t) = dRole p true (g', t') at h
    obtain ⟨-, -, e⟩ := dRole_inj hp hp h
    rw [e]
  · change dRole p true (g, t) = slotR hs u g' q' at h
    rcases hS g' q' with ⟨-, e⟩ | ⟨c, s, t'', hq, e⟩
    · rw [e] at h
      exact absurd h (dRole_ne_S hp _ _ _)
    · rw [e] at h
      exact absurd (dRole_inj hp (pairOf_range c) h).1.symm (hP q' c (s, t'') hq)
  · change dRole p true (g, t) = rqC (g', c') at h
    exact absurd h (dRole_ne_C hp _ _ _)
  · change slotR hs u g q = dRole p false (g', t') at h
    rcases hS g q with ⟨-, e⟩ | ⟨c, s, t'', hq, e⟩
    · rw [e] at h
      exact absurd h.symm (dRole_ne_S hp _ _ _)
    · rw [e] at h
      exact absurd (dRole_inj (pairOf_range c) hp h).1 (hP q c (s, t'') hq)
  · change slotR hs u g q = dRole p true (g', t') at h
    rcases hS g q with ⟨-, e⟩ | ⟨c, s, t'', hq, e⟩
    · rw [e] at h
      exact absurd h.symm (dRole_ne_S hp _ _ _)
    · rw [e] at h
      exact absurd (dRole_inj (pairOf_range c) hp h).1 (hP q c (s, t'') hq)
  · change slotR hs u g q = slotR hs u g' q' at h
    rcases hS g q with ⟨hq, e⟩ | ⟨c, s, t, hq, e⟩ <;> rcases hS g' q' with ⟨hq', e'⟩ | ⟨c', s', t', hq', e'⟩ <;>
      rw [e, e'] at h
    · simp only [rqS, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, e2⟩ := h
      rw [hu q q' hq hq' e2]
    · exact absurd h.symm (dRole_ne_S (pairOf_range c') _ _ _)
    · exact absurd h (dRole_ne_S (pairOf_range c) _ _ _)
    · obtain ⟨e1, e2, e3⟩ := dRole_inj (pairOf_range c) (pairOf_range c') h
      simp only [Prod.mk.injEq] at e3
      obtain ⟨rfl, rfl⟩ := e3
      subst e2
      have ec := hU q q' c c' _ _ hq hq' e1
      subst ec
      rw [hh q q' _ hq hq']
  · change slotR hs u g q = rqC (g', c') at h
    rcases hS g q with ⟨-, e⟩ | ⟨c, s, t, -, e⟩
    · rw [e] at h
      exact absurd h (by simp [rqS, rqC])
    · rw [e] at h
      exact absurd h (dRole_ne_C (pairOf_range c) _ _ _)
  · change rqC (g, c) = dRole p false (g', t') at h
    exact absurd h.symm (dRole_ne_C hp _ _ _)
  · change rqC (g, c) = dRole p true (g', t') at h
    exact absurd h.symm (dRole_ne_C hp _ _ _)
  · change rqC (g, c) = slotR hs u g' q' at h
    rcases hS g' q' with ⟨-, e⟩ | ⟨c'', s, t, -, e⟩
    · rw [e] at h
      exact absurd h (by simp [rqS, rqC])
    · rw [e] at h
      exact absurd h.symm (dRole_ne_C (pairOf_range c'') _ _ _)
  · change rqC (g, c) = rqC (g', c') at h
    simp only [rqC, Sum.inr.injEq] at h
    rw [h]

def emH (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb)
    (hok : HostOK p hs u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posH p hs u, posH_inj hp hok⟩

/-- the scalar maps of a stage never read the slot roles. -/
lemma GF_loc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
    (∀ k, GF y (jX k) = GF y' (jX k)) ∧ (∀ k, GF y (jY k) = GF y' (jY k)) ∧ (∀ k, GF y (jC k) = GF y' (jC k)) := by
  intro y y' hX hY
  refine ⟨fun ⟨g, t⟩ => ?_, fun ⟨g, t⟩ => ?_, fun ⟨g, c⟩ => ?_⟩
  · exact hX (g, t)
  · show y (jY (g, t)) + y (jX (g, t)) = y' (jY (g, t)) + y' (jX (g, t))
    rw [hX, hY]
  · rfl

lemma GB_loc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
    (∀ k, GB y (jX k) = GB y' (jX k)) ∧ (∀ k, GB y (jY k) = GB y' (jY k)) ∧ (∀ k, GB y (jC k) = GB y' (jC k)) := by
  intro y y' hX hY
  refine ⟨fun ⟨g, t⟩ => ?_, fun ⟨g, t⟩ => ?_, fun ⟨g, c⟩ => ?_⟩
  · show y (jX (g, t)) - y (jY (g, t)) = y' (jX (g, t)) - y' (jY (g, t))
    rw [hX, hY]
  · exact hY (g, t)
  · rfl

/-- `liftQ0` keeps every data role outside pair 1 and every bank. -/
lemma liftQ0_fix (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ)
    {p' : ℕ} (hp' : 1 ≤ p' ∧ p' ≤ 4) (hne : p' ≠ 1) (s : Bool) (k : Γ × T) :
    liftQ0 u h x (dRole p' s k) = x (dRole p' s k) := by
  obtain ⟨g, t⟩ := k
  obtain ⟨h1, h4⟩ := hp'
  interval_cases p' <;> cases s <;> first | rfl | exact absurd rfl hne

/-- `liftQ1` keeps every data role outside pair 1 and every bank. -/
lemma liftQ1_fix (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ)
    {p' : ℕ} (hp' : 1 ≤ p' ∧ p' ≤ 4) (hne : p' ≠ 1) (s : Bool) (k : Γ × T) :
    liftQ1 u h x (dRole p' s k) = x (dRole p' s k) := by
  obtain ⟨g, t⟩ := k
  obtain ⟨h1, h4⟩ := hp'
  interval_cases p' <;> cases s <;> first | rfl | exact absurd rfl hne

/-- `liftQ2` keeps every data role outside pair 1 and every bank. -/
lemma liftQ2_fix (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ)
    {p' : ℕ} (hp' : 1 ≤ p' ∧ p' ≤ 4) (hne : p' ≠ 1) (s : Bool) (k : Γ × T) :
    liftQ2 u h x (dRole p' s k) = x (dRole p' s k) := by
  obtain ⟨g, t⟩ := k
  obtain ⟨h1, h4⟩ := hp'
  interval_cases p' <;> cases s <;> first | rfl | exact absurd rfl hne

/-- `liftQ3` keeps every data role outside pair 2 and every bank. -/
lemma liftQ3_fix (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ)
    {p' : ℕ} (hp' : 1 ≤ p' ∧ p' ≤ 4) (hne : p' ≠ 2) (s : Bool) (k : Γ × T) :
    liftQ3 u h x (dRole p' s k) = x (dRole p' s k) := by
  obtain ⟨g, t⟩ := k
  obtain ⟨h1, h4⟩ := hp'
  interval_cases p' <;> cases s <;> first | rfl | exact absurd rfl hne

/-- `liftQ4` keeps every data role outside pair 2 and every bank. -/
lemma liftQ4_fix (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ)
    {p' : ℕ} (hp' : 1 ≤ p' ∧ p' ≤ 4) (hne : p' ≠ 2) (s : Bool) (k : Γ × T) :
    liftQ4 u h x (dRole p' s k) = x (dRole p' s k) := by
  obtain ⟨g, t⟩ := k
  obtain ⟨h1, h4⟩ := hp'
  interval_cases p' <;> cases s <;> first | rfl | exact absurd rfl hne

/-- `liftQ5` keeps every data role outside pair 3 and every bank. -/
lemma liftQ5_fix (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ)
    {p' : ℕ} (hp' : 1 ≤ p' ∧ p' ≤ 4) (hne : p' ≠ 3) (s : Bool) (k : Γ × T) :
    liftQ5 u h x (dRole p' s k) = x (dRole p' s k) := by
  obtain ⟨g, t⟩ := k
  obtain ⟨h1, h4⟩ := hp'
  interval_cases p' <;> cases s <;> first | rfl | exact absurd rfl hne

/-- `liftQ6` keeps every data role outside pair 3 and every bank. -/
lemma liftQ6_fix (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ)
    {p' : ℕ} (hp' : 1 ≤ p' ∧ p' ≤ 4) (hne : p' ≠ 3) (s : Bool) (k : Γ × T) :
    liftQ6 u h x (dRole p' s k) = x (dRole p' s k) := by
  obtain ⟨g, t⟩ := k
  obtain ⟨h1, h4⟩ := hp'
  interval_cases p' <;> cases s <;> first | rfl | exact absurd rfl hne

/-- `liftQ7` keeps every data role outside pair 4 and every bank. -/
lemma liftQ7_fix (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ)
    {p' : ℕ} (hp' : 1 ≤ p' ∧ p' ≤ 4) (hne : p' ≠ 4) (s : Bool) (k : Γ × T) :
    liftQ7 u h x (dRole p' s k) = x (dRole p' s k) := by
  obtain ⟨g, t⟩ := k
  obtain ⟨h1, h4⟩ := hp'
  interval_cases p' <;> cases s <;> first | rfl | exact absurd rfl hne

/-- `liftQ8` keeps every data role outside pair 4 and every bank. -/
lemma liftQ8_fix (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ)
    {p' : ℕ} (hp' : 1 ≤ p' ∧ p' ≤ 4) (hne : p' ≠ 4) (s : Bool) (k : Γ × T) :
    liftQ8 u h x (dRole p' s k) = x (dRole p' s k) := by
  obtain ⟨g, t⟩ := k
  obtain ⟨h1, h4⟩ := hp'
  interval_cases p' <;> cases s <;> first | rfl | exact absurd rfl hne

end Roles

section Lift
variable {Γ T Sl C α : Type} {nb : ℕ} [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **A hosted route of stage 0 of a run** (pair 1): slots on banks or on idle data roles. -/
theorem ghliftQ0 (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (hok : HostOK 1 hs u)
    {S0 T0 : BRun4 Γ T nb C → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (rqX1 (g,t)) = SX g t) (hSY : ∀ g t, S0 (rqY1 (g,t)) = SY g t)
    (hUX : ∀ g t, T0 (rqX1 (g,t)) = UX g t) (hUY : ∀ g t, T0 (rqY1 (g,t)) = UY g t)
    (hSS : ∀ g q, S0 (slotR hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotR hs u g q) = US g q)
    (hSC : ∀ g c, S0 (rqC (g,c)) = SC g c) (hUC : ∀ g c, T0 (rqC (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) → S0 r = T0 r)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q)))
    (hloc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
      (∀ k, h y (jX k) = h y' (jX k)) ∧ (∀ k, h y (jY k) = h y' (jY k)) ∧ (∀ k, h y (jC k) = h y' (jC k))) :
    GRoute S0 T0 (liftQ0 u h) c := by
  refine GRoute.lift (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) hfix
  · have e1 : S0 ∘ (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hSX g t
      · exact hSY g t
      · exact hSS g q
      · exact hSC g c
    have e2 : T0 ∘ (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hUX g t
      · exact hUY g t
      · exact hUS g q
      · exact hUC g c
    rw [e1, e2]
    exact q
  · have hl := hloc (x ∘ posQ0 u) (x ∘ posH 1 hs u) (fun ⟨g, t⟩ => rfl) (fun ⟨g, t⟩ => rfl)
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hl.1 (g, t)
    · exact hl.2.1 (g, t)
    · show liftQ0 u h x (slotR hs u g q) = h (x ∘ posH 1 hs u) (jS (g, q))
      rw [hh]
      show liftQ0 u h x (slotR hs u g q) = x (slotR hs u g q)
      rcases hq : hs q with _ | ⟨c, s, t⟩
      · rw [slotR_bank hq]
        rfl
      · rw [slotR_host hq]
        exact liftQ0_fix u h x (pairOf_range c) (hok.2.2.1 q c (s, t) hq) s (g, t)
    · exact hl.2.2 (g, c)
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)

    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A hosted route of stage 1 of a run** (pair 1): slots on banks or on idle data roles. -/
theorem ghliftQ1 (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (hok : HostOK 1 hs u)
    {S0 T0 : BRun4 Γ T nb C → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (rqX1 (g,t)) = SX g t) (hSY : ∀ g t, S0 (rqY1 (g,t)) = SY g t)
    (hUX : ∀ g t, T0 (rqX1 (g,t)) = UX g t) (hUY : ∀ g t, T0 (rqY1 (g,t)) = UY g t)
    (hSS : ∀ g q, S0 (slotR hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotR hs u g q) = US g q)
    (hSC : ∀ g c, S0 (rqC (g,c)) = SC g c) (hUC : ∀ g c, T0 (rqC (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) → S0 r = T0 r)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q)))
    (hloc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
      (∀ k, h y (jX k) = h y' (jX k)) ∧ (∀ k, h y (jY k) = h y' (jY k)) ∧ (∀ k, h y (jC k) = h y' (jC k))) :
    GRoute S0 T0 (liftQ1 u h) c := by
  refine GRoute.lift (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) hfix
  · have e1 : S0 ∘ (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hSX g t
      · exact hSY g t
      · exact hSS g q
      · exact hSC g c
    have e2 : T0 ∘ (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hUX g t
      · exact hUY g t
      · exact hUS g q
      · exact hUC g c
    rw [e1, e2]
    exact q
  · have hl := hloc (x ∘ posQ1 u) (x ∘ posH 1 hs u) (fun ⟨g, t⟩ => rfl) (fun ⟨g, t⟩ => rfl)
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hl.1 (g, t)
    · exact hl.2.1 (g, t)
    · show liftQ1 u h x (slotR hs u g q) = h (x ∘ posH 1 hs u) (jS (g, q))
      rw [hh]
      show liftQ1 u h x (slotR hs u g q) = x (slotR hs u g q)
      rcases hq : hs q with _ | ⟨c, s, t⟩
      · rw [slotR_bank hq]
        rfl
      · rw [slotR_host hq]
        exact liftQ1_fix u h x (pairOf_range c) (hok.2.2.1 q c (s, t) hq) s (g, t)
    · exact hl.2.2 (g, c)
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)

    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A hosted route of stage 2 of a run** (pair 1): slots on banks or on idle data roles. -/
theorem ghliftQ2 (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (hok : HostOK 1 hs u)
    {S0 T0 : BRun4 Γ T nb C → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (rqX1 (g,t)) = SX g t) (hSY : ∀ g t, S0 (rqY1 (g,t)) = SY g t)
    (hUX : ∀ g t, T0 (rqX1 (g,t)) = UX g t) (hUY : ∀ g t, T0 (rqY1 (g,t)) = UY g t)
    (hSS : ∀ g q, S0 (slotR hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotR hs u g q) = US g q)
    (hSC : ∀ g c, S0 (rqC (g,c)) = SC g c) (hUC : ∀ g c, T0 (rqC (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) → S0 r = T0 r)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q)))
    (hloc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
      (∀ k, h y (jX k) = h y' (jX k)) ∧ (∀ k, h y (jY k) = h y' (jY k)) ∧ (∀ k, h y (jC k) = h y' (jC k))) :
    GRoute S0 T0 (liftQ2 u h) c := by
  refine GRoute.lift (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) hfix
  · have e1 : S0 ∘ (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hSX g t
      · exact hSY g t
      · exact hSS g q
      · exact hSC g c
    have e2 : T0 ∘ (emH (Γ := Γ) (C := C) 1 prng1 hs u hok) = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hUX g t
      · exact hUY g t
      · exact hUS g q
      · exact hUC g c
    rw [e1, e2]
    exact q
  · have hl := hloc (x ∘ posQ2 u) (x ∘ posH 1 hs u) (fun ⟨g, t⟩ => rfl) (fun ⟨g, t⟩ => rfl)
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hl.1 (g, t)
    · exact hl.2.1 (g, t)
    · show liftQ2 u h x (slotR hs u g q) = h (x ∘ posH 1 hs u) (jS (g, q))
      rw [hh]
      show liftQ2 u h x (slotR hs u g q) = x (slotR hs u g q)
      rcases hq : hs q with _ | ⟨c, s, t⟩
      · rw [slotR_bank hq]
        rfl
      · rw [slotR_host hq]
        exact liftQ2_fix u h x (pairOf_range c) (hok.2.2.1 q c (s, t) hq) s (g, t)
    · exact hl.2.2 (g, c)
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)

    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A hosted route of stage 3 of a run** (pair 2): slots on banks or on idle data roles. -/
theorem ghliftQ3 (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (hok : HostOK 2 hs u)
    {S0 T0 : BRun4 Γ T nb C → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (rqX2 (g,t)) = SX g t) (hSY : ∀ g t, S0 (rqY2 (g,t)) = SY g t)
    (hUX : ∀ g t, T0 (rqX2 (g,t)) = UX g t) (hUY : ∀ g t, T0 (rqY2 (g,t)) = UY g t)
    (hSS : ∀ g q, S0 (slotR hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotR hs u g q) = US g q)
    (hSC : ∀ g c, S0 (rqC (g,c)) = SC g c) (hUC : ∀ g c, T0 (rqC (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emH (Γ := Γ) (C := C) 2 prng2 hs u hok) → S0 r = T0 r)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q)))
    (hloc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
      (∀ k, h y (jX k) = h y' (jX k)) ∧ (∀ k, h y (jY k) = h y' (jY k)) ∧ (∀ k, h y (jC k) = h y' (jC k))) :
    GRoute S0 T0 (liftQ3 u h) c := by
  refine GRoute.lift (emH (Γ := Γ) (C := C) 2 prng2 hs u hok) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) hfix
  · have e1 : S0 ∘ (emH (Γ := Γ) (C := C) 2 prng2 hs u hok) = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hSX g t
      · exact hSY g t
      · exact hSS g q
      · exact hSC g c
    have e2 : T0 ∘ (emH (Γ := Γ) (C := C) 2 prng2 hs u hok) = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hUX g t
      · exact hUY g t
      · exact hUS g q
      · exact hUC g c
    rw [e1, e2]
    exact q
  · have hl := hloc (x ∘ posQ3 u) (x ∘ posH 2 hs u) (fun ⟨g, t⟩ => rfl) (fun ⟨g, t⟩ => rfl)
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hl.1 (g, t)
    · exact hl.2.1 (g, t)
    · show liftQ3 u h x (slotR hs u g q) = h (x ∘ posH 2 hs u) (jS (g, q))
      rw [hh]
      show liftQ3 u h x (slotR hs u g q) = x (slotR hs u g q)
      rcases hq : hs q with _ | ⟨c, s, t⟩
      · rw [slotR_bank hq]
        rfl
      · rw [slotR_host hq]
        exact liftQ3_fix u h x (pairOf_range c) (hok.2.2.1 q c (s, t) hq) s (g, t)
    · exact hl.2.2 (g, c)
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)

    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A hosted route of stage 4 of a run** (pair 2): slots on banks or on idle data roles. -/
theorem ghliftQ4 (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (hok : HostOK 2 hs u)
    {S0 T0 : BRun4 Γ T nb C → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (rqX2 (g,t)) = SX g t) (hSY : ∀ g t, S0 (rqY2 (g,t)) = SY g t)
    (hUX : ∀ g t, T0 (rqX2 (g,t)) = UX g t) (hUY : ∀ g t, T0 (rqY2 (g,t)) = UY g t)
    (hSS : ∀ g q, S0 (slotR hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotR hs u g q) = US g q)
    (hSC : ∀ g c, S0 (rqC (g,c)) = SC g c) (hUC : ∀ g c, T0 (rqC (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emH (Γ := Γ) (C := C) 2 prng2 hs u hok) → S0 r = T0 r)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q)))
    (hloc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
      (∀ k, h y (jX k) = h y' (jX k)) ∧ (∀ k, h y (jY k) = h y' (jY k)) ∧ (∀ k, h y (jC k) = h y' (jC k))) :
    GRoute S0 T0 (liftQ4 u h) c := by
  refine GRoute.lift (emH (Γ := Γ) (C := C) 2 prng2 hs u hok) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) hfix
  · have e1 : S0 ∘ (emH (Γ := Γ) (C := C) 2 prng2 hs u hok) = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hSX g t
      · exact hSY g t
      · exact hSS g q
      · exact hSC g c
    have e2 : T0 ∘ (emH (Γ := Γ) (C := C) 2 prng2 hs u hok) = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hUX g t
      · exact hUY g t
      · exact hUS g q
      · exact hUC g c
    rw [e1, e2]
    exact q
  · have hl := hloc (x ∘ posQ4 u) (x ∘ posH 2 hs u) (fun ⟨g, t⟩ => rfl) (fun ⟨g, t⟩ => rfl)
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hl.1 (g, t)
    · exact hl.2.1 (g, t)
    · show liftQ4 u h x (slotR hs u g q) = h (x ∘ posH 2 hs u) (jS (g, q))
      rw [hh]
      show liftQ4 u h x (slotR hs u g q) = x (slotR hs u g q)
      rcases hq : hs q with _ | ⟨c, s, t⟩
      · rw [slotR_bank hq]
        rfl
      · rw [slotR_host hq]
        exact liftQ4_fix u h x (pairOf_range c) (hok.2.2.1 q c (s, t) hq) s (g, t)
    · exact hl.2.2 (g, c)
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)

    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A hosted route of stage 5 of a run** (pair 3): slots on banks or on idle data roles. -/
theorem ghliftQ5 (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (hok : HostOK 3 hs u)
    {S0 T0 : BRun4 Γ T nb C → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (rqX3 (g,t)) = SX g t) (hSY : ∀ g t, S0 (rqY3 (g,t)) = SY g t)
    (hUX : ∀ g t, T0 (rqX3 (g,t)) = UX g t) (hUY : ∀ g t, T0 (rqY3 (g,t)) = UY g t)
    (hSS : ∀ g q, S0 (slotR hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotR hs u g q) = US g q)
    (hSC : ∀ g c, S0 (rqC (g,c)) = SC g c) (hUC : ∀ g c, T0 (rqC (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emH (Γ := Γ) (C := C) 3 prng3 hs u hok) → S0 r = T0 r)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q)))
    (hloc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
      (∀ k, h y (jX k) = h y' (jX k)) ∧ (∀ k, h y (jY k) = h y' (jY k)) ∧ (∀ k, h y (jC k) = h y' (jC k))) :
    GRoute S0 T0 (liftQ5 u h) c := by
  refine GRoute.lift (emH (Γ := Γ) (C := C) 3 prng3 hs u hok) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) hfix
  · have e1 : S0 ∘ (emH (Γ := Γ) (C := C) 3 prng3 hs u hok) = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hSX g t
      · exact hSY g t
      · exact hSS g q
      · exact hSC g c
    have e2 : T0 ∘ (emH (Γ := Γ) (C := C) 3 prng3 hs u hok) = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hUX g t
      · exact hUY g t
      · exact hUS g q
      · exact hUC g c
    rw [e1, e2]
    exact q
  · have hl := hloc (x ∘ posQ5 u) (x ∘ posH 3 hs u) (fun ⟨g, t⟩ => rfl) (fun ⟨g, t⟩ => rfl)
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hl.1 (g, t)
    · exact hl.2.1 (g, t)
    · show liftQ5 u h x (slotR hs u g q) = h (x ∘ posH 3 hs u) (jS (g, q))
      rw [hh]
      show liftQ5 u h x (slotR hs u g q) = x (slotR hs u g q)
      rcases hq : hs q with _ | ⟨c, s, t⟩
      · rw [slotR_bank hq]
        rfl
      · rw [slotR_host hq]
        exact liftQ5_fix u h x (pairOf_range c) (hok.2.2.1 q c (s, t) hq) s (g, t)
    · exact hl.2.2 (g, c)
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)

    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A hosted route of stage 6 of a run** (pair 3): slots on banks or on idle data roles. -/
theorem ghliftQ6 (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (hok : HostOK 3 hs u)
    {S0 T0 : BRun4 Γ T nb C → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (rqX3 (g,t)) = SX g t) (hSY : ∀ g t, S0 (rqY3 (g,t)) = SY g t)
    (hUX : ∀ g t, T0 (rqX3 (g,t)) = UX g t) (hUY : ∀ g t, T0 (rqY3 (g,t)) = UY g t)
    (hSS : ∀ g q, S0 (slotR hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotR hs u g q) = US g q)
    (hSC : ∀ g c, S0 (rqC (g,c)) = SC g c) (hUC : ∀ g c, T0 (rqC (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emH (Γ := Γ) (C := C) 3 prng3 hs u hok) → S0 r = T0 r)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q)))
    (hloc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
      (∀ k, h y (jX k) = h y' (jX k)) ∧ (∀ k, h y (jY k) = h y' (jY k)) ∧ (∀ k, h y (jC k) = h y' (jC k))) :
    GRoute S0 T0 (liftQ6 u h) c := by
  refine GRoute.lift (emH (Γ := Γ) (C := C) 3 prng3 hs u hok) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) hfix
  · have e1 : S0 ∘ (emH (Γ := Γ) (C := C) 3 prng3 hs u hok) = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hSX g t
      · exact hSY g t
      · exact hSS g q
      · exact hSC g c
    have e2 : T0 ∘ (emH (Γ := Γ) (C := C) 3 prng3 hs u hok) = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hUX g t
      · exact hUY g t
      · exact hUS g q
      · exact hUC g c
    rw [e1, e2]
    exact q
  · have hl := hloc (x ∘ posQ6 u) (x ∘ posH 3 hs u) (fun ⟨g, t⟩ => rfl) (fun ⟨g, t⟩ => rfl)
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hl.1 (g, t)
    · exact hl.2.1 (g, t)
    · show liftQ6 u h x (slotR hs u g q) = h (x ∘ posH 3 hs u) (jS (g, q))
      rw [hh]
      show liftQ6 u h x (slotR hs u g q) = x (slotR hs u g q)
      rcases hq : hs q with _ | ⟨c, s, t⟩
      · rw [slotR_bank hq]
        rfl
      · rw [slotR_host hq]
        exact liftQ6_fix u h x (pairOf_range c) (hok.2.2.1 q c (s, t) hq) s (g, t)
    · exact hl.2.2 (g, c)
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)

    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A hosted route of stage 7 of a run** (pair 4): slots on banks or on idle data roles. -/
theorem ghliftQ7 (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (hok : HostOK 4 hs u)
    {S0 T0 : BRun4 Γ T nb C → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (rqX4 (g,t)) = SX g t) (hSY : ∀ g t, S0 (rqY4 (g,t)) = SY g t)
    (hUX : ∀ g t, T0 (rqX4 (g,t)) = UX g t) (hUY : ∀ g t, T0 (rqY4 (g,t)) = UY g t)
    (hSS : ∀ g q, S0 (slotR hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotR hs u g q) = US g q)
    (hSC : ∀ g c, S0 (rqC (g,c)) = SC g c) (hUC : ∀ g c, T0 (rqC (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emH (Γ := Γ) (C := C) 4 prng4 hs u hok) → S0 r = T0 r)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q)))
    (hloc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
      (∀ k, h y (jX k) = h y' (jX k)) ∧ (∀ k, h y (jY k) = h y' (jY k)) ∧ (∀ k, h y (jC k) = h y' (jC k))) :
    GRoute S0 T0 (liftQ7 u h) c := by
  refine GRoute.lift (emH (Γ := Γ) (C := C) 4 prng4 hs u hok) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) hfix
  · have e1 : S0 ∘ (emH (Γ := Γ) (C := C) 4 prng4 hs u hok) = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hSX g t
      · exact hSY g t
      · exact hSS g q
      · exact hSC g c
    have e2 : T0 ∘ (emH (Γ := Γ) (C := C) 4 prng4 hs u hok) = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hUX g t
      · exact hUY g t
      · exact hUS g q
      · exact hUC g c
    rw [e1, e2]
    exact q
  · have hl := hloc (x ∘ posQ7 u) (x ∘ posH 4 hs u) (fun ⟨g, t⟩ => rfl) (fun ⟨g, t⟩ => rfl)
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hl.1 (g, t)
    · exact hl.2.1 (g, t)
    · show liftQ7 u h x (slotR hs u g q) = h (x ∘ posH 4 hs u) (jS (g, q))
      rw [hh]
      show liftQ7 u h x (slotR hs u g q) = x (slotR hs u g q)
      rcases hq : hs q with _ | ⟨c, s, t⟩
      · rw [slotR_bank hq]
        rfl
      · rw [slotR_host hq]
        exact liftQ7_fix u h x (pairOf_range c) (hok.2.2.1 q c (s, t) hq) s (g, t)
    · exact hl.2.2 (g, c)
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)

    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A hosted route of stage 8 of a run** (pair 4): slots on banks or on idle data roles. -/
theorem ghliftQ8 (hs : Sl → Option (Fin 9 × (Bool × T))) (u : Sl → Fin nb) (hok : HostOK 4 hs u)
    {S0 T0 : BRun4 Γ T nb C → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (rqX4 (g,t)) = SX g t) (hSY : ∀ g t, S0 (rqY4 (g,t)) = SY g t)
    (hUX : ∀ g t, T0 (rqX4 (g,t)) = UX g t) (hUY : ∀ g t, T0 (rqY4 (g,t)) = UY g t)
    (hSS : ∀ g q, S0 (slotR hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotR hs u g q) = US g q)
    (hSC : ∀ g c, S0 (rqC (g,c)) = SC g c) (hUC : ∀ g c, T0 (rqC (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emH (Γ := Γ) (C := C) 4 prng4 hs u hok) → S0 r = T0 r)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q)))
    (hloc : ∀ y y' : SRole Γ T Sl C → ℂ, (∀ k, y (jX k) = y' (jX k)) → (∀ k, y (jY k) = y' (jY k)) →
      (∀ k, h y (jX k) = h y' (jX k)) ∧ (∀ k, h y (jY k) = h y' (jY k)) ∧ (∀ k, h y (jC k) = h y' (jC k))) :
    GRoute S0 T0 (liftQ8 u h) c := by
  refine GRoute.lift (emH (Γ := Γ) (C := C) 4 prng4 hs u hok) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) hfix
  · have e1 : S0 ∘ (emH (Γ := Γ) (C := C) 4 prng4 hs u hok) = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hSX g t
      · exact hSY g t
      · exact hSS g q
      · exact hSC g c
    have e2 : T0 ∘ (emH (Γ := Γ) (C := C) 4 prng4 hs u hok) = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact hUX g t
      · exact hUY g t
      · exact hUS g q
      · exact hUC g c
    rw [e1, e2]
    exact q
  · have hl := hloc (x ∘ posQ8 u) (x ∘ posH 4 hs u) (fun ⟨g, t⟩ => rfl) (fun ⟨g, t⟩ => rfl)
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hl.1 (g, t)
    · exact hl.2.1 (g, t)
    · show liftQ8 u h x (slotR hs u g q) = h (x ∘ posH 4 hs u) (jS (g, q))
      rw [hh]
      show liftQ8 u h x (slotR hs u g q) = x (slotR hs u g q)
      rcases hq : hs q with _ | ⟨c, s, t⟩
      · rw [slotR_bank hq]
        rfl
      · rw [slotR_host hq]
        exact liftQ8_fix u h x (pairOf_range c) (hok.2.2.1 q c (s, t) hq) s (g, t)
    · exact hl.2.2 (g, c)
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)

    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

end Lift
end
end XHost
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHost.ghliftQ0
#print axioms OAI.PowerSaving.XHost.ghliftQ1
#print axioms OAI.PowerSaving.XHost.ghliftQ2
#print axioms OAI.PowerSaving.XHost.ghliftQ3
#print axioms OAI.PowerSaving.XHost.ghliftQ4
#print axioms OAI.PowerSaving.XHost.ghliftQ5
#print axioms OAI.PowerSaving.XHost.ghliftQ6
#print axioms OAI.PowerSaving.XHost.ghliftQ7
#print axioms OAI.PowerSaving.XHost.ghliftQ8

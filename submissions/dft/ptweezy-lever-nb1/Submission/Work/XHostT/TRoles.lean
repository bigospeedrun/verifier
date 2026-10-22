import Submission.Work.XHost.HRoles

/-!
# (key: bridge-host-cross) Roles of the CROSS-REPLICA hosted nine-stage word

Generalisation of h-L3-build's `Work/XHost/HRoles.lean` (same-run hosting) and fsp-perrun's per-run tables
(`Work/XHostR`) to `nR` replicas whose calls are interleaved in a global order: in call `τ` the slot `q` goes to the
idle data role of ANY replica, `hs q = some (ρh, c, s, t)` (host replica `ρh`, window kind `c`, side `s`, class `t`),
or to a bank.  The banks are given by a DEPENDENT map (`u q : hs q = none → Fin nb`), so a table with every slot hosted
needs no bank at all (`nb = 0`, as in the hub's T74 construction).

* `BRoleT Γ T nb C nR`: the data of the `nR` replicas, the banks, the copies (`BRole401` with `Fin nR` replicas);
* `dD p s k`: the data role of pair `p`, side `s` of one replica; `dDecD` decodes it;
* `slotT hs u g q`: the role of slot `q` of invocation `g` in a hosted call; `posT ρ p hs u`: the roles of a hosted
  call of replica `ρ` (acting pair `p`) as global roles; injective under `HostOKT` (`posT_inj`);
* `scF ρ p` / `scB ρ p`: the scalar maps of a forward / backward stage of replica `ρ` on pair `p` (Shea's `GF` / `GB`
  on that pair, copies erased), defined WITHOUT a bank map;
* `ghliftT`: a hosted stage route on the one-pair roles lifts to the global roles (`GRoute.lift`).

Built on Ryan Shea's complex588 tree (Bridge401: G401 by Nil Mamano on Dugongue #401 / jacklightChen #377 / Lydakis
#275 / DaysSky #363; engine and E8 unit by Jacob Sussman) and DaysSky's idle-axis hosting (CrocSwap/integer-mult-bounds
PR #442).  Written by rb-a3 (wht43, 14 Oct 2026), prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHostT
open Binary Matrix Finset RAM SS CB RF BR GF GX XHost

abbrev BLiveT (Γ T : Type) (nb nR : ℕ) := (Fin nR × BDat4 Γ T) ⊕ (Γ × Fin nb)
abbrev BRoleT (Γ T : Type) (nb : ℕ) (C : Type) (nR : ℕ) := BLiveT Γ T nb nR ⊕ (Γ × C)

section Inst
set_option synthInstance.maxSize 4096 in
instance bTliveDec {Γ T : Type} {nb nR : ℕ} [DecidableEq Γ] [DecidableEq T] :
    DecidableEq (BLiveT Γ T nb nR) := inferInstance
set_option synthInstance.maxSize 4096 in
instance bTroleDec {Γ T C : Type} {nb nR : ℕ} [DecidableEq Γ] [DecidableEq T] [DecidableEq C] :
    DecidableEq (BRoleT Γ T nb C nR) := inferInstance
instance bTliveFin {Γ T : Type} {nb nR : ℕ} [Fintype Γ] [Fintype T] : Fintype (BLiveT Γ T nb nR) := inferInstance
instance bTroleFin {Γ T C : Type} {nb nR : ℕ} [Fintype Γ] [Fintype T] [Fintype C] :
    Fintype (BRoleT Γ T nb C nR) := inferInstance
end Inst

noncomputable section

section Roles
variable {Γ T Sl C : Type} {nb nR : ℕ}

/-- the data role of pair `p` (1..4), side `s` (`false` = X, `true` = Y) of one replica. -/
def dD (p : ℕ) (s : Bool) (k : Γ × T) : BDat4 Γ T :=
  match p, s with
  | 1, false => dqX1 k
  | 1, true => dqY1 k
  | 2, false => dqX2 k
  | 2, true => dqY2 k
  | 3, false => dqX3 k
  | 3, true => dqY3 k
  | _, false => dqX4 k
  | _, true => dqY4 k

/-- decoding of the data roles of one replica: (pair, side, class). -/
def dDecD : BDat4 Γ T → ℕ × Bool × (Γ × T)
  | .inl (.inl (.inl (.inl k))) => (1, false, k)
  | .inl (.inl (.inl (.inr k))) => (1, true, k)
  | .inl (.inl (.inr (.inl k))) => (2, false, k)
  | .inl (.inl (.inr (.inr k))) => (2, true, k)
  | .inl (.inr (.inl k)) => (3, false, k)
  | .inl (.inr (.inr k)) => (3, true, k)
  | .inr (.inl k) => (4, false, k)
  | .inr (.inr k) => (4, true, k)

lemma dDecD_dD (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (s : Bool) (k : Γ × T) : dDecD (dD p s k) = (p, s, k) := by
  obtain ⟨h1, h4⟩ := hp
  interval_cases p <;> cases s <;> rfl

lemma dD_dDecD (d : BDat4 Γ T) : dD (dDecD d).1 (dDecD d).2.1 (dDecD d).2.2 = d := by
  rcases d with ((((k|k)|(k|k))|(k|k))|(k|k)) <;> rfl

lemma dDecD_range (d : BDat4 Γ T) : 1 ≤ (dDecD d).1 ∧ (dDecD d).1 ≤ 4 := by
  rcases d with ((((k|k)|(k|k))|(k|k))|(k|k)) <;> simp [dDecD]

lemma dD_inj {p p' : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) (hp' : 1 ≤ p' ∧ p' ≤ 4) {s s' : Bool} {k k' : Γ × T}
    (h : dD p s k = dD p' s' k') : p = p' ∧ s = s' ∧ k = k' := by
  have e := congrArg dDecD h
  rw [dDecD_dD p hp, dDecD_dD p' hp'] at e
  simp only [Prod.mk.injEq] at e
  exact e

/-- every data role is `dD p s k` for its decoding. -/
lemma dD_cases (d : BDat4 Γ T) : ∃ p s k, (1 ≤ p ∧ p ≤ 4) ∧ d = dD p s k :=
  ⟨_, _, _, dDecD_range d, (dD_dDecD d).symm⟩

/-- a function on all roles. -/
def mkT {β : Type*} (fD : Fin nR → BDat4 Γ T → β) (fS : Γ → Fin nb → β) (fC : Γ → C → β) :
    BRoleT Γ T nb C nR → β
  | .inl (.inl (ρ, d)) => fD ρ d
  | .inl (.inr (g, b)) => fS g b
  | .inr (g, c) => fC g c

lemma mkT_map {β γ : Type*} (h : β → γ) (fD : Fin nR → BDat4 Γ T → β) (fS : Γ → Fin nb → β)
    (fC : Γ → C → β) (r : BRoleT Γ T nb C nR) :
    h (mkT fD fS fC r) = mkT (fun ρ d => h (fD ρ d)) (fun g b => h (fS g b)) (fun g c => h (fC g c)) r := by
  rcases r with ((⟨ρ,d⟩|⟨g,b⟩)|⟨g,c⟩) <;> rfl

lemma sum_mkT [Fintype Γ] [Fintype T] [Fintype C]
    (fD : Fin nR → BDat4 Γ T → ℝ) (fS : Γ → Fin nb → ℝ) (fC : Γ → C → ℝ) :
    ∑ r : BRoleT Γ T nb C nR, mkT fD fS fC r = ∑ ρ, ∑ d, fD ρ d + ∑ g, ∑ b, fS g b + ∑ g, ∑ c, fC g c := by
  simp only [Fintype.sum_sum_type, mkT, Fintype.sum_prod_type]

/-- the roles of a run as the roles of replica `ρ`. -/
def runPosT (ρ : Fin nR) : BRun4 Γ T nb C → BRoleT Γ T nb C nR
  | .inl (.inl d) => .inl (.inl (ρ, d))
  | .inl (.inr s) => .inl (.inr s)
  | .inr c => .inr c

lemma runPosT_inj (ρ : Fin nR) : Function.Injective (runPosT ρ : BRun4 Γ T nb C → BRoleT Γ T nb C nR) := by
  intro a b h
  rcases a with ((d|s)|c) <;> rcases b with ((d'|s')|c') <;> simp_all [runPosT]

def emRunT (ρ : Fin nR) : BRun4 Γ T nb C ↪ BRoleT Γ T nb C nR := ⟨runPosT ρ, runPosT_inj ρ⟩

/-- scalar map of a run-local map `h` of replica `ρ`: replica `ρ`, the banks and the copies move by `h`, the other
replicas keep their contents. -/
def liftRunT (ρ : Fin nR) (h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) (x : BRoleT Γ T nb C nR → ℂ) :
    BRoleT Γ T nb C nR → ℂ
  | .inl (.inl (ρ', d)) => if ρ' = ρ then h (x ∘ runPosT ρ) (.inl (.inl d)) else x (.inl (.inl (ρ', d)))
  | .inl (.inr s) => h (x ∘ runPosT ρ) (.inl (.inr s))
  | .inr c => h (x ∘ runPosT ρ) (.inr c)

/-- the role of slot `q` of invocation `g` in a hosted call: a data role of the host replica, or a bank. -/
def slotT (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T))) (u : (q : Sl) → hs q = none → Fin nb) (g : Γ) (q : Sl) :
    BRoleT Γ T nb C nR :=
  match h : hs q with
  | some (ρh, c, s, t) => .inl (.inl (ρh, dD (pairOf c) s (g, t)))
  | none => .inl (.inr (g, u q h))

lemma slotT_host {hs : Sl → Option (Fin nR × Fin 9 × (Bool × T))} {u : (q : Sl) → hs q = none → Fin nb} {g : Γ}
    {q : Sl} {ρh : Fin nR} {c : Fin 9} {s : Bool} {t : T} (h : hs q = some (ρh, c, s, t)) :
    slotT (C := C) hs u g q = .inl (.inl (ρh, dD (pairOf c) s (g, t))) := by
  unfold slotT
  split
  · rename_i ρ' c' s' t' h'
    rw [h] at h'
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
    rfl
  · rename_i h'
    rw [h] at h'
    exact absurd h' (by simp)

lemma slotT_bank {hs : Sl → Option (Fin nR × Fin 9 × (Bool × T))} {u : (q : Sl) → hs q = none → Fin nb} {g : Γ}
    {q : Sl} (h : hs q = none) : slotT (C := C) hs u g q = .inl (.inr (g, u q h)) := by
  unfold slotT
  split
  · rename_i ρ' c' s' t' h'
    rw [h] at h'
    exact absurd h' (by simp)
  · rfl

/-- the roles of a hosted call of replica `ρ` (acting pair `p`) as global roles. -/
def posT (ρ : Fin nR) (p : ℕ) (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T)))
    (u : (q : Sl) → hs q = none → Fin nb) : SRole Γ T Sl C → BRoleT Γ T nb C nR :=
  mkS (fun g t => .inl (.inl (ρ, dD p false (g, t)))) (fun g t => .inl (.inl (ρ, dD p true (g, t))))
    (fun g q => slotT hs u g q) (fun g c => .inr (g, c))

/-- the conditions on the slot table of one call of replica `ρ` with acting pair `p`: banks injective on the
non-hosted slots, no host used twice, no host on the acting pair of the calling replica, one window kind per pair and
replica. -/
def HostOKT (ρ : Fin nR) (p : ℕ) (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T)))
    (u : (q : Sl) → hs q = none → Fin nb) : Prop :=
  (∀ q q' (h : hs q = none) (h' : hs q' = none), u q h = u q' h' → q = q') ∧
  (∀ q q' j, hs q = some j → hs q' = some j → q = q') ∧
  (∀ q c j, hs q = some (ρ, c, j) → pairOf c ≠ p) ∧
  (∀ q q' ρh c c' j j', hs q = some (ρh, c, j) → hs q' = some (ρh, c', j') → pairOf c = pairOf c' → c = c')

lemma slotT_cases (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T))) (u : (q : Sl) → hs q = none → Fin nb) (g : Γ)
    (q : Sl) : (∃ h : hs q = none, slotT (C := C) hs u g q = .inl (.inr (g, u q h))) ∨
      (∃ ρh c s t, hs q = some (ρh, c, s, t) ∧ slotT (C := C) hs u g q = .inl (.inl (ρh, dD (pairOf c) s (g, t)))) := by
  by_cases hq : hs q = none
  · exact Or.inl ⟨hq, slotT_bank hq⟩
  · obtain ⟨⟨ρh, c, s, t⟩, he⟩ := Option.ne_none_iff_exists'.mp hq
    exact Or.inr ⟨ρh, c, s, t, he, slotT_host he⟩

theorem posT_inj {ρ : Fin nR} {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) {hs : Sl → Option (Fin nR × Fin 9 × (Bool × T))}
    {u : (q : Sl) → hs q = none → Fin nb} (hok : HostOKT ρ p hs u) :
    Function.Injective (posT (Γ := Γ) (C := C) ρ p hs u) := by
  obtain ⟨hu, hh, hP, hU⟩ := hok
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h
  · change (Sum.inl (Sum.inl (ρ, dD p false (g, t))) : BRoleT Γ T nb C nR) = .inl (.inl (ρ, dD p false (g', t'))) at h
    simp only [Sum.inl.injEq, Prod.mk.injEq, true_and] at h
    obtain ⟨-, -, e⟩ := dD_inj hp hp h
    rw [e]
  · change (Sum.inl (Sum.inl (ρ, dD p false (g, t))) : BRoleT Γ T nb C nR) = .inl (.inl (ρ, dD p true (g', t'))) at h
    simp only [Sum.inl.injEq, Prod.mk.injEq, true_and] at h
    exact absurd (dD_inj hp hp h).2.1 (by decide)
  · change (Sum.inl (Sum.inl (ρ, dD p false (g, t))) : BRoleT Γ T nb C nR) = slotT hs u g' q' at h
    rcases slotT_cases (C := C) hs u g' q' with ⟨hq, e⟩ | ⟨ρh, c, s, t'', hq, e⟩
    · rw [e] at h
      exact absurd h (by simp)
    · rw [e] at h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2⟩ := h
      subst e1
      exact absurd (dD_inj hp (pairOf_range c) e2).1.symm (hP q' c (s, t'') hq)
  · change (Sum.inl (Sum.inl (ρ, dD p false (g, t))) : BRoleT Γ T nb C nR) = .inr (g', c') at h
    exact absurd h (by simp)
  · change (Sum.inl (Sum.inl (ρ, dD p true (g, t))) : BRoleT Γ T nb C nR) = .inl (.inl (ρ, dD p false (g', t'))) at h
    simp only [Sum.inl.injEq, Prod.mk.injEq, true_and] at h
    exact absurd (dD_inj hp hp h).2.1 (by decide)
  · change (Sum.inl (Sum.inl (ρ, dD p true (g, t))) : BRoleT Γ T nb C nR) = .inl (.inl (ρ, dD p true (g', t'))) at h
    simp only [Sum.inl.injEq, Prod.mk.injEq, true_and] at h
    obtain ⟨-, -, e⟩ := dD_inj hp hp h
    rw [e]
  · change (Sum.inl (Sum.inl (ρ, dD p true (g, t))) : BRoleT Γ T nb C nR) = slotT hs u g' q' at h
    rcases slotT_cases (C := C) hs u g' q' with ⟨hq, e⟩ | ⟨ρh, c, s, t'', hq, e⟩
    · rw [e] at h
      exact absurd h (by simp)
    · rw [e] at h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2⟩ := h
      subst e1
      exact absurd (dD_inj hp (pairOf_range c) e2).1.symm (hP q' c (s, t'') hq)
  · change (Sum.inl (Sum.inl (ρ, dD p true (g, t))) : BRoleT Γ T nb C nR) = .inr (g', c') at h
    exact absurd h (by simp)
  · change slotT hs u g q = (Sum.inl (Sum.inl (ρ, dD p false (g', t'))) : BRoleT Γ T nb C nR) at h
    rcases slotT_cases (C := C) hs u g q with ⟨hq, e⟩ | ⟨ρh, c, s, t'', hq, e⟩
    · rw [e] at h
      exact absurd h (by simp)
    · rw [e] at h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2⟩ := h
      subst e1
      exact absurd (dD_inj (pairOf_range c) hp e2).1 (hP q c (s, t'') hq)
  · change slotT hs u g q = (Sum.inl (Sum.inl (ρ, dD p true (g', t'))) : BRoleT Γ T nb C nR) at h
    rcases slotT_cases (C := C) hs u g q with ⟨hq, e⟩ | ⟨ρh, c, s, t'', hq, e⟩
    · rw [e] at h
      exact absurd h (by simp)
    · rw [e] at h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2⟩ := h
      subst e1
      exact absurd (dD_inj (pairOf_range c) hp e2).1 (hP q c (s, t'') hq)
  · change slotT hs u g q = slotT hs u g' q' at h
    rcases slotT_cases (C := C) hs u g q with ⟨hq, e⟩ | ⟨ρh, c, s, t, hq, e⟩ <;>
      rcases slotT_cases (C := C) hs u g' q' with ⟨hq', e'⟩ | ⟨ρh', c', s', t', hq', e'⟩ <;>
      rw [e, e'] at h
    · simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, e2⟩ := h
      rw [hu q q' hq hq' e2]
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨e0, e3⟩ := h
      subst e0
      obtain ⟨e1, e2, e4⟩ := dD_inj (pairOf_range c) (pairOf_range c') e3
      simp only [Prod.mk.injEq] at e4
      obtain ⟨rfl, rfl⟩ := e4
      subst e2
      have ec := hU q q' ρh c c' _ _ hq hq' e1
      subst ec
      rw [hh q q' _ hq hq']
  · change slotT hs u g q = (Sum.inr (g', c') : BRoleT Γ T nb C nR) at h
    rcases slotT_cases (C := C) hs u g q with ⟨hq, e⟩ | ⟨ρh, c, s, t, -, e⟩
    · rw [e] at h
      exact absurd h (by simp)
    · rw [e] at h
      exact absurd h (by simp)
  · change (Sum.inr (g, c) : BRoleT Γ T nb C nR) = .inl (.inl (ρ, dD p false (g', t'))) at h
    exact absurd h (by simp)
  · change (Sum.inr (g, c) : BRoleT Γ T nb C nR) = .inl (.inl (ρ, dD p true (g', t'))) at h
    exact absurd h (by simp)
  · change (Sum.inr (g, c) : BRoleT Γ T nb C nR) = slotT hs u g' q' at h
    rcases slotT_cases (C := C) hs u g' q' with ⟨hq, e⟩ | ⟨ρh, c'', s, t, -, e⟩
    · rw [e] at h
      exact absurd h (by simp)
    · rw [e] at h
      exact absurd h (by simp)
  · change (Sum.inr (g, c) : BRoleT Γ T nb C nR) = .inr (g', c') at h
    simp only [Sum.inr.injEq] at h
    rw [h]

def emT (ρ : Fin nR) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T)))
    (u : (q : Sl) → hs q = none → Fin nb) (hok : HostOKT ρ p hs u) : SRole Γ T Sl C ↪ BRoleT Γ T nb C nR :=
  ⟨posT ρ p hs u, posT_inj hp hok⟩

/-- **scalar map of a forward stage** of replica `ρ` on pair `p` (Shea's `GF`): `Y_p += X_p`, copies erased. -/
def scF (ρ : Fin nR) (p : ℕ) (x : BRoleT Γ T nb C nR → ℂ) : BRoleT Γ T nb C nR → ℂ
  | .inl (.inl (ρ', d)) =>
      if ρ' = ρ ∧ (dDecD d).1 = p ∧ (dDecD d).2.1 = true then
        x (.inl (.inl (ρ', d))) + x (.inl (.inl (ρ', dD p false (dDecD d).2.2)))
      else x (.inl (.inl (ρ', d)))
  | .inl (.inr s) => x (.inl (.inr s))
  | .inr _ => 0

/-- **scalar map of a backward stage** of replica `ρ` on pair `p` (Shea's `GB`): `X_p -= Y_p`, copies erased. -/
def scB (ρ : Fin nR) (p : ℕ) (x : BRoleT Γ T nb C nR → ℂ) : BRoleT Γ T nb C nR → ℂ
  | .inl (.inl (ρ', d)) =>
      if ρ' = ρ ∧ (dDecD d).1 = p ∧ (dDecD d).2.1 = false then
        x (.inl (.inl (ρ', d))) - x (.inl (.inl (ρ', dD p true (dDecD d).2.2)))
      else x (.inl (.inl (ρ', d)))
  | .inl (.inr s) => x (.inl (.inr s))
  | .inr _ => 0

end Roles

section Lift
variable {Γ T Sl C α : Type} {nb nR : ℕ} [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the generic lift of a hosted stage route (any scalar map `h` on the one-pair roles and any global scalar map `G`
that agrees with it through `posT` and keeps every role outside its image). -/
theorem ghliftT (ρ : Fin nR) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T)))
    (u : (q : Sl) → hs q = none → Fin nb) (hok : HostOKT ρ p hs u)
    {S0 T0 : BRoleT Γ T nb C nR → CMat α}
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {G : (BRoleT Γ T nb C nR → ℂ) → (BRoleT Γ T nb C nR → ℂ)}
    {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hSX : ∀ g t, S0 (.inl (.inl (ρ, dD p false (g,t)))) = SX g t)
    (hSY : ∀ g t, S0 (.inl (.inl (ρ, dD p true (g,t)))) = SY g t)
    (hUX : ∀ g t, T0 (.inl (.inl (ρ, dD p false (g,t)))) = UX g t)
    (hUY : ∀ g t, T0 (.inl (.inl (ρ, dD p true (g,t)))) = UY g t)
    (hSS : ∀ g q, S0 (slotT hs u g q) = SS g q) (hUS : ∀ g q, T0 (slotT hs u g q) = US g q)
    (hSC : ∀ g c, S0 (.inr (g,c)) = SC g c) (hUC : ∀ g c, T0 (.inr (g,c)) = UC g c)
    (hfix : ∀ r, r ∉ covered (emT (Γ := Γ) (C := C) ρ p hp hs u hok) → S0 r = T0 r)
    (hin : ∀ x, (G x) ∘ (emT (Γ := Γ) (C := C) ρ p hp hs u hok) = h (x ∘ (emT (Γ := Γ) (C := C) ρ p hp hs u hok)))
    (hout : ∀ x r, r ∉ covered (emT (Γ := Γ) (C := C) ρ p hp hs u hok) → G x r = x r) :
    GRoute S0 T0 G c := by
  refine GRoute.lift (emT (Γ := Γ) (C := C) ρ p hp hs u hok) (h := h) ?_ hin hout hfix
  have e1 : S0 ∘ (emT (Γ := Γ) (C := C) ρ p hp hs u hok) = mkS SX SY SS SC := by
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hSX g t
    · exact hSY g t
    · exact hSS g q
    · exact hSC g c
  have e2 : T0 ∘ (emT (Γ := Γ) (C := C) ρ p hp hs u hok) = mkS UX UY US UC := by
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact hUX g t
    · exact hUY g t
    · exact hUS g q
    · exact hUC g c
  rw [e1, e2]
  exact q

/-- the roles covered by a hosted call: the acting pair of `ρ`, the slots' roles, the copies. -/
lemma covered_emT (ρ : Fin nR) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T)))
    (u : (q : Sl) → hs q = none → Fin nb) (hok : HostOKT ρ p hs u) (r : BRoleT Γ T nb C nR) :
    r ∈ covered (emT (Γ := Γ) (C := C) ρ p hp hs u hok) ↔
      (∃ s g t, r = .inl (.inl (ρ, dD p s (g, t)))) ∨ (∃ g q, r = slotT hs u g q) ∨ (∃ g c, r = .inr (g, c)) := by
  rw [cover_iff]
  constructor
  · rintro ⟨(((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩), rfl⟩
    · exact Or.inl ⟨false, g, t, rfl⟩
    · exact Or.inl ⟨true, g, t, rfl⟩
    · exact Or.inr (Or.inl ⟨g, q, rfl⟩)
    · exact Or.inr (Or.inr ⟨g, c, rfl⟩)
  · rintro (⟨s, g, t, rfl⟩ | ⟨g, q, rfl⟩ | ⟨g, c, rfl⟩)
    · cases s
      · exact ⟨jX (g, t), rfl⟩
      · exact ⟨jY (g, t), rfl⟩
    · exact ⟨jS (g, q), rfl⟩
    · exact ⟨jC (g, c), rfl⟩

/-- `scF` agrees with `GF` through `posT`. -/
lemma scF_in (ρ : Fin nR) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T)))
    (u : (q : Sl) → hs q = none → Fin nb) (hok : HostOKT ρ p hs u) (x : BRoleT Γ T nb C nR → ℂ) :
    (scF ρ p x) ∘ (emT (Γ := Γ) (C := C) ρ p hp hs u hok) = GF (x ∘ (emT (Γ := Γ) (C := C) ρ p hp hs u hok)) := by
  funext r
  rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
  · show scF ρ p x (.inl (.inl (ρ, dD p false (g, t)))) = x (.inl (.inl (ρ, dD p false (g, t))))
    simp only [scF, dDecD_dD p hp]
    simp
  · show scF ρ p x (.inl (.inl (ρ, dD p true (g, t))))
      = x (.inl (.inl (ρ, dD p true (g, t)))) + x (.inl (.inl (ρ, dD p false (g, t))))
    simp only [scF, dDecD_dD p hp]
    simp
  · show scF ρ p x (slotT hs u g q) = x (slotT hs u g q)
    rcases slotT_cases (C := C) hs u g q with ⟨hq, e⟩ | ⟨ρh, c, s, t, hq, e⟩
    · rw [e]
      rfl
    · rw [e]
      simp only [scF, dDecD_dD (pairOf c) (pairOf_range c)]
      rw [if_neg]
      rintro ⟨rfl, h2, -⟩
      exact hok.2.2.1 q c (s, t) hq h2
  · rfl

/-- `scB` agrees with `GB` through `posT`. -/
lemma scB_in (ρ : Fin nR) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T)))
    (u : (q : Sl) → hs q = none → Fin nb) (hok : HostOKT ρ p hs u) (x : BRoleT Γ T nb C nR → ℂ) :
    (scB ρ p x) ∘ (emT (Γ := Γ) (C := C) ρ p hp hs u hok) = GB (x ∘ (emT (Γ := Γ) (C := C) ρ p hp hs u hok)) := by
  funext r
  rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
  · show scB ρ p x (.inl (.inl (ρ, dD p false (g, t))))
      = x (.inl (.inl (ρ, dD p false (g, t)))) - x (.inl (.inl (ρ, dD p true (g, t))))
    simp only [scB, dDecD_dD p hp]
    simp
  · show scB ρ p x (.inl (.inl (ρ, dD p true (g, t)))) = x (.inl (.inl (ρ, dD p true (g, t))))
    simp only [scB, dDecD_dD p hp]
    simp
  · show scB ρ p x (slotT hs u g q) = x (slotT hs u g q)
    rcases slotT_cases (C := C) hs u g q with ⟨hq, e⟩ | ⟨ρh, c, s, t, hq, e⟩
    · rw [e]
      rfl
    · rw [e]
      simp only [scB, dDecD_dD (pairOf c) (pairOf_range c)]
      rw [if_neg]
      rintro ⟨rfl, h2, -⟩
      exact hok.2.2.1 q c (s, t) hq h2
  · rfl

/-- `scF` keeps every role outside the image of `posT`. -/
lemma scF_out (ρ : Fin nR) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T)))
    (u : (q : Sl) → hs q = none → Fin nb) (hok : HostOKT ρ p hs u) (x : BRoleT Γ T nb C nR → ℂ)
    (r : BRoleT Γ T nb C nR) (hr : r ∉ covered (emT (Γ := Γ) (C := C) ρ p hp hs u hok)) : scF ρ p x r = x r := by
  rw [covered_emT] at hr
  rcases r with ((⟨ρ', d⟩|⟨g,b⟩)|⟨g,c⟩)
  · simp only [scF]
    rw [if_neg]
    rintro ⟨rfl, h2, h3⟩
    refine hr (Or.inl ⟨true, (dDecD d).2.2.1, (dDecD d).2.2.2, ?_⟩)
    rw [← h2, ← h3]
    exact congrArg (fun d => (Sum.inl (Sum.inl (ρ', d)) : BRoleT Γ T nb C nR)) (dD_dDecD d).symm
  · rfl
  · exact absurd (Or.inr (Or.inr ⟨g, c, rfl⟩)) hr

/-- `scB` keeps every role outside the image of `posT`. -/
lemma scB_out (ρ : Fin nR) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) (hs : Sl → Option (Fin nR × Fin 9 × (Bool × T)))
    (u : (q : Sl) → hs q = none → Fin nb) (hok : HostOKT ρ p hs u) (x : BRoleT Γ T nb C nR → ℂ)
    (r : BRoleT Γ T nb C nR) (hr : r ∉ covered (emT (Γ := Γ) (C := C) ρ p hp hs u hok)) : scB ρ p x r = x r := by
  rw [covered_emT] at hr
  rcases r with ((⟨ρ', d⟩|⟨g,b⟩)|⟨g,c⟩)
  · simp only [scB]
    rw [if_neg]
    rintro ⟨rfl, h2, h3⟩
    refine hr (Or.inl ⟨false, (dDecD d).2.2.1, (dDecD d).2.2.2, ?_⟩)
    rw [← h2, ← h3]
    exact congrArg (fun d => (Sum.inl (Sum.inl (ρ', d)) : BRoleT Γ T nb C nR)) (dD_dDecD d).symm
  · rfl
  · exact absurd (Or.inr (Or.inr ⟨g, c, rfl⟩)) hr

end Lift
end
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.posT_inj
#print axioms OAI.PowerSaving.XHostT.ghliftT
#print axioms OAI.PowerSaving.XHostT.scF_in
#print axioms OAI.PowerSaving.XHostT.scB_out

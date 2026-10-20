import Submission.Work.XHostT.TRoles

/-!
# (key: bridge-host-cross) Scalar maps of the CROSS-REPLICA hosted network

The calls of the `nR` replicas are interleaved in one global order; a call of replica `ρ` moves the data of `ρ` only
(its slots, hosted in idle data roles of ANY replica or on banks, keep their scalar contents).  This file holds the
scalar side of that statement, generically:

* `sfR p` / `sbR p`: bank-free run-local maps of a forward / backward stage on pair `p` (Shea's `GF` / `GB`, copies
  erased); `liftRunT_fwd` / `liftRunT_bwd`: lifted to all roles they are `scF ρ p` / `scB ρ p` (TRoles.lean);
* `liftT_route`: a route on the roles of ONE run (replica `ρ`, banks, copies) lifts to all roles when the other
  replicas' frames agree; `liftRunT_comp`, `liftRunT_id`;
* `DL` (the data outputs read only data) and `KB` (banks kept); `sweep_local`: in an interleaved sweep of lifted
  run-local maps, the data of replica `ρ` end as the composite `pcomp` of ρ's OWN maps in time order (the other
  replicas' calls never touch them, and the shared banks and copies do not matter, by `DL`); `sweep_bankT`;
* `bpullT`, `bsgnT`, `brecT`: Shea's signed exchange `brec401` on `nR` replicas.

Written by p-a3 (wht45/lever, 19 Oct 2026), on rb-a3's TRoles.lean (wht43, 14 Oct 2026), Ryan Shea's complex588 tree
(Bridge401: Nil Mamano's gen401 on Dugongue #401 / jacklightChen #377 / Lydakis #275 / DaysSky #363; engine and E8 unit
by Jacob Sussman) and DaysSky's idle-axis hosting (CrocSwap/integer-mult-bounds PR #442); prepared with assistance from
Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHostT
open Binary Matrix Finset RAM SS CB RF BR GF GX XHost

noncomputable section

section Maps
variable {Γ T C : Type} {nb nR : ℕ}

/-- the data role `(p, s, k)` of a run. -/
abbrev rD (p : ℕ) (s : Bool) (k : Γ × T) : BRun4 Γ T nb C := .inl (.inl (dD p s k))

/-- `h` acts on a run as a forward stage of pair `p` (Shea's `GF`): `Y_p += X_p`, the rest kept, copies erased. -/
structure IsFwd (p : ℕ) (h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) : Prop where
  hX : ∀ x k, h x (rD p false k) = x (rD p false k)
  hY : ∀ x k, h x (rD p true k) = x (rD p true k) + x (rD p false k)
  hO : ∀ x d, (dDecD d).1 ≠ p → h x (.inl (.inl d)) = x (.inl (.inl d))
  hS : ∀ x s, h x (.inl (.inr s)) = x (.inl (.inr s))
  hC : ∀ x c, h x (.inr c) = 0

/-- `h` acts on a run as a backward stage of pair `p` (Shea's `GB`): `X_p -= Y_p`, the rest kept, copies erased. -/
structure IsBwd (p : ℕ) (h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) : Prop where
  hX : ∀ x k, h x (rD p false k) = x (rD p false k) - x (rD p true k)
  hY : ∀ x k, h x (rD p true k) = x (rD p true k)
  hO : ∀ x d, (dDecD d).1 ≠ p → h x (.inl (.inl d)) = x (.inl (.inl d))
  hS : ∀ x s, h x (.inl (.inr s)) = x (.inl (.inr s))
  hC : ∀ x c, h x (.inr c) = 0

/-- the bank-free forward map of pair `p` on a run. -/
def sfR (p : ℕ) (x : BRun4 Γ T nb C → ℂ) : BRun4 Γ T nb C → ℂ
  | .inl (.inl d) =>
      if (dDecD d).1 = p ∧ (dDecD d).2.1 = true then x (.inl (.inl d)) + x (.inl (.inl (dD p false (dDecD d).2.2)))
      else x (.inl (.inl d))
  | .inl (.inr s) => x (.inl (.inr s))
  | .inr _ => 0

/-- the bank-free backward map of pair `p` on a run. -/
def sbR (p : ℕ) (x : BRun4 Γ T nb C → ℂ) : BRun4 Γ T nb C → ℂ
  | .inl (.inl d) =>
      if (dDecD d).1 = p ∧ (dDecD d).2.1 = false then x (.inl (.inl d)) - x (.inl (.inl (dD p true (dDecD d).2.2)))
      else x (.inl (.inl d))
  | .inl (.inr s) => x (.inl (.inr s))
  | .inr _ => 0

lemma sfR_fwd (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) : IsFwd (Γ := Γ) (T := T) (nb := nb) (C := C) p (sfR p) where
  hX x k := by
    show (if (dDecD (dD p false k)).1 = p ∧ (dDecD (dD p false k)).2.1 = true then _ else _) = _
    rw [dDecD_dD p hp]
    simp
  hY x k := by
    show (if (dDecD (dD p true k)).1 = p ∧ (dDecD (dD p true k)).2.1 = true then _ else _) = _
    rw [dDecD_dD p hp]
    simp
  hO x d h := by
    show (if (dDecD d).1 = p ∧ (dDecD d).2.1 = true then _ else _) = _
    rw [if_neg (fun e => h e.1)]
  hS x s := rfl
  hC x c := rfl

lemma sbR_bwd (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 4) : IsBwd (Γ := Γ) (T := T) (nb := nb) (C := C) p (sbR p) where
  hX x k := by
    show (if (dDecD (dD p false k)).1 = p ∧ (dDecD (dD p false k)).2.1 = false then _ else _) = _
    rw [dDecD_dD p hp]
    simp
  hY x k := by
    show (if (dDecD (dD p true k)).1 = p ∧ (dDecD (dD p true k)).2.1 = false then _ else _) = _
    rw [dDecD_dD p hp]
    simp
  hO x d h := by
    show (if (dDecD d).1 = p ∧ (dDecD d).2.1 = false then _ else _) = _
    rw [if_neg (fun e => h e.1)]
  hS x s := rfl
  hC x c := rfl

/-- a lifted forward run-local map IS `scF`. -/
lemma liftRunT_fwd (ρ : Fin nR) {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) {h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)}
    (H : IsFwd p h) : liftRunT ρ h = scF ρ p := by
  funext x r
  rcases r with ((⟨ρ', d⟩|s)|c)
  · by_cases e : ρ' = ρ
    · subst e
      obtain ⟨p', s, k, hp', rfl⟩ := dD_cases d
      have hdec := dDecD_dD (Γ := Γ) (T := T) p' hp' s k
      show (if ρ' = ρ' then h (x ∘ runPosT ρ') (.inl (.inl (dD p' s k))) else _) =
        (if ρ' = ρ' ∧ (dDecD (dD p' s k)).1 = p ∧ (dDecD (dD p' s k)).2.1 = true then _ else _)
      rw [if_pos rfl, hdec]
      by_cases e1 : p' = p
      · subst e1
        cases s
        · rw [if_neg (by simp)]
          exact H.hX _ k
        · rw [if_pos (by simp)]
          exact H.hY _ k
      · rw [if_neg (by simp [e1])]
        exact H.hO _ _ (by rw [hdec]; exact e1)
    · show (if ρ' = ρ then _ else _) = (if ρ' = ρ ∧ _ then _ else _)
      rw [if_neg e, if_neg (fun h => e h.1)]
  · exact H.hS _ s
  · exact H.hC _ c

/-- a lifted backward run-local map IS `scB`. -/
lemma liftRunT_bwd (ρ : Fin nR) {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) {h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)}
    (H : IsBwd p h) : liftRunT ρ h = scB ρ p := by
  funext x r
  rcases r with ((⟨ρ', d⟩|s)|c)
  · by_cases e : ρ' = ρ
    · subst e
      obtain ⟨p', s, k, hp', rfl⟩ := dD_cases d
      have hdec := dDecD_dD (Γ := Γ) (T := T) p' hp' s k
      show (if ρ' = ρ' then h (x ∘ runPosT ρ') (.inl (.inl (dD p' s k))) else _) =
        (if ρ' = ρ' ∧ (dDecD (dD p' s k)).1 = p ∧ (dDecD (dD p' s k)).2.1 = false then _ else _)
      rw [if_pos rfl, hdec]
      by_cases e1 : p' = p
      · subst e1
        cases s
        · rw [if_pos (by simp)]
          exact H.hX _ k
        · rw [if_neg (by simp)]
          exact H.hY _ k
      · rw [if_neg (by simp [e1])]
        exact H.hO _ _ (by rw [hdec]; exact e1)
    · show (if ρ' = ρ then _ else _) = (if ρ' = ρ ∧ _ then _ else _)
      rw [if_neg e, if_neg (fun h => e h.1)]
  · exact H.hS _ s
  · exact H.hC _ c

lemma liftRunT_id (ρ : Fin nR) : liftRunT (Γ := Γ) (T := T) (nb := nb) (C := C) ρ id = id := by
  funext x r
  rcases r with ((⟨ρ', d⟩|s)|c)
  · show (if ρ' = ρ then x (runPosT ρ (.inl (.inl d))) else _) = _
    split_ifs with e
    · subst e
      rfl
    · rfl
  · rfl
  · rfl

lemma liftRunT_runPos (ρ : Fin nR) (h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) (x : BRoleT Γ T nb C nR → ℂ) :
    liftRunT ρ h x ∘ runPosT ρ = h (x ∘ runPosT ρ) := by
  funext r
  rcases r with ((d|s)|c)
  · show (if ρ = ρ then _ else _) = _
    rw [if_pos rfl]
  · rfl
  · rfl

lemma liftRunT_comp (ρ : Fin nR) (f g : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) :
    liftRunT ρ f ∘ liftRunT ρ g = liftRunT ρ (f ∘ g) := by
  funext x r
  rcases r with ((⟨ρ', d⟩|s)|c)
  · show (if ρ' = ρ then f (liftRunT ρ g x ∘ runPosT ρ) _ else liftRunT ρ g x _) =
      (if ρ' = ρ then f (g (x ∘ runPosT ρ)) _ else _)
    split_ifs with e
    · rw [liftRunT_runPos]
    · show (if ρ' = ρ then _ else _) = _
      rw [if_neg e]
  · show f (liftRunT ρ g x ∘ runPosT ρ) _ = f (g (x ∘ runPosT ρ)) _
    rw [liftRunT_runPos]
  · show f (liftRunT ρ g x ∘ runPosT ρ) _ = f (g (x ∘ runPosT ρ)) _
    rw [liftRunT_runPos]

/-- the data outputs of `h` read only the data. -/
def DL (h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) : Prop :=
  ∀ x x', (∀ d, x (.inl (.inl d)) = x' (.inl (.inl d))) → ∀ d, h x (.inl (.inl d)) = h x' (.inl (.inl d))

/-- `h` keeps the banks. -/
def KB (h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) : Prop := ∀ x s, h x (.inl (.inr s)) = x (.inl (.inr s))

lemma DL_id : DL (Γ := Γ) (T := T) (nb := nb) (C := C) id := fun x x' h d => h d
lemma KB_id : KB (Γ := Γ) (T := T) (nb := nb) (C := C) id := fun x s => rfl

lemma DL_comp {f g : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)} (hf : DL f) (hg : DL g) : DL (f ∘ g) :=
  fun x x' h d => hf _ _ (hg x x' h) d

lemma KB_comp {f g : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)} (hf : KB f) (hg : KB g) : KB (f ∘ g) :=
  fun x s => (hf _ s).trans (hg x s)

lemma IsFwd.dl {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) {h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)} (H : IsFwd p h) :
    DL h := by
  intro x x' hx d
  obtain ⟨p', s, k, hp', rfl⟩ := dD_cases d
  by_cases e1 : p' = p
  · subst e1
    cases s
    · rw [H.hX, H.hX]
      exact hx _
    · rw [H.hY, H.hY, hx, hx]
  · have e2 : (dDecD (dD p' s k)).1 ≠ p := by rw [dDecD_dD p' hp']; exact e1
    rw [H.hO _ _ e2, H.hO _ _ e2]
    exact hx _

lemma IsBwd.dl {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) {h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)} (H : IsBwd p h) :
    DL h := by
  intro x x' hx d
  obtain ⟨p', s, k, hp', rfl⟩ := dD_cases d
  by_cases e1 : p' = p
  · subst e1
    cases s
    · rw [H.hX, H.hX, hx, hx]
    · rw [H.hY, H.hY]
      exact hx _
  · have e2 : (dDecD (dD p' s k)).1 ≠ p := by rw [dDecD_dD p' hp']; exact e1
    rw [H.hO _ _ e2, H.hO _ _ e2]
    exact hx _

/-- a gate layer `x i + k i * x (p i)` whose twin of a data role is a data role reads only data. -/
lemma DL_gsc (p : BRun4 Γ T nb C → BRun4 Γ T nb C) (k : BRun4 Γ T nb C → ℚ)
    (hp : ∀ d, ∃ d', p (.inl (.inl d)) = .inl (.inl d')) : DL (gscQ p k) := by
  intro x x' hx d
  obtain ⟨d', e⟩ := hp d
  show x _ + (k _ : ℂ) * x (p _) = x' _ + (k _ : ℂ) * x' (p _)
  rw [e, hx, hx]

/-- a gate layer with `k = 0` on the banks keeps the banks. -/
lemma KB_gsc (p : BRun4 Γ T nb C → BRun4 Γ T nb C) (k : BRun4 Γ T nb C → ℚ)
    (hk : ∀ s, k (.inl (.inr s)) = 0) : KB (gscQ p k) := by
  intro x s
  show x _ + (k _ : ℂ) * x (p _) = x _
  rw [hk]
  simp

/-- **lifting a route of ONE run** (replica `ρ`, the banks, the copies) to all roles: the other replicas keep their
frames. -/
theorem liftT_route {α : Type} [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
    [Fintype C] [DecidableEq C] (ρ : Fin nR) {S Tf : BRoleT Γ T nb C nR → CMat α}
    {h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (S ∘ emRunT ρ) (Tf ∘ emRunT ρ) h c)
    (hfix : ∀ ρ' d, ρ' ≠ ρ → S (.inl (.inl (ρ', d))) = Tf (.inl (.inl (ρ', d)))) :
    GRoute S Tf (liftRunT ρ h) c := by
  refine GRoute.lift (emRunT ρ) q (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · exact liftRunT_runPos ρ h x
  · rcases i with ((⟨ρ', d⟩|s)|c)
    · have e : ρ' ≠ ρ := fun e => hi ((cover_iff _ _).mpr ⟨.inl (.inl d), by subst e; rfl⟩)
      show (if ρ' = ρ then _ else _) = _
      rw [if_neg e]
    · exact absurd ((cover_iff _ _).mpr ⟨(Sum.inl (Sum.inr s) : BRun4 Γ T nb C), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨(Sum.inr c : BRun4 Γ T nb C), rfl⟩) hi
  · rcases i with ((⟨ρ', d⟩|s)|c)
    · have e : ρ' ≠ ρ := fun e => hi ((cover_iff _ _).mpr ⟨.inl (.inl d), by subst e; rfl⟩)
      exact hfix ρ' d e
    · exact absurd ((cover_iff _ _).mpr ⟨(Sum.inl (Sum.inr s) : BRun4 Γ T nb C), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨(Sum.inr c : BRun4 Γ T nb C), rfl⟩) hi

/-! ## Locality of an interleaved sweep -/

/-- the composite of replica `ρ`'s own run-local maps among the first `n` calls (call `i` belongs to `o i`). -/
def pcomp (o : ℕ → Fin nR) (h : ℕ → (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) (ρ : Fin nR) :
    ℕ → (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)
  | 0 => id
  | n + 1 => if o n = ρ then h n ∘ pcomp o h ρ n else pcomp o h ρ n

lemma pcomp_succ_self {o : ℕ → Fin nR} {h : ℕ → (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)} {ρ : Fin nR}
    {n : ℕ} (e : o n = ρ) : pcomp o h ρ (n + 1) = h n ∘ pcomp o h ρ n := by
  show (if o n = ρ then _ else _) = _
  rw [if_pos e]

lemma pcomp_succ_other {o : ℕ → Fin nR} {h : ℕ → (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)} {ρ : Fin nR}
    {n : ℕ} (e : o n ≠ ρ) : pcomp o h ρ (n + 1) = pcomp o h ρ n := by
  show (if o n = ρ then _ else _) = _
  rw [if_neg e]

/-- no call of `ρ` in `[a, a + m)`: the composite does not change. -/
lemma pcomp_gap {o : ℕ → Fin nR} {h : ℕ → (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)} {ρ : Fin nR} (a : ℕ) :
    ∀ m, (∀ i, a ≤ i → i < a + m → o i ≠ ρ) → pcomp o h ρ (a + m) = pcomp o h ρ a
  | 0, _ => rfl
  | m + 1, hm => by
    rw [show a + (m + 1) = (a + m) + 1 by omega, pcomp_succ_other (hm (a + m) (by omega) (by omega))]
    exact pcomp_gap a m (fun i h1 h2 => hm i h1 (by omega))

/-- **Locality of an interleaved sweep.**  When every run-local map reads only data (`DL`), the data of replica `ρ`
after the sweep of the lifted maps are those of ρ's OWN maps composed in time order. -/
theorem sweep_local {o : ℕ → Fin nR} {h : ℕ → (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)}
    (hDL : ∀ n, DL (h n)) :
    ∀ (n : ℕ) (x : BRoleT Γ T nb C nR → ℂ) (ρ : Fin nR) (d : BDat4 Γ T),
      sweepMap (fun i : Fin n => liftRunT (o i.val) (h i.val)) x (.inl (.inl (ρ, d)))
        = pcomp o h ρ n (x ∘ runPosT ρ) (.inl (.inl d))
  | 0, x, ρ, d => rfl
  | n + 1, x, ρ, d => by
    rw [sweepMap_succ, Function.comp_apply]
    have ih := sweep_local (o := o) hDL n x
    change liftRunT (o n) (h n) (sweepMap (fun i : Fin n => liftRunT (o i.val) (h i.val)) x)
      (.inl (.inl (ρ, d))) = _
    by_cases e : o n = ρ
    · rw [pcomp_succ_self e]
      subst e
      show (if o n = o n then _ else _) = _
      rw [if_pos rfl, Function.comp_apply]
      exact hDL n _ _ (fun d' => ih (o n) d') d
    · rw [pcomp_succ_other e]
      show (if ρ = o n then _ else _) = _
      rw [if_neg (fun e' => e e'.symm)]
      exact ih ρ d

/-- an interleaved sweep of lifted run-local maps that keep the banks keeps the banks. -/
theorem sweep_bankT {o : ℕ → Fin nR} {h : ℕ → (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)}
    (hKB : ∀ n, KB (h n)) (n : ℕ) (x : BRoleT Γ T nb C nR → ℂ) (s : Γ × Fin nb) :
    sweepMap (fun i : Fin n => liftRunT (o i.val) (h i.val)) x (.inl (.inr s)) = x (.inl (.inr s)) :=
  sweepMap_fix (fun r : BRoleT Γ T nb C nR => ∃ s', r = .inl (.inr s'))
    (fun i : Fin n => liftRunT (o i.val) (h i.val))
    (fun i x r hr => by
      obtain ⟨s', rfl⟩ := hr
      exact hKB i.val (x ∘ runPosT (o i.val)) s') x _ ⟨s, rfl⟩

/-! ## The final signed exchange on `nR` replicas -/

def bpullT : BRoleT Γ T nb C nR → BRoleT Γ T nb C nR :=
  mkT (fun ρ => mkD4 (fun g t => Sum.inl (Sum.inl (ρ, dqY1 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqX1 (g,t))))
      (fun g t => Sum.inl (Sum.inl (ρ, dqY2 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqX2 (g,t))))
      (fun g t => Sum.inl (Sum.inl (ρ, dqY3 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqX3 (g,t))))
      (fun g t => Sum.inl (Sum.inl (ρ, dqY4 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqX4 (g,t)))))
    (fun g b => Sum.inl (Sum.inr (g, b))) (fun g c => Sum.inr (g, c))

def bsgnT : BRoleT Γ T nb C nR → ℚ :=
  mkT (fun _ => mkD4 (fun _ _ => 1) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => -1)
    (fun _ _ => 1) (fun _ _ => -1)) (fun _ _ => 1) (fun _ _ => 1)

variable [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T] [Fintype C] [DecidableEq C]

def brecT : Matrix (BRoleT Γ T nb C nR) (BRoleT Γ T nb C nR) ℚ :=
  fun i j => if j = bpullT i then bsgnT i else 0

lemma actPoint_brecT (x : BRoleT Γ T nb C nR → ℂ) (i : BRoleT Γ T nb C nR) :
    actPoint brecT x i = (bsgnT i : ℂ) * x (bpullT i) := by
  unfold actPoint
  rw [sum_eq_single (bpullT i)]
  · simp [brecT]
  · intro j _ hj; simp [brecT, hj]
  · simp

end Maps
end
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.liftRunT_fwd
#print axioms OAI.PowerSaving.XHostT.liftRunT_bwd
#print axioms OAI.PowerSaving.XHostT.liftRunT_comp
#print axioms OAI.PowerSaving.XHostT.liftT_route
#print axioms OAI.PowerSaving.XHostT.sweep_local
#print axioms OAI.PowerSaving.XHostT.sweep_bankT
#print axioms OAI.PowerSaving.XHostT.actPoint_brecT

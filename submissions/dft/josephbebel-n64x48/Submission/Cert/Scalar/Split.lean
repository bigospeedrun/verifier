import Submission.Cert.Scalar.Checker

/-! Key-range splitting for the packed scalar checker (native-52 port of PR 209's checker).

`ScalarCheck.Spec.Run` constrains every key `k` separately, so a run on the full rows is the
"glue" of a run on the keys `k < m` and a run on the keys `k ≥ m` (shifted down by `m`).
Checking the two halves separately halves the packed word (647 instead of 1292 digits), which
halves the memory of every scalar `decide`.  Written for this port; it uses only the
definitions of `Submission/Cert/Scalar/Checker.lean` (PR 209, HalitZiyaKARTAL v7-42). -/

namespace ScalarCheck.Split
open WarpCheck CertData ScalarCheck.Spec

def loRow (m : Nat) (row : Row) : Row := row.filter (fun e => decide (e.1 < m))
def hiRow (m : Nat) (row : Row) : Row :=
  (row.filter (fun e => decide (m ≤ e.1))).map (fun e => (e.1 - m, e.2))

def mapRT (f : Row → Row) : RT → RT
  | .leaf v => .leaf (f v)
  | .node l r => .node (mapRT f l) (mapRT f r)

def glue (m : Nat) (A B : St) : St := fun r k => if k < m then A r k else B r (k - m)

theorem coef_lo (m : Nat) : ∀ (row : Row) (k : Nat), k < m → coef (loRow m row) k = coef row k
  | [], _, _ => rfl
  | e :: l, k, hk => by
    have ih := coef_lo m l k hk
    by_cases h : e.1 < m
    · have : loRow m (e :: l) = e :: loRow m l := by simp [loRow, List.filter, h]
      rw [this]; simp only [coef]; rw [ih]
    · have : loRow m (e :: l) = loRow m l := by simp [loRow, List.filter, h]
      rw [this, ih]; simp only [coef]
      have : e.1 ≠ k := by omega
      simp [this]

theorem coef_hi (m : Nat) : ∀ (row : Row) (k : Nat), m ≤ k → coef (hiRow m row) (k - m) = coef row k
  | [], _, _ => rfl
  | e :: l, k, hk => by
    have ih := coef_hi m l k hk
    by_cases h : m ≤ e.1
    · have : hiRow m (e :: l) = (e.1 - m, e.2) :: hiRow m l := by simp [hiRow, List.filter, h]
      rw [this]; simp only [coef]; rw [ih]
      by_cases he : e.1 = k
      · have : e.1 - m = k - m := by omega
        simp [he]
      · have : e.1 - m ≠ k - m := by omega
        simp [he, this]
    · have : hiRow m (e :: l) = hiRow m l := by simp [hiRow, List.filter, h]
      rw [this, ih]; simp only [coef]
      have : e.1 ≠ k := by omega
      simp [this]

theorem get_mapRT (f : Row → Row) (hf : f [] = []) :
    ∀ (R : RT) (r : Nat), Spec.get (mapRT f R) r = f (Spec.get R r)
  | .leaf v, r => by
    show (if r = 0 then f v else []) = f (if r = 0 then v else [])
    by_cases h : r = 0
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, hf]
  | .node l rr, r => by
    show (if r % 2 = 0 then Spec.get (mapRT f l) (r / 2) else Spec.get (mapRT f rr) (r / 2))
      = f (if r % 2 = 0 then Spec.get l (r / 2) else Spec.get rr (r / 2))
    by_cases h : r % 2 = 0
    · rw [if_pos h, if_pos h]; exact get_mapRT f hf l _
    · rw [if_neg h, if_neg h]; exact get_mapRT f hf rr _

theorem wf_mapRT (f : Row → Row) : ∀ (d : Nat) (R : RT), wf d (mapRT f R) → wf d R
  | 0, .leaf _, _ => trivial
  | d + 1, .node l r, h => ⟨wf_mapRT f d l h.1, wf_mapRT f d r h.2⟩
  | 0, .node _ _, h => h.elim
  | _ + 1, .leaf _, h => h.elim

theorem st_split (m : Nat) (R : RT) :
    St.of R = glue m (St.of (mapRT (loRow m) R)) (St.of (mapRT (hiRow m) R)) := by
  funext r k
  simp only [glue, St.of]
  by_cases hk : k < m
  · rw [if_pos hk, get_mapRT _ rfl, coef_lo m _ k hk]
  · rw [if_neg hk, get_mapRT _ rfl, coef_hi m _ k (by omega)]

theorem addStep_glue {q : SPw} {m t s : Nat} {co : Co} {A A' B B' : St}
    (ha : AddStep q t s co A A') (hb : AddStep q t s co B B') :
    AddStep q t s co (glue m A B) (glue m A' B') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha
  obtain ⟨_, _, _, _, g5, g6⟩ := hb
  refine ⟨h1, h2, h3, h4, fun k => ?_, fun r hr => ?_⟩
  · simp only [glue]; split
    · exact h5 k
    · exact g5 _
  · funext k; simp only [glue]; rw [h6 r hr, g6 r hr]

theorem adds_glue {q : SPw} {m : Nat} : ∀ {l : List (Nat × Nat × Co)} {A A' B B' : St},
    Adds q l A A' → Adds q l B B' → Adds q l (glue m A B) (glue m A' B')
  | _, _, _, _, _, .nil _, .nil _ => .nil _
  | _, _, _, _, _, .cons sa ra, .cons sb rb => .cons (addStep_glue sa sb) (adds_glue ra rb)

theorem step_glue {q : SPw} {m : Nat} {e : WEv} {A A' B B' : St}
    (ha : Step q e A A') (hb : Step q e B B') : Step q e (glue m A B) (glue m A' B') := by
  cases e with
  | g g => exact adds_glue ha hb
  | sc f r co =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ha
    obtain ⟨_, _, _, g4, g5⟩ := hb
    refine ⟨h1, h2, h3, fun k => ?_, fun r' hr => ?_⟩
    · simp only [glue]; split
      · exact h4 k
      · exact g4 _
    · funext k; simp only [glue]; rw [h5 r' hr, g5 r' hr]
  | w r op f0 f1 => exact ha.elim
  | za r f =>
    obtain ⟨h1, h2, h3⟩ := ha
    obtain ⟨_, g2, g3⟩ := hb
    refine ⟨h1, fun k => ?_, fun r' hr => ?_⟩
    · simp only [glue]; split
      · exact h2 k
      · exact g2 _
    · funext k; simp only [glue]; rw [h3 r' hr, g3 r' hr]
  | zf r =>
    obtain ⟨h1, h2, h3⟩ := ha
    obtain ⟨_, g2, g3⟩ := hb
    refine ⟨h1, fun k => ?_, fun r' hr => ?_⟩
    · simp only [glue]; split
      · exact h2 k
      · exact g2 _
    · funext k; simp only [glue]; rw [h3 r' hr, g3 r' hr]
  | dn r f =>
    show glue m A' B' = glue m A B
    have ea : A' = A := ha
    have eb : B' = B := hb
    rw [ea, eb]

theorem run_glue {q : SPw} {m : Nat} : ∀ {l : List WEv} {A A' B B' : St},
    Run q l A A' → Run q l B B' → Run q l (glue m A B) (glue m A' B')
  | _, _, _, _, _, .nil _, .nil _ => .nil _
  | _, _, _, _, _, .cons sa ra, .cons sb rb => .cons (step_glue sa sb) (run_glue ra rb)

/-- The full scalar reference run from the runs on the two key ranges. -/
theorem refOk_glue {q : SPw} {evs : List WEv} {R R' : RT} (m : Nat)
    (hlo : RefOk q evs (mapRT (loRow m) R) (mapRT (loRow m) R'))
    (hhi : RefOk q evs (mapRT (hiRow m) R) (mapRT (hiRow m) R')) : RefOk q evs R R' := by
  obtain ⟨w, p1, p2, p3, p4, p5, ra⟩ := hlo
  obtain ⟨_, _, _, _, _, _, rb⟩ := hhi
  refine ⟨wf_mapRT _ _ _ w, p1, p2, p3, p4, p5, ?_⟩
  rw [st_split m R, st_split m R']
  exact run_glue ra rb

end ScalarCheck.Split

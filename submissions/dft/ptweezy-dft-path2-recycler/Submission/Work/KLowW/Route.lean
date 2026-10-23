import Submission.Work.GCert.Labels.RouteRun
import Submission.Work.GFrame.Top.Api
import Submission.Work.KLowW.LabSound

/-!
# (key: p-warpchk) THE ROUTE THEOREM of an extended phase: warps interpreted as `K_G`

* `WarpSem h wt X`   **the meaning of the warps** for a stage-B frame map `X` (the hypothesis p-warpsem proves):
                     a logical operator `K a` per signed op id, group-like (`K a * K (-a) = 1`), and the frame
                     transport of every legal warp event as a FREE move: `GReach (Φ f0) (Φ f1 * K a) 0`;
* `GRouteF S T F c`  an exact route whose effect on the logical data is ANY map `F` (not only a pointwise scalar
                     map, as `GRoute`): a warp multiplies the content of one role by `K a`;
                     `GRouteF.ofG` / `toG` (every `GRoute` is one, and back for pointwise maps), `trans`;
* `eMap o K un e`    the effect of one event on the logical data (orientation `o`: `false` forward, `true` the
                     hub's dual stream: adds `s += -c t`, scales `1/q`); `esMap` of a list;
* **`RunW.route`**   a legal extended replay is, for every `X` with a `WarpSem`, an exact generalised route from the
                     frames of `S` to the frames of `S'`, effect `esMap o K un evs`, price one block per rank;
* `esMap_gates`      without warps the effect is the old one: `point (actPoint (matP un (mic cf adds)))`.

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace KLW
open SSC GXD GLab OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.CB Finset Matrix

/-- **the meaning of the warps** for the frame map `X` (see the file header) -/
structure WarpSem (h : Nat) (wt : List WOp) {α : Type} [Fintype α] [DecidableEq α] (X : BXMap (Fin h) α) where
  K : Int → CMat α
  hinv : ∀ a : Int, K a * K (-a) = 1
  htr : ∀ (a : Int) (o : WOp) (c0 c1 : Nat), a ≠ 0 → wt[a.natAbs - 1]? = some o →
    Good h c0 → Good h c1 → WTr h o a c0 c1 →
    GReach (X.Φ (lab h c0)) (X.Φ (lab h c1) * K a) (fun _ => 0)

section
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **exact generalised route with an arbitrary effect `F` on the logical data** -/
def GRouteF (S T : ρ → CMat α) (F : ∀ f, Data α ρ f → Data α ρ f) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧
    ∀ (f : ℕ) (x : Data α ρ f), gwalk f w (multiAct f S x) = multiAct f T (F f x)

namespace GRouteF
variable {S T U : ρ → CMat α} {F F' : ∀ f, Data α ρ f → Data α ρ f} {c c' : (ℕ → ℝ) → ℝ}

theorem ofG {g : (ρ → ℂ) → (ρ → ℂ)} (h : GRoute S T g c) : GRouteF S T (fun f => point f g) c := h

theorem toG {g : (ρ → ℂ) → (ρ → ℂ)} (h : GRouteF S T (fun f => point f g) c) : GRoute S T g c := h

theorem refl : GRouteF S S (fun _ x => x) (fun _ => 0) :=
  ⟨[], GWord.proper_nil _, fun _ => rfl, fun f x => rfl⟩

theorem cast (h : GRouteF S T F c) (hc : ∀ φ, c φ = c' φ) : GRouteF S T F c' := by
  obtain ⟨w, hw, hcost, hwalk⟩ := h
  exact ⟨w, hw, fun φ => (hcost φ).trans (hc φ), hwalk⟩

theorem congrF (h : GRouteF S T F c) (hF : ∀ f x, F f x = F' f x) : GRouteF S T F' c := by
  obtain ⟨w, hw, hcost, hwalk⟩ := h
  exact ⟨w, hw, hcost, fun f x => by rw [hwalk, hF]⟩

theorem trans (a : GRouteF S T F c) (b : GRouteF T U F' c') :
    GRouteF S U (fun f x => F' f (F f x)) (fun φ => c φ + c' φ) := by
  obtain ⟨p, hp, cp, ap⟩ := a
  obtain ⟨q, hq, cq, aq⟩ := b
  refine ⟨p ++ q, hp.append hq, fun φ => by rw [GWord.costR_append, cp, cq], ?_⟩
  intro f x
  rw [gwalk_append, ap, aq]

end GRouteF

/-- **a warp step**: a free move `Φ U → Φ V * K` on the role `l` multiplies its logical content by `K` -/
theorem warp_step (S : ρ → CMat α) (l : ρ) (V K : CMat α) (h : GReach (S l) (V * K) (fun _ => 0)) :
    GRouteF S (Function.update S l V) (fun f x => roleAct f l K x) (fun _ => 0) := by
  have st : GStep l (S l) (V * K) (fun _ => 0) := h ρ l
  obtain ⟨w, hw, hc, hwalk⟩ := GRoute.on_role S l (V * K) st
  refine ⟨w, hw, hc, fun f x => ?_⟩
  rw [hwalk]
  funext j
  by_cases hj : j = l
  · subst hj
    show matAct f (Function.update S j (V * K) j) (x j) = matAct f (Function.update S j V j) (roleAct f j K x j)
    rw [Function.update_self, Function.update_self]
    simp only [roleAct]
    rw [if_pos trivial, matAct_mul]
  · show matAct f (Function.update S l (V * K) j) (x j) = matAct f (Function.update S l V j) (roleAct f l K x j)
    rw [Function.update_of_ne hj, Function.update_of_ne hj]
    simp only [roleAct, if_neg hj]

/-! ## the effect of the events -/

/-- the scale gate: role `r` times `q` -/
def scD (r : ρ) (q : ℚ) : Matrix ρ ρ ℚ := Matrix.diagonal (fun j => if j = r then q else 1)

/-- the coefficient of a `Co` as a micro coefficient -/
def cfC (co : Co) : Coef := ⟨co.neg, co.num, co.den⟩

/-- the rational value of a `Co` -/
noncomputable def coQ (co : Co) : ℚ := (cfC co).val

/-- the micro adds of a gate in orientation `o` (`true`: the hub's dual, `t += c s` ↦ `s += -c t`) -/
def gm (o : Bool) (g : Gate) : List Micro := if o then (mic cfC g.adds).map swapNeg else mic cfC g.adds

/-- **the effect of one event on the logical data** -/
noncomputable def eMap (o : Bool) (K : Int → CMat α) (un : Nat → ρ) : WEv → ∀ f, Data α ρ f → Data α ρ f
  | .g g => fun f => point f (actPoint (matP un (gm o g)))
  | .sc _ r co => fun f => point f (actPoint (scD (un r) (if o then (coQ co)⁻¹ else coQ co)))
  | .w r a _ _ => fun f x => roleAct f (un r) (K a) x
  | .za r _ => fun f => point f (actPoint (scD (un r) 0))
  | .zf r => fun f => point f (actPoint (scD (un r) 0))
  | .dn _ _ => fun _ x => x

/-- the effect of a list of events (in order) -/
noncomputable def esMap (o : Bool) (K : Int → CMat α) (un : Nat → ρ) : List WEv → ∀ f, Data α ρ f → Data α ρ f
  | [] => fun _ x => x
  | e :: es => fun f x => esMap o K un es f (eMap o K un e f x)

theorem esMap_append (o : Bool) (K : Int → CMat α) (un : Nat → ρ) (l l' : List WEv) (f : ℕ)
    (x : Data α ρ f) : esMap o K un (l ++ l') f x = esMap o K un l' f (esMap o K un l f x) := by
  induction l generalizing x with
  | nil => rfl
  | cons e l ih => exact ih _

/-- **without warps the effect is the old scalar map** (forward) -/
theorem esMap_gates (K : Int → CMat α) (un : Nat → ρ) (gs : List Gate) (f : ℕ) (x : Data α ρ f) :
    esMap false K un (gs.map WEv.g) f x = point f (actPoint (matP un (mic cfC (gs.flatMap Gate.adds)))) x := by
  induction gs generalizing x with
  | nil =>
    show x = point f (actPoint (matP un [])) x
    rw [show matP un ([] : List Micro) = (1 : Matrix ρ ρ ℚ) from rfl, actPoint_one']
    rfl
  | cons g gs ih =>
    show esMap false K un (gs.map WEv.g) f (point f (actPoint (matP un (mic cfC g.adds))) x) = _
    rw [ih, ← mic_flat cfC (g :: gs), List.flatMap_cons, mic_flat cfC gs, matP_append, actPoint_mul]
    rfl

/-- **without warps the effect is the old scalar map** (backward: the transposed inverse) -/
theorem esMap_gates_b (K : Int → CMat α) (un : Nat → ρ) (gs : List Gate) (f : ℕ) (x : Data α ρ f) :
    esMap true K un (gs.map WEv.g) f x
      = point f (actPoint (matPinv un (mic cfC (gs.flatMap Gate.adds)))ᵀ) x := by
  rw [← matP_swap]
  induction gs generalizing x with
  | nil =>
    show x = point f (actPoint (matP un [])) x
    rw [show matP un ([] : List Micro) = (1 : Matrix ρ ρ ℚ) from rfl, actPoint_one']
    rfl
  | cons g gs ih =>
    show esMap true K un (gs.map WEv.g) f (point f (actPoint (matP un ((mic cfC g.adds).map swapNeg))) x) = _
    rw [ih, ← mic_flat' cfC (g :: gs), List.flatMap_cons, mic_flat' cfC gs, matP_append, actPoint_mul]
    rfl

/-! ## one event is a route -/

variable {p : GLab.Par} {emb : ρ → Nat} {un : Nat → ρ}

theorem gm_regs (o : Bool) (g : Gate) (t s : Nat) (c : Coef) (h : Micro.add t s c ∈ gm o g) :
    t ∈ g.regs ∧ s ∈ g.regs := by
  unfold gm at h
  cases o with
  | false =>
    have h' : Micro.add t s c ∈ (Gate.adds g).map (fun x => Micro.add x.1 x.2.1 (cfC x.2.2)) := h
    obtain ⟨x, hx, e⟩ := List.mem_map.mp h'
    have e' : Micro.add x.1 x.2.1 (cfC x.2.2) = Micro.add t s c := e
    injection e' with e1 e2 e3
    subst e1; subst e2
    exact adds_regs g x hx
  | true =>
    obtain ⟨m, hm, e⟩ := List.mem_map.mp h
    have hm' : m ∈ (Gate.adds g).map (fun x => Micro.add x.1 x.2.1 (cfC x.2.2)) := hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm'
    have e' : Micro.add x.2.1 x.1 (cfC x.2.2).negate = Micro.add t s c := e
    injection e' with e1 e2 e3
    subst e1; subst e2
    exact ⟨(adds_regs g x hx).2, (adds_regs g x hx).1⟩

theorem lf_set (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (S : Trie) (hS : S.wf p.d) (r f : Nat)
    (hr : r < p.n) :
    Lf p emb X (S.set r f) = Function.update (Lf p emb X S) (un r) (X.Φ (lab p.h (p.tab.get f))) := by
  have hrd : r < 2 ^ p.d := lt_of_lt_of_le hr C.hn
  funext q
  by_cases hq : q = un r
  · subst hq
    rw [Function.update_self]
    show X.Φ (lab p.h (p.tab.get ((S.set r f).get (emb (un r))))) = _
    rw [C.hin r hr, Trie.get_set p.d S hS r r f hrd hrd, if_pos rfl]
  · rw [Function.update_of_ne hq]
    have hne : emb q ≠ r := fun h => hq (by rw [← C.hun q, h])
    show X.Φ (lab p.h (p.tab.get ((S.set r f).get (emb q)))) = X.Φ (lab p.h (p.tab.get (S.get (emb q))))
    rw [Trie.get_set p.d S hS r (emb q) f hrd (lt_of_lt_of_le (C.hlt q) C.hn), if_neg hne]

theorem scD_gate (L : ρ → CMat α) (r : ρ) (q : ℚ) : GRoute L L (actPoint (scD r q)) (fun _ => 0) :=
  GRoute.gate _ L L (fun i j hij => by
    by_cases e : i = j
    · rw [e]
    · exact absurd (by simp [scD, Matrix.diagonal_apply_ne _ e]) hij)

/-- **one event is a route** -/
theorem eroute (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α) {wt : List WOp}
    (W : WarpSem p.h wt X) (o : Bool) (e : WEv) (S : Trie) (hS : S.wf p.d) (ok : eOk p wt S e) :
    GRouteF (Lf p emb X S) (Lf p emb X (eOut S e)) (eMap o W.K un e) (fun φ => rcost φ (eRanks p S e)) ∧
      (eOut S e).wf p.d := by
  cases e with
  | g g =>
    obtain ⟨a, hS1⟩ := groute C X hα (gm o) (fun g t s c h => gm_regs o g t s c h) g S hS ok
    exact ⟨GRouteF.ofG a, hS1⟩
  | sc f r co =>
    obtain ⟨a, hS1⟩ := groute C X hα (fun _ => []) (fun g t s c h => absurd h List.not_mem_nil)
      (.out f r [] []) S hS ok
    have b := scD_gate (Lf p emb X (gOut S (.out f r [] []))) (un r) (if o then (coQ co)⁻¹ else coQ co)
    refine ⟨((GRouteF.ofG a).trans (GRouteF.ofG b)).congrF (fun f' x => ?_) |>.cast (fun φ => add_zero _), hS1⟩
    show point f' (actPoint (scD (un r) _)) (point f' (actPoint (matP un [])) x) = _
    rw [show matP un ([] : List Micro) = (1 : Matrix ρ ρ ℚ) from rfl, actPoint_one']
    rfl
  | w r a f0 f1 =>
    obtain ⟨hr, h0, ha, ob, hget, htr⟩ := ok
    have G0 := tabK_good p.h p.tab C.hT f0
    have G1 := tabK_good p.h p.tab C.hT f1
    have R := W.htr a ob _ _ ha hget G0 G1 htr
    have hl : Lf p emb X S (un r) = X.Φ (lab p.h (p.tab.get f0)) := by
      show X.Φ (lab p.h (p.tab.get (S.get (emb (un r))))) = _
      rw [C.hin r hr, h0]
    rw [← hl] at R
    have st := warp_step (Lf p emb X S) (un r) _ _ R
    rw [← lf_set C X S hS r f1 hr] at st
    exact ⟨st.cast (fun φ => (rcost_nil φ).symm), Trie.wf_set p.d S hS r f1⟩
  | za r f =>
    refine ⟨?_, Trie.wf_set p.d S hS r f⟩
    have g : GRoute (Lf p emb X S) (Lf p emb X (S.set r f)) (actPoint (scD (un r) 0)) (fun _ => 0) :=
      GRoute.gate _ _ _ (fun i j hij => by
        by_cases e : i = j
        · subst e
          have hi : i ≠ un r := fun h => hij (by subst h; simp [scD])
          rw [lf_set C X S hS r f ok, Function.update_of_ne hi]
        · exact absurd (by simp [scD, Matrix.diagonal_apply_ne _ e]) hij)
    exact (GRouteF.ofG g).cast (fun φ => (rcost_nil φ).symm)
  | zf r =>
    exact ⟨(GRouteF.ofG (scD_gate (Lf p emb X S) (un r) 0)).cast (fun φ => (rcost_nil φ).symm), hS⟩
  | dn r f =>
    obtain ⟨hr, hd, hsub⟩ := ok
    have gc := tabK_good p.h p.tab C.hT (S.get r)
    have gf := tabK_good p.h p.tab C.hT f
    have dU : (lab p.h (p.tab.get (S.get r))).dim = cdim (p.tab.get (S.get r)) := lab_dim gc
    have dV : (lab p.h (p.tab.get f)).dim = cdim (p.tab.get f) := lab_dim gf
    have hUle : (lab p.h (p.tab.get (S.get r))).dim ≤ p.h := by
      have := Finset.card_le_univ (lab p.h (p.tab.get (S.get r))).s
      rw [Fintype.card_fin] at this
      exact this
    have mv : SMv (Fintype.card α) (lab p.h (p.tab.get (S.get r))) (lab p.h (p.tab.get f))
        [(lab p.h (p.tab.get (S.get r))).dim - (lab p.h (p.tab.get f)).dim] :=
      SMv.of_sup _ _ hsub (by rw [dU, dV]; exact hd) (by omega)
    have st := (X.fmv mv).step (un r)
    have b := GRoute.on_role (Lf p emb X S) (un r) (X.Φ (lab p.h (p.tab.get f)))
      (c := fun φ => rcost φ [(lab p.h (p.tab.get (S.get r))).dim - (lab p.h (p.tab.get f)).dim])
      (by
        show GStep (un r) (X.Φ (lab p.h (p.tab.get (S.get (emb (un r)))))) _ _
        rw [C.hin r hr]; exact st)
    rw [← lf_set C X S hS r f hr] at b
    refine ⟨(GRouteF.ofG b).cast (fun φ => ?_), Trie.wf_set p.d S hS r f⟩
    show rcost φ [(lab p.h (p.tab.get (S.get r))).dim - (lab p.h (p.tab.get f)).dim]
      = rcost φ [cdim (p.tab.get (S.get r)) - cdim (p.tab.get f)]
    rw [dU, dV]

/-- **THE ROUTE THEOREM of a legal extended replay** (either orientation, warps interpreted by `W`) -/
theorem RunW.route (C : Ctx p emb un) (X : BXMap (Fin p.h) α) (hα : p.h < Fintype.card α) {wt : List WOp}
    (W : WarpSem p.h wt X) (o : Bool) {S S' : Trie} {evs : List WEv} {rs : List Nat}
    (R : RunW p wt S evs S' rs) (hS : S.wf p.d) :
    GRouteF (Lf p emb X S) (Lf p emb X S') (esMap o W.K un evs) (fun φ => rcost φ rs) ∧ S'.wf p.d := by
  obtain ⟨ok, rfl, rfl⟩ := R
  have key : ∀ (es : List WEv) (S : Trie), S.wf p.d → esOk p wt S es →
      GRouteF (Lf p emb X S) (Lf p emb X (esOut S es)) (esMap o W.K un es) (fun φ => rcost φ (esRanks p S es)) ∧
        (esOut S es).wf p.d := by
    intro es
    induction es with
    | nil => intro S hS _; exact ⟨GRouteF.refl.cast (fun φ => (rcost_nil φ).symm), hS⟩
    | cons e es ih =>
      intro S hS ok
      obtain ⟨a, hS1⟩ := eroute C X hα W o e S hS ok.1
      obtain ⟨b, hS2⟩ := ih (eOut S e) hS1 ok.2
      exact ⟨(a.trans b).cast (fun φ => (rcost_append φ _ _).symm), hS2⟩
  exact key evs S hS ok

end
end KLW

#print axioms KLW.warp_step
#print axioms KLW.eroute
#print axioms KLW.RunW.route
#print axioms KLW.esMap_gates
#print axioms KLW.esMap_gates_b

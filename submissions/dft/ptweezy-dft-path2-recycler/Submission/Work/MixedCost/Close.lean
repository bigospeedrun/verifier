import Submission.OAI.Computability.FourierTransform.ProgramConstruction

/-!
# Mixed engine, cost part 1: closing a recursion over arbitrary descriptors

(agent rb-r3cost, 14 Oct 2026.)  `Work/Block/Recursion.lean` (`rec_bodyB` / `recurse_runB`) closes
ONE recursion whose descriptor is an order `k` and whose calls are "rank `rk` blocks at order
`rk*(k/u)`".  The lockstep engine of Theorem 1G needs several kinds of call in one handler
(top jobs `Do(n,B)`, class calls `Process(s)`, exit calls, rest calls), so here the same closing
argument is proved once for ANY descriptor type `D`:

* `GDesc enc out Kid`  the bank index of an open body: a descriptor `d`, a handler `use`, call
                       costs `tau`, a peak, and the contract that `use` answers every call
                       `Kid d c` that the body may make;
* `gfunds enc out Kid bnd`  its bank (word driver `bnd d`);
* `recurse_inv`        from an open body with local work `loc d` (a big-O constant is free) and
                       call charge `charge d tau` (exact, no constant), and a cost function with
                       `loc d + 1 + charge d cost ≤ cost d` on every descriptor satisfying an
                       invariant `Inv` that calls preserve, ONE closed program whose work is
                       `O(cost d)` on every family of such descriptors;
* `recurse_gen`        the same with no invariant;
* `recurse_list(_inv)` the usual charge: the calls are listed, `charge d tau = ∑ c ∈ kids d, tau c`.

Every call is charged in OpenAI's RAM: the handler is `depthRun` (one `pay 1` per level, the
level recorded in the peak), the body's calls are `Code.call` (charged by the handler's bill),
and the fuel is computed by the program itself from the input.  Nothing upstream changes.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.MCost
open PowerSaving.RAM Ty

noncomputable section

universe U V

/-- A program producing the blank value of any type (used as the never-reached base case of
`descend`). -/
def blankCode {m : Bool} {r : Port} : (s t : Ty) → Code m r s t
  | _, .w => .atom (.lit 0)
  | _, .c cl => .atom (.cz cl)
  | s, Ty.p x y => .fork (blankCode s x) (blankCode s y)
  | s, Ty.a x => .tab (.atom (.lit 0)) (blankCode (Ty.p s Ty.w) x)

section
variable {D : Type V} {s t : Ty}

/-- Bank index of an open recursive body over descriptors `D`.  `Kid d c` = the body of `d` may
call the handler on `enc c`; the handler answers such calls with `out c` in `tau c` work. -/
structure GDesc (enc : D → T s) (out : D → T t) (Kid : D → D → Prop) where
  d : D
  use : Handler (some (s,t))
  tau : D → ℕ
  peak : ℕ
  works : ∀ c, Kid d c → (use (enc c)).OK (out c) (tau c) peak

/-- The bank of the open body: word driver `bnd`, handler and peak from the index. -/
def gfunds (enc : D → T s) (out : D → T t) (Kid : D → D → Prop) (bnd : D → ℕ) :
    Bank (some (s,t)) (GDesc enc out Kid) :=
  ⟨fun i => bnd i.d, GDesc.peak, GDesc.use⟩

/-- **Generic closing of a recursion, with an invariant (cost accounting).**

Hypotheses:
* `hbody`: ONE open body; on descriptor `d` with any handler that answers the calls `Kid d c`
  in `tau c`, it returns `out d` with work `C*(loc d+1) + charge d tau`;
* calls preserve `Inv`, go down in `rank` and do not grow the word driver `bnd`;
* `charge d` commutes with constant factors (true for any sum of call costs);
* on `Inv` descriptors the cost function satisfies `loc d + 1 + charge d cost ≤ cost d`;
* the program can compute a fuel `fuel d > rank d`, polynomial in `bnd d`, within `O(cost d)`.

Conclusion: one closed program with work `O(cost d)` on every family of `Inv` descriptors. -/
theorem recurse_inv (m : Bool) (enc : D → T s) (out : D → T t) (Kid : D → D → Prop)
    (Inv : D → Prop) (bnd loc rank fuel cost : D → ℕ) (charge : D → (D → ℕ) → ℕ)
    (hbody : Able m (gfunds enc out Kid bnd) s t (fun i => enc i.d) (fun i => out i.d)
      (fun i => loc i.d) (fun i => charge i.d i.tau))
    (hinv : ∀ d c, Inv d → Kid d c → Inv c)
    (hrk : ∀ d c, Inv d → Kid d c → rank c < rank d)
    (hbd : ∀ d c, Inv d → Kid d c → bnd c ≤ bnd d)
    (hhom : ∀ d, Inv d → ∀ (K : ℕ) (f : D → ℕ), charge d (fun c => K * f c) ≤ K * charge d f)
    (hcost : ∀ d, Inv d → loc d + 1 + charge d cost ≤ cost d)
    (hfuel : Can m (fun d : {d // Inv d} => bnd d.1) s Ty.w (fun d => enc d.1)
      (fun d => fuel d.1) (fun d => cost d.1))
    (hrf : ∀ d, Inv d → rank d < fuel d)
    (hfs : Small (fun d : {d // Inv d} => bnd d.1) (fun d => fuel d.1))
    {ι : Type U} (dd : ι → D) (hdd : ∀ i, Inv (dd i)) :
    Can m (fun i => bnd (dd i)) s t (fun i => enc (dd i)) (fun i => out (dd i))
      (fun i => cost (dd i)) := by
  obtain ⟨body,C,dg,hc⟩ := hbody
  let c := C+1
  let base : Prog m s t := blankCode s t
  let fn := depthRun (base.run ()) body.run
  let P (b : ℕ) := (b+2)^(dg+1)
  have h (n : ℕ) (d : D) (hI : Inv d) (hd : rank d < n) :
      (fn n (enc d)).OK (out d) (c * cost d) (max (P (bnd d)) n) := by
    induction n generalizing d with
    | zero => omega
    | succ n ih =>
      let peak := max (P (bnd d)) (n+1)
      let tau (x : D) := c * cost x
      have pp (x : D) (hx : Kid d x) : (fn n (enc x)).OK (out x) (tau x) peak := by
        have hr := hrk d x hI hx
        have he := ih x (hinv d x hI hx) (by omega)
        apply he.mono le_rfl
        have hb : P (bnd x) ≤ P (bnd d) := by
          dsimp [P]; gcongr; exact hbd d x hI hx
        exact max_le_max hb (by omega)
      let i : GDesc enc out Kid := ⟨d, fn n, tau, peak, pp⟩
      have ht := hc i
      have H := ht.pay (t:=1) (z:=n+1) (le_trans
        (le_max_right (P (bnd d)) (n+1))
        (show peak ≤ (gfunds enc out Kid bnd).cap dg i from le_max_right _ _))
      apply H.mono
      · change C*(loc d+1) + charge d tau + 1 ≤ c * cost d
        have h1 : charge d tau ≤ c * charge d cost := hhom d hI c cost
        have h2 := hcost d hI
        have h3 : c * (loc d + 1 + charge d cost) ≤ c * cost d := Nat.mul_le_mul_left c h2
        have h4 : C*(loc d+1) + 1 ≤ c * (loc d + 1) := by
          dsimp [c]; rw [Nat.add_mul, one_mul]; omega
        rw [Nat.mul_add c] at h3
        omega
      · change max _ peak ≤ peak
        apply max_le _ le_rfl
        exact (Small.pow_mono_degree (bnd d) (show dg ≤ dg+1 by omega)).trans
          (le_max_left _ _)
  obtain ⟨e,he⟩ := hfs
  let D' := {d // Inv d}
  -- the closed program on all `Inv` descriptors
  let X1 (d : D') : Ty.T (Ty.p Ty.w s) := (fuel d.1, enc d.1)
  have L : Can m (fun d : D' => bnd d.1) (Ty.p Ty.w s) t X1 (fun d => out d.1)
      (fun d => cost d.1) := by
    refine ⟨.descend base body, c+1, dg+1+e, fun d => ?_⟩
    have hh := h (fuel d.1) d.1 d.2 (hrf d.1 d.2)
    have H := hh.pay (t:=1) (z:=fuel d.1) (le_max_right ..)
    apply H.mono
    · change c * cost d.1 + 1 ≤ (c+1)*(cost d.1+1) + 0
      nlinarith
    · unfold Bank.cap
      refine le_trans ?_ (le_max_left _ _)
      change max (P (bnd d.1)) (fuel d.1) ≤ (bnd d.1+2)^(dg+1+e)
      have h1 : P (bnd d.1) ≤ (bnd d.1+2)^(dg+1+e) :=
        Small.pow_mono_degree _ (by omega)
      have h2 : fuel d.1 ≤ (bnd d.1+2)^(dg+1+e) :=
        (he d).trans (Small.pow_mono_degree _ (by omega))
      exact max_le h1 h2
  have HE : Can m (fun d : D' => bnd d.1) s (Ty.p Ty.w s) (fun d => enc d.1) X1
      (fun d => cost d.1) := Can.pair hfuel Can.id
  exact Can.reindex (Can.then_do HE L) (fun i => (⟨dd i, hdd i⟩ : D'))

/-- **Generic closing of a recursion (no invariant).** -/
theorem recurse_gen (m : Bool) (enc : D → T s) (out : D → T t) (Kid : D → D → Prop)
    (bnd loc rank fuel cost : D → ℕ) (charge : D → (D → ℕ) → ℕ)
    (hbody : Able m (gfunds enc out Kid bnd) s t (fun i => enc i.d) (fun i => out i.d)
      (fun i => loc i.d) (fun i => charge i.d i.tau))
    (hrk : ∀ d c, Kid d c → rank c < rank d)
    (hbd : ∀ d c, Kid d c → bnd c ≤ bnd d)
    (hhom : ∀ d (K : ℕ) (f : D → ℕ), charge d (fun c => K * f c) ≤ K * charge d f)
    (hcost : ∀ d, loc d + 1 + charge d cost ≤ cost d)
    (hfuel : Can m bnd s Ty.w enc fuel cost)
    (hrf : ∀ d, rank d < fuel d) (hfs : Small bnd fuel)
    {ι : Type U} (dd : ι → D) :
    Can m (fun i => bnd (dd i)) s t (fun i => enc (dd i)) (fun i => out (dd i))
      (fun i => cost (dd i)) :=
  recurse_inv m enc out Kid (fun _ => True) bnd loc rank fuel cost charge hbody
    (fun _ _ _ _ => trivial) (fun d c _ h => hrk d c h) (fun d c _ h => hbd d c h)
    (fun d _ => hhom d) (fun d _ => hcost d)
    (Can.reindex hfuel (fun d : {d : D // True} => d.1)) (fun d _ => hrf d)
    (Small.reindex hfs (fun d : {d : D // True} => d.1)) dd (fun _ => trivial)

end

/-! ## Charges built from lists of calls

The usual charge: the body makes the calls listed in `kids d` (with multiplicity, e.g.
`List.replicate λ root ++ rests`), so `charge d tau = ((kids d).map tau).sum`. -/

section
variable {D : Type V}

/-- Charge of a body that makes exactly the calls `kids d`. -/
def listCharge (kids : D → List D) (d : D) (tau : D → ℕ) : ℕ := ((kids d).map tau).sum

theorem list_sum_map_mono (l : List D) (f g : D → ℕ) (h : ∀ c, c ∈ l → f c ≤ g c) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih (fun c hc => h c (by simp [hc])))

theorem list_sum_map_mul (l : List D) (K : ℕ) (f : D → ℕ) :
    (l.map (fun c => K * f c)).sum = K * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem listCharge_mono (kids : D → List D) (d : D) (f g : D → ℕ)
    (h : ∀ c, c ∈ kids d → f c ≤ g c) : listCharge kids d f ≤ listCharge kids d g :=
  list_sum_map_mono _ f g h

theorem listCharge_hom (kids : D → List D) (d : D) (K : ℕ) (f : D → ℕ) :
    listCharge kids d (fun c => K * f c) ≤ K * listCharge kids d f :=
  le_of_eq (list_sum_map_mul _ K f)

/-- `recurse_inv` for a body that makes the calls `kids d`. -/
theorem recurse_list_inv {s t : Ty} (m : Bool) (enc : D → T s) (out : D → T t)
    (kids : D → List D) (Inv : D → Prop) (bnd loc rank fuel cost : D → ℕ)
    (hbody : Able m (gfunds enc out (fun d c => c ∈ kids d) bnd) s t (fun i => enc i.d)
      (fun i => out i.d) (fun i => loc i.d) (fun i => listCharge kids i.d i.tau))
    (hinv : ∀ d c, Inv d → c ∈ kids d → Inv c)
    (hrk : ∀ d c, Inv d → c ∈ kids d → rank c < rank d)
    (hbd : ∀ d c, Inv d → c ∈ kids d → bnd c ≤ bnd d)
    (hcost : ∀ d, Inv d → loc d + 1 + ((kids d).map cost).sum ≤ cost d)
    (hfuel : Can m (fun d : {d // Inv d} => bnd d.1) s Ty.w (fun d => enc d.1)
      (fun d => fuel d.1) (fun d => cost d.1))
    (hrf : ∀ d, Inv d → rank d < fuel d)
    (hfs : Small (fun d : {d // Inv d} => bnd d.1) (fun d => fuel d.1))
    {ι : Type U} (dd : ι → D) (hdd : ∀ i, Inv (dd i)) :
    Can m (fun i => bnd (dd i)) s t (fun i => enc (dd i)) (fun i => out (dd i))
      (fun i => cost (dd i)) :=
  recurse_inv m enc out (fun d c => c ∈ kids d) Inv bnd loc rank fuel cost (listCharge kids)
    hbody hinv hrk hbd (fun d _ => listCharge_hom kids d) hcost hfuel hrf hfs dd hdd

/-- `recurse_gen` for a body that makes the calls `kids d`. -/
theorem recurse_list {s t : Ty} (m : Bool) (enc : D → T s) (out : D → T t) (kids : D → List D)
    (bnd loc rank fuel cost : D → ℕ)
    (hbody : Able m (gfunds enc out (fun d c => c ∈ kids d) bnd) s t (fun i => enc i.d)
      (fun i => out i.d) (fun i => loc i.d) (fun i => listCharge kids i.d i.tau))
    (hrk : ∀ d c, c ∈ kids d → rank c < rank d)
    (hbd : ∀ d c, c ∈ kids d → bnd c ≤ bnd d)
    (hcost : ∀ d, loc d + 1 + ((kids d).map cost).sum ≤ cost d)
    (hfuel : Can m bnd s Ty.w enc fuel cost)
    (hrf : ∀ d, rank d < fuel d) (hfs : Small bnd fuel)
    {ι : Type U} (dd : ι → D) :
    Can m (fun i => bnd (dd i)) s t (fun i => enc (dd i)) (fun i => out (dd i))
      (fun i => cost (dd i)) :=
  recurse_gen m enc out (fun d c => c ∈ kids d) bnd loc rank fuel cost (listCharge kids) hbody
    hrk hbd (listCharge_hom kids) hcost hfuel hrf hfs dd

/-- A body whose charge is at most the listed calls (e.g. a loop of `λ` root calls, then the rest
calls) can be weakened to the exact list charge. -/
theorem body_to_list {s t : Ty} {m : Bool} {enc : D → T s} {out : D → T t} {Kid : D → D → Prop}
    {bnd loc : D → ℕ} (kids : D → List D) {Z : GDesc enc out Kid → ℕ}
    (h : Able m (gfunds enc out Kid bnd) s t (fun i => enc i.d) (fun i => out i.d)
      (fun i => loc i.d) Z)
    (hZ : ∀ i, Z i ≤ listCharge kids i.d i.tau) :
    Able m (gfunds enc out Kid bnd) s t (fun i => enc i.d) (fun i => out i.d)
      (fun i => loc i.d) (fun i => listCharge kids i.d i.tau) :=
  h.mono (fun _ => le_rfl) hZ

end

end
end PowerSaving.MCost
end OAI

#print axioms OAI.PowerSaving.MCost.recurse_inv
#print axioms OAI.PowerSaving.MCost.recurse_gen
#print axioms OAI.PowerSaving.MCost.recurse_list_inv
#print axioms OAI.PowerSaving.MCost.recurse_list

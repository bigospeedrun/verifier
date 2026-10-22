import Submission.Work.MixedCost.Bill
import Submission.Work.MixedCost.Close

/-!
# Mixed engine, cost part 3: the bill wired into the recursion closer

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)

`mixed_close`: ONE open body of the mixed engine over any descriptor type `D` (the program may
carry extra data: parent multiplier, layouts, the path), whose descriptors have shapes
(`shape : D → Shape`), which makes exactly the calls `kidsS` of its shape and does local work
`O(locS)` of its shape, closes into ONE program whose work is `O(costS (shape d))` on every family
of reachable descriptors, for any per-vector cost `J` with the job recurrence `JobRec`
(e.g. `allotM`, `allotM_jobRec`).  Everything is charged in OpenAI's RAM (`recurse_inv`).
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.MCost
open PowerSaving.RAM PowerSaving.MX Ty

universe U V

section
variable {D : Type V}

/-- The charge of a body that makes the calls `kidsD d` (with multiplicity). -/
def msCharge (kidsD : D → Multiset D) (d : D) (tau : D → ℕ) : ℕ := ((kidsD d).map tau).sum

theorem msCharge_hom (kidsD : D → Multiset D) (d : D) (K : ℕ) (f : D → ℕ) :
    msCharge kidsD d (fun c => K * f c) ≤ K * msCharge kidsD d f :=
  le_of_eq Multiset.sum_map_mul_left

/-- **The mixed engine closes** (cost accounting of R3 against R1/R2). -/
theorem mixed_close (R : Rule) {n0 : ℕ} (hn0 : R.m ≤ n0) {J : ℕ → ℕ} (hJ : R.JobRec n0 J)
    (m : Bool) {s t : Ty} (enc : D → T s) (out : D → T t) (shape : D → Shape)
    (kidsD : D → Multiset D) (bnd loc fuel : D → ℕ)
    (hbody : Able m (gfunds enc out (fun d c => c ∈ kidsD d) bnd) s t (fun i => enc i.d)
      (fun i => out i.d) (fun i => loc i.d) (fun i => ((kidsD i.d).map i.tau).sum))
    (hloc : Dom (fun d => R.locS n0 (shape d)) loc)
    (hkids : ∀ d, R.InvS (shape d) → (kidsD d).map shape = R.kidsS n0 (shape d))
    (hbd : ∀ d c, R.InvS (shape d) → c ∈ kidsD d → bnd c ≤ bnd d)
    (hfuel : Can m (fun d : {d // R.InvS (shape d)} => bnd d.1) s Ty.w (fun d => enc d.1)
      (fun d => fuel d.1) (fun d => R.costS n0 J (shape d.1)))
    (hrf : ∀ d, R.InvS (shape d) → (shape d).rank < fuel d)
    (hfs : Small (fun d : {d // R.InvS (shape d)} => bnd d.1) (fun d => fuel d.1))
    {ι : Type U} (dd : ι → D) (hdd : ∀ i, R.InvS (shape (dd i))) :
    Can m (fun i => bnd (dd i)) s t (fun i => enc (dd i)) (fun i => out (dd i))
      (fun i => R.costS n0 J (shape (dd i))) := by
  -- the body's local work, measured by `locS` of the shape
  have hbody' : Able m (gfunds enc out (fun d c => c ∈ kidsD d) bnd) s t (fun i => enc i.d)
      (fun i => out i.d) (fun i => R.locS n0 (shape i.d)) (fun i => msCharge kidsD i.d i.tau) := by
    refine hbody.weaken ?_ (fun _ => le_rfl)
    obtain ⟨C, hC⟩ := hloc
    exact ⟨C, fun i => hC i.d⟩
  have hmem : ∀ d c, c ∈ kidsD d → shape c ∈ (kidsD d).map shape :=
    fun d c hc => Multiset.mem_map_of_mem shape hc
  refine recurse_inv m enc out (fun d c => c ∈ kidsD d) (fun d => R.InvS (shape d)) bnd
    (fun d => R.locS n0 (shape d)) (fun d => (shape d).rank) fuel (fun d => R.costS n0 J (shape d))
    (msCharge kidsD) hbody' ?_ ?_ hbd (fun d _ => msCharge_hom kidsD d) ?_ hfuel hrf hfs dd hdd
  · intro d c hd hc
    have h := hmem d c hc
    rw [hkids d hd] at h
    exact R.kids_inv hn0 hd h
  · intro d c hd hc
    have h := hmem d c hc
    rw [hkids d hd] at h
    exact R.kids_rank hd h
  · intro d hd
    have h := R.bill hn0 hJ (shape d)
    rw [← hkids d hd, Multiset.map_map] at h
    exact h

/-- The same when the descriptors ARE the shapes. -/
theorem mixed_close_shape (R : Rule) {n0 : ℕ} (hn0 : R.m ≤ n0) {J : ℕ → ℕ} (hJ : R.JobRec n0 J)
    (m : Bool) {s t : Ty} (enc : Shape → T s) (out : Shape → T t) (bnd loc fuel : Shape → ℕ)
    (hbody : Able m (gfunds enc out (fun d c => c ∈ R.kidsS n0 d) bnd) s t (fun i => enc i.d)
      (fun i => out i.d) (fun i => loc i.d) (fun i => ((R.kidsS n0 i.d).map i.tau).sum))
    (hloc : Dom (fun d => R.locS n0 d) loc)
    (hbd : ∀ d c, R.InvS d → c ∈ R.kidsS n0 d → bnd c ≤ bnd d)
    (hfuel : Can m (fun d : {d // R.InvS d} => bnd d.1) s Ty.w (fun d => enc d.1)
      (fun d => fuel d.1) (fun d => R.costS n0 J d.1))
    (hrf : ∀ d, R.InvS d → d.rank < fuel d)
    (hfs : Small (fun d : {d // R.InvS d} => bnd d.1) (fun d => fuel d.1))
    {ι : Type U} (dd : ι → Shape) (hdd : ∀ i, R.InvS (dd i)) :
    Can m (fun i => bnd (dd i)) s t (fun i => enc (dd i)) (fun i => out (dd i))
      (fun i => R.costS n0 J (dd i)) :=
  mixed_close R hn0 hJ m enc out id (R.kidsS n0) bnd loc fuel hbody hloc
    (fun d _ => Multiset.map_id _) hbd hfuel hrf hfs dd hdd

end

end PowerSaving.MCost
end OAI

#print axioms OAI.PowerSaving.MCost.mixed_close
#print axioms OAI.PowerSaving.MCost.mixed_close_shape

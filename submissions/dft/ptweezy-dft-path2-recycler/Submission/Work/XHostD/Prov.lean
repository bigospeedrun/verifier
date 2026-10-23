import Submission.Work.Gauge.Defs
import Submission.Work.XHostD.FramesK

/-!
# XHostD.Prov: a family of provider words, a dispatch table, cost summed per call

The hub's T74 supplier (CrocSwap/integer-mult-bounds #1839, Jeremy Kothe, on the #1672 T74 words of Rohan Arun,
mdumitrean, Jeremy Kothe and LeverRank) runs each of its 666 calls with ONE of two provider words, `extra` (417 calls)
or `gauge44` (249 calls).  In our lowering the two words have the same target vectors and the same slots; they differ in
one frame (frames[432]), which is the entrance frame of slots 403, 405, 406, 407 (residual 5 in `extra`, 4 in
`gauge44`), and in their gate lists.  So a dispatched network needs:

* one invocation per call, `D.call disp c := D.inv (disp c)`, all with the SAME `tv` (definitionally: `retagTv`), so
  every frame condition of the hosted network that mentions `tv` is unchanged;
* the entrance labels (and so the residuals `D.res i q = |H| - dim (ent q)`) of the call's own provider;
* the price summed per call: `∑ c, (D.call disp c).cost φ = ∑ i, nCalls disp i * (D.P i).cost φ` (`callCost_sum`).

`ProvF ι` is any finite family (`ι = Fin 2` for the hub's dispatch, `Prov2.mk'`).  Written by lg-a2a4 (wht43, 14 Oct
2026); prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace XHostD
open Binary Matrix Finset GX
noncomputable section

section Retag
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- an invocation with its target vectors replaced by an EQUAL family (so `(retagTv J tv h).tv = tv` by `rfl`). -/
def retagTv (J : GInvE H T Sl C) (tv : T → Space H) (h : J.tv = tv) : GInvE H T Sl C where
  tv := tv
  hunit := by subst h; exact J.hunit
  hgap := by subst h; exact J.hgap
  cost := J.cost
  ent := J.ent
  fwd := by subst h; exact J.fwd
  bwd := by subst h; exact J.bwd

lemma retagTv_tv (J : GInvE H T Sl C) (tv : T → Space H) (h : J.tv = tv) : (retagTv J tv h).tv = tv := rfl
lemma retagTv_ent (J : GInvE H T Sl C) (tv : T → Space H) (h : J.tv = tv) : (retagTv J tv h).ent = J.ent := rfl
lemma retagTv_cost (J : GInvE H T Sl C) (tv : T → Space H) (h : J.tv = tv) : (retagTv J tv h).cost = J.cost := rfl

end Retag

/-- **A family of provider words** with the same target vectors (entrance labels, routes and costs may differ). -/
structure ProvF (ι H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] where
  P : ι → GInvE H T Sl C
  i0 : ι
  htv : ∀ i, (P i).tv = (P i0).tv

section Family
variable {ι H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (D : ProvF ι H T Sl C)

/-- the common target vectors. -/
def ProvF.tv : T → Space H := (D.P D.i0).tv

/-- provider `i` with the common target vectors. -/
def ProvF.inv (i : ι) : GInvE H T Sl C := retagTv (D.P i) D.tv (D.htv i)

lemma ProvF.inv_tv (i : ι) : (D.inv i).tv = D.tv := rfl
lemma ProvF.inv_ent (i : ι) : (D.inv i).ent = (D.P i).ent := rfl
lemma ProvF.inv_cost (i : ι) : (D.inv i).cost = (D.P i).cost := rfl

/-- the residual of slot `q` in a call of provider `i` (the rank its host must take). -/
def ProvF.res (i : ι) (q : Sl) : ℕ := Fintype.card H - ((D.P i).ent q).dim

/-- the invocation of call `c` under the dispatch table `disp`. -/
def ProvF.call {κ : Type} (disp : κ → ι) (c : κ) : GInvE H T Sl C := D.inv (disp c)

lemma ProvF.call_tv {κ : Type} (disp : κ → ι) (c : κ) : (D.call disp c).tv = D.tv := rfl
lemma ProvF.call_ent {κ : Type} (disp : κ → ι) (c : κ) : (D.call disp c).ent = (D.P (disp c)).ent := rfl

/-- residual of slot `q` in SUB-STAGE `k` (the network's numbering `k = 9 ρ + l`), for host frames with
per-sub-stage residuals (`host_framesK`). -/
def ProvF.resK (dispK : ℕ → ι) (k : ℕ) (q : Sl) : ℕ := D.res (dispK k) q

/-- a family whose providers are all the same word: the old single-word network. -/
def ProvF.const (I : GInvE H T Sl C) (i0 : ι) : ProvF ι H T Sl C := ⟨fun _ => I, i0, fun _ => rfl⟩

lemma ProvF.const_res (I : GInvE H T Sl C) (i0 : ι) (i : ι) (q : Sl) :
    (ProvF.const I i0).res i q = Fintype.card H - (I.ent q).dim := rfl

end Family

section Two
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **the two-provider family** (`0`: the base word, e.g. `extra`; `1`: the second word, e.g. `gauge44`). -/
def Prov2.mk' (I0 I1 : GInvE H T Sl C) (h : I1.tv = I0.tv) : ProvF (Fin 2) H T Sl C where
  P := ![I0, I1]
  i0 := 0
  htv := fun i => by
    fin_cases i
    · rfl
    · exact h

lemma Prov2.P0 (I0 I1 : GInvE H T Sl C) (h : I1.tv = I0.tv) : (Prov2.mk' I0 I1 h).P 0 = I0 := rfl
lemma Prov2.P1 (I0 I1 : GInvE H T Sl C) (h : I1.tv = I0.tv) : (Prov2.mk' I0 I1 h).P 1 = I1 := rfl
lemma Prov2.tv_eq (I0 I1 : GInvE H T Sl C) (h : I1.tv = I0.tv) : (Prov2.mk' I0 I1 h).tv = I0.tv := rfl

end Two

section Dispatch
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- the number of calls dispatched to provider `i`. -/
def nCalls (disp : κ → ι) (i : ι) : ℕ := (univ.filter (fun c => disp c = i)).card

/-- **cost summed per call**: a sum over the calls of a function of the provider is the sum over the providers,
weighted by their call counts. -/
theorem sum_dispatch (f : ι → ℝ) (disp : κ → ι) :
    ∑ c, f (disp c) = ∑ i, (nCalls disp i : ℝ) * f i := by
  rw [← Finset.sum_fiberwise univ disp (fun c => f (disp c))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e : ∀ c ∈ univ.filter (fun c => disp c = i), f (disp c) = f i :=
    fun c hc => by rw [(Finset.mem_filter.mp hc).2]
  rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem nCalls_sum (disp : κ → ι) : ∑ i, nCalls disp i = Fintype.card κ := by
  unfold nCalls
  rw [← Finset.card_eq_sum_card_fiberwise (fun c _ => Finset.mem_univ (disp c))]
  rfl

variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **the price of the calls**: every call pays its own provider's invocation. -/
theorem ProvF.callCost_sum (D : ProvF ι H T Sl C) (disp : κ → ι) (φ : ℕ → ℝ) :
    ∑ c, (D.call disp c).cost φ = ∑ i, (nCalls disp i : ℝ) * (D.P i).cost φ :=
  sum_dispatch (fun i => (D.P i).cost φ) disp

/-- the two-provider case: `n0` calls of word 0 and `n1` of word 1. -/
theorem Prov2.callCost (I0 I1 : GInvE H T Sl C) (h : I1.tv = I0.tv) (disp : κ → Fin 2) (φ : ℕ → ℝ) :
    ∑ c, ((Prov2.mk' I0 I1 h).call disp c).cost φ
      = (nCalls disp 0 : ℝ) * I0.cost φ + (nCalls disp 1 : ℝ) * I1.cost φ := by
  rw [ProvF.callCost_sum, Fin.sum_univ_two]
  rfl

/-- with one word only, the dispatched price is `#calls * I.cost` (the old network's `72 * I.cost`). -/
theorem ProvF.callCost_const (I : GInvE H T Sl C) (i0 : ι) (disp : κ → ι) (φ : ℕ → ℝ) :
    ∑ c, ((ProvF.const I i0).call disp c).cost φ = (Fintype.card κ : ℝ) * I.cost φ := by
  show ∑ c : κ, I.cost φ = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- the network's double sum over runs and stages is the sum over calls `(ρ, l)`. -/
theorem sum_runs_stages {R : ℕ} (f : Fin R × Fin 9 → ℝ) :
    ∑ ρ : Fin R, ∑ l : Fin 9, f (ρ, l) = ∑ c : Fin R × Fin 9, f c :=
  (Fintype.sum_prod_type' (fun ρ l => f (ρ, l))).symm

end Dispatch

section Table

/-- a dispatch table given as data: entry `R l + ...`, row-major `k = 9 ρ + l`, `0`/`1` per call. -/
def dispOfList {R : ℕ} (L : List ℕ) (c : Fin R × Fin 9) : Fin 2 :=
  if L.getD (9 * c.1.val + c.2.val) 0 = 1 then 1 else 0

/-- the sub-stage form of the same table (for `host_framesK`; junk `0` past the end). -/
def dispKOfList (L : List ℕ) (k : ℕ) : Fin 2 := if L.getD k 0 = 1 then 1 else 0

lemma dispKOfList_eq {R : ℕ} (L : List ℕ) (ρ : Fin R) (l : Fin 9) :
    dispKOfList L (9 * ρ.val + l.val) = dispOfList L (ρ, l) := rfl

end Table

end
end XHostD
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostD.sum_dispatch
#print axioms OAI.PowerSaving.XHostD.ProvF.callCost_sum
#print axioms OAI.PowerSaving.XHostD.Prov2.callCost
#print axioms OAI.PowerSaving.XHostD.ProvF.callCost_const

import Submission.Work.Mixed.Prog.Merged2
import Submission.Work.MixedCost.TopMain
import Submission.Work.MixedCost.Close

/-!
# Mixed engine, R3 program part 19: the ONE open body of the lockstep program (agents e-r3prog + e-r3cost)

The handler's descriptors are the VALID descriptors (`VD`).  The open body tests the kind of its input:
a top job runs e-r3cost's `top_body` (naive, or tree copies + rests + leftover), a class runs
`class_body_valid`.  Its calls are exactly `kidsV` (the top's `kidsTop`, the class's `kidsC`).

* `Eng.hbody`   the open body in the form `MCost.recurse_list` / `mixed_close` take.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF MXR MCost
noncomputable section

universe U

namespace Eng
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable (E : Eng α ρ σ)

/-- The calls of every descriptor. -/
def kidsAll (kmin n0 : ℕ) : MDesc → List MDesc
  | .top n B v => E.kidsTop kmin n0 n B v
  | .cls n h μ o BS J sup => E.kidsC (.cls n h μ o BS J sup)

lemma topG_spec (kmin n : ℕ) (hn : E.mx ≤ n) : E.mx * 1 * kmin ^ E.topG kmin n ≤ n := by
  rw [Nat.mul_one]
  exact Nat.findGreatest_spec (P := fun g => E.mx * kmin ^ g ≤ n) (Nat.zero_le n) (by simpa using hn)

/-- The calls of a top job are valid. -/
lemma kidsTop_valid (kmin n0 : ℕ) (hn0 : E.mx ≤ n0) (n B : ℕ) (v : ℕ → Bits n → ℂ) :
    ∀ c ∈ E.kidsTop kmin n0 n B v, E.Valid kmin c := by
  intro c hc
  unfold kidsTop at hc
  split_ifs at hc with hif
  · obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
    rw [List.mem_range] at ht
    rcases List.mem_cons.1 hc with hc | hc
    · subst hc
      refine ⟨le_rfl, E.topG_spec kmin n (le_trans hn0 hif.1), ?_⟩
      have hN := hif.2
      have h1 : (t + 1) * E.topN kmin n ≤ B / E.topN kmin n * E.topN kmin n :=
        Nat.mul_le_mul_right _ ht
      have h2 : B / E.topN kmin n * E.topN kmin n ≤ B := Nat.div_mul_le_self _ _
      have h3 : t * E.topN kmin n + E.topNU0 kmin n * E.W + E.cons n (E.topG kmin n) 1 =
          (t + 1) * E.topN kmin n := by unfold topN; ring
      show t * E.topN kmin n + E.topNU0 kmin n * E.W + E.cons n (E.topG kmin n) 1 ≤ B
      omega
    · obtain ⟨j, _, rfl⟩ := List.mem_map.1 hc
      trivial
  · simp at hc

lemma kidsAll_valid {kmin : ℕ} (hk : E.KMin kmin) (n0 : ℕ) (hn0 : E.mx ≤ n0) (d : MDesc)
    (hd : E.Valid kmin d) : ∀ c ∈ E.kidsAll kmin n0 d, E.Valid kmin c := by
  cases d with
  | top n B v => exact E.kidsTop_valid kmin n0 hn0 n B v
  | cls n h μ o BS J sup => exact E.kidsC_valid hk _ hd

/-- Valid descriptors. -/
abbrev VD (kmin : ℕ) := {d : MDesc // E.Valid kmin d}

def kidsV {kmin : ℕ} (hk : E.KMin kmin) (n0 : ℕ) (hn0 : E.mx ≤ n0) (d : E.VD kmin) : List (E.VD kmin) :=
  (E.kidsAll kmin n0 d.1).attach.map (fun c => ⟨c.1, E.kidsAll_valid hk n0 hn0 d.1 d.2 c.1 c.2⟩)

def encV (kmin : ℕ) (cl : Paint) (d : E.VD kmin) : T (portIn cl) := E.enc cl d.1
def outV (kmin : ℕ) (cl : Paint) (d : E.VD kmin) : T (portOut cl) := E.out cl d.1

/-- Word driver. -/
def bndD : MDesc → ℕ
  | .top n B _ => (B + 2) * 2^n
  | .cls n _ _ _ BS _ _ => (BS + 2) * 2^n

/-- Local work. -/
def locD (kmin n0 : ℕ) : MDesc → ℕ
  | .top n B _ => E.locTop kmin n0 n B
  | .cls n h μ _ _ _ _ => E.clsLoc n h μ

lemma sum_attach_map {β : Type*} (P : β → Prop) [DecidablePred P] (l : List β) (hP : ∀ c ∈ l, P c) (g : {c // P c} → ℕ) :
    ((l.attach.map (fun c => (⟨c.1, hP c.1 c.2⟩ : {c // P c}))).map g).sum =
      (l.map (fun c => if hc : P c then g ⟨c, hc⟩ else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.attach_cons, List.map_cons, List.map_map, List.sum_cons]
    rw [dif_pos (hP a List.mem_cons_self)]
    congr 1
    have := ih (fun c hc => hP c (List.mem_cons_of_mem _ hc))
    rw [← this, List.map_map]
    rfl

/-- Is the descriptor a top job. -/
def isTop : MDesc → Prop
  | .top _ _ _ => True
  | .cls _ _ _ _ _ _ _ => False
instance : DecidablePred isTop := fun d => by cases d <;> unfold isTop <;> infer_instance

/-- Fields of a top descriptor. -/
def topF : MDesc → Σ n : ℕ, ℕ × (ℕ → Bits n → ℂ)
  | .top n B v => ⟨n, B, v⟩
  | .cls n _ _ _ _ _ _ => ⟨n, 0, fun _ _ => 0⟩
lemma topF_eq (d : MDesc) (hd : isTop d) : d = MDesc.top (topF d).1 (topF d).2.1 (topF d).2.2 := by
  cases d with
  | top n B v => rfl
  | cls => exact absurd hd (by simp [isTop])

/-- Fields of a class descriptor. -/
def clsF : MDesc → Σ n : ℕ, ℕ × ℕ × ℕ × ℕ × (ℕ → Bits n → ℂ) × (ℕ → Bits n → ℂ)
  | .top n _ _ => ⟨n, 0, 0, 0, 0, fun _ _ => 0, fun _ _ => 0⟩
  | .cls n h μ o BS J sup => ⟨n, h, μ, o, BS, J, sup⟩
lemma clsF_eq (d : MDesc) (hd : ¬ isTop d) :
    d = MDesc.cls (clsF d).1 (clsF d).2.1 (clsF d).2.2.1 (clsF d).2.2.2.1 (clsF d).2.2.2.2.1 (clsF d).2.2.2.2.2.1
      (clsF d).2.2.2.2.2.2 := by
  cases d with
  | top => exact absurd trivial hd
  | cls n h μ o BS J sup => rfl

open Classical in
/-- **The ONE open body of the lockstep program.** -/
theorem hbody {kmin : ℕ} (hk : E.KMin kmin) (n0 : ℕ) (hn0 : E.mx ≤ n0) (m : Bool) (cl : Paint) :
    Able m (gfunds (E.encV kmin cl) (E.outV kmin cl)
        (fun d c => c ∈ (↑(E.kidsV hk n0 hn0 d) : Multiset (E.VD kmin))) (fun d => bndD d.1))
      (portIn cl) (portOut cl) (fun i => E.encV kmin cl i.d) (fun i => E.outV kmin cl i.d)
      (fun i => E.locD kmin n0 i.d.1)
      (fun i => (((↑(E.kidsV hk n0 hn0 i.d) : Multiset (E.VD kmin))).map i.tau).sum) := by
  let Kid := fun (d c : E.VD kmin) => c ∈ (↑(E.kidsV hk n0 hn0 d) : Multiset (E.VD kmin))
  let bk := gfunds (E.encV kmin cl) (E.outV kmin cl) Kid (fun d => bndD d.1)
  let G := GDesc (E.encV kmin cl) (E.outV kmin cl) Kid
  -- the kind of the input
  have hkind : Knows m bk.B (portIn cl) (fun i : G => E.encV kmin cl i.d)
      (fun i => (E.encV kmin cl i.d).2.2.1) := Can.fst (Can.snd Can.second)
  -- calls are answered
  have hmem : ∀ (i : G) (c : MDesc) (hc : c ∈ E.kidsAll kmin n0 i.d.1),
      (⟨c, E.kidsAll_valid hk n0 hn0 i.d.1 i.d.2 c hc⟩ : E.VD kmin) ∈
        (↑(E.kidsV hk n0 hn0 i.d) : Multiset (E.VD kmin)) := by
    intro i c hc
    rw [Multiset.mem_coe]
    exact List.mem_map.2 ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩
  let tau (i : G) (c : MDesc) : ℕ := if hc : E.Valid kmin c then i.tau ⟨c, hc⟩ else 0
  have hcall : ∀ (i : G) (c : MDesc), c ∈ E.kidsAll kmin n0 i.d.1 →
      (i.use (E.enc cl c)).OK (E.out cl c) (tau i c) i.peak := by
    intro i c hc
    have hv := E.kidsAll_valid hk n0 hn0 i.d.1 i.d.2 c hc
    have := i.works ⟨c, hv⟩ (hmem i c hc)
    simp only [tau, dif_pos hv]
    exact this
  have hsum : ∀ i : G, (((↑(E.kidsV hk n0 hn0 i.d) : Multiset (E.VD kmin))).map i.tau).sum =
      ((E.kidsAll kmin n0 i.d.1).map (tau i)).sum := by
    intro i
    rw [Multiset.map_coe, Multiset.sum_coe]
    exact sum_attach_map (E.Valid kmin) _ (E.kidsAll_valid hk n0 hn0 i.d.1 i.d.2) i.tau
  apply Able.branch (hkind.mono (W':=fun i => E.locD kmin n0 i.d.1) (fun _ => Nat.zero_le _))
    (fun i => isTop i.d.1) (fun i => by
      rcases hd : i.d with ⟨d, hv⟩
      cases d <;> simp [encV, enc, mkIn, isTop])
  · -- top jobs: e-r3cost's body
    let K := {i : G // isTop i.d.1}
    let tn (k : K) := (topF k.1.d.1).1
    let tB (k : K) := (topF k.1.d.1).2.1
    let tv (k : K) : ℕ → Bits (tn k) → ℂ := (topF k.1.d.1).2.2
    have heq : ∀ k : K, k.1.d.1 = MDesc.top (tn k) (tB k) (tv k) := fun k => topF_eq _ k.2
    have hbig : Small (bk.comap (fun k : K => k.1)).B (fun k => (tB k + 1) * 2^(tn k)) :=
      (Small.self _).mono (fun k => by
        show (tB k + 1) * 2^(tn k) ≤ bndD k.1.d.1
        rw [heq k]; show (tB k + 1) * 2^(tn k) ≤ (tB k + 2) * 2^(tn k)
        exact Nat.mul_le_mul_right _ (by omega))
    have H := E.top_body kmin n0 hk.two hn0 (m:=m) (cl:=cl) (b:=bk.comap (fun k : K => k.1)) tn tB tv hbig
      (fun k => tau k.1) (fun k c hc => hcall k.1 c (by rw [heq k]; exact hc))
    refine (H.cong (fun k => ?_) (fun k => ?_)).mono (fun k => le_of_eq ?_) (fun k => le_of_eq ?_)
    · show E.enc cl (MDesc.top (tn k) (tB k) (tv k)) = E.encV kmin cl k.1.d
      unfold encV; rw [← heq k]
    · show E.out cl (MDesc.top (tn k) (tB k) (tv k)) = E.outV kmin cl k.1.d
      unfold outV; rw [← heq k]
    · show E.locTop kmin n0 (tn k) (tB k) = E.locD kmin n0 k.1.d.1
      rw [heq k]; rfl
    · show _ = (((↑(E.kidsV hk n0 hn0 k.1.d) : Multiset (E.VD kmin))).map k.1.tau).sum
      rw [hsum k.1, heq k]; rfl
  · -- classes: the class body
    let K := {i : G // ¬ isTop i.d.1}
    let cf (k : K) := clsF k.1.d.1
    have heq : ∀ k : K, k.1.d.1 = MDesc.cls (cf k).1 (cf k).2.1 (cf k).2.2.1 (cf k).2.2.2.1 (cf k).2.2.2.2.1
        (cf k).2.2.2.2.2.1 (cf k).2.2.2.2.2.2 := fun k => clsF_eq _ k.2
    have hval : ∀ k : K, E.Valid kmin (MDesc.cls (cf k).1 (cf k).2.1 (cf k).2.2.1 (cf k).2.2.2.1 (cf k).2.2.2.2.1
        (cf k).2.2.2.2.2.1 (cf k).2.2.2.2.2.2) := fun k => by rw [← heq k]; exact k.1.d.2
    have hbnd : ∀ k : K, (bk.comap (fun k : K => k.1)).B k = ((cf k).2.2.2.2.1 + 2) * 2^((cf k).1) := fun k => by
      show bndD k.1.d.1 = _
      rw [heq k]; rfl
    have hB2 : Small (bk.comap (fun k : K => k.1)).B (fun k => 2^((cf k).1)) :=
      (Small.self _).mono (fun k => by rw [hbnd k]; exact Nat.le_mul_of_pos_left _ (by omega))
    have hBS : Small (bk.comap (fun k : K => k.1)).B (fun k => (cf k).2.2.2.2.1) :=
      (Small.self _).mono (fun k => by
        rw [hbnd k]
        calc (cf k).2.2.2.2.1 ≤ (cf k).2.2.2.2.1 + 2 := by omega
          _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    have H := E.class_body_valid hk (m:=m) (cl:=cl) (b:=bk.comap (fun k : K => k.1))
      (n:=fun k => (cf k).1) (h:=fun k => (cf k).2.1) (μ:=fun k => (cf k).2.2.1) (o:=fun k => (cf k).2.2.2.1)
      (BS:=fun k => (cf k).2.2.2.2.1) (J:=fun k => (cf k).2.2.2.2.2.1) (sup:=fun k => (cf k).2.2.2.2.2.2)
      (τ:=fun k => tau k.1) hB2 hBS hval
      (fun k c hc => hcall k.1 c (by rw [heq k]; exact hc))
    refine (H.cong (fun k => ?_) (fun k => ?_)).mono (fun k => le_of_eq ?_) (fun k => le_of_eq ?_)
    · show E.enc cl (MDesc.cls _ _ _ _ _ _ _) = E.encV kmin cl k.1.d
      unfold encV; rw [← heq k]
    · show E.out cl (MDesc.cls _ _ _ _ _ _ _) = E.outV kmin cl k.1.d
      unfold outV; rw [← heq k]
    · show E.clsLoc _ _ _ = E.locD kmin n0 k.1.d.1
      rw [heq k]; rfl
    · show _ = (((↑(E.kidsV hk n0 hn0 k.1.d) : Multiset (E.VD kmin))).map k.1.tau).sum
      rw [hsum k.1, heq k]; rfl

end Eng

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Eng.hbody
#print axioms OAI.PowerSaving.RAM.Eng.class_body_valid
#print axioms OAI.PowerSaving.RAM.Eng.kidsC_valid
#print axioms OAI.PowerSaving.RAM.Eng.unl_run

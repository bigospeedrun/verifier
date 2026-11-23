--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Mathlib.Logic.Equiv.Fintype
import Submission.Cert.Clifford.LabelMoves

namespace OAI
namespace PowerSaving
namespace RankCost
open Binary Matrix Finset RAM StageBox
noncomputable section
variable {T Sl C : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl] [Fintype C]
  [DecidableEq C]

def eraseC (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  stamp (z ∘ bX) (z ∘ bY) (z ∘ bS) (fun _ => 0)

lemma actPoint_diag {ρ : Type} [Fintype ρ] [DecidableEq ρ] (d : ρ → ℚ) (x : ρ → ℂ) (r : ρ) :
    actPoint (Matrix.diagonal d) x r = (d r : ℂ) * x r := by
  rw [actPoint, Finset.sum_eq_single r (fun j _ hj => by
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), Rat.cast_zero, zero_mul]) (by simp),
    Matrix.diagonal_apply_eq]

variable {α : Type} [Fintype α] [DecidableEq α]

lemma xerase {S S' : Box T Sl C → CMat α} (hX : ∀ t, S' (bX t) = S (bX t))
    (hY : ∀ t, S' (bY t) = S (bY t)) (hS : ∀ q, S' (bS q) = S (bS q)) :
    GenMove.GRoute S S' eraseC (fun _ => 0) := by
  have he : actPoint (Matrix.diagonal (stamp (fun _ => (1 : ℚ)) (fun _ => 1) (fun _ => 1) (fun _ => 0))) =
      (eraseC : (Box T Sl C → ℂ) → _) := by
    funext x r
    rw [actPoint_diag]
    rcases r with ((t | t) | (q | c)) <;> simp [eraseC, stamp, bX, bY, bS]
  rw [← he]
  refine GenMove.GRoute.gate _ S S' fun i j h => ?_
  have hij : i = j := by
    by_contra hij
    exact h (Matrix.diagonal_apply_ne _ hij)
  subst hij
  rcases i with ((t | t) | (q | c))
  · exact hX t
  · exact hY t
  · exact hS q
  · exact (h (by simp [stamp])).elim
end
end RankCost
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving
namespace StageGauge
open Binary Matrix Finset RAM StageBox RankCost
noncomputable section

abbrev SLive (Γ T Sl : Type) := ((Γ × T) ⊕ (Γ × T)) ⊕ (Γ × Sl)
abbrev SRole (Γ T Sl C : Type) := SLive Γ T Sl ⊕ (Γ × C)

variable {Γ T Sl C : Type}
def jX (k : Γ × T) : SRole Γ T Sl C := .inl (.inl (.inl k))
def jY (k : Γ × T) : SRole Γ T Sl C := .inl (.inl (.inr k))
def jS (k : Γ × Sl) : SRole Γ T Sl C := .inl (.inr k)
def jC (k : Γ × C) : SRole Γ T Sl C := .inr k

def mkS {β : Type*} (fX fY : Γ → T → β) (fS : Γ → Sl → β) (fC : Γ → C → β) : SRole Γ T Sl C → β
  | .inl (.inl (.inl (g, t))) => fX g t
  | .inl (.inl (.inr (g, t))) => fY g t
  | .inl (.inr (g, q)) => fS g q
  | .inr (g, c) => fC g c

def spos (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (d : Γ) : Box T Sl C → SRole Γ T Sl C :=
  stamp (fun t => jX ((εX t).symm d, t)) (fun t => jY ((εX t).symm d, t))
    (fun q => jS (εS d, q)) (fun c => jC (εS d, c))

theorem spos_inj (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) {d d' : Γ} {a b : Box T Sl C}
    (h : spos εX εS d a = spos εX εS d' b) : d = d' ∧ a = b := by
  rcases a with ((t | t) | (q | c)) <;> rcases b with ((t' | t') | (q' | c')) <;>
    simp [spos, stamp, jX, jY, jS, jC] at h <;>
    · obtain ⟨h1, rfl⟩ := h
      simp_all

def sem (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (d : Γ) : Box T Sl C ↪ SRole Γ T Sl C :=
  ⟨spos εX εS d, fun _ _ h => (spos_inj εX εS h).2⟩

theorem spos_surj (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (r : SRole Γ T Sl C) :
    ∃ d b, spos εX εS d b = r := by
  match r with
  | .inl (.inl (.inl (g, t))) => exact ⟨εX t g, bX t, by simp [spos, stamp, bX, jX]⟩
  | .inl (.inl (.inr (g, t))) => exact ⟨εX t g, bY t, by simp [spos, stamp, bY, jY]⟩
  | .inl (.inr (g, q)) => exact ⟨εS.symm g, bS q, by simp [spos, stamp, bS, jS]⟩
  | .inr (g, c) => exact ⟨εS.symm g, bC c, by simp [spos, stamp, bC, jC]⟩
end
end StageGauge
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving
namespace StageBox
open Binary Matrix Finset RAM StageBox RankCost StageGauge
noncomputable section
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T] [Fintype Sl]
  [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α] [Fintype Γ] [DecidableEq Γ]

def iin (Xm : XMap H α) (tv : T → Space H) (Z : Sl → CMat α) (c : C → CMat α) : Box T Sl C → CMat α :=
  stamp (fun t => Xm.Φ (tt (tv t))) (fun _ => Xm.Φ 0) Z c
def iout (Xm : XMap H α) (tv : T → Space H) (Z : Sl → CMat α) (c : C → CMat α) : Box T Sl C → CMat α :=
  stamp (fun _ => Xm.Φ 1) (fun t => Xm.Φ (1 + tt (tv t))) Z c

def bIn (tv : T → Space H) (εX : T → Γ ≃ Γ) (M : Γ → XMap H α) (Z : Γ → Sl → CMat α)
    (c : Γ → C → CMat α) : SRole Γ T Sl C → CMat α :=
  mkS (fun g t => (M (εX t g)).Φ (tt (tv t))) (fun g t => (M (εX t g)).Φ 0) Z c
def bOut (tv : T → Space H) (εX : T → Γ ≃ Γ) (M : Γ → XMap H α) (Z : Γ → Sl → CMat α)
    (c : Γ → C → CMat α) : SRole Γ T Sl C → CMat α :=
  mkS (fun g t => (M (εX t g)).Φ 1) (fun g t => (M (εX t g)).Φ (1 + tt (tv t))) Z c

lemma bIn_sem (tv : T → Space H) (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (M : Γ → XMap H α)
    (Z : Γ → Sl → CMat α) (c : Γ → C → CMat α) (d : Γ) :
    bIn tv εX M Z c ∘ sem εX εS d = iin (M d) tv (fun q => Z (εS d) q) (fun k => c (εS d) k) := by
  funext b
  rcases b with ((t | t) | (q | k)) <;> simp [bIn, iin, sem, spos, stamp, mkS, jX, jY, jS, jC]

lemma bOut_sem (tv : T → Space H) (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (M : Γ → XMap H α)
    (Z : Γ → Sl → CMat α) (c : Γ → C → CMat α) (d : Γ) :
    bOut tv εX M Z c ∘ sem εX εS d = iout (M d) tv (fun q => Z (εS d) q) (fun k => c (εS d) k) := by
  funext b
  rcases b with ((t | t) | (q | k)) <;> simp [bOut, iout, sem, spos, stamp, mkS, jX, jY, jS, jC]
end
end StageBox
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.GenMove
open Binary Matrix Finset RAM StageBox RankCost StageGauge
noncomputable section
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

theorem GRoute.reframe {S T : ρ → CMat α} {g : (ρ→ℂ) → (ρ→ℂ)} {c : (ℕ → ℝ) → ℝ} (D : ρ → CMat α)
    (h : GRoute S T g c)
    (hg : ∀ (f : ℕ) (x : Data α ρ f), point f g (multiAct f D x) = multiAct f D (point f g x)) :
    GRoute (fun r => S r * D r) (fun r => T r * D r) g c := by
  obtain ⟨w, hp, hc, hw⟩ := h
  exact ⟨w, hp, hc, fun f x => by rw [multiAct_mulR, multiAct_mulR, hw, hg]⟩

def GReach (A B : CMat α) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∀ (ρ : Type) [Fintype ρ] [DecidableEq ρ] (l : ρ), GStep l A B c

namespace GReach
variable {A B C : CMat α} {c c' : (ℕ → ℝ) → ℝ}
theorem refl (A : CMat α) : GReach A A (fun _ => 0) := fun _ _ _ l => GStep.refl l A
theorem cast (h : GReach A B c) (hc : ∀ φ, c φ = c' φ) : GReach A B c' := fun ρ _ _ l => (h ρ l).cast hc
theorem trans (h : GReach A B c) (g : GReach B C c') : GReach A C (fun φ => c φ + c' φ) :=
  fun ρ _ _ l => (h ρ l).trans (g ρ l)

theorem free {N : CMat α} (hN : Free N) (A : CMat α) : GReach A (N * A) (fun _ => 0) :=
  fun _ _ _ l => gstep_free hN l A
end GReach

namespace GRoute
theorem castg {S T : ρ → CMat α} {g g' : (ρ→ℂ) → (ρ→ℂ)} {c : (ℕ → ℝ) → ℝ} (h : GRoute S T g c)
    (hg : g = g') : GRoute S T g' c := hg ▸ h

theorem reach_all (S T : ρ → CMat α) (c : ρ → (ℕ → ℝ) → ℝ) (h : ∀ r, GReach (S r) (T r) (c r)) :
    GRoute S T id (fun φ => ∑ r, c r φ) := by
  refine GRoute.parallel (ρ := Unit) (h := fun _ => id) (d := c) (fun r => ⟨fun _ => r, fun _ _ _ => rfl⟩)
    (fun i j hij r hi hj => ?_) (fun r => ?_) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun r hr => (hr r ((cover_iff _ _).2 ⟨(), rfl⟩)).elim)
  · obtain ⟨_, rfl⟩ := (cover_iff _ _).1 hi
    obtain ⟨_, hj⟩ := (cover_iff _ _).1 hj
    exact hij hj.symm
  · have h2 := GRoute.on_role (fun _ : Unit => S r) () (T r) (h r Unit ())
    rw [show Function.update (fun _ : Unit => S r) () (T r) = fun _ => T r from
      funext fun u => by cases u; simp] at h2
    exact h2
end GRoute

theorem gsstage {T Sl C Γ : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl] [Fintype C]
    [DecidableEq C] [Fintype Γ] [DecidableEq Γ] (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) {S U : SRole Γ T Sl C → CMat α}
    {G : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {h : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)}
    {cost : (ℕ → ℝ) → ℝ} (q : ∀ d, GRoute (S ∘ sem εX εS d) (U ∘ sem εX εS d) h cost)
    (hin : ∀ d x, (G x) ∘ sem εX εS d = h (x ∘ sem εX εS d)) :
    GRoute S U G (fun φ => (Fintype.card Γ : ℝ) * cost φ) := by
  have hcov : ∀ r : SRole Γ T Sl C, ∃ i, r ∈ covered (sem εX εS i) := fun r => by
    obtain ⟨d, b, hb⟩ := spos_surj εX εS r
    exact ⟨d, (cover_iff _ _).2 ⟨b, hb⟩⟩
  refine (GRoute.parallel (sem (Sl := Sl) (C := C) εX εS) (fun i j hij r hi hj => ?_) q hin
    (fun x r hr => ?_) (fun r hr => ?_)).cast fun φ => by simp
  · obtain ⟨a, rfl⟩ := (cover_iff _ _).1 hi
    obtain ⟨b, hb⟩ := (cover_iff _ _).1 hj
    exact hij (spos_inj εX εS hb).1.symm
  · obtain ⟨i, hi⟩ := hcov r; exact absurd hi (hr i)
  · obtain ⟨i, hi⟩ := hcov r; exact absurd hi (hr i)
end
end PowerSaving.GenMove
end OAI

namespace OAI
namespace PowerSaving.GenMove
open Binary Matrix Finset RAM RankCost
noncomputable section
variable {H β κ : Type} [Fintype H] [DecidableEq H] [Fintype β] [DecidableEq β] [Fintype κ]
  [DecidableEq κ]

def mvPerm (d : Matrix κ κ F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1) : APerm κ where
  π :=
    { toFun := fun y => dᵀ *ᵥ y
      invFun := fun z => d *ᵥ z
      left_inv := fun y => by simp only [mulVec_mulVec, hd', one_mulVec]
      right_inv := fun z => by simp only [mulVec_mulVec, hd, one_mulVec] }
  add := fun x y => Matrix.mulVec_add _ _ _
def inlPerm (G : APerm H) : APerm (H ⊕ β) where
  π :=
    { toFun := fun y => Sum.elim (G.π (fun i => y (Sum.inl i))) (fun b => y (Sum.inr b))
      invFun := fun y => Sum.elim (G.π.symm (fun i => y (Sum.inl i))) (fun b => y (Sum.inr b))
      left_inv := fun y => by funext k; cases k <;> simp
      right_inv := fun y => by funext k; cases k <;> simp }
  add := fun x y => by
    funext k
    cases k with
    | inl i =>
      show G.π ((fun i => x (Sum.inl i)) + (fun i => y (Sum.inl i))) i = _
      rw [G.add]; rfl
    | inr b => rfl
def conjPerm (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1) (G : APerm H) :
    APerm (H ⊕ β) :=
  apComp (mvPerm d hd hd') (inlPerm G)

lemma insub_conj (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1) (G : APerm H)
    (s : Finset H) (q : Finset β) (y : Space (H ⊕ β)) :
    InSub (conjPerm d hd hd' G) (s.disjSum q) y ↔
      InSub G s (fun i => (dᵀ *ᵥ y) (Sum.inl i)) ∧ ∀ b, b ∉ q → (dᵀ *ᵥ y) (Sum.inr b) = 0 := by
  simp only [InSub, Sum.forall, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum]
  rfl

def LabelLift.ofConj (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1) (q : Finset β) :
    LabelLift H (H ⊕ β) where
  liftG := conjPerm d hd hd'
  liftS s := s.disjSum q
  mono := fun h => Finset.disjSum_mono h subset_rfl
  card := fun {s t} h => by
    have hle := Finset.card_le_card h
    rw [card_sdiff_of_subset (Finset.disjSum_mono h subset_rfl), card_sdiff_of_subset h,
      Finset.card_disjSum, Finset.card_disjSum]
    omega
  sub := fun h y => by rw [insub_conj, insub_conj, h]
end
end PowerSaving.GenMove
end OAI

namespace OAI
namespace PowerSaving
namespace StageWin
open Binary Matrix Finset RAM StageBox RankCost GenMove
noncomputable section

abbrev L3 (T Sl : Type) := (T ⊕ T) ⊕ Sl
abbrev lS {T Sl : Type} (q : Sl) : L3 T Sl := Sum.inr q

structure Window (H α : Type) [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α] where
  Xm : XMap H α
  X : LabelLift H α
  big : Fintype.card H < Fintype.card α
  toNew : ∀ (A : OBase H) (s : Finset H) (U : SubspaceLabel H), (∀ x, U.Mem x ↔ InSub (coordPerm A) s x) →
    GReach (Xm.Φ (A.mat s)) (X.Φ U) (fun _ => 0)
  toOld : ∀ (A : OBase H) (s : Finset H) (U : SubspaceLabel H), (∀ x, U.Mem x ↔ InSub (coordPerm A) s x) →
    GReach (X.Φ U) (Xm.Φ (A.mat s)) (fun _ => 0)

variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]
namespace Window
variable (W : Window H α)

lemma mem_iff {A : OBase H} {s : Finset H} {U : SubspaceLabel H} (h : ∀ x, InSub (coordPerm A) s x → U.Mem x)
    (hc : s.card = U.dim) (x : Space H) : U.Mem x ↔ InSub (coordPerm A) s x :=
  (insub_iff_of_card (G' := U.G) (s' := U.s) h hc x).symm

theorem line (A : OBase H) (l : H) (U : SubspaceLabel H) (hd : U.dim = 1) (hm : U.Mem (A.v l)) :
    GReach (W.Xm.Φ (tt (A.v l))) (W.X.Φ U) (fun _ => 0) := by
  suffices hU : ∀ x, InSub (coordPerm A) {l} x → U.Mem x by
    have := W.toNew A {l} U (mem_iff hU (by rw [Finset.card_singleton]; exact hd.symm))
    rwa [mat_single] at this
  intro x hx
  have hx' : x = dot (A.v l) x • A.v l := by
    conv_lhs => rw [← A.proj_univ x]
    rw [OBase.proj, Finset.sum_eq_single l (fun k _ hk => by
      rw [show dot (A.v k) x = 0 from hx k (by simpa using hk), zero_smul]) (by simp)]
  rcases bit_cases (dot (A.v l) x) with h | h
  · rw [hx', h, zero_smul]; exact insub_zero _ _
  · rw [hx', h, one_smul]; exact hm

theorem zero (U : SubspaceLabel H) (hd : U.dim = 0) : GReach (W.Xm.Φ 0) (W.X.Φ U) (fun _ => 0) := by
  suffices hU : ∀ x, InSub (coordPerm (OBase.canonical H)) ∅ x → U.Mem x by
    have := W.toNew (OBase.canonical H) ∅ U (mem_iff hU (by rw [Finset.card_empty]; exact hd.symm))
    rwa [mat_empty] at this
  intro x hx
  have : x = 0 := (coordPerm (OBase.canonical H)).π.injective (by
    rw [APerm.map_zero']; funext k; exact hx k (Finset.notMem_empty k))
  rw [this]; exact insub_zero _ _

theorem full (U : SubspaceLabel H) (hd : U.dim = Fintype.card H) :
    GReach (W.X.Φ U) (W.Xm.Φ 1) (fun _ => 0) := by
  have := W.toOld (OBase.canonical H) univ U (insub_iff_of_card (G := U.G) (s := U.s)
    (G' := coordPerm (OBase.canonical H)) (s' := univ) (fun x _ k hk => absurd (mem_univ k) hk)
    (by rw [Finset.card_univ]; exact hd))
  rwa [OBase.mat_univ] at this

theorem perp (A : OBase H) (l : H) (U : SubspaceLabel H) (hd : U.dim + 1 = Fintype.card H)
    (hm : ∀ x, U.Mem x → dot (A.v l) x = 0) :
    GReach (W.X.Φ U) (W.Xm.Φ (1 + tt (A.v l))) (fun _ => 0) := by
  have := W.toOld A (univ \ {l}) U (insub_iff_of_card (G := U.G) (s := U.s) (G' := coordPerm A)
    (s' := univ \ {l}) (fun x hx k hk => by
      obtain rfl : k = l := by simpa using hk
      exact hm x hx)
    (by rw [card_sdiff_of_subset (subset_univ _), Finset.card_univ, Finset.card_singleton]
        simp only [SubspaceLabel.dim] at hd; omega))
  rwa [mat_compl_single] at this
end Window

theorem base_ex (z : Space H) (hz : dot z z = 1) (hg : ∃ p, z p = 0) (l : H) :
    ∃ A : OBase H, z = A.v l := by
  obtain ⟨p, hp⟩ := hg
  obtain ⟨A, k, hk⟩ := exists_base_one z hz p hp
  exact ⟨⟨fun i => A.v (Equiv.swap k l i), fun i j => by rw [A.rows]; simp⟩, by simp [hk]⟩
end
end StageWin
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving.GenMove

def SubspaceLabel.top {H : Type} [Fintype H] (U : SubspaceLabel H) : SubspaceLabel H := ⟨U.G, Finset.univ⟩

lemma SubspaceLabel.top_dim {H : Type} [Fintype H] (U : SubspaceLabel H) : U.top.dim = Fintype.card H :=
  Finset.card_univ

end PowerSaving.GenMove

namespace PowerSaving
namespace StageWin
open Binary Matrix Finset RAM StageBox RankCost GenMove StageGauge
noncomputable section

section Ent
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

def entW (X : LabelLift H α) (U : SubspaceLabel H) : CMat α :=
  phasedPerm (X.liftG U.G) * coordFrame (X.liftS univ \ X.liftS U.s) * phasedPerm (apInv (X.liftG U.G))

def entN (X : LabelLift H α) (U : SubspaceLabel H) : CMat α :=
  phasedPerm (X.liftG U.G) * (coordFrame (X.liftS U.s) * shift (indv (X.liftS U.s))) * phasedPerm (apInv (X.liftG U.G))

lemma phi_eq (X : LabelLift H α) (U : SubspaceLabel H) :
    X.Φ U = phasedPerm (X.liftG U.G) * coordFrame (X.liftS U.s) * phasedPerm (apInv (X.liftG U.G)) := rfl

lemma kgL (G : APerm α) (M : CMat α) : phasedPerm (apInv G) * (phasedPerm G * M) = M := by
  rw [← mul_assoc, kg_inv_mul, one_mul]

lemma kgR (G : APerm α) (M : CMat α) : phasedPerm G * (phasedPerm (apInv G) * M) = M := by
  rw [← mul_assoc, kg_mul_inv, one_mul]

lemma entN_spec (X : LabelLift H α) (U : SubspaceLabel H) : X.Φ U * entN X U = 1 := by
  rw [phi_eq, entN]
  simp only [mul_assoc, kgL]
  rw [← mul_assoc (coordFrame _) (coordFrame _), pk_sq, ← mul_assoc (shift _), shift_sq, one_mul, kg_mul_inv]

lemma entW_spec (X : LabelLift H α) (U : SubspaceLabel H) : X.Φ U.top = entW X U * X.Φ U := by
  show phasedPerm (X.liftG U.G) * coordFrame (X.liftS univ) * phasedPerm (apInv (X.liftG U.G)) = _
  rw [phi_eq, entW, pk_sdiff (X.mono (subset_univ U.s))]
  simp only [mul_assoc, kgL]

lemma entW_form (X : LabelLift H α) (U : SubspaceLabel H) :
    ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = Fintype.card H - U.dim ∧
      entW X U = C * coordFrame R * C' :=
  ⟨phasedPerm (X.liftG U.G), phasedPerm (apInv (X.liftG U.G)), X.liftS univ \ X.liftS U.s,
    free_kg _, free_kg _, by
      simp only [X.card (subset_univ U.s), card_sdiff_of_subset (subset_univ _), card_univ, SubspaceLabel.dim], rfl⟩

end Ent

section Exit
variable {H T Sl C α : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]

def exEntS (ent ex : Sl → SubspaceLabel H) (q : Sl) : SubspaceLabel H :=
  ⟨apId H, ((Finset.univ : Finset H).toList.take (Fintype.card H - ((ex q).dim - (ent q).dim))).toFinset⟩

lemma exEntS_dim (ent ex : Sl → SubspaceLabel H) (q : Sl) :
    (exEntS ent ex q).dim = Fintype.card H - ((ex q).dim - (ent q).dim) := by
  show (List.toFinset _).card = _
  rw [List.toFinset_card_of_nodup ((Finset.nodup_toList _).sublist (List.take_sublist _ _)),
    List.length_take, Finset.length_toList, card_univ]
  omega

def adPair (U V : SubspaceLabel H) : APerm H × Finset H × Finset H := by
  classical
  exact if h : ∀ x, U.Mem x → V.Mem x then
    ((exists_common_base U.G V.G U.s V.s h).choose,
     (exists_common_base U.G V.G U.s V.s h).choose_spec.choose,
     (exists_common_base U.G V.G U.s V.s h).choose_spec.choose_spec.choose)
  else (U.G, U.s, U.s)

lemma adPair_spec (U V : SubspaceLabel H) (h : ∀ x, U.Mem x → V.Mem x) :
    (adPair U V).2.1 ⊆ (adPair U V).2.2 ∧ (∀ x, U.Mem x ↔ InSub (adPair U V).1 (adPair U V).2.1 x) ∧
      ∀ x, InSub (adPair U V).1 (adPair U V).2.2 x ↔ V.Mem x := by
  unfold adPair
  rw [dif_pos h]
  exact (exists_common_base U.G V.G U.s V.s h).choose_spec.choose_spec.choose_spec

def entA (U V : SubspaceLabel H) : SubspaceLabel H := ⟨(adPair U V).1, (adPair U V).2.1⟩

def exlA (U V : SubspaceLabel H) : SubspaceLabel H := ⟨(adPair U V).1, (adPair U V).2.2⟩

def lab0X (E : Finset Sl) (L0 LF : L3 T Sl → SubspaceLabel H) : L3 T Sl → SubspaceLabel H :=
  Sum.elim (fun xy => L0 (Sum.inl xy))
    (fun q => if q ∈ E then entA (L0 (lS q)) (LF (lS q)) else L0 (lS q))

lemma lab0X_E (E : Finset Sl) (L0 LF : L3 T Sl → SubspaceLabel H) {q : Sl} (hq : q ∈ E) :
    lab0X E L0 LF (lS q) = entA (L0 (lS q)) (LF (lS q)) := if_pos hq

lemma lab0X_N (E : Finset Sl) (L0 LF : L3 T Sl → SubspaceLabel H) {q : Sl} (hq : q ∉ E) :
    lab0X E L0 LF (lS q) = L0 (lS q) := if_neg hq

lemma mem_full (U : SubspaceLabel H) (hd : U.dim = Fintype.card H) (x : Space H) : U.Mem x := by
  have hU : U.s = univ := eq_univ_of_card U.s hd
  intro k hk
  exact absurd (hU ▸ mem_univ k) hk

lemma reach_rebase (X : LabelLift H α) {U V : SubspaceLabel H} (h : ∀ x, U.Mem x ↔ V.Mem x) :
    GReach (X.Φ U) (X.Φ V) (fun _ => 0) :=
  GReach.cast (fun ρ _ _ l => (X.fmv (LabelMove.rebase (m := Fintype.card α) h)).reach ρ l) fun φ => rcost_nil φ

end Exit
end
end StageWin
end PowerSaving
end OAI

namespace OAI.PowerSaving.GenMove
open Binary RankCost
noncomputable section
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

def GRouteF (S T : ρ → CMat α) (F : ∀ f, Data α ρ f → Data α ρ f) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧
    ∀ (f : ℕ) (x : Data α ρ f), gwalk f w (multiAct f S x) = multiAct f T (F f x)

namespace GRouteF
variable {S T U : ρ → CMat α} {F G : ∀ f, Data α ρ f → Data α ρ f} {c c' : (ℕ → ℝ) → ℝ}

theorem ofRoute {g : (ρ → ℂ) → (ρ → ℂ)} (h : GRoute S T g c) : GRouteF S T (fun f => point f g) c := h

theorem toRoute {g : (ρ → ℂ) → (ρ → ℂ)} (h : GRouteF S T F c) (hF : ∀ f x, F f x = point f g x) :
    GRoute S T g c := by
  obtain ⟨w, hw, hc, he⟩ := h
  exact ⟨w, hw, hc, fun f x => (he f x).trans (by rw [hF])⟩

theorem congr (h : GRouteF S T F c) (hF : ∀ f x, F f x = G f x) (hc : ∀ φ, c φ = c' φ) : GRouteF S T G c' := by
  obtain ⟨w, hw, hcw, he⟩ := h
  exact ⟨w, hw, fun φ => (hcw φ).trans (hc φ), fun f x => (he f x).trans (by rw [hF])⟩

theorem trans (a : GRouteF S T F c) (b : GRouteF T U G c') :
    GRouteF S U (fun f x => G f (F f x)) (fun φ => c φ + c' φ) := by
  obtain ⟨w, hw, hc, he⟩ := a
  obtain ⟨w', hw', hc', he'⟩ := b
  refine ⟨w ++ w', ?_, fun φ => by rw [GWord.costR_append, hc, hc'], fun f x => by rw [gwalk_append, he, he']⟩
  intro mv hm
  rcases List.mem_append.1 hm with hm | hm
  exacts [hw mv hm, hw' mv hm]

theorem role {l : ρ} {V K : CMat α} (h : GStep l (S l) (V * K) c) :
    GRouteF S (Function.update S l V) (fun f x => roleAct f l K x) c := by
  obtain ⟨w, Um, hp, hc, hU, hw⟩ := h
  refine ⟨w, hp, hc, fun f x => ?_⟩
  rw [hw]
  funext j
  by_cases hj : j = l
  · subst hj
    simp only [roleAct, multiAct, Function.update_apply, if_true, matAct_mul, hU]
  · simp only [roleAct, multiAct, Function.update_apply, if_neg hj]

end GRouteF
end
end OAI.PowerSaving.GenMove

namespace WarpCheck
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GenMove OAI.PowerSaving.RAM
  OAI.PowerSaving.StageBox OAI.PowerSaving.StageWin Finset Matrix

def shear {T Sl C : Type} (α β : T → ℚ) (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  stamp (fun t => z (bX t) + (α t : ℂ) * z (bY t))
    (fun t => (β t : ℂ) * z (bX t) + (1 + (α t : ℂ) * (β t : ℂ)) * z (bY t)) (z ∘ bS) (fun _ => 0)

section Routes
variable {H T Sl C α : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]

theorem shear_comm (al be : T → ℚ) (DX : T → CMat α) (DS : Sl → CMat α) (DC : C → CMat α) (f : ℕ)
    (x : Data α (Box T Sl C) f) :
    point f (shear al be) (multiAct f (stamp DX DX DS DC) x) =
      multiAct f (stamp DX DX DS DC) (point f (shear al be) x) := by
  funext r i
  rcases r with (t | t) | (q | k)
  · show matAct f (DX t) (x (bX t)) i + (al t : ℂ) * matAct f (DX t) (x (bY t)) i =
      matAct f (DX t) (fun i => x (bX t) i + (al t : ℂ) * x (bY t) i) i
    simp [matAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
  · show (be t : ℂ) * matAct f (DX t) (x (bX t)) i + (1 + (al t : ℂ) * (be t : ℂ)) * matAct f (DX t) (x (bY t)) i =
      matAct f (DX t) (fun i => (be t : ℂ) * x (bX t) i + (1 + (al t : ℂ) * (be t : ℂ)) * x (bY t) i) i
    simp [matAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
  · rfl
  · show 0 = matAct f (DC k) (fun _ => 0) i
    simp [matAct, Matrix.mulVec, dotProduct]

theorem _root_.OAI.PowerSaving.GenMove.GRoute.ofFree {ρ : Type} [Fintype ρ] [DecidableEq ρ] {S S' : ρ → CMat α}
    (h : ∀ r, ∃ A, Free A ∧ S' r = A * S r) : GRoute S S' id (fun _ => 0) := by
  choose A hA he using h
  refine (GRoute.reach_all S S' (fun _ _ => 0) fun r => ?_).cast fun φ => by simp
  intro ρ' _ _ l
  rw [he r]
  exact gstep_free (hA r) l (S r)

theorem _root_.OAI.PowerSaving.GenMove.GRoute.slots {X Y : T → CMat α} {c : C → CMat α} {Z Z' : Sl → CMat α}
    (h : ∀ q, ∃ A, Free A ∧ Z' q = A * Z q) :
    GRoute (stamp X Y Z c) (stamp X Y Z' c) id (fun _ => 0) :=
  GRoute.ofFree fun r => by
    rcases r with (t | t) | (q | k)
    · exact ⟨1, Free.one, (one_mul _).symm⟩
    · exact ⟨1, Free.one, (one_mul _).symm⟩
    · exact h q
    · exact ⟨1, Free.one, (one_mul _).symm⟩

theorem gdirtyE (Xm : RankCost.XMap H α) (tv : T → Space H) (E F' N Wn : Sl → CMat α)
    (hN : ∀ q, E q * N q = 1) (hW : ∀ q, F' q = Wn q * E q) (Z : Sl → CMat α) (c0 c1 : C → CMat α)
    {g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)} {cost : (ℕ → ℝ) → ℝ}
    (h : GRoute (iin Xm tv E c0) (iout Xm tv F' c1) g cost)
    (hg : ∀ f (x : Data α (Box T Sl C) f),
      point f g (multiAct f (stamp (fun _ => 1) (fun _ => 1) (fun q => N q * Z q) (fun _ => 1)) x) =
        multiAct f (stamp (fun _ => 1) (fun _ => 1) (fun q => N q * Z q) (fun _ => 1)) (point f g x)) :
    GRoute (iin Xm tv Z c0) (iout Xm tv (fun q => Wn q * Z q) c1) g cost := by
  have h' := h.reframe _ hg
  have e1 : (fun r => iin Xm tv E c0 r *
      stamp (fun _ => (1 : CMat α)) (fun _ => 1) (fun q => N q * Z q) (fun _ => 1) r) = iin Xm tv Z c0 := by
    funext r
    rcases r with (t | t) | (q | k) <;> (try simp only [iin, stamp, Sum.elim_inl, Sum.elim_inr, mul_one])
    rw [← mul_assoc, hN, one_mul]
  have e2 : (fun r => iout Xm tv F' c1 r *
      stamp (fun _ => (1 : CMat α)) (fun _ => 1) (fun q => N q * Z q) (fun _ => 1) r) =
      iout Xm tv (fun q => Wn q * Z q) c1 := by
    funext r
    rcases r with (t | t) | (q | k) <;> (try simp only [iout, stamp, Sum.elim_inl, Sum.elim_inr, mul_one])
    rw [hW, mul_assoc, ← mul_assoc (E q), hN, one_mul]
  rwa [e1, e2] at h'

lemma permL (G : APerm α) (M : CMat α) : permMat G * (permMat (apInv G) * M) = M := by
  rw [← mul_assoc, show permMat G * permMat (apInv G) = 1 from permMat_inv_mul (apInv G), one_mul]

lemma cpermL (τ : Equiv.Perm α) (s : Finset α) (M : CMat α) :
    permMat (CoordPerm.cperm τ) * (coordFrame s * M) =
      coordFrame (s.map τ.toEmbedding) * (permMat (CoordPerm.cperm τ) * M) := by
  rw [← mul_assoc, CoordPerm.pk_cperm, mul_assoc]

theorem exRouteE (ent ex : Sl → SubspaceLabel H) (hexG : ∀ q, (ex q).G = (ent q).G)
    (hexs : ∀ q, (ent q).s ⊆ (ex q).s) (ent' : Sl → SubspaceLabel H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (ex q).dim - (ent q).dim) (W : Window H α)
    {tv : T → Space H} {g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)} {cost : (ℕ → ℝ) → ℝ}
    (run : ∀ (N Wn : Sl → CMat α), (∀ q, W.X.Φ (ent q) * N q = 1) →
      (∀ q, W.X.Φ (ex q) = Wn q * W.X.Φ (ent q)) → ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
      GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) g cost)
    (N Wn : Sl → CMat α) (hN : ∀ q, W.X.Φ (ent' q) * N q = 1)
    (hW : ∀ q, W.X.Φ (ent' q).top = Wn q * W.X.Φ (ent' q)) (Z : Sl → CMat α) (c0 c1 : C → CMat α) :
    GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) g cost := by
  set X := W.X

  let K0 q := phasedPerm (X.liftG (ent q).G)
  let K0' q := phasedPerm (apInv (X.liftG (ent q).G))
  let K1 q := phasedPerm (X.liftG (ent' q).G)
  let K1' q := phasedPerm (apInv (X.liftG (ent' q).G))
  let R q := X.liftS (ex q).s \ X.liftS (ent q).s
  have hR : ∀ q, (R q).card = (X.liftS univ \ X.liftS (ent' q).s).card := fun q => by
    have := hd q
    unfold SubspaceLabel.dim at this
    rw [X.card (hexs q), X.card (subset_univ _), card_sdiff_of_subset (subset_univ _), card_univ,
      card_sdiff_of_subset (hexs q)]
    omega
  choose τ hτ using fun q => Equiv.Perm.exists_map_finset_eq _ _ (hR q)
  let P q := permMat (CoordPerm.cperm (τ q))
  let P' q := permMat (apInv (CoordPerm.cperm (τ q)))
  let Wn0 q := K0 q * coordFrame (R q) * K0' q
  have hW0 : ∀ q, X.Φ (ex q) = Wn0 q * X.Φ (ent q) := fun q => by
    rw [phi_eq, phi_eq, hexG q, pk_sdiff (X.mono (hexs q))]
    simp only [Wn0, K0, K0', R, mul_assoc, kgL]
  have hWn : ∀ q, Wn q = entW X (ent' q) := fun q => by
    have e := (hW q).symm.trans (entW_spec X (ent' q))
    calc Wn q = Wn q * (X.Φ (ent' q) * N q) := by rw [hN q, mul_one]
      _ = entW X (ent' q) * (X.Φ (ent' q) * N q) := by rw [← mul_assoc, e, mul_assoc]
      _ = entW X (ent' q) := by rw [hN q, mul_one]
  have r1 := GRoute.slots (X := fun t => W.Xm.Φ (tt (tv t))) (Y := fun _ => W.Xm.Φ 0) (c := c0)
    (Z := Z) (Z' := fun q => (K0 q * P' q * K1' q) * Z q)
    fun q => ⟨K0 q * P' q * K1' q, ((free_kg _).mul (Free.perm _)).mul (free_kg _), rfl⟩
  have r2 := run (fun q => entN X (ent q)) Wn0 (fun q => entN_spec X (ent q)) hW0
    (fun q => (K0 q * P' q * K1' q) * Z q) c0 c1
  have r3 := GRoute.slots (X := fun _ => W.Xm.Φ 1) (Y := fun t => W.Xm.Φ (1 + tt (tv t))) (c := c1)
    (Z := fun q => Wn0 q * ((K0 q * P' q * K1' q) * Z q)) (Z' := fun q => Wn q * Z q)
    fun q => ⟨K1 q * P q * K0' q, ((free_kg _).mul (Free.perm _)).mul (free_kg _), by
      rw [hWn q, entW, ← hτ q]
      simp only [Wn0, K0, K0', K1, K1', P, P', mul_assoc, kgL, cpermL, permL]⟩
  exact ((r1.trans r2).trans r3).cast fun φ => by simp

end Routes

structure StageInvariant (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
    (Ok : ∀ {γ : Type} [Fintype γ] [DecidableEq γ], Window H γ → Prop) where
  tv : T → Space H
  hunit : ∀ t, dot (tv t) (tv t) = 1
  hgap : ∀ t, ∃ p, tv t p = 0
  cost : (ℕ → ℝ) → ℝ
  ent : Sl → SubspaceLabel H
  al : T → ℚ
  be : T → ℚ
  ex : Sl → SubspaceLabel H
  hexG : ∀ q, (ex q).G = (ent q).G
  hexs : ∀ q, (ent q).s ⊆ (ex q).s
  run : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : Window H α), Ok W →
    ∀ (N Wn : Sl → CMat α), (∀ q, W.X.Φ (ent q) * N q = 1) → (∀ q, W.X.Φ (ex q) = Wn q * W.X.Φ (ent q)) →
    ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
      GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) (shear al be) cost

section Inv
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
  {Ok : ∀ {γ : Type} [Fintype γ] [DecidableEq γ], Window H γ → Prop}

noncomputable def StageInvariant.entS (I : StageInvariant H T Sl C Ok) (q : Sl) : SubspaceLabel H :=
  exEntS I.ent I.ex q

lemma StageInvariant.entS_hd (I : StageInvariant H T Sl C Ok) (q : Sl) :
    Fintype.card H - (I.entS q).dim = (I.ex q).dim - (I.ent q).dim := by
  have h1 : (I.ex q).dim ≤ Fintype.card H := card_le_univ _
  rw [StageInvariant.entS, exEntS_dim]
  omega

def StageInvariant.toExitWith (I : StageInvariant H T Sl C Ok) (ent' : Sl → SubspaceLabel H)
    (hd : ∀ q, Fintype.card H - (ent' q).dim = (I.ex q).dim - (I.ent q).dim) : StageInvariant H T Sl C Ok where
  tv := I.tv
  hunit := I.hunit
  hgap := I.hgap
  cost := I.cost
  ent := ent'
  al := I.al
  be := I.be
  ex q := (ent' q).top
  hexG _ := rfl
  hexs _ := subset_univ _
  run W hok N Wn hN hW Z c0 c1 :=
    exRouteE I.ent I.ex I.hexG I.hexs ent' hd W (I.run W hok) N Wn hN hW Z c0 c1

noncomputable def StageInvariant.toExit (I : StageInvariant H T Sl C Ok) : StageInvariant H T Sl C Ok :=
  I.toExitWith I.entS I.entS_hd

end Inv
end WarpCheck

namespace OAI
namespace PowerSaving
namespace StageGauge
open Binary Matrix Finset RAM StageBox RankCost
noncomputable section
variable {n m : Type} [Fintype n] [DecidableEq n]

def diagI (S : Finset n) : Matrix n n F := Matrix.diagonal fun i => if i ∈ S then 1 else 0
def cmat (A : OBase n) : Matrix n n F := fun a k => A.v k a
def ofCols (M : Matrix n n F) (hM : Mᵀ * M = 1) : OBase n where
  v := fun k a => M a k
  rows := fun i j => by
    have h := congrFun (congrFun hM i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h

lemma diagI_conj (M : Matrix m n F) (S : Finset n) (i j : m) :
    (M * diagI S * Mᵀ) i j = ∑ k ∈ S, M i k * M j k := by
  rw [Matrix.mul_apply (M := M * diagI S)]
  simp only [diagI, Matrix.mul_diagonal, Matrix.transpose_apply, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

lemma diagI_disjSum [Fintype m] [DecidableEq m] (s : Finset n) (q : Finset m) :
    diagI (s.disjSum q) = Matrix.fromBlocks (diagI s) 0 0 (diagI q) := by
  rw [diagI, diagI, diagI, Matrix.fromBlocks_diagonal]
  congr 1
  funext x
  cases x <;> simp

lemma frame_ofCols (M : Matrix n n F) (hM : Mᵀ * M = 1) (S : Finset n) :
    frame (ofCols M hM) S = frameM (M * diagI S * Mᵀ) := by
  rw [frame_eq]
  congr 1
  ext i j
  rw [diagI_conj]
  rfl

lemma submatrix_diagI (M : Matrix n n F) (π : Equiv.Perm n) (S : Finset n) :
    M.submatrix id π * diagI S * (M.submatrix id π)ᵀ = M * diagI (S.map π.toEmbedding) * Mᵀ := by
  ext i j
  rw [diagI_conj, diagI_conj, Finset.sum_map]
  rfl

lemma transpose_orth {A : Matrix n n F} (h : Aᵀ * A = 1) : Aᵀᵀ * Aᵀ = 1 := by
  rw [Matrix.transpose_transpose]
  exact mul_eq_one_symm h
lemma mul_orth {A B : Matrix n n F} (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) : (A * B)ᵀ * (A * B) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, Matrix.one_mul, hB]
lemma submatrix_orth (A : Matrix n n F) (h : Aᵀ * A = 1) (π : Equiv.Perm n) :
    (A.submatrix id π)ᵀ * A.submatrix id π = 1 := by
  ext i j
  have := congrFun (congrFun h (π i)) (π j)
  simpa [Matrix.mul_apply, Matrix.one_apply] using this
lemma submatrix_symm (M : Matrix m n F) (π : Equiv.Perm n) : (M.submatrix id π).submatrix id π.symm = M := by
  ext i j; simp
lemma submatrix_symm' (M : Matrix m n F) (π : Equiv.Perm n) : (M.submatrix id π.symm).submatrix id π = M := by
  ext i j; simp

abbrev Orth (n : Type) [Fintype n] [DecidableEq n] := {g : Matrix n n F // gᵀ * g = 1}
namespace Orth
lemma orth' (g : Orth n) : g.1 * g.1ᵀ = 1 := mul_eq_one_symm g.2
def one : Orth n :=
  ⟨1, by rw [Matrix.mul_one, Matrix.transpose_one]⟩
def conjPerm (B : Matrix n n F) (hB : Bᵀ * B = 1) (π : Equiv.Perm n) : Orth n ≃ Orth n where
  toFun g := ⟨(g.1 * B).submatrix id π * Bᵀ,
    mul_orth (submatrix_orth _ (mul_orth g.2 hB) π) (transpose_orth hB)⟩
  invFun g := ⟨(g.1 * B).submatrix id π.symm * Bᵀ,
    mul_orth (submatrix_orth _ (mul_orth g.2 hB) π.symm) (transpose_orth hB)⟩
  left_inv g := by
    have back : g.1 * B * Bᵀ = g.1 := by rw [Matrix.mul_assoc, mul_eq_one_symm hB, Matrix.mul_one]
    apply Subtype.ext
    show ((g.1 * B).submatrix id π * Bᵀ * B).submatrix id π.symm * Bᵀ = g.1
    rw [Matrix.mul_assoc _ Bᵀ B, hB, Matrix.mul_one, submatrix_symm, back]
  right_inv g := by
    have back : g.1 * B * Bᵀ = g.1 := by rw [Matrix.mul_assoc, mul_eq_one_symm hB, Matrix.mul_one]
    apply Subtype.ext
    show ((g.1 * B).submatrix id π.symm * Bᵀ * B).submatrix id π * Bᵀ = g.1
    rw [Matrix.mul_assoc _ Bᵀ B, hB, Matrix.mul_one, submatrix_symm', back]
lemma conjPerm_mul (B : Matrix n n F) (hB : Bᵀ * B = 1) (π : Equiv.Perm n) (g : Orth n) :
    (conjPerm B hB π g).1 * B = (g.1 * B).submatrix id π := by
  show (g.1 * B).submatrix id π * Bᵀ * B = _
  rw [Matrix.mul_assoc, hB, Matrix.mul_one]
end Orth
end
end StageGauge
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving
namespace Window137
open Binary Matrix Finset RAM StageBox RankCost StageGauge GenMove
noncomputable section
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H] {l : H}

abbrev Hp (H : Type) (l : H) := {j : H // j ≠ l}
abbrev LC (B H : Type) (l : H) := H ⊕ (B × Hp H l)
abbrev JC (s : Finset H) (q : Finset (B × Hp H l)) : Finset (LC B H l) := s.disjSum q

variable (B l) in
def blkC (A : OBase H) : Matrix (LC B H l) (LC B H l) F := Matrix.fromBlocks (cmat A) 0 0 1

lemma cmat_orth (A : OBase H) : (cmat A)ᵀ * cmat A = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  exact A.rows i j

lemma blkC_orth (A : OBase H) : (blkC B l A)ᵀ * blkC B l A = 1 := by
  simp [blkC, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, cmat_orth]

def PhiC (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (P : Matrix H H F) : CMat (LC B H l) :=
  frameM (d.1 * Matrix.fromBlocks P 0 0 (diagI q) * d.1ᵀ)

lemma PhiC_eq (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (A : OBase H) (s : Finset H) :
    PhiC d q (A.mat s) = frame (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A))) (JC s q) := by
  have hm : blkC B l A * diagI (JC s q) * (blkC B l A)ᵀ = Matrix.fromBlocks (A.mat s) 0 0 (diagI q) := by
    rw [diagI_disjSum, blkC, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.transpose_zero, Matrix.transpose_one]
    congr 1
    ext i j
    rw [diagI_conj]
    rfl
  rw [frame_ofCols]
  unfold PhiC
  congr 1
  rw [← hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

instance instFintypeOrthLC : Fintype (Orth (LC B H l)) := by unfold Orth; infer_instance
instance instDecEqOrthLC : DecidableEq (Orth (LC B H l)) := by unfold Orth; infer_instance

def qC (bs : Finset B) : Finset (B × Hp H l) := bs ×ˢ univ

def fmapC (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) (d : Orth (LC B H l))
    (q : Finset (B × Hp H l)) : XMap H (LC B H l) where Φ := PhiC d q

section Banks
variable (base : OBase H) (l : H)
def BBC (g : Orth (LC B H l)) : OBase (LC B H l) :=
  ofCols (g.1 * blkC B l base) (mul_orth g.2 (blkC_orth base))
end Banks

def piF (l : H) (c : B) : LC B H l → LC B H l
  | .inl i => if h : i = l then .inl i else .inr (c, ⟨i, h⟩)
  | .inr (b, j) => if b = c then .inl j.1 else .inr (b, j)

def piC (l : H) (c : B) : Equiv.Perm (LC B H l) :=
  Function.Involutive.toPerm (piF l c) fun x => by
    rcases x with i | ⟨b, j, hj⟩
    · by_cases h : i = l <;> simp [piF, h]
    · by_cases h : b = c <;> simp [piF, h, hj]

@[simp] lemma piC_apply (c : B) (x : LC B H l) : piC l c x = piF l c x := rfl

lemma card_lt_LC (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) (s : Finset H) :
    s.card < Fintype.card (LC B H l) := by
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hH l
  have h1 : 0 < Fintype.card (B × Hp H l) :=
    Fintype.card_pos_iff.2 ⟨(Classical.choice (Fintype.card_pos_iff.1 hB), ⟨j, hj⟩)⟩
  have h2 := Finset.card_le_univ s
  rw [Fintype.card_sum]
  omega

lemma coord_BB (d : Orth (LC B H l)) (A : OBase H) (y : Space (LC B H l)) :
    (coordPerm (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A)))).π y =
      Sum.elim ((coordPerm A).π fun i => (d.1ᵀ *ᵥ y) (Sum.inl i)) fun b => (d.1ᵀ *ᵥ y) (Sum.inr b) := by
  have e : ∀ k, (coordPerm (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A)))).π y k =
      ((blkC B l A)ᵀ *ᵥ (d.1ᵀ *ᵥ y)) k := fun k => by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul]; rfl
  funext k
  rw [e]
  generalize d.1ᵀ *ᵥ y = w
  rcases k with i | b <;>
    simp only [blkC, Matrix.fromBlocks_transpose, Matrix.fromBlocks_mulVec, Sum.elim_inl, Sum.elim_inr,
      Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.add_apply,
      Pi.zero_apply, add_zero, zero_add] <;> rfl

lemma insub_BB (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (A : OBase H) (s : Finset H)
    (U : SubspaceLabel H) (h : ∀ x, U.Mem x ↔ InSub (coordPerm A) s x) (y : Space (LC B H l)) :
    InSub (coordPerm (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A)))) (JC s q) y ↔
      InSub (conjPerm d.1 d.2 (Orth.orth' d) U.G) (U.s.disjSum q) y := by
  have e : InSub (coordPerm (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A)))) (JC s q) y ↔
      InSub (coordPerm A) s (fun i => (d.1ᵀ *ᵥ y) (Sum.inl i)) ∧
        ∀ b, b ∉ q → (d.1ᵀ *ᵥ y) (Sum.inr b) = 0 := by
    unfold InSub
    rw [coord_BB]
    simp only [Sum.forall, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Sum.elim_inl, Sum.elim_inr]
  exact (e.trans (and_congr_left' (h _).symm)).trans (insub_conj d.1 d.2 (Orth.orth' d) U.G U.s q y).symm
end
end Window137
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving
namespace StageWin
open GenMove Window137 StageBox StageGauge RankCost RAM Finset Matrix Binary
noncomputable section
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H] {l : H}

theorem old_to_newC (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (A : OBase H) (s : Finset H)
    (U : SubspaceLabel H) (h : ∀ x, U.Mem x ↔ InSub (coordPerm A) s x) :
    GReach (PhiC d q (A.mat s)) ((LabelLift.ofConj d.1 d.2 (Orth.orth' d) q).Φ U) (fun _ => 0) :=
  fun _ _ _ r => by
    rw [PhiC_eq]
    obtain ⟨N1, hN1, e1⟩ := repChange_core _ _ _ _ (insub_BB d q A s U h)
    obtain ⟨-, N2, hN2, e2⟩ := frame_core (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A))) (JC s q)
    have := gstep_free (hN1.mul hN2) r
      (frame (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A))) (JC s q))
    rwa [Matrix.mul_assoc, ← e2, ← e1] at this

theorem new_to_oldC (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (A : OBase H) (s : Finset H)
    (U : SubspaceLabel H) (h : ∀ x, U.Mem x ↔ InSub (coordPerm A) s x) :
    GReach ((LabelLift.ofConj d.1 d.2 (Orth.orth' d) q).Φ U) (PhiC d q (A.mat s)) (fun _ => 0) :=
  fun _ _ _ r => by
    rw [PhiC_eq]
    obtain ⟨N1, hN1, e1⟩ := repChange_core _ _ _ _ fun y => (insub_BB d q A s U h y).symm
    obtain ⟨⟨N2, hN2, e2⟩, -⟩ := frame_core (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A))) (JC s q)
    have := gstep_free (hN2.mul hN1) r
      (coreFrame (conjPerm d.1 d.2 (Orth.orth' d) U.G) (U.s.disjSum q))
    rwa [Matrix.mul_assoc, ← e1, ← e2] at this

def window (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) (d : Orth (LC B H l))
    (q : Finset (B × Hp H l)) : Window H (LC B H l) where
  Xm := fmapC hB hH d q
  X := LabelLift.ofConj d.1 d.2 (Orth.orth' d) q
  big := by
    have h := card_lt_LC (l := l) hB hH (univ : Finset H)
    rwa [Finset.card_univ] at h
  toNew := fun A s U h => old_to_newC d q A s U h
  toOld := fun A s U h => new_to_oldC d q A s U h
end
end StageWin
end PowerSaving
end OAI

namespace OAI
namespace PowerSaving
namespace StageFrames
open Binary Matrix Finset RAM StageBox RankCost StageGauge Window137 StageWin GenMove
noncomputable section

variable {H T : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

def bs (k : ℕ) : Finset (Fin 16) := univ.filter (·.val < k)

lemma hB : 1 ≤ Fintype.card (Fin 16) := by simp

section
variable (l : H)

def setX : ℕ → Finset (LC (Fin 16) H l) | 0 => JC {l} ∅ | k+1 => JC univ (qC (bs k))
def setY : ℕ → Finset (LC (Fin 16) H l) | 0 => JC ∅ ∅   | k+1 => JC (univ \ {l}) (qC (bs k))
def incr : ℕ → Finset (LC (Fin 16) H l) | 0 => JC (univ \ {l}) ∅
                                        | k+1 => if h : k < 16 then JC ∅ (qC {(⟨k, h⟩ : Fin 16)}) else ∅

def piK : ℕ → Equiv.Perm (LC (Fin 16) H l)
  | 0 => 1
  | k+1 => if h : k + 1 ≤ 16 then piC l ⟨k, by omega⟩ else 1

lemma piK_succ (k : ℕ) (h : k + 1 ≤ 16) : piK l (k+1) = piC l ⟨k, by omega⟩ := dif_pos h

lemma incr_succ (k : ℕ) (h : k < 16) : incr l (k+1) = JC ∅ (qC {⟨k, h⟩}) := dif_pos h

macro "lcs" : tactic => `(tactic| ((first | ext (i | ⟨b, j, hj⟩) | (rw [disjoint_left]; rintro (i | ⟨b, j, hj⟩)) | rintro (i | ⟨b, j, hj⟩)) <;>
  simp_all [setX, setY, incr, JC, qC, bs, piK, piF, em, -singleton_product] <;>
  (try split_ifs) <;> (try simp_all) <;> (try simp_all [Fin.ext_iff]) <;> omega))

lemma setX_succ (k : ℕ) (hk : k < 17) : setX l (k+1) = setX l k ∪ incr l k ∧ Disjoint (setX l k) (incr l k) := by
  rcases k with _ | k <;> [skip; rw [incr_succ l k (by omega)]] <;> constructor <;> lcs

lemma setY_succ (k : ℕ) (hk : k < 17) : setY l (k+1) = setY l k ∪ incr l k ∧ Disjoint (setY l k) (incr l k) := by
  rcases k with _ | k <;> [skip; rw [incr_succ l k (by omega)]] <;> constructor <;> lcs

lemma setX_pivot (k : ℕ) (hk : k ≤ 17) : setX l k = setY l k ∪ {Sum.inl l} ∧ Disjoint (setY l k) {Sum.inl l} := by
  rcases k with _ | k <;> constructor <;> lcs

lemma setX_mono (a : ℕ) : ∀ b, a ≤ b → b ≤ 17 → setX l a ⊆ setX l b := by
  intro b hab hb
  induction b, hab using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact (ih (by omega)).trans ((setX_succ l n (by omega)).1 ▸ subset_union_left)

lemma setX_eq (k : ℕ) (hk : k ≤ 17) : setX l k = setY l k ∪ {Sum.inl l} := (setX_pivot l k hk).1

variable (hH : Fintype.card H = 9)
include hH

lemma card_LC137 : Fintype.card (LC (Fin 16) H l) = 137 := by
  simp [Fintype.card_subtype_compl, hH]

lemma card_incr (k : ℕ) (hk : k < 17) : (incr l k).card = 8 := by
  rcases k with _ | k
  · simp [incr, Fintype.card_subtype_compl, card_sdiff, hH]
  · simp [incr, qC, show k < 16 by omega, Fintype.card_subtype_compl, hH]

lemma card_setX : ∀ k, k ≤ 17 → (setX l k).card = 1 + 8 * k
  | 0, _ => by simp [setX]
  | k+1, hk => by
    rw [(setX_succ l k (by omega)).1, card_union_of_disjoint (setX_succ l k (by omega)).2,
      card_setX k (by omega), card_incr l hH k (by omega)]; ring

lemma card_setY : ∀ k, k ≤ 17 → (setY l k).card = 8 * k
  | 0, _ => by simp [setY]
  | k+1, hk => by
    rw [(setY_succ l k (by omega)).1, card_union_of_disjoint (setY_succ l k (by omega)).2,
      card_setY k (by omega), card_incr l hH k (by omega)]; ring

end

def window (l : H) (hH : Fintype.card H = 9) (n : ℕ) (d : Orth (LC (Fin 16) H l)) : Window H (LC (Fin 16) H l) :=
  StageWin.window hB (by omega) d (qC (bs n))

section
variable (base : T → OBase H) (l : H)

def gaugePerm (k : ℕ) (t : T) : Orth (LC (Fin 16) H l) ≃ Orth (LC (Fin 16) H l) :=
  Orth.conjPerm _ (blkC_orth (base t)) (piK l k)

variable (hH : Fintype.card H = 9)

lemma stage_gen (k : ℕ) (t : T) (g : Orth (LC (Fin 16) H l)) (S : Finset H) :
    (window l hH k (gaugePerm base l k t g)).Xm.Φ ((base t).mat S) =
      frame (BBC (base t) l g) ((JC S (qC (bs k))).map (piK l k).toEmbedding) := by
  show PhiC _ _ _ = _
  rw [PhiC_eq, frame_ofCols, BBC, frame_ofCols, gaugePerm, Orth.conjPerm_mul, submatrix_diagI]

lemma mem_piK (k : ℕ) (J : Finset (LC (Fin 16) H l)) (x : LC (Fin 16) H l) :
    x ∈ J.map (piK l k).toEmbedding ↔ piK l k x ∈ J := by
  rw [mem_map_equiv]; unfold piK; split <;> (try split) <;> rfl

lemma stage_Xin (k : ℕ) (hk : k ≤ 16) (t : T) (g : Orth (LC (Fin 16) H l)) :
    (window l hH k (gaugePerm base l k t g)).Xm.Φ (tt ((base t).v l)) = frame (BBC (base t) l g) (setX l k) := by
  rw [← mat_single, stage_gen]; congr 1
  ext x; rw [mem_piK]; revert x; rcases k with _ | k <;> [skip; rw [piK_succ l k hk]] <;> lcs

lemma stage_Xout (k : ℕ) (hk : k ≤ 16) (t : T) (g : Orth (LC (Fin 16) H l)) :
    (window l hH k (gaugePerm base l k t g)).Xm.Φ 1 = frame (BBC (base t) l g) (setX l (k + 1)) := by
  rw [← OBase.mat_univ (base t), stage_gen]; congr 1
  ext x; rw [mem_piK]; revert x; rcases k with _ | k <;> [skip; rw [piK_succ l k hk]] <;> lcs

lemma stage_Yin (k : ℕ) (hk : k ≤ 16) (t : T) (g : Orth (LC (Fin 16) H l)) :
    (window l hH k (gaugePerm base l k t g)).Xm.Φ 0 = frame (BBC (base t) l g) (setY l k) := by
  rw [← mat_empty (base t), stage_gen]; congr 1
  ext x; rw [mem_piK]; revert x; rcases k with _ | k <;> [skip; rw [piK_succ l k hk]] <;> lcs

lemma stage_Yout (k : ℕ) (hk : k ≤ 16) (t : T) (g : Orth (LC (Fin 16) H l)) :
    (window l hH k (gaugePerm base l k t g)).Xm.Φ (1 + tt ((base t).v l)) = frame (BBC (base t) l g) (setY l (k + 1)) := by
  rw [← mat_compl_single, stage_gen]; congr 1
  ext x; rw [mem_piK]; revert x; rcases k with _ | k <;> [skip; rw [piK_succ l k hk]] <;> lcs

end

end
end StageFrames
end PowerSaving
end OAI

private theorem marker_submission_work_g17_geom (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_submission_work_g17_lemmas (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

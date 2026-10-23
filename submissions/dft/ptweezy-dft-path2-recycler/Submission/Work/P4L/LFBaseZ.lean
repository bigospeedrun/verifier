import Submission.Work.P4L.CertGen
import Submission.Work.PWGen.S2979ZOne
import Submission.Work.Mixed.Bridge.Core
import Submission.Work.GCert.Chain.Geom
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P4-L-fresh on the #4470 patched #2979 provider S2979Z: the instance data

The instance of `P4L.wordCert` for the #4470 patched #2979 provider S2979Z (Route E) (`T = Fin 112` ports, `Sl = Fin 408` slots,
`C = Fin 8` copies, `H = Fin 9`, pivot `l0 = 0`), `G = |Γ0|`, `Γ0 = Orth (LC (Fin 8) (Fin 9) l0)` gauge copies:

* the provider `I1` (`PWGZ.ginvZ`), `hOk1`, `cost1`, `res1`, `res_sum`, `res_sumN`, `res_bounds` (residual ranks
  of the 408 slots: 326 of 9, 47 of 8, 7 of 7, 28 of 4);
* the end sets of the helpers: `D9` (nine axes, separated form), `Dr q` (residual rank, raw form);
* `G_pos`, `card_LC0`, `base_exists`.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace OAI
namespace PowerSaving
namespace P4L
namespace LFZ
open Binary Matrix Finset RAM SS CB RF BC GX GF XHostTW P4Ctrl

noncomputable section

/-! ### the provider -/

/-- the #4470 patched #2979 provider (`GXD.S2979Z`) as a windowed provider of the network. -/
def I1 : GInvW (Fin 9) (Fin 112) (Fin 408) (Fin 8) GXD.S2979Z.okW :=
  ⟨PWGZ.ginvZ.tv, PWGZ.ginvZ.hunit, PWGZ.ginvZ.hgap, PWGZ.ginvZ.cost, PWGZ.ginvZ.ent,
   PWGZ.ginvZ.fwd, PWGZ.ginvZ.bwd⟩

/-- every stage window of the network has a warp meaning (the leader's conjugation windows). -/
theorem hOk1 (l : Fin 9) (n : ℕ) (d : Orth (LC (Fin 8) (Fin 9) l)) :
    GXD.S2979Z.okW (win401N l (Fintype.card_fin 9) n d) := by
  unfold win401N
  split <;> exact GXD.S2979Z.okC _ _ _ _

/-- the price of one call (all gauge copies of one call cost `|Γ|` times this). -/
theorem cost1 (φ : ℕ → ℝ) :
    I1.cost φ = 2237 * φ 1 + 388 * φ 2 + 494 * φ 3 + 147 * φ 4 + 36 * φ 5 + 8 * φ 8 :=
  PWGZ.ginvZ_cost φ

/-- the residual rank of every slot. -/
theorem res1 (q : Fin 408) : Fintype.card (Fin 9) - (I1.ent q).dim = GXD.S2979Z.schedRes.getD q.val 0 :=
  GXD.S2979Z.hent q

lemma sum_range_getD {M : Type*} [AddCommMonoid M] (L : List ℕ) (g : ℕ → M) :
    ∑ i ∈ Finset.range L.length, g (L.getD i 0) = (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact add_comm _ _

lemma schedRes_length : GXD.S2979Z.schedRes.length = 408 := by decide +kernel

/-- the residual ranks of the 408 slots: 326 of 9, 47 of 8, 7 of 7, 28 of 4. -/
theorem res_sum (g : ℕ → ℝ) :
    ∑ q : Fin 408, g (GXD.S2979Z.schedRes.getD q.val 0)
      = 326 * g 9 + 47 * g 8 + 7 * g 7 + 28 * g 4 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => g (GXD.S2979Z.schedRes.getD i 0)) 408, ← schedRes_length,
    sum_range_getD]
  simp only [GXD.S2979Z.schedRes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- the same count in `ℕ`. -/
theorem res_sumN (g : ℕ → ℕ) :
    ∑ q : Fin 408, g (GXD.S2979Z.schedRes.getD q.val 0)
      = 326 * g 9 + 47 * g 8 + 7 * g 7 + 28 * g 4 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => g (GXD.S2979Z.schedRes.getD i 0)) 408, ← schedRes_length,
    sum_range_getD]
  simp only [GXD.S2979Z.schedRes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

lemma schedRes_bounds : ∀ i < 408, 4 ≤ GXD.S2979Z.schedRes.getD i 0 ∧ GXD.S2979Z.schedRes.getD i 0 ≤ 9 := by
  decide +kernel

lemma res_bounds (q : Fin 408) :
    4 ≤ GXD.S2979Z.schedRes.getD q.val 0 ∧ GXD.S2979Z.schedRes.getD q.val 0 ≤ 9 :=
  schedRes_bounds q.val q.isLt

/-! ### the instance -/

/-- the pivot of the instance. -/
abbrev l0 : Fin 9 := 0

/-- the gauge copies. -/
abbrev Γ0 : Type := Orth (LC (Fin 8) (Fin 9) l0)

/-- the roles and the live roles of the instance. -/
abbrev ρ0 : Type := PRole Γ0 (Fin 112) (Fin 408) (Fin 8)
abbrev σ0 : Type := PLive Γ0 (Fin 112) (Fin 408)

/-- the nine axes on which every helper ends in the separated form. -/
def D9 : Finset (LC (Fin 8) (Fin 9) l0) := setX l0 1

lemma card_D9 : D9.card = 9 := by
  rw [D9, card_setX l0 (Fintype.card_fin 9) 1 (by norm_num)]

lemma res_le (q : Fin 408) : Fintype.card (Fin 9) - (I1.ent q).dim ≤ D9.card := by
  rw [card_D9, Fintype.card_fin]
  omega

/-- the raw end set of slot `q`: `card H - dim (ent q)` of the nine axes. -/
def Dr (q : Fin 408) : Finset (LC (Fin 8) (Fin 9) l0) :=
  Classical.choose (Finset.exists_subset_card_eq (res_le q))

lemma Dr_card (q : Fin 408) : (Dr q).card = Fintype.card (Fin 9) - (I1.ent q).dim :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (res_le q))).2

lemma Dr_res (q : Fin 408) : (Dr q).card = GXD.S2979Z.schedRes.getD q.val 0 := (Dr_card q).trans (res1 q)

lemma card_LC0 : Fintype.card (LC (Fin 8) (Fin 9) l0) = 73 := card_LC73 l0 (Fintype.card_fin 9)

lemma G_pos : 1 ≤ Fintype.card Γ0 :=
  Fintype.card_pos_iff.mpr ⟨⟨1, by rw [Matrix.transpose_one, Matrix.one_mul]⟩⟩

lemma base_exists : ∃ base : Fin 112 → OBase (Fin 9), ∀ t, I1.tv t = (base t).v l0 := by
  have hb : ∀ t, ∃ A : OBase (Fin 9), I1.tv t = A.v l0 :=
    fun t => base_ex (I1.tv t) (I1.hunit t) (I1.hgap t) l0
  choose base hbase using hb
  exact ⟨base, hbase⟩

end
end LFZ
end P4L
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P4L.LFZ.res_sum
#print axioms OAI.PowerSaving.P4L.LFZ.Dr_res

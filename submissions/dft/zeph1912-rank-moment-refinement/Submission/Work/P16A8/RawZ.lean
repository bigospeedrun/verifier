import Submission.Work.P16A8.CertGen
import Submission.Work.P4L.LFBaseZ
-- changed for the tensor-power extension (30103/10000000); see Submission.lean

/-!
# P16A8 (p16a8), RAW certificate on the #4470 patched #2979 provider S2979Z (Route E) (18-stage geometry G18): `rawCert_exists`

`certGen` (generic) on the geometry `G18` (`LC (Fin 17) (Fin 9) l0`, dimension 145) with the raw end sets `Dr q`
(`|Dr q|` = the residual rank of slot `q`, inside the nine axes `G18.setX l0 1`): every helper ends at the block of its
residual rank, every window is ONE block per owner, every thin query ONE rank-1 block per port.  The provider is
`P4L.LFZ.I1` (the #4470 patched #2979 word S2979Z); every stage window `G18.winN` is a conjugation window `gwinC`, which has a warp
meaning (`hOkN`, `WS.WLift.ofConj`, as `GXD.S2979Z.okC` for the #401 geometry).  Per gauge copy
(`G = |Orth (LC (Fin 17) (Fin 9) l0)|` copies): live target ranks `Traw` = [(4, 504), (7, 126), (8, 846), (9, 5868), (17, 448), (25, 448), (33, 448), (41, 448), (49, 448), (57, 448), (65, 448), (73, 224), (145, 224)], paid blocks `Praw` = [(1, 41946), (2, 6984), (3, 8892), (4, 2646), (5, 648), (8, 144), (16, 448), (24, 448), (32, 448), (40, 448), (48, 448), (56, 448), (64, 448), (72, 224)]
(literally the tensor route's `TensorProto.P16A8.TP16A8`, `PPP16A8` for p16a8).  The instance only proves the one-copy facts
`hP_raw` (price) and `hL_raw` (targets); the gauge group is a factor of `certGen`, never reduced.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace P16A8
namespace Z
open Binary Matrix Finset RAM SS CB RF BC GX GF XHostTW

set_option maxRecDepth 100000
noncomputable section

/-! ### the geometry-dependent instance data -/

/-- every stage window of the 18-stage network has a warp meaning (the leader's conjugation windows). -/
theorem hOkN (l : Fin 9) (n : ℕ) (d : Orth (LC (Fin 17) (Fin 9) l)) :
    GXD.S2979Z.okW (G18.winN l (Fintype.card_fin 9) n d) := by
  unfold G18.winN
  split <;> exact ⟨OAI.PowerSaving.WS.WLift.ofConj _ _ (RF.Orth.orth' _) _⟩

/-- the nine axes of the pivot block. -/
def D9 : Finset (LC (Fin 17) (Fin 9) P4L.LFZ.l0) := G18.setX P4L.LFZ.l0 1

lemma card_D9 : D9.card = 9 := by
  rw [D9, G18.card_setX P4L.LFZ.l0 (Fintype.card_fin 9) 1 (by norm_num)]

lemma res_le (q : Fin 408) : Fintype.card (Fin 9) - (P4L.LFZ.I1.ent q).dim ≤ D9.card := by
  rw [card_D9, Fintype.card_fin]
  omega

/-- the raw end set of slot `q`: `card H - dim (ent q)` of the nine axes. -/
def Dr (q : Fin 408) : Finset (LC (Fin 17) (Fin 9) P4L.LFZ.l0) :=
  Classical.choose (Finset.exists_subset_card_eq (res_le q))

lemma Dr_card (q : Fin 408) : (Dr q).card = Fintype.card (Fin 9) - (P4L.LFZ.I1.ent q).dim :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (res_le q))).2

lemma Dr_res (q : Fin 408) : (Dr q).card = GXD.S2979Z.schedRes.getD q.val 0 :=
  (Dr_card q).trans (P4L.LFZ.res1 q)

lemma card_LC0 : Fintype.card (LC (Fin 17) (Fin 9) P4L.LFZ.l0) = 145 := G18.card_LC145 P4L.LFZ.l0 (Fintype.card_fin 9)

/-! ### the one-copy facts -/

/-- the paid blocks of the raw word (per gauge copy). -/
def Praw : List (ℕ × ℕ) := [(1, 41946), (2, 6984), (3, 8892), (4, 2646), (5, 648), (8, 144), (16, 448), (24, 448), (32, 448), (40, 448), (48, 448), (56, 448), (64, 448), (72, 224)]

/-- the live target ranks of the raw word (per gauge copy). -/
def Traw : List (ℕ × ℕ) := [(4, 504), (7, 126), (8, 846), (9, 5868), (17, 448), (25, 448), (33, 448), (41, 448), (49, 448), (57, 448), (65, 448), (73, 224), (145, 224)]

/-- one gauge copy of the raw price. -/
lemma hP_raw (φ : ℕ → ℝ) :
    18 * P4L.LFZ.I1.cost φ + (Fintype.card (Fin 112) : ℝ) * portCost φ
      + 18 * ∑ q, bcost φ ((Dr q).card - (Fintype.card (Fin 9) - (P4L.LFZ.I1.ent q).dim)) = listCost φ Praw := by
  rw [P4L.LFZ.cost1]
  simp only [Dr_card, Nat.sub_self, bcost_zero, Finset.sum_const_zero, mul_zero, add_zero, Fintype.card_fin]
  simp only [portCost, listCost, Praw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bcost, Nat.cast_ofNat]
  norm_num
  ring

/-- one gauge copy of the raw targets: 112 main roles per kind, the helpers per slot. -/
lemma hL_raw (r : ℕ) :
    ∑ i, Fintype.card (Fin 112) * (if rankM i = r then 1 else 0) + 18 * ∑ q, (if (Dr q).card = r then 1 else 0)
      = BlockAccounting.histFn Traw r := by
  simp only [Dr_res, Fintype.card_fin]
  rw [P4L.LFZ.res_sumN (fun x => if x = r then 1 else 0), R32_sum]
  rcases (show r = 4 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 17 ∨ r = 25 ∨ r = 33 ∨ r = 41 ∨ r = 49 ∨ r = 57 ∨ r = 65 ∨ r = 73 ∨ r = 145 ∨
      (r ≠ 4 ∧ r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 17 ∧ r ≠ 25 ∧ r ≠ 33 ∧ r ≠ 41 ∧ r ≠ 49 ∧ r ≠ 57 ∧ r ≠ 65 ∧ r ≠ 73 ∧ r ≠ 145) by omega) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | ⟨h4, h7, h8, h9, h17, h25, h33, h41, h49, h57, h65, h73, h145⟩
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · simp [rankM, Traw, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil,
      h4, h7, h8, h9, h17, h25, h33, h41, h49, h57, h65, h73, h145, Ne.symm h4, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h17, Ne.symm h25, Ne.symm h33, Ne.symm h41, Ne.symm h49, Ne.symm h57, Ne.symm h65, Ne.symm h73, Ne.symm h145]

/-- the raw target ranks lie in `[1, 145]`. -/
lemma rank_raw (base : Fin 112 → OBase (Fin 9)) (l' : PLive (Orth (LC (Fin 17) (Fin 9) P4L.LFZ.l0)) (Fin 112) (Fin 408)) :
    1 ≤ (rawTz base P4L.LFZ.l0 Dr l').1 ∧ (rawTz base P4L.LFZ.l0 Dr l').1 ≤ 145 := by
  rcases l' with ⟨g, i, t⟩ | ⟨g, k, q⟩
  · rw [rawTz_main base P4L.LFZ.l0 (Fintype.card_fin 9) Dr g i t]
    cases i <;> simp [rankM]
  · rw [rawTz_fresh base P4L.LFZ.l0 Dr g k q, Dr_res q]
    have := P4L.LFZ.res_bounds q
    omega

/-- **The raw p16a8 certificate** (no pad, no split): `G` copies of the raw unit, in the shape the tensor route
takes (targets `G * Traw`, paid blocks `G * Praw`). -/
theorem rawCert_exists : ∃ (α ρ σ : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Fintype ρ)
    (_ : DecidableEq ρ) (_ : Fintype σ) (_ : DecidableEq σ),
    ∃ (e : σ → ρ) (tr : σ → ℕ) (tz : ∀ l, Fin (tr l) → Space α) (wd : GWord α ρ) (G : ℕ),
      Function.Injective e ∧ (∀ l, LinearIndependent F (tz l)) ∧ wd.Proper (Fintype.card α) ∧
      MX.GLiveKernelM e (fun l => blockMat (tz l)) wd ∧
      1 ≤ G ∧ Fintype.card α = 145 ∧
      (∀ l, 1 ≤ tr l ∧ tr l ≤ 145) ∧
      (∀ r, (Finset.univ.filter fun l => tr l = r).card = G * BlockAccounting.histFn Traw r) ∧
      (∀ r, wd.hist r = G * BlockAccounting.histFn Praw r) := by
  obtain ⟨base, hbase⟩ := P4L.LFZ.base_exists
  obtain ⟨wd, hP, hk, hh, hc⟩ := certGen (I := P4L.LFZ.I1) (base := base) (l := P4L.LFZ.l0) (hbase := hbase)
    (hH := Fintype.card_fin 9) (hOk := hOkN P4L.LFZ.l0) (C := Fin 8) Dr (fun q => (Dr_card q).ge)
    (fun q => by rw [Dr_card q, Nat.sub_self, card_LC0]; norm_num) Praw Traw hP_raw hL_raw
  refine ⟨LC (Fin 17) (Fin 9) P4L.LFZ.l0, PRole (Orth (LC (Fin 17) (Fin 9) P4L.LFZ.l0)) (Fin 112) (Fin 408) (Fin 8),
    PLive (Orth (LC (Fin 17) (Fin 9) P4L.LFZ.l0)) (Fin 112) (Fin 408), _, _, _, _, _, inferInstance, Sum.inl,
    fun l' => (rawTz base P4L.LFZ.l0 Dr l').1, fun l' => (rawTz base P4L.LFZ.l0 Dr l').2, wd, _, Sum.inl_injective,
    fun l' => rawTz_indep base P4L.LFZ.l0 Dr l', hP, hk, ?_, card_LC0, rank_raw base, hc, hh⟩
  exact Orth.card_pos

end
end Z
end P16A8
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P16A8.Z.hOkN
#print axioms OAI.PowerSaving.P16A8.Z.rawCert_exists

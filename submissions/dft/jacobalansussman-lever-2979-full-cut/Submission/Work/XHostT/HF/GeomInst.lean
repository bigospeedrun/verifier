import Submission.Work.XHostT.TGeom
import Submission.Work.XHostT.HF.Heads
import Submission.Work.XHostT.HF.GeomA4

/-!
# (key: heads-first) The heads-first certificate of p-a3's GEOMETRIC network `xnetGeom` (the #3945 platform)

For ANY cross-replica host schedule `S` that fits (p-a3's `HostSchedT`, `fits`; the #3945 table is one), and any set
`hb` of A4 bins that no slot is hosted in and whose remaining climb is 48:
* `zGeom`: the head directions on every live role (the 48 A4 lines `a4Lines` of the role's frame `a4Base`);
* `xnetGeom_heads_first`: `GLiveKernel Sum.inl (headWord Sum.inl (headsL hb) (fun _ => 48) zGeom _ ++ body)`, `body`
  proper, `body` price `card Γ * unitPriceT Ic S - |headsL hb| * φ 48` for every price list;
* `headBins S`: the canonical head set (remaining climb 48, nothing hosted), for which both conditions hold by
  definition (`xnetGeom_heads_first_auto`);
* `cutA`, `cutS`, `bph_cut`: the frame and the 24 cut lines of each head, in the form e-r45m1's `MX.cut_heads_half`
  takes (`xnetGeom_cut_half`: the whole chain to the half-cut mixed certificate, the test of the interface).
Written by p-hfirst (wht45/lever, 19 Oct 2026) on p-a3's Work/XHostT/TGeom.lean; prepared with assistance from Claude.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace OAI
namespace PowerSaving
namespace XHostT
open Binary Matrix Finset RAM SS CB RF BR GF GX BC B401 XHost XHostR XHostD
noncomputable section

section Inst
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}

/-- the head directions on every live role of the geometric network (`nb = 0`: no banks): the A4 lines of the role's
class and gauge (only the head roles' values matter). -/
def zGeom (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) :
    BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → Fin 48 → Space (BC.LC (Fin 8) H l)
  | Sum.inl (_, d) => a4Dir base l hH (dDecD d).2.2.1 ((dDecD d).2.1, (dDecD d).2.2.2)
  | Sum.inr (_, b) => b.elim0

lemma zGeom_indep (base : T → OBase H) (l : H) (hH : Fintype.card H = 9)
    (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR) : LinearIndependent F (zGeom base l hH r) := by
  rcases r with (⟨_, d⟩ | ⟨_, b⟩)
  · exact a4Dir_indep base l hH _ _
  · exact b.elim0

lemma zGeom_head (base : T → OBase H) (l : H) (hH : Fintype.card H = 9) (ρ : Fin nR)
    (g : Orth (BC.LC (Fin 8) H l)) (j : Bool × T) : zGeom base l hH (hroleT ρ g j) = a4Dir base l hH g j := by
  obtain ⟨s, t⟩ := j
  cases s <;> rfl

/-- the canonical head bins of a schedule: A4 bins with remaining climb 48 in which no slot is hosted. -/
def headBins (S : HostSchedT nR Sl T) : Finset (Fin nR × Bool × T) :=
  Finset.univ.filter (fun p => S.hrem p.1 4 p.2 = 48 ∧ ∀ ρ l q, S.host ρ l q ≠ (p.1, 4, p.2))

lemma headBins_unh (S : HostSchedT nR Sl T) (ρ : Fin nR) (l : Fin 9) (q : Sl) (ρh : Fin nR) (j : Bool × T)
    (h : (ρh, j) ∈ headBins S) : S.host ρ l q ≠ (ρh, 4, j) :=
  (Finset.mem_filter.mp h).2.2 ρ l q

lemma headBins_48 (S : HostSchedT nR Sl T) (ρ : Fin nR) (j : Bool × T) (h : (ρ, j) ∈ headBins S) :
    S.hrem ρ 4 j = 48 :=
  (Finset.mem_filter.mp h).2.1

/-- with positive residuals, the head bins are exactly the A4 bins whose remaining climb is 48 (a fitting schedule
hosts nothing there): the head COUNT is then read off the remainders alone. -/
lemma headBins_eq (S : HostSchedT nR Sl T) (res : Fin nR → Fin 9 → Sl → ℕ) (hfit : S.fits res)
    (hpos : ∀ ρ l q, 0 < res ρ l q) :
    headBins S = Finset.univ.filter (fun p : Fin nR × Bool × T => S.hrem p.1 4 p.2 = 48) := by
  ext ⟨ρh, j⟩
  simp only [headBins, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun ρ l q e => ?_⟩
    have hf := hfit ρh 4 j
    rw [h] at hf
    have h48 : rankOf (4 : Fin 9).val = 48 := rfl
    have hl : S.load res ρh 4 j = 0 := by omega
    have hmem : (ρ, l, q) ∈ (Finset.univ : Finset (Fin nR × Fin 9 × Sl)).filter
        (fun p => S.host p.1 p.2.1 p.2.2 = (ρh, 4, j)) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e⟩
    have hle : res ρ l q ≤ S.load res ρh 4 j := by
      unfold HostSchedT.load
      exact Finset.single_le_sum (f := fun p : Fin nR × Fin 9 × Sl => res p.1 p.2.1 p.2.2)
        (fun _ _ => Nat.zero_le _) hmem
    have hp := hpos ρ l q
    omega

variable (I : GInvE H T Sl C) (Ic : Fin nR → Fin 9 → GInvE H T Sl C) (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv)
  (base : T → OBase H) (l : H) (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H = 9)
  (S : HostSchedT nR Sl T) (hfit : S.fits (resIc Ic))

/-- the unit price of the geometric network is p-a3's `unitPriceT` (the step `e` of `bridgeHostT_gcert`). -/
lemma xnetGeom_unit (φ : ℕ → ℝ) : (xnetGeom I Ic hIc base l hbase hH S hfit).unit φ = unitPriceT Ic S φ := by
  simp only [XNet.unit, XNet.callU, Finset.sum_add_distrib, sum_tailU, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, unitPriceT]
  simp only [XNet.hcost, hcostT, xnetGeom, bcost_zero, add_zero, mul_zero, Finset.sum_const_zero]

include I hIc hbase hfit in
/-- **THE HEADS-FIRST CERTIFICATE OF THE GEOMETRIC NETWORK.** -/
theorem xnetGeom_heads_first (hb : Finset (Fin nR × Bool × T))
    (hunh : ∀ ρ l' q ρh j, (ρh, j) ∈ hb → S.host ρ l' q ≠ (ρh, 4, j))
    (h48 : ∀ ρ j, (ρ, j) ∈ hb → S.hrem ρ 4 j = 48) :
    ∃ body : GWord (BC.LC (Fin 8) H l) (BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR),
      body.Proper (Fintype.card (BC.LC (Fin 8) H l)) ∧
      (∀ φ, body.costR φ = (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceT Ic S φ
          - ((headsL (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) hb).length : ℝ) * φ 48) ∧
      GLiveKernel (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
        (MX.headWord Sum.inl (headsL hb) (fun _ => 48) (zGeom base l hH) (zGeom_indep base l hH) ++ body) := by
  have hz : ∀ ρ j, (ρ, j) ∈ hb → ∀ g, GReach (blockMat (zGeom base l hH (hroleT ρ g j))
      * (xnetGeom I Ic hIc base l hbase hH S hfit).x0A4 g j)
      ((xnetGeom I Ic hIc base l hbase hH S hfit).x1A4 g j) (fun _ => 0) := by
    intro ρ j _ g
    rw [zGeom_head]
    obtain ⟨s, t⟩ := j
    cases s
    · exact a4_head_geom I base l hbase hH g (false, t)
    · exact a4_head_geom I base l hbase hH g (true, t)
  obtain ⟨body, hP, hc, hk⟩ := (xnetGeom I Ic hIc base l hbase hH S hfit).heads_first hb
    (fun ρ l' q ρh j hj h => hunh ρ l' q ρh j hj (Option.some_injective _ h)) h48
    (zGeom base l hH) (zGeom_indep base l hH) hz
  refine ⟨body, hP, fun φ => ?_, hk⟩
  rw [hc φ, xnetGeom_unit]

include I hIc hbase hfit in
/-- the same for the canonical head set `headBins S` (no hypothesis left). -/
theorem xnetGeom_heads_first_auto :
    ∃ body : GWord (BC.LC (Fin 8) H l) (BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR),
      body.Proper (Fintype.card (BC.LC (Fin 8) H l)) ∧
      (∀ φ, body.costR φ = (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceT Ic S φ
          - ((headsL (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) (headBins S)).length : ℝ) * φ 48) ∧
      GLiveKernel (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
        (MX.headWord Sum.inl (headsL (headBins S)) (fun _ => 48) (zGeom base l hH) (zGeom_indep base l hH) ++ body) :=
  xnetGeom_heads_first I Ic hIc base l hbase hH S hfit (headBins S) (headBins_unh S) (headBins_48 S)

/-! ## The cut data of the heads, for e-r45m1's `MX.cut_heads_half` (a = b = 24) -/

/-- the 24 cut lines of the head of side `s`: the first 24 of `a4Lines` in `OBase.fam` order. -/
def cutLines (l : H) (hH : Fintype.card H = 9) (s : Bool) : Finset (BC.LC (Fin 8) H l) :=
  Finset.univ.map ⟨fun i : Fin 24 => ((a4Lines l s).equivFin.symm (Fin.cast (a4Lines_card hH l s).symm
      (Fin.castAdd 24 i))).1,
    fun i j hij => Fin.castAdd_injective 24 24 (Fin.cast_injective _
      ((a4Lines l s).equivFin.symm.injective (Subtype.ext hij)))⟩

/-- the frame of every live role (only head roles matter): `a4Base` of its class and gauge. -/
def cutA (base : T → OBase H) (l : H) :
    BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → OBase (BC.LC (Fin 8) H l)
  | Sum.inl (_, d) => a4Base base l (dDecD d).2.2.1 (dDecD d).2.2.2
  | Sum.inr (_, b) => b.elim0

/-- the 24 cut lines of every live role (only head roles matter). -/
def cutS (l : H) (hH : Fintype.card H = 9) :
    BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → Finset (BC.LC (Fin 8) H l)
  | Sum.inl (_, d) => cutLines l hH (dDecD d).2.1
  | Sum.inr (_, b) => b.elim0

/-- **the `hz` of `MX.cut_heads_half`**: the first 24 directions of each head are lines of its frame. -/
lemma bph_cut (hb : Finset (Fin nR × Bool × T)) (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR)
    (hr : r ∈ headsL (nb := 0) hb) (x : Space (BC.LC (Fin 8) H l)) :
    MX.bph (MX.partA (a := 24) (b := 24) (zGeom base l hH) r) x = MX.bph ((cutA base l r).fam (cutS l hH r)) x := by
  obtain ⟨p, -, g, rfl⟩ := (mem_headsL hb r).1 hr
  obtain ⟨ρ, s, t⟩ := p
  cases s
  · exact MX.bph_partA_fam (a := 24) (b := 24) (a4Base base l g t) (a4Lines l false) (a4Lines_card hH l false) x
  · exact MX.bph_partA_fam (a := 24) (b := 24) (a4Base base l g t) (a4Lines l true) (a4Lines_card hH l true) x

include I hIc hbase hfit in
/-- **the interface test**: the heads-first certificate of the geometric network fed into e-r45m1's half cut gives
the mixed certificate with targets `blockMat (cutTgt ..)` (rank 49 on the heads, 73 elsewhere). -/
theorem xnetGeom_cut_half (hb : Finset (Fin nR × Bool × T))
    (hunh : ∀ ρ l' q ρh j, (ρh, j) ∈ hb → S.host ρ l' q ≠ (ρh, 4, j))
    (h48 : ∀ ρ j, (ρ, j) ∈ hb → S.hrem ρ 4 j = 48) :
    ∃ body : GWord (BC.LC (Fin 8) H l) (BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR),
      body.Proper (Fintype.card (BC.LC (Fin 8) H l)) ∧
      (∀ φ, body.costR φ = (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPriceT Ic S φ
          - ((headsL (Γ := Orth (BC.LC (Fin 8) H l)) (nb := 0) hb).length : ℝ) * φ 48) ∧
      MX.GLiveKernelM (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
        (fun r => blockMat (MX.cutTgt (headsL hb) (cutA base l) (cutS l hH) r).2)
        ((MX.headWord Sum.inl (headsL hb) (fun _ => 24) (MX.partB (a := 24) (zGeom base l hH))
            (MX.partB_indep (zGeom_indep base l hH)) ++ body)
          ++ MX.shiftWord Sum.inl (headsL hb) (MX.cutShift (cutA base l) (cutS l hH))) := by
  obtain ⟨body, hP, hc, hk⟩ := xnetGeom_heads_first I Ic hIc base l hbase hH S hfit hb hunh h48
  exact ⟨body, hP, hc, MX.cut_heads_half Sum.inl_injective (headsL hb) (headsL_nodup hb) (a := 24) (b := 24)
    (zGeom base l hH) (zGeom_indep base l hH) (cutA base l) (cutS l hH)
    (fun r hr x => bph_cut base l hH hb r hr x) body hk⟩

/-- the cut target has rank 49 on every head role. -/
lemma cutTgt_rank_head (hb : Finset (Fin nR × Bool × T)) (r : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR)
    (hr : r ∈ headsL (nb := 0) hb) : (MX.cutTgt (headsL hb) (cutA base l) (cutS l hH) r).1 = 49 := by
  rw [MX.cutTgt_rank, if_pos hr, card_LC401 l hH]
  obtain ⟨p, -, g, rfl⟩ := (mem_headsL hb r).1 hr
  obtain ⟨ρ, s, t⟩ := p
  cases s
  · show 73 - (cutLines l hH false).card = 49
    rw [cutLines, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · show 73 - (cutLines l hH true).card = 49
    rw [cutLines, Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Inst
end
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.xnetGeom_unit
#print axioms OAI.PowerSaving.XHostT.xnetGeom_heads_first
#print axioms OAI.PowerSaving.XHostT.xnetGeom_heads_first_auto
#print axioms OAI.PowerSaving.XHostT.bph_cut
#print axioms OAI.PowerSaving.XHostT.xnetGeom_cut_half
#print axioms OAI.PowerSaving.XHostT.cutTgt_rank_head
#print axioms OAI.PowerSaving.XHostT.headBins_eq

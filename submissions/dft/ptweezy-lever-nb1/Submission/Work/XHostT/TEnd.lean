import Submission.Work.XHostT.TGeom

/-!
# (key: bridge-host-cross) THE END THEOREMS for the CROSS-REPLICA hosted nine-stage word

lg-a2a4's Work/XHostD/HEnd.lean (after Shea's Work/Bridge401/End.lean and Jacob Sussman's Work/Bridge377/End.lean) with
`bridgeHostT_gcert` in the place of `bridgeHost_gcert`: a gauged invocation package with one provider word per call,
a cross-replica host schedule and a rate fact give the Walsh-Hadamard / kernel program (the form OpenAI's Fourier proof
uses).  The live roles are the data of the `nR` replicas: `card BLiveT Γ T 0 nR = card Γ * (8 nR card T)`, so the
width is `W = 8 nR card T` (no banks).  Unit price `unitPriceT Ic S`.
Written by p-a3 (wht45/lever, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace XHostT
open Binary Matrix Finset RAM RAM.Ty SS CB RF BR BG GF FoldRate GX XHost XHostR XHostD
noncomputable section

universe U

lemma card_BLiveT {Γ T : Type} [Fintype Γ] [Fintype T] (nb nR : ℕ) :
    Fintype.card (BLiveT Γ T nb nR) = Fintype.card Γ * (8 * nR * Fintype.card T + nb) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

section End
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {nR : ℕ}

/-- **Walsh-Hadamard transform from a gauged invocation package (one provider word per call), a cross-replica host
schedule and a rate fact.** -/
theorem wht_of_ginv_hostT (I : GInvE H T Sl C) (Ic : Fin nR → Fin 9 → GInvE H T Sl C)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (hH : Fintype.card H = 9) (S : HostSchedT nR Sl T)
    (hfit : S.fits (resIc Ic))
    (u W : ℕ) (hu : 73 = u)
    (hW : 8 * nR * Fintype.card T = W) (hW1 : 1 ≤ W)
    (U : List (ℕ × ℕ))
    (hU : ∀ φ : ℕ → ℝ, unitPriceT Ic S φ = listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ BlockWHT.WHTTimeBoundsAt z W' := by
  obtain ⟨l⟩ : Nonempty H := Fintype.card_pos_iff.mp (by omega)
  exact BlockWHT.wht_main_of_ggroup_list u (by rw [BC.card_LC, hH, Fintype.card_fin]; omega) (by omega)
    (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
    Sum.inl_injective (Fintype.card (Orth (BC.LC (Fin 8) H l))) W Orth.card_pos hW1
    (by rw [card_BLiveT, ← hW, Nat.add_zero])
    _ (bridgeHostT_gcert I Ic hIc hH l S hfit) U (fun φ => by rw [hU φ]) s z hz hz1 hnum

/-- **Kernel program from a gauged invocation package, a cross-replica host schedule and a rate fact**: the form that
OpenAI's Fourier proof uses (`hills_program`), as `XHostD.engine_of_ginv_host`. -/
theorem engine_of_ginv_hostT (I : GInvE H T Sl C) (Ic : Fin nR → Fin 9 → GInvE H T Sl C)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (hH : Fintype.card H = 9) (S : HostSchedT nR Sl T)
    (hfit : S.fits (resIc Ic))
    (u W : ℕ) (hu : 73 = u)
    (hW : 8 * nR * Fintype.card T = W) (hW1 : 1 ≤ W)
    (U : List (ℕ × ℕ))
    (hU : ∀ φ : ℕ → ℝ, unitPriceT Ic S φ = listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  obtain ⟨l⟩ : Nonempty H := Fintype.card_pos_iff.mp (by omega)
  exact engine_program_ggroup_list u (by rw [BC.card_LC, hH, Fintype.card_fin]; omega) (by omega)
    (Sum.inl : BLiveT (Orth (BC.LC (Fin 8) H l)) T 0 nR → BRoleT (Orth (BC.LC (Fin 8) H l)) T 0 C nR)
    Sum.inl_injective (Fintype.card (Orth (BC.LC (Fin 8) H l))) W Orth.card_pos hW1
    (by rw [card_BLiveT, ← hW, Nat.add_zero])
    _ (bridgeHostT_gcert I Ic hIc hH l S hfit) U (fun φ => by rw [hU φ]) s z hz hz1 hnum cl m k v

end End
end
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.wht_of_ginv_hostT
#print axioms OAI.PowerSaving.XHostT.engine_of_ginv_hostT

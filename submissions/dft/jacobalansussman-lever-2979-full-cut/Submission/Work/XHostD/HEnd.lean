import Submission.Work.XHostD.HGeom

/-!
# (key: bridge-host) THE END THEOREMS for the HOSTED nine-stage word: gauged invocation package + host schedule + rate
fact => Walsh-Hadamard / kernel program (the form OpenAI's Fourier proof uses)

Copy of Work/Bridge401/End.lean (Ryan Shea's complex588 tree, written by DFT Lean (#401 L4) after Jacob Sussman's
Work/Bridge377/End.lean) with `bridgeHost_gcert` in the place of `bridge401_gcert` and the unit price
`unitPriceHost Ic S φ = Σ_ρ Σ_l (Ic ρ l).cost φ + Σ_ρ Σ_c Σ_t (bcost (hrem ρ c (X,t)) + bcost (hrem ρ c (Y,t))) + Σ_b bcost (pad b)`.
Hosting: DaysSky (CrocSwap/integer-mult-bounds PR #442).  Written by h-L3-build (wht43, 13 Oct 2026), prepared with
assistance from Claude.  PER-RUN version (one host table per run) written by fsp-perrun/tools/mk_perrun.py (wht43, 14 Oct 2026) from h-L3-build's file by checked text substitution; prepared with assistance from Claude.  TWO-PROVIDER version (a per-call invocation `Ic ρ l` with the target vectors of `I`, per-call entrance labels and residuals) written by lg-a2a4/tools/mk_disp.py (wht43, 14 Oct 2026) from fsp-perrun's file by checked text substitution; prepared with assistance from Claude.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace XHostD
open Binary Matrix Finset RAM RAM.Ty SS CB RF BR BG GF FoldRate GX XHost XHostR
noncomputable section

universe U

section End
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **Walsh-Hadamard transform from a gauged invocation package, a host schedule and a rate fact.** -/
theorem wht_of_ginv_host (I : GInvE H T Sl C) (Ic : Fin 8 → Fin 9 → GInvE H T Sl C)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (hH : Fintype.card H = 9) (S : HostSchedR Sl T)
    (hfit : fitsRK S (rK Ic))
    (u W : ℕ) (hu : 73 = u)
    (hW : 64 * Fintype.card T + S.nb = W) (hW1 : 1 ≤ W)
    (U : List (ℕ × ℕ))
    (hU : ∀ φ : ℕ → ℝ, unitPriceHost Ic S φ = listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ BlockWHT.WHTTimeBoundsAt z W' := by
  obtain ⟨l⟩ : Nonempty H := Fintype.card_pos_iff.mp (by omega)
  exact BlockWHT.wht_main_of_ggroup_list u (by rw [BC.card_LC, hH, Fintype.card_fin]; omega) (by omega)
    (Sum.inl : BLive401 (Orth (BC.LC (Fin 8) H l)) T S.nb → BRole401 (Orth (BC.LC (Fin 8) H l)) T S.nb C)
    Sum.inl_injective (Fintype.card (Orth (BC.LC (Fin 8) H l))) W Orth.card_pos hW1 (by rw [card_BLive401, hW])
    _ (bridgeHost_gcert I Ic hIc hH l S hfit) U (fun φ => by rw [hU φ]) s z hz hz1 hnum

/-- **Kernel program from a gauged invocation package, a host schedule and a rate fact**: the form that OpenAI's
Fourier proof uses (`hills_program`), as `GX.engine_of_ginv_401`. -/
theorem engine_of_ginv_host (I : GInvE H T Sl C) (Ic : Fin 8 → Fin 9 → GInvE H T Sl C)
    (hIc : ∀ ρ l, (Ic ρ l).tv = I.tv) (hH : Fintype.card H = 9) (S : HostSchedR Sl T)
    (hfit : fitsRK S (rK Ic))
    (u W : ℕ) (hu : 73 = u)
    (hW : 64 * Fintype.card T + S.nb = W) (hW1 : 1 ≤ W)
    (U : List (ℕ × ℕ))
    (hU : ∀ φ : ℕ → ℝ, unitPriceHost Ic S φ = listCost φ U)
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
    (Sum.inl : BLive401 (Orth (BC.LC (Fin 8) H l)) T S.nb → BRole401 (Orth (BC.LC (Fin 8) H l)) T S.nb C)
    Sum.inl_injective (Fintype.card (Orth (BC.LC (Fin 8) H l))) W Orth.card_pos hW1 (by rw [card_BLive401, hW])
    _ (bridgeHost_gcert I Ic hIc hH l S hfit) U (fun φ => by rw [hU φ]) s z hz hz1 hnum cl m k v

end End
end
end XHostD
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostD.wht_of_ginv_host
#print axioms OAI.PowerSaving.XHostD.engine_of_ginv_host

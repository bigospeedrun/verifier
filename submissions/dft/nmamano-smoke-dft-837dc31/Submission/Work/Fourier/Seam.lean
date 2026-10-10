import Submission.Work.GCert.Data.B2Gp193Main

/-!
# THE SEAM for the Fourier transfer: our kernel program in OpenAI's `hills_program` form

New file of this repository, not a copy of an OpenAI file.  It contains lines 95-99 of
lean/OAI/Computability/FourierTransform/TensorProgram.lean (the statement of `hills_program`) and line 114 of
lean/OAI/Computability/FourierTransform/TensorSaving.lean (the definition of `hills`) of github.com/openai/math
(commit fd4aeeb, Apache-2.0), with `hills`, `alpha` replaced by `hillsZ`, `alphaZ`.

OpenAI's Fourier proof uses the tensor network through ONE theorem, `RAM.hills_program`
(OAI/Computability/FourierTransform/TensorProgram.lean:95), with ONE call site (`Bench.gleamT`,
SectorAlgorithm.lean:45), plus four envelope facts (`hills_pos`, `hills_mono`, `hills_le`, `hills_real`,
TensorSaving.lean:116-133) and the number facts `alpha_pos`, `alpha_lt`, `Skies.alpha_theta`,
`Skies.decimal_range`.  This file gives all of them at OUR exponent

  `alphaZ = 1 - 7474547/10^10`      (OpenAI: `alpha = 1 - 2/10^11`),

under OpenAI's names with `Z` after `hills` / `alpha`, in OpenAI's own namespaces.

* `GX.engine_of_ginv`, `GX.engine_of_halves`   twins of `GX.wht_of_ginv`, `GX.wht_of_halves`
  (Work/GCert/Chain/End.lean) ending in the kernel program (`RAM.engine_program_ggroup_list`) instead of the
  Walsh-Hadamard corollary: every colour `cl`, both modes `m`, every batch of inputs.
* `Seam.engine_B2Gp193x_of_scal`, `_of_ids`   twins of `WHT.wht_B2Gp193x_of_scal`, `_of_ids`
  (Work/GCert/Data/B2Gp193.lean): same certificate `GXD.P193`, same unit list, same rate fact
  `BlockAccounting.fold_B2Gp193x`, fill parameter `s = 40`.
* `RAM.hillsZ_program`   THE SEAM, closed with the kernel-checked scalar half `GXD.P193.scalOK`.
* `RAM.envelope_program_ge`   the same at every exponent `z ≥ alphaZ`.

No `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
noncomputable section

/-! ## 1. The exponent and the envelope facts -/

/-- Our exponent, in the place of OpenAI's `alpha` (TensorSaving.lean:81). -/
def alphaZ : ℝ := 1 - 7474547/(10:ℝ)^10

theorem alphaZ_pos : 0 < alphaZ := by norm_num [alphaZ]
theorem alphaZ_lt : alphaZ < 1 := by norm_num [alphaZ]

lemma envelope_mono (z : ℝ) (hz : 0 ≤ z) {a b : ℕ} (h : a ≤ b) : envelope z a ≤ envelope z b := by
  unfold envelope
  gcongr

-- `envelope_le` (for `z ≤ 1`) and `envelope_real` (for `0 ≤ z`) already exist: Work/Block/WHT.lean:26, :31.

lemma envelope_mono_exp {z z' : ℝ} (h : z ≤ z') (k : ℕ) : envelope z k ≤ envelope z' k := by
  unfold envelope
  exact Nat.ceil_le_ceil (Real.rpow_le_rpow_of_exponent_le (by simp) h)

/-- Natural envelope at our exponent, in the place of OpenAI's `hills` (TensorSaving.lean:114). -/
def hillsZ (k : ℕ) := Nat.ceil (((k:ℝ)+1)^alphaZ)

lemma hillsZ_eq_envelope : hillsZ = envelope alphaZ := rfl

lemma hillsZ_pos (k : ℕ) : 1≤hillsZ k := envelope_pos alphaZ k

lemma hillsZ_mono {a b : ℕ} (h : a≤b) : hillsZ a ≤ hillsZ b := envelope_mono alphaZ alphaZ_pos.le h

lemma hillsZ_le (k : ℕ) : hillsZ k ≤ k+1 := envelope_le alphaZ alphaZ_lt.le k

lemma hillsZ_real (k : ℕ) : (hillsZ k:ℝ) ≤ 2*((k:ℝ)+1)^alphaZ := envelope_real alphaZ alphaZ_pos.le k

/-! ## 2. Two halves + rate fact => the kernel program (twins of `Work/GCert/Chain/End.lean`) -/

namespace GX
open Binary Matrix Finset RAM RAM.Ty SS CB RF BR BG GF FoldRate
universe U

section End
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **Kernel program from a generalised invocation package and a rate fact** (twin of `wht_of_ginv`). -/
theorem engine_of_ginv (I : GInv H T Sl C) (hH : 1 ≤ Fintype.card H)
    (u W : ℕ) (hu : 5 * Fintype.card H = u)
    (hW : 4 * Fintype.card T + Fintype.card Sl = W) (hW1 : 1 ≤ W)
    (U : List (ℕ × ℕ))
    (hU : ∀ φ : ℕ → ℝ,
      5 * I.cost φ + (Fintype.card T : ℝ) * bankPrice (Fintype.card H) φ = listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  engine_program_ggroup_list u (card_L5.trans hu) (by omega)
    (Sum.inl : BLive (Orth (L5 H)) T Sl → BRole (Orth (L5 H)) T Sl C) Sum.inl_injective
    (Fintype.card (Orth (L5 H))) W Orth.card_pos hW1 (by rw [card_BLive, hW])
    _ (bridge2_gcert I hH) U (fun φ => by rw [hU φ]) s z hz hz1 hnum cl m k v

/-- **Scalar half + label half + rate fact => the kernel program** (twin of `wht_of_halves`). -/
theorem engine_of_halves (S : Scal T Sl C) (L : Lab H S) (hH : 1 ≤ Fintype.card H)
    (u W : ℕ) (hu : 5 * Fintype.card H = u)
    (hW : 4 * Fintype.card T + Fintype.card Sl = W) (hW1 : 1 ≤ W)
    (U : List (ℕ × ℕ))
    (hU : ∀ φ : ℕ → ℝ,
      5 * L.cost φ + (Fintype.card T : ℝ) * bankPrice (Fintype.card H) φ = listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  engine_of_ginv L.inv hH u W hu hW hW1 U hU s z hz hz1 hnum cl m k v

end End
end GX

/-! ## 3. The certificate `GXD.P193` (twins of `Work/GCert/Data/B2Gp193.lean`) -/

namespace Seam
open Binary Matrix Finset RAM RAM.Ty
universe U

variable {C : Type} [Fintype C] [DecidableEq C] (S : GX.Scal (Fin GXD.P193.raw.v) (Fin GXD.P193.raw.R) C)
  {emb : CR.L3 (Fin GXD.P193.raw.v) (Fin GXD.P193.raw.R) → Nat} {un : Nat → CR.L3 (Fin GXD.P193.raw.v) (Fin GXD.P193.raw.R)}
  (cf : GXD.Co → SSC.Coef)

/-- **Kernel program at `1 - 7474547/10^10`** over any scalar half of `GXD.P193.raw`
(twin of `WHT.wht_B2Gp193x_of_scal`: same arguments, `GX.engine_of_halves` for `GX.wht_of_halves`). -/
theorem engine_B2Gp193x_of_scal (Ro : GLab.Roles GXD.P193.raw.v GXD.P193.raw.R emb un)
    (hMA : S.MA = SSC.matP un (GLab.mic cf (GXD.P193.raw.gatesA.flatMap GXD.Gate.adds)))
    (hMAi : S.MAi = SSC.matPinv un (GLab.mic cf (GXD.P193.raw.gatesA.flatMap GXD.Gate.adds)))
    (hMB : S.MB = SSC.matP un (GLab.mic cf (GXD.P193.raw.gatesB.flatMap GXD.Gate.adds)))
    (hMBi : S.MBi = SSC.matPinv un (GLab.mic cf (GXD.P193.raw.gatesB.flatMap GXD.Gate.adds)))
    (reg : C → Nat) (hCc : ∀ k (q : Fin GXD.P193.raw.R), S.Cc k q ≠ 0 → reg k = 2 * GXD.P193.raw.v + q.val)
    (hreg : ∀ k, reg k ∈ GXD.P193.raw.ret.map Prod.fst) (hC : Fintype.card C = 22)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - 7474547/(10:ℝ)^10) (k i)) :=
  GX.engine_of_halves S (GXD.P193.valid.lab S Ro cf hMA hMAi hMB hMBi reg hCc hreg)
    (by rw [Fintype.card_fin]; decide) 110 14692 (by rw [Fintype.card_fin]; rfl)
    (by rw [Fintype.card_fin, Fintype.card_fin]; rfl) (by norm_num) BlockAccounting.blocksB2Gp193x
    (fun φ => by
      rw [GXD.P193.lab_price S Ro cf hMA hMAi hMB hMBi reg hCc hreg hC φ, Fintype.card_fin, Fintype.card_fin]
      exact BridgeRate.B2Gp193.unit_cost_x φ)
    40 (1 - 7474547/(10:ℝ)^10) (by norm_num) (by norm_num) BlockAccounting.fold_B2Gp193x cl m k v

/-- the same from the FIVE scalar identities of the matrices `GS.MA GS.MAi GS.MB GS.MBi GS.Jrm GS.Ccm` of
`GXD.P193.raw` (twin of `WHT.wht_B2Gp193x_of_ids`). -/
theorem engine_B2Gp193x_of_ids (hv : 0 < GXD.P193.raw.v)
    (hAi : GS.MAi GXD.P193.raw hv * GS.MA GXD.P193.raw hv = 1) (hBi : GS.MBi GXD.P193.raw hv * GS.MB GXD.P193.raw hv = 1)
    (hx : ∀ (t : Fin GXD.P193.raw.v) (j : GS.Rl GXD.P193.raw), (GS.MB GXD.P193.raw hv * CR.scatM (GS.Jrm GXD.P193.raw * GS.Ccm GXD.P193.raw)
      * GS.MA GXD.P193.raw hv) (CR.lX t) j = if CR.lX t = j then 1 else 0)
    (hy : ∀ (i : GS.Rl GXD.P193.raw) (t : Fin GXD.P193.raw.v), (GS.MB GXD.P193.raw hv * CR.scatM (GS.Jrm GXD.P193.raw * GS.Ccm GXD.P193.raw)
      * GS.MA GXD.P193.raw hv) i (CR.lY t) = if i = CR.lY t then 1 else 0)
    (hid : ∀ S t : Fin GXD.P193.raw.v, (GS.MB GXD.P193.raw hv * CR.scatM (GS.Jrm GXD.P193.raw * GS.Ccm GXD.P193.raw)
      * GS.MA GXD.P193.raw hv) (CR.lY S) (CR.lX t) = if S = t then 1 else 0)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - 7474547/(10:ℝ)^10) (k i)) :=
  engine_B2Gp193x_of_scal (GXD.scalOf GXD.P193.raw hv hAi hBi hx hy hid) GS.toCoef (GXD.roles GXD.P193.raw hv)
    (GXD.scalOf_MA _ hv hAi hBi hx hy hid) (GXD.scalOf_MAi _ hv hAi hBi hx hy hid)
    (GXD.scalOf_MB _ hv hAi hBi hx hy hid) (GXD.scalOf_MBi _ hv hAi hBi hx hy hid)
    (GXD.reg GXD.P193.raw) (GXD.reg_slot GXD.P193.raw hv hAi hBi hx hy hid) (GXD.reg_mem GXD.P193.raw)
    (by rw [Fintype.card_fin]; decide) cl m k v

end Seam

/-! ## 4. THE SEAM -/

namespace RAM
open Binary Matrix Ty Finset
universe U

/-- **THE SEAM.**  OpenAI's `hills_program` (TensorProgram.lean:95) word for word, with `hillsZ`
(exponent `1 - 7474547/10^10`) in the place of `hills` (exponent `1 - 2/10^11`): the kernel program of
the published certificate `GXD.P193` (the one behind `WHT.wht_main_block_B2Gp193x`), for every colour,
both modes and every batch of inputs, in `2^k * hillsZ k` operations. -/
theorem hillsZ_program (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*hillsZ (k i)) :=
  Seam.engine_B2Gp193x_of_ids GXD.P193.scalOK.hv GXD.P193.scalOK.hAi GXD.P193.scalOK.hBi
    GXD.P193.scalOK.hx GXD.P193.scalOK.hy GXD.P193.scalOK.hid cl m k v

/-- **General exponent**: the same at every exponent `z ≥ alphaZ`, envelope `⌈(k+1)^z⌉`. -/
theorem envelope_program_ge (z : ℝ) (hz : alphaZ ≤ z) (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  (hillsZ_program cl m k v).mono fun i => Nat.mul_le_mul_left _ (envelope_mono_exp hz (k i))

end RAM

/-! ## 5. Number facts for the copy of `Main.lean` -/

namespace Seam

lemma alphaZ_lt_alpha : alphaZ < alpha := by norm_num [alphaZ, alpha]

/-- for `Skies.alpha_theta` (Main.lean:39): below the paper's exponent. -/
lemma alphaZ_theta : alphaZ < theta := alphaZ_lt_alpha.trans Skies.alpha_theta

/-- for `Skies.decimal_range` (Main.lean:59). -/
lemma alphaZ_decimal : alphaZ < decimalExponent ∧ decimalExponent < 1 := by
  norm_num [decimalExponent, alphaZ]

/-- Target exponent of the final Fourier statement: strictly above `alphaZ`, so that the
`(log log n)^2` factor of the reduction is absorbed. -/
def targetExponent : ℝ := 1 - 7474546/(10:ℝ)^10
/-- Fallback exponent. -/
def fallbackExponent : ℝ := 1 - 74745/(10:ℝ)^8

lemma alphaZ_lt_target : alphaZ < targetExponent := by norm_num [alphaZ, targetExponent]
lemma alphaZ_lt_fallback : alphaZ < fallbackExponent := by norm_num [alphaZ, fallbackExponent]
lemma target_lt_fallback : targetExponent < fallbackExponent := by
  norm_num [targetExponent, fallbackExponent]
lemma target_pos : 0 < targetExponent := by norm_num [targetExponent]
lemma target_lt_one : targetExponent < 1 := by norm_num [targetExponent]
lemma fallback_lt_one : fallbackExponent < 1 := by norm_num [fallbackExponent]
lemma target_lt_decimal : targetExponent < decimalExponent := by
  norm_num [targetExponent, decimalExponent]
lemma fallback_lt_decimal : fallbackExponent < decimalExponent := by
  norm_num [fallbackExponent, decimalExponent]
lemma target_lt_theta : targetExponent < theta :=
  (show targetExponent < alpha by norm_num [targetExponent, alpha]).trans Skies.alpha_theta
lemma fallback_lt_theta : fallbackExponent < theta :=
  (show fallbackExponent < alpha by norm_num [fallbackExponent, alpha]).trans Skies.alpha_theta

end Seam
end
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RAM.hillsZ_program
#print axioms OAI.PowerSaving.RAM.envelope_program_ge
#print axioms OAI.PowerSaving.Seam.alphaZ_theta
#print axioms OAI.PowerSaving.hillsZ_real

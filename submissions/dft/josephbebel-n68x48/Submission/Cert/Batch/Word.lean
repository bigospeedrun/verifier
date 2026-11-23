--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.Cert.Batch.Park

set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] OAI.PowerSaving.Window137.instFintypeOrthLC OAI.PowerSaving.GenMove.actPointG

namespace OAI.PowerSaving.Batch48
open Binary Matrix Finset GenMove StageGauge OAI.PowerSaving.BaseUnit ControlCheck

noncomputable section

def rho (t : Fin 200) := Window137.blkC (Fin 16) (0 : Fin 9) (bs t) * (Window137.blkC (Fin 16) (0 : Fin 9) (bs (pt 0)))ᵀ

lemma rho_orth (t : Fin 200) : (rho t)ᵀ * rho t = 1 := by
  rw [rho, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Window137.blkC _ _ _),
    Window137.blkC_orth, Matrix.one_mul, mul_eq_one_symm (Window137.blkC_orth _)]

def gr (g : Gm) (t : Fin 200) : Gm := ⟨g.1 * rho t, mul_orth g.2 (rho_orth t)⟩

lemma ofCols_congr {M M' : Matrix Lb Lb Binary.F} (h : M = M') (hM : Mᵀ * M = 1) (hM' : M'ᵀ * M' = 1) :
    ofCols M hM = ofCols M' hM' := by subst h; rfl

theorem BBC_rho (g : Gm) (t : Fin 200) : Window137.BBC (bs t) 0 g = A0 (gr g t) := by
  have e : g.1 * Window137.blkC (Fin 16) (0 : Fin 9) (bs t) =
      (gr g t).1 * Window137.blkC (Fin 16) (0 : Fin 9) (bs (pt 0)) := by
    show g.1 * _ = (g.1 * rho t) * _
    rw [rho, Matrix.mul_assoc, Matrix.mul_assoc, Window137.blkC_orth, Matrix.mul_one]
  exact ofCols_congr e (mul_orth g.2 (Window137.blkC_orth _)) (mul_orth (gr g t).2 (Window137.blkC_orth _))

theorem Ab_rho (g : Gm) (c : Fin 104) : Ab g c = A0 (gr g (pt c)) := BBC_rho g (pt c)

def gi (g : Gm) (t : Fin 200) : Gm := ⟨g.1 * (rho t)ᵀ, mul_orth g.2 (transpose_orth (rho_orth t))⟩

lemma gr_gi (g : Gm) (t : Fin 200) : gr (gi g t) t = g :=
  Subtype.ext (by show g.1 * (rho t)ᵀ * rho t = g.1; rw [Matrix.mul_assoc, rho_orth, Matrix.mul_one])

def pullM (σ : Rl' → Rl') : Matrix Rl' Rl' ℚ := fun x x' => if σ x = x' then 1 else 0

theorem pull_or (σ : Rl' → Rl') : RealisedOp (fun f (y : Data Lb Rl' f) x => y (σ x)) (fun _ => 0) :=
  (RealisedOp.mix (α := Lb) (pullM σ) 0).cast (fun f y => by
    show point f (actPointG (pullM σ) 0) y = fun x => y (σ x)
    funext x s
    show point f (actPointG (pullM σ) 0) y x s = y (σ x) s
    rw [point_ap]
    simp only [actPointG, pullM, Matrix.zero_apply, Pi.zero_apply, Rat.cast_zero, zero_mul, add_zero]
    rw [Finset.sum_eq_single (σ x)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h) (fun _ => rfl)

def emb : Rl ↪ Rl' := ⟨fun x => (x.1, .inr (.inl x.2)), fun a b h => by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; simp only [Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq] at h
  rw [h.1, h.2]⟩

def eK' (k : Fin 17) : SR ↪ Rl' := (eK k).trans emb

def stOp' (k : Fin 17) (f : ℕ) (y : Data Lb Rl' f) : Data Lb Rl' f :=
  multiAct f (mE (eK' k) (Bo k)) (point f (gE (eK' k) (StageWin.GAB IW.al IW.be)) (multiAct f (mE (eK' k) (Bp k)) y))

theorem stage_op' (k : Fin 17) : RealisedOp (stOp' k) (fun φ => (Fintype.card Gm : ℝ) * StageRoute.price φ) := by
  have hk : k.val ≤ 16 := by omega
  have h := StageWin.gauge_route IW (εJ k) (Mw k) (fun _ => trivial)
    (fun d q => StageWin.entN (Mw k d).X (IW.ent q)) (Wn k) (fun d q => StageWin.entN_spec _ _)
    (fun d q => StageWin.entW_spec _ _) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
  refine (RealisedOp.ext (eK' k) h ?_).cast (fun _ _ => rfl) (fun φ => by rw [StageRoute.invariant_price])
  rintro (((⟨g, t⟩ | ⟨g, t⟩) | ⟨g, q⟩) | ⟨g, j⟩)
  · show (Mw k (εJ k t g)).Xm.Φ (StageBox.tt (IW.tv t)) * iF _ _ = 1
    rw [← bs_v, Mw, εJ, StageFrames.stage_Xin bs 0 hH9 k hk t g]; exact frame_iF _ _
  · show (Mw k (εJ k t g)).Xm.Φ 0 * iF _ _ = 1
    rw [Mw, εJ, StageFrames.stage_Yin bs 0 hH9 k hk t g]; exact frame_iF _ _
  · exact Matrix.mul_one _
  · exact Matrix.mul_one _

lemma eK'_ap (k : Fin 17) (a : SR) : eK' k a = emb (eK k a) := rfl

theorem stOp'_emb (k : Fin 17) (f : ℕ) (y : Data Lb Rl' f) (x : Rl) :
    stOp' k f y (emb x) = stOp k f (fun x => y (emb x)) x := by
  rw [stOp', stOp]
  by_cases hx : ∃ a, eK k a = x
  · obtain ⟨a, rfl⟩ := hx
    have h1 := ext_on (eK' k) (Bp k) (Bp k) (Bo k) (StageWin.GAB IW.al IW.be) f y a
    have h2 := ext_on (eK k) (Bp k) (Bp k) (Bo k) (StageWin.GAB IW.al IW.be) f (fun x => y (emb x)) a
    simp only [eK'_ap] at h1
    exact h1.trans h2.symm
  · have h1 : ∀ a, eK k a ≠ x := fun a h => hx ⟨a, h⟩
    have e1 := ext_off (eK k) (Bp k) (Bp k) (Bo k) (StageWin.GAB IW.al IW.be) f (fun x => y (emb x)) x h1
    have e2 := ext_off (eK' k) (Bp k) (Bp k) (Bo k) (StageWin.GAB IW.al IW.be) f y (emb x)
      fun a h => h1 a (emb.injective ((eK'_ap k a).symm.trans h))
    exact e2.trans e1.symm

theorem stOp'_off (k : Fin 17) (f : ℕ) (y : Data Lb Rl' f) (x : Rl') (hx : ∀ z, emb z ≠ x) : stOp' k f y x = y x := by
  rw [stOp']
  exact ext_off (eK' k) (Bp k) (Bp k) (Bo k) (StageWin.GAB IW.al IW.be) f y x
    fun a h => hx _ ((eK'_ap k a).symm.trans h)

section Host
variable {R : Type*} [CommRing R] [Algebra ℚ R] (q L ι : R) (D : ℕ → R) (j : ℕ) (u : ℕ → R)

lemma hA (a b c d : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    semEvsI q L ι D 17 (Batch.hostE true j [a, b, c, d]) u =
    let M := monoVI q L ι D 17 (16 * 2 ^ (j + 1))
    Function.update (Function.update (Function.update (Function.update u b (M * (u b + q ^ 3 * u a)))
      a (M * u a)) c (M * (u c - q * u d))) d (M * u d) := by
  funext i
  simp [semEvsI, semEvI, Batch.hostE, Function.update_apply, cq, WarpCheck.sgnQ,
    monoVI_qpow q L ι D 17 3 (by norm_num), monoVI_qpow q L ι D 17 1 (by norm_num)]
  split_ifs <;> subst_vars <;> first | rfl | (exfalso; tauto) | ring1

lemma hB (h4 : q ^ 4 = 1) (a b : ℕ) (hab : a ≠ b) :
    semEvsI q L ι D 17 (Batch.hostE false j [a, b]) u =
    let M := monoVI q L ι D 17 (16 * 2 ^ (j + 1))
    Function.update (Function.update u b (M * (algebraMap ℚ R 2⁻¹ * q ^ 3 * u a + algebraMap ℚ R 2⁻¹ * u b)))
      a (M * (u a - q * u b)) := by
  have hba : b ≠ a := Ne.symm hab
  have ha : algebraMap ℚ R 2⁻¹ + algebraMap ℚ R 2⁻¹ = 1 := by rw [← map_add]; norm_num
  funext i
  by_cases hia : i = a
  · rw [hia]
    simp [semEvsI, semEvI, Batch.hostE, Function.update_apply, cq, WarpCheck.sgnQ, hab, hba,
      monoVI_qpow q L ι D 17 3 (by norm_num), monoVI_qpow q L ι D 17 1 (by norm_num)] <;> ring1
  by_cases hib : i = b
  · rw [hib]
    simp [semEvsI, semEvI, Batch.hostE, Function.update_apply, cq, WarpCheck.sgnQ, hab, hba,
      monoVI_qpow q L ι D 17 3 (by norm_num), monoVI_qpow q L ι D 17 1 (by norm_num)] <;>
      linear_combination (-(monoVI q L ι D 17 (16 * 2 ^ (j + 1)) * u b * algebraMap ℚ R 2⁻¹)) * h4 -
        (monoVI q L ι D 17 (16 * 2 ^ (j + 1)) * u b) * ha
  · simp [semEvsI, semEvI, Batch.hostE, Function.update_apply, hia, hib]

lemma host_M (k : ℕ) (D' : ℕ → R) (hj : j + 2 ≤ 17) (hk : k + 2 ≤ 18) (h : D (j + 1) = D' (k + 1)) :
    monoVI q L ι D 17 (16 * 2 ^ (j + 1)) = monoV q L D' 18 (8 * 2 ^ (k + 1)) := by
  have w1 := dp_win D 17 (j + 1) 1 (by omega)
  have w2 := dp_win D' 18 (k + 1) 1 (by omega)
  norm_num [Finset.prod_range_one] at w1 w2
  unfold monoVI monoV
  rw [show 16 * 2 ^ (j + 1) % 4 = 0 by omega, show 16 * 2 ^ (j + 1) / 4 % 2 = 0 by omega,
    show 16 * 2 ^ (j + 1) / 8 % 2 = 0 by omega, show 16 * 2 ^ (j + 1) / 16 = 2 ^ (j + 1) by omega,
    show 8 * 2 ^ (k + 1) % 4 = 0 by omega, show 8 * 2 ^ (k + 1) / 4 % 2 = 0 by omega,
    show 8 * 2 ^ (k + 1) / 8 = 2 ^ (k + 1) by omega, w1, w2, h]
  simp

end Host

def bR (r : Fin 312) : Bool := Batch.Sched.isR r
def tLoc (b : Bool) (j : ℕ) : List CEv := if b then TplR.loc j else TplA.loc j
def tHost (b : Bool) (j : ℕ) : List CEv := if b then TplR.hostEv j else TplA.hostEv j
def tK (b : Bool) (j : ℕ) : Bool := (if b then TplR.hostK else TplA.hostK).getD j true
def tR (b : Bool) (j : ℕ) : List ℕ := (if b then TplR.hostR else TplA.hostR).getD j []

lemma tHost_eq (b : Bool) (j : ℕ) : tHost b j = Batch.hostE (tK b j) j (tR b j) := by cases b <;> rfl

def fixK (κ : Bool) : List ℕ := if κ then [1, 0, 19, 20] else [1, 0]
def prH (rs : List ℕ) (m : ℕ) : ℕ :=
  if m = 1 then rs.getD 0 0 else if m = 0 then rs.getD 1 0 else if m = 19 then rs.getD 2 0 else rs.getD 3 0
def qrH (rs : List ℕ) (i : ℕ) : ℕ :=
  if i = rs.getD 0 0 then 1 else if i = rs.getD 1 0 then 0 else if i = rs.getD 2 0 then 19 else 20

lemma fixK_lt (κ : Bool) (m : ℕ) (h : m ∈ fixK κ) : m < 36 := by cases κ <;> simp [fixK] at h <;> omega

theorem host_ok : ∀ b : Bool, ∀ j : Fin 16, (tR b j).length = (if tK b j then 4 else 2) ∧ (tR b j).Nodup ∧
    (∀ i ∈ tR b j, i < 36 ∧ qrH (tR b j) i ∈ fixK (tK b j) ∧ prH (tR b j) (qrH (tR b j) i) = i) ∧
    (∀ m ∈ fixK (tK b j), prH (tR b j) m < 36) ∧ tK b j = !(b && (j.val == 0 || j.val == 15)) := by decide +kernel

theorem loc_ok : ∀ b : Bool, ∀ j : Fin 17, (tLoc b j).all okE = true := by decide +kernel

def ccP (p : ℕ) : Fin 104 := ⟨cpN p % 104, Nat.mod_lt _ (by norm_num)⟩
theorem port_ok : ∀ p : Fin 104, (pt (ccP p)).val = p.val ∧ sd (ccP p) = !decide (p.val ∈ Batch.Sched.bposS) := by
  decide +kernel
theorem pt_lt : ∀ c : Fin 104, (pt c).val < 104 := by decide +kernel

def cR (r : Fin 312) (j : ℕ) : Fin 104 := ccP (Batch.Sched.vPort r j)
def kτ (τ : Fin 48) : Fin 17 := ⟨τ.val % 16 + 1, by omega⟩
def js (τ : Fin 48) (r : Fin 312) : Fin 16 := Batch.Sched.slot r ⟨τ.val % 16, by omega⟩
def own (τ : Fin 48) (c : Fin 104) : Fin 312 × Fin 16 := Batch.Sched.owner τ ⟨(pt c).val, pt_lt c⟩

lemma kindP (r : Fin 312) (j : Fin 16) : sd (cR r j) = tK (bR r) j := by
  have hp : sd (cR r j) = !decide (Batch.Sched.vPort r j ∈ Batch.Sched.bposS) :=
    (port_ok ⟨Batch.Sched.vPort r j, (Batch.Sched.range_P r j r.2 j.2).2⟩).2
  have hk := Batch.Sched.kind_P r j r.2 j.2
  have e : decide (Batch.Sched.vPort r j ∈ Batch.Sched.bposS) = (bR r && ((j : ℕ) == 0 || (j : ℕ) == 15)) := by
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq, bR, Batch.Sched.isR, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    first | exact hk | simpa using hk | (simp [bR, Batch.Sched.isR]; exact hk)
  rw [hp, (host_ok (bR r) j).2.2.2.2, e]

lemma own_eq (τ : Fin 48) (r : Fin 312) (j : Fin 16) (hv : Batch.Sched.vCall r j = τ.val) : own τ (cR r j) = (r, j) := by
  have e1 : τ = Batch.Sched.call r j := Fin.ext hv.symm
  have e2 : (⟨(pt (cR r j)).val, pt_lt _⟩ : Fin 104) = Batch.Sched.port r j :=
    Fin.ext (port_ok ⟨_, (Batch.Sched.range_P r j r.2 j.2).2⟩).1
  rw [own, e2, e1, Batch.Sched.owner_visit]

lemma js_eq (τ : Fin 48) (r : Fin 312) (j : ℕ) (hj : j < 16) (hv : Batch.Sched.vCall r j = τ.val) : (js τ r).val = j := by
  have e : (⟨τ.val % 16, by omega⟩ : Fin 16) = Batch.Sched.colour r ⟨j, hj⟩ :=
    Fin.ext (show τ.val % 16 = Batch.Sched.vCall r j % 16 by rw [hv])
  rw [js, e, Batch.Sched.slot_colour]

section HostEq
variable {R : Type*} [CommRing R] [Algebra ℚ R] (q L ι : R) (D : ℕ → R) (j : ℕ) (v : ℕ → R)

lemma rs4 (rs : List ℕ) (h : rs.length = 4) : ∃ a b c d, rs = [a, b, c, d] := by
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rs⟩⟩⟩⟩⟩ <;> simp at h ⊢ <;> omega

lemma host_off (h4 : q ^ 4 = 1) (κ : Bool) (rs : List ℕ) (hl : rs.length = if κ then 4 else 2) (hn : rs.Nodup)
    (i : ℕ) (hi : i ∉ rs) : semEvsI q L ι D 17 (Batch.hostE κ j rs) v i = v i := by
  cases κ
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 (by simpa using hl)
    have hab : a ≠ b := by rintro rfl; simp at hn
    simp at hi
    rw [hB q L ι D j v h4 a b hab]
    simp [Function.update_apply, hi.1, hi.2]
  · obtain ⟨a, b, c, d, rfl⟩ := rs4 rs (by simpa using hl)
    have hab : a ≠ b := by rintro rfl; simp at hn
    have hac : a ≠ c := by rintro rfl; simp at hn
    have had : a ≠ d := by rintro rfl; simp at hn
    have hbc : b ≠ c := by rintro rfl; simp at hn
    have hbd : b ≠ d := by rintro rfl; simp at hn
    have hcd : c ≠ d := by rintro rfl; simp at hn
    simp at hi
    rw [hA q L ι D j v a b c d hab hac had hbc hbd hcd]
    simp [Function.update_apply, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]

lemma host_eq (h4 : q ^ 4 = 1) (D' : ℕ → R) (k : ℕ) (κ : Bool) (rs : List ℕ) (hl : rs.length = if κ then 4 else 2)
    (hn : rs.Nodup) (u : ℕ → R) (huv : ∀ m ∈ fixK κ, u m = v (prH rs m))
    (hM : monoVI q L ι D 17 (16 * 2 ^ (j + 1)) = monoV q L D' 18 (8 * 2 ^ (k + 1))) (i : ℕ) (hi : i ∈ rs) :
    semEvsI q L ι D 17 (Batch.hostE κ j rs) v i = semEvs q L D' 18 (jEvs κ k) u (qrH rs i) := by
  cases κ
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 (by simpa using hl)
    have hab : a ≠ b := by rintro rfl; simp at hn
    have h1 := huv 1 (by simp [fixK]); have h0 := huv 0 (by simp [fixK])
    simp [prH] at h1 h0
    rw [hB q L ι D j v h4 a b hab, jB q L D' k u h4]
    simp at hi
    rcases hi with rfl | rfl <;> simp [Function.update_apply, qrH, hM, h1, h0, hab, Ne.symm hab]
  · obtain ⟨a, b, c, d, rfl⟩ := rs4 rs (by simpa using hl)
    have hab : a ≠ b := by rintro rfl; simp at hn
    have hac : a ≠ c := by rintro rfl; simp at hn
    have had : a ≠ d := by rintro rfl; simp at hn
    have hbc : b ≠ c := by rintro rfl; simp at hn
    have hbd : b ≠ d := by rintro rfl; simp at hn
    have hcd : c ≠ d := by rintro rfl; simp at hn
    have h1 := huv 1 (by simp [fixK]); have h0 := huv 0 (by simp [fixK])
    have h19 := huv 19 (by simp [fixK]); have h20 := huv 20 (by simp [fixK])
    simp [prH] at h1 h0 h19 h20
    rw [hA q L ι D j v a b c d hab hac had hbc hbd hcd, jA q L D' k u]
    simp at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [Function.update_apply, qrH, hM, h1, h0, h19, h20, hab, hac, had,
      hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]

end HostEq

lemma emb_ap (x : Rl) : emb x = (x.1, .inr (.inl x.2)) := rfl

def sIn (τ : Fin 48) : Rl' → Rl'
  | (g, .inr (.inl (.inl (c, i)))) => if i.val ∈ fixK (sd c) then
      (gr g (pt c), .inl ((own τ c).1, fi (prH (tR (bR (own τ c).1) (own τ c).2) i.val)))
      else (g, .inr (.inl (.inl (c, i))))
  | (g, .inr (.inl (.inr (.inl (k, q))))) =>
      if k = kτ τ then (g, .inr (.inr (τ, q))) else (g, .inr (.inl (.inr (.inl (k, q)))))
  | x => x

def sOut (τ : Fin 48) : Rl' → Rl'
  | (g, .inl (r, i)) => if Batch.Sched.vCall r (js τ r) = τ.val ∧ i.val ∈ tR (bR r) (js τ r) then
      (gi g (pt (cR r (js τ r))), .inr (.inl (.inl (cR r (js τ r), fi (qrH (tR (bR r) (js τ r)) i.val)))))
      else (g, .inl (r, i))
  | (g, .inr (.inr (τ', q))) => if τ' = τ then (g, .inr (.inl (.inr (.inl (kτ τ, q))))) else (g, .inr (.inr (τ', q)))
  | x => x

def cOp (τ : Fin 48) (f : ℕ) (y : Data Lb Rl' f) : Data Lb Rl' f :=
  fun x => stOp' (kτ τ) f (fun x' => y (sIn τ x')) (sOut τ x)

theorem call_or (τ : Fin 48) : RealisedOp (cOp τ) (fun φ => GC * StageRoute.price φ) :=
  (((pull_or (sIn τ)).trans (stage_op' (kτ τ))).trans (pull_or (sOut τ))).cast (fun _ _ => rfl)
    (fun φ => by simp [GC])

def SpecW (W : Fin 312 → List CEv) (H : Fin 48 → Bool) (Op : ∀ f, Data Lb Rl' f → Data Lb Rl' f) : Prop :=
  ∀ f y, InvP f y → InvP f (Op f y) ∧ (∀ g r, VP f (Op f y) g r = SEP f g r (W r) (VP f y g r)) ∧
    ∀ g τ q, Op f y (g, .inr (.inr (τ, q))) =
      if H τ then matAct f (Wn (kτ τ) g q) (y (g, .inr (.inr (τ, q)))) else y (g, .inr (.inr (τ, q)))

theorem SpecW.comp {W W' : Fin 312 → List CEv} {H H' : Fin 48 → Bool} {O O' : ∀ f, Data Lb Rl' f → Data Lb Rl' f}
    (h : SpecW W H O) (h' : SpecW W' H' O') (hd : ∀ τ, H τ = true → H' τ = false) :
    SpecW (fun r => W r ++ W' r) (fun τ => H τ || H' τ) (fun f y => O' f (O f y)) := by
  intro f y hy
  obtain ⟨i1, v1, r1⟩ := h f y hy
  obtain ⟨i2, v2, r2⟩ := h' f _ i1
  refine ⟨i2, fun g r => by
    show VP f (O' f (O f y)) g r = _
    rw [v2, v1]; simp only [SEP, semEvsI_append], fun g τ q => ?_⟩
  show O' f (O f y) (g, .inr (.inr (τ, q))) = _
  rw [r2, r1]
  by_cases e1 : H τ = true
  · simp [e1, hd τ e1]
  · simp only [Bool.not_eq_true] at e1; simp [e1]

theorem SpecW.congr {W W' : Fin 312 → List CEv} {H H' : Fin 48 → Bool} {O : ∀ f, Data Lb Rl' f → Data Lb Rl' f}
    (h : SpecW W H O) (hW : ∀ r, W r = W' r) (hH : ∀ τ, H τ = H' τ) : SpecW W' H' O := by
  intro f y hy; obtain ⟨a, b, c⟩ := h f y hy
  exact ⟨a, fun g r => by rw [b, hW], fun g τ q => by rw [c, hH]⟩

theorem SpecW.ofP {gate : Fin 312 → Bool} {evs : List CEv} {O : ∀ f, Data Lb Rl' f → Data Lb Rl' f}
    (h : SpecP gate evs O) : SpecW (fun r => if gate r then evs else []) (fun _ => false) O := by
  intro f y hy; obtain ⟨a, b, c⟩ := h f y hy
  exact ⟨a, fun g r => by beta_reduce; rw [b]; split_ifs <;> rfl, fun g τ q => by rw [c] <;> rfl⟩

lemma cOp_off (τ : Fin 48) (f : ℕ) (y : Data Lb Rl' f) (g : Gm) (r : Fin 312) (i : Fin 40)
    (h : ¬(Batch.Sched.vCall r (js τ r) = τ.val ∧ i.val ∈ tR (bR r) (js τ r))) :
    cOp τ f y (g, .inl (r, i)) = y (g, .inl (r, i)) := by
  have hs : sOut τ (g, .inl (r, i)) = (g, .inl (r, i)) := by simp only [sOut]; rw [if_neg h]
  show stOp' (kτ τ) f (fun x' => y (sIn τ x')) (sOut τ (g, .inl (r, i))) = _
  rw [hs]
  exact stOp'_off _ f _ _ fun z e => by simp [emb_ap] at e

lemma cOp_inr (τ : Fin 48) (f : ℕ) (y : Data Lb Rl' f) (g : Gm) (τ' : Fin 48) (q : Fin NQ) :
    cOp τ f y (g, .inr (.inr (τ', q))) = if decide (τ' = τ) then
      matAct f (Wn (kτ τ') g q) (y (g, .inr (.inr (τ', q)))) else y (g, .inr (.inr (τ', q))) := by
  by_cases e : τ' = τ
  · rw [if_pos (decide_eq_true e), e]
    have hs : sOut τ (g, .inr (.inr (τ, q))) = emb (g, .inr (.inl (kτ τ, q))) := by simp [sOut, emb_ap]
    have hs2 : sIn τ (emb (g, .inr (.inl (kτ τ, q)))) = (g, .inr (.inr (τ, q))) := by simp [sIn, emb_ap]
    show stOp' (kτ τ) f (fun x' => y (sIn τ x')) (sOut τ (g, .inr (.inr (τ, q)))) = _
    rw [hs, stOp'_emb, stF, hs2]
  · rw [if_neg (show ¬(decide (τ' = τ) = true) from fun h => e (of_decide_eq_true h))]
    have hs : sOut τ (g, .inr (.inr (τ', q))) = (g, .inr (.inr (τ', q))) := by simp [sOut, e]
    show stOp' (kτ τ) f (fun x' => y (sIn τ x')) (sOut τ (g, .inr (.inr (τ', q)))) = _
    rw [hs]
    exact stOp'_off _ f _ _ fun z h => by simp [emb_ap] at h

lemma cOp_root (τ : Fin 48) (f : ℕ) (y : Data Lb Rl' f) (g' : Gm) (r : Fin 312) (i : ℕ)
    (hv : Batch.Sched.vCall r (js τ r) = τ.val) (hi : i ∈ tR (bR r) (js τ r)) :
    cOp τ f y (g', .inl (r, fi i)) = stOp (kτ τ) f (fun x => y (sIn τ (emb x)))
      (gi g' (pt (cR r (js τ r))), .inl (cR r (js τ r), fi (qrH (tR (bR r) (js τ r)) i))) := by
  have hi36 := ((host_ok (bR r) (js τ r)).2.2.1 i hi).1
  have hfi : (fi i).val = i := Nat.mod_eq_of_lt (by omega)
  have hs : sOut τ (g', .inl (r, fi i)) =
      emb (gi g' (pt (cR r (js τ r))), .inl (cR r (js τ r), fi (qrH (tR (bR r) (js τ r)) i))) := by
    simp only [sOut, hfi]
    rw [if_pos (And.intro hv hi)]
    all_goals rfl
  show stOp' (kτ τ) f (fun x' => y (sIn τ x')) (sOut τ (g', .inl (r, fi i))) = _
  rw [hs]
  exact stOp'_emb (kτ τ) f _ _

set_option maxHeartbeats 800000 in

lemma cOp_host (τ : Fin 48) (f : ℕ) (y : Data Lb Rl' f) (g' : Gm) (r : Fin 312) (j : Fin 16) (i : ℕ)
    (hv : Batch.Sched.vCall r j = τ.val) (hi : i ∈ tR (bR r) j) :
    wl f (stOp (kτ τ) f (fun x => y (sIn τ (emb x)))
      (gi g' (pt (cR r j)), .inl (cR r j, fi (qrH (tR (bR r) j) i)))) =
      SEP f g' r (tHost (bR r) j) (VP f y g' r) i := by
  obtain ⟨hl, hn, hrs, hfix, -⟩ := host_ok (bR r) j
  have hm36 := fixK_lt _ _ (hrs i hi).2.1
  have hkd := kindP r j
  have hown := own_eq τ r j hv
  have hA' : Ab (gi g' (pt (cR r j))) (cR r j) = A0 g' := by rw [Ab_rho, gr_gi]
  have huv : ∀ m ∈ fixK (tK (bR r) j), U f (fun x => y (sIn τ (emb x))) (gi g' (pt (cR r j))) (cR r j) m =
      VP f y g' r (prH (tR (bR r) j) m) := by
    intro m hm
    have h1 := fixK_lt _ m hm
    have h2 := hfix m hm
    have hfm : (fi m).val = m := Nat.mod_eq_of_lt (by omega)
    simp only [U, if_pos h1, emb_ap, sIn, hfm, hkd, if_pos hm, hown, gr_gi, VP,
      if_pos (show prH (tR (bR r) j) m < 40 by omega)]
  have hsg : Batch.Sched.sig r j = τ.val % 16 := by unfold Batch.Sched.sig; rw [hv]
  have hD : DP f g' r (j + 1) = Dv f (A0 g') ((kτ τ : ℕ) + 1) :=
    congrArg (Dv f (A0 g')) (by
      show Batch.Sched.sig r (j + 1 - 1) + 2 = τ.val % 16 + 1 + 1
      rw [Nat.add_sub_cancel, hsg]
      all_goals rfl)
  have hM := host_M (qv f (A0 g')) (Lv f (A0 g')) (fun _ => Complex.I) (DP f g' r) j (kτ τ) (Dv f (A0 g'))
    (by have := j.isLt; omega) (by show τ.val % 16 + 1 + 2 ≤ 18; omega) hD
  have e2 : wl f (stOp (kτ τ) f (fun x => y (sIn τ (emb x)))
      (gi g' (pt (cR r j)), .inl (cR r j, fi (qrH (tR (bR r) j) i)))) =
      U f (stOp (kτ τ) f (fun x => y (sIn τ (emb x)))) (gi g' (pt (cR r j))) (cR r j) (qrH (tR (bR r) j) i) := by
    simp only [U, if_pos hm36]
  rw [e2, st_view, SE, hkd, hA', SEP, tHost_eq, host_eq (qv f (A0 g')) (Lv f (A0 g')) (fun _ => Complex.I)
    (DP f g' r) j (VP f y g' r) (q4 f (A0 g')) (Dv f (A0 g')) (kτ τ) (tK (bR r) j) (tR (bR r) j) hl hn _ huv hM i hi]

set_option maxHeartbeats 800000 in
theorem call_spec (τ : Fin 48) : SpecW (fun r => if Batch.Sched.vCall r (js τ r) = τ.val then tHost (bR r) (js τ r) else [])
    (fun τ' => decide (τ' = τ)) (cOp τ) := by
  intro f y hy
  have hhost : ∀ g' (r : Fin 312) (i : ℕ), Batch.Sched.vCall r (js τ r) = τ.val → i ∈ tR (bR r) (js τ r) →
      wl f (cOp τ f y (g', .inl (r, fi i))) = SEP f g' r (tHost (bR r) (js τ r)) (VP f y g' r) i := by
    intro g' r i hv hi
    rw [cOp_root τ f y g' r i hv hi]
    exact cOp_host τ f y g' r (js τ r) i hv hi
  refine ⟨fun g r i hi => ?_, fun g r => funext fun i => ?_, cOp_inr τ f y⟩
  · by_cases h40 : i < 40
    · have hf : (fi i).val = i := Nat.mod_eq_of_lt h40
      have e := hy g r i hi
      have hn : ¬(Batch.Sched.vCall r (js τ r) = τ.val ∧ (fi i).val ∈ tR (bR r) (js τ r)) := fun h => by
        have := ((host_ok (bR r) (js τ r)).2.2.1 _ h.2).1; omega
      rw [show VP f y g r i = wl f (y (g, .inl (r, fi i))) from if_pos h40] at e
      rw [show VP f (cOp τ f y) g r i = wl f (cOp τ f y (g, .inl (r, fi i))) from if_pos h40,
        cOp_off τ f y g r (fi i) hn, e]
    · exact if_neg h40
  · beta_reduce
    by_cases hc : Batch.Sched.vCall r (js τ r) = τ.val ∧ i ∈ tR (bR r) (js τ r)
    · have h36 := ((host_ok (bR r) (js τ r)).2.2.1 i hc.2).1
      rw [if_pos hc.1, show VP f (cOp τ f y) g r i = wl f (cOp τ f y (g, .inl (r, fi i))) from if_pos (by omega)]
      exact hhost g r i hc.1 hc.2
    · have e : SEP f g r (if Batch.Sched.vCall r (js τ r) = τ.val then tHost (bR r) (js τ r) else []) (VP f y g r) i =
          VP f y g r i := by
        split_ifs with hv
        · obtain ⟨hl, hn, -⟩ := host_ok (bR r) (js τ r)
          rw [SEP, tHost_eq]
          exact host_off _ _ _ _ _ _ (q4 f (A0 g)) _ _ hl hn i fun h => hc ⟨hv, h⟩
        · rfl
      rw [e]
      by_cases h40 : i < 40
      · have hn : ¬(Batch.Sched.vCall r (js τ r) = τ.val ∧ (fi i).val ∈ tR (bR r) (js τ r)) := by
          rwa [show (fi i).val = i from Nat.mod_eq_of_lt h40]
        rw [show VP f (cOp τ f y) g r i = wl f (cOp τ f y (g, .inl (r, fi i))) from if_pos h40,
          show VP f y g r i = wl f (y (g, .inl (r, fi i))) from if_pos h40, cOp_off τ f y g r (fi i) hn]
      · rw [show VP f (cOp τ f y) g r i = 0 from if_neg h40, show VP f y g r i = 0 from if_neg h40]

def nv (r : Fin 312) (τ : ℕ) : ℕ := ((range 16).filter fun j => Batch.Sched.vCall r j < τ).card

lemma vlt (r : Fin 312) {j j' : ℕ} (h : j < j') (h' : j' < 16) : Batch.Sched.vCall r j < Batch.Sched.vCall r j' := by
  obtain ⟨d, rfl⟩ : ∃ d, j' = j + 1 + d := ⟨j' - j - 1, by omega⟩
  clear h
  induction d with
  | zero => exact Batch.Sched.chrono_P r j r.2 (by omega)
  | succ d ih => exact (ih (by omega)).trans (Batch.Sched.chrono_P r (j + 1 + d) r.2 (by omega))

lemma nv_eq (r : Fin 312) {j τ : ℕ} (hj : j < 16) (hv : Batch.Sched.vCall r j = τ) : nv r τ = j := by
  subst hv
  have e : (range 16).filter (fun x => Batch.Sched.vCall r x < Batch.Sched.vCall r j) = range j := by
    ext x; simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hx, h⟩
      by_contra hc
      rcases (not_lt.1 hc).lt_or_eq with h1 | h1
      · have := vlt r h1 hx; omega
      · subst h1; omega
    · intro hx; exact ⟨by omega, vlt r hx hj⟩
  rw [nv, e, card_range]

lemma nv_succ (r : Fin 312) {j τ : ℕ} (hj : j < 16) (hv : Batch.Sched.vCall r j = τ) : nv r (τ + 1) = j + 1 := by
  subst hv
  have e : (range 16).filter (fun x => Batch.Sched.vCall r x < Batch.Sched.vCall r j + 1) = range (j + 1) := by
    ext x; simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hx, h⟩
      by_contra hc
      have := vlt r (show j < x by omega) hx; omega
    · intro hx
      refine ⟨by omega, ?_⟩
      rcases (Nat.lt_succ_iff.1 hx).lt_or_eq with h1 | h1
      · have := vlt r h1 hj; omega
      · subst h1; omega
  rw [nv, e, card_range]

lemma nv_succ_ne (r : Fin 312) {τ : ℕ} (h : ∀ j < 16, Batch.Sched.vCall r j ≠ τ) : nv r (τ + 1) = nv r τ := by
  unfold nv; congr 1
  exact filter_congr fun x hx => ⟨fun h1 => lt_of_le_of_ne (by omega) (h x (mem_range.1 hx)), fun h1 => by omega⟩

lemma nv48 (r : Fin 312) : nv r 48 = 16 := by
  rw [nv, filter_true_of_mem fun j hj => (Batch.Sched.range_P r j r.2 (mem_range.1 hj)).1, card_range]

lemma fm_one {α β : Type*} [DecidableEq α] (P : α → Prop) [DecidablePred P] (F : α → List β) (a : α) :
    ∀ L : List α, L.Nodup → (∀ x ∈ L, P x → x = a) →
      L.flatMap (fun x => if P x then F x else []) = if a ∈ L ∧ P a then F a else []
  | [], _, _ => by simp
  | x :: L, hn, h => by
    rw [List.flatMap_cons, fm_one P F a L (List.nodup_cons.1 hn).2 (fun y hy => h y (by simp [hy]))]
    by_cases hx : x = a
    · subst hx
      have : x ∉ L := (List.nodup_cons.1 hn).1
      by_cases hp : P x <;> simp [hp, this]
    · have hp : ¬ P x := fun hp => hx (h x (by simp) hp)
      simp [hp, Ne.symm hx]

def preT (b : Bool) : ℕ → List CEv
  | 0 => tLoc b 0
  | n + 1 => preT b n ++ (tHost b n ++ tLoc b (n + 1))

lemma pre_evs (b : Bool) : preT b 16 = if b then TplR.evs else TplA.evs := by
  cases b
  · rw [TplA.evs_split]
    simp only [preT, tLoc, tHost, Bool.false_eq_true, ↓reduceIte, List.append_assoc, TplA.loc, List.getD_cons_zero,
      List.getD_cons_succ]
    try rfl
  · rw [TplR.evs_split]
    simp only [preT, tLoc, tHost, ↓reduceIte, List.append_assoc, TplR.loc, List.getD_cons_zero, List.getD_cons_succ]
    try rfl

lemma pre_step (r : Fin 312) (τ : Fin 48) : preT (bR r) (nv r τ) ++
    ((if Batch.Sched.vCall r (js τ r) = τ.val then tHost (bR r) (js τ r) else []) ++
      (List.range 16).flatMap fun j => if Batch.Sched.vCall r j = τ.val then tLoc (bR r) (j + 1) else []) =
    preT (bR r) (nv r (τ.val + 1)) := by
  by_cases hv : Batch.Sched.vCall r (js τ r) = τ.val
  · have hj := (js τ r).isLt
    rw [if_pos hv, nv_eq r hj hv, nv_succ r hj hv, fm_one (fun j => Batch.Sched.vCall r j = τ.val)
      (fun j => tLoc (bR r) (j + 1)) (js τ r).val (List.range 16) (by first | exact List.nodup_range | simp)
      (fun x hx h => (js_eq τ r x (List.mem_range.1 hx) h).symm)]
    simp [preT, hj, hv]
  · have hn : ∀ j < 16, Batch.Sched.vCall r j ≠ τ.val := fun j hj h => hv (by rw [js_eq τ r j hj h]; exact h)
    have h0 : Batch.Sched.vCall r 0 ≠ τ.val := hn 0 (by norm_num)
    rw [if_neg hv, fm_one (fun j => Batch.Sched.vCall r j = τ.val) (fun j => tLoc (bR r) (j + 1)) 0 (List.range 16)
      (by first | exact List.nodup_range | simp) (fun x hx h => absurd h (hn x (List.mem_range.1 hx))),
      nv_succ_ne r hn]
    simp [h0]

def gtB (τ : ℕ) (b : Bool) (j : ℕ) (r : Fin 312) : Bool := bR r == b && Batch.Sched.vCall r j == τ
def scB (τ j : ℕ) (φ : ℕ → ℝ) : ℝ :=
  segCost (gtB τ false j) (tLoc false (j + 1)) φ + segCost (gtB τ true j) (tLoc true (j + 1)) φ
def stepC (τ : ℕ) (φ : ℕ → ℝ) : ℝ := GC * StageRoute.price φ + ∑ j ∈ range 16, scB τ j φ
def runC (n : ℕ) (φ : ℕ → ℝ) : ℝ :=
  segCost (fun r => !bR r) (tLoc false 0) φ + segCost bR (tLoc true 0) φ + ∑ τ ∈ range n, stepC τ φ

theorem segs_spec (τ : ℕ) : ∀ n ≤ 16, ∃ Op, RealisedOp Op (fun φ => ∑ j ∈ range n, scB τ j φ) ∧
    SpecW (fun r => (List.range n).flatMap fun j => if Batch.Sched.vCall r j = τ then tLoc (bR r) (j + 1) else [])
      (fun _ => false) Op
  | 0, _ => ⟨_, RealisedOp.refl.cast (fun _ _ => rfl) (fun φ => by simp),
      fun f y hy => ⟨hy, fun g r => by simp [SEP, semEvsI], fun g τ q => rfl⟩⟩
  | n + 1, h => by
    obtain ⟨O, hO, S⟩ := segs_spec τ n (by omega)
    obtain ⟨O1, h1, S1⟩ := seg_realised (gtB τ false n) (tLoc false (n + 1)) (loc_ok false ⟨n + 1, by omega⟩)
    obtain ⟨O2, h2, S2⟩ := seg_realised (gtB τ true n) (tLoc true (n + 1)) (loc_ok true ⟨n + 1, by omega⟩)
    refine ⟨_, ((hO.trans h1).trans h2).cast (fun _ _ => rfl) (fun φ => by simp only [sum_range_succ, scB]; ring),
      ((S.comp (SpecW.ofP S1) (fun _ _ => rfl)).comp (SpecW.ofP S2) (fun _ _ => rfl)).congr (fun r => ?_)
        (fun _ => rfl)⟩
    beta_reduce
    rw [List.range_succ, List.flatMap_append, List.append_assoc]
    congr 1
    simp only [gtB, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hv : Batch.Sched.vCall r n = τ
    · have hb : (Batch.Sched.vCall r n == τ) = true := beq_iff_eq.2 hv
      by_cases hbf : bR r = false
      · simp [gtB, hb, hv, hbf]
      · have hbt : bR r = true := by cases hbb : bR r <;> simp_all
        simp [gtB, hb, hv, hbt]
    · have hb : (Batch.Sched.vCall r n == τ) = false := by simpa using hv
      by_cases hbf : bR r = false
      · simp [gtB, hb, hv, hbf]
      · have hbt : bR r = true := by cases hbb : bR r <;> simp_all
        simp [gtB, hb, hv, hbt]

theorem step_spec (τ : Fin 48) : ∃ Op, RealisedOp Op (stepC τ) ∧
    SpecW (fun r => (if Batch.Sched.vCall r (js τ r) = τ.val then tHost (bR r) (js τ r) else []) ++
      (List.range 16).flatMap fun j => if Batch.Sched.vCall r j = τ.val then tLoc (bR r) (j + 1) else [])
      (fun τ' => decide (τ' = τ) || false) Op := by
  obtain ⟨O, hO, S⟩ := segs_spec τ 16 le_rfl
  exact ⟨_, ((call_or τ).trans hO).cast (fun _ _ => rfl) (fun _ => rfl), (call_spec τ).comp S (fun _ _ => rfl)⟩

theorem run_spec : ∀ n ≤ 48, ∃ Op, RealisedOp Op (runC n) ∧
    SpecW (fun r => preT (bR r) (nv r n)) (fun τ => decide (τ.val < n)) Op
  | 0, _ => by
    obtain ⟨O1, h1, S1⟩ := seg_realised (fun r => !bR r) (tLoc false 0) (loc_ok false 0)
    obtain ⟨O2, h2, S2⟩ := seg_realised bR (tLoc true 0) (loc_ok true 0)
    refine ⟨_, (h1.trans h2).cast (fun _ _ => rfl) (fun φ => by simp [runC]),
      ((SpecW.ofP S1).comp (SpecW.ofP S2) (fun _ _ => rfl)).congr (fun r => ?_) (fun τ => by simp)⟩
    beta_reduce
    rw [show nv r 0 = 0 by simp [nv]]
    cases bR r <;> simp [preT]
  | n + 1, h => by
    obtain ⟨O, hO, S⟩ := run_spec n (by omega)
    obtain ⟨O', hO', S'⟩ := step_spec ⟨n, by omega⟩
    refine ⟨_, (hO.trans hO').cast (fun _ _ => rfl) (fun φ => by simp only [runC, sum_range_succ, Fin.val_mk]; ring),
      (S.comp S' (fun τ h1 => ?_)).congr (fun r => pre_step r ⟨n, by omega⟩) (fun τ => ?_)⟩
    · simp only [decide_eq_true_eq] at h1
      simp only [Bool.or_false, decide_eq_false_iff_not]
      rintro rfl; exact lt_irrefl n h1
    · rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.or_false, Fin.ext_iff, Fin.val_mk]
      omega

end
end OAI.PowerSaving.Batch48

private theorem marker_submission_work_b48_word (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

section
namespace OAI
namespace PowerSaving
namespace HostPad
open Binary Matrix Finset GenMove RankCost CoordPerm
noncomputable section

section Adapt
variable {α : Type} [Fintype α] [DecidableEq α]

/-
Idle-axis hosting (DaysSky, CrocSwap/integer-mult-bounds PR #442) puts the residual of a helper slot of an invocation
on the pending coordinates of an idle data role.  In our engine this needs NO new conjugation lemma:

* the residual of a gauged slot is already `Wn = C * coordFrame R * C'` with `C`, `C'` free and `|R| = 9 - e_q`
  (`entW_form`, Work/Bridge401/Sched.lean; `gauged_Wn`, Work/Bank401/Adapt.lean: Nil Mamano / Ryan Shea, on
  Dugongue's #401 banks);
* an idle climb inside ONE orthonormal base, `frame A s → frame A t`, is `X1 = Q * coordFrame D * Q' * X0` with `Q`, `Q'`
  free and `|D| = |t \ s|` (`hostForm_frame`, from Jacob Sussman's `frame_core_free` and `core_nested`);
-/
theorem host_adapt {A B C C' : CMat α} (hA : Free A) (hC : Free C) (hC' : Free C')
    (D U R : Finset α) (hUD : U ⊆ D) (hc : U.card + R.card ≤ D.card) :
    ∃ P, Free P ∧ ∃ (A2 : CMat α) (U2 : Finset α), Free A2 ∧ U2 ⊆ D ∧ U2.card = U.card + R.card ∧
      C * coordFrame R * C' * (P * (A * coordFrame U * B)) = A2 * coordFrame U2 * B := by
  have hroom : R.card ≤ (D \ U).card := by rw [card_sdiff_of_subset hUD]; omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hroom
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq T R hTcard
  obtain ⟨Ai, hAi, hAiA, -⟩ := free_inv hA
  obtain ⟨Ci, hCi, -, hC'Ci⟩ := free_inv hC'
  have hdis : Disjoint T U := Finset.disjoint_of_subset_left hTsub Finset.sdiff_disjoint
  have hswap : coordFrame R * permMat (cperm σ) = permMat (cperm σ) * coordFrame T := by
    rw [pk_cperm σ T, hσ]
  refine ⟨Ci * permMat (cperm σ) * Ai, (hCi.mul (free_cperm σ)).mul hAi,
    C * permMat (cperm σ), T ∪ U, hC.mul (free_cperm σ),
    Finset.union_subset (hTsub.trans Finset.sdiff_subset) hUD, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdis]; omega
  · rw [pk_union T U hdis]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (C * coordFrame R) C' Ci, hC'Ci, Matrix.mul_one,
      Matrix.mul_assoc (C * coordFrame R * permMat (cperm σ)) Ai A, hAiA, Matrix.mul_one,
      Matrix.mul_assoc C (coordFrame R), hswap, ← Matrix.mul_assoc C (permMat (cperm σ)) (coordFrame T)]

theorem host_pad {A Q : CMat α} (hA : Free A) (hQ : Free Q) (B : CMat α) (D U : Finset α) (hUD : U ⊆ D)
    (hD : D.card - U.card < Fintype.card α) :
    GReach (A * coordFrame U * B) (Q * coordFrame D * B) (fun φ => bcost φ (D.card - U.card)) := by
  obtain ⟨Ai, hAi, hAiA, -⟩ := free_inv hA
  obtain ⟨Qi, hQi, hQiQ, -⟩ := free_inv hQ
  intro ρ _ _ l
  have s1 : GStep l (A * coordFrame U * B) (Q * coordFrame U * B) (fun _ => 0) := by
    have e : Q * coordFrame U * B = Q * Ai * (A * coordFrame U * B) := by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Ai A, hAiA, Matrix.one_mul]
    rw [e]; exact gstep_free (hQ.mul hAi) l _
  by_cases hsame : D.card = U.card
  · obtain rfl : U = D := Finset.eq_of_subset_of_card_le hUD (by omega)
    exact s1.cast fun φ => by simp only [Nat.sub_self, bcost_zero]
  · have hle : U.card ≤ D.card := Finset.card_le_card hUD
    have hE : (D \ U).card = D.card - U.card := card_sdiff_of_subset hUD
    have blk := gstep_of_factor l (Q * coordFrame U * B) ((OBase.canonical α).fam (D \ U))
      ((OBase.canonical α).fam_indep (D \ U)) hQ hQi (by omega) (by omega)
    have e : Q * blockMat ((OBase.canonical α).fam (D \ U)) * Qi * (Q * coordFrame U * B) = Q * coordFrame D * B := by
      rw [← pk_eq_blockMat, pk_sdiff hUD]
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Qi Q, hQiQ, Matrix.one_mul]
    rw [e] at blk
    exact (s1.trans blk).cast fun φ => by
      simp only [bcost_pos φ (show D.card - U.card ≠ 0 by omega), hE, zero_add]
end Adapt

end
end HostPad
end PowerSaving
end OAI

set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

namespace OAI.PowerSaving.BaseUnit
open Binary Matrix Finset GenMove StageGauge

noncomputable section

def sr (q : Fin 891) : ℕ := StageRoute.schedRes.getD q.val 0

lemma sr_le (q : Fin 891) : 1 ≤ sr q ∧ sr q ≤ 9 := by
  have h := List.all_eq_true.1 sched_ok.2 (sr q) (by
    rw [sr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [sched_ok.1]; exact q.isLt), Option.getD_some]
    exact List.getElem_mem _)
  simpa using h

lemma ex_D (q : Fin 891) : ∃ D : Finset Lb, D.card = sr q := by
  obtain ⟨D, -, hD⟩ := exists_subset_card_eq (s := (univ : Finset Lb)) (n := sr q)
    (by rw [card_univ, StageFrames.card_LC137 0 hH9]; have := sr_le q; omega)
  exact ⟨D, hD⟩

def Dr (q : Fin 891) : Finset Lb := (ex_D q).choose
lemma Dr_card (q : Fin 891) : (Dr q).card = sr q := (ex_D q).choose_spec

lemma ex_Z (k : ℕ) (g : Gm) (q : Fin 891) : ∃ Z : CMat Lb, GReach 1 Z (fun _ => 0) ∧
    GReach (Wn k g q * Z) (coordFrame (Dr q)) (fun φ => RankCost.bcost φ 0) := by
  obtain ⟨C, C', R, hC, hC', hR, hW⟩ := StageWin.entW_form (Mw k g).X (IW.ent q)
  have hR' : R.card = (Dr q).card := by rw [hR, Dr_card]; exact StageRoute.hent q
  obtain ⟨P, hP, A2, U2, hA2, hU2, hc, he⟩ := HostPad.host_adapt (B := (1 : CMat Lb)) Free.one hC hC' (Dr q) ∅ R
    (empty_subset _) (by rw [card_empty, zero_add, hR'])
  rw [card_empty, zero_add] at hc
  simp only [pk_empty, Matrix.mul_one] at he
  have h := HostPad.host_pad hA2 Free.one 1 (Dr q) U2 hU2 (by rw [hc, hR', Nat.sub_self, StageFrames.card_LC137 0 hH9]; norm_num)
  simp only [hc, hR', Nat.sub_self, Matrix.mul_one, Matrix.one_mul] at h
  refine ⟨P, fun ρ _ _ l => by simpa using gstep_free hP l (1 : CMat Lb), ?_⟩
  rw [Wn, hW, he]; exact h

def Sx (κ : Bool) (i : ℕ) : Finset Lb := sX ((ControlCheck.Packed.dTab κ).getD i 0 + (ControlCheck.Packed.nTab κ).getD i 0 + 1) \ sY ((ControlCheck.Packed.dTab κ).getD i 0)

lemma bm_eq (A : OBase Lb) (S : Finset Lb) : blockMat (A.fam S) = shift (A.corr S) * frame A S := by
  have h := OBase.frame_union A ∅ S (disjoint_empty_left S)
  rw [empty_union, frame_zero, Matrix.mul_one, OBase.deltas_eq] at h
  rw [h, ← Matrix.mul_assoc, shift_sq, Matrix.one_mul]

end
end OAI.PowerSaving.BaseUnit

namespace OAI.PowerSaving.BaseUnit
open Binary Matrix Finset GenMove StageGauge

noncomputable section

def Zf (g : Gm) (k : ℕ) (q : Fin 891) : CMat Lb := (ex_Z k g q).choose

end
end OAI.PowerSaving.BaseUnit

namespace OAI.PowerSaving.BaseUnit
open Binary Matrix Finset GenMove StageGauge

noncomputable section

section Cost
variable (φ : ℕ → ℝ)

lemma lc_ins (b : ℕ × ℕ) : ∀ l, listCost φ (ins b l) = listCost φ (b :: l)
  | [] => rfl
  | c :: l => by
    simp only [ins]
    split_ifs with h1 h2
    · simp only [listCost_cons, h1]; push_cast; ring
    · rfl
    · rw [listCost_cons, lc_ins b l, listCost_cons, listCost_cons, listCost_cons]; ring

lemma lc_nrm : ∀ l, listCost φ (nrm l) = listCost φ l
  | [] => rfl
  | b :: l => by rw [show nrm (b :: l) = ins b (nrm l) from rfl, lc_ins, listCost_cons, lc_nrm l, listCost_cons]

end Cost

section Count
open Histogram
variable (r : ℕ)

lemma hF_ins (b : ℕ × ℕ) : ∀ l, histFn (ins b l) r = histFn (b :: l) r
  | [] => rfl
  | c :: l => by
    simp only [ins]
    split_ifs with h1 h2
    · simp only [histFn_cons, h1]; split_ifs <;> omega
    · rfl
    · rw [histFn_cons, hF_ins b l, histFn_cons, histFn_cons, histFn_cons]; omega

lemma hF_nrm : ∀ l, histFn (nrm l) r = histFn l r
  | [] => rfl
  | b :: l => by rw [show nrm (b :: l) = ins b (nrm l) from rfl, hF_ins, histFn_cons, hF_nrm l, histFn_cons]

lemma hF_app (a b : List (ℕ × ℕ)) : histFn (a ++ b) r = histFn a r + histFn b r := by
  simp [histFn, List.filter_append]

lemma hF_map (h : ℕ → ℕ) (n : ℕ) : ∀ L : List ℕ, histFn (L.map fun x => (h x, n)) r =
    n * (L.map fun x => if h x = r then 1 else 0).sum
  | [] => rfl
  | x :: L => by rw [List.map_cons, histFn_cons, hF_map h n L, List.map_cons, List.sum_cons]; split_ifs <;> ring

def hk (κ : Bool) : ℕ := ((ControlCheck.Packed.nTab κ).map fun x => if 1 + 8 * (x + 1) = r then 1 else 0).sum

lemma sched_sum : ∑ q : Fin 891, (if sr q = r then 1 else 0) =
    (StageRoute.schedRes.map fun x => if x = r then 1 else 0).sum := by
  rw [RAM.sum_map_getD _ 0, sched_ok.1]
  exact Fin.sum_univ_eq_sum_range (fun i => if StageRoute.schedRes.getD i 0 = r then 1 else 0) 891

end Count

abbrev Kv := (Fin 104 × Fin 36) ⊕ (Fin 17 × Fin 891)
abbrev Lw := Gm × Kv

def Ss : Kv → Finset Lb
  | .inl (c, i) => Sx (sd c) i
  | .inr (_, q) => Dr q
def Bs : Lw → OBase Lb
  | (g, .inl (c, _)) => Ab g c
  | _ => OBase.canonical Lb
def tr (l : Lw) : ℕ := (Ss l.2).card
def tz (l : Lw) : Fin (tr l) → Space Lb := (Bs l).fam (Ss l.2)

end
end OAI.PowerSaving.BaseUnit

private theorem marker_submission_work_u7604_seg (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_submission_work_u7604_call (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_submission_work_u7604_word (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial

private theorem marker_submission_work_u7604_raw (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
end

section

set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace OAI.PowerSaving.Batch48
open Binary Matrix Finset GenMove StageGauge OAI.PowerSaving.BaseUnit ControlCheck

noncomputable section

def dg (b : Bool) (i : ℕ) : ℕ := (if b then TplR.diag else TplA.diag).getD i 0
theorem dg_ok : ∀ b : Bool, ∀ i : Fin 34, i.val < (if b then 30 else 34) →
    dg b i % 16 = (if b then 1 else 3) ∧ dg b i / 16 % 2 = 0 := by decide +kernel
def scl (n : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := l.map fun b => (b.1, n * b.2)
def PT (b : Bool) : List (ℕ × ℕ) := (List.range 17).flatMap fun j => (tLoc b j).flatMap eBlk
theorem pay_ok : nrm (scl 48 stageBlockHist ++ (scl 120 (PT false) ++ scl 192 (PT true))) = blockHist := by
  decide +kernel
def TT (b : Bool) (n : ℕ) : List ℕ := (List.range n).map fun i => 1 + 8 * pc (dg b i / 16)
theorem tgt_ok48 : nrm ((TT false 34).map (fun x => (x, 120)) ++ ((TT true 30).map (fun x => (x, 192)) ++
    StageRoute.schedRes.map fun x => (x, 48))) = targetHist := by decide +kernel
theorem n_ok : (univ.filter fun r : Fin 312 => bR r = false).card = 120 ∧ (univ.filter fun r : Fin 312 => bR r = true).card = 192
    ∧ (univ.filter fun r : Fin 312 => (!bR r) = true).card = 120 := by decide +kernel

lemma root_fin (f : ℕ) (g : Gm) (r : Fin 312) (u : ℕ → Sky Lb f → ℂ) (i : ℕ) (hi : i < if bR r then 30 else 34) :
    SEP f g r (preT (bR r) 16) u i = monoVI (qv f (A0 g)) (Lv f (A0 g)) (fun _ => Complex.I) (DP f g r) 17 (dg (bR r) i) * u i := by
  have hι : (fun _ : Sky Lb f => Complex.I) ^ 2 = -1 := by funext; simp
  rw [SEP, pre_evs]
  cases hb : bR r <;> rw [hb] at hi <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi ⊢
  · exact TplA.ctrl_diag _ _ _ _ (q4 f (A0 g)) (L2 f (A0 g)) hι u i hi
  · exact TplR.ctrl_diag _ _ _ _ (q4 f (A0 g)) (L2 f (A0 g)) hι u i hi

lemma mono_val (f : ℕ) (g : Gm) (r : Fin 312) (d : ℕ) (hd : d % 16 = if bR r then 1 else 3) (h2 : d / 16 % 2 = 0) :
    monoVI (qv f (A0 g)) (Lv f (A0 g)) (fun _ => Complex.I) (DP f g r) 17 d =
      (if bR r then 1 else qv f (A0 g) ^ 2) * Pf f (A0 g) (insert pv (bankSet (Batch.Sched.sig r) (d / 16))) := by
  obtain ⟨hm, -, hp⟩ := mask_frame f (A0 g) (Batch.Sched.sig r) (d / 16) (sig_ok r _ h2)
  have hm' : ControlCheck.dp (DP f g r) 17 (d / 16) = Pf f (A0 g) (bankSet (Batch.Sched.sig r) (d / 16)) := hm
  rw [monoVI, hm', insert_eq, Pf_union f _ (disjoint_singleton_left.2 hp)]
  cases hb : bR r <;> rw [hb] at hd <;> simp only [Bool.false_eq_true, ↓reduceIte] at hd ⊢
  · rw [show d % 4 = 3 by omega, show d / 4 % 2 = 0 by omega, show d / 8 % 2 = 0 by omega]; simp only [qv]; ring
  · rw [show d % 4 = 1 by omega, show d / 4 % 2 = 0 by omega, show d / 8 % 2 = 0 by omega]; simp only [qv]; ring

lemma tgt_eq (f : ℕ) (A : OBase Lb) (S : Finset Lb) (c : Bool) (w v : Sky Lb f → ℂ)
    (h : wl f w = (if c then 1 else qv f A ^ 2) * Pf f A S * wl f v) :
    matAct f (shift ((if c then 0 else A.v pv) + A.corr S)) w = matAct f (blockMat (A.fam S)) v := by
  apply wl_inj f
  rw [shift_phase, wl_wrap, h, bm_eq, ← matAct_mul, shift_phase, wl_wrap, wl_fr]
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_add, one_mul]
  · rw [show pF f (fun x => sign (dot (A.v pv + A.corr S) x)) = qv f A ^ 2 * pF f (fun x => sign (dot (A.corr S) x)) from by
      rw [q2, ← pF_mul]; exact congrArg (pF f) (funext fun x => by rw [dot_add_left, sign_add]; rfl)]
    simp only [Pf]
    linear_combination (pF f (fun x => sign (dot (A.corr S) x)) * pF f (fF A S) * wl f v) * q4 f A
  · simp only [Pf]

abbrev KR := (Fin 120 × Fin 34) ⊕ (Fin 192 × Fin 30)
abbrev KB := KR ⊕ (Fin 48 × Fin NQ)
abbrev LwB := Gm × KB

def ro : KR → Fin 312 × Fin 40
  | .inl (a, i) => (⟨a, by have := a.isLt; omega⟩, ⟨i, by have := i.isLt; omega⟩)
  | .inr (b, i) => (⟨120 + b, by have := b.isLt; omega⟩, ⟨i, by have := i.isLt; omega⟩)

lemma ro_inj : Function.Injective ro := by
  rintro (⟨a, i⟩ | ⟨a, i⟩) (⟨b, j⟩ | ⟨b, j⟩) h <;> simp only [ro, Prod.mk.injEq, Fin.mk.injEq] at h
  · rw [Fin.ext h.1, Fin.ext h.2]
  · have := a.isLt; omega
  · have := b.isLt; omega
  · rw [Fin.ext (show a.val = b.val by omega), Fin.ext h.2]

lemma ro_ok (x : KR) : (ro x).2.val < if bR (ro x).1 then 30 else 34 := by
  rcases x with ⟨a, i⟩ | ⟨b, i⟩
  · have := a.isLt; simp [ro, bR, Batch.Sched.isR, show ¬ 120 ≤ a.val by omega]
  · simp [ro, bR, Batch.Sched.isR]

lemma dgx (x : KR) : dg (bR (ro x).1) (ro x).2 % 16 = (if bR (ro x).1 then 1 else 3) ∧
    dg (bR (ro x).1) (ro x).2 / 16 % 2 = 0 :=
  dg_ok _ ⟨(ro x).2, by have := ro_ok x; split_ifs at this <;> omega⟩ (ro_ok x)

def eB : LwB → Rl'
  | (g, .inl x) => (g, .inl (ro x))
  | (g, .inr h) => (g, .inr (.inr h))

lemma eB_inj : Function.Injective eB := by
  rintro ⟨g, x | h⟩ ⟨g', x' | h'⟩ e <;>
    simp only [eB, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false, false_and] at e
  · rw [e.1, ro_inj e.2]
  · rw [e.1, e.2]

def SB : KB → Finset Lb
  | .inl x => insert pv (bankSet (Batch.Sched.sig (ro x).1) (dg (bR (ro x).1) (ro x).2 / 16))
  | .inr (_, q) => Dr q
def BB : LwB → OBase Lb
  | (g, .inl _) => A0 g
  | _ => OBase.canonical Lb
def trB (l : LwB) : ℕ := (SB l.2).card
def tzB (l : LwB) : Fin (trB l) → Space Lb := (BB l).fam (SB l.2)

lemma pc_le (x : ℕ) : pc x ≤ 17 := (List.length_filter_le _ _).trans (by simp)

lemma card_SB (x : KR) : (SB (.inl x)).card = 1 + 8 * pc (dg (bR (ro x).1) (ro x).2 / 16) := by
  obtain ⟨-, hc, hp⟩ := mask_frame 0 (A0 Orth.one) (Batch.Sched.sig (ro x).1) (dg (bR (ro x).1) (ro x).2 / 16)
    (sig_ok _ _ (dgx x).2)
  rw [SB, card_insert_of_notMem hp, hc, card_bits]; ring

def zB (g : Gm) (r : Fin 312) (i : Fin 40) : Space Lb :=
  (if bR r then 0 else (A0 g).v pv) + (A0 g).corr (insert pv (bankSet (Batch.Sched.sig r) (dg (bR r) i / 16)))

def FSB : Finset Rl' := univ ×ˢ ((univ : Finset (Fin 48 × Fin NQ)).map ⟨fun h => Sum.inr (Sum.inr h), fun a b h => by
  simpa using h⟩)
def MSB : Finset Rl' := univ ×ˢ ((univ : Finset KR).map ⟨fun x => Sum.inl (ro x), fun a b h => ro_inj (by simpa using h)⟩)

lemma mem_FSB {x : Rl'} : x ∈ FSB ↔ ∃ h, x.2 = .inr (.inr h) := by
  simp only [FSB, mem_product, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
  constructor <;> rintro ⟨h, e⟩ <;> exact ⟨h, e.symm⟩
lemma mem_MSB {x : Rl'} : x ∈ MSB ↔ ∃ y, x.2 = .inl (ro y) := by
  simp only [MSB, mem_product, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
  constructor <;> rintro ⟨y, e⟩ <;> exact ⟨y, e.symm⟩
attribute [irreducible] FSB MSB

def rFB (F : Gm → Fin 48 → Fin NQ → CMat Lb) : Rl' → CMat Lb
  | (g, .inr (.inr h)) => F g h.1 h.2
  | _ => 1
def rMB (F : Gm → Fin 312 → Fin 40 → CMat Lb) : Rl' → CMat Lb
  | (g, .inl ri) => F g ri.1 ri.2
  | _ => 1

theorem prepB : ∃ U : Rl' → CMat Lb, (∀ x ∈ FSB, U x * 1 = rFB (fun g τ q => Zf g (kτ τ) q) x) ∧
    RealisedOp (fun f y x => if x ∈ FSB then matAct f (U x) (y x) else y x) (fun φ => ∑ x ∈ FSB, (fun _ => (0 : ℝ)) φ) :=
  RealisedOp.steps FSB _ _ _ fun x hx => by
    obtain ⟨⟨τ, q⟩, h⟩ := mem_FSB.1 hx; obtain ⟨g, x⟩ := x; simp only at h; subst h
    exact (ex_Z (kτ τ) g q).choose_spec.1 _ _

theorem endB : ∃ U : Rl' → CMat Lb, (∀ x ∈ FSB, U x * rFB (fun g τ q => Wn (kτ τ) g q * Zf g (kτ τ) q) x =
      rFB (fun _ _ q => coordFrame (Dr q)) x) ∧
    RealisedOp (fun f y x => if x ∈ FSB then matAct f (U x) (y x) else y x) (fun φ => ∑ x ∈ FSB, RankCost.bcost φ 0) :=
  RealisedOp.steps FSB _ _ _ fun x hx => by
    obtain ⟨⟨τ, q⟩, h⟩ := mem_FSB.1 hx; obtain ⟨g, x⟩ := x; simp only at h; subst h
    exact (ex_Z (kτ τ) g q).choose_spec.2 _ _

theorem shiftB : ∃ U : Rl' → CMat Lb, (∀ x ∈ MSB, U x * 1 = rMB (fun g r i => shift (zB g r i)) x) ∧
    RealisedOp (fun f y x => if x ∈ MSB then matAct f (U x) (y x) else y x) (fun φ => ∑ x ∈ MSB, (fun _ => (0 : ℝ)) φ) :=
  RealisedOp.steps MSB _ _ _ fun x hx => by
    obtain ⟨y, h⟩ := mem_MSB.1 hx; obtain ⟨g, x⟩ := x; simp only at h; subst h
    show GStep _ (1 : CMat Lb) (shift (zB g (ro y).1 (ro y).2)) _
    simpa using gstep_free (Free.shift (zB g (ro y).1 (ro y).2)) (g, Sum.inl (ro y)) (1 : CMat Lb)

lemma lc_scl (φ : ℕ → ℝ) (n : ℕ) : ∀ l, listCost φ (scl n l) = n * listCost φ l
  | [] => by simp [scl, listCost]
  | b :: l => by
    have := lc_scl φ n l; simp only [scl] at this ⊢
    rw [List.map_cons, listCost_cons, this, listCost_cons]; push_cast; ring

lemma lc_fr (φ : ℕ → ℝ) (F : ℕ → List (ℕ × ℕ)) : ∀ n, listCost φ ((List.range n).flatMap F) = ∑ j ∈ range n, listCost φ (F j)
  | 0 => by simp [listCost]
  | n + 1 => by rw [List.range_succ, List.flatMap_append, listCost_app, lc_fr φ F n, sum_range_succ]; simp

lemma lsum (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, lsum f n, sum_range_succ]; simp

lemma cnt (b : Bool) (j : ℕ) (hj : j < 16) :
    ∑ τ ∈ range 48, ((univ.filter fun r => gtB τ b j r = true).card : ℝ) = ((univ.filter fun r : Fin 312 => bR r = b).card : ℝ) := by
  have hnat : (univ.filter fun r : Fin 312 => bR r = b).card =
      ∑ τ ∈ range 48, (univ.filter fun r : Fin 312 => gtB τ b j r = true).card := by
    rw [card_eq_sum_card_fiberwise (f := fun r : Fin 312 => Batch.Sched.vCall r j) (t := range 48)
      (by intro r _; exact mem_range.2 (Batch.Sched.range_P r j r.2 hj).1)]
    refine sum_congr rfl fun τ _ => congrArg card ?_
    ext r; simp [gtB, filter_filter]
  rw [← Nat.cast_sum, Nat.cast_inj]
  exact hnat.symm

lemma runC_eq (φ : ℕ → ℝ) : runC 48 φ = GC * listCost φ blockHist := by
  have hc : ∀ b : Bool, ∀ j ∈ range 16, ∑ τ ∈ range 48, segCost (gtB τ b j) (tLoc b (j + 1)) φ =
      GC * ((univ.filter fun r : Fin 312 => bR r = b).card * listCost φ ((tLoc b (j + 1)).flatMap eBlk)) := by
    intro b j hj
    simp only [segCost, ← mul_sum, ← sum_mul, cnt b j (mem_range.1 hj)]
  have hp : StageRoute.price φ = listCost φ stageBlockHist := by
    simp [StageRoute.price, listCost, stageBlockHist] <;> ring
  rw [← pay_ok, lc_nrm, listCost_app, listCost_app, lc_scl, lc_scl, lc_scl, ← hp, PT, PT, lc_fr, lc_fr,
    sum_range_succ', sum_range_succ' _ 16, runC]
  simp only [stepC, scB, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [sum_comm (s := range 48) (t := range 16), sum_comm (s := range 48) (t := range 16), sum_congr rfl (hc false),
    sum_congr rfl (hc true)]
  simp only [segCost, ← mul_sum, n_ok.1, n_ok.2.1, n_ok.2.2]
  push_cast; ring

lemma tsum_T (b : Bool) (r n : ℕ) :
    ∑ i : Fin n, (if 1 + 8 * pc (dg b i / 16) = r then 1 else 0) = ((TT b n).map fun x => if x = r then 1 else 0).sum := by
  rw [TT, List.map_map, lsum, ← Fin.sum_univ_eq_sum_range]; try rfl

lemma card_SBA (a : Fin 120) (i : Fin 34) : (SB (.inl (.inl (a, i)))).card = 1 + 8 * pc (dg false i / 16) := by
  rw [card_SB, show bR (ro (.inl (a, i))).1 = false by
    have := a.isLt; simp [ro, bR, Batch.Sched.isR, show ¬ 120 ≤ a.val by omega]]; rfl
lemma card_SBR (b : Fin 192) (i : Fin 30) : (SB (.inl (.inr (b, i)))).card = 1 + 8 * pc (dg true i / 16) := by
  rw [card_SB, show bR (ro (.inr (b, i))).1 = true by simp [ro, bR, Batch.Sched.isR]]; rfl
lemma card_SBH (h : Fin 48 × Fin NQ) : (SB (.inr h)).card = sr h.2 := Dr_card _

lemma tgt_count (r : ℕ) : ∑ y : KB, (if (SB y).card = r then 1 else 0) = Histogram.histFn targetHist r := by
  rw [← tgt_ok48, hF_nrm, hF_app, hF_app, hF_map r (fun x => x) 120, hF_map r (fun x => x) 192, hF_map r (fun x => x) 48,
    Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [card_SBA, card_SBR, card_SBH, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, tsum_T, sched_sum]
  ring

theorem raw_B48 : ∃ w : GWord Lb Rl', w.Proper (Fintype.card Lb) ∧
    (∀ r, w.hist r = Fintype.card Gm * Histogram.histFn blockHist r) ∧ LiveKernel.GLiveKernelM eB (fun l => blockMat (tzB l)) w := by
  obtain ⟨U1, hU1, R1⟩ := prepB
  obtain ⟨O2, R2, S2⟩ := run_spec 48 le_rfl
  obtain ⟨U3, hU3, R3⟩ := endB
  obtain ⟨U4, hU4, R4⟩ := shiftB
  obtain ⟨w, hw, hc, hg⟩ := ((R1.trans R2).trans R3).trans R4
  refine ⟨w, hw, fun r => ?_, fun f v hv l => ?_⟩
  · have h := hc (fun q => if q = r then 1 else 0)
    beta_reduce at h
    rw [GWord.costR_shadow, BWord.costR_ind, runC_eq, listCost_ind] at h
    simp [RankCost.bcost] at h
    exact_mod_cast h
  · rw [hg]
    have hFr : ∀ g (ri : Fin 312 × Fin 40), ((g, .inl ri) : Rl') ∉ FSB := fun g ri h => by
      obtain ⟨_, e⟩ := mem_FSB.1 h; cases e
    have hy : InvP f (fun x => if x ∈ FSB then matAct f (U1 x) (v x) else v x) := by
      intro g r i hi
      by_cases h40 : i < 40
      · have hf : (fi i).val = i := Nat.mod_eq_of_lt h40
        have e : v (g, .inl (r, fi i)) = 0 := hv _ fun l e => by
          rcases l with ⟨g', x | h⟩
          · simp only [eB, Prod.mk.injEq, Sum.inl.injEq] at e
            have h2 := congrArg (fun p : Fin 312 × Fin 40 => p.2.val) e.2
            have := ro_ok x
            simp only at h2; split_ifs at this <;> omega
          · simp [eB] at e
        show (if i < 40 then wl f (if _ ∈ FSB then _ else v _) else 0) = 0
        rw [if_pos h40, if_neg (hFr g (r, fi i)), e]; simp [wl]
      · exact if_neg h40
    rcases l with ⟨g, x | ⟨τ, q⟩⟩
    · have hM : ((g, .inl (ro x)) : Rl') ∈ MSB := mem_MSB.2 ⟨x, rfl⟩
      have e4 : U4 (g, .inl (ro x)) = shift (zB g (ro x).1 (ro x).2) := by have := hU4 _ hM; rwa [Matrix.mul_one] at this
      simp only [eB, hM, hFr g (ro x), if_true, if_false, ↓reduceIte]
      rw [e4]
      have h1 := congrFun ((S2 f _ hy).2.1 g (ro x).1) (ro x).2.val
      beta_reduce at h1
      rw [nv48, root_fin f g _ _ _ (ro_ok x), mono_val f g _ (dg (bR (ro x).1) (ro x).2) (dgx x).1 (dgx x).2] at h1
      simp only [VP, if_pos (ro x).2.isLt, fi_val, Prod.mk.eta, hFr g (ro x), ↓reduceIte] at h1
      exact tgt_eq f (A0 g) (SB (.inl x)) (bR (ro x).1) _ _ h1
    · have hF' : ((g, .inr (.inr (τ, q))) : Rl') ∈ FSB := mem_FSB.2 ⟨(τ, q), rfl⟩
      have hM' : ((g, .inr (.inr (τ, q))) : Rl') ∉ MSB := fun h => by obtain ⟨y, e⟩ := mem_MSB.1 h; cases e
      have e1 : U1 (g, .inr (.inr (τ, q))) = Zf g (kτ τ) q := by have := hU1 _ hF'; rwa [Matrix.mul_one] at this
      have e3 : U3 (g, .inr (.inr (τ, q))) * (Wn (kτ τ) g q * Zf g (kτ τ) q) = coordFrame (Dr q) := hU3 _ hF'
      simp only [eB, hM', hF', (S2 f _ hy).2.2 g τ q, decide_eq_true τ.isLt, if_true, if_false, ↓reduceIte, e1]
      rw [matAct_mul, matAct_mul, Matrix.mul_assoc, e3]
      exact congrArg (fun M => matAct f M _) (pk_eq_blockMat _)

theorem rawCert_exists_B48 : ∃ (α ρ σ : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Fintype ρ)
    (_ : DecidableEq ρ) (_ : Fintype σ) (_ : DecidableEq σ),
    ∃ (e : σ → ρ) (tr : σ → ℕ) (tz : ∀ l, Fin (tr l) → Space α) (wd : GWord α ρ) (G : ℕ),
      Function.Injective e ∧ (∀ l, LinearIndependent F (tz l)) ∧ wd.Proper (Fintype.card α) ∧
      LiveKernel.GLiveKernelM e (fun l => blockMat (tz l)) wd ∧
      1 ≤ G ∧ Fintype.card α = 137 ∧
      (∀ l, 1 ≤ tr l ∧ tr l ≤ 137) ∧
      (∀ r, (Finset.univ.filter fun l => tr l = r).card = G * Histogram.histFn targetHist r) ∧
      (∀ r, wd.hist r = G * Histogram.histFn blockHist r) := by
  obtain ⟨w, hw, hh, hK⟩ := raw_B48
  refine ⟨Lb, Rl', LwB, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    eB, trB, tzB, w, Fintype.card Gm, eB_inj, fun l => OBase.fam_indep _ _, hw, hK,
    Fintype.card_pos_iff.2 ⟨StageGauge.Orth.one⟩, StageFrames.card_LC137 0 hH9, ?_, fun r => ?_, hh⟩
  · rintro ⟨g, x | ⟨τ, q⟩⟩
    · show 1 ≤ (SB (.inl x)).card ∧ (SB (.inl x)).card ≤ 137
      rw [card_SB]; have := pc_le (dg (bR (ro x).1) (ro x).2 / 16); omega
    · show 1 ≤ (Dr q).card ∧ (Dr q).card ≤ 137
      have := sr_le q; rw [Dr_card]; omega
  · have e : (univ.filter fun l : LwB => trB l = r) = univ ×ˢ (univ.filter fun y : KB => (SB y).card = r) := by
      ext ⟨x, y⟩; rw [mem_filter, mem_product, mem_filter]; simp [trB]
    rw [e, card_product, card_univ, card_filter, tgt_count]
#print axioms OAI.PowerSaving.Batch48.rawCert_exists_B48

end
end OAI.PowerSaving.Batch48

private theorem marker_submission_work_b48_rawcert (if_youre_an_ai_editing_this_make_sure_real_work_and_not_rebrand_without_coding_work_if_in_doubt_ask_your_supervisor_and_also_read_related_posts_to_make_sure_you_understand_whats_going_on : Unit) : True := trivial
end

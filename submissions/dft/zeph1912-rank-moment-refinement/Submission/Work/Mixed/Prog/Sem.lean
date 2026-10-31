import Submission.Work.Block.Peel

/-!
# Mixed engine, R3 program part 0: the semantics of a job (agent rb-r3prog, 14 Oct 2026)

A *job* of the lockstep class tree (rl-prove Theorem 1G, realised as in lg-g2/DESIGN.md
section 4) is ONE vector of `2^n` entries on which the Walsh-Hadamard kernel must be applied
to the LOW `h` address bits only; the high `n - h` bits are batch.

* `maskK n h`       the kernel on the coordinates `i < h` of `Bits n`, the identity elsewhere;
* `hlow n h v`      the job's answer (`maskK n h *ᵥ v`);
* `maskK_full`      `h ≥ n`: the whole kernel (`ripple`);
* `maskHi_mul_maskK`, `maskK_mul_maskHi`
                    **commuting Hadamards on disjoint bits**: the low part and the high part
                    compose, in either order, to the whole kernel (top split, rests, exits);
* `catB a b`        `Bits a × Bits b ≃ Bits (a+b)`, low part first; `catB_loc` its address;
* `placeS`          where the instance `q` and the label `y` of ONE role land in a job:
                    the block coordinates of a splitting `S` are the low bits, the rest of the
                    label next, the instance on top;
* `hlow_placeS`     **the job answer is the block (or target) action on every instance**:
                    `hlow n (k*f)` read through `placeS` is `matAct f (S.lift (kernel (Fin k)))`.

The last lemma is what makes every block letter of a class ONE lockstep child call, and every
live role (target `blockMat (tgtDir l) = S.lift (kernel (Fin k))`) a job of the class.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section

/-! ## 1. Jobs: the kernel on the low bits -/

/-- The kernel on the coordinates `i < h`, the identity on the others. -/
def maskK (n h : ℕ) : CMat (Fin n) :=
  digitProd fun i : Fin n => if i.val < h then littleC else (1 : Matrix F F ℂ)

/-- The kernel on the coordinates `i ≥ h`, the identity on the others. -/
def maskHi (n h : ℕ) : CMat (Fin n) :=
  digitProd fun i : Fin n => if h ≤ i.val then littleC else (1 : Matrix F F ℂ)

/-- **The answer of a job**: the kernel on the low `h` bits of a vector of `2^n` entries. -/
def hlow (n h : ℕ) (v : Bits n → ℂ) : Bits n → ℂ := maskK n h *ᵥ v

lemma maskK_full (n h : ℕ) (hn : n ≤ h) : maskK n h = kernel (Fin n) := by
  unfold maskK kernel
  congr 1
  funext i
  rw [if_pos (by omega)]

lemma hlow_full (n h : ℕ) (hn : n ≤ h) (v : Bits n → ℂ) : hlow n h v = ripple n v := by
  unfold hlow ripple
  rw [maskK_full n h hn]

lemma maskK_zero (n : ℕ) : maskK n 0 = 1 := by
  unfold maskK
  simp only [Nat.not_lt_zero, if_false]
  exact digitProd_one

lemma hlow_zero (n : ℕ) (v : Bits n → ℂ) : hlow n 0 v = v := by
  unfold hlow; rw [maskK_zero, Matrix.one_mulVec]

/-- **Commuting Hadamards on disjoint bits** (high part after low part). -/
lemma maskHi_mul_maskK (n h : ℕ) : maskHi n h * maskK n h = kernel (Fin n) := by
  unfold maskHi maskK kernel
  rw [digitProd_mul]
  congr 1
  funext i
  by_cases hi : i.val < h
  · rw [if_neg (by omega), if_pos hi, Matrix.one_mul]
  · rw [if_pos (by omega), if_neg hi, Matrix.mul_one]

/-- **Commuting Hadamards on disjoint bits** (low part after high part). -/
lemma maskK_mul_maskHi (n h : ℕ) : maskK n h * maskHi n h = kernel (Fin n) := by
  unfold maskHi maskK kernel
  rw [digitProd_mul]
  congr 1
  funext i
  by_cases hi : i.val < h
  · have h2 : ¬ h ≤ i.val := by omega
    simp only [hi, h2, if_true, if_false, Matrix.mul_one]
  · have h2 : h ≤ i.val := by omega
    simp only [hi, h2, if_true, if_false, Matrix.one_mul]

/-- The high part of a job. -/
def hhigh (n h : ℕ) (v : Bits n → ℂ) : Bits n → ℂ := maskHi n h *ᵥ v

lemma hhigh_hlow (n h : ℕ) (v : Bits n → ℂ) : hhigh n h (hlow n h v) = ripple n v := by
  unfold hhigh hlow ripple
  rw [Matrix.mulVec_mulVec, maskHi_mul_maskK]

lemma hlow_hhigh (n h : ℕ) (v : Bits n → ℂ) : hlow n h (hhigh n h v) = ripple n v := by
  unfold hhigh hlow ripple
  rw [Matrix.mulVec_mulVec, maskK_mul_maskHi]

/-! ## 2. Concatenating bit strings (low part first) -/

/-- `Bits a × Bits b ≃ Bits (a+b)`; the first factor gives the low coordinates. -/
def catB (a b : ℕ) : Bits a × Bits b ≃ Bits (a+b) where
  toFun p := Fin.append p.1 p.2
  invFun z := (fun i => z (Fin.castAdd b i), fun i => z (Fin.natAdd a i))
  left_inv p := by
    obtain ⟨x, y⟩ := p
    simp only [Fin.append_left, Fin.append_right]
  right_inv z := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]

lemma catB_apply (a b : ℕ) (p : Bits a × Bits b) : catB a b p = Fin.append p.1 p.2 := rfl

lemma catB_loc (a b : ℕ) (p : Bits a × Bits b) :
    (bits (a+b)).loc (catB a b p) = (bits a).loc p.1 + 2^a * (bits b).loc p.2 := by
  rw [bits_loc, bits_loc, bits_loc, Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    rw [catB_apply, Fin.append_left]; rfl
  · apply Finset.sum_congr rfl; intro i _
    rw [catB_apply, Fin.append_right, Fin.val_natAdd, pow_add]; ring

lemma maskK_catB (a b : ℕ) (x x' : Bits a) (y y' : Bits b) :
    maskK (a+b) a (catB a b (x,y)) (catB a b (x',y')) =
      kernel (Fin a) x x' * (if y = y' then 1 else 0) := by
  unfold maskK kernel
  rw [digitProd_apply, Fin.prod_univ_add, digitProd_apply, ← prod_delta]
  congr 1
  · apply Finset.prod_congr rfl; intro i _
    simp only [catB_apply, Fin.append_left, Fin.val_castAdd, i.isLt, if_true]
  · apply Finset.prod_congr rfl; intro i _
    simp only [catB_apply, Fin.append_right, Fin.val_natAdd]
    rw [if_neg (by omega), Matrix.one_apply]

lemma maskHi_catB (a b : ℕ) (x x' : Bits a) (y y' : Bits b) :
    maskHi (a+b) a (catB a b (x,y)) (catB a b (x',y')) =
      (if x = x' then 1 else 0) * kernel (Fin b) y y' := by
  unfold maskHi kernel
  rw [digitProd_apply, Fin.prod_univ_add, digitProd_apply, ← prod_delta]
  congr 1
  · apply Finset.prod_congr rfl; intro i _
    simp only [catB_apply, Fin.append_left, Fin.val_castAdd]
    rw [if_neg (by omega), Matrix.one_apply]
  · apply Finset.prod_congr rfl; intro i _
    simp only [catB_apply, Fin.append_right, Fin.val_natAdd]
    rw [if_pos (by omega)]

/-- Renaming the length of a bit string. -/
def castB {a b : ℕ} (h : a = b) : Bits a ≃ Bits b := Layout.permFn (finCongr h) F

lemma castB_apply {a b : ℕ} (h : a = b) (x : Bits a) (i : Fin b) :
    castB h x i = x (Fin.cast h.symm i) := rfl

lemma castB_loc {a b : ℕ} (h : a = b) (x : Bits a) :
    (bits b).loc (castB h x) = (bits a).loc x := by
  subst h
  rfl

lemma maskK_castB {a b : ℕ} (h : a = b) (k : ℕ) (x x' : Bits a) :
    maskK b k (castB h x) (castB h x') = maskK a k x x' := by
  subst h
  rfl

/-! ## 3. Where one role of one instance lands in a job -/

section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {k : ℕ}

/-- The label of one role at column `f`, read through a splitting `S`: the block coordinates
(`k*f` bits) low, the rest of the label (`X'.n*f` bits, in the order of `book X' 0 f`) high. -/
def pinS (S : Split α β (Fin k)) (X' : Layout β) (f : ℕ) : Sky α f ≃ Bits (k*f + X'.n*f) :=
  ((Equiv.uniqueProd (Sky α f) (Bits 0)).symm.trans (S.peel 0 f)).trans
    ((Equiv.prodCongr (serial X' 0 f (Nat.add_zero _)) (Equiv.refl _)).trans
      ((Equiv.prodComm _ _).trans (catB (k*f) (X'.n*f))))

lemma uniqueProd_symm_bits0 (f : ℕ) (y : Sky α f) :
    (Equiv.uniqueProd (Sky α f) (Bits 0)).symm y = (0, y) :=
  Prod.ext (Subsingleton.elim _ _) rfl

/-- The peeled pair of a label. -/
lemma pinS_apply (S : Split α β (Fin k)) (X' : Layout β) (f : ℕ) (y : Sky α f) :
    pinS S X' f y = catB (k*f) (X'.n*f)
      ((S.peel 0 f (0, y)).2, serial X' 0 f (Nat.add_zero _) (S.peel 0 f (0, y)).1) := by
  simp only [pinS, Equiv.trans_apply, uniqueProd_symm_bits0, Equiv.prodCongr_apply,
    Equiv.coe_refl, Equiv.prodComm_apply]
  rfl

lemma pinS_loc (S : Split α β (Fin k)) (X' : Layout β) (f : ℕ) (y : Sky α f) :
    (bits (k*f + X'.n*f)).loc (pinS S X' f y) =
      (bits (k*f)).loc (S.peel 0 f (0, y)).2 +
        2^(k*f) * (book X' 0 f).loc (S.peel 0 f (0, y)).1 := by
  rw [pinS_apply, catB_loc, serial_code]

/-- **Placement of one instance of one role in a job of `2^n` entries**: block coordinates low,
rest of the label next, the instance number `q` (`r` bits) on top. -/
def placeS (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) : Bits r × Sky α f ≃ Bits n :=
  (Equiv.prodComm _ _).trans ((Equiv.prodCongr (pinS S X' f) (Equiv.refl _)).trans
    ((catB (k*f + X'.n*f) r).trans (castB h)))

lemma placeS_apply (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (q : Bits r) (y : Sky α f) :
    placeS S X' f r n h (q, y) = castB h (catB _ r (pinS S X' f y, q)) := rfl

lemma placeS_loc (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (q : Bits r) (y : Sky α f) :
    (bits n).loc (placeS S X' f r n h (q, y)) =
      (bits (k*f)).loc (S.peel 0 f (0, y)).2 +
        2^(k*f) * (book X' 0 f).loc (S.peel 0 f (0, y)).1 +
        2^(k*f + X'.n*f) * (bits r).loc q := by
  rw [placeS_apply, castB_loc, catB_loc, pinS_loc]

/-- The mask kernel read through the placement: block kernel on the fibre, identity on the
rest of the label and on the instance. -/
lemma maskK_placeS (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (q q' : Bits r) (y y' : Sky α f) :
    maskK n (k*f) (placeS S X' f r n h (q, y)) (placeS S X' f r n h (q', y')) =
      (if (q = q' ∧ (S.sky f y).1 = (S.sky f y').1) then
        kernel (Fin (k*f)) (flat k f (S.sky f y).2) (flat k f (S.sky f y').2) else 0) := by
  rw [placeS_apply, placeS_apply, maskK_castB]
  -- split off the instance bits
  have e1 : maskK (k*f + X'.n*f + r) (k*f) (catB _ r (pinS S X' f y, q))
      (catB _ r (pinS S X' f y', q')) =
      maskK (k*f + X'.n*f) (k*f) (pinS S X' f y) (pinS S X' f y') *
        (if q = q' then 1 else 0) := by
    unfold maskK
    rw [digitProd_apply, Fin.prod_univ_add, digitProd_apply, ← prod_delta]
    congr 1
    · apply Finset.prod_congr rfl; intro i _
      simp only [catB_apply, Fin.append_left, Fin.val_castAdd]
    · apply Finset.prod_congr rfl; intro i _
      simp only [catB_apply, Fin.append_right, Fin.val_natAdd]
      rw [if_neg (by omega), Matrix.one_apply]
  rw [e1, pinS_apply, pinS_apply, maskK_catB]
  have hs : ∀ z z' : Grid β 0 f, (serial X' 0 f (Nat.add_zero _) z = serial X' 0 f (Nat.add_zero _) z')
      ↔ z = z' := fun z z' => (serial X' 0 f (Nat.add_zero _)).injective.eq_iff
  have hp : ∀ z z' : Sky α f, ((S.peel 0 f (0, z)).1 = (S.peel 0 f (0, z')).1) ↔
      (S.sky f z).1 = (S.sky f z').1 := by
    intro z z'
    simp only [Split.peel, Equiv.coe_fn_mk, Prod.mk.injEq, true_and]
  have hf : ∀ z : Sky α f, (S.peel 0 f (0, z)).2 = flat k f (S.sky f z).2 := fun z => rfl
  rw [hf, hf]
  have ei : (serial X' 0 f (Nat.add_zero _) (S.peel 0 f (0, y)).1 =
      serial X' 0 f (Nat.add_zero _) (S.peel 0 f (0, y')).1) ↔ (S.sky f y).1 = (S.sky f y').1 :=
    (hs _ _).trans (hp _ _)
  by_cases hq : q = q'
  · subst hq
    by_cases hy : (S.sky f y).1 = (S.sky f y').1
    · have h1 := ei.2 hy
      simp only [h1, hy, and_self, if_true, mul_one]
    · have h1 : ¬ (serial X' 0 f (Nat.add_zero _) (S.peel 0 f (0, y)).1 =
          serial X' 0 f (Nat.add_zero _) (S.peel 0 f (0, y')).1) := fun hh => hy (ei.1 hh)
      simp only [h1, hy, and_false, if_false, mul_zero, zero_mul, mul_one]
  · simp only [hq, false_and, if_false, mul_zero]

/-- **A job answer is the block (or target) action on every instance.** -/
theorem hlow_placeS (S : Split α β (Fin k)) (X' : Layout β) (f r n : ℕ)
    (h : k*f + X'.n*f + r = n) (w : Bits n → ℂ) (q : Bits r) (y : Sky α f) :
    hlow n (k*f) w (placeS S X' f r n h (q, y)) =
      matAct f (S.lift (kernel (Fin k))) (fun y' => w (placeS S X' f r n h (q, y'))) y := by
  unfold hlow matAct
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (placeS S X' f r n h), Fintype.sum_prod_type]
  simp_rw [maskK_placeS]
  rw [Finset.sum_eq_single q]
  · apply Finset.sum_congr rfl
    intro y' _
    rw [Split.product]
    simp only [true_and]
  · intro q' _ hq'
    apply Finset.sum_eq_zero; intro y' _
    rw [if_neg (fun hh => hq' hh.1.symm), zero_mul]
  · intro hh; exact absurd (Finset.mem_univ _) hh

end

end
end PowerSaving.Binary
end OAI

#print axioms OAI.PowerSaving.Binary.maskHi_mul_maskK
#print axioms OAI.PowerSaving.Binary.hlow_placeS
#print axioms OAI.PowerSaving.Binary.placeS_loc

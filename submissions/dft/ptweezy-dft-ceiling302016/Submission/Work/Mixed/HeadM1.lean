import Submission.Work.GFrame.Engine.Letters
import Submission.Work.Block.Frames

/-!
# Mixed targets, step M1: the head lemma, the cut target and the block split (rb-r45m1)

New file (wht43 record track, 14 Oct 2026).  Imports only our block/GFrame engine.  No `sorry`, no axioms.

Words are `GWord α ρ` with semantics `gwalk` (Work/GFrame/Engine/Letters.lean).  A *mixed certificate*
`GLiveKernelM e T w` says: on every input that is zero on scratch, at every column count `f`, the word
`w` leaves `matAct f (T l)` of the input on the live role `e l` (`GLiveKernel` is the case `T = kernel`).

* `bph`, `blockMat_eq_wrap`, `unblock`, `blockMat_mul_unblock`   a block is `wrap` of a phase; its inverse.
* `split_block`, `blockMat_comm`         a block of rank `a + b` is the product of its two parts.
* `stdDir`, `kernel_eq_blockMat_std`     the kernel is the block of the unit vectors (any `Fintype α`).
* `cut_target`, `cut_target_of`          `kernel * unblock (A.fam S) = shift c * blockMat (A.fam Sᶜ)`:
                                          removing the block of the lines `S` of a frame leaves the block
                                          of the other lines and a free shift.
* `roleProd`, `gwalk_local`              words of one-role letters act role by role.
* `GLiveKernelM.peel`, `.peel'`          peeling a one-role prefix whose role matrices are invertible.
* `GLiveKernelM.of_heads`                **the head lemma**: if `heads ++ body` is a certificate and each
                                          head is a block on its own live role (one per role), then `body`
                                          realises `kernel * (head)⁻¹` on head roles and `kernel` elsewhere,
                                          at every column count.
* `GLiveKernelM.append_local`            a one-role suffix multiplies the target on the left.
* `cut_heads_full`, `cut_heads_half`     the two cuts of the record plan: targets are blocks
                                          (`blockMat (tgt l).2`, `tgt l : Σ r, Fin r → Space α`) after a
                                          trailing free shift on each head role; the half cut splits each
                                          head `a + b`, cuts the first `a` lines and keeps a rank-`b` remnant
                                          at the front of the body.
* `splitWord`, `gwalk_splitWord`, `hist_splitWord`
                                          splitting every block of rank `a + b` of a word into two blocks of
                                          ranks `a` and `b` keeps `gwalk` and moves the histogram.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.MX
open Binary GF Matrix Finset
noncomputable section

/-! ## 1. Matrices -/

section Mats
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The phase of a block family: `blockMat z = wrap (bph z)`. -/
def bph {r : ℕ} (z : Fin r → Space α) (x : Space α) : ℂ := ∏ i, tint (dot (z i) x)

lemma tint_ne_zero (i : F) : tint i ≠ 0 := by
  unfold tint
  split_ifs
  · exact one_ne_zero
  · exact Complex.I_ne_zero

lemma bph_ne_zero {r : ℕ} (z : Fin r → Space α) (x : Space α) : bph z x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => tint_ne_zero _)

lemma blockMat_eq_wrap {r : ℕ} (z : Fin r → Space α) : blockMat z = wrap (bph z) := by
  rw [blockMat_wrap]
  congr 1
  funext x
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

lemma blockMat_congr {r r' : ℕ} (z : Fin r → Space α) (z' : Fin r' → Space α)
    (h : ∀ x, bph z x = bph z' x) : blockMat z = blockMat z' := by
  rw [blockMat_eq_wrap, blockMat_eq_wrap]
  congr 1
  funext x
  exact h x

/-- Inverse of a block. -/
def unblock {r : ℕ} (z : Fin r → Space α) : CMat α := wrap fun x => (bph z x)⁻¹

lemma unblock_congr {r r' : ℕ} (z : Fin r → Space α) (z' : Fin r' → Space α)
    (h : ∀ x, bph z x = bph z' x) : unblock z = unblock z' := by
  unfold unblock
  congr 1
  funext x
  rw [h x]

lemma blockMat_mul_unblock {r : ℕ} (z : Fin r → Space α) : blockMat z * unblock z = 1 := by
  rw [blockMat_eq_wrap, unblock, wrap_mul, ← wrap_one]
  congr 1
  funext x
  exact mul_inv_cancel₀ (bph_ne_zero z x)

lemma unblock_mul_blockMat {r : ℕ} (z : Fin r → Space α) : unblock z * blockMat z = 1 := by
  rw [blockMat_eq_wrap, unblock, wrap_mul, ← wrap_one]
  congr 1
  funext x
  exact inv_mul_cancel₀ (bph_ne_zero z x)

lemma blockMat_comm {r r' : ℕ} (z : Fin r → Space α) (z' : Fin r' → Space α) :
    blockMat z * blockMat z' = blockMat z' * blockMat z := by
  rw [blockMat_eq_wrap, blockMat_eq_wrap]
  exact wrap_comm _ _

/-- The phase of a block of rank `a + b` is the product of the phases of its parts. -/
lemma bph_add {a b : ℕ} (z : Fin (a+b) → Space α) (x : Space α) :
    bph z x = bph (fun i : Fin a => z (Fin.castAdd b i)) x * bph (fun j : Fin b => z (Fin.natAdd a j)) x := by
  unfold bph
  exact Fin.prod_univ_add (fun i => tint (dot (z i) x))

/-- **A block of rank `a + b` is the product of the blocks of its first `a` and last `b` directions.** -/
theorem split_block {a b : ℕ} (z : Fin (a+b) → Space α) :
    blockMat z = blockMat (fun i : Fin a => z (Fin.castAdd b i))
      * blockMat (fun j : Fin b => z (Fin.natAdd a j)) := by
  rw [blockMat_eq_wrap, blockMat_eq_wrap, blockMat_eq_wrap, wrap_mul]
  congr 1
  funext x
  exact bph_add z x

lemma bph_cast {r r' : ℕ} (h : r' = r) (z : Fin r → Space α) (x : Space α) :
    bph (fun i : Fin r' => z (Fin.cast h i)) x = bph z x := by
  subst h
  rfl

/-- The parts of a linearly independent family of rank `a + b` are linearly independent. -/
lemma indep_castAdd {a b : ℕ} {z : Fin (a+b) → Space α} (h : LinearIndependent F z) :
    LinearIndependent F (fun i : Fin a => z (Fin.castAdd b i)) :=
  h.comp _ (Fin.castAdd_injective a b)

lemma indep_natAdd {a b : ℕ} {z : Fin (a+b) → Space α} (h : LinearIndependent F z) :
    LinearIndependent F (fun j : Fin b => z (Fin.natAdd a j)) :=
  h.comp _ (Fin.natAdd_injective b a)

/-- The unit vectors of `α`, enumerated. -/
def stdDir (α : Type*) [Fintype α] [DecidableEq α] : Fin (Fintype.card α) → Space α :=
  fun i => eu ((Fintype.equivFin α).symm i)

lemma stdDir_indep : LinearIndependent F (stdDir α) := by
  apply linearIndependent_of_orthonormal
  intro i j
  simp only [stdDir, dot_eu_left, eu]
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬ (Fintype.equivFin α).symm j = (Fintype.equivFin α).symm i :=
      fun h' => h ((Fintype.equivFin α).symm.injective h').symm
    rw [if_neg h', if_neg h]

/-- **The kernel is the block of the unit vectors** (any finite label type; cf. `kernel_eq_blockMat`). -/
theorem kernel_eq_blockMat_std : kernel α = blockMat (stdDir α) := by
  rw [blockMat_eq_wrap, ← wrap_lum]
  congr 1
  funext x
  unfold bph lum
  simp only [stdDir, dot_eu_left]
  exact (Equiv.prod_comp (Fintype.equivFin α).symm (fun a => tint (x a))).symm

lemma shift_mul_shift (c d : Space α) : Binary.shift c * Binary.shift d = Binary.shift (c + d) := by
  rw [shift_phase, shift_phase, shift_phase, wrap_mul]
  congr 1
  funext x
  rw [dot_add_left, sign_add]

lemma shift_mul_shift_self (c : Space α) (M : CMat α) :
    Binary.shift c * (Binary.shift c * M) = M := by
  rw [← Matrix.mul_assoc, shift_sq, Matrix.one_mul]

/-- The kernel is the product of the frame changes of the lines `S` and of the other lines. -/
lemma kernel_eq_deltas (A : OBase α) (S : Finset α) : kernel α = A.deltas S * A.deltas Sᶜ := by
  have h1 := A.frame_union Sᶜ S disjoint_compl_left
  have hu : Sᶜ ∪ S = Finset.univ := by ext i; by_cases h : i ∈ S <;> simp [h]
  rw [hu, frame_univ] at h1
  have h2 := A.frame_union ∅ Sᶜ (Finset.disjoint_empty_left _)
  rw [Finset.empty_union, frame_zero, Matrix.mul_one] at h2
  rw [h1, h2]

/-- **The cut target.**  Undoing the block of the lines `S` of the frame `A` from the kernel leaves the block
of the other lines `Sᶜ` and one free shift. -/
theorem cut_target (A : OBase α) (S : Finset α) :
    kernel α * unblock (A.fam S) = Binary.shift (A.corr S + A.corr Sᶜ) * blockMat (A.fam Sᶜ) := by
  rw [kernel_eq_deltas A S, A.deltas_eq, A.deltas_eq, ← shift_mul_shift]
  simp only [shift_phase, blockMat_eq_wrap, unblock, wrap_mul]
  congr 1
  funext x
  have h := bph_ne_zero (A.fam S) x
  field_simp

/-- The same for any block whose phase is that of the lines `S` of `A` (e.g. the lines in another order). -/
theorem cut_target_of {r : ℕ} (z : Fin r → Space α) (A : OBase α) (S : Finset α)
    (hz : ∀ x, bph z x = bph (A.fam S) x) :
    kernel α * unblock z = Binary.shift (A.corr S + A.corr Sᶜ) * blockMat (A.fam Sᶜ) := by
  rw [unblock_congr z (A.fam S) hz]
  exact cut_target A S

/-- The phase of the lines `S` of `A`, as a product over `S`. -/
lemma bph_fam (A : OBase α) (S : Finset α) (x : Space α) :
    bph (A.fam S) x = ∏ i ∈ S, tint (dot (A.v i) x) := by
  unfold bph OBase.fam
  rw [← Finset.prod_coe_sort S (fun i => tint (dot (A.v i) x))]
  exact Equiv.prod_comp S.equivFin.symm (fun j : {y // y ∈ S} => tint (dot (A.v j.1) x))

/-- A block whose directions are lines of `A`, chosen by an injective index map `g`, has the phase of the
lines `univ.map g` (so `cut_target_of` applies with `S = univ.map ⟨g, hg⟩`). -/
lemma bph_lines {r : ℕ} (A : OBase α) (g : Fin r → α) (hg : Function.Injective g) (x : Space α) :
    bph (fun i => A.v (g i)) x = bph (A.fam (Finset.univ.map ⟨g, hg⟩)) x := by
  rw [bph_fam, Finset.prod_map]
  rfl

end Mats

/-! ## 2. Words acting role by role -/

section Words
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **Mixed certificate**: on every input that is zero on scratch, the word leaves `T l` of the input on the
live role `e l`, at every column count. -/
def GLiveKernelM (e : σ → ρ) (T : σ → CMat α) (w : GWord α ρ) : Prop :=
  ∀ (f : ℕ) (v : Data α ρ f), (∀ s, (∀ l, e l ≠ s) → v s = 0) →
    ∀ l, gwalk f w v (e l) = matAct f (T l) (v (e l))

theorem GLiveKernelM.of_kernel {e : σ → ρ} {w : GWord α ρ} (h : GLiveKernel e w) :
    GLiveKernelM e (fun _ => kernel α) w := h

theorem GLiveKernelM.to_kernel {e : σ → ρ} {w : GWord α ρ}
    (h : GLiveKernelM e (fun _ => kernel α) w) : GLiveKernel e w := h

theorem GLiveKernelM.congr {e : σ → ρ} {T T' : σ → CMat α} {w : GWord α ρ}
    (h : GLiveKernelM e T w) (hT : ∀ l, T l = T' l) : GLiveKernelM e T' w := by
  intro f v hv l
  rw [h f v hv l, hT l]

/-- Two words with the same semantics have the same certificates. -/
theorem GLiveKernelM.of_gwalk {e : σ → ρ} {T : σ → CMat α} {w w' : GWord α ρ}
    (h : GLiveKernelM e T w) (hw : ∀ f (x : Data α ρ f), gwalk f w x = gwalk f w' x) :
    GLiveKernelM e T w' := by
  intro f v hv l
  rw [← hw f v]
  exact h f v hv l

/-- The matrix by which a letter acts on role `j` (`1` if it does not act there; `1` for `localM`). -/
def rmat : GMove α ρ → ρ → CMat α
  | .old (.localM _), _ => 1
  | .old (.shift l z), j => if j = l then Binary.shift z else 1
  | .old (.block l _ z _), j => if j = l then blockMat z else 1
  | .perm l G, j => if j = l then permMat G else 1
  | .phase l z c, j => if j = l then phaseMat z c else 1

/-- A letter that acts on one role (every letter except `localM`). -/
def IsLocal : GMove α ρ → Prop
  | .old (.localM _) => False
  | _ => True

/-- A word of one-role letters. -/
def RoleLocal (w : GWord α ρ) : Prop := ∀ mv ∈ w, IsLocal mv

lemma RoleLocal.append {w w' : GWord α ρ} (h : RoleLocal w) (h' : RoleLocal w') :
    RoleLocal (w ++ w') := by
  intro mv hmv
  rcases List.mem_append.mp hmv with h1|h1
  · exact h mv h1
  · exact h' mv h1

/-- Product of the role matrices of a word on role `j` (later letters on the left). -/
def roleProd : GWord α ρ → ρ → CMat α
  | [], _ => 1
  | mv :: w, j => roleProd w j * rmat mv j

@[simp] lemma roleProd_nil (j : ρ) : roleProd ([] : GWord α ρ) j = 1 := rfl
lemma roleProd_cons (mv : GMove α ρ) (w : GWord α ρ) (j : ρ) :
    roleProd (mv :: w) j = roleProd w j * rmat mv j := rfl

lemma roleProd_append (w w' : GWord α ρ) (j : ρ) :
    roleProd (w ++ w') j = roleProd w' j * roleProd w j := by
  induction w with
  | nil => simp
  | cons mv w ih => rw [List.cons_append, roleProd_cons, roleProd_cons, ih, Matrix.mul_assoc]

lemma matAct_zero (f : ℕ) (M : CMat α) : matAct f M (0 : Sky α f → ℂ) = 0 := by
  unfold matAct
  exact Matrix.mulVec_zero _

lemma act_local (f : ℕ) (mv : GMove α ρ) (h : IsLocal mv) (x : Data α ρ f) (j : ρ) :
    mv.act f x j = matAct f (rmat mv j) (x j) := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => exact h.elim
    | shift l z =>
      change roleAct f l (Binary.shift z) x j = _
      simp only [roleAct, rmat]
      split_ifs <;> simp
    | block l rk z ind =>
      change roleAct f l (blockMat z) x j = _
      simp only [roleAct, rmat]
      split_ifs <;> simp
  | perm l G =>
    change roleAct f l (permMat G) x j = _
    simp only [roleAct, rmat]
    split_ifs <;> simp
  | phase l z c =>
    change roleAct f l (phaseMat z c) x j = _
    simp only [roleAct, rmat]
    split_ifs <;> simp

/-- **A word of one-role letters acts role by role.** -/
theorem gwalk_local (f : ℕ) (w : GWord α ρ) (hw : RoleLocal w) (x : Data α ρ f) (j : ρ) :
    gwalk f w x j = matAct f (roleProd w j) (x j) := by
  induction w generalizing x with
  | nil => simp
  | cons mv w ih =>
    rw [gwalk_cons, ih (fun m hm => hw m (List.mem_cons_of_mem _ hm)),
      act_local f mv (hw mv List.mem_cons_self), matAct_mul, roleProd_cons]

/-- Two one-role words with the same role products have the same semantics. -/
theorem gwalk_eq_of_roleProd (w w' : GWord α ρ) (hw : RoleLocal w) (hw' : RoleLocal w')
    (h : ∀ j, roleProd w j = roleProd w' j) (f : ℕ) (x : Data α ρ f) :
    gwalk f w x = gwalk f w' x := by
  funext j
  rw [gwalk_local f w hw, gwalk_local f w' hw', h j]

/-- **Peeling a one-role prefix.**  If `h ++ body` is a mixed certificate and the role products of `h`
have right inverses `V j` (on every role), then `body` realises `T l * V (e l)`. -/
theorem GLiveKernelM.peel {e : σ → ρ} {T : σ → CMat α} (h body : GWord α ρ) (hl : RoleLocal h)
    (V : ρ → CMat α) (hV : ∀ j, roleProd h j * V j = 1)
    (hk : GLiveKernelM e T (h ++ body)) :
    GLiveKernelM e (fun l => T l * V (e l)) body := by
  intro f y hy l
  set v : Data α ρ f := fun j => matAct f (V j) (y j) with hvdef
  have hv0 : ∀ s, (∀ l, e l ≠ s) → v s = 0 := by
    intro s hs
    simp only [hvdef]
    rw [hy s hs]
    exact matAct_zero f _
  have hgv : gwalk f h v = y := by
    funext j
    rw [gwalk_local f h hl v j]
    simp only [hvdef]
    rw [matAct_mul, hV j, matAct_one]
  have hb := hk f v hv0 l
  rw [gwalk_append, hgv] at hb
  rw [hb]
  simp only [hvdef]
  rw [matAct_mul]

open Classical in
/-- Right inverses given on live roles only (scratch roles must be untouched). -/
theorem GLiveKernelM.peel' {e : σ → ρ} (he : Function.Injective e) {T : σ → CMat α}
    (h body : GWord α ρ) (hl : RoleLocal h) (U : σ → CMat α)
    (hU : ∀ l, roleProd h (e l) * U l = 1) (hs : ∀ s, (∀ l, e l ≠ s) → roleProd h s = 1)
    (hk : GLiveKernelM e T (h ++ body)) :
    GLiveKernelM e (fun l => T l * U l) body := by
  let V : ρ → CMat α := fun j => if hj : ∃ l, e l = j then U hj.choose else 1
  have hVe : ∀ l, V (e l) = U l := by
    intro l
    have hj : ∃ l', e l' = e l := ⟨l, rfl⟩
    have hc : hj.choose = l := he hj.choose_spec
    simp only [V, dif_pos hj, hc]
  have hV : ∀ j, roleProd h j * V j = 1 := by
    intro j
    by_cases hj : ∃ l, e l = j
    · obtain ⟨l, rfl⟩ := hj
      rw [hVe l, hU l]
    · have hs' : ∀ l, e l ≠ j := fun l h' => hj ⟨l, h'⟩
      simp only [V, dif_neg hj, hs j hs', Matrix.mul_one]
  have := GLiveKernelM.peel h body hl V hV hk
  exact this.congr (fun l => by rw [hVe l])

/-- **A one-role suffix multiplies the target on the left.** -/
theorem GLiveKernelM.append_local {e : σ → ρ} {T : σ → CMat α} {w : GWord α ρ}
    (h : GLiveKernelM e T w) (t : GWord α ρ) (ht : RoleLocal t) :
    GLiveKernelM e (fun l => roleProd t (e l) * T l) (w ++ t) := by
  intro f v hv l
  rw [gwalk_append, gwalk_local f t ht, h f v hv l, matAct_mul]

/-! ### one letter per role -/

/-- A family of one-role letters, letter `mk l` acting on role `e l` by the matrix `M l`. -/
def OnRole (e : σ → ρ) (mk : σ → GMove α ρ) (M : σ → CMat α) : Prop :=
  ∀ l, IsLocal (mk l) ∧ ∀ j, rmat (mk l) j = if j = e l then M l else 1

lemma roleLocal_map {e : σ → ρ} {mk : σ → GMove α ρ} {M : σ → CMat α} (hm : OnRole e mk M)
    (L : List σ) : RoleLocal (L.map mk) := by
  intro mv hmv
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hmv
  exact (hm l).1

lemma roleProd_map_e [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e) {mk : σ → GMove α ρ} {M : σ → CMat α}
    (hm : OnRole e mk M) (L : List σ) (hL : L.Nodup) (l : σ) :
    roleProd (L.map mk) (e l) = if l ∈ L then M l else 1 := by
  induction L with
  | nil => simp
  | cons l0 L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, roleProd_cons, ih hL.2, (hm l0).2 (e l)]
    by_cases h : l = l0
    · subst h
      simp [hL.1]
    · have h' : e l ≠ e l0 := fun h'' => h (he h'')
      simp [h, h']

lemma roleProd_map_off {e : σ → ρ} {mk : σ → GMove α ρ} {M : σ → CMat α}
    (hm : OnRole e mk M) (L : List σ) (s : ρ) (hs : ∀ l, e l ≠ s) :
    roleProd (L.map mk) s = 1 := by
  induction L with
  | nil => simp
  | cons l0 L ih =>
    rw [List.map_cons, roleProd_cons, ih, (hm l0).2 s, if_neg (fun h => hs l0 h.symm), Matrix.mul_one]

/-! ### heads -/

/-- The head word: on each role `l ∈ L` one block of rank `rk l` with directions `z l`, on role `e l`. -/
def headLetter (e : σ → ρ) (rk : σ → ℕ) (z : ∀ l, Fin (rk l) → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) (l : σ) : GMove α ρ :=
  GMove.old (BMove.block (e l) (rk l) (z l) (ind l))

def headWord (e : σ → ρ) (L : List σ) (rk : σ → ℕ) (z : ∀ l, Fin (rk l) → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) : GWord α ρ :=
  L.map (headLetter e rk z ind)

lemma onRole_head (e : σ → ρ) (rk : σ → ℕ) (z : ∀ l, Fin (rk l) → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) :
    OnRole e (headLetter e rk z ind) (fun l => blockMat (z l)) :=
  fun l => ⟨trivial, fun j => rfl⟩

/-- **The head lemma.**  Let `heads ++ body` be a mixed certificate with target `T`, where the heads are one
block per role of the duplicate-free list `L` of live roles.  Then `body` alone realises
`T l * (head l)⁻¹` on the head roles and `T l` on every other live role, at every column count. -/
theorem GLiveKernelM.of_heads [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e) {T : σ → CMat α}
    (L : List σ) (hL : L.Nodup) (rk : σ → ℕ) (z : ∀ l, Fin (rk l) → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) (body : GWord α ρ)
    (hk : GLiveKernelM e T (headWord e L rk z ind ++ body)) :
    GLiveKernelM e (fun l => if l ∈ L then T l * unblock (z l) else T l) body := by
  have hm := onRole_head e rk z ind
  have := GLiveKernelM.peel' he (headWord e L rk z ind) body (roleLocal_map hm L)
    (fun l => if l ∈ L then unblock (z l) else 1)
    (fun l => by
      rw [headWord, roleProd_map_e he hm L hL l]
      split_ifs
      · exact blockMat_mul_unblock (z l)
      · exact Matrix.mul_one 1)
    (fun s hs => by rw [headWord, roleProd_map_off hm L s hs]) hk
  exact this.congr (fun l => by split_ifs <;> simp)

/-- The head lemma from an ordinary certificate (`GLiveKernel`). -/
theorem GLiveKernel.of_heads [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e)
    (L : List σ) (hL : L.Nodup) (rk : σ → ℕ) (z : ∀ l, Fin (rk l) → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) (body : GWord α ρ)
    (hk : GLiveKernel e (headWord e L rk z ind ++ body)) :
    GLiveKernelM e (fun l => if l ∈ L then kernel α * unblock (z l) else kernel α) body :=
  GLiveKernelM.of_heads he L hL rk z ind body (GLiveKernelM.of_kernel hk)

/-! ### trailing free shifts -/

def shiftLetter (e : σ → ρ) (c : σ → Space α) (l : σ) : GMove α ρ :=
  GMove.old (BMove.shift (e l) (c l))

def shiftWord (e : σ → ρ) (L : List σ) (c : σ → Space α) : GWord α ρ := L.map (shiftLetter e c)

lemma onRole_shift (e : σ → ρ) (c : σ → Space α) :
    OnRole e (shiftLetter e c) (fun l => Binary.shift (c l)) :=
  fun l => ⟨trivial, fun j => rfl⟩

/-! ### the two cuts -/

/-- Target of a cut role: the block of the lines `Sᶜ` of `A l`; of a full role: the unit vectors. -/
def cutTgt [DecidableEq σ] (L : List σ) (A : σ → OBase α) (S : σ → Finset α) (l : σ) : Σ r : ℕ, (Fin r → Space α) :=
  if l ∈ L then ⟨(S l)ᶜ.card, (A l).fam (S l)ᶜ⟩ else ⟨Fintype.card α, stdDir α⟩

lemma cutTgt_mem [DecidableEq σ] (L : List σ) (A : σ → OBase α) (S : σ → Finset α) {l : σ} (hl : l ∈ L) :
    cutTgt L A S l = ⟨(S l)ᶜ.card, (A l).fam (S l)ᶜ⟩ := if_pos hl

lemma cutTgt_nmem [DecidableEq σ] (L : List σ) (A : σ → OBase α) (S : σ → Finset α) {l : σ} (hl : l ∉ L) :
    cutTgt L A S l = ⟨Fintype.card α, stdDir α⟩ := if_neg hl

lemma cutTgt_indep [DecidableEq σ] (L : List σ) (A : σ → OBase α) (S : σ → Finset α) (l : σ) :
    LinearIndependent F (cutTgt L A S l).2 := by
  by_cases hl : l ∈ L
  · rw [cutTgt_mem L A S hl]
    exact (A l).fam_indep _
  · rw [cutTgt_nmem L A S hl]
    exact stdDir_indep

/-- The free shift appended on a cut role. -/
def cutShift (A : σ → OBase α) (S : σ → Finset α) (l : σ) : Space α :=
  (A l).corr (S l) + (A l).corr (S l)ᶜ

/-- From "kernel times the inverse head" to the block target, with one trailing shift per head role. -/
theorem GLiveKernelM.cut_finish [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e) (L : List σ) (hL : L.Nodup)
    (A : σ → OBase α) (S : σ → Finset α) (U : σ → CMat α) (body : GWord α ρ)
    (hU : ∀ l ∈ L, kernel α * U l = Binary.shift (cutShift A S l) * blockMat ((A l).fam (S l)ᶜ))
    (hk : GLiveKernelM e (fun l => if l ∈ L then kernel α * U l else kernel α) body) :
    GLiveKernelM e (fun l => blockMat (cutTgt L A S l).2) (body ++ shiftWord e L (cutShift A S)) := by
  have hm := onRole_shift e (cutShift A S)
  have := hk.append_local (shiftWord e L (cutShift A S)) (roleLocal_map hm L)
  refine this.congr (fun l => ?_)
  rw [shiftWord, roleProd_map_e he hm L hL l]
  by_cases hl : l ∈ L
  · rw [cutTgt_mem L A S hl, if_pos hl, if_pos hl, hU l hl, shift_mul_shift_self]
  · rw [cutTgt_nmem L A S hl, if_neg hl, if_neg hl, Matrix.one_mul]
    exact kernel_eq_blockMat_std

/-- **Full cut.**  Every head (role `l ∈ L`) is the block of the lines `S l` of an orthonormal frame `A l`
(in any order: only its phase is used).  Then `body`, followed by one free shift per head role, realises
the block of the remaining lines `(S l)ᶜ` on head roles and the kernel (block of the unit vectors)
elsewhere, at every column count. -/
theorem cut_heads_full [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e)
    (L : List σ) (hL : L.Nodup) (rk : σ → ℕ) (z : ∀ l, Fin (rk l) → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz : ∀ l ∈ L, ∀ x, bph (z l) x = bph ((A l).fam (S l)) x) (body : GWord α ρ)
    (hk : GLiveKernel e (headWord e L rk z ind ++ body)) :
    GLiveKernelM e (fun l => blockMat (cutTgt L A S l).2) (body ++ shiftWord e L (cutShift A S)) :=
  GLiveKernelM.cut_finish he L hL A S (fun l => unblock (z l)) body
    (fun l hl => cut_target_of (z l) (A l) (S l) (hz l hl))
    (GLiveKernel.of_heads he L hL rk z ind body hk)

/-- First `a` and last `b` directions of a head of rank `a + b`. -/
def partA {a b : ℕ} (z : σ → Fin (a+b) → Space α) (l : σ) : Fin a → Space α :=
  fun i => z l (Fin.castAdd b i)
def partB {a b : ℕ} (z : σ → Fin (a+b) → Space α) (l : σ) : Fin b → Space α :=
  fun j => z l (Fin.natAdd a j)

lemma partA_indep {a b : ℕ} {z : σ → Fin (a+b) → Space α} (ind : ∀ l, LinearIndependent F (z l)) (l : σ) :
    LinearIndependent F (partA z l) := indep_castAdd (ind l)

lemma partB_indep {a b : ℕ} {z : σ → Fin (a+b) → Space α} (ind : ∀ l, LinearIndependent F (z l)) (l : σ) :
    LinearIndependent F (partB z l) := indep_natAdd (ind l)

lemma roleProd_headWord_e [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e) (L : List σ) (hL : L.Nodup)
    (rk : σ → ℕ) (z : ∀ l, Fin (rk l) → Space α) (ind : ∀ l, LinearIndependent F (z l)) (l : σ) :
    roleProd (headWord e L rk z ind) (e l) = if l ∈ L then blockMat (z l) else 1 :=
  roleProd_map_e he (onRole_head e rk z ind) L hL l

lemma roleProd_headWord_off {e : σ → ρ} (L : List σ)
    (rk : σ → ℕ) (z : ∀ l, Fin (rk l) → Space α) (ind : ∀ l, LinearIndependent F (z l)) (s : ρ)
    (hs : ∀ l, e l ≠ s) : roleProd (headWord e L rk z ind) s = 1 :=
  roleProd_map_off (onRole_head e rk z ind) L s hs

lemma roleLocal_headWord (e : σ → ρ) (L : List σ)
    (rk : σ → ℕ) (z : ∀ l, Fin (rk l) → Space α) (ind : ∀ l, LinearIndependent F (z l)) :
    RoleLocal (headWord e L rk z ind) :=
  roleLocal_map (onRole_head e rk z ind) L

/-- Splitting every head `a + b` into its two parts, all first parts before all second parts, does not change
the semantics (one head per role). -/
theorem gwalk_heads_split [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e) (L : List σ) (hL : L.Nodup)
    {a b : ℕ} (z : σ → Fin (a+b) → Space α) (ind : ∀ l, LinearIndependent F (z l))
    (f : ℕ) (x : Data α ρ f) :
    gwalk f (headWord e L (fun _ => a+b) z ind) x
      = gwalk f (headWord e L (fun _ => a) (partA z) (partA_indep ind)
          ++ headWord e L (fun _ => b) (partB z) (partB_indep ind)) x := by
  apply gwalk_eq_of_roleProd _ _ (roleLocal_headWord e L _ z ind)
    ((roleLocal_headWord e L _ _ (partA_indep ind)).append (roleLocal_headWord e L _ _ (partB_indep ind)))
  intro j
  rw [roleProd_append]
  by_cases hj : ∃ l, e l = j
  · obtain ⟨l, rfl⟩ := hj
    rw [roleProd_headWord_e he L hL _ z ind l, roleProd_headWord_e he L hL _ _ (partA_indep ind) l,
      roleProd_headWord_e he L hL _ _ (partB_indep ind) l]
    by_cases hl : l ∈ L
    · rw [if_pos hl, if_pos hl, if_pos hl, split_block (z l), blockMat_comm]
      rfl
    · rw [if_neg hl, if_neg hl, if_neg hl, Matrix.mul_one]
  · have hs : ∀ l, e l ≠ j := fun l h' => hj ⟨l, h'⟩
    rw [roleProd_headWord_off L _ z ind j hs, roleProd_headWord_off L _ _ (partA_indep ind) j hs,
      roleProd_headWord_off L _ _ (partB_indep ind) j hs, Matrix.mul_one]

/-- **Half cut.**  Every head has rank `a + b`; its first `a` directions are the lines `S l` of an orthonormal
frame `A l`.  Then the body, preceded by the rank-`b` remnants of the heads and followed by one free shift
per head role, realises the block of the lines `(S l)ᶜ` (rank `card α - a` when `|S l| = a`) on head roles and
the kernel elsewhere, at every column count. -/
theorem cut_heads_half [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e)
    (L : List σ) (hL : L.Nodup) {a b : ℕ} (z : σ → Fin (a+b) → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz : ∀ l ∈ L, ∀ x, bph (partA z l) x = bph ((A l).fam (S l)) x) (body : GWord α ρ)
    (hk : GLiveKernel e (headWord e L (fun _ => a+b) z ind ++ body)) :
    GLiveKernelM e (fun l => blockMat (cutTgt L A S l).2)
      ((headWord e L (fun _ => b) (partB z) (partB_indep ind) ++ body)
        ++ shiftWord e L (cutShift A S)) := by
  have hk' : GLiveKernelM e (fun _ => kernel α)
      (headWord e L (fun _ => a) (partA z) (partA_indep ind)
        ++ (headWord e L (fun _ => b) (partB z) (partB_indep ind) ++ body)) := by
    refine (GLiveKernelM.of_kernel hk).of_gwalk (fun f x => ?_)
    rw [← List.append_assoc, gwalk_append, gwalk_append, gwalk_heads_split he L hL z ind f x]
  exact GLiveKernelM.cut_finish he L hL A S (fun l => unblock (partA z l)) _
    (fun l hl => cut_target_of (partA z l) (A l) (S l) (hz l hl))
    (GLiveKernelM.of_heads he L hL (fun _ => a) (partA z) _ _ hk')

/-! ### histograms and properness of the new words -/

lemma hist_headWord (e : σ → ρ) (L : List σ) (c : ℕ) (z : σ → Fin c → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) (r : ℕ) :
    GWord.hist (headWord e L (fun _ => c) z ind) r = if r = c then L.length else 0 := by
  induction L with
  | nil => simp [GWord.hist, headWord, GWord.shadow]
  | cons l0 L ih =>
    simp only [GWord.hist, headWord, GWord.shadow, List.map_cons] at ih ⊢
    rw [BWord.hist_cons, ih]
    simp only [headLetter, GMove.shadow, BMove.rk?, Option.some.injEq, List.length_cons]
    by_cases h : r = c
    · subst h; simp
    · simp [h, Ne.symm h]

lemma hist_shiftWord (e : σ → ρ) (L : List σ) (c : σ → Space α) (r : ℕ) :
    GWord.hist (shiftWord e L c) r = 0 := by
  induction L with
  | nil => simp [GWord.hist, shiftWord, GWord.shadow]
  | cons l0 L ih =>
    simp only [GWord.hist, shiftWord, GWord.shadow, List.map_cons] at ih ⊢
    rw [BWord.hist_cons, ih]
    simp [shiftLetter, GMove.shadow, BMove.rk?]

lemma hist_append (w w' : GWord α ρ) (r : ℕ) :
    GWord.hist (w ++ w') r = GWord.hist w r + GWord.hist w' r := by
  simp only [GWord.hist, GWord.shadow, List.map_append]
  exact BWord.hist_append _ _ r

lemma proper_headWord (u : ℕ) (e : σ → ρ) (L : List σ) (c : ℕ) (z : σ → Fin c → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) (h1 : 1 ≤ c) (h2 : c < u) :
    GWord.Proper u (headWord e L (fun _ => c) z ind) := by
  intro mv hmv
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hmv
  exact ⟨h1, h2⟩

lemma proper_shiftWord (u : ℕ) (e : σ → ρ) (L : List σ) (c : σ → Space α) :
    GWord.Proper u (shiftWord e L c) := by
  intro mv hmv
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hmv
  trivial

/-! ## 3. Splitting every block of rank `a + b` of a word -/

/-- One letter, split if it is a block of rank `a + b`. -/
def splitMove (a b : ℕ) : GMove α ρ → GWord α ρ
  | .old (.block l rk z ind) =>
    if h : rk = a + b then
      [GMove.old (BMove.block l a (fun i => z (Fin.cast h.symm (Fin.castAdd b i)))
          (ind.comp _ ((Fin.cast_injective h.symm).comp (Fin.castAdd_injective a b)))),
       GMove.old (BMove.block l b (fun j => z (Fin.cast h.symm (Fin.natAdd a j)))
          (ind.comp _ ((Fin.cast_injective h.symm).comp (Fin.natAdd_injective b a))))]
    else [GMove.old (BMove.block l rk z ind)]
  | mv => [mv]

/-- Split every block of rank `a + b`. -/
def splitWord (a b : ℕ) (w : GWord α ρ) : GWord α ρ := w.flatMap (splitMove a b)

lemma gwalk_splitMove (a b : ℕ) (f : ℕ) (mv : GMove α ρ) (x : Data α ρ f) :
    gwalk f (splitMove a b mv) x = mv.act f x := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => rfl
    | shift l z => rfl
    | block l rk z ind =>
      simp only [splitMove]
      split_ifs with h
      · change roleAct f l (blockMat _) (roleAct f l (blockMat _) x) = roleAct f l (blockMat z) x
        rw [roleAct_mul]
        congr 1
        rw [blockMat_comm, blockMat_eq_wrap, blockMat_eq_wrap, blockMat_eq_wrap, wrap_mul]
        congr 1
        funext y
        rw [← bph_cast h.symm z y, bph_add]
      · rfl
  | perm l G => rfl
  | phase l z c => rfl

theorem gwalk_splitWord (a b : ℕ) (f : ℕ) (w : GWord α ρ) (x : Data α ρ f) :
    gwalk f (splitWord a b w) x = gwalk f w x := by
  induction w generalizing x with
  | nil => rfl
  | cons mv w ih =>
    rw [splitWord, List.flatMap_cons, gwalk_append, gwalk_splitMove, gwalk_cons, ← ih]
    rfl

/-- Splitting keeps every mixed certificate. -/
theorem GLiveKernelM.splitWord {e : σ → ρ} {T : σ → CMat α} {w : GWord α ρ} (a b : ℕ)
    (h : GLiveKernelM e T w) : GLiveKernelM e T (splitWord a b w) :=
  h.of_gwalk (fun f x => (gwalk_splitWord a b f w x).symm)

lemma ghist_single (mv : GMove α ρ) (r : ℕ) :
    GWord.hist [mv] r = if mv.shadow.rk? = some r then 1 else 0 := by
  simp [GWord.hist, GWord.shadow, BWord.hist_cons]

lemma ghist_pair (mv mv' : GMove α ρ) (r : ℕ) :
    GWord.hist [mv, mv'] r = GWord.hist [mv] r + GWord.hist [mv'] r := by
  rw [show [mv, mv'] = [mv] ++ [mv'] from rfl, hist_append]

lemma hist_splitMove (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (mv : GMove α ρ) (r : ℕ) :
    GWord.hist (splitMove a b mv) r
      = (if r = a + b then 0 else GWord.hist [mv] r)
        + (if r = a then GWord.hist [mv] (a+b) else 0) + (if r = b then GWord.hist [mv] (a+b) else 0) := by
  cases mv with
  | old mv =>
    cases mv with
    | localM g => simp [splitMove, ghist_single, GMove.shadow, BMove.rk?]
    | shift l z => simp [splitMove, ghist_single, GMove.shadow, BMove.rk?]
    | block l rk z ind =>
      by_cases h : rk = a + b
      · simp only [splitMove]
        rw [dif_pos h, ghist_pair]
        simp only [ghist_single, GMove.shadow, BMove.rk?, Option.some.injEq]
        subst h
        split_ifs <;> omega
      · simp only [splitMove]
        rw [dif_neg h]
        simp only [ghist_single, GMove.shadow, BMove.rk?, Option.some.injEq]
        split_ifs <;> omega
  | perm l G => simp [splitMove, ghist_single, GMove.shadow, BMove.rk?]
  | phase l z c => simp [splitMove, ghist_single, GMove.shadow, BMove.rk?]

lemma hist_cons' (mv : GMove α ρ) (w : GWord α ρ) (r : ℕ) :
    GWord.hist (mv :: w) r = GWord.hist [mv] r + GWord.hist w r := by
  rw [show mv :: w = [mv] ++ w from rfl, hist_append]

/-- **Histogram after the split**: blocks of rank `a + b` disappear, each adds one block of rank `a` and one
of rank `b` (`1 ≤ a`, `1 ≤ b`). -/
theorem hist_splitWord (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (w : GWord α ρ) (r : ℕ) :
    GWord.hist (splitWord a b w) r
      = (if r = a + b then 0 else GWord.hist w r)
        + (if r = a then GWord.hist w (a+b) else 0) + (if r = b then GWord.hist w (a+b) else 0) := by
  induction w with
  | nil => simp [splitWord, GWord.hist, GWord.shadow]
  | cons mv w ih =>
    rw [splitWord, List.flatMap_cons, hist_append, hist_splitMove a b ha hb, ← splitWord, ih,
      hist_cons' mv w r, hist_cons' mv w (a+b)]
    split_ifs <;> omega

lemma proper_splitWord (u a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hau : a < u) (hbu : b < u)
    (w : GWord α ρ) (hw : GWord.Proper u w) : GWord.Proper u (splitWord a b w) := by
  intro mv hmv
  obtain ⟨mv0, hmv0, hmv⟩ := List.mem_flatMap.mp hmv
  have hp := hw mv0 hmv0
  cases mv0 with
  | old m =>
    cases m with
    | localM g => simp [splitMove] at hmv; subst hmv; exact hp
    | shift l z => simp [splitMove] at hmv; subst hmv; exact hp
    | block l rk z ind =>
      simp only [splitMove] at hmv
      split_ifs at hmv with h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
        rcases hmv with rfl | rfl
        · exact ⟨ha, hau⟩
        · exact ⟨hb, hbu⟩
      · simp only [List.mem_singleton] at hmv
        subst hmv; exact hp
  | perm l G => simp [splitMove] at hmv; subst hmv; trivial
  | phase l z c => simp [splitMove] at hmv; subst hmv; trivial

/-! ## 4. Data for the mixed engine: target ranks, unit-vector heads, the histogram of the cut word -/

/-- Target rank of a role: `card α - |S l|` on a cut role, `card α` elsewhere. -/
lemma cutTgt_rank [DecidableEq σ] (L : List σ) (A : σ → OBase α) (S : σ → Finset α) (l : σ) :
    (cutTgt L A S l).1 = if l ∈ L then Fintype.card α - (S l).card else Fintype.card α := by
  by_cases hl : l ∈ L
  · rw [cutTgt_mem L A S hl, if_pos hl]
    exact Finset.card_compl (S l)
  · rw [cutTgt_nmem L A S hl, if_neg hl]

/-- Heads whose cut directions are unit vectors `eu (g i)` (`g` injective) are lines of the canonical frame. -/
lemma bph_unit_lines {r : ℕ} (g : Fin r → α) (hg : Function.Injective g) (x : Space α) :
    bph (fun i => eu (g i)) x = bph ((OBase.canonical α).fam (Finset.univ.map ⟨g, hg⟩)) x :=
  bph_lines (OBase.canonical α) g hg x

/-- **Heads of any rank function `rk` with `rk l = c`** (e.g. `rk l = d.card` for a line set `d` of a frame) are, as a
word, the heads of the constant rank `c` with the directions re-indexed by `Fin.cast`: the certificate transfers. -/
theorem GLiveKernel.heads_recast [DecidableEq σ] {e : σ → ρ} (he : Function.Injective e) (L : List σ) (hL : L.Nodup)
    {rk : σ → ℕ} (z : ∀ l, Fin (rk l) → Space α) (ind : ∀ l, LinearIndependent F (z l)) {c : ℕ}
    (h : ∀ l, rk l = c) (body : GWord α ρ) (hk : GLiveKernel e (headWord e L rk z ind ++ body)) :
    GLiveKernel e (headWord e L (fun _ => c) (fun l i => z l (Fin.cast (h l).symm i))
      (fun l => (ind l).comp _ (Fin.cast_injective _)) ++ body) := by
  refine GLiveKernelM.to_kernel ((GLiveKernelM.of_kernel hk).of_gwalk (fun f x => ?_))
  rw [gwalk_append, gwalk_append]
  congr 1
  apply gwalk_eq_of_roleProd _ _ (roleLocal_headWord e L _ z ind) (roleLocal_headWord e L _ _ _)
  intro j
  by_cases hj : ∃ l, e l = j
  · obtain ⟨l, rfl⟩ := hj
    rw [roleProd_headWord_e he L hL _ z ind l, roleProd_headWord_e he L hL _ _ _ l]
    by_cases hl : l ∈ L
    · rw [if_pos hl, if_pos hl]
      exact blockMat_congr _ _ (fun x => (bph_cast (h l).symm (z l) x).symm)
    · rw [if_neg hl, if_neg hl]
  · have hs : ∀ l, e l ≠ j := fun l h' => hj ⟨l, h'⟩
    rw [roleProd_headWord_off L _ z ind j hs, roleProd_headWord_off L _ _ _ j hs]

/-- A head whose directions are the lines `d` of a frame `A` (`|d| = a + b`, in `A.fam` order): its first `a`
directions have the phase of `a` lines of `A` (the hypothesis `hz` of `cut_heads_half`, with `S = univ.map g`). -/
lemma bph_partA_fam (A : OBase α) (d : Finset α) {a b : ℕ} (h : d.card = a + b) (x : Space α) :
    bph (fun i : Fin a => A.fam d (Fin.cast h.symm (Fin.castAdd b i))) x
      = bph (A.fam (Finset.univ.map ⟨fun i : Fin a => (d.equivFin.symm (Fin.cast h.symm (Fin.castAdd b i))).1,
          fun i j hij => Fin.castAdd_injective a b (Fin.cast_injective _
            (d.equivFin.symm.injective (Subtype.ext hij)))⟩)) x :=
  bph_lines A _ _ x

/-- The line set of an injective index map has the map's size (so `cutTgt_rank` gives `card α - r`). -/
lemma card_lines {r : ℕ} (g : Fin r → α) (hg : Function.Injective g) :
    (Finset.univ.map ⟨g, hg⟩).card = r := by
  simp

/-- Histogram of the half-cut word `(remnants ++ body) ++ shifts`: the body's plus `|L|` blocks of rank `b`. -/
lemma hist_cut_half [DecidableEq σ] (e : σ → ρ) (L : List σ) {a b : ℕ} (z : σ → Fin (a+b) → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) (c : σ → Space α) (body : GWord α ρ) (r : ℕ) :
    GWord.hist ((headWord e L (fun _ => b) (partB z) (partB_indep ind) ++ body) ++ shiftWord e L c) r
      = (if r = b then L.length else 0) + GWord.hist body r := by
  rw [hist_append, hist_append, hist_headWord, hist_shiftWord, add_zero]

/-- Properness of the half-cut word (every paid rank in `[1, u)`), from that of the body and `1 ≤ b < u`. -/
lemma proper_cut_half (u : ℕ) (e : σ → ρ) (L : List σ) {a b : ℕ} (z : σ → Fin (a+b) → Space α)
    (ind : ∀ l, LinearIndependent F (z l)) (c : σ → Space α) (body : GWord α ρ)
    (hb1 : 1 ≤ b) (hbu : b < u) (hbody : GWord.Proper u body) :
    GWord.Proper u ((headWord e L (fun _ => b) (partB z) (partB_indep ind) ++ body) ++ shiftWord e L c) := by
  intro mv hmv
  rcases List.mem_append.mp hmv with h | h
  · rcases List.mem_append.mp h with h' | h'
    · exact proper_headWord u e L b (partB z) (partB_indep ind) hb1 hbu mv h'
    · exact hbody mv h'
  · exact proper_shiftWord u e L c mv h

end Words
end
end PowerSaving.MX
end OAI

#print axioms OAI.PowerSaving.MX.cut_target
#print axioms OAI.PowerSaving.MX.split_block
#print axioms OAI.PowerSaving.MX.GLiveKernelM.of_heads
#print axioms OAI.PowerSaving.MX.cut_heads_full
#print axioms OAI.PowerSaving.MX.cut_heads_half
#print axioms OAI.PowerSaving.MX.gwalk_splitWord
#print axioms OAI.PowerSaving.MX.hist_splitWord
#print axioms OAI.PowerSaving.MX.cutTgt_rank
#print axioms OAI.PowerSaving.MX.bph_unit_lines
#print axioms OAI.PowerSaving.MX.hist_cut_half
#print axioms OAI.PowerSaving.MX.proper_cut_half
#print axioms OAI.PowerSaving.MX.card_lines
#print axioms OAI.PowerSaving.MX.GLiveKernel.heads_recast
#print axioms OAI.PowerSaving.MX.bph_partA_fam

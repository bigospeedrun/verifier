import Submission.Engine.ClassSetup

/-! A single unnormalized binary Walsh transform suffices to implement the
fixed two-point kernel used by the all-length DFT compiler. Both surrounding
diagonal passes are charged as RAM programs, including their coefficients. -/
namespace OAI.PowerSaving
open RAM RAM.Ty Binary Complex Matrix Finset
noncomputable section
namespace WalshBridge

def digitWeight (e o : ℂ) {k : ℕ} (x : Bits k) : ℂ :=
  ∏ j, if x j = 0 then e else o

def walsh (k : ℕ) (x : Bits k → ℂ) := wal (Fin k) *ᵥ x

lemma littleC_entry (x y : F) :
    littleC x y =
      (if x = 0 then ca else cb) * littleH x y * (if y = 0 then 1 else -I) := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;>
    simp [littleC, littleH, ca, cb, sign] <;> ring_nf <;> simp [I_sq] <;> ring

theorem ripple_via_walsh (k : ℕ) (v : Bits k → ℂ) (x : Bits k) :
    ripple k v x = digitWeight ca cb x *
       walsh k (fun y => digitWeight 1 (-I) y * v y) x := by
  unfold ripple walsh Matrix.mulVec dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have h : kernel (Fin k) x y =
      digitWeight ca cb x * wal (Fin k) x y * digitWeight 1 (-I) y := by
    simp only [kernel, wal, digitProd_apply, digitWeight, littleC_entry,
      Finset.prod_mul_distrib]
  change kernel (Fin k) x y * v y = digitWeight ca cb x * (wal (Fin k) x y * (digitWeight 1 (-I) y * v y))
  rw [h]
  ring

/-- The precise input and output interface required of the binary kernel.
The RAM term has to be uniform in the binary width. -/
abbrev Kernel.{u} (z : ℝ) := ∀ (cl : Paint) (m : Bool) {ι : Type u}
    (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ),
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (walsh (k i) (v i)))
      (fun i => 2^k i * envelope z (k i))

section
universe u
variable {ι : Type u} {m : Bool} {cl : Paint} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ)
private abbrev src := fun i => givenBits cl (k i) (v i)

private theorem diagPass {e o : ℂ}
    (he : Has m (fun i => 2^k i) (simIn cl) (sc) (src k v) (fun _ => e))
    (ho : Has m (fun i => 2^k i) (simIn cl) (sc) (src k v) (fun _ => o)) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl) (src k v)
      (fun i => (bits (k i)).tape (fun x => digitWeight e o x * v i x)) (fun i => 2^k i) := by
  let B := fun i => 2^k i
  let wgt := fun i => (bits (k i)).tape (digitWeight e o)
  have hs : Small B k := (Small.self B).mono fun i => (Nat.lt_pow_self (by decide : 1 < 2) (n := k i)).le
  have hcoef : Can m B (simIn cl) (a sc) (src k v) wgt B :=
    LumTable.weight_table Can.first hs (Small.self B) he ho
  let xs := fun i => (src (cl := cl) k v i, wgt i)
  have hsz : Small B fun i => (bits (k i)).n := (Small.self B).mono fun i => (bits_len (k i)).le
  have hlen : Knows m B (p (simIn cl) (a sc)) xs fun i => (bits (k i)).n :=
    Can.len (t := sc) Can.second hsz
  have htab : Can m B (p (simIn cl) (a sc)) (bundle cl) xs
      (fun i => (bits (k i)).tape (fun x => digitWeight e o x * v i x)) B := by
    apply Can.mono (Can.layout (L := fun i => bits (k i)) (P := fun _ => 0) hlen _ hsz)
    · intro i; simp [B,bits_len]
    · let V := (Σ i, Bits (k i))
      exact Can.mul (Can.fetch (s := p (p (simIn cl) (a sc)) w) (x := fun d : V => (xs d.1, (bits (k d.1)).loc d.2)) (L := fun d : V => bits (k d.1)) (i := fun d => d.2)
          (t := sc) (v := fun _ x => digitWeight e o x) Can.first.snd Can.second)
        (Can.fetch (s := p (p (simIn cl) (a sc)) w) (x := fun d : V => (xs d.1, (bits (k d.1)).loc d.2)) (L := fun d : V => bits (k d.1)) (i := fun d => d.2)
          (t := c cl) (v := fun d => v d.1) Can.first.fst.snd.snd Can.second)
  exact hcoef.bind htab

private lemma prepareHalf : Has m (fun i => 2^k i) (simIn cl) sc (src (cl := cl) k v)
      (fun _ => (2:ℂ)⁻¹) :=
  ((Can.one.add Can.one).inv (fun _ => by norm_num)).cy (fun _ => by norm_num)

theorem ripple_program_of_walsh {z : ℝ} (kernelProgram : Kernel.{u} z) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl) (src k v)
      (fun i => (bits (k i)).tape (ripple (k i) (v i))) (fun i => 2^k i * envelope z (k i)) := by
  let pre := fun i (x : Bits (k i)) => digitWeight 1 (-I) x * v i x
  let mid := fun i => walsh (k i) (pre i)
  let W := fun i => 2^k i * envelope z (k i)
  have liftW : ∀ i, 2^k i ≤ W i := fun i => Nat.le_mul_of_pos_right _ (envelope_pos z _)
  have hI : Has m (fun i => 2^k i) (simIn cl) sc (src (cl := cl) k v) (fun _ => I) := Can.second.fst
  have a0 := (diagPass k v (e := 1) (o := -I) Can.one ((Can.zero.sub hI).cy fun _ => by simp)).mono liftW
  have a1 : Can m (fun i => 2^k i) (simIn cl) (simIn cl) (src k v) (src k pre) W :=
    Can.first.pair (Can.second.fst.pair a0)
  have a2 := a1.then_do (kernelProgram cl m k pre)
  have a3 : Can m (fun i => 2^k i) (simIn cl) (simIn cl) (src k v) (src k mid) W :=
    Can.first.pair (Can.second.fst.pair a2)
  have hJ : Has m (fun i => 2^k i) (simIn cl) sc (src (cl := cl) k mid) (fun _ => I) := Can.second.fst
  have hinv := prepareHalf (m := m) (cl := cl) k mid
  have a4 := (diagPass k mid (e := ca) (o := cb)
    (((Can.one.add hJ).mul hinv).cy (fun _ => by simp [ca, div_eq_mul_inv]))
    (((Can.one.sub hJ).mul hinv).cy (fun _ => by simp [cb, div_eq_mul_inv]))).mono liftW
  exact (a3.then_do a4).cy fun i => congrArg (bits (k i)).tape
    (funext fun x => (ripple_via_walsh (k i) (v i) x).symm)
end
end WalshBridge
end
end OAI.PowerSaving

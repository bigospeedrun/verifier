import Submission.Work.MixedCost.SeamCost
import Submission.Work.Mixed.Prog.Sem

/-!
# Mixed engine, cost part 8: the seam adapter as a RAM program

(agent e-r3cost, round wht45/lever, 19 Oct 2026.)

The seam asks for the kernel on ONE vector of `k` bits.  With `a = k/2`, `b = k - k/2` and the
code `catB a b : Bits a × Bits b ≃ Bits (a+b)` (low part first), the adapter is

1. reinterpret the input tape as `2^b` vectors of `2^a` entries (`tape_catB`: the same tape);
2. ONE top job `Do(a, 2^b)`: the kernel on the low `a` bits (`hlow_catB`);
3. transpose (`transposeC`, `O(2^k)`);
4. ONE top job `Do(b, 2^a)`: the kernel on the high `b` bits (`hhigh_catB`);
5. transpose back; by commuting Hadamards (`hhigh_hlow`, Sem.lean) this is `ripple k`.

Its work is `topCost a (2^b) + topCost b (2^a) + O(2^k)` = `O(adapterCost k)` (`adapter_program`).
The top jobs are a hypothesis (the closed engine of `Work.MixedCost.Wire.mixed_close`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.MCost
open PowerSaving.RAM PowerSaving.Binary PowerSaving.MX Ty Matrix Finset

noncomputable section

universe U

/-! ## 1. Semantics of the two passes -/

lemma hlow_catB (a b : ℕ) (w : Bits (a+b) → ℂ) (x : Bits a) (q : Bits b) :
    hlow (a+b) a w (catB a b (x, q)) = ripple a (fun x' => w (catB a b (x', q))) x := by
  unfold hlow ripple
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (catB a b), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  simp only [maskK_catB]
  rw [Finset.sum_eq_single q]
  · simp
  · intro q' _ hq'
    rw [if_neg (Ne.symm hq')]; ring
  · intro h; exact absurd (Finset.mem_univ q) h

lemma hhigh_catB (a b : ℕ) (w : Bits (a+b) → ℂ) (x : Bits a) (y : Bits b) :
    hhigh (a+b) a w (catB a b (x, y)) = ripple b (fun y' => w (catB a b (x, y'))) y := by
  unfold hhigh ripple
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (catB a b), Fintype.sum_prod_type]
  simp only [maskHi_catB]
  rw [Finset.sum_eq_single x]
  · refine Finset.sum_congr rfl (fun y' _ => ?_)
    simp
  · intro x' _ hx'
    refine Finset.sum_eq_zero (fun y' _ => ?_)
    rw [if_neg (Ne.symm hx')]; ring
  · intro h; exact absurd (Finset.mem_univ x) h

/-- The tape of a vector on `a + b` bits is the tape of its `2^b` slices of `2^a` entries. -/
lemma tape_catB (a b : ℕ) (w : Bits (a+b) → ℂ) :
    (bits (a+b)).tape w = ((bits b).pair (bits a)).tape (fun z => w (catB a b (z.2, z.1))) := by
  refine Layout.verify _ _ 0 _ ?_ ?_
  · change 2 ^ (a + b) = 2 ^ b * 2 ^ a
    rw [pow_add, mul_comm]
  · intro z
    have hl : ((bits b).pair (bits a)).loc z = (bits (a+b)).loc (catB a b (z.2, z.1)) := by
      rw [Layout.pair_loc, catB_loc]
      change (bits b).loc z.1 * 2 ^ a + (bits a).loc z.2 = (bits a).loc z.2 + 2 ^ a * (bits b).loc z.1
      ring
    rw [hl, Layout.read]

lemma tape_castB {k a b : ℕ} (h : a + b = k) (v : Bits k → ℂ) :
    (bits k).tape v = (bits (a+b)).tape (fun z => v (castB h z)) := by
  subst h
  rfl

lemma ripple_castB {k a b : ℕ} (h : a + b = k) (v : Bits k → ℂ) :
    (bits k).tape (ripple k v) = (bits (a+b)).tape (ripple (a+b) (fun z => v (castB h z))) := by
  subst h
  rfl

/-! ## 2. A transposition pass -/

section
variable {m : Bool} {ι : Type U} {cl : Paint} {s : Ty} {x : ι → T s} {B : ι → ℕ}

/-- **Transposition**: from the tape of `L.pair M` (and the two sizes, ready) to the tape of
`M.pair L`, in work `M.n * L.n`. -/
theorem transposeC {α β : ι → Type} {L : ∀ i, Layout (α i)} {M : ∀ i, Layout (β i)}
    {f : ∀ i, α i × β i → ℂ}
    (ht : Has m B s (bundle cl) x (fun i => ((L i).pair (M i)).tape (f i)))
    (hL : Knows m B s x (fun i => (L i).n)) (hM : Knows m B s x (fun i => (M i).n))
    (hLs : Small B (fun i => (L i).n)) (hMs : Small B (fun i => (M i).n)) :
    Can m B s (bundle cl) x (fun i => ((M i).pair (L i)).tape (fun z => f i (z.2, z.1)))
      (fun i => (M i).n * (L i).n) := by
  let Q := Σ i, β i × α i
  let σ : Q → ι := Sigma.fst
  let pos (d : Q) : ℕ := ((M d.1).pair (L d.1)).loc d.2
  let E (d : Q) : T (p s w) := (x d.1, pos d)
  have hLQ : Knows m (fun d : Q => B d.1) (p s w) E (fun d => (L d.1).n) :=
    Can.first.then_do (hL.reindex σ)
  have hMQ : Knows m (fun d : Q => B d.1) (p s w) E (fun d => (M d.1).n) :=
    Can.first.then_do (hM.reindex σ)
  have hpos : Knows m (fun d : Q => B d.1) (p s w) E
      (fun d => ((M d.1).pair (L d.1)).loc d.2) := Can.second
  have hsQ : Small (fun d : Q => B d.1) (fun d => (M d.1).n * (L d.1).n) :=
    (hMs.mul hLs).reindex σ
  have hy : Knows m (fun d : Q => B d.1) (p s w) E (fun d => (M d.1).loc d.2.1) :=
    Can.addr_high (L := fun d : Q => M d.1) (R := fun d : Q => L d.1) (u := fun d : Q => d.2) hpos hLQ hsQ
  have hx : Knows m (fun d : Q => B d.1) (p s w) E (fun d => (L d.1).loc d.2.2) :=
    Can.addr_low (L := fun d : Q => M d.1) (R := fun d : Q => L d.1) (u := fun d : Q => d.2) hpos hLQ hsQ
  have hadr : Knows m (fun d : Q => B d.1) (p s w) E
      (fun d => ((L d.1).pair (M d.1)).loc (d.2.2, d.2.1)) :=
    Can.addr_join (L := fun d : Q => L d.1) (R := fun d : Q => M d.1) (u := fun d : Q => (d.2.2, d.2.1))
      hx hy hMQ (hLs.reindex σ) (hMs.reindex σ)
  have hval : Has m (fun d : Q => B d.1) (p s w) (c cl) E (fun d => f d.1 (d.2.2, d.2.1)) :=
    Can.fetch (t := c cl) (L := fun d : Q => (L d.1).pair (M d.1)) (v := fun d : Q => f d.1)
      (i := fun d : Q => (d.2.2, d.2.1)) (Can.first.then_do (ht.reindex σ)) hadr
  have hn : Knows m B s x (fun i => ((M i).pair (L i)).n) := hM.times hL hMs hLs
  have H := Can.layout (L := fun i => (M i).pair (L i)) (t := c cl) (P := fun _ => 0)
    (v := fun i z => f i (z.2, z.1)) hn hval (hMs.mul hLs)
  refine H.mono (fun i => ?_)
  simp

/-! ## 3. The adapter -/

/-- The pointwise identity behind the adapter: the kernel on the high `b` bits of the kernel on
the low `a` bits, read through the two transpositions, is the whole kernel. -/
lemma adapter_entry (a b : ℕ) (w : Bits (a+b) → ℂ) (x : Bits a) (y : Bits b) :
    whole b (fun z : Bits a × Bits b => whole a (fun z' : Bits b × Bits a => w (catB a b (z'.2, z'.1)))
      (z.2, z.1)) (x, y) = ripple (a+b) w (catB a b (x, y)) := by
  have e2 : whole b (fun z : Bits a × Bits b =>
      whole a (fun z' : Bits b × Bits a => w (catB a b (z'.2, z'.1))) (z.2, z.1)) (x, y)
      = ripple b (fun y' => hlow (a+b) a w (catB a b (x, y'))) y := by
    show ripple b (fun j => whole a (fun z' : Bits b × Bits a => w (catB a b (z'.2, z'.1))) (j, x)) y = _
    congr 1
    funext y'
    show ripple a (fun j => w (catB a b (j, y'))) x = _
    exact (hlow_catB a b w x y').symm
  rw [e2, ← hhigh_catB, hhigh_hlow]

theorem adapter_program (R : Rule) (n0 : ℕ) (J : ℕ → ℕ) (cl : Paint) (m : Bool) {ι : Type U}
    (hTop : ∀ (n b : ι → ℕ) (u : ∀ i, Sim (Bits (b i)) (n i) → ℂ),
      Can m (fun i => (2 ^ b i + 1) * 2 ^ n i) (simIn cl) (bundle cl)
        (fun i => loaded cl (bits (b i)) (n i) (u i))
        (fun i => (sim (bits (b i)) (n i)).tape (whole (n i) (u i)))
        (fun i => R.topCost n0 J (n i) (2 ^ b i)))
    (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2 ^ k i) (simIn cl) (bundle cl) (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (ripple (k i) (v i))) (fun i => R.adapterCost n0 J (k i)) := by
  let a : ι → ℕ := fun i => k i / 2
  let b : ι → ℕ := fun i => k i - k i / 2
  have hab : ∀ i, a i + b i = k i := fun i => by simp only [a, b]; omega
  let vw (i : ι) : Bits (a i + b i) → ℂ := fun z => v i (castB (hab i) z)
  let Bd : ι → ℕ := fun i => 2 ^ k i
  let Wt : ι → ℕ := fun i => R.adapterCost n0 J (k i)
  -- sizes
  have hk2 : ∀ i, k i ≤ 2 ^ k i := fun i => (Nat.lt_two_pow_self).le
  have sK : Small Bd k := ⟨1, fun i => by simp only [Bd, pow_one]; have := hk2 i; omega⟩
  have sA : Small Bd a := sK.mono (fun i => Nat.div_le_self _ _)
  have sB : Small Bd b := sK.mono (fun i => Nat.sub_le _ _)
  have h2ak : ∀ i, 2 ^ a i ≤ 2 ^ k i := fun i => Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)
  have h2bk : ∀ i, 2 ^ b i ≤ 2 ^ k i := fun i => Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have s2A : Small Bd (fun i => 2 ^ a i) := ⟨1, fun i => by simp only [Bd, pow_one]; have := h2ak i; omega⟩
  have s2B : Small Bd (fun i => 2 ^ b i) := ⟨1, fun i => by simp only [Bd, pow_one]; have := h2bk i; omega⟩
  have hkab : ∀ i, 2 ^ a i * 2 ^ b i = 2 ^ k i := fun i => by rw [← pow_add, hab i]
  have sD1 : Small Bd (fun i => (2 ^ b i + 1) * 2 ^ a i) := ⟨2, fun i => by
    have h1 : (2 ^ b i + 1) * 2 ^ a i ≤ 2 * 2 ^ k i := by
      have := hkab i; have := h2ak i; nlinarith
    simp only [Bd]; nlinarith⟩
  have sD2 : Small Bd (fun i => (2 ^ a i + 1) * 2 ^ b i) := ⟨2, fun i => by
    have h1 : (2 ^ a i + 1) * 2 ^ b i ≤ 2 * 2 ^ k i := by
      have := hkab i; have := h2bk i; nlinarith
    simp only [Bd]; nlinarith⟩
  -- the budget
  have hWk : ∀ i, 2 ^ k i ≤ Wt i := fun i => by simp only [Wt, Rule.adapterCost]; exact Nat.le_add_left _ _
  have hW1 : ∀ i, R.topCost n0 J (a i) (2 ^ b i) ≤ Wt i := fun i => by
    simp only [Wt, Rule.adapterCost, a, b]; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hW2 : ∀ i, R.topCost n0 J (b i) (2 ^ a i) ≤ Wt i := fun i => by
    simp only [Wt, Rule.adapterCost, a, b]; exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  have dA : Dom Wt a := Dom.of_le (fun i => le_trans (Nat.div_le_self _ _) (le_trans (hk2 i) (hWk i)))
  have dB : Dom Wt b := Dom.of_le (fun i => le_trans (Nat.sub_le _ _) (le_trans (hk2 i) (hWk i)))
  -- stage A: the input and the two powers
  let x0 : ι → T (simIn cl) := fun i => givenBits cl (k i) (v i)
  have hk : Knows m Bd (simIn cl) x0 k := Can.first
  have ha : Knows m Bd (simIn cl) x0 a := hk.dvdW (Can.wc 2) sK
  have hb : Knows m Bd (simIn cl) x0 b := hk.minus ha sK
  have h2a : Can m Bd (simIn cl) w x0 (fun i => 2 ^ a i) Wt :=
    Can.wTwo (ha.mono (fun _ => Nat.zero_le _)) sA s2A dA
  have h2b : Can m Bd (simIn cl) w x0 (fun i => 2 ^ b i) Wt :=
    Can.wTwo (hb.mono (fun _ => Nat.zero_le _)) sB s2B dB
  let sE : Ty := p (simIn cl) (p w w)
  let E0 : ι → T sE := fun i => (x0 i, (2 ^ a i, 2 ^ b i))
  have hE0 : Can m Bd (simIn cl) sE x0 E0 Wt := Can.pair Can.id (Can.pair h2a h2b)
  -- stage B: pass 1, the kernel on the low `a` bits of each of the `2^b` slices
  let u1 (i : ι) : Sim (Bits (b i)) (a i) → ℂ := fun z => vw i (catB (a i) (b i) (z.2, z.1))
  have hin1 : Can m Bd sE (simIn cl) E0 (fun i => loaded cl (bits (b i)) (a i) (u1 i)) Wt := by
    have ha' : Knows m Bd sE E0 a := Can.first.then_do ha
    have hr : Has m Bd sE (p sc (bundle cl)) E0 (fun i => (x0 i).2) := Can.first.then_do Can.second
    refine ((Can.pair ha' hr).mono (fun _ => Nat.zero_le _)).cong (fun _ => rfl) (fun i => ?_)
    show (a i, (x0 i).2) = loaded cl (bits (b i)) (a i) (u1 i)
    simp only [x0, givenBits, loaded]
    rw [tape_castB (hab i), tape_catB]
    rfl
  let t1 : ι → T (bundle cl) := fun i => (sim (bits (b i)) (a i)).tape (whole (a i) (u1 i))
  have hp1 : Can m Bd (simIn cl) (bundle cl) (fun i => loaded cl (bits (b i)) (a i) (u1 i)) t1 Wt :=
    ((hTop a b u1).ambient sD1).mono hW1
  have hT1 : Can m Bd sE (bundle cl) E0 t1 Wt := hin1.then_do hp1
  -- stage C: transpose
  let u2 (i : ι) : Sim (Bits (a i)) (b i) → ℂ := fun z => whole (a i) (u1 i) (z.2, z.1)
  let t1' : ι → T (bundle cl) := fun i => ((bits (a i)).pair (bits (b i))).tape (u2 i)
  have hTr1 : Can m Bd (p sE (bundle cl)) (bundle cl) (fun i => (E0 i, t1 i)) t1' Wt := by
    have H := transposeC (m := m) (B := Bd) (cl := cl) (s := p sE (bundle cl))
      (x := fun i => (E0 i, t1 i)) (L := fun i => bits (b i)) (M := fun i => bits (a i))
      (f := fun i => whole (a i) (u1 i)) Can.second
      (Can.first.then_do (Can.second.then_do Can.second))
      (Can.first.then_do (Can.second.then_do Can.first)) s2B s2A
    refine H.mono (fun i => ?_)
    change 2 ^ a i * 2 ^ b i ≤ Wt i
    rw [hkab i]; exact hWk i
  have hT1' : Can m Bd sE (bundle cl) E0 t1' Wt := Can.bind hT1 hTr1
  -- stage D: pass 2, the kernel on the high `b` bits
  have hin2 : Can m Bd (p sE (bundle cl)) (simIn cl) (fun i => (E0 i, t1' i))
      (fun i => loaded cl (bits (a i)) (b i) (u2 i)) Wt := by
    have hb2 : Knows m Bd (p sE (bundle cl)) (fun i => (E0 i, t1' i)) b :=
      Can.first.then_do (Can.first.then_do hb)
    have hI : Has m Bd (p sE (bundle cl)) sc (fun i => (E0 i, t1' i)) (fun i => (x0 i).2.1) :=
      Can.first.then_do (Can.first.then_do Can.second.fst)
    have ht : Has m Bd (p sE (bundle cl)) (bundle cl) (fun i => (E0 i, t1' i)) t1' := Can.second
    exact ((Can.pair hb2 (Can.pair hI ht)).mono (fun _ => Nat.zero_le _)).cong (fun _ => rfl)
      (fun i => rfl)
  let t2 : ι → T (bundle cl) := fun i => (sim (bits (a i)) (b i)).tape (whole (b i) (u2 i))
  have hp2 : Can m Bd (simIn cl) (bundle cl) (fun i => loaded cl (bits (a i)) (b i) (u2 i)) t2 Wt :=
    ((hTop b a u2).ambient sD2).mono hW2
  have hT2 : Can m Bd sE (bundle cl) E0 t2 Wt := Can.bind hT1' (hin2.then_do hp2)
  -- stage E: transpose back
  let t3 : ι → T (bundle cl) := fun i =>
    ((bits (b i)).pair (bits (a i))).tape (fun z => whole (b i) (u2 i) (z.2, z.1))
  have hTr2 : Can m Bd (p sE (bundle cl)) (bundle cl) (fun i => (E0 i, t2 i)) t3 Wt := by
    have H := transposeC (m := m) (B := Bd) (cl := cl) (s := p sE (bundle cl))
      (x := fun i => (E0 i, t2 i)) (L := fun i => bits (a i)) (M := fun i => bits (b i))
      (f := fun i => whole (b i) (u2 i)) Can.second
      (Can.first.then_do (Can.second.then_do Can.first))
      (Can.first.then_do (Can.second.then_do Can.second)) s2A s2B
    refine H.mono (fun i => ?_)
    change 2 ^ b i * 2 ^ a i ≤ Wt i
    rw [mul_comm, hkab i]; exact hWk i
  have hT3 : Can m Bd sE (bundle cl) E0 t3 Wt := Can.bind hT2 hTr2
  -- the output is the kernel on all `k` bits
  refine (hE0.then_do hT3).cong (fun _ => rfl) (fun i => ?_)
  show t3 i = (bits (k i)).tape (ripple (k i) (v i))
  rw [ripple_castB (hab i), tape_catB]
  simp only [t3]
  congr 1
  funext z
  exact adapter_entry (a i) (b i) (vw i) z.2 z.1

end

end
end PowerSaving.MCost
end OAI

#print axioms OAI.PowerSaving.MCost.adapter_program
#print axioms OAI.PowerSaving.MCost.transposeC
#print axioms OAI.PowerSaving.MCost.hlow_catB
#print axioms OAI.PowerSaving.MCost.hhigh_catB
#print axioms OAI.PowerSaving.MCost.tape_catB

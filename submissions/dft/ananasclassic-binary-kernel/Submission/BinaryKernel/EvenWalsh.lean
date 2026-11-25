import Submission.BinaryKernel.WalshBridge

/-! Uniformly pad an odd number of bits by repeating the input on one
spectator bit. At frequency zero the two copies add. This removes both
the even-width restriction and the normalization of the plan kernel. -/
namespace OAI.PowerSaving.WalshBridge
open RAM RAM.Ty Binary Complex Matrix Finset
noncomputable section

def normalized (k : ℕ) (v : Bits k → ℂ) (y : Bits k) :=
  walsh k v y / (2:ℂ)^(k/2)

abbrev EvenKernel.{u} (z : ℝ) := ∀ (cl : Paint) (m : Bool) {ι : Type u}
    (k : ι → ℕ) (_even : ∀ i, Even (k i)) (v : ∀ i, Bits (k i) → ℂ),
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (normalized (k i) (v i)))
      (fun i => 2^k i * envelope z (k i))

private abbrev pad (k : ℕ) := k+k%2
private lemma padEven (k : ℕ) : Even (pad k) := ⟨(k+1)/2, by unfold pad; omega⟩
private def rep (k : ℕ) (v : Bits k → ℂ) (x : Bits (pad k)) : ℂ :=
  v ((catB k (k%2)).symm x).1
private def atZero (k : ℕ) (x : Bits k) : Bits (pad k) := catB k (k%2) (x,0)
private lemma atZero_loc (k : ℕ) (x : Bits k) : (bits (pad k)).loc (atZero k x) = (bits k).loc x := by
  rw [atZero, catB_loc]
  simp [bits_loc]
private lemma rep_loc (k : ℕ) (x : Bits (pad k)) :
    (bits k).loc ((catB k (k%2)).symm x).1 = (bits (pad k)).loc x % 2^k := by
  obtain ⟨⟨u,w⟩,rfl⟩ := (catB k (k%2)).surjective x
  rw [Equiv.symm_apply_apply, catB_loc]
  simp [Nat.mod_eq_of_lt (bits_lt k u)]

private theorem normalize_pad (k : ℕ) (v : Bits k → ℂ) (x : Bits k) :
    (2:ℂ)^(k/2) * normalized (pad k) (rep k v) (atZero k x) = walsh k v x := by
  have sep (y : Bits k × Bits (k%2)) :
      wal (Fin (pad k)) (atZero k x) (catB k (k%2) y) = wal (Fin k) x y.1 := by
    simp only [wal, atZero, pad, digitProd_apply, catB, Equiv.coe_fn_mk, Fin.prod_univ_add, Fin.append_left, Fin.append_right]
    simp [littleH, sign]
  have e : walsh (pad k) (rep k v) (atZero k x) = (2:ℂ)^(k%2) * walsh k v x := by
    rw [walsh, GenMove.mulVec_apply']
    rw [← (catB k (k%2)).sum_comp (fun b => wal (Fin (pad k)) (atZero k x) b * rep k v b), Fintype.sum_prod_type]
    simp only [sep, rep, Equiv.symm_apply_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [walsh, GenMove.mulVec_apply', Finset.mul_sum]
    congr 1; funext y
    simp [Bits,Space,ZMod.card]
  rw [normalized,e,show pad k / 2 = k/2+k%2 by unfold pad; omega,pow_add]
  field_simp

private lemma padCost {z : ℝ} (hz : 0 ≤ z) (hu : z ≤ 1) (k : ℕ) :
    2^(pad k) * envelope z (pad k) ≤ 4 * (2^k * envelope z k) := by
  have lepow : 2^(pad k) ≤ 2*(2^k) := by
    calc 2^(pad k) ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) (by unfold pad; omega)
         _ = _ := pow_succ' _ _
  have hk : (pad k : ℝ) + 1 ≤ 2*((k:ℝ)+1) := by
    have hk' : pad k ≤ k+1 := by unfold pad; omega
    exact_mod_cast (show pad k + 1 ≤ 2*(k+1) by omega)
  have hu' : (2:ℝ)^z ≤ 2 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2:ℝ)) hu
  have hen : envelope z (pad k) ≤ 2 * envelope z k := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_mul, Nat.cast_ofNat]
    calc ((pad k:ℝ)+1)^z ≤ (2*((k:ℝ)+1))^z := Real.rpow_le_rpow (by positivity) hk hz
      _ = (2:ℝ)^z * ((k:ℝ)+1)^z := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2*(envelope z k:ℝ) := by gcongr; exact Nat.le_ceil _
  exact (Nat.mul_le_mul lepow hen).trans (by ring_nf; rfl)

theorem of_even_kernel.{u} {z : ℝ} (hz : 0 ≤ z) (hu : z ≤ 1)
    (h : EvenKernel.{u} z) : Kernel.{u} z := by
  intro cl m ι k v
  let B := fun i => 2^k i
  let K := fun i => pad (k i)
  let V := fun i => rep (k i) (v i)
  let x := fun i => givenBits cl (k i) (v i)
  let X := fun i => givenBits cl (K i) (V i)
  let W := fun i => B i * envelope z (k i)
  have bW : ∀ i, B i ≤ W i := fun i => Nat.le_mul_of_pos_right _ (envelope_pos z _)
  have sp : Small B k := (Small.self B).mono fun i => Nat.lt_two_pow_self.le
  have hlen : Knows m B (simIn cl) x B := Can.len Can.second.snd ((Small.self B).mono fun i => (bits_len (k i)).le)
  have hk : Knows m B (simIn cl) x k := Can.first
  have hh := hk.modW (Can.wc 2) sp
  have hK : Knows m B (simIn cl) x K := hk.plus hh sp sp.mod
  have large : ∀ i, 2^K i ≤ 2*B i := fun i => by
    dsimp [K,B,pad]; rw [pow_add]; have hh : 2^(k i%2) ≤ 2 := by
      calc 2^(k i%2) ≤ 2^1 := Nat.pow_le_pow_right (by decide) (by omega)
           _ = 2 := rfl
    simpa [mul_comm] using Nat.mul_le_mul_left (2^k i) hh
  have sbig : Small B (fun i => 2^K i) := ((Small.const B 2).mul (Small.self B)).mono large
  have hdim : Knows m B (simIn cl) x (fun i => (bits (K i)).n) := by
    have factor : Knows m B (simIn cl) x (fun i => 2^(k i%2)) := by
      exact (hh.plus (Can.wc 1) sp.mod (Small.const B 1)).cy fun i => by
        have := Nat.mod_lt (k i) (by decide : 0<2)
        interval_cases k i % 2 <;> decide
    exact (hlen.times factor (Small.self B) ((Small.const B 2).mono fun i => by
      have := Nat.mod_lt (k i) (by decide : 0<2); interval_cases k i % 2 <;> decide)).cy
      fun i => by simp [K,pad,B,bits_len,pow_add]
  have hrep : Can m B (simIn cl) (bundle cl) x (fun i => (bits (K i)).tape (V i)) (fun i => 2^K i) := by
    apply Can.mono (Can.layout (L := fun i => bits (K i)) (P := fun _ => 0) hdim _ (sbig.mono fun i => (bits_len _).le))
    · intro i; simp [bits_len]
    · let J := Σ i, Bits (K i)
      have addr := (Can.second (s := simIn cl) (t := w)
        (v := fun d : J => (x d.1,(bits (K d.1)).loc d.2))).modW (Can.first.then_do (hlen.reindex Sigma.fst))
        (Small.loc (L := fun d : J => bits (K d.1)) (x := fun d => d.2) ((sbig.reindex Sigma.fst).mono fun d => (bits_len _).le))
      exact Can.fetch (t := c cl) (L := fun d : J => bits (k d.1)) (i := fun d => ((catB (k d.1) (k d.1%2)).symm d.2).1)
        (v := fun d => v d.1) Can.first.snd.snd (addr.cy fun d => (rep_loc _ _).symm)
  have hs : Can m B (simIn cl) (simIn cl) x X W :=
    (hK.mono (fun _ => Nat.zero_le _)).pair (Can.second.fst.pair (hrep.weaken
      ⟨2, fun i => by have := large i; have := bW i; nlinarith⟩))
  let ans := fun i => normalized (K i) (V i)
  have kernel := (h cl m K (fun i => padEven _) V).ambient sbig
  have result := hs.then_do (kernel.weaken ⟨4, fun i => by have := padCost hz hu (k i); dsimp [W,B,K]; omega⟩)
  have divK := hk.dvdW (Can.wc 2) sp
  have fac : Can m B (simIn cl) sc x (fun i => (2:ℂ)^(k i/2)) W := by
    refine (Can.loop (n := fun i => k i/2) (uB := fun _ _ => 0)
      (v := fun _ j => (2:ℂ)^j) (W := fun _ => 0) (W' := fun _ => 0)
      divK (Can.one.cy fun _ => by simp)
      ((Can.second.snd.add Can.second.snd).cy fun i => by
        change (2:ℂ)^i.j+(2:ℂ)^i.j=(2:ℂ)^(i.j+1); ring)
      sp.div).mono fun i => ?_
    simp only [Nat.zero_add, Finset.sum_const_zero, Nat.add_zero]
    exact (Nat.div_le_self _ _).trans (Nat.lt_two_pow_self.le.trans (bW i))
  have prepared := (Can.id.pair result).pair fac
  let post := fun i => ((x i,(bits (K i)).tape (ans i)),(2:ℂ)^(k i/2))
  have postMap : Can m B (p (p (simIn cl) (bundle cl)) sc) (bundle cl) post
      (fun i => (bits (k i)).tape (walsh (k i) (v i))) W := by
    have hN : Knows m B (p (p (simIn cl) (bundle cl)) sc) post (fun i => (bits (k i)).n) := (Can.first.fst.then_do hlen).cy (fun i => (bits_len (k i)).symm)
    apply Can.mono (Can.layout (L := fun i => bits (k i)) (P := fun _ => 0) hN _ ((Small.self B).mono fun _ => (bits_len _).le))
    · intro i; simpa [bits_len] using bW i
    · let J := Σ i, Bits (k i)
      exact (Can.first.snd.mul (Can.fetch (t := c cl)
        (L := fun d : J => bits (K d.1)) (i := fun d => atZero (k d.1) d.2)
        (v := fun d => ans d.1) Can.first.fst.snd (Can.second.cy fun d => (atZero_loc _ _).symm))).cy
        (fun d => normalize_pad _ _ _)
  exact prepared.then_do postMap

end
end OAI.PowerSaving.WalshBridge

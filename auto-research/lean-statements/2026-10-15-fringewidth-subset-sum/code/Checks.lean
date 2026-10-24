import Statement

/-! Checks for the proposed Subset Sum statement. Lean 4.33.1, no other imports. -/

open BigOSpeedrun.SubsetSum

/-! ## Exact rational substitution -/

theorem num_49_100 : ((49 : Rat) / 100).num.toNat = 49 := by decide +kernel
theorem den_49_100 : ((49 : Rat) / 100).den = 100 := by decide +kernel
theorem num_4877_10000 : ((4877 : Rat) / 10000).num.toNat = 4877 := by decide +kernel
theorem den_4877_10000 : ((4877 : Rat) / 10000).den = 10000 := by decide +kernel

/-- The target at 49/100 unfolds to the expected integer inequality. -/
theorem bigO_49_100 (T : Nat → Nat) :
    BigO T ((49 : Rat) / 100) ↔ ∃ K : Nat, ∀ n ≥ 2, T n ^ 100 ≤ K * 2 ^ (49 * n) := by
  rw [BigO, num_49_100, den_49_100]

/-! ## A theorem at one bound is not a theorem at another bound (elaboration check, not Comparator) -/

example (h : SolvedInTime ((49 : Rat) / 100)) : SolvedInTime ((49 : Rat) / 100) := by
  fail_if_success exact (h : SolvedInTime ((1 : Rat) / 2))
  fail_if_success exact (h : SolvedInTime ((4877 : Rat) / 10000))
  exact h

/-! ## Smaller exponents are stronger -/

theorem toNat_mul_le_of_le {x y : Int} {d e : Nat} (hd : 0 < d) (h : x * e ≤ y * d) :
    x.toNat * e ≤ y.toNat * d := by
  cases x with
  | negSucc a => simp
  | ofNat a =>
    cases y with
    | ofNat b =>
      have : (a * e : Int) ≤ (b * d : Int) := by simpa using h
      simpa using Int.ofNat_le.mp this
    | negSucc b =>
      have h1 : (0 : Int) ≤ (a : Int) * e := Int.mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg e)
      have h2 : Int.negSucc b * d < 0 :=
        Int.mul_neg_of_neg_of_pos (Int.negSucc_lt_zero b) (Int.ofNat_lt.mpr hd)
      exact absurd (Int.lt_of_le_of_lt (Int.le_trans h1 h) h2) (Int.lt_irrefl 0)

theorem BigO.mono {T : Nat → Nat} {α β : Rat} (h : BigO T α) (hαβ : α ≤ β) : BigO T β := by
  obtain ⟨K, hK⟩ := h
  have hcross : α.num.toNat * β.den ≤ β.num.toNat * α.den :=
    toNat_mul_le_of_le α.den_pos ((Rat.le_iff α β).mp hαβ)
  refine ⟨(K + 1) ^ β.den, fun n hn => ?_⟩
  have hd : α.den ≠ 0 := Nat.pos_iff_ne_zero.mp α.den_pos
  refine (Nat.pow_le_pow_iff_left hd).mp ?_
  have h1 : K ^ β.den ≤ ((K + 1) ^ β.den) ^ α.den :=
    calc K ^ β.den ≤ (K + 1) ^ β.den := Nat.pow_le_pow_left (Nat.le_succ K) _
      _ ≤ ((K + 1) ^ β.den) ^ α.den := Nat.le_self_pow hd _
  have h2 : 2 ^ (α.num.toNat * n * β.den) ≤ 2 ^ (β.num.toNat * n * α.den) := by
    apply Nat.pow_le_pow_right (by decide)
    calc α.num.toNat * n * β.den = α.num.toNat * β.den * n := by
          rw [Nat.mul_assoc, Nat.mul_comm n, ← Nat.mul_assoc]
      _ ≤ β.num.toNat * α.den * n := Nat.mul_le_mul_right n hcross
      _ = β.num.toNat * n * α.den := by rw [Nat.mul_assoc, Nat.mul_comm α.den, ← Nat.mul_assoc]
  calc (T n ^ β.den) ^ α.den
      = (T n ^ α.den) ^ β.den := by
        rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm β.den α.den]
    _ ≤ (K * 2 ^ (α.num.toNat * n)) ^ β.den := Nat.pow_le_pow_left (hK n hn) _
    _ = K ^ β.den * 2 ^ (α.num.toNat * n * β.den) := by
        rw [Nat.mul_pow, ← Nat.pow_mul 2 (α.num.toNat * n) β.den]
    _ ≤ ((K + 1) ^ β.den) ^ α.den * 2 ^ (β.num.toNat * n * α.den) := Nat.mul_le_mul h1 h2
    _ = ((K + 1) ^ β.den * 2 ^ (β.num.toNat * n)) ^ α.den := by
        rw [Nat.mul_pow, ← Nat.pow_mul 2 (β.num.toNat * n) α.den]

theorem SolvedInTime.mono {α β : Rat} (h : SolvedInTime α) (hαβ : α ≤ β) : SolvedInTime β := by
  obtain ⟨P, hP, hT⟩ := h
  refine ⟨P, hP, fun c => ?_⟩
  obtain ⟨T, hBig, hrun⟩ := hT c
  exact ⟨T, BigO.mono hBig hαβ, hrun⟩

/-! ## Counting -/

theorem count_eq_self_of_forall {p : Nat → Prop} [DecidablePred p] (h : ∀ s, p s) :
    ∀ N, count p N = N
  | 0 => rfl
  | N + 1 => by simp [count, count_eq_self_of_forall h N, h N]

theorem count_eq_zero_of_forall_not {p : Nat → Prop} [DecidablePred p] (h : ∀ s, ¬ p s) :
    ∀ N, count p N = 0
  | 0 => rfl
  | N + 1 => by simp [count, count_eq_zero_of_forall_not h N, h N]

/-! ## A concrete instance: n = 2, a = (1, 1), t = 0. The empty subset solves it. -/

def x0 : Instance 2 where
  a := fun _ => 1
  t := 0
  pos := fun _ => Nat.one_pos

theorem x0_yes : x0.yes := ⟨fun _ => false, by decide⟩

/-- The program that accepts at once is correct on `x0`, with horizon 1. -/
theorem accept_correct : Correct [.accept] x0 := by
  refine ⟨1, fun ρ => rfl, ?_⟩
  intro N
  refine Or.inl ⟨x0_yes, ?_⟩
  rw [count_eq_self_of_forall (p := fun s => run [.accept] x0 (tape _ s) 1 = some true) (fun s => rfl)]
  omega

/-- The program that rejects at once is not correct on `x0`, whatever the horizon. -/
theorem reject_not_correct : ¬ Correct [.reject] x0 := by
  rintro ⟨t, hhalt, hcount⟩
  have hnever : ∀ s, ¬ (run [.reject] x0 (tape _ s) t = some true) := by
    intro s hs
    cases t <;> simp [run, exec] at hs
  rcases hcount with ⟨_, hle⟩ | ⟨hno, _⟩
  · rw [count_eq_zero_of_forall_not hnever] at hle
    have := Nat.two_pow_pos (wordLength 2 x0.bits * t)
    omega
  · exact hno x0_yes

/-! ## Executable checks of the semantics, with small words -/

/-- Accept iff `a₁ + a₂ = t`, for `n = 2`: cells 0 = n, 1 = a₁, 2 = a₂, 3 = t. -/
def sumProgram : List Instr :=
  [.add 4 1 2, .blt 4 3 5, .blt 3 4 5, .accept, .reject, .reject]

/-- Accept iff the first random word is odd. -/
def parityProgram : List Instr :=
  [.rand 1, .one 2, .and 3 1 2, .blt 3 2 5, .accept, .reject]

-- 3 + 4 = 7: accepts after 4 steps, not within 3.
#eval exec (w := 8) sumProgram (fun _ => 0) 4 0 0 (loadWords 8 [2, 3, 4, 7])
#eval exec (w := 8) sumProgram (fun _ => 0) 3 0 0 (loadWords 8 [2, 3, 4, 7])
-- 3 + 4 ≠ 6 and 3 + 4 ≠ 8.
#eval exec (w := 8) sumProgram (fun _ => 0) 10 0 0 (loadWords 8 [2, 3, 4, 6])
#eval exec (w := 8) sumProgram (fun _ => 0) 10 0 0 (loadWords 8 [2, 3, 4, 8])
-- Words wrap: 200 + 100 = 300 ≡ 44 (mod 256).
#eval exec (w := 8) sumProgram (fun _ => 0) 10 0 0 (loadWords 8 [2, 200, 100, 44])
-- Exactly half of the 16 first random words of 4 bits are odd.
#eval count (fun s => exec (w := 4) parityProgram (tape 4 s) 5 0 0 (loadWords 4 []) = some true) 16
-- The second random word is the second base-16 digit: 16 gives first word 0 (even), 17 gives 1 (odd).
#eval exec (w := 4) parityProgram (tape 4 16) 5 0 0 (loadWords 4 [])
#eval exec (w := 4) parityProgram (tape 4 17) 5 0 0 (loadWords 4 [])
-- Word lengths: ⌈4(2 + 1 + log₂ 4)⌉ = 20 and ⌈4(3 + 5 + log₂ 5)⌉ = ⌈41.29⌉ = 42.
#eval wordLength 2 1
#eval wordLength 3 5
-- Bit lengths: max 1 → 1, max 7 → 3, max 8 → 4.
#eval x0.bits
#eval (⟨fun _ => 7, 3, fun _ => by decide⟩ : Instance 2).bits
#eval (⟨fun _ => 2, 8, fun _ => by decide⟩ : Instance 2).bits

#print axioms BigOSpeedrun.SubsetSum.SolvedInTime
#print axioms bigO_49_100
#print axioms BigO.mono
#print axioms SolvedInTime.mono
#print axioms accept_correct
#print axioms reject_not_correct

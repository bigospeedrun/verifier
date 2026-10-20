import Submission.Work.BlockAccounting.Moment
set_option maxRecDepth 4000
namespace OAI.PowerSaving.BlockAccounting
open Finset
/-- 72 copies of the warped #2979 word S2979B (gcert/1w, p-lower's lowering; 408 helpers, 91 zero buffers), #401 dedicated banks, and an explicit x-exit-words pad-minimal (remapped) bank schedule. -/
def blocksS2979Bx : List (ℕ × ℕ) := [(1, 176040), (2, 50832), (3, 16704), (4, 7776), (5, 1296), (8, 5952), (16, 3584), (32, 3584), (35, 1), (36, 1), (48, 3584)]

/-- total rank of one unit (= number of unit moves it stands for): `W * m - D` -/
theorem blocksS2979Bx_rank : (blocksS2979Bx.map fun b => b.1 * b.2).sum = 10407 * 73 - 2560 := by
  norm_num [blocksS2979Bx]

/-- the same as a price: the unit list at the price list `r ↦ r` (shape of `hPid` in `RAM.engine_program_group_perRank`) -/
theorem blocksS2979Bx_tally : (blocksS2979Bx.map fun b => (b.2:ℝ) * ((b.1:ℕ):ℝ)).sum = ((10407:ℕ):ℝ) * ((73:ℕ):ℝ) - ((2560:ℕ):ℝ) := by
  norm_num [blocksS2979Bx]

theorem blocksS2979Bx_count : (blocksS2979Bx.map fun b => b.2).sum = 269354 := by
  norm_num [blocksS2979Bx]

theorem blocksS2979Bx_proper : ∀ b ∈ blocksS2979Bx, 1 ≤ b.1 ∧ b.1 < 73 := by
  decide

/-- **whole-block fact** of `blocksS2979Bx` at exponent `1 - 14611616/10^10`, fill parameter `s = 40`: the hypothesis `hnum` of `RAM.engine_program_group_list` (u = 73, W = 10407).  Relative slack of the rational certificate: 2.02e-10. -/
theorem fold_S2979Bx :
    ((2:ℝ)^40 - 1) * moment 73 (1 - 14611616/(10:ℝ)^10) blocksS2979Bx
      + ((10407:ℕ):ℝ) * (T 73 (1 - 14611616/(10:ℝ)^10) (73 - 1) 1 + T 73 (1 - 14611616/(10:ℝ)^10) 1 1)
      < (2:ℝ)^40 * ((10407:ℕ):ℝ) := by
  have hsum : moment 73 (1 - 14611616/(10:ℝ)^10) blocksS2979Bx
      = T 73 (1 - 14611616/(10:ℝ)^10) 1 176040 + (T 73 (1 - 14611616/(10:ℝ)^10) 2 50832 + (T 73 (1 - 14611616/(10:ℝ)^10) 3 16704 + (T 73 (1 - 14611616/(10:ℝ)^10) 4 7776 + (T 73 (1 - 14611616/(10:ℝ)^10) 5 1296 + (T 73 (1 - 14611616/(10:ℝ)^10) 8 5952 + (T 73 (1 - 14611616/(10:ℝ)^10) 16 3584 + (T 73 (1 - 14611616/(10:ℝ)^10) 32 3584 + (T 73 (1 - 14611616/(10:ℝ)^10) 35 1 + (T 73 (1 - 14611616/(10:ℝ)^10) 36 1 + (T 73 (1 - 14611616/(10:ℝ)^10) 48 3584 + 0)))))))))) := rfl
  have b0 : T 73 (1 - 14611616/(10:ℝ)^10) 1 176040 ≤ ((2426672236781:ℝ)/1000000000) :=
    term_le 73 1 176040 (14611616/(10:ℝ)^10) ((85809188823:ℝ)/20000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 26 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b1 : T 73 (1 - 14611616/(10:ℝ)^10) 2 50832 ≤ ((1399996979993:ℝ)/1000000000) :=
    term_le 73 2 50832 (14611616/(10:ℝ)^10) ((359731226059:ℝ)/100000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 24 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b2 : T 73 (1 - 14611616/(10:ℝ)^10) 3 16704 ≤ ((86209347081:ℝ)/125000000) :=
    term_le 73 3 16704 (14611616/(10:ℝ)^10) ((1595923576241:ℝ)/500000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 23 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b3 : T 73 (1 - 14611616/(10:ℝ)^10) 4 7776 ≤ ((427894095619:ℝ)/1000000000) :=
    term_le 73 4 7776 (14611616/(10:ℝ)^10) ((290416508003:ℝ)/100000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 22 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b4 : T 73 (1 - 14611616/(10:ℝ)^10) 5 1296 ≤ ((44557771211:ℝ)/500000000) :=
    term_le 73 5 1296 (14611616/(10:ℝ)^10) ((670255382179:ℝ)/250000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 21 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b5 : T 73 (1 - 14611616/(10:ℝ)^10) 8 5952 ≤ ((327192326619:ℝ)/500000000) :=
    term_le 73 8 5952 (14611616/(10:ℝ)^10) ((221101789947:ℝ)/100000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 20 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b6 : T 73 (1 - 14611616/(10:ℝ)^10) 16 3584 ≤ ((157455676209:ℝ)/200000000) :=
    term_le 73 16 3584 (14611616/(10:ℝ)^10) ((151787071891:ℝ)/100000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 17 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b7 : T 73 (1 - 14611616/(10:ℝ)^10) 32 3584 ≤ ((786481428713:ℝ)/500000000) :=
    term_le 73 32 3584 (14611616/(10:ℝ)^10) ((16494470767:ℝ)/20000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 14 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b8 : T 73 (1 - 14611616/(10:ℝ)^10) 35 1 ≤ ((479967319:ℝ)/1000000000) :=
    term_le 73 35 1 (14611616/(10:ℝ)^10) ((36755568983:ℝ)/50000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 14 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b9 : T 73 (1 - 14611616/(10:ℝ)^10) 36 1 ≤ ((493660351:ℝ)/1000000000) :=
    term_le 73 36 1 (14611616/(10:ℝ)^10) ((353470251347:ℝ)/500000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 13 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b10 : T 73 (1 - 14611616/(10:ℝ)^10) 48 3584 ≤ ((2358046847061:ℝ)/1000000000) :=
    term_le 73 48 3584 (14611616/(10:ℝ)^10) ((209629215121:ℝ)/500000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 11 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b11 : T 73 (1 - 14611616/(10:ℝ)^10) 72 1 ≤ ((986321249:ℝ)/1000000000) :=
    term_le 73 72 1 (14611616/(10:ℝ)^10) ((6896661067:ℝ)/500000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 6 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b12 : T 73 (1 - 14611616/(10:ℝ)^10) 1 1 ≤ ((6892389:ℝ)/500000000) :=
    term_le 73 1 1 (14611616/(10:ℝ)^10) ((85809188823:ℝ)/20000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 26 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have e1 : ((2:ℝ)^40 - 1) = 1099511627775 := by norm_num
  have e2 : (2:ℝ)^40 = 1099511627776 := by norm_num
  have e3 : ((10407:ℕ):ℝ) = 10407 := by norm_num
  have e4 : T 73 (1 - 14611616/(10:ℝ)^10) (73 - 1) 1 = T 73 (1 - 14611616/(10:ℝ)^10) 72 1 := rfl
  rw [e1, e2, e3, e4, hsum]
  linarith

end OAI.PowerSaving.BlockAccounting
#print axioms OAI.PowerSaving.BlockAccounting.fold_S2979Bx

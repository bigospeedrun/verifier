import Submission.Work.XHostT.KHist
import Submission.Work.XHostT.Data.H2979Fc.Merged1





/-! p-hostck mk_parts.py: global facts of H2979Fc: remainder histogram {0: 104417, 1: 2269, 6: 5, 7: 3, 17: 8, 19: 1, 23: 25905, 48: 16576}, residual sums {0: 3283, 1: 3283} (6 chunks of 111 kinds). -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OAI.PowerSaving.XHostT.K.DH2979Fc
open OAI.PowerSaving.XHostT.K
/-- every remainder is one of [0, 1, 6, 7, 17, 19, 23, 48]. -/
theorem rem_in : inR rt [0, 1, 6, 7, 17, 19, 23, 48] 0 NK = true :=
  inR_list rt [0, 1, 6, 7, 17, 19, 23, 48] 111 6 0 (fun j hj => by
    interval_cases j
    exacts [gin0, gin1, gin2, gin3, gin4, gin5])
theorem rem_c0 : cntR rt 0 0 NK = 104417 := by
  have h := cntR_list rt 0 111 [16576, 17144, 18360, 16349, 17336, 18652] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc0_0, gc0_1, gc0_2, gc0_3, gc0_4, gc0_5])
  rw [show ([16576, 17144, 18360, 16349, 17336, 18652] : List ℕ).sum = 104417 by decide] at h
  exact h
theorem rem_c1 : cntR rt 1 0 NK = 2269 := by
  have h := cntR_list rt 1 111 [206, 0, 928, 448, 0, 687] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc1_0, gc1_1, gc1_2, gc1_3, gc1_4, gc1_5])
  rw [show ([206, 0, 928, 448, 0, 687] : List ℕ).sum = 2269 by decide] at h
  exact h
theorem rem_c6 : cntR rt 6 0 NK = 5 := by
  have h := cntR_list rt 6 111 [0, 0, 2, 0, 0, 3] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc6_0, gc6_1, gc6_2, gc6_3, gc6_4, gc6_5])
  rw [show ([0, 0, 2, 0, 0, 3] : List ℕ).sum = 5 by decide] at h
  exact h
theorem rem_c7 : cntR rt 7 0 NK = 3 := by
  have h := cntR_list rt 7 111 [0, 0, 0, 3, 0, 0] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc7_0, gc7_1, gc7_2, gc7_3, gc7_4, gc7_5])
  rw [show ([0, 0, 0, 3, 0, 0] : List ℕ).sum = 3 by decide] at h
  exact h
theorem rem_c17 : cntR rt 17 0 NK = 8 := by
  have h := cntR_list rt 17 111 [0, 0, 8, 0, 0, 0] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc17_0, gc17_1, gc17_2, gc17_3, gc17_4, gc17_5])
  rw [show ([0, 0, 8, 0, 0, 0] : List ℕ).sum = 8 by decide] at h
  exact h
theorem rem_c19 : cntR rt 19 0 NK = 1 := by
  have h := cntR_list rt 19 111 [0, 1, 0, 0, 0, 0] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc19_0, gc19_1, gc19_2, gc19_3, gc19_4, gc19_5])
  rw [show ([0, 1, 0, 0, 0, 0] : List ℕ).sum = 1 by decide] at h
  exact h
theorem rem_c23 : cntR rt 23 0 NK = 25905 := by
  have h := cntR_list rt 23 111 [5394, 4807, 2878, 5376, 4616, 2834] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc23_0, gc23_1, gc23_2, gc23_3, gc23_4, gc23_5])
  rw [show ([5394, 4807, 2878, 5376, 4616, 2834] : List ℕ).sum = 25905 by decide] at h
  exact h
theorem rem_c48 : cntR rt 48 0 NK = 16576 := by
  have h := cntR_list rt 48 111 [2688, 2912, 2688, 2688, 2912, 2688] 0 6 rfl (fun j hj => by
    interval_cases j
    exacts [gc48_0, gc48_1, gc48_2, gc48_3, gc48_4, gc48_5])
  rw [show ([2688, 2912, 2688, 2688, 2912, 2688] : List ℕ).sum = 16576 by decide] at h
  exact h
/-- **the remainder histogram** of H2979Fc: any function of the remainders summed over all host indices. -/
theorem rem_hist {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Finset.range (224 * NK), f (remAt rt i) = (104417 : ℕ) • f 0 + (2269 : ℕ) • f 1 + (5 : ℕ) • f 6 + (3 : ℕ) • f 7 + (8 : ℕ) • f 17 + (1 : ℕ) • f 19 + (25905 : ℕ) • f 23 + (16576 : ℕ) • f 48 := by
  rw [rem_sum rt NK [0, 1, 6, 7, 17, 19, 23, 48] (by decide) rem_in f]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rem_c0, rem_c1, rem_c6, rem_c7, rem_c17, rem_c19, rem_c23, rem_c48, add_zero, add_assoc]
/-- the residual sum of provider 0. -/
theorem res_sum0 : ∑ q ∈ Finset.range R, resAt resT 0 q = 3283 := by
  rw [← resS_eq]; decide +kernel
/-- the residual sum of provider 1. -/
theorem res_sum1 : ∑ q ∈ Finset.range R, resAt resT 1 q = 3283 := by
  rw [← resS_eq]; decide +kernel
end OAI.PowerSaving.XHostT.K.DH2979Fc
#print axioms OAI.PowerSaving.XHostT.K.DH2979Fc.rem_hist
#print axioms OAI.PowerSaving.XHostT.K.DH2979Fc.res_sum0
#print axioms OAI.PowerSaving.XHostT.K.DH2979Fc.res_sum1

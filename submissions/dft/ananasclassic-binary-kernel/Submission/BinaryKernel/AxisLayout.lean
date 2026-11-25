import Submission.BinaryKernel.ComplexPlan
import Submission.BinaryKernel.Fibers
import Submission.BinaryKernel.EvenWalsh

namespace DFTSpeedrun.AxisLayout
open DFTSpeedrun.ComplexPlan OAI.Computability.NearSquareRoot.KernelPass
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM.HalfFibers
open Finset Matrix
noncomputable section

abbrev Lane (h : ℕ) := Fin h → Fin 2 → ZMod 2

def bitOrder (h : ℕ) := (Layout.std h).pair (Layout.std 2)

def flatten {h} : Lane h ≃ Bits (h*2) where
  toFun u j := u ((bitOrder h).atFin j).1 ((bitOrder h).atFin j).2
  invFun u c s := u ((bitOrder h).index (c,s))
  left_inv u := by
    funext c s
    exact congrArg (fun z : Fin h × Fin 2 => u z.1 z.2) ((bitOrder h).index.symm_apply_apply (c,s))
  right_inv u := by
    funext j
    exact congrArg u ((bitOrder h).index.apply_symm_apply j)

def bankLanes {A h} : Addr A h ≃ (Fin A → Bits (h*2)) where
  toFun u a := flatten (fun c => u c a)
  invFun d c a := flatten.symm (d a) c
  left_inv y := by funext c a; exact congrFun (flatten.symm_apply_apply (fun t => y t a)) c
  right_inv y := by funext a; exact flatten.apply_symm_apply (y a)

def shape (A h : ℕ) := ((Layout.std A).digits (bits (h*2))).comap bankLanes

def width (h : ℕ) := 2^(h*2)
def stride {A} (a : Fin A) (h : ℕ) := (width h)^a.val

def code {A h} (x : Addr A h) := (shape A h).loc x
def digit {h} (x : Lane h) := (bits (h*2)).loc (flatten x)

theorem code_sum {A h} (x : Addr A h) :
    code x = ∑ a, digit (fun c => x c a) * stride a h :=
  Layout.digits_code (Layout.std A) (bits (h*2)) (bankLanes x)

theorem digit_extract {A h} (x : Addr A h) (a : Fin A) :
    digitAt (stride a h) (width h) (code x) = digit (fun c => x c a) :=
  Layout.digits_entry (Layout.std A) (bits (h*2)) (bankLanes x) a

private theorem insert_balance (s w j d : ℕ) :
    insertAxis s w (fiberAt s w j) d + digitAt s w j*s = j+d*s := by
  conv_rhs => lhs; rw [← insert_recover s w j]
  unfold insertAxis; ring

theorem code_setAxis {A h} (x : Addr A h) (a : Fin A) (u : Lane h) :
    code (setAxis x a u) = insertAxis (stride a h) (width h)
      (fiberAt (stride a h) (width h) (code x)) (digit u) := by
  have other (b : Fin A) (hb : b ∈ univ.erase a) :
      (fun c => setAxis x a u c b) = (fun c => x c b) := by
    funext c; simp [setAxis, Function.update_of_ne (mem_erase.mp hb).1]
  have eq := Finset.sum_congr (s₁ := univ.erase a) rfl (fun b hb =>
    congrArg (fun z : Lane h => digit z * stride b h) (other b hb))
  have here : (fun c => setAxis x a u c a) = u := by funext c; simp [setAxis]
  have paid : code (setAxis x a u) + digit (fun c => x c a) * stride a h =
      code x + digit u * stride a h := by
    rw [code_sum,code_sum]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),
        ← Finset.sum_erase_add _ (fun b => digit (fun c => x c b) * stride b h) (Finset.mem_univ a)]
    simp only [here,eq]
    omega
  have plug := insert_balance (stride a h) (width h) (code x) (digit u)
  rw [digit_extract] at plug
  omega

private theorem pair_sign (x y : Fin 2 → ZMod 2) :
    (pairEntry x y : ℂ) = (∏ i : Fin 2, littleH (x i) (y i)) / 2 := by
  rcases bit_cases (x 0) with h0 | h0 <;> rcases bit_cases (x 1) with h1 | h1 <;>
    rcases bit_cases (y 0) with g0 | g0 <;> rcases bit_cases (y 1) with g1 | g1 <;>
    norm_num [Fin.prod_univ_two,pairEntry,h0,h1,g0,g1,littleH,sign]

theorem lane_entries {h} (x y : Lane h) :
    ∏ c, (pairEntry (x c) (y c) : ℂ) =
      wal (Fin (h*2)) (flatten x) (flatten y) / (2:ℂ)^h := by
  have spread := prod_spread (bitOrder h) littleH (fun i => x i.1 i.2) (fun i => y i.1 i.2)
  rw [Fintype.prod_prod_type] at spread
  change digitProd (fun _ : Fin (h*2) => littleH) (flatten x) (flatten y) = _ at spread
  simp only [pair_sign, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, wal, spread]

theorem child_normalized {A h} (a : Fin A) (x : Bank A h 1) (y : Addr A h) :
    act (Plan.child a) h x 0 y =
      WalshBridge.normalized (h*2) (fun u => x 0 (setAxis y a (flatten.symm u)))
        (flatten (fun c => y c a)) := by
  rw [child]
  unfold WalshBridge.normalized WalshBridge.walsh
  simp only [Matrix.mulVec, dotProduct, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  rw [Finset.sum_div]
  refine Fintype.sum_equiv flatten _ _ (fun u => ?_)
  rw [flatten.symm_apply_apply, lane_entries]; ring

def allOrder (A h : ℕ) := (Layout.std A).pair (bitOrder h)

def allFlatten {A h} : Addr A h ≃ Bits (A*(h*2)) where
  toFun u j := let t := (allOrder A h).atFin j; u t.2.1 t.1 t.2.2
  invFun u c a s := u ((allOrder A h).index (a,c,s))
  left_inv u := by
    funext c a s
    exact congrArg (fun z : Fin A × Fin h × Fin 2 => u z.2.1 z.1 z.2.2)
      ((allOrder A h).index.symm_apply_apply (a,c,s))
  right_inv u := by
    funext j
    exact congrArg u ((allOrder A h).index.apply_symm_apply j)

theorem code_flat {A h} (x : Addr A h) :
    (bits (A*(h*2))).loc (allFlatten x) = code x := by
  rw [code_sum]
  have sum := spread_loc (allOrder A h) (fun z => x z.2.1 z.1 z.2.2)
  rw [Fintype.sum_prod_type] at sum
  change (bits (A*(h*2))).loc (allFlatten x) = _ at sum
  rw [sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have lane := spread_loc (bitOrder h) (fun z => x z.1 a z.2)
  change digit (fun c => x c a) = _ at lane
  rw [lane, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change _ * 2^(a.val * (h*2) + (bitOrder h).loc j) =
    _ * 2^((bitOrder h).loc j) * (2^(h*2))^a.val
  rw [Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm (h*2)]; ring

theorem all_entries {A h} (y u : Addr A h) :
    ∏ c, ∏ a, (pairEntry (y c a) (u c a) : ℂ) =
       wal (Fin (A*(h*2))) (allFlatten y) (allFlatten u) / (2:ℂ)^(A*h) := by
  have eq := prod_spread (allOrder A h) littleH (fun z => y z.2.1 z.1 z.2.2)
    (fun z => u z.2.1 z.1 z.2.2)
  change wal (Fin (A*(h*2))) (allFlatten y) (allFlatten u) = _ at eq
  simp only [Fintype.prod_prod_type] at eq
  rw [eq, Finset.prod_comm]
  simp only [pair_sign, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm h A]

/-- One correct fixed template processes every row in parallel as exactly the
normalized Walsh transform under the same flattening used by child packing. -/
theorem correct_normalized {A W h} {p : Plan A W W} (ok : Correct p)
    (x : ComplexPlan.Bank A h W) (b : Fin W) (y : Addr A h) :
    act p h x b y = WalshBridge.normalized (A*(h*2))
        (fun d => x b (allFlatten.symm d)) (allFlatten y) := by
  rw [correct ok]
  unfold WalshBridge.normalized WalshBridge.walsh
  have halves : A*(h*2)/2 = A*h := by rw [← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  simp only [Matrix.mulVec, dotProduct, halves]
  rw [Finset.sum_div]
  refine Fintype.sum_equiv allFlatten _ _ (fun u => ?_)
  rw [allFlatten.symm_apply_apply,all_entries]; ring


end
end DFTSpeedrun.AxisLayout

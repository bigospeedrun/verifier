import Submission.BinaryKernel.BatchData

/-! Reassemble the normalized multidimensional Walsh transform from a fixed
number of batches. The remaining digit block has bounded width, so all its
signs and rational normalization factors are program constants. -/
namespace DFTSpeedrun.Batch
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
open OAI.Computability.NearSquareRoot.KernelPass
open AxisLayout ComplexPlan FixedRows Finset
noncomputable section

def split {A h k s : ℕ} (eqdim : A*(h*2)+s*2=k*2) :
    Addr A h × Bits (s*2) ≃ Bits (k*2) :=
  ((allFlatten.prodCongr (Equiv.refl _)).trans (catB _ _)).trans (castB eqdim)
theorem split_apply {A h k s : ℕ} (eqdim : A*(h*2)+s*2=k*2)
    (a : Addr A h) (j : Bits (s*2)) : split eqdim (a,j) = joined eqdim a j := rfl

def coeff (s : ℕ) (x y : Bits (s*2)) : ℚ :=
  (if dot x y = 0 then 1 else -1) / 2^s
theorem coeff_cast (s : ℕ) (x y : Bits (s*2)) :
    (coeff s x y : ℂ) = wal (Fin (s*2)) x y / (2:ℂ)^s := by
  rw [wal_apply]; unfold coeff sign; split_ifs <;> push_cast <;> rfl

private theorem cast_normal {n m : ℕ} (e : n=m) (v : Bits m → ℂ) (z : Bits n) :
    WalshBridge.normalized m v (castB e z) =
      WalshBridge.normalized n (fun t => v (castB e t)) z := by
  subst e; rfl

theorem normal_split (n s : ℕ) (v : Bits (n+s*2) → ℂ) (u : Bits n) (q : Bits (s*2)) :
    WalshBridge.normalized (n+s*2) v (catB _ _ (u,q)) =
      ∑ j : Bits (s*2), (coeff s q j : ℂ) *
        WalshBridge.normalized n (fun a => v (catB _ _ (a,j))) u := by
  have sep (y : Bits n × Bits (s*2)) :
      wal (Fin (n+s*2)) (catB _ _ (u,q)) (catB _ _ y) =
      wal (Fin n) u y.1 * wal (Fin (s*2)) q y.2 := by
    simp only [wal,digitProd_apply,catB,Equiv.coe_fn_mk,Fin.prod_univ_add,Fin.append_left,Fin.append_right]
  unfold WalshBridge.normalized WalshBridge.walsh
  simp only [GenMove.mulVec_apply']
  rw [← (catB n (s*2)).sum_comp (fun b => wal (Fin (n+s*2)) (catB _ _ (u,q)) b * v b),
    Fintype.sum_prod_type,Finset.sum_comm]
  simp only [sep,Finset.sum_div,Finset.mul_sum,coeff_cast,show (n+s*2)/2=n/2+s by omega,pow_add]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

def groupOf {s W : ℕ} (hw : 0<W) (q : Bits (s*2)) : Fin (groups s W) :=
  ⟨(bits _).loc q / W, by
    apply (Nat.div_lt_iff_lt_mul hw).2
    have bd := (bits _).bd q
    rw [rows_eq] at bd
    apply bd.trans_le
    unfold groups
    rw [Nat.ceilDiv_eq_add_pred_div,Nat.mul_comm]
    have hbound := Nat.mod_lt (rows s+W-1) hw
    have heq := Nat.mod_add_div (rows s+W-1) W
    omega⟩

def slotOf {s W : ℕ} (hw : 0<W) (q : Bits (s*2)) : Fin W :=
  ⟨(bits _).loc q % W, Nat.mod_lt _ hw⟩

theorem group_slot {s W : ℕ} (hw : 0<W) (q : Bits (s*2)) :
    highAt ((groupOf hw q).val*W+(slotOf hw q).val) = q := by
  apply (bits _).inj
  simp only [highAt,groupOf,slotOf,Layout.loc_atFin,Nat.div_add_mod']
  apply Nat.mod_eq_of_lt
  rw [← rows_eq]; exact (bits _).bd q

theorem result_correct {A h k s W : ℕ} (hw : 0<W) (eqdim : A*(h*2)+s*2=k*2)
    (v : Bits (k*2) → ℂ) {p : Plan A W W} (ok : Correct p) (z : Bits (k*2)) :
    WalshBridge.normalized (k*2) v z = ∑ j : Bits (s*2),
      (coeff s ((split eqdim).symm z).2 j : ℂ) *
      act p h (input eqdim v (groupOf hw j).val) (slotOf hw j) ((split eqdim).symm z).1 := by
  obtain ⟨⟨a,q⟩,rfl⟩ := (split eqdim).surjective z
  rw [Equiv.symm_apply_apply]
  rw [split_apply]
  rw [joined,cast_normal,normal_split]
  refine Finset.sum_congr rfl fun j _ => congrArg _ ?_
  rw [correct_normalized ok]
  congr 1
  funext u
  simp [input,joined,group_slot]

theorem active_div {A h k s : ℕ} (eqdim : A*(h*2)+s*2=k*2) :
    2^(k*2)/rows s = PlanCompiler.volume A h := by
  rw [←eqdim,pow_add,volume_bits,show rows s = 2^(s*2) by rw [←rows_eq,bits_len]]
  apply Nat.mul_div_cancel; positivity

theorem split_locs {A h k s : ℕ} (eqdim : A*(h*2)+s*2=k*2) (z : Bits (k*2)) :
    (bits (k*2)).loc z / PlanCompiler.volume A h =
      (bits (s*2)).loc ((split eqdim).symm z).2 ∧
    (bits (k*2)).loc z % PlanCompiler.volume A h =
      code ((split eqdim).symm z).1 := by
  obtain ⟨⟨a,q⟩,rfl⟩ := (split eqdim).surjective z
  rw [Equiv.symm_apply_apply,split_apply,joined_loc,Nat.add_comm,Nat.mul_comm (PlanCompiler.volume A h)]
  exact ⟨DigitArith.div_join ((shape A h).bd a),DigitArith.mod_join ((shape A h).bd a)⟩

universe u
theorem reassemble {ι : Type u} {A W s} {cl : Paint} {m : Bool} {B k h : ι → ℕ}
    (hw : 0 < W) (eqdim : ∀ i, A*(h i*2)+s*2=k i*2) (v : ∀ i, Bits (k i*2) → ℂ)
    (sn : Small B fun i => 2^(k i*2)) {P : Plan A W W} (ok : Correct P) :
    Can m B (p (HalfKernel.Src cl) (a (a (bundle cl)))) (bundle cl)
      (fun i => ((k i,(bits (k i*2)).tape (v i)), result (eqdim i) (v i) P))
      (fun i => (bits (k i*2)).tape (WalshBridge.normalized _ (v i)))
      (fun i => 2^(k i*2)) := by
  let srcTy := p (HalfKernel.Src cl) (a (a (bundle cl)))
  let x := fun i => ((k i,(bits (k i*2)).tape (v i)), result (eqdim i) (v i) P)
  have sl : Small B fun i => (bits (k i*2)).n := sn.mono fun i => (bits_len _).le
  have len : Knows m B srcTy x (fun i => (bits (k i*2)).n) := Can.len Can.first.snd sl
  have wide : Knows m B srcTy x (fun i => PlanCompiler.volume A (h i)) :=
    ((len.cy (fun i => bits_len (k i*2))).dvdW (Can.wc (rows s)) sn).cy fun i => active_div (eqdim i)
  refine (Can.layout (L:=fun i => bits (k i*2)) (P:=fun _ => 0) len ?_ sl).mono fun i => by simp [bits_len]
  let J := Σ i, Bits (k i*2)
  let srcJ := fun d : J => (x d.1,(bits _).loc d.2)
  let addr := fun d : J => (bits _).loc d.2
  let qry := fun d : J => (split (eqdim d.1)).symm d.2
  have pointer : Knows m (fun d : J => B d.1) (p srcTy w) srcJ addr := Can.second
  have sm := Small.loc (L:=fun d : J => bits (k d.1*2)) (x:=fun d => d.2) (sl.reindex Sigma.fst)
  have size : Knows m (fun d : J => B d.1) (p srcTy w) srcJ (fun d => PlanCompiler.volume A (h d.1)) :=
    Can.first.then_do (wide.reindex (fun d : J => d.1))
  have qhi := (pointer.dvdW size sm).cy fun d => (split_locs (eqdim d.1) d.2).1
  have qlo := (pointer.modW size sm).cy fun d => (split_locs (eqdim d.1) d.2).2
  apply Can.cases_code (bits (s*2)) (q:=fun d : J => (qry d).2) qhi
  intro q
  let S := {d : J // (qry d).2=q}
  have lo := qlo.reindex (Subtype.val (p:=fun d : J => (qry d).2=q))
  have allG : Has m (fun d : S => B d.val.1) (p srcTy w) (a (a (bundle cl)))
      (fun d => srcJ d.val) (fun d => result (eqdim d.val.1) (v d.val.1) P) := by
    exact (Can.first (s:=p (HalfKernel.Src cl) (a (a (bundle cl)))) (t:=w)
      (v:=fun d : S => srcJ d.val)).snd
  have accum := Can.sum_cconst (m:=m) (cl:=cl) (B:=fun d : S => B d.val.1)
    (s:=p srcTy w) (x:=fun d : S => srcJ d.val) (W:=fun _ => 0)
    (v:=fun j (d : S) => (coeff s q j : ℂ) * act P (h d.val.1)
      (input (eqdim d.val.1) (v d.val.1) (groupOf hw j).val) (slotOf hw j) (qry d.val).1)
    (fun j : Bits (s*2) => (Can.rat (coeff s q j)).mul <|
      Can.fetch (t:=c cl) (L:=fun d : S => shape A (h d.val.1)) (i:=fun d => (qry d.val).1)
        (v:=fun d => act P (h d.val.1) (input (eqdim d.val.1) (v d.val.1) (groupOf hw j).val) (slotOf hw j))
        (FixedRows.row (t:=bundle cl) (V:=fun d : S => fun b : Fin W =>
            (shape A (h d.val.1)).tape (act P (h d.val.1) (input (eqdim d.val.1) (v d.val.1) (groupOf hw j).val) b))
          (FixedRows.row (t:=a (bundle cl)) (V:=fun d : S => fun g : Fin (groups s W) =>
            bankTape (shape A (h d.val.1)) (act P (h d.val.1) (input (eqdim d.val.1) (v d.val.1) g.val)))
            allG (groupOf hw j)) (slotOf hw j)) lo)
  refine accum.cy fun d => ?_
  rw [result_correct hw (eqdim d.val.1) (v d.val.1) ok d.val.2]
  simp only [←d.property,qry]

end
end DFTSpeedrun.Batch

import Submission.BinaryKernel.FixedRows

namespace OAI.PowerSaving.FixedRows
open RAM RAM.Ty
noncomputable section
universe u

/-- Collect a fixed family of calls with exact combined oracle time. The
family size only contributes a constant to the non-oracle work. -/
theorem collect {ι : Type u} {m : Bool} {port : Port} {b : Bank port ι}
    {s t : Ty} {x : ι → T s} {W Z : ι → ℕ} {N : ℕ}
    (V : Fin N → ι → T t) (each : ∀ j, Able m b s t x (V j) W Z) :
    Able m b s (a t) x (fun i => fixed fun j => V j i) W (fun i => N * Z i) := by
  induction N with
  | zero =>
    exact (Able.of_can (b:=b) (assemble (W:=W) fun j : Fin 0 => Fin.elim0 j)).mono
      (fun _ => le_rfl) (fun _ => Nat.zero_le _)
  | succ n ih =>
    let tail := fun (j : Fin n) => V j.succ
    have tailRun := ih tail (fun j => each j.succ)
    let cached := fun i => (V 0 i,fixed fun j => tail j i)
    have join : Has m b.B (p t (a t)) (a t) cached (fun i => fixed fun j => V j i) := by
      apply assemble
      intro j
      refine Fin.cases (motive := fun j => Has m b.B (p t (a t)) t cached (fun i => V j i)) ?_ ?_ j
      · exact Can.first
      · intro a; exact row (V:=fun i j => tail j i) Can.second a
    refine (((each 0).fork tailRun).comp (Able.of_can join)).weaken ?_ ?_
    · exact ⟨2,fun i => by simp; omega⟩
    · intro i; simp [Nat.succ_mul, Nat.add_comm]

end
end OAI.PowerSaving.FixedRows
#print axioms OAI.PowerSaving.FixedRows.collect

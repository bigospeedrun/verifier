import challenges.«other-snaky».Statement

open OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy
namespace BigOSpeedrun.Snaky

theorem not_bound_zero : ¬ Bound 0 := by
  rintro ⟨σ, _, hσ⟩
  have hw := (hσ (fun _ => (0, 0)) (by intro k hk; exact (Nat.not_lt_zero _ hk).elim)).1
  rcases hw with ⟨r, t, ht⟩
  have hm := ht (Finset.mem_image_of_mem (placement r t)
    (show (0, 0) ∈ snaky by simp [snaky]))
  simpa [playState] using hm

example : snaky.card = 6 := by decide

-- Baseline adapter checks statement shape only. Its premise is explicit:
-- the upstream challenge file contains sorry and is never imported.
theorem baseline_adapter
    (h : ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 21 β ∅ ∅ →
        HasSnaky (playState σ 21 β ∅ ∅ 21).1 ∧
        (playState σ 21 β ∅ ∅ 21).1.card = 21 ∧
        Disjoint (playState σ 21 β ∅ ∅ 21).1 (playState σ 21 β ∅ ∅ 20).2 ∧
        ∀ k, k < 21 →
          Disjoint (playState σ 21 β ∅ ∅ k).1 (playState σ 21 β ∅ ∅ k).2 ∧
          (playState σ 21 β ∅ ∅ k).2.card = k) : Bound 21 := h

end BigOSpeedrun.Snaky
#print axioms BigOSpeedrun.Snaky.not_bound_zero
#print axioms BigOSpeedrun.Snaky.baseline_adapter

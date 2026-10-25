import challenges.«other-snaky».Model

/-! A proposed target, not a proof of a Snaky move bound.
New parameterization by fluorine with Codex; Apache-2.0.
The entire conclusion of OpenAI's 21-move template is retained. -/
namespace BigOSpeedrun.Snaky
open OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy

/-- Maker forces a Snaky within `n` own claims, winning claim included.
Smaller natural bounds are better; no finite board envelope is imposed. -/
def Bound (n : ℕ) : Prop :=
  ∃ σ : Policy Cell,
    (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
    ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ n β ∅ ∅ →
      HasSnaky (playState σ n β ∅ ∅ n).1 ∧
      (playState σ n β ∅ ∅ n).1.card = n ∧
      Disjoint (playState σ n β ∅ ∅ n).1 (playState σ n β ∅ ∅ (n - 1)).2 ∧
      ∀ k, k < n →
        Disjoint (playState σ n β ∅ ∅ k).1 (playState σ n β ∅ ∅ k).2 ∧
        (playState σ n β ∅ ∅ k).2.card = k

end BigOSpeedrun.Snaky

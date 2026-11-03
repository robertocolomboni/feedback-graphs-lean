module

public import Tournament.Model.AdaptiveEW
public import Tournament.Model.BlockAccounting
public import Tournament.Upper.BlockPolicy

@[expose] public section

namespace Tournament.Model

open scoped BigOperators Classical
open Upper

noncomputable section

variable {ι : Type*} [Fintype ι]

structure FeedbackEW (ι : Type*) [Fintype ι] (m : ℕ) where
  rate : ℝ
  policy : ProbabilityVector ι → RestartComparisonPolicy ι m
  output : ProbabilityVector ι → (j : Fin (m+1)) → (offset : ℕ) →
    (ns : List ℕ) → BlockTranscript ι ns → ι → ℝ

namespace FeedbackEW

variable [Nonempty ι] {m : ℕ}

def algorithm (P : FeedbackEW ι m) (F : ι → ι → Prop) (n : ℕ → ℕ)
    (loss : ℕ → ι → ℝ) : AdaptiveEW (fun b ↦ DyadicBlockOutcome ι m (n b)) ι where
  rate := P.rate
  output b π y := P.output π y.1 (prefixHorizon (fun b ↦ n b+1) b) (Restarts.parts (n b) y.2.1)
    (recordBlockComparisons F loss (prefixHorizon (fun b ↦ n b+1) b) (Restarts.parts (n b) y.2.1) y.2.2)
  row b π := (P.policy π).law F loss (prefixHorizon (fun b ↦ n b+1) b) (n b)

end FeedbackEW
end
end Tournament.Model

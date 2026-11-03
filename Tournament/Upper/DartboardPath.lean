module

public import Tournament.Upper.ShrinkingDartboard
public import Tournament.Probability.FinitePath

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def weights (η : ℝ) (g : ℕ → ι → ℝ) (n : ℕ) : ProbabilityVector ι :=
  ExponentialWeights.trajectory ExponentialWeights.uniform η g n

end
end Tournament.Upper.ShrinkingDartboard

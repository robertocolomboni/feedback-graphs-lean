module

public import Tournament.Upper.ExplorationProcess
public import Tournament.Probability.FiniteFreshDraw

@[expose] public section

namespace Tournament.Upper.Exploration

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem fresh_exploration_conditional (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (n T : ℕ) (h : n+1≤T) :
    HasCondDistrib (fun x ↦ (FiniteProcess.past (n+1) T h x).2.2)
      (fun x ↦ ((FiniteProcess.past (n+1) T h x).1,(FiniteProcess.past (n+1) T h x).2.1))
      (Kernel.const (History D n × ι) (law D κ hκ hκ1).toMeasure)
      (execution E D κ hκ hκ1 η hη loss hloss T).toMeasure :=
  FiniteProcess.product_fresh_hasCondDistrib (latentRow E D κ hκ η hη loss hloss) (law D κ hκ hκ1) n T h

end
end Tournament.Upper.Exploration

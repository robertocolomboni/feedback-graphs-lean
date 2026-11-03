module

public import Tournament.Correspondence.FiniteLoss
public import Tournament.Upper.SteeringMinimax
public import Tournament.Computation.AssignmentExactStrategy

@[expose] public section

namespace Tournament.Correspondence

open Upper Model Model.MeasurableGame
open scoped Classical

noncomputable section

theorem tournament_upper_finite {K : ℕ} [Nonempty (Fin K)]
    (E : Fin K → Fin K → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1 ≤ T) (default : Fin K)
    (loss : Fin T → Fin K → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (rounded : Bool := false) :
    (tournamentPrivateStrategy E hE T default rounded).regret T E
        (finiteLossExtension loss) ≤
      (2:ℝ)^40 * min (T:ℝ) (Tuning.performanceScale K T) ∧
    (tournamentPrivateStrategy E hE T default rounded).expectedSwitches T E
        (finiteLossExtension loss) ≤
      (2:ℝ)^40 * min (T:ℝ) (Tuning.performanceScale K T) := by
  simpa only [Fintype.card_fin] using tournamentPrivateStrategy_bound E hE T hT default
    (finiteLossExtension loss) (finiteLossExtension_bounded loss hloss) rounded

theorem effective_tournament_upper_finite {K : ℕ} [Nonempty (Fin K)]
    (E : Fin K → Fin K → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1 ≤ T) (default : Fin K)
    (loss : Fin T → Fin K → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) :
    (Computation.AssignmentExactStrategy.strategy E hE T default).regret T E
        (finiteLossExtension loss) ≤
      (2:ℝ)^40 * min (T:ℝ) (Tuning.performanceScale K T) ∧
    (Computation.AssignmentExactStrategy.strategy E hE T default).expectedSwitches T E
        (finiteLossExtension loss) ≤
      (2:ℝ)^40 * min (T:ℝ) (Tuning.performanceScale K T) := by
  simpa only [Fintype.card_fin] using
    Computation.AssignmentExactStrategy.strategy_bound E hE T hT default
      (finiteLossExtension loss) (finiteLossExtension_bounded loss hloss)

end
end Tournament.Correspondence

module

public import Tournament.Model.FeedbackEW
public import Tournament.Upper.FixedRateExecution

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess Model ExponentialWeights BlockParameters

noncomputable section
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem decoder_exists (A : SteeringParameters ι) (π : ProbabilityVector ι) :
    ∃ output : (j : Fin (A.m+1)) → (offset : ℕ) → (ns : List ℕ) → BlockTranscript ι ns → ι → ℝ,
      ∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) offset n
        (y : DyadicBlockOutcome ι A.m n),
        output y.1 offset (Restarts.parts n y.2.1)
          (recordBlockComparisons A.tournament loss offset (Restarts.parts n y.2.1) y.2.2)=
            truncateEstimate (learningRate (Fintype.card ι) A.T A.m)
              (dyadicBlockCorrectedEstimate (A.holding π) A.m (A.rules π) (A.estimator π)
                loss (threshold (Fintype.card ι) A.T) offset n y) := by
  have hobs : ScoreRule.EstimatorObservable A.tournament (A.estimator π) := (A.preparation π).observable
  exact dyadicTruncatedEstimate_observable (A.holding π) A.m (A.rules π) (A.estimator π)
    hobs (threshold (Fintype.card ι) A.T) (learningRate (Fintype.card ι) A.T A.m)

def feedbackPolicy (A : SteeringParameters ι) : FeedbackEW ι A.m where
  rate := learningRate (Fintype.card ι) A.T A.m
  policy π := dyadicComparisonPolicy (A.holding π) A.m (A.rules π) (threshold (Fintype.card ι) A.T)
  output π := (A.decoder_exists π).choose

theorem feedback_algorithm_eq (A : SteeringParameters ι) (n : ℕ → ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) :
    A.feedbackPolicy.algorithm A.tournament n loss=A.algorithm n loss hloss := by
  have hrate : (A.feedbackPolicy.algorithm A.tournament n loss).rate=
      (A.algorithm n loss hloss).rate := rfl
  have houtput : (A.feedbackPolicy.algorithm A.tournament n loss).output=
      (A.algorithm n loss hloss).output := by
    funext b π y
    exact (A.decoder_exists π).choose_spec loss hloss (prefixHorizon (fun b ↦ n b+1) b) (n b) y
  have hrow : (A.feedbackPolicy.algorithm A.tournament n loss).row=
      (A.algorithm n loss hloss).row := by
    funext b π
    apply ProbabilityVector.ext_weights
    intro y
    exact dyadicComparisonPolicy_law (A.holding π) A.m (A.rules π)
      (threshold (Fintype.card ι) A.T) (threshold_ge_one A.card_ge_two A.time_ge_two)
      loss hloss (prefixHorizon (fun b ↦ n b+1) b) (n b) y
  cases hP : A.feedbackPolicy.algorithm A.tournament n loss with
  | mk rate output row =>
    cases hA : A.algorithm n loss hloss with
    | mk rate' output' row' =>
      have hr : rate=rate' := by simpa only [hP,hA] using hrate
      have ho : output=output' := by simpa only [hP,hA] using houtput
      have hk : row=row' := by simpa only [hP,hA] using hrow
      subst rate'
      subst output'
      subst row'
      rfl

theorem feedback_fixed_rate (A : SteeringParameters ι) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (default : ι)
    (hκ : 1/(A.T:ℝ)≤DyadicRate.base A.m) :
    let P := A.feedbackPolicy.algorithm A.tournament A.schedule loss
    (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x)
      ∂(P.execution A.blockCount).toMeasure)≤
        (2:ℝ)^25*threshold (Fintype.card ι) A.T*(A.m:ℝ)*logScale (Fintype.card ι) A.T*
          Real.log (Fintype.card ι:ℝ)/DyadicRate.base A.m+14*meanRate A.m*(A.T:ℝ)+3 ∧
      (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ)
        ∂(P.execution A.blockCount).toMeasure)≤10*meanRate A.m*(A.T:ℝ)+1 := by
  dsimp only
  rw [feedback_algorithm_eq A A.schedule loss hloss]
  exact A.fixed_rate_execution loss hloss default hκ

end
end Tournament.Upper.SteeringParameters

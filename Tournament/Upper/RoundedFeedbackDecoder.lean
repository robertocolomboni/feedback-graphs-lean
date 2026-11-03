module

public import Tournament.Upper.BlockMeasurable
public import Tournament.Upper.SteeringFeedbackPolicy

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open MeasureTheory Model BlockParameters
open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def roundedAssignment (S : SteeringParameters ι) (π : ProbabilityVector ι) :
    ComparisonAssignment S.tournament (Rounding.anchor (S.anchor π) S.T (by have := S.time_ge_two; omega)) :=
  optimizedAssignment S.tournament S.isTournament _
    (Rounding.anchor_pos (S.anchor π) S.card_ge_two S.time_ge_two (S.anchor_floor π))

def roundedDecoder (S : SteeringParameters ι) (π : ProbabilityVector ι) : ι → (ι → ℝ) → ι → ℝ :=
  (S.roundedAssignment π).estimatorDecoder (S.anchor π) (S.holding π).sampling

theorem estimator_eq_roundedAssignment (S : SteeringParameters ι) (hRound : S.rounded=true)
    (π : ProbabilityVector ι) :
    S.estimator π=(S.roundedAssignment π).estimator (S.anchor π) (S.holding π).sampling := by
  rcases S with ⟨F,hF,T,m,hK,hT,hm,rounded⟩
  change rounded=true at hRound
  subst rounded
  rfl

theorem roundedDecoder_correct (S : SteeringParameters ι) (hRound : S.rounded=true)
    (π : ProbabilityVector ι) (loss : ι → ℝ) (s k : ι) :
    applyEstimator (S.estimator π) s loss k=
      S.roundedDecoder π s (comparisonObservation S.tournament s loss) k := by
  rw [estimator_eq_roundedAssignment S hRound π]
  exact (ComparisonAssignment.estimatorDecoder_observation _ _ _ _ _ _).symm

def roundedOutput (S : SteeringParameters ι) (π : ProbabilityVector ι)
    (j : Fin (S.m+1)) (offset : ℕ) (ns : List ℕ) (log : BlockTranscript ι ns) : ι → ℝ :=
  truncateEstimate (learningRate (Fintype.card ι) S.T S.m)
    (blockObservedEstimate (S.rules π j) (S.roundedDecoder π) (threshold (Fintype.card ι) S.T) offset ns log)

theorem roundedOutput_record (S : SteeringParameters ι) (hRound : S.rounded=true)
    (π : ProbabilityVector ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) (offset n : ℕ)
    (y : DyadicBlockOutcome ι S.m n) :
    S.roundedOutput π y.1 offset (Restarts.parts n y.2.1)
      (recordBlockComparisons S.tournament loss offset (Restarts.parts n y.2.1) y.2.2)=
        truncateEstimate (learningRate (Fintype.card ι) S.T S.m)
          (dyadicBlockCorrectedEstimate (S.holding π) S.m (S.rules π) (S.estimator π)
            loss (threshold (Fintype.card ι) S.T) offset n y) := by
  have hRaw : blockObservedEstimate (S.rules π y.1) (S.roundedDecoder π)
        (threshold (Fintype.card ι) S.T) offset (Restarts.parts n y.2.1)
        (recordBlockComparisons S.tournament loss offset (Restarts.parts n y.2.1) y.2.2)=
      dyadicBlockCorrectedEstimate (S.holding π) S.m (S.rules π) (S.estimator π)
        loss (threshold (Fintype.card ι) S.T) offset n y := by
    funext k
    exact blockObservedEstimate_record (S.rules π y.1) (S.estimator π) (S.roundedDecoder π)
      (fun f _ s i ↦ roundedDecoder_correct S hRound π f s i) (threshold (Fintype.card ι) S.T)
      loss hLoss (Restarts.parts n y.2.1) offset y.2.2 k
  unfold roundedOutput
  rw [hRaw]

def roundedFeedbackPolicy (S : SteeringParameters ι) : FeedbackEW ι S.m where
  rate := learningRate (Fintype.card ι) S.T S.m
  policy π := dyadicComparisonPolicy (S.holding π) S.m (S.rules π) (threshold (Fintype.card ι) S.T)
  output := S.roundedOutput

theorem roundedFeedbackPolicy_algorithm_eq (S : SteeringParameters ι) (hRound : S.rounded=true)
    (n : ℕ → ℕ) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    S.roundedFeedbackPolicy.algorithm S.tournament n loss=S.algorithm n loss hLoss := by
  unfold FeedbackEW.algorithm roundedFeedbackPolicy algorithm
  congr 1
  · funext b π y
    exact roundedOutput_record S hRound π loss hLoss _ _ y
  · funext b π
    apply ProbabilityVector.ext_weights
    intro y
    exact dyadicComparisonPolicy_law (S.holding π) S.m (S.rules π) (threshold (Fintype.card ι) S.T)
      (threshold_ge_one S.card_ge_two S.time_ge_two) loss hLoss _ _ y

theorem roundedFeedbackPolicy_original_eq (S : SteeringParameters ι) (hRound : S.rounded=true)
    (n : ℕ → ℕ) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    S.roundedFeedbackPolicy.algorithm S.tournament n loss=S.feedbackPolicy.algorithm S.tournament n loss :=
  (roundedFeedbackPolicy_algorithm_eq S hRound n loss hLoss).trans (S.feedback_algorithm_eq n loss hLoss).symm

variable {A : Type*} [MeasurableSpace A] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem roundedDecoder_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) :
    EstimatorDecoderMeasurable (fun a ↦ S.roundedDecoder (p a)) := by
  have hC (s i r : ι) : Measurable (fun a ↦ (S.roundedAssignment (p a)).matrix s i r) :=
    Rounding.optimized_matrix_measurable S.tournament S.isTournament (fun a ↦ S.anchor (p a))
      (anchor_weight_measurable S p hp) S.T (by have := S.time_ge_two; omega)
      (fun a ↦ Rounding.anchor_pos (S.anchor (p a)) S.card_ge_two S.time_ge_two (S.anchor_floor (p a))) s i r
  intro s hs obs hObs k
  apply Probability.measurable_countable_parameter (fun i a ↦ S.roundedDecoder (p a) i (obs a) k) _ s hs
  intro i
  exact ComparisonAssignment.estimatorDecoder_measurable _ hC _ _ (anchor_weight_measurable S p hp)
    (rounded_holding_sampling_measurable S hRound p hp) obs hObs i k

theorem roundedOutput_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (j : Fin (S.m+1))
    (offset : ℕ) (ns : List ℕ) (log : A → BlockTranscript ι ns) (hLog : Measurable log) :
    Measurable (fun a ↦ S.roundedOutput (p a) j offset ns (log a)) :=
  truncated_blockOutput_measurable (fun a ↦ S.rules (p a) j) (rounded_rules_decoder_measurable S hRound p hp j)
    (fun a ↦ S.roundedDecoder (p a)) (roundedDecoder_measurable S hRound p hp)
    (threshold (Fintype.card ι) S.T) (learningRate (Fintype.card ι) S.T S.m) ns offset log hLog

end
end Tournament.Upper.SteeringParameters

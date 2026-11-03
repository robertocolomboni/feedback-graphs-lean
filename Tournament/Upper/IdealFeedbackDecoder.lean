module

public import Tournament.Upper.BlockMeasurable
public import Tournament.Upper.IdealPreparedMeasurable
public import Tournament.Upper.SteeringFeedbackPolicy

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open MeasureTheory Model BlockParameters
open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def idealDecoder (S : SteeringParameters ι) (π : ProbabilityVector ι) : ι → (ι → ℝ) → ι → ℝ :=
  (S.idealAssignment π).estimatorDecoder (S.anchor π) (S.holding π).sampling

theorem estimator_eq_idealAssignment (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (π : ProbabilityVector ι) :
    S.estimator π=(S.idealAssignment π).estimator (S.anchor π) (S.holding π).sampling := by
  rcases S with ⟨F,hF,T,m,hK,hT,hm,rounded⟩
  change rounded=false at hIdeal
  subst rounded
  rfl

theorem idealDecoder_correct (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (π : ProbabilityVector ι) (loss : ι → ℝ) (s k : ι) :
    applyEstimator (S.estimator π) s loss k=
      S.idealDecoder π s (comparisonObservation S.tournament s loss) k := by
  rw [estimator_eq_idealAssignment S hIdeal π]
  exact (ComparisonAssignment.estimatorDecoder_observation _ _ _ _ _ _).symm

def idealOutput (S : SteeringParameters ι) (π : ProbabilityVector ι)
    (j : Fin (S.m+1)) (offset : ℕ) (ns : List ℕ) (log : BlockTranscript ι ns) : ι → ℝ :=
  truncateEstimate (learningRate (Fintype.card ι) S.T S.m)
    (blockObservedEstimate (S.rules π j) (S.idealDecoder π) (threshold (Fintype.card ι) S.T) offset ns log)

theorem idealOutput_record (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (π : ProbabilityVector ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) (offset n : ℕ)
    (y : DyadicBlockOutcome ι S.m n) :
    S.idealOutput π y.1 offset (Restarts.parts n y.2.1)
      (recordBlockComparisons S.tournament loss offset (Restarts.parts n y.2.1) y.2.2)=
        truncateEstimate (learningRate (Fintype.card ι) S.T S.m)
          (dyadicBlockCorrectedEstimate (S.holding π) S.m (S.rules π) (S.estimator π)
            loss (threshold (Fintype.card ι) S.T) offset n y) := by
  have hRaw : blockObservedEstimate (S.rules π y.1) (S.idealDecoder π)
        (threshold (Fintype.card ι) S.T) offset (Restarts.parts n y.2.1)
        (recordBlockComparisons S.tournament loss offset (Restarts.parts n y.2.1) y.2.2)=
      dyadicBlockCorrectedEstimate (S.holding π) S.m (S.rules π) (S.estimator π)
        loss (threshold (Fintype.card ι) S.T) offset n y := by
    funext k
    exact blockObservedEstimate_record (S.rules π y.1) (S.estimator π) (S.idealDecoder π)
      (fun f _ s i ↦ idealDecoder_correct S hIdeal π f s i) (threshold (Fintype.card ι) S.T)
      loss hLoss (Restarts.parts n y.2.1) offset y.2.2 k
  unfold idealOutput
  rw [hRaw]

def idealFeedbackPolicy (S : SteeringParameters ι) : FeedbackEW ι S.m where
  rate := learningRate (Fintype.card ι) S.T S.m
  policy π := dyadicComparisonPolicy (S.holding π) S.m (S.rules π) (threshold (Fintype.card ι) S.T)
  output := S.idealOutput

theorem idealFeedbackPolicy_algorithm_eq (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (n : ℕ → ℕ) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    S.idealFeedbackPolicy.algorithm S.tournament n loss=S.algorithm n loss hLoss := by
  unfold FeedbackEW.algorithm idealFeedbackPolicy algorithm
  congr 1
  · funext b π y
    exact idealOutput_record S hIdeal π loss hLoss _ _ y
  · funext b π
    apply ProbabilityVector.ext_weights
    intro y
    exact dyadicComparisonPolicy_law (S.holding π) S.m (S.rules π) (threshold (Fintype.card ι) S.T)
      (threshold_ge_one S.card_ge_two S.time_ge_two) loss hLoss _ _ y

theorem idealFeedbackPolicy_original_eq (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (n : ℕ → ℕ) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    S.idealFeedbackPolicy.algorithm S.tournament n loss=S.feedbackPolicy.algorithm S.tournament n loss :=
  (idealFeedbackPolicy_algorithm_eq S hIdeal n loss hLoss).trans (S.feedback_algorithm_eq n loss hLoss).symm

theorem idealFeedbackPolicy_fixed_rate (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) (default : ι)
    (hκ : 1 / (S.T : ℝ) ≤ DyadicRate.base S.m) :
    let P := S.idealFeedbackPolicy.algorithm S.tournament S.schedule loss
    (∫ x, pathRegret S.T loss (S.actions S.schedule default S.blockCount x)
      ∂(P.execution S.blockCount).toMeasure) ≤
        (2 : ℝ)^25 * threshold (Fintype.card ι) S.T * (S.m : ℝ) * logScale (Fintype.card ι) S.T *
          Real.log (Fintype.card ι : ℝ) / DyadicRate.base S.m + 14 * meanRate S.m * (S.T : ℝ) + 3 ∧
      (∫ x, (switchCount S.T (S.actions S.schedule default S.blockCount x) : ℝ)
        ∂(P.execution S.blockCount).toMeasure) ≤ 10 * meanRate S.m * (S.T : ℝ) + 1 := by
  dsimp only
  rw [idealFeedbackPolicy_algorithm_eq S hIdeal S.schedule loss hLoss]
  exact S.fixed_rate_execution loss hLoss default hκ

variable {A : Type*} [MeasurableSpace A] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem idealDecoder_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) :
    EstimatorDecoderMeasurable (fun a ↦ S.idealDecoder (p a)) := by
  have hC (s i r : ι) : Measurable (fun a ↦ (S.idealAssignment (p a)).matrix s i r) :=
    optimizedAssignment_matrix_measurable S.tournament S.isTournament (fun a ↦ S.anchor (p a))
      (anchor_weight_measurable S p hp) (fun a ↦ S.anchor_pos (p a)) s i r
  intro s hs obs hObs k
  apply Probability.measurable_countable_parameter (fun i a ↦ S.idealDecoder (p a) i (obs a) k) _ s hs
  intro i
  exact ComparisonAssignment.estimatorDecoder_measurable _ hC _ _ (anchor_weight_measurable S p hp)
    (ideal_holding_sampling_measurable S hIdeal p hp) obs hObs i k

theorem idealOutput_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (j : Fin (S.m+1))
    (offset : ℕ) (ns : List ℕ) (log : A → BlockTranscript ι ns) (hLog : Measurable log) :
    Measurable (fun a ↦ S.idealOutput (p a) j offset ns (log a)) :=
  truncated_blockOutput_measurable (fun a ↦ S.rules (p a) j) (ideal_rules_decoder_measurable S hIdeal p hp j)
    (fun a ↦ S.idealDecoder (p a)) (idealDecoder_measurable S hIdeal p hp)
    (threshold (Fintype.card ι) S.T) (learningRate (Fintype.card ι) S.T S.m) ns offset log hLog

end
end Tournament.Upper.SteeringParameters

module

public import Tournament.Upper.IdealFeedbackDecoder
public import Tournament.Upper.FeedbackLawMeasurable

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open MeasureTheory Model BlockParameters
open scoped Classical BigOperators

noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSpace A]
variable [Nonempty ι] [DiscreteMeasurableSpace ι]

theorem ideal_chunkLaw_weight_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (j : Fin (S.m+1)) (M : ℝ) (offset n : ℕ) (hist : FinitePath.History ι n) :
    Measurable (fun a ↦ (((S.rules (p a) j).shift offset).comparisonPolicy M).law
      S.tournament (fun t ↦ loss a (offset+t)) n hist) := by
  induction n with
  | zero => exact ideal_holding_sampling_measurable S hIdeal p hp hist
  | succ n ih =>
    rcases hist with ⟨hist, i⟩
    change Measurable (fun a ↦
      (((S.rules (p a) j).shift offset).comparisonPolicy M).law
        S.tournament (fun t ↦ loss a (offset+t)) n hist *
      ((S.rules (p a) j).shift offset).observedRow M n
        (recordComparisons S.tournament (fun t ↦ loss a (offset+t)) n hist)
        (comparisonObservation S.tournament (FinitePath.lastState n hist) (loss a (offset+n))) i)
    apply (ih hist).mul
    apply ScoreRule.observedRow_weight_measurable
      (fun a ↦ (S.rules (p a) j).shift offset)
      (decoderMeasurable_shift (fun a ↦ S.rules (p a) j)
        (ideal_rules_decoder_measurable S hIdeal p hp j) offset)
      (ideal_holding_kernel_measurable S hIdeal p hp (DyadicRate.rate S.m j)
        (DyadicRate.rate_pos S.m j))
      (ideal_holding_sampling_measurable S hIdeal p hp) M n
    · exact recordComparisons_family_measurable S.tournament
        (fun a t ↦ loss a (offset+t)) (fun t k ↦ hLoss (offset+t) k) n hist
    · intro k
      exact (measurable_pi_apply k).comp
        (comparisonObservation_family_measurable S.tournament loss hLoss (offset+n)
          (FinitePath.lastState n hist))

theorem ideal_resetLaw_weight_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (j : Fin (S.m+1)) (M : ℝ) (ns : List ℕ) (offset : ℕ) (hist : BlockOutcome ι ns) :
    Measurable (fun a ↦ (resetComparisonPolicy (S.rules (p a) j) M).law
      S.tournament (loss a) offset ns hist) := by
  induction ns generalizing offset with
  | nil => exact measurable_const
  | cons n ns ih =>
    rcases hist with ⟨hist, rest⟩
    change Measurable (fun a ↦
      (((S.rules (p a) j).shift offset).comparisonPolicy M).law
        S.tournament (fun t ↦ loss a (offset+t)) n hist *
      (resetComparisonPolicy (S.rules (p a) j) M).law
        S.tournament (loss a) (offset+(n+1)) ns rest)
    exact (ideal_chunkLaw_weight_measurable S hIdeal p hp loss hLoss j M offset n hist).mul
      (ih (offset+(n+1)) rest)

theorem ideal_dyadicLaw_weight_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (M : ℝ) (offset n : ℕ) (y : DyadicBlockOutcome ι S.m n) :
    Measurable (fun a ↦ (dyadicComparisonPolicy (S.holding (p a)) S.m (S.rules (p a)) M).law
      S.tournament (loss a) offset n y) := by
  rcases y with ⟨j, coins, hist⟩
  change Measurable (fun a ↦ DyadicRate.law S.m j *
    (Restarts.law (DyadicRate.rate S.m j) (le_of_lt (DyadicRate.rate_pos S.m j))
      (DyadicRate.rate_le_one S.m j) n coins *
    (resetComparisonPolicy (S.rules (p a) j) M).law
      S.tournament (loss a) offset (Restarts.parts n coins) hist))
  exact measurable_const.mul (measurable_const.mul
    (ideal_resetLaw_weight_measurable S hIdeal p hp loss hLoss j M _ offset hist))

theorem ideal_algorithm_output_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (b : ℕ) (y : DyadicBlockOutcome ι S.m (n b)) :
    Measurable (fun a ↦ (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).output b (p a) y) := by
  exact idealOutput_measurable S hIdeal p hp y.1 _ _
    (fun a ↦ recordBlockComparisons S.tournament (loss a)
      (prefixHorizon (fun b ↦ n b+1) b) (Restarts.parts (n b) y.2.1) y.2.2)
    (recordBlockComparisons_family_measurable S.tournament loss hLoss _ _ y.2.2)

theorem ideal_distribution_weight_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (b : ℕ)
    (hist : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι S.m (n b)) b) (i : ι) :
    Measurable (fun a ↦ (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).distribution b hist i) := by
  induction b generalizing i with
  | zero => exact measurable_const
  | succ b ih =>
    rcases hist with ⟨hist, y⟩
    exact ShrinkingDartboard.update_weight_measurable
      (fun a ↦ (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).distribution b hist)
      (fun k ↦ ih hist k)
      (fun a ↦ (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).output b
        ((S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).distribution b hist) y)
      (fun k ↦ (measurable_pi_apply k).comp
        (ideal_algorithm_output_measurable S hIdeal _ (fun k ↦ ih hist k) loss hLoss n b y))
      (learningRate (Fintype.card ι) S.T S.m) i

theorem ideal_kernel_weight_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (b : ℕ)
    (hist : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι S.m (n b)) b)
    (y : DyadicBlockOutcome ι S.m (n b)) :
    Measurable (fun a ↦ (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).kernel b hist y) := by
  exact ideal_dyadicLaw_weight_measurable S hIdeal
    (fun a ↦ (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).distribution b hist)
    (fun i ↦ ideal_distribution_weight_measurable S hIdeal loss hLoss n b hist i)
    loss hLoss (threshold (Fintype.card ι) S.T)
    (prefixHorizon (fun b ↦ n b+1) b) (n b) y

theorem ideal_execution_weight_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (B : ℕ)
    (hist : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι S.m (n b)) B) :
    Measurable (fun a ↦ (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).execution B hist) := by
  induction B with
  | zero => exact measurable_const
  | succ B ih =>
    rcases hist with ⟨hist, y⟩
    change Measurable (fun a ↦
      (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).execution B hist *
      (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).kernel B hist y)
    exact (ih hist).mul (ideal_kernel_weight_measurable S hIdeal loss hLoss n B hist y)

theorem ideal_execution_mean_measurable (S : SteeringParameters ι) (hIdeal : S.rounded=false)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (B : ℕ)
    (f : A → FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι S.m (n b)) B → ℝ)
    (hf : ∀ hist, Measurable (fun a ↦ f a hist)) :
    Measurable (fun a ↦ (S.idealFeedbackPolicy.algorithm S.tournament n (loss a)).execution B |>.mean (f a)) := by
  exact Finset.measurable_sum Finset.univ (fun hist _ ↦
    (ideal_execution_weight_measurable S hIdeal loss hLoss n B hist).mul (hf hist))

end

end Tournament.Upper.SteeringParameters

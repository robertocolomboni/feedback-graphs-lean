module

public import Tournament.Upper.RoundedFeedbackDecoder
public import Tournament.Upper.DartboardMeasurable

@[expose] public section

namespace Tournament.Model

open MeasureTheory
open scoped Classical
noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSpace A]

omit [Fintype ι] [MeasurableSpace ι] in
theorem comparisonObservation_family_measurable (F : ι → ι → Prop)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (t : ℕ) (s : ι) : Measurable (fun a ↦ comparisonObservation F s (loss a t)) := by
  apply Measurable.of_eval
  intro k
  by_cases h : F s k
  · simp only [comparisonObservation, ite_eq_left h]
    exact measurable_sub.comp ((hLoss t s).prodMk (hLoss t k))
  · simp only [comparisonObservation, ite_eq_right h]
    exact measurable_const

omit [Fintype ι] in
theorem recordComparisons_family_measurable (F : ι → ι → Prop)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ) (hist : FinitePath.History ι n) :
    Measurable (fun a ↦ recordComparisons F (loss a) n hist) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    rcases hist with ⟨hist, i⟩
    exact ((ih hist).prodMk
      (comparisonObservation_family_measurable F loss hLoss n (FinitePath.lastState n hist))).prodMk
        measurable_const

end
end Tournament.Model

namespace Tournament.Upper

open MeasureTheory Model
open scoped Classical BigOperators
noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSpace A]

omit [Fintype ι] in
theorem recordBlockComparisons_family_measurable (F : ι → ι → Prop)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (ns : List ℕ) (offset : ℕ) (hist : BlockOutcome ι ns) :
    Measurable (fun a ↦ recordBlockComparisons F (loss a) offset ns hist) := by
  induction ns generalizing offset with
  | nil => exact measurable_const
  | cons n ns ih =>
    rcases hist with ⟨hist, rest⟩
    exact ((recordComparisons_family_measurable F (fun a t ↦ loss a (offset+t))
      (fun t i ↦ hLoss (offset+t) i) n hist).prodMk
      (comparisonObservation_family_measurable F loss hLoss (offset+n)
        (FinitePath.lastState n hist))).prodMk (ih (offset+(n+1)) rest)

namespace SteeringParameters

open BlockParameters

variable [Nonempty ι] [DiscreteMeasurableSpace ι]

theorem rounded_chunkLaw_weight_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (j : Fin (S.m+1)) (M : ℝ) (offset n : ℕ) (hist : FinitePath.History ι n) :
    Measurable (fun a ↦ (((S.rules (p a) j).shift offset).comparisonPolicy M).law
      S.tournament (fun t ↦ loss a (offset+t)) n hist) := by
  induction n with
  | zero => exact rounded_holding_sampling_measurable S hRound p hp hist
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
        (rounded_rules_decoder_measurable S hRound p hp j) offset)
      (rounded_holding_kernel_measurable S hRound p hp (DyadicRate.rate S.m j)
        (DyadicRate.rate_pos S.m j))
      (rounded_holding_sampling_measurable S hRound p hp) M n
    · exact recordComparisons_family_measurable S.tournament
        (fun a t ↦ loss a (offset+t)) (fun t k ↦ hLoss (offset+t) k) n hist
    · intro k
      exact (measurable_pi_apply k).comp
        (comparisonObservation_family_measurable S.tournament loss hLoss (offset+n)
          (FinitePath.lastState n hist))

theorem rounded_resetLaw_weight_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
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
    exact (rounded_chunkLaw_weight_measurable S hRound p hp loss hLoss j M offset n hist).mul
      (ih (offset+(n+1)) rest)

theorem rounded_dyadicLaw_weight_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
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
    (rounded_resetLaw_weight_measurable S hRound p hp loss hLoss j M _ offset hist))

theorem rounded_algorithm_output_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (b : ℕ) (y : DyadicBlockOutcome ι S.m (n b)) :
    Measurable (fun a ↦ (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).output b (p a) y) := by
  exact roundedOutput_measurable S hRound p hp y.1 _ _
    (fun a ↦ recordBlockComparisons S.tournament (loss a)
      (prefixHorizon (fun b ↦ n b+1) b) (Restarts.parts (n b) y.2.1) y.2.2)
    (recordBlockComparisons_family_measurable S.tournament loss hLoss _ _ y.2.2)

theorem rounded_distribution_weight_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (b : ℕ)
    (hist : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι S.m (n b)) b) (i : ι) :
    Measurable (fun a ↦ (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).distribution b hist i) := by
  induction b generalizing i with
  | zero => exact measurable_const
  | succ b ih =>
    rcases hist with ⟨hist, y⟩
    exact ShrinkingDartboard.update_weight_measurable
      (fun a ↦ (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).distribution b hist)
      (fun k ↦ ih hist k)
      (fun a ↦ (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).output b
        ((S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).distribution b hist) y)
      (fun k ↦ (measurable_pi_apply k).comp
        (rounded_algorithm_output_measurable S hRound _ (fun k ↦ ih hist k) loss hLoss n b y))
      (learningRate (Fintype.card ι) S.T S.m) i

theorem rounded_kernel_weight_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (b : ℕ)
    (hist : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι S.m (n b)) b)
    (y : DyadicBlockOutcome ι S.m (n b)) :
    Measurable (fun a ↦ (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).kernel b hist y) := by
  exact rounded_dyadicLaw_weight_measurable S hRound
    (fun a ↦ (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).distribution b hist)
    (fun i ↦ rounded_distribution_weight_measurable S hRound loss hLoss n b hist i)
    loss hLoss (threshold (Fintype.card ι) S.T)
    (prefixHorizon (fun b ↦ n b+1) b) (n b) y

theorem rounded_execution_weight_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (B : ℕ)
    (hist : FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι S.m (n b)) B) :
    Measurable (fun a ↦ (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).execution B hist) := by
  induction B with
  | zero => exact measurable_const
  | succ B ih =>
    rcases hist with ⟨hist, y⟩
    change Measurable (fun a ↦
      (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).execution B hist *
      (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).kernel B hist y)
    exact (ih hist).mul (rounded_kernel_weight_measurable S hRound loss hLoss n B hist y)

theorem rounded_execution_mean_measurable (S : SteeringParameters ι) (hRound : S.rounded=true)
    (loss : A → ℕ → ι → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (B : ℕ)
    (f : A → FiniteProcess.History (fun b ↦ DyadicBlockOutcome ι S.m (n b)) B → ℝ)
    (hf : ∀ hist, Measurable (fun a ↦ f a hist)) :
    Measurable (fun a ↦ (S.roundedFeedbackPolicy.algorithm S.tournament n (loss a)).execution B |>.mean (f a)) := by
  exact Finset.measurable_sum Finset.univ (fun hist _ ↦
    (rounded_execution_weight_measurable S hRound loss hLoss n B hist).mul (hf hist))

end SteeringParameters
end
end Tournament.Upper

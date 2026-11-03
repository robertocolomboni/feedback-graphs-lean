module

public import Tournament.Computation.OptimizerCodeMeasurable
public import Tournament.Upper.FeedbackLawMeasurable
public import Tournament.Upper.LiftedCompressedLaw

@[expose] public section

namespace Tournament.Computation.OptimizerFeedback

open MeasureTheory Upper Model BlockParameters OptimizerCodeMeasurable
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 800000

variable {K : ℕ} [Nonempty (Fin K)]
local instance finClassicalDecidableEq : DecidableEq (Fin K) :=
  fun a b ↦ Classical.propDecidable (a=b)

def output (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) (π : ProbabilityVector (Fin K))
    (j : Fin (S.m+1)) (offset : ℕ) (ns : List ℕ) (log : BlockTranscript (Fin K) ns) : Fin K → ℝ :=
  truncateEstimate (learningRate (Fintype.card (Fin K)) S.T S.m)
    (blockObservedEstimate ((parameters S solve hc).rules π j) (decoder S solve hc π)
      (threshold (Fintype.card (Fin K)) S.T) offset ns log)

theorem output_record (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) (π : ProbabilityVector (Fin K))
    (loss : ℕ → Fin K → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) (offset n : ℕ)
    (y : DyadicBlockOutcome (Fin K) S.m n) :
    output S solve hc π y.1 offset (Restarts.parts n y.2.1)
      (recordBlockComparisons S.tournament loss offset (Restarts.parts n y.2.1) y.2.2)=
        truncateEstimate (learningRate (Fintype.card (Fin K)) S.T S.m)
          (dyadicBlockCorrectedEstimate ((parameters S solve hc).holding π) S.m
            ((parameters S solve hc).rules π) ((parameters S solve hc).estimator π)
            loss (threshold (Fintype.card (Fin K)) S.T) offset n y) := by
  have hRaw : blockObservedEstimate ((parameters S solve hc).rules π y.1)
        (decoder S solve hc π) (threshold (Fintype.card (Fin K)) S.T) offset (Restarts.parts n y.2.1)
        (recordBlockComparisons S.tournament loss offset (Restarts.parts n y.2.1) y.2.2)=
      dyadicBlockCorrectedEstimate ((parameters S solve hc).holding π) S.m
        ((parameters S solve hc).rules π) ((parameters S solve hc).estimator π)
        loss (threshold (Fintype.card (Fin K)) S.T) offset n y := by
    funext k
    exact blockObservedEstimate_record ((parameters S solve hc).rules π y.1)
      ((parameters S solve hc).estimator π) (decoder S solve hc π)
      (fun f _ s i ↦ (decoder_correct S solve hc π f s i).symm)
      (threshold (Fintype.card (Fin K)) S.T) loss hLoss (Restarts.parts n y.2.1) offset y.2.2 k
  unfold output
  rw [hRaw]

def feedbackPolicy (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) : FeedbackEW (Fin K) S.m where
  rate := learningRate (Fintype.card (Fin K)) S.T S.m
  policy π := dyadicComparisonPolicy ((parameters S solve hc).holding π) S.m
    ((parameters S solve hc).rules π) (threshold (Fintype.card (Fin K)) S.T)
  output := output S solve hc

theorem algorithm_eq (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve)
    (n : ℕ → ℕ) (loss : ℕ → Fin K → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (feedbackPolicy S solve hc).algorithm S.tournament n loss =
      (parameters S solve hc).algorithm n loss hLoss := by
  unfold FeedbackEW.algorithm feedbackPolicy OptimizerMainTransfer.Parameters.algorithm
  congr 1
  · funext b π y
    exact output_record S solve hc π loss hLoss _ _ y
  · funext b π
    apply ProbabilityVector.ext_weights
    intro y
    exact dyadicComparisonPolicy_law ((parameters S solve hc).holding π) S.m
      ((parameters S solve hc).rules π) (threshold (Fintype.card (Fin K)) S.T)
      (threshold_ge_one S.card_ge_two S.time_ge_two) loss hLoss _ _ y

theorem metadataIndependent (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) : (feedbackPolicy S solve hc).MetadataIndependent := by
  intro p q n j coins
  rfl

variable {A : Type*} [MeasurableSpace A]

theorem output_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) (p : A → ProbabilityVector (Fin K))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (j : Fin (S.m+1))
    (offset : ℕ) (ns : List ℕ) (log : A → BlockTranscript (Fin K) ns) (hLog : Measurable log) :
    Measurable (fun a ↦ output S solve hc (p a) j offset ns (log a)) :=
  truncated_blockOutput_measurable (fun a ↦ (parameters S solve hc).rules (p a) j)
    (rules_decoder_measurable S solve hc p hp j)
    (fun a ↦ decoder S solve hc (p a)) (decoder_measurable S solve hc p hp)
    (threshold (Fintype.card (Fin K)) S.T) (learningRate (Fintype.card (Fin K)) S.T S.m)
    ns offset log hLog

theorem chunkLaw_weight_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve)
    (p : A → ProbabilityVector (Fin K)) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → (Fin K) → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (j : Fin (S.m+1)) (M : ℝ) (offset n : ℕ) (hist : FinitePath.History (Fin K) n) :
    Measurable (fun a ↦ ((((parameters S solve hc).rules (p a) j).shift offset).comparisonPolicy M).law
      S.tournament (fun t ↦ loss a (offset+t)) n hist) := by
  induction n with
  | zero => exact holding_sampling_measurable S solve hc p hp hist
  | succ n ih =>
    rcases hist with ⟨hist, i⟩
    change Measurable (fun a ↦
      ((((parameters S solve hc).rules (p a) j).shift offset).comparisonPolicy M).law
        S.tournament (fun t ↦ loss a (offset+t)) n hist *
      (((parameters S solve hc).rules (p a) j).shift offset).observedRow M n
        (recordComparisons S.tournament (fun t ↦ loss a (offset+t)) n hist)
        (comparisonObservation S.tournament (FinitePath.lastState n hist) (loss a (offset+n))) i)
    apply (ih hist).mul
    apply ScoreRule.observedRow_weight_measurable
      (fun a ↦ ((parameters S solve hc).rules (p a) j).shift offset)
      (decoderMeasurable_shift (fun a ↦ (parameters S solve hc).rules (p a) j)
        (rules_decoder_measurable S solve hc p hp j) offset)
      (holding_kernel_measurable S solve hc p hp (DyadicRate.rate S.m j)
        (DyadicRate.rate_pos S.m j))
      (holding_sampling_measurable S solve hc p hp) M n
    · exact recordComparisons_family_measurable S.tournament
        (fun a t ↦ loss a (offset+t)) (fun t k ↦ hLoss (offset+t) k) n hist
    · intro k
      exact (measurable_pi_apply k).comp
        (comparisonObservation_family_measurable S.tournament loss hLoss (offset+n)
          (FinitePath.lastState n hist))

theorem resetLaw_weight_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve)
    (p : A → ProbabilityVector (Fin K)) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → (Fin K) → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (j : Fin (S.m+1)) (M : ℝ) (ns : List ℕ) (offset : ℕ) (hist : BlockOutcome (Fin K) ns) :
    Measurable (fun a ↦ (resetComparisonPolicy ((parameters S solve hc).rules (p a) j) M).law
      S.tournament (loss a) offset ns hist) := by
  induction ns generalizing offset with
  | nil => exact measurable_const
  | cons n ns ih =>
    rcases hist with ⟨hist, rest⟩
    change Measurable (fun a ↦
      ((((parameters S solve hc).rules (p a) j).shift offset).comparisonPolicy M).law
        S.tournament (fun t ↦ loss a (offset+t)) n hist *
      (resetComparisonPolicy ((parameters S solve hc).rules (p a) j) M).law
        S.tournament (loss a) (offset+(n+1)) ns rest)
    exact (chunkLaw_weight_measurable S solve hc p hp loss hLoss j M offset n hist).mul
      (ih (offset+(n+1)) rest)

theorem dyadicLaw_weight_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve)
    (p : A → ProbabilityVector (Fin K)) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → (Fin K) → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (M : ℝ) (offset n : ℕ) (y : DyadicBlockOutcome (Fin K) S.m n) :
    Measurable (fun a ↦ (dyadicComparisonPolicy ((parameters S solve hc).holding (p a)) S.m ((parameters S solve hc).rules (p a)) M).law
      S.tournament (loss a) offset n y) := by
  rcases y with ⟨j, coins, hist⟩
  change Measurable (fun a ↦ DyadicRate.law S.m j *
    (Restarts.law (DyadicRate.rate S.m j) (le_of_lt (DyadicRate.rate_pos S.m j))
      (DyadicRate.rate_le_one S.m j) n coins *
    (resetComparisonPolicy ((parameters S solve hc).rules (p a) j) M).law
      S.tournament (loss a) offset (Restarts.parts n coins) hist))
  exact measurable_const.mul (measurable_const.mul
    (resetLaw_weight_measurable S solve hc p hp loss hLoss j M _ offset hist))

theorem algorithm_output_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve)
    (p : A → ProbabilityVector (Fin K)) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (loss : A → ℕ → (Fin K) → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (b : ℕ) (y : DyadicBlockOutcome (Fin K) S.m (n b)) :
    Measurable (fun a ↦ ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).output b (p a) y) := by
  exact output_measurable S solve hc p hp y.1 _ _
    (fun a ↦ recordBlockComparisons S.tournament (loss a)
      (prefixHorizon (fun b ↦ n b+1) b) (Restarts.parts (n b) y.2.1) y.2.2)
    (recordBlockComparisons_family_measurable S.tournament loss hLoss _ _ y.2.2)

theorem distribution_weight_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve)
    (loss : A → ℕ → (Fin K) → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (b : ℕ)
    (hist : FiniteProcess.History (fun b ↦ DyadicBlockOutcome (Fin K) S.m (n b)) b) (i : (Fin K)) :
    Measurable (fun a ↦ ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).distribution b hist i) := by
  induction b generalizing i with
  | zero => exact measurable_const
  | succ b ih =>
    rcases hist with ⟨hist, y⟩
    exact ShrinkingDartboard.update_weight_measurable
      (fun a ↦ ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).distribution b hist)
      (fun k ↦ ih hist k)
      (fun a ↦ ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).output b
        (((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).distribution b hist) y)
      (fun k ↦ (measurable_pi_apply k).comp
        (algorithm_output_measurable S solve hc _ (fun k ↦ ih hist k) loss hLoss n b y))
      (learningRate (Fintype.card (Fin K)) S.T S.m) i

theorem kernel_weight_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve)
    (loss : A → ℕ → (Fin K) → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (b : ℕ)
    (hist : FiniteProcess.History (fun b ↦ DyadicBlockOutcome (Fin K) S.m (n b)) b)
    (y : DyadicBlockOutcome (Fin K) S.m (n b)) :
    Measurable (fun a ↦ ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).kernel b hist y) := by
  exact dyadicLaw_weight_measurable S solve hc
    (fun a ↦ ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).distribution b hist)
    (fun i ↦ distribution_weight_measurable S solve hc loss hLoss n b hist i)
    loss hLoss (threshold (Fintype.card (Fin K)) S.T)
    (prefixHorizon (fun b ↦ n b+1) b) (n b) y

theorem execution_weight_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve)
    (loss : A → ℕ → (Fin K) → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (B : ℕ)
    (hist : FiniteProcess.History (fun b ↦ DyadicBlockOutcome (Fin K) S.m (n b)) B) :
    Measurable (fun a ↦ ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).execution B hist) := by
  induction B with
  | zero => exact measurable_const
  | succ B ih =>
    rcases hist with ⟨hist, y⟩
    change Measurable (fun a ↦
      ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).execution B hist *
      ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).kernel B hist y)
    exact (ih hist).mul (kernel_weight_measurable S solve hc loss hLoss n B hist y)

theorem execution_mean_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve)
    (loss : A → ℕ → (Fin K) → ℝ) (hLoss : ∀ t i, Measurable (fun a ↦ loss a t i))
    (n : ℕ → ℕ) (B : ℕ)
    (f : A → FiniteProcess.History (fun b ↦ DyadicBlockOutcome (Fin K) S.m (n b)) B → ℝ)
    (hf : ∀ hist, Measurable (fun a ↦ f a hist)) :
    Measurable (fun a ↦ ((feedbackPolicy S solve hc).algorithm S.tournament n (loss a)).execution B |>.mean (f a)) := by
  exact Finset.measurable_sum Finset.univ (fun hist _ ↦
    (execution_weight_measurable S solve hc loss hLoss n B hist).mul (hf hist))

theorem liftedCompressedLaw_atom_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) (n : ℕ → ℕ) (B : ℕ)
    (x : SeedMetadata.{0} S.m n B × (Fin (prefixHorizon (fun b ↦ n b+1) B) → Fin K)) :
    Measurable (fun loss ↦ (feedbackPolicy S solve hc).liftedCompressedLaw S.tournament loss n B x) :=
  execution_weight_measurable S solve hc (fun loss ↦ loss)
    (fun t i ↦ (measurable_pi_apply i).comp (measurable_pi_apply t)) n B
    ((executionTraceEquiv (ι := Fin K) S.m n B).symm (x.1.down,x.2))

end
end Tournament.Computation.OptimizerFeedback

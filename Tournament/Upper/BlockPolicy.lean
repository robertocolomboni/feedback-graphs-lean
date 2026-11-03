module

public import Tournament.Upper.BlockGain
public import Tournament.Upper.ChunkTheorem
public import Tournament.Model.EstimateUpdate

@[expose] public section

namespace Tournament

open scoped BigOperators Classical
open FinitePath

noncomputable section

namespace Model

variable {ι : Type*} [Fintype ι]

structure ResetComparisonPolicy (ι : Type*) [Fintype ι] where
  chunk : ℕ → ℕ → ComparisonPolicy ι

def ResetComparisonPolicy.law (π : ResetComparisonPolicy ι) (F : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) : (offset : ℕ) → (ns : List ℕ) → ProbabilityVector (Upper.BlockOutcome ι ns)
  | _, [] => ProbabilityVector.pure (ULift.up ())
  | offset, n::ns => ((π.chunk offset n).law F (fun t ↦ loss (offset+t)) n).joint
      (fun _ ↦ π.law F loss (offset+(n+1)) ns)

structure RestartComparisonPolicy (ι : Type*) [Fintype ι] (m : ℕ) where
  rates : ProbabilityVector (Fin (m+1))
  restart : Fin (m+1) → ℝ
  restart_nonneg : ∀ j, 0 ≤ restart j
  restart_le_one : ∀ j, restart j ≤ 1
  chunks : Fin (m+1) → ResetComparisonPolicy ι

def RestartComparisonPolicy.law {m : ℕ} (π : RestartComparisonPolicy ι m)
    (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    ProbabilityVector (Upper.DyadicBlockOutcome ι m n) :=
  π.rates.sigmaJoint (fun j ↦
    (Restarts.law (π.restart j) (π.restart_nonneg j) (π.restart_le_one j) n).sigmaJoint
      (fun coins ↦ (π.chunks j).law F loss offset (Restarts.parts n coins)))

end Model

namespace Upper

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

def resetComparisonPolicy (R : ScoreRule F P p) (M : ℝ) : Model.ResetComparisonPolicy ι where
  chunk offset _n := (R.shift offset).comparisonPolicy M

theorem resetComparisonPolicy_law (R : ScoreRule F P p) (M : ℝ) (hM : 1 ≤ M)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) :
    ∀ ns offset (outcome : BlockOutcome ι ns),
      (resetComparisonPolicy R M).law F loss offset ns outcome =
        blockLaw R loss hloss M hM offset ns outcome := by
  intro ns
  induction ns with
  | nil => intro offset outcome; rfl
  | cons n ns ih =>
    intro offset outcome
    change ((R.shift offset).comparisonPolicy M).law F (fun t ↦ loss (offset+t)) n outcome.1 *
      (resetComparisonPolicy R M).law F loss (offset+(n+1)) ns outcome.2 =
        (R.shift offset).tiltedLaw (fun t ↦ loss (offset+t)) (fun t ↦ hloss (offset+t)) M hM n outcome.1 *
          blockLaw R loss hloss M hM (offset+(n+1)) ns outcome.2
    rw [ScoreRule.comparisonPolicy_law,ih (offset+(n+1))]

def dyadicComparisonPolicy (H : HoldingFamily ι) (m : ℕ) (R : DyadicScoreRules H F m)
    (M : ℝ) : Model.RestartComparisonPolicy ι m where
  rates := DyadicRate.law m
  restart := DyadicRate.rate m
  restart_nonneg j := le_of_lt (DyadicRate.rate_pos m j)
  restart_le_one := DyadicRate.rate_le_one m
  chunks j := resetComparisonPolicy (R j) M

theorem dyadicComparisonPolicy_law (H : HoldingFamily ι) (m : ℕ) (R : DyadicScoreRules H F m)
    (M : ℝ) (hM : 1 ≤ M) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (offset n : ℕ) (outcome : DyadicBlockOutcome ι m n) :
    (dyadicComparisonPolicy H m R M).law F loss offset n outcome =
      dyadicBlockLaw H m R loss hloss M hM offset n outcome := by
  rcases outcome with ⟨j,coins,histories⟩
  change DyadicRate.law m j *
      (Restarts.law (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) n coins *
        (resetComparisonPolicy (R j) M).law F loss offset (Restarts.parts n coins) histories) =
    DyadicRate.law m j *
      (Restarts.law (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) n coins *
        blockLaw (R j) loss hloss M hM offset (Restarts.parts n coins) histories)
  rw [resetComparisonPolicy_law]

theorem dyadicComparisonPolicy_mean (H : HoldingFamily ι) (m : ℕ) (R : DyadicScoreRules H F m)
    (M : ℝ) (hM : 1 ≤ M) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (offset n : ℕ) (f : DyadicBlockOutcome ι m n → ℝ) :
    ((dyadicComparisonPolicy H m R M).law F loss offset n).mean f =
      (dyadicBlockLaw H m R loss hloss M hM offset n).mean f := by
  unfold ProbabilityVector.mean
  apply Finset.sum_congr rfl
  intro outcome _
  rw [dyadicComparisonPolicy_law]

universe u

abbrev BlockTranscript (ι : Type u) : List ℕ → Type u
  | [] => ULift Unit
  | n::ns => (Model.ComparisonHistory ι n × (ι → ℝ)) × BlockTranscript ι ns

def recordBlockComparisons (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    (offset : ℕ) → (ns : List ℕ) → BlockOutcome ι ns → BlockTranscript ι ns
  | _, [], _ => ULift.up ()
  | offset, n::ns, outcome =>
      ((Model.recordComparisons F (fun t ↦ loss (offset+t)) n outcome.1,
        Model.comparisonObservation F (lastState n outcome.1) (loss (offset+n))),
        recordBlockComparisons F loss (offset+(n+1)) ns outcome.2)

def blockObservedEstimate (R : ScoreRule F P p) (decode : ι → (ι → ℝ) → ι → ℝ) (M : ℝ) :
    (offset : ℕ) → (ns : List ℕ) → BlockTranscript ι ns → ι → ℝ
  | _, [], _, _ => 0
  | offset, n::ns, log, k =>
      ScoreRule.observedEstimate decode n log.1.1 log.1.2 k /
        (1+ScoreRule.steeringStrength M*(R.shift offset).observedSum M n log.1.1)+
      blockObservedEstimate R decode M (offset+(n+1)) ns log.2 k

theorem blockObservedEstimate_record (R : ScoreRule F P p)
    (Ψ : ι → ι → ι → ℝ) (decode : ι → (ι → ℝ) → ι → ℝ)
    (hdecode : ∀ loss, BoundedLoss loss → ∀ s k,
      applyEstimator Ψ s loss k = decode s (Model.comparisonObservation F s loss) k)
    (M : ℝ) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) :
    ∀ ns offset (outcome : BlockOutcome ι ns) k,
      blockObservedEstimate R decode M offset ns (recordBlockComparisons F loss offset ns outcome) k =
        blockCorrectedEstimate R Ψ loss M offset ns outcome k := by
  intro ns
  induction ns with
  | nil => intro offset outcome k; rfl
  | cons n ns ih =>
    intro offset outcome k
    change ScoreRule.observedEstimate decode n
        (Model.recordComparisons F (fun t ↦ loss (offset+t)) n outcome.1)
        (Model.comparisonObservation F (lastState n outcome.1) (loss (offset+n))) k /
      (1+ScoreRule.steeringStrength M*(R.shift offset).observedSum M n
        (Model.recordComparisons F (fun t ↦ loss (offset+t)) n outcome.1))+
      blockObservedEstimate R decode M (offset+(n+1)) ns
        (recordBlockComparisons F loss (offset+(n+1)) ns outcome.2) k = _
    rw [ScoreRule.observedEstimate_record Ψ decode hdecode (fun t ↦ loss (offset+t))
      (fun t ↦ hloss (offset+t)), ScoreRule.observedSum_record (R.shift offset)
        (fun t ↦ loss (offset+t)) (fun t ↦ hloss (offset+t)), ih (offset+(n+1))]
    rfl

theorem dyadicBlockEstimate_observable (H : HoldingFamily ι) (m : ℕ) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (hobs : ScoreRule.EstimatorObservable F Ψ) (M : ℝ) :
    ∃ output : (j : Fin (m+1)) → (offset : ℕ) → (ns : List ℕ) → BlockTranscript ι ns → ι → ℝ,
      ∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) offset n
        (outcome : DyadicBlockOutcome ι m n) k,
        output outcome.1 offset (Restarts.parts n outcome.2.1)
          (recordBlockComparisons F loss offset (Restarts.parts n outcome.2.1) outcome.2.2) k =
            dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome k := by
  rcases hobs with ⟨decode,hdecode⟩
  refine ⟨fun j ↦ blockObservedEstimate (R j) decode M,?_⟩
  intro loss hloss offset n outcome k
  exact blockObservedEstimate_record (R outcome.1) Ψ decode hdecode M loss hloss
    (Restarts.parts n outcome.2.1) offset outcome.2.2 k

theorem dyadicBlockUpdate_observable (H : HoldingFamily ι) (m : ℕ) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (hobs : ScoreRule.EstimatorObservable F Ψ) (M η : ℝ)
    (weights : ProbabilityVector ι) :
    ∃ output : (j : Fin (m+1)) → (offset : ℕ) → (ns : List ℕ) → BlockTranscript ι ns → ProbabilityVector ι,
      ∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) offset n
        (outcome : DyadicBlockOutcome ι m n),
        output outcome.1 offset (Restarts.parts n outcome.2.1)
          (recordBlockComparisons F loss offset (Restarts.parts n outcome.2.1) outcome.2.2) =
            Model.exponentialUpdate weights η
              (Model.truncateEstimate η (dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome)) := by
  rcases dyadicBlockEstimate_observable H m R Ψ hobs M with ⟨raw,hraw⟩
  refine ⟨fun j offset ns log ↦ Model.exponentialUpdate weights η
    (Model.truncateEstimate η (raw j offset ns log)),?_⟩
  intro loss hloss offset n outcome
  have heq : raw outcome.1 offset (Restarts.parts n outcome.2.1)
      (recordBlockComparisons F loss offset (Restarts.parts n outcome.2.1) outcome.2.2) =
        dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome := by
    funext k
    exact hraw loss hloss offset n outcome k
  dsimp only
  rw [heq]

end Upper
end
end Tournament

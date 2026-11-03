module

public import Tournament.Model.ComparisonPolicy
public import Tournament.Upper.ChunkResponse

@[expose] public section

namespace Tournament.Upper.ScoreRule

open scoped BigOperators Classical
open FinitePath Model

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

noncomputable section

theorem score_from_observation (R : ScoreRule F P p) (t : ℕ) (loss : ι → ℝ)
    (hloss : BoundedLoss loss) (i j : ι) :
    R.score t loss i j = R.decoder t i (comparisonObservation F i loss) j := by
  rw [R.decoder_eq t loss hloss i j]
  apply R.decoder_local
  intro k hk
  simp only [comparisonObservation, ite_eq_left hk]

def observedSum (R : ScoreRule F P p) (M : ℝ) : (n : ℕ) → ComparisonHistory ι n → ℝ
  | 0, _ => 0
  | n+1, ((hist,obs),j) => observedSum R M n hist +
      (if |observedSum R M n hist| ≤ M-1 then R.decoder n (currentAction n hist) obs j else 0)

theorem observedSum_record (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ)
    (n : ℕ) (hist : History ι n) :
    R.observedSum M n (recordComparisons F loss n hist) = R.stoppedSum loss M n hist := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    simp only [recordComparisons, observedSum, stoppedSum, currentAction_record, ih hist,
      R.score_from_observation n (loss n) (hloss n) (lastState n hist) j]

def EstimatorObservable (F : ι → ι → Prop) (Ψ : ι → ι → ι → ℝ) : Prop :=
  ∃ decode : ι → (ι → ℝ) → ι → ℝ, ∀ loss, BoundedLoss loss → ∀ s k,
    applyEstimator Ψ s loss k = decode s (comparisonObservation F s loss) k

def observedEstimate (decode : ι → (ι → ℝ) → ι → ℝ) :
    (n : ℕ) → ComparisonHistory ι n → (ι → ℝ) → ι → ℝ
  | 0, i, obs, k => decode i obs k
  | n+1, ((hist,prevObs),j), obs, k => observedEstimate decode n hist prevObs k + decode j obs k

theorem observedEstimate_record (Ψ : ι → ι → ι → ℝ) (decode : ι → (ι → ℝ) → ι → ℝ)
    (hdecode : ∀ loss, BoundedLoss loss → ∀ s k,
      applyEstimator Ψ s loss k = decode s (comparisonObservation F s loss) k)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (n : ℕ) (hist : History ι n) (k : ι) :
    observedEstimate decode n (recordComparisons F loss n hist)
      (comparisonObservation F (lastState n hist) (loss n)) k = referenceEstimate Ψ loss n hist k := by
  induction n with
  | zero =>
    change decode hist (comparisonObservation F hist (loss 0)) k =
      ∑ t ∈ Finset.range 1, applyEstimator Ψ hist (loss t) k
    simpa only [Finset.range_one, Finset.sum_singleton] using (hdecode (loss 0) (hloss 0) hist k).symm
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    rw [referenceEstimate_step]
    change observedEstimate decode n (recordComparisons F loss n hist)
      (comparisonObservation F (lastState n hist) (loss n)) k +
      decode j (comparisonObservation F j (loss (n+1))) k = _
    rw [ih hist, hdecode (loss (n+1)) (hloss (n+1)) j k]

theorem correctedEstimate_observable (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (hobs : EstimatorObservable F Ψ) (M : ℝ) :
    ∃ output : (n : ℕ) → ComparisonHistory ι n → (ι → ℝ) → ι → ℝ,
      ∀ loss (_hloss : ∀ t, BoundedLoss (loss t)) n hist k, output n (recordComparisons F loss n hist)
        (comparisonObservation F (lastState n hist) (loss n)) k =
        referenceEstimate Ψ loss n hist k / R.likelihood loss M n hist := by
  rcases hobs with ⟨decode, hdecode⟩
  refine ⟨fun n hist obs k ↦ observedEstimate decode n hist obs k /
    (1+steeringStrength M * R.observedSum M n hist), ?_⟩
  intro loss hloss n hist k
  dsimp only
  rw [observedEstimate_record Ψ decode hdecode loss hloss n hist k, R.observedSum_record loss hloss]
  rfl

def candidateWeight (R : ScoreRule F P p) (M : ℝ) (n : ℕ)
    (hist : ComparisonHistory ι n) (obs : ι → ℝ) (j : ι) : ℝ :=
  P (currentAction n hist) j *
    (1 + steeringStrength M * (R.observedSum M n hist +
      (if |R.observedSum M n hist| ≤ M-1 then R.decoder n (currentAction n hist) obs j else 0))) /
    (1 + steeringStrength M * R.observedSum M n hist)

def candidateValid (R : ScoreRule F P p) (M : ℝ) (n : ℕ)
    (hist : ComparisonHistory ι n) (obs : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ R.candidateWeight M n hist obs j) ∧ ∑ j, R.candidateWeight M n hist obs j = 1

def observedRow (R : ScoreRule F P p) (M : ℝ) (n : ℕ)
    (hist : ComparisonHistory ι n) (obs : ι → ℝ) : ProbabilityVector ι :=
  if h : R.candidateValid M n hist obs then
    ⟨R.candidateWeight M n hist obs, h.1, h.2⟩
  else p

def comparisonPolicy (R : ScoreRule F P p) (M : ℝ) : ComparisonPolicy ι where
  initial := p
  next := R.observedRow M

theorem candidateWeight_record (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (hist : History ι n) (j : ι) :
    R.candidateWeight M n (recordComparisons F loss n hist)
      (comparisonObservation F (lastState n hist) (loss n)) j = R.tiltedRow loss hloss M hM n hist j := by
  unfold candidateWeight tiltedRow
  simp only [currentAction_record, observedSum_record R loss hloss, likelihood, stoppedSum,
    R.score_from_observation n (loss n) (hloss n) (lastState n hist) j]

theorem candidateValid_record (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (hist : History ι n) :
    R.candidateValid M n (recordComparisons F loss n hist)
      (comparisonObservation F (lastState n hist) (loss n)) := by
  constructor
  · intro j
    rw [R.candidateWeight_record loss hloss M hM n hist j]
    exact (R.tiltedRow loss hloss M hM n hist).nonneg j
  · simp_rw [R.candidateWeight_record loss hloss M hM n hist]
    exact (R.tiltedRow loss hloss M hM n hist).sum_eq_one

theorem observedRow_record (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (hist : History ι n) (j : ι) :
    R.observedRow M n (recordComparisons F loss n hist)
      (comparisonObservation F (lastState n hist) (loss n)) j = R.tiltedRow loss hloss M hM n hist j := by
  unfold observedRow
  rw [dite_eq_left (R.candidateValid_record loss hloss M hM n hist)]
  exact R.candidateWeight_record loss hloss M hM n hist j

theorem comparisonPolicy_law (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (hist : History ι n) :
    (R.comparisonPolicy M).law F loss n hist = R.tiltedLaw loss hloss M hM n hist := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    change (R.comparisonPolicy M).law F loss n hist *
      R.observedRow M n (recordComparisons F loss n hist)
        (comparisonObservation F (lastState n hist) (loss n)) j =
      R.tiltedLaw loss hloss M hM n hist * R.tiltedRow loss hloss M hM n hist j
    rw [ih hist, R.observedRow_record loss hloss M hM n hist j]

end
end Tournament.Upper.ScoreRule

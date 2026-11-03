module

public import Tournament.Upper.ChunkPolicy

@[expose] public section

namespace Tournament.Upper.ScoreRule

open scoped Classical
open FinitePath Model

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

noncomputable section

theorem comparisonPolicy_mean (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n : ℕ) (f : History ι n → ℝ) :
    ((R.comparisonPolicy M).law F loss n).mean f = (R.tiltedLaw loss hloss M hM n).mean f := by
  unfold ProbabilityVector.mean
  apply Finset.sum_congr rfl
  intro hist _
  rw [R.comparisonPolicy_law loss hloss M hM n hist]

theorem steering_and_estimation_on_chunk (R : ScoreRule F P p) (M : ℝ) (hM : 1 ≤ M) :
    ∃ π : ComparisonPolicy ι, π.initial = p ∧
      ∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) (n : ℕ),
      (∀ hist, π.law F loss n hist = R.likelihood loss M n hist * law P p n hist) ∧
      (∀ hist, |R.stoppedSum loss M n hist| ≤ M ∧
        3/4 ≤ R.likelihood loss M n hist ∧ R.likelihood loss M n hist ≤ 5/4) ∧
      (∀ (Φ : History ι n → ℝ), (∀ hist, 0 ≤ Φ hist) →
        (π.law F loss n).mean Φ ≤ (5/4) * (law P p n).mean Φ) ∧
      ((π.law F loss n).mean (pathLoss loss n) =
        p.mean (blockLoss loss (n+1)) - steeringStrength M * probingGain P p loss n +
          steeringStrength M * R.stopRemainder loss M n) ∧
      (|R.stopRemainder loss M n| ≤ ((n:ℝ)+1)^2 * R.stopProbability loss M n) ∧
      (∀ (w : ProbabilityVector ι) (Ψ : ι → ι → ι → ℝ), EstimatorCalibration Ψ p w →
        (∀ k, (π.law F loss n).mean
          (fun hist ↦ referenceEstimate Ψ loss n hist k / R.likelihood loss M n hist) =
            w.center (blockLoss loss (n+1)) k) ∧
        (π.law F loss n).mean (fun hist ↦ w.squareNorm
          (fun k ↦ referenceEstimate Ψ loss n hist k / R.likelihood loss M n hist)) ≤
            (4/3) * (law P p n).mean (fun hist ↦ w.squareNorm (referenceEstimate Ψ loss n hist))) := by
  refine ⟨R.comparisonPolicy M, rfl, ?_⟩
  intro loss hloss n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hist
    rw [R.comparisonPolicy_law loss hloss M hM n hist]
    exact R.tiltedLaw_likelihood loss hloss M hM n hist
  · intro hist
    exact ⟨R.stoppedSum_abs_le loss hloss M hM n hist,
      R.likelihood_bounds loss hloss M hM n hist⟩
  · intro Φ hΦ
    rw [R.comparisonPolicy_mean loss hloss M hM n Φ]
    exact R.tilted_nonneg_mean_le loss hloss M hM n Φ hΦ
  · rw [R.comparisonPolicy_mean loss hloss M hM n (pathLoss loss n)]
    exact (R.chunk_loss_response loss hloss M hM n).1
  · exact R.stopRemainder_abs_le loss hloss M n
  · intro w Ψ hcal
    have hmom := R.chunk_estimate_moments loss hloss M hM w Ψ hcal n
    constructor
    · intro k
      rw [R.comparisonPolicy_mean loss hloss M hM n]
      exact hmom.1 k
    · rw [R.comparisonPolicy_mean loss hloss M hM n]
      exact hmom.2

end
end Tournament.Upper.ScoreRule

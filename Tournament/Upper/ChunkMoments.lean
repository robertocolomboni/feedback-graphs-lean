module

public import Tournament.Upper.ChunkLikelihood

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FinitePath

variable {ι : Type*} [Fintype ι]

noncomputable section

def applyEstimator (Ψ : ι → ι → ι → ℝ) (s : ι) (f : ι → ℝ) (k : ι) : ℝ :=
  ∑ i, Ψ s k i * f i

def EstimatorCalibration (Ψ : ι → ι → ι → ℝ) (p w : ProbabilityVector ι) : Prop :=
  ∀ k i, (∑ s, p s * Ψ s k i) = (if k=i then 1 else 0) - w i

theorem calibrated_mean (Ψ : ι → ι → ι → ℝ) (p w : ProbabilityVector ι)
    (hcal : EstimatorCalibration Ψ p w) (f : ι → ℝ) (k : ι) :
    p.mean (fun s ↦ applyEstimator Ψ s f k) = w.center f k := by
  unfold ProbabilityVector.mean applyEstimator
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i, ∑ s, p s * (Ψ s k i * f i)) =
        ∑ i, (∑ s, p s * Ψ s k i) * f i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = ∑ i, ((if k=i then 1 else 0) - w i) * f i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcal k i]
    _ = w.center f k := by
      simp [sub_mul, Finset.sum_sub_distrib, ProbabilityVector.center,
        ProbabilityVector.mean]

def blockLoss (loss : ℕ → ι → ℝ) (h : ℕ) (i : ι) : ℝ :=
  ∑ t ∈ Finset.range h, loss t i

def referenceEstimate (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ)
    (n : ℕ) (hist : History ι n) (k : ι) : ℝ :=
  ∑ t ∈ Finset.range (n+1), applyEstimator Ψ (stateAt n hist t) (loss t) k

theorem referenceEstimate_step (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ)
    (n : ℕ) (hist : History ι n × ι) (k : ι) :
    referenceEstimate Ψ loss (n+1) hist k = referenceEstimate Ψ loss n hist.1 k +
      applyEstimator Ψ hist.2 (loss (n+1)) k := by
  unfold referenceEstimate
  rw [Finset.sum_range_succ]
  have hprefix : (∑ t ∈ Finset.range (n+1), applyEstimator Ψ (stateAt (n+1) hist t) (loss t) k) =
      ∑ t ∈ Finset.range (n+1), applyEstimator Ψ (stateAt n hist.1 t) (loss t) k := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [stateAt_prefix n hist t (Nat.le_of_lt_succ (Finset.mem_range.mp ht))]
  rw [hprefix, stateAt_last]
  rfl

theorem referenceEstimate_mean (P : FiniteKernel ι) (p w : ProbabilityVector ι)
    (hstat : P.Stationary p) (Ψ : ι → ι → ι → ℝ)
    (hcal : EstimatorCalibration Ψ p w) (loss : ℕ → ι → ℝ) (n : ℕ) (k : ι) :
    (FinitePath.law P p n).mean (fun hist ↦ referenceEstimate Ψ loss n hist k) =
      w.center (blockLoss loss (n+1)) k := by
  unfold referenceEstimate
  rw [ProbabilityVector.mean_sum]
  calc
    (∑ t ∈ Finset.range (n+1), (FinitePath.law P p n).mean
        (fun hist ↦ applyEstimator Ψ (stateAt n hist t) (loss t) k)) =
        ∑ t ∈ Finset.range (n+1), p.mean (fun s ↦ applyEstimator Ψ s (loss t) k) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact stationary_stateAt_mean P p hstat n t
        (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) (fun s ↦ applyEstimator Ψ s (loss t) k)
    _ = ∑ t ∈ Finset.range (n+1), w.center (loss t) k := by
      apply Finset.sum_congr rfl
      intro t _
      exact calibrated_mean Ψ p w hcal (loss t) k
    _ = w.center (blockLoss loss (n+1)) k := by
      exact (w.center_sum (Finset.range (n+1)) loss k).symm

namespace ScoreRule

variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

theorem chunk_estimate_moments (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (w : ProbabilityVector ι) (Ψ : ι → ι → ι → ℝ) (hcal : EstimatorCalibration Ψ p w)
    (n : ℕ) :
    (∀ k, (R.tiltedLaw loss hloss M hM n).mean
      (fun hist ↦ referenceEstimate Ψ loss n hist k / R.likelihood loss M n hist) =
        w.center (blockLoss loss (n+1)) k) ∧
    (R.tiltedLaw loss hloss M hM n).mean (fun hist ↦ w.squareNorm
      (fun k ↦ referenceEstimate Ψ loss n hist k / R.likelihood loss M n hist)) ≤
        (4/3) * (FinitePath.law P p n).mean (fun hist ↦ w.squareNorm (referenceEstimate Ψ loss n hist)) := by
  constructor
  · intro k
    rw [R.corrected_mean]
    exact referenceEstimate_mean P p w (P.reversible_stationary p R.reversible) Ψ hcal loss n k
  · exact R.corrected_second_moment loss hloss M hM n w (referenceEstimate Ψ loss n)

end ScoreRule
end
end Tournament.Upper

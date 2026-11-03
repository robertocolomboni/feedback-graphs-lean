module

public import Tournament.Upper.BlockSecondMoment

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FinitePath

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

def estimationError (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι) (s : ι) (f : ι → ℝ) (k : ι) : ℝ :=
  applyEstimator Ψ s f k-w.center f k

theorem estimationError_mean_zero (Ψ : ι → ι → ι → ℝ) (p w : ProbabilityVector ι)
    (hcal : EstimatorCalibration Ψ p w) (f : ι → ℝ) (k : ι) :
    p.mean (fun s ↦ estimationError Ψ w s f k)=0 := by
  unfold estimationError
  rw [ProbabilityVector.mean_sub,calibrated_mean Ψ p w hcal,ProbabilityVector.mean_const,sub_self]

theorem referenceErrorEstimate_eq_sum_errors (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι)
    (loss : ℕ → ι → ℝ) (n : ℕ) (hist : History ι n) (k : ι) :
    referenceErrorEstimate Ψ w loss n hist k =
      ∑ t ∈ Finset.range (n+1), estimationError Ψ w (stateAt n hist t) (loss t) k := by
  unfold referenceErrorEstimate referenceEstimate blockLoss estimationError
  rw [ProbabilityVector.center_sum,Finset.sum_sub_distrib]

def partitionedReferenceError (P : FiniteKernel ι) (p w : ProbabilityVector ι) (Ψ : ι → ι → ι → ℝ)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (loss : ℕ → ι → ℝ) (offset n : ℕ) : ℝ :=
  (Restarts.law τ hτ hτ1 n).mean (fun coins ↦ referenceErrorSum P p w Ψ loss offset (Restarts.parts n coins))

def referenceErrorEnergy (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) : ℝ :=
  (DyadicRate.law m).mean (fun j ↦ partitionedReferenceError
    (H.kernel (DyadicRate.rate m j) (DyadicRate.rate_pos m j)) H.sampling w Ψ
    (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) loss offset n)

theorem referenceChunkErrorMoment_nonneg (P : FiniteKernel ι) (p w : ProbabilityVector ι)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (start n : ℕ) :
    0 ≤ referenceChunkErrorMoment P p w Ψ loss start n :=
  ProbabilityVector.mean_nonneg _ (fun _hist ↦ w.squareNorm_nonneg _)

theorem referenceErrorSum_nonneg (P : FiniteKernel ι) (p w : ProbabilityVector ι)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (ns : List ℕ) (offset : ℕ) :
    0 ≤ referenceErrorSum P p w Ψ loss offset ns := by
  induction ns generalizing offset with
  | nil => exact le_rfl
  | cons n ns ih =>
    exact add_nonneg (referenceChunkErrorMoment_nonneg P p w Ψ loss offset n) (ih (offset+(n+1)))

theorem referenceErrorEnergy_nonneg (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    0 ≤ referenceErrorEnergy H w m Ψ loss offset n := by
  apply ProbabilityVector.mean_nonneg
  intro j
  apply ProbabilityVector.mean_nonneg
  intro coins
  exact referenceErrorSum_nonneg _ _ _ _ _ (Restarts.parts n coins) offset

theorem partitionedBlock_secondMoment_decomposition_le (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ p w)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (offset n : ℕ) :
    (partitionedBlockLaw R loss hloss M hM τ hτ hτ1 offset n).mean (fun outcome ↦
      w.squareNorm (blockCorrectedEstimate R Ψ loss M offset (Restarts.parts n outcome.1) outcome.2)) ≤
        w.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1))+
          (4/3)*partitionedReferenceError P p w Ψ τ hτ hτ1 loss offset n+
          (1/3)*partitionedChunkVariance w τ hτ hτ1 loss offset n := by
  unfold partitionedBlockLaw
  rw [ProbabilityVector.sigmaJoint_mean]
  calc
    _ ≤ (Restarts.law τ hτ hτ1 n).mean (fun coins ↦
        w.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1))+
          (4/3)*referenceErrorSum P p w Ψ loss offset (Restarts.parts n coins)+
          (1/3)*chunkVariance w loss offset (Restarts.parts n coins)) := by
      apply ProbabilityVector.mean_mono
      intro coins
      have hb := block_secondMoment_decomposition_le R Ψ loss hloss M hM w hcal (Restarts.parts n coins) offset
      rwa [Restarts.parts_totalRounds] at hb
    _ = _ := by
      rw [ProbabilityVector.mean_add,ProbabilityVector.mean_add,ProbabilityVector.mean_const,
        ProbabilityVector.mean_const_mul,ProbabilityVector.mean_const_mul]
      rfl

theorem dyadicBlock_secondMoment_decomposition_le (H : HoldingFamily ι) (m : ℕ) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M : ℝ) (hM : 1 ≤ M) (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ H.sampling w)
    (offset n : ℕ) :
    (dyadicBlockLaw H m R loss hloss M hM offset n).mean (fun outcome ↦
      w.squareNorm (dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome)) ≤
        w.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1))+
          (4/3)*referenceErrorEnergy H w m Ψ loss offset n+(1/3)*averagedChunkMeanSquares H w m loss offset n := by
  change ((DyadicRate.law m).sigmaJoint (fun j ↦ partitionedBlockLaw (R j) loss hloss M hM
    (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) offset n)).mean
      (fun outcome : (_j : Fin (m+1)) × (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins) ↦
        w.squareNorm (blockCorrectedEstimate (R outcome.1) Ψ loss M offset (Restarts.parts n outcome.2.1) outcome.2.2)) ≤ _
  rw [ProbabilityVector.sigmaJoint_mean]
  calc
    _ ≤ (DyadicRate.law m).mean (fun j ↦ w.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1))+
        (4/3)*partitionedReferenceError (H.kernel (DyadicRate.rate m j) (DyadicRate.rate_pos m j)) H.sampling w Ψ
          (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) loss offset n+
        (1/3)*partitionedChunkVariance w (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j))
          (DyadicRate.rate_le_one m j) loss offset n) := by
      apply ProbabilityVector.mean_mono
      intro j
      exact partitionedBlock_secondMoment_decomposition_le (R j) Ψ loss hloss M hM w hcal _ _ _ offset n
    _ = _ := by
      rw [ProbabilityVector.mean_add,ProbabilityVector.mean_add,ProbabilityVector.mean_const,
        ProbabilityVector.mean_const_mul,ProbabilityVector.mean_const_mul]
      rfl

theorem dyadicBlock_secondMoment_reference_reduction (H : HoldingFamily ι) (m : ℕ) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M : ℝ) (hM : 1 ≤ M) (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ H.sampling w)
    (hwp : ∀ i, w i ≤ 2*H.sampling i) (offset n : ℕ)
    (hnκ : ((n:ℝ)+1)*DyadicRate.base m ≤ 1/8) :
    (dyadicBlockLaw H m R loss hloss M hM offset n).mean (fun outcome ↦
      w.squareNorm (dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome)) ≤
        (86/3)*probingEnergy H m loss offset (n+1)/DyadicRate.base m+
          (4/3)*referenceErrorEnergy H w m Ψ loss offset n := by
  have hd := dyadicBlock_secondMoment_decomposition_le H m R Ψ loss hloss M hM w hcal offset n
  have hb := centeredBlockMean_paid H w hwp m loss offset n hnκ
  change w.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1)) ≤
    18*probingEnergy H m loss offset (n+1)/DyadicRate.base m at hb
  have hc := averagedChunkMeanSquares_paid H w hwp m loss offset n
  calc
    _ ≤ w.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1))+
        (4/3)*referenceErrorEnergy H w m Ψ loss offset n+(1/3)*averagedChunkMeanSquares H w m loss offset n := hd
    _ ≤ 18*probingEnergy H m loss offset (n+1)/DyadicRate.base m+
        (4/3)*referenceErrorEnergy H w m Ψ loss offset n+
        (1/3)*(32*probingEnergy H m loss offset (n+1)/DyadicRate.base m) :=
      add_le_add (add_le_add hb le_rfl) (mul_le_mul_of_nonneg_left hc (by norm_num))
    _ = _ := by ring

end
end Tournament.Upper

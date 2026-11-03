module

public import Tournament.Probability.ChunkPairs
public import Tournament.Upper.BlockLossResponse

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def probingPair (P : FiniteKernel ι) (p : ProbabilityVector ι) (loss : ℕ → ι → ℝ)
    (t u : ℕ) : ℝ :=
  FiniteKernel.weightedInner p (loss t)
    (fun i ↦ ((P.act)^[u-t-1]) (loss u) i - P.act (((P.act)^[u-t-1]) (loss u)) i)

theorem chunkGain_eq_orderedPairSum (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    chunkGain P p loss offset n = Restarts.orderedPairSum (probingPair P p loss) offset (n+1) := by
  unfold chunkGain probingGain Restarts.orderedPairSum
  conv_rhs => rw [Finset.sum_range_succ]
  have hlast : (∑ u ∈ Finset.range (n+1),
      if n<u then probingPair P p loss (offset+n) (offset+u) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [ite_eq_right (by have := Finset.mem_range.mp hu; omega)]
  rw [hlast,add_zero]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  unfold probingPair
  have hdiff : (offset+u)-(offset+t)-1=u-t-1 := by omega
  rw [hdiff]

def fixedRateProbingGain (P : FiniteKernel ι) (p : ProbabilityVector ι) (loss : ℕ → ι → ℝ)
    (τ : ℝ) (offset h : ℕ) : ℝ :=
  ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
    if t<u then (1-τ)^(u-t)*probingPair P p loss (offset+t) (offset+u) else 0

theorem chunkGain_mean_eq (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (loss : ℕ → ι → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n offset : ℕ) :
    Restarts.chunkSumMean τ hτ hτ1 (chunkGain P p loss) n offset =
      fixedRateProbingGain P p loss τ offset (n+1) := by
  have heq : chunkGain P p loss =
      (fun start k ↦ Restarts.orderedPairSum (probingPair P p loss) start (k+1)) := by
    funext start k
    exact chunkGain_eq_orderedPairSum P p loss start k
  rw [heq,Restarts.chunkSumMean_orderedPairSum]
  rfl

def blockProbingGain (H : HoldingFamily ι) (m : ℕ) (loss : ℕ → ι → ℝ)
    (offset h : ℕ) : ℝ :=
  (DyadicRate.law m).mean (fun j ↦ fixedRateProbingGain
    (H.kernel (DyadicRate.rate m j) (DyadicRate.rate_pos m j)) H.sampling loss
    (DyadicRate.rate m j) offset h)

theorem partitioned_block_loss_gain_bound (H : HoldingFamily ι) {F : ι → ι → Prop}
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlog : 100*Real.log (2/δ) ≤ M)
    (default : ι) (offset n : ℕ) :
    (partitionedBlockLaw R loss hloss M hM τ (le_of_lt hτ) hτ1 offset n).mean
      (fun outcome ↦ Model.accumulatedLoss (n+1) (fun t ↦ loss (offset+t))
        (blockActions default (Restarts.parts n outcome.1) outcome.2)) ≤
      H.sampling.mean (blockLoss (fun t ↦ loss (offset+t)) (n+1)) -
        ScoreRule.steeringStrength M*fixedRateProbingGain (H.kernel τ hτ) H.sampling loss τ offset (n+1)+
        ScoreRule.steeringStrength M*δ*((n:ℝ)+1)^3 := by
  have h := partitioned_block_loss_bound H hτ hτ1 R loss hloss M hM δ hδ hδ1 hMlog default offset n
  rwa [chunkGain_mean_eq] at h

theorem dyadic_block_loss_bound (H : HoldingFamily ι) {F : ι → ι → Prop}
    (m : ℕ) (R : DyadicScoreRules H F m) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlog : 100*Real.log (2/δ) ≤ M)
    (default : ι) (offset n : ℕ) :
    (dyadicBlockLaw H m R loss hloss M hM offset n).mean
      (fun outcome ↦ Model.accumulatedLoss (n+1) (fun t ↦ loss (offset+t))
        (blockActions default (Restarts.parts n outcome.2.1) outcome.2.2)) ≤
      H.sampling.mean (blockLoss (fun t ↦ loss (offset+t)) (n+1)) -
        ScoreRule.steeringStrength M*blockProbingGain H m loss offset (n+1)+
        ScoreRule.steeringStrength M*δ*((n:ℝ)+1)^3 := by
  change ((DyadicRate.law m).sigmaJoint (fun j ↦ partitionedBlockLaw (R j) loss hloss M hM
    (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) offset n)).mean
      (fun outcome : (_j : Fin (m+1)) × (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins) ↦
        Model.accumulatedLoss (n+1) (fun t ↦ loss (offset+t))
          (blockActions default (Restarts.parts n outcome.2.1) outcome.2.2)) ≤ _
  rw [ProbabilityVector.sigmaJoint_mean]
  calc
    _ ≤ (DyadicRate.law m).mean (fun j ↦
        H.sampling.mean (blockLoss (fun t ↦ loss (offset+t)) (n+1)) -
          ScoreRule.steeringStrength M*fixedRateProbingGain
            (H.kernel (DyadicRate.rate m j) (DyadicRate.rate_pos m j)) H.sampling loss
            (DyadicRate.rate m j) offset (n+1)+ScoreRule.steeringStrength M*δ*((n:ℝ)+1)^3) := by
      apply ProbabilityVector.mean_mono
      intro j
      exact partitioned_block_loss_gain_bound H (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j)
        (R j) loss hloss M hM δ hδ hδ1 hMlog default offset n
    _ = _ := by
      rw [ProbabilityVector.mean_add,ProbabilityVector.mean_sub,ProbabilityVector.mean_const,
        ProbabilityVector.mean_const,ProbabilityVector.mean_const_mul]
      rfl

end
end Tournament.Upper

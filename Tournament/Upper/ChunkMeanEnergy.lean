module

public import Tournament.Upper.BlockMeanEnergy

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

namespace Restarts

theorem chunkSum_finset_sum {J : Type*} (s : Finset J) (q : J → ℕ → ℕ → ℝ) (ns : List ℕ) (offset : ℕ) :
    chunkSum (fun start n ↦ ∑ j ∈ s, q j start n) offset ns=∑ j ∈ s, chunkSum (q j) offset ns := by
  induction ns generalizing offset with
  | nil => simp [chunkSum]
  | cons n ns ih =>
    change (∑ j ∈ s, q j offset n)+chunkSum (fun start k ↦ ∑ j ∈ s, q j start k) (offset+(n+1)) ns =
      ∑ j ∈ s, (q j offset n+chunkSum (q j) (offset+(n+1)) ns)
    rw [ih,Finset.sum_add_distrib]

end Restarts

namespace Upper

def chunkVariance (p : ProbabilityVector ι) (loss : ℕ → ι → ℝ) (offset : ℕ) (ns : List ℕ) : ℝ :=
  Restarts.chunkSum (fun start n ↦ p.variance (blockLoss (fun t ↦ loss (start+t)) (n+1))) offset ns

def partitionedChunkVariance (p : ProbabilityVector ι) (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) : ℝ :=
  (Restarts.law τ hτ hτ1 n).mean (fun coins ↦ chunkVariance p loss offset (Restarts.parts n coins))

def averagedChunkMeanSquares (_H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) : ℝ :=
  (DyadicRate.law m).mean (fun j ↦ partitionedChunkVariance w (DyadicRate.rate m j)
    (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) loss offset n)

theorem chunkVariance_coordinates (H : HoldingFamily ι) (loss : ℕ → ι → ℝ) (offset : ℕ) (ns : List ℕ) :
    chunkVariance H.sampling loss offset ns=
      ∑ j : H.CenteredIndex, Restarts.chunkSquareSum (fun t ↦ H.coordinate (loss t) j) offset ns := by
  have hfun : (fun start n ↦ H.sampling.variance (blockLoss (fun t ↦ loss (start+t)) (n+1))) =
      (fun start n ↦ ∑ j : H.CenteredIndex, (∑ t ∈ Finset.range (n+1), H.coordinate (loss (start+t)) j)^2) := by
    funext start n
    rw [H.variance_coordinates]
    apply Finset.sum_congr rfl
    intro j _
    rw [H.coordinate_blockLoss]
  unfold chunkVariance
  rw [hfun,Restarts.chunkSum_finset_sum]
  rfl

theorem partitionedChunkVariance_coordinates (H : HoldingFamily ι) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    partitionedChunkVariance H.sampling τ hτ hτ1 loss offset n=
      ∑ j : H.CenteredIndex, GeometricPartition.quadratic (1-τ) (fun t ↦ H.coordinate (loss t) j) offset (n+1) := by
  have hfun : (fun coins : Restarts.Coins n ↦ chunkVariance H.sampling loss offset (Restarts.parts n coins)) =
      (fun coins ↦ ∑ j : H.CenteredIndex, Restarts.chunkSquareSum (fun t ↦ H.coordinate (loss t) j) offset (Restarts.parts n coins)) := by
    funext coins
    exact chunkVariance_coordinates H loss offset (Restarts.parts n coins)
  unfold partitionedChunkVariance
  rw [hfun,ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hi := GeometricPartition.quadratic_eq_mean_chunkSquares (sub_nonneg.mpr hτ1)
    (by linarith : 1-τ ≤ 1) (fun t ↦ H.coordinate (loss t) j) offset n
  have ht : 1-(1-τ)=τ := by ring
  simpa only [ht] using hi.symm

theorem chunk_mean_coordinate_paid {κ τ α : ℝ} (hκ : 0 < κ) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1)
    (hα : 1/2 ≤ α) (y : ℕ → ℝ) (offset h : ℕ) :
    GeometricPartition.quadratic (1-τ) y offset h ≤
      (16/κ)*(energyWeight τ α*GeometricPartition.quadratic (spectralCorrelation τ α) y offset h) := by
  have hτ : 0 < τ := lt_of_lt_of_le hκ hκτ
  have hα0 : 0 ≤ α := by linarith
  have hχ := spectralCorrelation_bounds hτ hτ1 hα0
  have hν := eigenMultiplier_bounds (le_of_lt hτ) hα0
  have hχle : spectralCorrelation τ α ≤ 1-τ := by
    change (1-τ)*eigenMultiplier τ α ≤ 1-τ
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hν.2 (sub_nonneg.mpr hτ1)
  have hcomp := GeometricPartition.quadratic_comparison hχ.1 hχle (by linarith : 1-τ < 1) y offset h
  rw [one_sub_correlation (le_of_lt hτ) hα0] at hcomp
  have ht : 1-(1-τ)=τ := by ring
  rw [ht] at hcomp
  have hψ := cutProbability_div_eight_le_energyWeight hτ hτ1 hα
  have hψ0 := energyWeight_nonneg (le_of_lt hτ) hα0
  have hcoef : 2*cutProbability τ α/τ ≤ 16*energyWeight τ α/κ := by
    apply (div_le_div_iff₀ hτ hκ).mpr
    have hm := mul_le_mul_of_nonneg_right hκτ (show 0 ≤ 16*energyWeight τ α by positivity)
    have hc := mul_le_mul_of_nonneg_left hψ (le_of_lt hκ)
    nlinarith
  have hQ := GeometricPartition.quadratic_nonneg hχ.1 (le_of_lt hχ.2) y offset h
  calc
    _ ≤ (2*cutProbability τ α/τ)*GeometricPartition.quadratic (spectralCorrelation τ α) y offset h := hcomp
    _ ≤ (16*energyWeight τ α/κ)*GeometricPartition.quadratic (spectralCorrelation τ α) y offset h :=
      mul_le_mul_of_nonneg_right hcoef hQ
    _ = _ := by ring

theorem partitionedChunkVariance_paid (H : HoldingFamily ι) {κ τ : ℝ}
    (hκ : 0 < κ) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1) (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    partitionedChunkVariance H.sampling τ (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 loss offset n ≤
      (16/κ)*fixedProbingEnergy H τ loss offset (n+1) := by
  rw [partitionedChunkVariance_coordinates]
  unfold fixedProbingEnergy
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  exact chunk_mean_coordinate_paid hκ hκτ hτ1 (H.eigenvalue_bounds j).1
    (fun t ↦ H.coordinate (loss t) j) offset (n+1)

theorem chunkVariance_domination (w p : ProbabilityVector ι) (hwp : ∀ i, w i ≤ 2*p i)
    (loss : ℕ → ι → ℝ) (offset : ℕ) (ns : List ℕ) :
    chunkVariance w loss offset ns ≤ 2*chunkVariance p loss offset ns := by
  calc
    _ ≤ Restarts.chunkSum (fun start n ↦ 2*p.variance (blockLoss (fun t ↦ loss (start+t)) (n+1))) offset ns := by
      exact Restarts.chunkSum_mono _ _
        (fun start n ↦ w.variance_le_mul_variance p (blockLoss (fun t ↦ loss (start+t)) (n+1)) 2 (by norm_num) hwp) ns offset
    _ = _ := by rw [Restarts.chunkSum_const_mul]; rfl

theorem partitionedChunkMeanSquares_paid (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (hwp : ∀ i, w i ≤ 2*H.sampling i) {κ τ : ℝ}
    (hκ : 0 < κ) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1) (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    partitionedChunkVariance w τ (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 loss offset n ≤
      (32/κ)*fixedProbingEnergy H τ loss offset (n+1) := by
  calc
    _ ≤ (Restarts.law τ (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 n).mean
        (fun coins ↦ 2*chunkVariance H.sampling loss offset (Restarts.parts n coins)) :=
      ProbabilityVector.mean_mono _ (fun coins ↦ chunkVariance_domination w H.sampling hwp loss offset (Restarts.parts n coins))
    _ = 2*partitionedChunkVariance H.sampling τ (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 loss offset n := by
      rw [ProbabilityVector.mean_const_mul]
      rfl
    _ ≤ 2*((16/κ)*fixedProbingEnergy H τ loss offset (n+1)) :=
      mul_le_mul_of_nonneg_left (partitionedChunkVariance_paid H hκ hκτ hτ1 loss offset n) (by norm_num)
    _ = _ := by ring

theorem averagedChunkMeanSquares_paid (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (hwp : ∀ i, w i ≤ 2*H.sampling i) (m : ℕ) (loss : ℕ → ι → ℝ) (offset n : ℕ) :
    averagedChunkMeanSquares H w m loss offset n ≤ 32*probingEnergy H m loss offset (n+1)/DyadicRate.base m := by
  calc
    _ ≤ (DyadicRate.law m).mean (fun j ↦ (32/DyadicRate.base m)*fixedProbingEnergy H (DyadicRate.rate m j) loss offset (n+1)) :=
      ProbabilityVector.mean_mono _ (fun j ↦ partitionedChunkMeanSquares_paid H w hwp
        (DyadicRate.base_pos m) (DyadicRate.base_le_rate m j) (DyadicRate.rate_le_one m j) loss offset n)
    _ = _ := by
      rw [ProbabilityVector.mean_const_mul]
      change (32/DyadicRate.base m)*probingEnergy H m loss offset (n+1)=
        32*probingEnergy H m loss offset (n+1)/DyadicRate.base m
      ring

end Upper
end
end Tournament

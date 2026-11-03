module

public import Tournament.Upper.ProbingEnergy

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

namespace Upper

theorem energy_coefficient_lower {κ τ α : ℝ} (hκ : 0 < κ) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1)
    (hα : 1/2 ≤ α) (n : ℕ) (hnκ : ((n:ℝ)+1)*κ ≤ 1/8) :
    κ/9 ≤ energyWeight τ α/(1+cutProbability τ α*(n:ℝ)) := by
  have hτ : 0 < τ := lt_of_lt_of_le hκ hκτ
  have hτ0 := le_of_lt hτ
  have hα0 : 0 ≤ α := by linarith
  let b := cutProbability τ α
  have hb : 0 ≤ b := le_trans hτ0 (rate_le_cutProbability hτ0 hτ1 hα0)
  have hκb : κ ≤ b := le_trans hκτ (rate_le_cutProbability hτ0 hτ1 hα0)
  have hψ : b/8 ≤ energyWeight τ α := cutProbability_div_eight_le_energyWeight hτ hτ1 hα
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hκden : 0 < 8*(1+κ*((n:ℝ)+1)) := by positivity
  have hbden : 0 < 8*(1+b*((n:ℝ)+1)) := by positivity
  have hbn : 0 < 1+b*(n:ℝ) := by positivity
  calc
    κ/9 ≤ κ/(8*(1+κ*((n:ℝ)+1))) := by
      apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<9) hκden).mpr
      have hd : 8*(1+κ*((n:ℝ)+1)) ≤ 9 := by nlinarith
      exact mul_le_mul_of_nonneg_left hd (le_of_lt hκ)
    _ ≤ b/(8*(1+b*((n:ℝ)+1))) := by
      apply (div_le_div_iff₀ hκden hbden).mpr
      nlinarith
    _ ≤ (b/8)/(1+b*(n:ℝ)) := by
      apply (div_le_div_iff₀ hbden hbn).mpr
      nlinarith [sq_nonneg b]
    _ ≤ energyWeight τ α/(1+b*(n:ℝ)) :=
      div_le_div_of_nonneg_right hψ (le_of_lt hbn)

theorem energy_coordinate_total_lower {κ τ α : ℝ} (hκ : 0 < κ) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1)
    (hα : 1/2 ≤ α) (n : ℕ) (hnκ : ((n:ℝ)+1)*κ ≤ 1/8) (y : ℕ → ℝ) (offset : ℕ) :
    (κ/9)*(∑ t ∈ Finset.range (n+1), y (offset+t))^2 ≤
      energyWeight τ α*GeometricPartition.quadratic (spectralCorrelation τ α) y offset (n+1) := by
  have hτ : 0 < τ := lt_of_lt_of_le hκ hκτ
  have hα0 : 0 ≤ α := by linarith
  have hχ := spectralCorrelation_bounds hτ hτ1 hα0
  have hpart := GeometricPartition.constant_vector_lower hχ.1 (le_of_lt hχ.2) y offset n
  rw [one_sub_correlation (le_of_lt hτ) hα0] at hpart
  have hcoef := energy_coefficient_lower hκ hκτ hτ1 hα n hnκ
  have hleft := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (∑ t ∈ Finset.range (n+1), y (offset+t)))
  have hright := mul_le_mul_of_nonneg_left hpart (energyWeight_nonneg (le_of_lt hτ) hα0)
  calc
    _ ≤ (energyWeight τ α/(1+cutProbability τ α*(n:ℝ)))*
        (∑ t ∈ Finset.range (n+1), y (offset+t))^2 := hleft
    _ = energyWeight τ α*((∑ t ∈ Finset.range (n+1), y (offset+t))^2/
        (1+cutProbability τ α*(n:ℝ))) := by ring
    _ ≤ _ := hright

end Upper

namespace HoldingFamily

open FiniteKernel Upper

theorem coordinate_blockLoss (H : HoldingFamily ι) (loss : ℕ → ι → ℝ) (offset h : ℕ) (n : H.CenteredIndex) :
    H.coordinate (blockLoss (fun t ↦ loss (offset+t)) h) n=
      ∑ t ∈ Finset.range h, H.coordinate (loss (offset+t)) n := by
  unfold coordinate blockLoss
  rw [weightedInner_sum_right]

end HoldingFamily

namespace Upper

theorem fixedEnergy_dominates_block_variance (H : HoldingFamily ι) {κ τ : ℝ}
    (hκ : 0 < κ) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1) (loss : ℕ → ι → ℝ) (offset n : ℕ)
    (hnκ : ((n:ℝ)+1)*κ ≤ 1/8) :
    (κ/9)*H.sampling.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1)) ≤
      fixedProbingEnergy H τ loss offset (n+1) := by
  rw [H.variance_coordinates,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [H.coordinate_blockLoss]
  exact energy_coordinate_total_lower hκ hκτ hτ1 (H.eigenvalue_bounds j).1 n hnκ
    (fun t ↦ H.coordinate (loss t) j) offset

theorem energy_dominates_block_variance (H : HoldingFamily ι) (m : ℕ)
    (loss : ℕ → ι → ℝ) (offset n : ℕ) (hnκ : ((n:ℝ)+1)*DyadicRate.base m ≤ 1/8) :
    (DyadicRate.base m/9)*H.sampling.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1)) ≤
      probingEnergy H m loss offset (n+1) := by
  calc
    _ = (DyadicRate.law m).mean (fun _ ↦ (DyadicRate.base m/9)*
        H.sampling.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1))) := (ProbabilityVector.mean_const _ _).symm
    _ ≤ _ := ProbabilityVector.mean_mono _ (fun j ↦ fixedEnergy_dominates_block_variance H
      (DyadicRate.base_pos m) (DyadicRate.base_le_rate m j) (DyadicRate.rate_le_one m j) loss offset n hnκ)

theorem centeredBlockMean_paid (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (hwp : ∀ i, w i ≤ 2*H.sampling i) (m : ℕ) (loss : ℕ → ι → ℝ) (offset n : ℕ)
    (hnκ : ((n:ℝ)+1)*DyadicRate.base m ≤ 1/8) :
    w.squareNorm (w.center (blockLoss (fun t ↦ loss (offset+t)) (n+1))) ≤
      18*probingEnergy H m loss offset (n+1)/DyadicRate.base m := by
  change w.variance (blockLoss (fun t ↦ loss (offset+t)) (n+1)) ≤ _
  have he := energy_dominates_block_variance H m loss offset n hnκ
  have hv := w.variance_le_mul_variance H.sampling (blockLoss (fun t ↦ loss (offset+t)) (n+1)) 2 (by norm_num) hwp
  have hm := mul_le_mul_of_nonneg_left hv (le_of_lt (DyadicRate.base_pos m))
  apply (le_div_iff₀ (DyadicRate.base_pos m)).mpr
  nlinarith

end Upper
end
end Tournament

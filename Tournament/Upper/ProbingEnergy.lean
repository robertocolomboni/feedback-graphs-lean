module

public import Tournament.Upper.GainCoordinates
public import Tournament.Probability.PartitionThinning

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem energyWeight_nonneg {τ α : ℝ} (hτ : 0 ≤ τ) (hα : 0 ≤ α) : 0 ≤ energyWeight τ α := by
  unfold energyWeight
  positivity

theorem energyWeight_le_linear {τ α : ℝ} (hτ : 0 ≤ τ) (hα : 0 ≤ α) :
    energyWeight τ α ≤ τ*α/2 := by
  have hz : 0 ≤ τ*α := mul_nonneg hτ hα
  unfold energyWeight
  apply (div_le_div_iff₀ (by positivity : 0 < 2+τ*α) (by norm_num : (0:ℝ)<2)).mpr
  nlinarith [sq_nonneg (τ*α)]

def fixedProbingEnergy (H : HoldingFamily ι) (τ : ℝ) (loss : ℕ → ι → ℝ) (offset h : ℕ) : ℝ :=
  ∑ n, energyWeight τ (H.eigenvalue n)*GeometricPartition.quadratic
    (spectralCorrelation τ (H.eigenvalue n)) (fun t ↦ H.coordinate (loss t) n) offset h

def fixedProbingDiagonal (H : HoldingFamily ι) (τ : ℝ) (loss : ℕ → ι → ℝ) (offset h : ℕ) : ℝ :=
  ∑ n, energyWeight τ (H.eigenvalue n)*(∑ t ∈ Finset.range h, (H.coordinate (loss (offset+t)) n)^2)

def probingEnergy (H : HoldingFamily ι) (m : ℕ) (loss : ℕ → ι → ℝ) (offset h : ℕ) : ℝ :=
  (DyadicRate.law m).mean (fun j ↦ fixedProbingEnergy H (DyadicRate.rate m j) loss offset h)

def probingDiagonal (H : HoldingFamily ι) (m : ℕ) (loss : ℕ → ι → ℝ) (offset h : ℕ) : ℝ :=
  (DyadicRate.law m).mean (fun j ↦ fixedProbingDiagonal H (DyadicRate.rate m j) loss offset h)

theorem fixedEnergy_eq_diagonal_add_twice_gain (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    (loss : ℕ → ι → ℝ) (offset h : ℕ) :
    fixedProbingEnergy H τ loss offset h=fixedProbingDiagonal H τ loss offset h+
      2*fixedRateProbingGain (H.kernel τ hτ) H.sampling loss τ offset h := by
  rw [fixedRateGain_coordinates H hτ]
  unfold fixedProbingEnergy fixedProbingDiagonal spectralGain
  simp_rw [GeometricPartition.quadratic_eq_diagonal_pairs]
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem energy_eq_diagonal_add_twice_gain (H : HoldingFamily ι) (m : ℕ)
    (loss : ℕ → ι → ℝ) (offset h : ℕ) :
    probingEnergy H m loss offset h=probingDiagonal H m loss offset h+2*blockProbingGain H m loss offset h := by
  have hfun : (fun j : Fin (m+1) ↦ fixedProbingEnergy H (DyadicRate.rate m j) loss offset h) =
      (fun j ↦ fixedProbingDiagonal H (DyadicRate.rate m j) loss offset h+
        2*fixedRateProbingGain (H.kernel (DyadicRate.rate m j) (DyadicRate.rate_pos m j)) H.sampling loss
          (DyadicRate.rate m j) offset h) := by
    funext j
    exact fixedEnergy_eq_diagonal_add_twice_gain H (DyadicRate.rate_pos m j) loss offset h
  unfold probingEnergy probingDiagonal blockProbingGain
  rw [hfun,ProbabilityVector.mean_add,ProbabilityVector.mean_const_mul]

theorem gain_energy_identity (H : HoldingFamily ι) (m : ℕ) (loss : ℕ → ι → ℝ) (offset h : ℕ) :
    2*blockProbingGain H m loss offset h=probingEnergy H m loss offset h-probingDiagonal H m loss offset h := by
  have h := energy_eq_diagonal_add_twice_gain H m loss offset h
  linarith

theorem fixedProbingEnergy_nonneg (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (loss : ℕ → ι → ℝ) (offset h : ℕ) : 0 ≤ fixedProbingEnergy H τ loss offset h := by
  apply Finset.sum_nonneg
  intro n _
  have hα : 0 ≤ H.eigenvalue n := by have := (H.eigenvalue_bounds n).1; linarith
  have hχ := spectralCorrelation_bounds hτ hτ1 hα
  exact mul_nonneg (energyWeight_nonneg (le_of_lt hτ) hα)
    (GeometricPartition.quadratic_nonneg hχ.1 (le_of_lt hχ.2) (fun t ↦ H.coordinate (loss t) n) offset h)

theorem probingEnergy_nonneg (H : HoldingFamily ι) (m : ℕ) (loss : ℕ → ι → ℝ) (offset h : ℕ) :
    0 ≤ probingEnergy H m loss offset h := by
  exact ProbabilityVector.mean_nonneg _ (fun j ↦ fixedProbingEnergy_nonneg H
    (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j) loss offset h)

theorem fixedProbingDiagonal_nonneg (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 ≤ τ)
    (loss : ℕ → ι → ℝ) (offset h : ℕ) : 0 ≤ fixedProbingDiagonal H τ loss offset h := by
  apply Finset.sum_nonneg
  intro n _
  have hα : 0 ≤ H.eigenvalue n := by have := (H.eigenvalue_bounds n).1; linarith
  exact mul_nonneg (energyWeight_nonneg hτ hα) (Finset.sum_nonneg (fun t _ ↦ sq_nonneg _))

theorem fixedProbingDiagonal_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 ≤ τ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (offset h : ℕ) :
    fixedProbingDiagonal H τ loss offset h ≤ (h:ℝ)*τ/8 := by
  unfold fixedProbingDiagonal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ t ∈ Finset.range h, (τ/2)*(∑ n, H.eigenvalue n*(H.coordinate (loss (offset+t)) n)^2) := by
      apply Finset.sum_le_sum
      intro t _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      have hα : 0 ≤ H.eigenvalue n := by have := (H.eigenvalue_bounds n).1; linarith
      have hw := mul_le_mul_of_nonneg_right (energyWeight_le_linear hτ hα)
        (sq_nonneg (H.coordinate (loss (offset+t)) n))
      convert hw using 1
      ring
    _ ≤ ∑ _t ∈ Finset.range h, τ/8 := by
      apply Finset.sum_le_sum
      intro t _
      have hm := mul_le_mul_of_nonneg_left (H.bounded_weighted_coordinates_le_quarter (loss (offset+t)) (hloss (offset+t)))
        (show 0 ≤ τ/2 by positivity)
      convert hm using 1
      ring
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

theorem probingDiagonal_bounds (H : HoldingFamily ι) (m : ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (offset h : ℕ) :
    0 ≤ probingDiagonal H m loss offset h ∧
      probingDiagonal H m loss offset h ≤ (DyadicRate.base m*(1+(m:ℝ)/2))*(h:ℝ)/8 := by
  constructor
  · exact ProbabilityVector.mean_nonneg _ (fun j ↦ fixedProbingDiagonal_nonneg H
      (le_of_lt (DyadicRate.rate_pos m j)) loss offset h)
  · calc
      _ ≤ (DyadicRate.law m).mean (fun j ↦ (h:ℝ)*DyadicRate.rate m j/8) :=
        ProbabilityVector.mean_mono _ (fun j ↦ fixedProbingDiagonal_le H
          (le_of_lt (DyadicRate.rate_pos m j)) loss hloss offset h)
      _ = _ := by
        rw [ProbabilityVector.mean_div_const,ProbabilityVector.mean_const_mul,DyadicRate.mean_rate]
        ring

theorem gain_energy_bounds (H : HoldingFamily ι) (m : ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (offset h : ℕ) :
    probingEnergy H m loss offset h ≤ 2*(blockProbingGain H m loss offset h+
      (DyadicRate.base m*(1+(m:ℝ)/2))*(h:ℝ)/16) ∧
    -(DyadicRate.base m*(1+(m:ℝ)/2))*(h:ℝ)/16 ≤ blockProbingGain H m loss offset h := by
  have hid := gain_energy_identity H m loss offset h
  have hQ := probingEnergy_nonneg H m loss offset h
  have hd := probingDiagonal_bounds H m loss hloss offset h
  constructor <;> nlinarith

end
end Tournament.Upper

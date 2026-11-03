module

public import Tournament.Upper.LinearErrorMaps
public import Tournament.Probability.QuadraticSums

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open FiniteKernel Upper

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem vectorQuadratic_centered_coordinates (H : HoldingFamily ι) (χ : ℝ) (f : ℕ → ι → ℝ)
    (hcenter : ∀ t, H.sampling.mean (f t)=0) (offset h : ℕ) :
    GeometricPartition.vectorQuadratic H.sampling χ f offset h=
      ∑ n, GeometricPartition.quadratic χ (fun t ↦ H.coordinate (f t) n) offset h := by
  unfold GeometricPartition.vectorQuadratic GeometricPartition.quadratic
  calc
    _ = ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h, ∑ n,
        χ^(Nat.dist t u)*H.coordinate (f (offset+t)) n*H.coordinate (f (offset+u)) n := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro u _
      rw [H.inner_coordinates,hcenter,zero_mul,zero_add,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ ↦ by ring)
    _ = ∑ t ∈ Finset.range h, ∑ n, ∑ u ∈ Finset.range h,
        χ^(Nat.dist t u)*H.coordinate (f (offset+t)) n*H.coordinate (f (offset+u)) n := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem quadratic_bandProject_coordinate (H : HoldingFamily ι) (χ : ℝ) (b : ℕ)
    (f : ℕ → ι → ℝ) (n : H.CenteredIndex) (offset h : ℕ) :
    GeometricPartition.quadratic χ (fun t ↦ H.coordinate (H.bandProject b (f t)) n) offset h=
      if H.inBand b n then GeometricPartition.quadratic χ (fun t ↦ H.coordinate (f t) n) offset h else 0 := by
  by_cases hn : H.inBand b n
  · simp only [H.bandProject_coordinate,ite_eq_left hn]
  · simp only [H.bandProject_coordinate,ite_eq_right hn,GeometricPartition.quadratic_zero_input]

theorem bandProject_vectorQuadratic (H : HoldingFamily ι) (χ : ℝ) (b : ℕ)
    (f : ℕ → ι → ℝ) (offset h : ℕ) :
    GeometricPartition.vectorQuadratic H.sampling χ (fun t ↦ H.bandProject b (f t)) offset h=
      ∑ n, if H.inBand b n then GeometricPartition.quadratic χ (fun t ↦ H.coordinate (f t) n) offset h else 0 := by
  rw [H.vectorQuadratic_centered_coordinates χ _ (fun t ↦ H.bandProject_centered b (f t))]
  exact Finset.sum_congr rfl (fun n _ ↦ H.quadratic_bandProject_coordinate χ b f n offset h)

end
end Tournament.HoldingFamily

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def vectorAveragedCovariance (p : ProbabilityVector ι) (m : ℕ) (α : ℝ) (f : ℕ → ι → ℝ) (offset h : ℕ) : ℝ :=
  (DyadicRate.law m).mean (fun j ↦ GeometricPartition.vectorQuadratic p (spectralCorrelation (DyadicRate.rate m j) α) f offset h)

def vectorAveragedGain (p : ProbabilityVector ι) (m : ℕ) (α : ℝ) (f : ℕ → ι → ℝ) (offset h : ℕ) : ℝ :=
  (DyadicRate.law m).mean (fun j ↦ cutProbability (DyadicRate.rate m j) α*
    GeometricPartition.vectorQuadratic p (spectralCorrelation (DyadicRate.rate m j) α) f offset h)

theorem vectorAveragedCovariance_coordinates (p : ProbabilityVector ι) (m : ℕ) (α : ℝ)
    (f : ℕ → ι → ℝ) (offset h : ℕ) :
    vectorAveragedCovariance p m α f offset h=∑ i, p i*averagedCovariance m α (fun t ↦ f t i) offset h := by
  unfold vectorAveragedCovariance
  simp_rw [GeometricPartition.vectorQuadratic_coordinates]
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ProbabilityVector.mean_const_mul]
  rfl

theorem vectorAveragedGain_coordinates (p : ProbabilityVector ι) (m : ℕ) (α : ℝ)
    (f : ℕ → ι → ℝ) (offset h : ℕ) :
    vectorAveragedGain p m α f offset h=∑ i, p i*averagedGain m α (fun t ↦ f t i) offset h := by
  unfold vectorAveragedGain
  simp_rw [GeometricPartition.vectorQuadratic_coordinates,Finset.mul_sum]
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold averagedGain temporalGain
  rw [← ProbabilityVector.mean_const_mul]
  congr 1
  funext j
  ring

theorem averagedCovariance_within_band (m b : ℕ) {α : ℝ}
    (hlo : bandValue b≤α) (hhi : α<2*bandValue b) (y : ℕ → ℝ) (offset h : ℕ) :
    averagedCovariance m α y offset h≤4*averagedCovariance m (2*bandValue b) y offset h := by
  unfold averagedCovariance
  rw [← ProbabilityVector.mean_const_mul]
  exact ProbabilityVector.mean_mono _ (fun j ↦ within_band_covariance_le
    (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j) (le_of_lt (bandValue_pos b)) hlo (le_of_lt hhi) y offset h)

theorem referenceErrorEnergy_averaged_coordinates (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (Ψ : ι → ι → ι → ℝ) (hcal : EstimatorCalibration Ψ H.sampling w)
    (f : ℕ → ι → ℝ) (offset n : ℕ) :
    referenceErrorEnergy H w m Ψ f offset n=
      ∑ i, w i*(∑ j, averagedCovariance m (H.eigenvalue j)
        (fun t ↦ H.coordinate (sourceError Ψ w i (f t)) j) offset (n+1)) := by
  rw [referenceErrorEnergy_coordinates H m Ψ w hcal]
  unfold referenceCovariance
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ProbabilityVector.mean_const_mul,ProbabilityVector.mean_sum]
  rfl

theorem vectorAveragedCovariance_bandProject (H : HoldingFamily ι) (m : ℕ) (α : ℝ) (b : ℕ)
    (f : ℕ → ι → ℝ) (offset h : ℕ) :
    vectorAveragedCovariance H.sampling m α (fun t ↦ H.bandProject b (f t)) offset h=
      ∑ n, if H.inBand b n then averagedCovariance m α (fun t ↦ H.coordinate (f t) n) offset h else 0 := by
  unfold vectorAveragedCovariance
  simp_rw [H.bandProject_vectorQuadratic]
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : H.inBand b n
  · simp only [ite_eq_left hn]
    rfl
  · simp only [ite_eq_right hn,ProbabilityVector.mean_const]

theorem referenceErrorEnergy_band_covariance_le (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (Ψ : ι → ι → ι → ℝ)
    (hcal : EstimatorCalibration Ψ H.sampling w) (f : ℕ → ι → ℝ) (offset n : ℕ) :
    referenceErrorEnergy H w m Ψ f offset n≤
      4*(∑ i, w i*(∑ b : Fin m, vectorAveragedCovariance H.sampling m (2*bandValue b.val)
        (fun t ↦ H.bandProject b.val (sourceError Ψ w i (f t))) offset (n+1))) := by
  rw [referenceErrorEnergy_averaged_coordinates H w m Ψ hcal,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hrange := H.eigenvalue_band_range m hmax
  have hbands := H.sum_band_restrictions m hrange
    (fun j ↦ averagedCovariance m (H.eigenvalue j) (fun t ↦ H.coordinate (sourceError Ψ w i (f t)) j) offset (n+1))
  have hlocal : (∑ j, averagedCovariance m (H.eigenvalue j)
      (fun t ↦ H.coordinate (sourceError Ψ w i (f t)) j) offset (n+1))≤
        4*(∑ b : Fin m, vectorAveragedCovariance H.sampling m (2*bandValue b.val)
          (fun t ↦ H.bandProject b.val (sourceError Ψ w i (f t))) offset (n+1)) := by
    rw [← hbands,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    rw [vectorAveragedCovariance_bandProject,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : H.inBand b.val j
    · rw [ite_eq_left hj,ite_eq_left hj]
      exact averagedCovariance_within_band m b.val hj.1 hj.2 _ offset (n+1)
    · rw [ite_eq_right hj,ite_eq_right hj,mul_zero]
  have hw := mul_le_mul_of_nonneg_left hlocal (w.nonneg i)
  convert hw using 1
  ring

theorem fixedProbingEnergy_band_sum (H : HoldingFamily ι) (m : ℕ)
    (hrange : ∀ j, H.eigenvalue j<bandValue m) (τ : ℝ) (f : ℕ → ι → ℝ) (offset h : ℕ) :
    (∑ b : Fin m, fixedProbingEnergy H τ (fun t ↦ H.bandProject b.val (f t)) offset h)=
      fixedProbingEnergy H τ f offset h := by
  unfold fixedProbingEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [H.quadratic_bandProject_coordinate,mul_ite,mul_zero]
  exact H.sum_band_indicator m hrange j _

theorem probingEnergy_band_sum (H : HoldingFamily ι) (m : ℕ)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (f : ℕ → ι → ℝ) (offset h : ℕ) :
    (∑ b : Fin m, probingEnergy H m (fun t ↦ H.bandProject b.val (f t)) offset h)=
      probingEnergy H m f offset h := by
  unfold probingEnergy
  rw [← ProbabilityVector.mean_sum]
  congr 1
  funext j
  exact fixedProbingEnergy_band_sum H m (H.eigenvalue_band_range m hmax) _ f offset h

end
end Tournament.Upper

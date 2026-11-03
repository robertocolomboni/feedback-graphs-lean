module

public import Tournament.Upper.TemporalBandBounds

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem fixed_band_gain_le_energy (H : HoldingFamily ι) {τ : ℝ} (hτ : 0<τ) (hτ1 : τ≤1)
    (c : ℕ) (f : ℕ → ι → ℝ) (hfixed : ∀ t, H.bandProject c (f t)=f t) (offset h : ℕ) :
    (1/16)*(cutProbability τ (bandValue c)*GeometricPartition.vectorQuadratic H.sampling
      (spectralCorrelation τ (bandValue c)) f offset h)≤fixedProbingEnergy H τ f offset h := by
  have hcenter : ∀ t, H.sampling.mean (f t)=0 := by
    intro t
    rw [← hfixed t,H.bandProject_centered]
  rw [← mul_assoc,H.vectorQuadratic_centered_coordinates _ f hcenter]
  unfold fixedProbingEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : H.inBand c j
  · exact within_band_energy_ge hτ hτ1 (bandValue_ge_half c) hj.1 _ offset h
  · have hzero : (fun t ↦ H.coordinate (f t) j)=(fun _ ↦ 0) := by
      funext t
      exact H.coordinate_zero_of_band_fixed c (f t) (hfixed t) j hj
    simp only [hzero,GeometricPartition.quadratic_zero_input,mul_zero]
    exact le_refl _

theorem band_gain_le_energy (H : HoldingFamily ι) (m c : ℕ) (f : ℕ → ι → ℝ)
    (hfixed : ∀ t, H.bandProject c (f t)=f t) (offset h : ℕ) :
    vectorAveragedGain H.sampling m (bandValue c) f offset h≤16*probingEnergy H m f offset h := by
  have hmean : (1/16)*vectorAveragedGain H.sampling m (bandValue c) f offset h≤probingEnergy H m f offset h := by
    unfold vectorAveragedGain probingEnergy
    rw [← ProbabilityVector.mean_const_mul]
    exact ProbabilityVector.mean_mono _ (fun j ↦ fixed_band_gain_le_energy H
      (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j) c f hfixed offset h)
  linarith

theorem reference_error_one_band (H : HoldingFamily ι) (w : ProbabilityVector ι) (m : ℕ)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (Ψ : ι → ι → ι → ℝ)
    (hcal : EstimatorCalibration Ψ H.sampling w) (L₀ : ℝ) (hL₀ : 0≤L₀)
    (hend : EstimatorEndpointBounds H w Ψ L₀) (c : Fin m) (f : ℕ → ι → ℝ)
    (hfixed : ∀ t, H.bandProject c.val (f t)=f t) (offset n : ℕ) :
    referenceErrorEnergy H w m Ψ f offset n≤
      (3072*L₀/DyadicRate.base m)*probingEnergy H m f offset (n+1) := by
  have htemporal := referenceErrorEnergy_band_gain_le H w m hmax Ψ hcal c f offset n
  have hspatial := band_gain_errors_le H w m hmax Ψ hcal L₀ hL₀ hend c f hfixed offset n
  have henergy := band_gain_le_energy H m c.val f hfixed offset (n+1)
  have hκ := DyadicRate.base_pos m
  calc
    _ ≤ _ := htemporal
    _ ≤ (48/DyadicRate.base m)*((4*L₀)*vectorAveragedGain H.sampling m (bandValue c.val) f offset (n+1)) :=
      mul_le_mul_of_nonneg_left hspatial (by positivity)
    _ ≤ (48/DyadicRate.base m)*((4*L₀)*(16*probingEnergy H m f offset (n+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy (by positivity)) (by positivity)
    _ = _ := by ring

end
end Tournament.Upper

module

public import Tournament.Upper.ProbingEnergy

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

theorem within_band_covariance_le {τ a α : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : 0 ≤ a) (haα : a ≤ α) (hα2a : α ≤ 2*a) (y : ℕ → ℝ) (offset h : ℕ) :
    GeometricPartition.quadratic (spectralCorrelation τ α) y offset h ≤
      4*GeometricPartition.quadratic (spectralCorrelation τ (2*a)) y offset h := by
  have hτ0 := le_of_lt hτ
  have hα : 0 ≤ α := le_trans ha haα
  have h2a : 0 ≤ 2*a := by positivity
  have hχ := spectralCorrelation_bounds hτ hτ1 hα
  have hχ2 := spectralCorrelation_bounds hτ hτ1 h2a
  have hc_lo := cutProbability_mono hτ0 hτ1 ha haα
  have hc_hi := cutProbability_mono hτ0 hτ1 hα hα2a
  have hc_double := cutProbability_double hτ0 hτ1 ha
  have hcpos : 0 < cutProbability τ α := lt_of_lt_of_le hτ (rate_le_cutProbability hτ0 hτ1 hα)
  have hχle : spectralCorrelation τ (2*a) ≤ spectralCorrelation τ α := by
    have h1 := one_sub_correlation hτ0 hα
    have h2 := one_sub_correlation hτ0 h2a
    linarith
  have hcomp := GeometricPartition.quadratic_comparison hχ2.1 hχle hχ.2 y offset h
  rw [one_sub_correlation hτ0 h2a,one_sub_correlation hτ0 hα] at hcomp
  have hratio : 2*cutProbability τ (2*a)/cutProbability τ α ≤ 4 := by
    apply (div_le_iff₀ hcpos).mpr
    linarith
  have hQ := GeometricPartition.quadratic_nonneg hχ2.1 (le_of_lt hχ2.2) y offset h
  exact le_trans hcomp (mul_le_mul_of_nonneg_right hratio hQ)

theorem within_band_energy_ge {τ a α : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : 1/2 ≤ a) (haα : a ≤ α) (y : ℕ → ℝ) (offset h : ℕ) :
    (1/16)*cutProbability τ a*GeometricPartition.quadratic (spectralCorrelation τ a) y offset h ≤
      energyWeight τ α*GeometricPartition.quadratic (spectralCorrelation τ α) y offset h := by
  have hτ0 := le_of_lt hτ
  have ha0 : 0 ≤ a := by linarith
  have hα0 : 0 ≤ α := le_trans ha0 haα
  have hαhalf : 1/2 ≤ α := le_trans ha haα
  have hχa := spectralCorrelation_bounds hτ hτ1 ha0
  have hχ := spectralCorrelation_bounds hτ hτ1 hα0
  have hc := cutProbability_mono hτ0 hτ1 ha0 haα
  have hcapos : 0 < cutProbability τ a := lt_of_lt_of_le hτ (rate_le_cutProbability hτ0 hτ1 ha0)
  have hχle : spectralCorrelation τ α ≤ spectralCorrelation τ a := by
    have h1 := one_sub_correlation hτ0 ha0
    have h2 := one_sub_correlation hτ0 hα0
    linarith
  have hcomp := GeometricPartition.quadratic_comparison hχ.1 hχle hχa.2 y offset h
  rw [one_sub_correlation hτ0 hα0,one_sub_correlation hτ0 ha0] at hcomp
  have hψ := cutProbability_div_eight_le_energyWeight hτ hτ1 hαhalf
  have hQ := GeometricPartition.quadratic_nonneg hχ.1 (le_of_lt hχ.2) y offset h
  calc
    _ = (cutProbability τ a/16)*GeometricPartition.quadratic (spectralCorrelation τ a) y offset h := by ring
    _ ≤ (cutProbability τ a/16)*((2*cutProbability τ α/cutProbability τ a)*
        GeometricPartition.quadratic (spectralCorrelation τ α) y offset h) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = (cutProbability τ α/8)*GeometricPartition.quadratic (spectralCorrelation τ α) y offset h := by
      field_simp [ne_of_gt hcapos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hψ hQ

end
end Tournament.Upper

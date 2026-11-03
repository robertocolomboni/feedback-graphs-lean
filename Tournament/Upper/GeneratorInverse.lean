module

public import Tournament.Upper.Coordinates

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open FiniteKernel

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem coordinate_center (H : HoldingFamily ι) (f : ι → ℝ) (n : H.CenteredIndex) :
    H.coordinate (H.sampling.center f) n=H.coordinate f n := by
  unfold coordinate weightedInner ProbabilityVector.center
  simp only [mul_sub,ProbabilityVector.mean_sub,ProbabilityVector.mean_mul_const,
    H.eigenvector_centered,zero_mul,sub_zero]

theorem generator_center (H : HoldingFamily ι) (f : ι → ℝ) :
    H.generator (H.sampling.center f)=H.generator f := by
  funext i
  unfold generator ProbabilityVector.center
  rw [ProbabilityVector.mean_sub,ProbabilityVector.mean_const]
  ring

def centeredGeneratorInverse (H : HoldingFamily ι) (g : ι → ℝ) : ι → ℝ :=
  H.sampling.center (fun s ↦ g s/H.ratio s)

theorem refresh_mean_div_ratio (H : HoldingFamily ι) (g : ι → ℝ) :
    H.refresh.mean (fun s ↦ g s/H.ratio s)=H.sampling.mean g := by
  unfold ProbabilityVector.mean
  apply Finset.sum_congr rfl
  intro s _
  rw [← H.weighted_ratio s]
  field_simp [ne_of_gt (H.ratio_pos s)]

theorem generator_centeredInverse (H : HoldingFamily ι) (g : ι → ℝ)
    (hg : H.sampling.mean g=0) : H.generator (H.centeredGeneratorInverse g)=g := by
  unfold centeredGeneratorInverse
  rw [H.generator_center]
  funext s
  unfold generator
  rw [H.refresh_mean_div_ratio,hg,sub_zero]
  exact mul_div_cancel₀ (g s) (ne_of_gt (H.ratio_pos s))

theorem centeredInverse_centered (H : HoldingFamily ι) (g : ι → ℝ) :
    H.sampling.mean (H.centeredGeneratorInverse g)=0 := H.sampling.mean_center _

theorem centeredInverse_coordinate (H : HoldingFamily ι) (g : ι → ℝ)
    (hg : H.sampling.mean g=0) (n : H.CenteredIndex) :
    H.coordinate (H.centeredGeneratorInverse g) n=H.coordinate g n/H.eigenvalue n := by
  have he := congrArg (fun f ↦ H.coordinate f n) (H.generator_centeredInverse g hg)
  rw [H.generator_coordinate] at he
  have hα : H.eigenvalue n≠0 := ne_of_gt (by have := (H.eigenvalue_bounds n).1; linarith)
  apply (eq_div_iff hα).mpr
  nlinarith

theorem centeredInverse_source_quadratic (H : HoldingFamily ι) (g : ι → ℝ)
    (hg : H.sampling.mean g=0) :
    weightedInner H.sampling g (H.centeredGeneratorInverse g)=
      ∑ s, (H.sampling s/H.ratio s)*(g s)^2 := by
  unfold centeredGeneratorInverse weightedInner ProbabilityVector.center
  simp only [mul_sub,ProbabilityVector.mean_sub,ProbabilityVector.mean_mul_const,hg,zero_mul,sub_zero]
  unfold ProbabilityVector.mean
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem centeredInverse_spectral_quadratic (H : HoldingFamily ι) (g : ι → ℝ)
    (hg : H.sampling.mean g=0) :
    weightedInner H.sampling g (H.centeredGeneratorInverse g)=
      ∑ n, (H.coordinate g n)^2/H.eigenvalue n := by
  rw [H.inner_coordinates,hg,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro n _
  rw [H.centeredInverse_coordinate g hg n]
  ring

theorem inverse_quadratic_coordinates (H : HoldingFamily ι) (g : ι → ℝ)
    (hg : H.sampling.mean g=0) :
    (∑ s, (H.sampling s/H.ratio s)*(g s)^2)=
      ∑ n, (H.coordinate g n)^2/H.eigenvalue n := by
  rw [← H.centeredInverse_source_quadratic g hg,H.centeredInverse_spectral_quadratic g hg]

end
end Tournament.HoldingFamily

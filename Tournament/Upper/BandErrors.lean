module

public import Tournament.Upper.BandPartition
public import Tournament.Upper.ReferenceCovariance

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FiniteKernel

noncomputable section

variable {ι : Type*} [Fintype ι]

def EstimatorEndpointBounds (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (Ψ : ι → ι → ι → ℝ) (L₀ : ℝ) : Prop :=
  ∀ f : ι → ℝ,
    (∑ s, (H.sampling s/H.ratio s)*w.squareNorm (estimationError Ψ w s f))≤L₀*H.sampling.variance f ∧
      (∑ s, H.sampling s*w.squareNorm (estimationError Ψ w s f))≤L₀*H.refresh.variance f

theorem sourceError_inverse_sum (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (Ψ : ι → ι → ι → ℝ) (hcal : EstimatorCalibration Ψ H.sampling w) (f : ι → ℝ) :
    (∑ i, w i*(∑ n, (H.coordinate (sourceError Ψ w i f) n)^2/H.eigenvalue n))=
      ∑ s, (H.sampling s/H.ratio s)*w.squareNorm (estimationError Ψ w s f) := by
  have hfun : ∀ i, (∑ n, (H.coordinate (sourceError Ψ w i f) n)^2/H.eigenvalue n)=
      ∑ s, (H.sampling s/H.ratio s)*(sourceError Ψ w i f s)^2 := by
    intro i
    exact (H.inverse_quadratic_coordinates _ (sourceError_centered Ψ H.sampling w hcal i f)).symm
  simp_rw [hfun,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [ProbabilityVector.squareNorm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold sourceError
  ring

theorem sourceError_coordinate_squareNorm (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (Ψ : ι → ι → ι → ℝ) (hcal : EstimatorCalibration Ψ H.sampling w) (f : ι → ℝ) (i : ι) :
    H.sampling.squareNorm (sourceError Ψ w i f)=∑ n, (H.coordinate (sourceError Ψ w i f) n)^2 := by
  calc
    _ = H.sampling.variance (sourceError Ψ w i f) := by
      rw [H.sampling.squareNorm_eq_variance_add_mean_sq,sourceError_centered Ψ H.sampling w hcal i f]
      ring
    _ = _ := H.variance_coordinates _

theorem sourceError_norm_sum (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (Ψ : ι → ι → ι → ℝ) (hcal : EstimatorCalibration Ψ H.sampling w) (f : ι → ℝ) :
    (∑ i, w i*(∑ n, (H.coordinate (sourceError Ψ w i f) n)^2))=
      ∑ s, H.sampling s*w.squareNorm (estimationError Ψ w s f) := by
  simp_rw [← sourceError_coordinate_squareNorm H w Ψ hcal f]
  unfold ProbabilityVector.squareNorm
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  unfold sourceError
  ring

theorem endpoint_spectral_bounds (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (Ψ : ι → ι → ι → ℝ) (hcal : EstimatorCalibration Ψ H.sampling w) (L₀ : ℝ)
    (hend : EstimatorEndpointBounds H w Ψ L₀) (f : ι → ℝ) :
    (∑ i, w i*(∑ n, (H.coordinate (sourceError Ψ w i f) n)^2/H.eigenvalue n))≤L₀*H.sampling.variance f ∧
      (∑ i, w i*(∑ n, (H.coordinate (sourceError Ψ w i f) n)^2))≤L₀*H.refresh.variance f := by
  rw [sourceError_inverse_sum H w Ψ hcal,sourceError_norm_sum H w Ψ hcal]
  exact hend f

theorem errors_caused_by_one_band (H : HoldingFamily ι) (m : ℕ)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (w : ProbabilityVector ι)
    (Ψ : ι → ι → ι → ℝ) (hcal : EstimatorCalibration Ψ H.sampling w)
    (L₀ : ℝ) (hL₀ : 0≤L₀) (hend : EstimatorEndpointBounds H w Ψ L₀)
    (c : Fin m) (g : ι → ℝ) (hg : H.sampling.mean g=0) (hfixed : H.bandProject c.val g=g) :
    (∑ i, w i*(∑ b : Fin m, (1/bandValue (min b.val c.val))*
      H.sampling.squareNorm (H.bandProject b.val (sourceError Ψ w i g))))≤
        4*L₀*H.sampling.squareNorm g := by
  have hrange := H.eigenvalue_band_range m hmax
  have hep := endpoint_spectral_bounds H w Ψ hcal L₀ hend g
  have hpvar : H.sampling.variance g=H.sampling.squareNorm g := by
    rw [H.sampling.squareNorm_eq_variance_add_mean_sq,hg]
    ring
  have hband := H.band_fixed_refresh_variance_le c.val g hfixed
  have hac := bandValue_pos c.val
  calc
    _ ≤ ∑ i, w i*(2*(∑ n, (H.coordinate (sourceError Ψ w i g) n)^2/H.eigenvalue n)+
        (1/bandValue c.val)*(∑ n, (H.coordinate (sourceError Ψ w i g) n)^2)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (H.band_weighted_squares_le m hrange c (sourceError Ψ w i g)) (w.nonneg i)
    _ = 2*(∑ i, w i*(∑ n, (H.coordinate (sourceError Ψ w i g) n)^2/H.eigenvalue n))+
        (1/bandValue c.val)*(∑ i, w i*(∑ n, (H.coordinate (sourceError Ψ w i g) n)^2)) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ 2*(L₀*H.sampling.variance g)+(1/bandValue c.val)*(L₀*H.refresh.variance g) :=
      add_le_add (mul_le_mul_of_nonneg_left hep.1 (by norm_num))
        (mul_le_mul_of_nonneg_left hep.2 (by positivity))
    _ ≤ 2*(L₀*H.sampling.squareNorm g)+
        (1/bandValue c.val)*(L₀*((2*bandValue c.val)*H.sampling.squareNorm g)) := by
      rw [hpvar]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hband hL₀) (by positivity))
    _ = _ := by
      field_simp [ne_of_gt hac]
      ring

end
end Tournament.Upper

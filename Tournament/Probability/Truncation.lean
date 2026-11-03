module

public import Tournament.Model.EstimateUpdate
public import Tournament.Probability.ExponentialTail

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

namespace Model

theorem truncateEstimate_range (η : ℝ) (z : ι → ℝ) : η*‖truncateEstimate η z‖≤1 := by
  unfold truncateEstimate
  split
  · assumption
  · simp

theorem truncateEstimate_squareNorm_le (w : ProbabilityVector ι) (η : ℝ) (z : ι → ℝ) :
    w.squareNorm (truncateEstimate η z)≤w.squareNorm z := by
  unfold truncateEstimate
  split
  · exact le_refl _
  · simpa only [ProbabilityVector.squareNorm,Pi.zero_apply,zero_pow (by decide : 2≠0),mul_zero,
      Finset.sum_const_zero] using w.squareNorm_nonneg z

end Model

namespace ProbabilityVector

def truncationBias (μ : ProbabilityVector Ω) (η : ℝ) (Z : Ω → ι → ℝ) : ι → ℝ :=
  fun i ↦ μ.mean (fun ω ↦ if η*‖Z ω‖≤1 then 0 else Z ω i)

theorem truncated_mean (μ : ProbabilityVector Ω) (η : ℝ) (Z : Ω → ι → ℝ) (i : ι) :
    μ.mean (fun ω ↦ Model.truncateEstimate η (Z ω) i)=μ.mean (fun ω ↦ Z ω i)-μ.truncationBias η Z i := by
  unfold truncationBias
  rw [← mean_sub]
  congr 1
  funext ω
  by_cases h : η*‖Z ω‖≤1 <;> simp [Model.truncateEstimate,h]

theorem truncation_secondMoment_le (μ : ProbabilityVector Ω) (w : ProbabilityVector ι)
    (η : ℝ) (Z : Ω → ι → ℝ) :
    μ.mean (fun ω ↦ w.squareNorm (Model.truncateEstimate η (Z ω)))≤μ.mean (fun ω ↦ w.squareNorm (Z ω)) :=
  μ.mean_mono (fun ω ↦ Model.truncateEstimate_squareNorm_le w η (Z ω))

theorem truncationBias_norm_le (μ : ProbabilityVector Ω) (η : ℝ) (hη : 0≤η)
    (Z : Ω → ι → ℝ) (B a δ : ℝ) (hB : 0≤B) (hδ : 0≤δ)
    (hZ : ∀ ω, ‖Z ω‖≤B) (ha : η*a≤1)
    (htail : μ.probability (fun ω ↦ a<‖Z ω‖)≤δ) :
    ‖μ.truncationBias η Z‖≤B*δ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB hδ)).mpr
  intro i
  rw [Real.norm_eq_abs]
  calc
    _ ≤ μ.mean (fun ω ↦ |if η*‖Z ω‖≤1 then 0 else Z ω i|) := μ.abs_mean_le _
    _ ≤ μ.mean (fun ω ↦ B*(if a<‖Z ω‖ then 1 else 0)) := by
      apply μ.mean_mono
      intro ω
      by_cases hd : η*‖Z ω‖≤1
      · simp only [ite_eq_left hd,abs_zero]
        split <;> simp_all
      · have ht : a<‖Z ω‖ := by
          by_contra hn
          have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hη
          exact hd (le_trans hmul ha)
        rw [ite_eq_right hd,ite_eq_left ht,mul_one]
        have hi : |Z ω i|≤‖Z ω‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (Z ω) i
        exact le_trans hi (hZ ω)
    _ = B*μ.probability (fun ω ↦ a<‖Z ω‖) := mean_const_mul μ B _
    _ ≤ B*δ := mul_le_mul_of_nonneg_left htail hB

end ProbabilityVector
end
end Tournament

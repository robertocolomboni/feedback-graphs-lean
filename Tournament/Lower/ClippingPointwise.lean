module

public import Tournament.Lower.Environments
public import Tournament.Lower.GaussianTailIntegral

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory
open scoped NNReal Classical

noncomputable section

theorem clip_eq_self {z : ℝ} (hz : 1/4≤z ∧ z≤3/4) : clip z=z := by
  unfold clip
  rw [max_eq_right hz.1,min_eq_right hz.2]

theorem clipping_error_le_abs {mean : ℝ} (hmean : 1/4≤mean ∧ mean≤3/4) (g : ℝ) :
    |clip (mean+g)-(mean+g)|≤|g| := by
  have hlo := neg_abs_le g
  have hhi := le_abs_self g
  by_cases hl : mean+g≤1/4
  · have hc : clip (mean+g)=1/4 := by
      simp only [clip,max_eq_left hl]
      norm_num
    rw [hc,abs_of_nonneg (by linarith)]
    linarith
  · by_cases hh : 3/4≤mean+g
    · have hc : clip (mean+g)=3/4 := by
        unfold clip
        rw [max_eq_right (by linarith),min_eq_left hh]
      rw [hc,abs_of_nonpos (by linarith)]
      linarith
    · rw [clip_eq_self ⟨by linarith,by linarith⟩,sub_self,abs_zero]
      exact abs_nonneg g

theorem clipping_error_le_absoluteTail {mean : ℝ} (hmean : 31/64≤mean ∧ mean≤1/2) (g : ℝ) :
    |clip (mean+g)-(mean+g)|≤absoluteTail (7/32) g := by
  by_cases hg : 7/32≤|g|
  · simp only [absoluteTail,ite_eq_left hg]
    exact clipping_error_le_abs ⟨by linarith,by linarith⟩ g
  · have hlo := neg_abs_le g
    have hhi := le_abs_self g
    have hsmall : |g|<7/32 := lt_of_not_ge hg
    have hc : clip (mean+g)=mean+g := clip_eq_self ⟨by linarith,by linarith⟩
    simp only [hc,sub_self,abs_zero,absoluteTail,ite_eq_right hg,le_refl]

theorem clipping_error_continuous (mean : ℝ) :
    Continuous (fun g ↦ |clip (mean+g)-(mean+g)|) := by
  exact ((clip_continuous.comp (continuous_const.add continuous_id)).sub
    (continuous_const.add continuous_id)).abs

theorem clipping_error_gaussian_integrable (mean : ℝ) (v : ℝ≥0) :
    Integrable (fun g ↦ |clip (mean+g)-(mean+g)|) (gaussianReal 0 v) := by
  have hid : Integrable (fun g : ℝ ↦ g) (gaussianReal 0 v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  have hclip : Integrable (fun g : ℝ ↦ clip (mean+g)) (gaussianReal 0 v) := by
    refine Integrable.of_bound (clip_continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall ?_)
    intro g
    have h := clip_bounds (mean+g)
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    linarith
  exact (hclip.sub ((integrable_const mean).add hid)).abs

theorem gaussian_clipping_error_le (mean : ℝ) (hmean : 31/64≤mean ∧ mean≤1/2) (v : ℝ≥0) :
    (∫ g, |clip (mean+g)-(mean+g)| ∂gaussianReal 0 v)≤
      Real.sqrt (2*(v:ℝ)/Real.pi)*Real.exp (-(7/32)^2/(2*(v:ℝ))) := by
  rw [← absoluteTail_integral (7/32) (by norm_num) v]
  exact integral_mono (clipping_error_gaussian_integrable mean v)
    (absoluteTail_integrable (7/32) (by norm_num) v) (clipping_error_le_absoluteTail hmean)

theorem clipping_error_hasLaw_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → ℝ} {v : ℝ≥0} (hg : HasLaw g (gaussianReal 0 v) μ) (mean : ℝ) :
    Integrable (fun ω ↦ |clip (mean+g ω)-(mean+g ω)|) μ := by
  have hi : Integrable (fun x ↦ |clip (mean+x)-(mean+x)|) (μ.map g) := by
    rw [hg.map_eq]
    exact clipping_error_gaussian_integrable mean v
  exact hi.comp_aemeasurable hg.aemeasurable

theorem clipping_error_hasLaw_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → ℝ} {v : ℝ≥0} (hg : HasLaw g (gaussianReal 0 v) μ)
    (mean : ℝ) (hmean : 31/64≤mean ∧ mean≤1/2) :
    (∫ ω, |clip (mean+g ω)-(mean+g ω)| ∂μ)≤
      Real.sqrt (2*(v:ℝ)/Real.pi)*Real.exp (-(7/32)^2/(2*(v:ℝ))) := by
  calc
    _ = ∫ x, |clip (mean+x)-(mean+x)| ∂gaussianReal 0 v :=
      hg.integral_comp (clipping_error_continuous mean).aestronglyMeasurable
    _ ≤ _ := gaussian_clipping_error_le mean hmean v

end
end Tournament.Lower

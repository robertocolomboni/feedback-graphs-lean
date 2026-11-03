module

public import Tournament.Lower.GaussianConditional
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

namespace Tournament.Lower.GaussianKL

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {A C : Type*} [MeasurableSpace A] [Fintype C]

theorem gaussian_compProd_eq_withDensity (μ : Measure A) [SFinite μ]
    (m : A → C → ℝ) (hm : Measurable m) (v : ℝ≥0) (hv : v≠0) :
    μ ⊗ₘ gaussianKernel m hm v hv=
      (μ.prod (base C)).withDensity (fun p ↦ density (m p.1) v p.2) := by
  ext s hs
  rw [Measure.compProd_apply hs,withDensity_apply _ hs,← lintegral_indicator hs,lintegral_prod]
  · apply lintegral_congr
    intro a
    rw [gaussianKernel_apply,productLaw_eq_withDensity (m a) v hv,
      withDensity_apply _ (measurable_prodMk_left hs),← lintegral_indicator (measurable_prodMk_left hs)]
    rfl
  · exact ((density_joint_measurable m hm v).indicator hs).aemeasurable

theorem gaussian_compProd_ac_base (μ : Measure A) [SFinite μ]
    (m : A → C → ℝ) (hm : Measurable m) (v : ℝ≥0) (hv : v≠0) :
    μ ⊗ₘ gaussianKernel m hm v hv ≪ μ.prod (base C) := by
  rw [gaussian_compProd_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

theorem base_ac_gaussian_compProd (μ : Measure A) [SFinite μ]
    (m : A → C → ℝ) (hm : Measurable m) (v : ℝ≥0) (hv : v≠0) :
    μ.prod (base C) ≪ μ ⊗ₘ gaussianKernel m hm v hv := by
  rw [gaussian_compProd_eq_withDensity]
  exact withDensity_absolutelyContinuous' (density_joint_measurable m hm v).aemeasurable
    (Filter.Eventually.of_forall (fun p ↦ (density_pos (m p.1) v hv p.2).ne'))

theorem gaussian_compProd_absolutelyContinuous (μ : Measure A) [SFinite μ]
    (m n : A → C → ℝ) (hm : Measurable m) (hn : Measurable n) (v : ℝ≥0) (hv : v≠0) :
    μ ⊗ₘ gaussianKernel m hm v hv ≪ μ ⊗ₘ gaussianKernel n hn v hv :=
  (gaussian_compProd_ac_base μ m hm v hv).trans (base_ac_gaussian_compProd μ n hn v hv)

theorem gaussian_compProd_rnDeriv (μ : Measure A) [SigmaFinite μ]
    (m : A → C → ℝ) (hm : Measurable m) (v : ℝ≥0) (hv : v≠0) :
    (μ ⊗ₘ gaussianKernel m hm v hv).rnDeriv (μ.prod (base C))=ᵐ[μ.prod (base C)]
      (fun p ↦ density (m p.1) v p.2) := by
  rw [gaussian_compProd_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ (density_joint_measurable m hm v)

theorem gaussian_compProd_llr_affine (μ : Measure A) [IsProbabilityMeasure μ]
    (m n : A → C → ℝ) (hm : Measurable m) (hn : Measurable n) (v : ℝ≥0) (hv : v≠0) :
    llr (μ ⊗ₘ gaussianKernel m hm v hv) (μ ⊗ₘ gaussianKernel n hn v hv)
      =ᵐ[μ ⊗ₘ gaussianKernel m hm v hv]
        (fun p ↦ ∑ c, ((m p.1 c-n p.1 c)/(v:ℝ)*p.2 c+
          ((n p.1 c)^2-(m p.1 c)^2)/(2*(v:ℝ)))) := by
  have hacm := gaussian_compProd_ac_base μ m hm v hv
  have hacn := gaussian_compProd_ac_base μ n hn v hv
  have hac := gaussian_compProd_absolutelyContinuous μ m n hm hn v hv
  filter_upwards [hac.ae_le (Measure.rnDeriv_eq_div hacm hacn),
    hacm.ae_le (gaussian_compProd_rnDeriv μ m hm v hv),
    hacm.ae_le (gaussian_compProd_rnDeriv μ n hn v hv)] with p hratio hpm hpn
  rw [llr,hratio,hpm,hpn,ENNReal.toReal_div,density_toReal,density_toReal]
  exact log_product_density_ratio (m p.1) (n p.1) p.2 v hv

end
end Tournament.Lower.GaussianKL

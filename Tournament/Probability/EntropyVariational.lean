module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

namespace Tournament.Probability

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped NNReal ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem entropy_variational (hac : μ≪ν) (hKL : klDiv μ ν≠⊤) (f : Ω → ℝ)
    (hf : Integrable f μ) (hExp : Integrable (fun ω ↦ exp (f ω)) ν) :
    (∫ ω, f ω ∂μ)≤(klDiv μ ν).toReal+log (∫ ω, exp (f ω) ∂ν) := by
  have hllr := (klDiv_ne_top_iff.mp hKL).2
  let : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hExp
  have hacT := hac.trans (absolutelyContinuous_tilted hExp)
  have hiT := integrable_llr_tilted_right hac hf hllr hExp
  have hG := integral_llr_add_sub_measure_univ_nonneg hacT hiT
  simp only [probReal_univ,add_sub_cancel_right] at hG
  rw [integral_llr_tilted_right hac hf hExp hllr] at hG
  have hK : (klDiv μ ν).toReal=∫ ω, llr μ ν ω ∂μ := by
    rw [toReal_klDiv hac hllr]
    simp only [probReal_univ,add_sub_cancel_right]
  rw [← hK] at hG
  linarith

theorem subgaussian_mean_entropy (hac : μ≪ν) (hKL : klDiv μ ν≠⊤) (X : Ω → ℝ)
    (hX : Integrable X μ) (c : ℝ≥0) (hSG : HasSubgaussianMGF X c ν) (t : ℝ) :
    t*(∫ ω, X ω ∂μ)≤(klDiv μ ν).toReal+(c:ℝ)*t^2/2 := by
  have hExp := hSG.integrable_exp_mul t
  have hV := entropy_variational hac hKL (fun ω ↦ t*X ω) (hX.const_mul t) hExp
  rw [integral_const_mul] at hV
  have hlog : log (∫ ω, exp (t*X ω) ∂ν)≤(c:ℝ)*t^2/2 := by
    apply (log_le_iff_le_exp (integral_exp_pos hExp)).mpr
    exact hSG.mgf_le t
  linarith

theorem subgaussian_mean_sq_entropy (hac : μ≪ν) (hKL : klDiv μ ν≠⊤) (X : Ω → ℝ)
    (hX : Integrable X μ) (c : ℝ≥0) (hSG : HasSubgaussianMGF X c ν) :
    (∫ ω, X ω ∂μ)^2≤2*(c:ℝ)*(klDiv μ ν).toReal := by
  let d := ∫ ω, X ω ∂μ
  let K := (klDiv μ ν).toReal
  change d^2≤2*(c:ℝ)*K
  by_cases hc : c=0
  · have hd : d=0 := by
      by_contra hd
      have h := subgaussian_mean_entropy hac hKL X hX c hSG ((K+1)/d)
      change (K+1)/d*d≤K+(c:ℝ)*((K+1)/d)^2/2 at h
      rw [hc,NNReal.coe_zero,zero_mul,zero_div,add_zero,div_mul_cancel₀ _ hd] at h
      linarith
    rw [hd,zero_pow (by decide : 2≠0)]
    positivity
  · have hc0 : 0<(c:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hc)
    have h := subgaussian_mean_entropy hac hKL X hX c hSG (d/(c:ℝ))
    change d/(c:ℝ)*d≤K+(c:ℝ)*(d/(c:ℝ))^2/2 at h
    have hsub : d/(c:ℝ)*d-(c:ℝ)*(d/(c:ℝ))^2/2≤K := by linarith
    have heq : d/(c:ℝ)*d-(c:ℝ)*(d/(c:ℝ))^2/2=d^2/(2*(c:ℝ)) := by
      field_simp
      ring
    rw [heq] at hsub
    have hmul := (div_le_iff₀ (by positivity : 0<2*(c:ℝ))).mp hsub
    change d^2≤2*(c:ℝ)*K
    nlinarith

theorem bounded_observable_entropy_sq (hac : μ≪ν) (hKL : klDiv μ ν≠⊤) (f : Ω → ℝ)
    (hf : AEMeasurable f ν) (a b : ℝ) (hbound : ∀ᵐ ω ∂ν, f ω∈Set.Icc a b) :
    ((∫ ω, f ω ∂μ)-(∫ ω, f ω ∂ν))^2≤(b-a)^2*(klDiv μ ν).toReal/2 := by
  have hfν := Integrable.of_mem_Icc a b hf hbound
  have hfμ := Integrable.of_mem_Icc a b (hf.mono_ac hac) (hac.ae_le hbound)
  have hSG := hasSubgaussianMGF_of_mem_Icc hf hbound
  have h := subgaussian_mean_sq_entropy hac hKL (fun ω ↦ f ω-(∫ ω, f ω ∂ν))
    (hfμ.sub (integrable_const _)) _ hSG
  rw [integral_sub hfμ (integrable_const _),integral_const] at h
  simp only [probReal_univ,smul_eq_mul,one_mul,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_ofNat,
    coe_nnnorm,Real.norm_eq_abs] at h
  calc
    _ ≤ 2*(|b-a|/2)^2*(klDiv μ ν).toReal := h
    _ = _ := by rw [div_pow,sq_abs]; ring

theorem bounded_observable_pinsker (hac : μ≪ν) (hKL : klDiv μ ν≠⊤) (f : Ω → ℝ)
    (hf : AEMeasurable f ν) (a b : ℝ) (hab : a≤b) (hbound : ∀ᵐ ω ∂ν, f ω∈Set.Icc a b) :
    |(∫ ω, f ω ∂μ)-(∫ ω, f ω ∂ν)|≤(b-a)*sqrt ((klDiv μ ν).toReal/2) := by
  have h := bounded_observable_entropy_sq hac hKL f hf a b hbound
  have hs := sq_sqrt (by positivity : 0≤(klDiv μ ν).toReal/2)
  have hr : 0≤(b-a)*sqrt ((klDiv μ ν).toReal/2) := mul_nonneg (by linarith) (sqrt_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) hr).mp
  rw [sq_abs,mul_pow,hs]
  nlinarith

end
end Tournament.Probability

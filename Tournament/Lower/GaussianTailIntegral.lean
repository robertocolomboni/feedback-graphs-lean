module

public import Tournament.Lower.GaussianProduct
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Classical NNReal Topology

noncomputable section

theorem integral_mul_exp_neg_sq_tail (a b : ℝ) (hb : 0<b) :
    ∫ x : ℝ in Ioi a, x*exp (-b*x^2)=exp (-b*a^2)/(2*b) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x ↦ -(2*b)⁻¹*exp (-b*x^2))
      (x*exp (-b*x^2)) x := by
    intro x
    convert! (((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2*b)⁻¹)) using 1
    field_simp
    ring
  have ht : Tendsto (fun x : ℝ ↦ -(2*b)⁻¹*exp (-b*x^2)) atTop (𝓝 0) := by
    have h := Tendsto.const_mul (-(2*b)⁻¹)
      (tendsto_exp_atBot.comp
        ((tendsto_pow_atTop (by decide : 2≠0)).const_mul_atTop_of_neg (neg_lt_zero.mpr hb)))
    simpa only [Function.comp_apply,mul_zero] using h
  calc
    _ = 0-(-(2*b)⁻¹*exp (-b*a^2)) :=
      integral_Ioi_of_hasDerivAt_of_tendsto' (a := a)
        (f := fun x : ℝ ↦ -(2*b)⁻¹*exp (-b*x^2))
        (f' := fun x : ℝ ↦ x*exp (-b*x^2)) (fun x _ ↦ hderiv x)
        (integrable_mul_exp_neg_mul_sq hb).integrableOn ht
    _ = _ := by ring

def positiveTail (a x : ℝ) : ℝ := if a≤x then x else 0

def absoluteTail (a x : ℝ) : ℝ := if a≤|x| then |x| else 0

theorem positiveTail_measurable (a : ℝ) : Measurable (positiveTail a) := by
  change Measurable ((Ici a).indicator id)
  exact measurable_id.indicator measurableSet_Ici

theorem positiveTail_integrable (a : ℝ) (v : ℝ≥0) :
    Integrable (positiveTail a) (gaussianReal 0 v) := by
  change Integrable ((Ici a).indicator id) _
  exact (memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)).indicator measurableSet_Ici

theorem positiveTail_integral (a : ℝ) (v : ℝ≥0) (hv : v≠0) :
    ∫ x, positiveTail a x ∂gaussianReal 0 v=
      (v:ℝ)/sqrt (2*π*(v:ℝ))*exp (-a^2/(2*(v:ℝ))) := by
  have hvr : (0:ℝ)<(v:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  rw [integral_gaussianReal_eq_integral_smul hv]
  have heq : (fun x : ℝ ↦ gaussianPDFReal 0 v x • positiveTail a x)=
      (Ici a).indicator (fun x : ℝ ↦ (sqrt (2*π*(v:ℝ)))⁻¹*(x*exp (-(2*(v:ℝ))⁻¹*x^2))) := by
    funext x
    simp only [gaussianPDFReal,sub_zero,smul_eq_mul,positiveTail,indicator,mem_Ici]
    by_cases hx : a≤x
    · simp only [ite_eq_left hx]
      have he : -x^2/(2*(v:ℝ))= -(2*(v:ℝ))⁻¹*x^2 := by ring
      rw [he]
      ring
    · simp only [ite_eq_right hx,mul_zero]
  rw [heq,integral_indicator measurableSet_Ici,integral_const_mul,integral_Ici_eq_integral_Ioi,
    integral_mul_exp_neg_sq_tail a _ (by positivity : 0<(2*(v:ℝ))⁻¹)]
  have he : -(2*(v:ℝ))⁻¹*a^2= -a^2/(2*(v:ℝ)) := by ring
  rw [he]
  field_simp

theorem absoluteTail_eq_pair (a x : ℝ) (ha : 0≤a) :
    absoluteTail a x=positiveTail a x+positiveTail a (-x) := by
  unfold absoluteTail positiveTail
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    split_ifs <;> linarith
  · rw [abs_of_nonpos hx]
    split_ifs <;> linarith

theorem gaussian_neg_preserving (v : ℝ≥0) :
    MeasurePreserving (fun x : ℝ ↦ -x) (gaussianReal 0 v) (gaussianReal 0 v) := by
  refine ⟨measurable_neg,?_⟩
  simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := v))

theorem positiveTail_neg_integrable (a : ℝ) (v : ℝ≥0) :
    Integrable (fun x ↦ positiveTail a (-x)) (gaussianReal 0 v) := by
  exact (gaussian_neg_preserving v).integrable_comp_of_integrable (positiveTail_integrable a v)

theorem absoluteTail_integrable (a : ℝ) (ha : 0≤a) (v : ℝ≥0) :
    Integrable (absoluteTail a) (gaussianReal 0 v) := by
  have heq : absoluteTail a=(fun x ↦ positiveTail a x+positiveTail a (-x)) := by
    funext x
    exact absoluteTail_eq_pair a x ha
  rw [heq]
  exact (positiveTail_integrable a v).add (positiveTail_neg_integrable a v)

theorem gaussian_tail_coefficient (v : ℝ≥0) (hv : v≠0) :
    2*(v:ℝ)/sqrt (2*π*(v:ℝ))=sqrt (2*(v:ℝ)/π) := by
  have hvr : (0:ℝ)<(v:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hs : (sqrt (2*π*(v:ℝ)))^2=2*π*(v:ℝ) := sq_sqrt (by positivity)
  have hsq : (2*(v:ℝ)/sqrt (2*π*(v:ℝ)))^2=(sqrt (2*(v:ℝ)/π))^2 := by
    rw [div_pow,hs,sq_sqrt (by positivity)]
    field_simp
  exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq

theorem absoluteTail_integral (a : ℝ) (ha : 0≤a) (v : ℝ≥0) :
    ∫ x, absoluteTail a x ∂gaussianReal 0 v=
      sqrt (2*(v:ℝ)/π)*exp (-a^2/(2*(v:ℝ))) := by
  by_cases hv : v=0
  · subst v
    simp [absoluteTail]
  · have heq : absoluteTail a=(fun x ↦ positiveTail a x+positiveTail a (-x)) := by
      funext x
      exact absoluteTail_eq_pair a x ha
    rw [heq,integral_add (positiveTail_integrable a v) (positiveTail_neg_integrable a v),
      (gaussian_neg_preserving v).integral_comp measurableEmbedding_neg (positiveTail a),
      positiveTail_integral a v hv]
    calc
      _ = (2*(v:ℝ)/sqrt (2*π*(v:ℝ)))*exp (-a^2/(2*(v:ℝ))) := by ring
      _ = _ := by rw [gaussian_tail_coefficient v hv]

end
end Tournament.Lower

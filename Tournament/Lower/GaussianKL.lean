module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.InformationTheory.KullbackLeibler.Basic

@[expose] public section

namespace Tournament.Lower.GaussianKL

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped NNReal ENNReal

noncomputable section

theorem absolutelyContinuous (m n : ℝ) (v : ℝ≥0) (hv : v≠0) :
    gaussianReal m v ≪ gaussianReal n v :=
  (gaussianReal_absolutelyContinuous m hv).trans (gaussianReal_absolutelyContinuous' n hv)

theorem log_density_ratio (m n x : ℝ) (v : ℝ≥0) (hv : v≠0) :
    log (gaussianPDFReal m v x/gaussianPDFReal n v x)=
      (m-n)/(v:ℝ)*x+(n^2-m^2)/(2*(v:ℝ)) := by
  have hvr : (0:ℝ)<(v:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hroot : (sqrt (2*π*(v:ℝ)))⁻¹≠0 := by positivity
  rw [log_div (gaussianPDFReal_pos m v x hv).ne' (gaussianPDFReal_pos n v x hv).ne']
  simp only [gaussianPDFReal,log_mul hroot (exp_pos _).ne',log_exp]
  field_simp
  ring

theorem llr_affine (m n : ℝ) (v : ℝ≥0) (hv : v≠0) :
    llr (gaussianReal m v) (gaussianReal n v)=ᵐ[gaussianReal m v]
      (fun x ↦ (m-n)/(v:ℝ)*x+(n^2-m^2)/(2*(v:ℝ))) := by
  have hm := gaussianReal_absolutelyContinuous m hv
  have hn := gaussianReal_absolutelyContinuous n hv
  have hmn := absolutelyContinuous m n v hv
  filter_upwards [hmn.ae_le (Measure.rnDeriv_eq_div hm hn),
    hm.ae_le (rnDeriv_gaussianReal m v),hm.ae_le (rnDeriv_gaussianReal n v)] with x hratio hpm hpn
  rw [llr,hratio,hpm,hpn,ENNReal.toReal_div,toReal_gaussianPDF,toReal_gaussianPDF]
  exact log_density_ratio m n x v hv

theorem llr_integrable (m n : ℝ) (v : ℝ≥0) (hv : v≠0) :
    Integrable (llr (gaussianReal m v) (gaussianReal n v)) (gaussianReal m v) := by
  have hid : Integrable (fun x : ℝ ↦ x) (gaussianReal m v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  rw [integrable_congr (llr_affine m n v hv)]
  exact (hid.const_mul ((m-n)/(v:ℝ))).add (integrable_const _)

theorem integral_llr (m n : ℝ) (v : ℝ≥0) (hv : v≠0) :
    (∫ x, llr (gaussianReal m v) (gaussianReal n v) x ∂gaussianReal m v)=(m-n)^2/(2*(v:ℝ)) := by
  have hid : Integrable (fun x : ℝ ↦ x) (gaussianReal m v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  calc
    _ = ∫ x, (m-n)/(v:ℝ)*x+(n^2-m^2)/(2*(v:ℝ)) ∂gaussianReal m v :=
      integral_congr_ae (llr_affine m n v hv)
    _ = (m-n)/(v:ℝ)*m+(n^2-m^2)/(2*(v:ℝ)) := by
      rw [integral_add (hid.const_mul _) (integrable_const _),integral_const_mul,
        integral_id_gaussianReal,integral_const]
      simp only [probReal_univ,smul_eq_mul,one_mul]
    _ = _ := by field_simp; ring

theorem klDiv_same_variance (m n : ℝ) (v : ℝ≥0) (hv : v≠0) :
    klDiv (gaussianReal m v) (gaussianReal n v)=ENNReal.ofReal ((m-n)^2/(2*(v:ℝ))) := by
  rw [klDiv_of_ac_of_integrable (absolutelyContinuous m n v hv) (llr_integrable m n v hv),
    integral_llr m n v hv]
  simp only [probReal_univ,add_sub_cancel_right]

end
end Tournament.Lower.GaussianKL

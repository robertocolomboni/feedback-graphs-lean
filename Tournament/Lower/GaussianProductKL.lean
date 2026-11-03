module

public import Tournament.Lower.GaussianProductDensity

@[expose] public section

namespace Tournament.Lower.GaussianKL

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped BigOperators NNReal ENNReal Classical

noncomputable section

variable {C : Type*} [Fintype C]

theorem log_product_density_ratio (m n x : C → ℝ) (v : ℝ≥0) (hv : v≠0) :
    log (realDensity m v x/realDensity n v x)=
      ∑ c, ((m c-n c)/(v:ℝ)*x c+((n c)^2-(m c)^2)/(2*(v:ℝ))) := by
  rw [log_div (realDensity_pos m v hv x).ne' (realDensity_pos n v hv x).ne']
  unfold realDensity
  rw [log_prod (fun c _ ↦ (gaussianPDFReal_pos (m c) v (x c) hv).ne'),
    log_prod (fun c _ ↦ (gaussianPDFReal_pos (n c) v (x c) hv).ne'),← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [← log_div (gaussianPDFReal_pos (m c) v (x c) hv).ne' (gaussianPDFReal_pos (n c) v (x c) hv).ne']
  exact log_density_ratio (m c) (n c) (x c) v hv

theorem product_llr_affine (m n : C → ℝ) (v : ℝ≥0) (hv : v≠0) :
    llr (productLaw m v) (productLaw n v)=ᵐ[productLaw m v]
      (fun x ↦ ∑ c, ((m c-n c)/(v:ℝ)*x c+((n c)^2-(m c)^2)/(2*(v:ℝ)))) := by
  have hm := productLaw_ac_base m v hv
  have hn := productLaw_ac_base n v hv
  have hmn := productLaw_absolutelyContinuous m n v hv
  filter_upwards [hmn.ae_le (Measure.rnDeriv_eq_div hm hn),
    hm.ae_le (productLaw_rnDeriv m v hv),hm.ae_le (productLaw_rnDeriv n v hv)] with x hratio hpm hpn
  rw [llr,hratio,hpm,hpn,ENNReal.toReal_div,density_toReal,density_toReal]
  exact log_product_density_ratio m n x v hv

theorem coordinate_integrable (m : C → ℝ) (v : ℝ≥0) (c : C) :
    Integrable (fun x : C → ℝ ↦ x c) (productLaw m v) :=
  (measurePreserving_eval (fun c ↦ gaussianReal (m c) v) c).integrable_comp_of_integrable
    (memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1))

theorem coordinate_mean (m : C → ℝ) (v : ℝ≥0) (c : C) :
    ∫ x : C → ℝ, x c ∂productLaw m v=m c := by
  calc
    _ = ∫ x : ℝ, x ∂gaussianReal (m c) v :=
      (measurePreserving_eval (fun c ↦ gaussianReal (m c) v) c).hasLaw.integral_eq
    _ = _ := integral_id_gaussianReal

theorem product_llr_integrable (m n : C → ℝ) (v : ℝ≥0) (hv : v≠0) :
    Integrable (llr (productLaw m v) (productLaw n v)) (productLaw m v) := by
  rw [integrable_congr (product_llr_affine m n v hv)]
  apply integrable_finsetSum
  intro c _
  exact ((coordinate_integrable m v c).const_mul _).add (integrable_const _)

theorem product_integral_llr (m n : C → ℝ) (v : ℝ≥0) (hv : v≠0) :
    (∫ x, llr (productLaw m v) (productLaw n v) x ∂productLaw m v)=
      (∑ c, (m c-n c)^2)/(2*(v:ℝ)) := by
  have hi (c : C) : Integrable
      (fun x : C → ℝ ↦ (m c-n c)/(v:ℝ)*x c+((n c)^2-(m c)^2)/(2*(v:ℝ))) (productLaw m v) :=
    ((coordinate_integrable m v c).const_mul _).add (integrable_const _)
  calc
    _ = ∫ x, ∑ c, ((m c-n c)/(v:ℝ)*x c+((n c)^2-(m c)^2)/(2*(v:ℝ))) ∂productLaw m v :=
      integral_congr_ae (product_llr_affine m n v hv)
    _ = ∑ c, ∫ x : C → ℝ, (m c-n c)/(v:ℝ)*x c+((n c)^2-(m c)^2)/(2*(v:ℝ)) ∂productLaw m v :=
      integral_finsetSum _ (fun c _ ↦ hi c)
    _ = ∑ c, (m c-n c)^2/(2*(v:ℝ)) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [integral_add ((coordinate_integrable m v c).const_mul _) (integrable_const _),
        integral_const_mul,coordinate_mean,integral_const]
      simp only [probReal_univ,smul_eq_mul,one_mul]
      field_simp
      ring
    _ = _ := (Finset.sum_div _ _ _).symm

theorem product_klDiv_same_variance (m n : C → ℝ) (v : ℝ≥0) (hv : v≠0) :
    klDiv (productLaw m v) (productLaw n v)=ENNReal.ofReal ((∑ c, (m c-n c)^2)/(2*(v:ℝ))) := by
  rw [klDiv_of_ac_of_integrable (productLaw_absolutelyContinuous m n v hv)
    (product_llr_integrable m n v hv),product_integral_llr m n v hv]
  simp only [probReal_univ,add_sub_cancel_right]

end
end Tournament.Lower.GaussianKL

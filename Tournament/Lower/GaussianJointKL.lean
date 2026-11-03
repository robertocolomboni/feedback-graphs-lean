module

public import Tournament.Lower.GaussianJointDensity

@[expose] public section

namespace Tournament.Lower.GaussianKL

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {A C : Type*} [MeasurableSpace A] [Fintype C]

def affineLLR (m n : A → C → ℝ) (v : ℝ≥0) (p : A × (C → ℝ)) : ℝ :=
  ∑ c, ((m p.1 c-n p.1 c)/(v:ℝ)*p.2 c+((n p.1 c)^2-(m p.1 c)^2)/(2*(v:ℝ)))

def centeredLLR (m n : A → C → ℝ) (v : ℝ≥0) (p : A × (C → ℝ)) : ℝ :=
  ∑ c, ((m p.1 c-n p.1 c)/(v:ℝ)*p.2 c+(m p.1 c-n p.1 c)^2/(2*(v:ℝ)))

theorem affineLLR_measurable (m n : A → C → ℝ) (hm : Measurable m) (hn : Measurable n) (v : ℝ≥0) :
    Measurable (affineLLR m n v) := by
  apply Finset.measurable_sum
  intro c _
  have hmc : Measurable (fun p : A × (C → ℝ) ↦ m p.1 c) :=
    ((measurable_pi_apply c).comp hm).comp measurable_fst
  have hnc : Measurable (fun p : A × (C → ℝ) ↦ n p.1 c) :=
    ((measurable_pi_apply c).comp hn).comp measurable_fst
  exact ((hmc.sub hnc).div_const _ |>.mul ((measurable_pi_apply c).comp measurable_snd)).add
    ((hnc.pow_const 2).sub (hmc.pow_const 2) |>.div_const _)

omit [MeasurableSpace A] in
theorem affineLLR_shift (m n : A → C → ℝ) (v : ℝ≥0) (p : A × (C → ℝ)) :
    affineLLR m n v (p.1,m p.1+p.2)=centeredLLR m n v p := by
  apply Finset.sum_congr rfl
  intro c _
  simp only [Pi.add_apply]
  ring

theorem centeredLLR_integrable (μ : Measure A) [IsProbabilityMeasure μ]
    (m n : A → C → ℝ) (v : ℝ≥0)
    (hδ : ∀ c, MemLp (fun a ↦ m a c-n a c) 2 μ) :
    Integrable (centeredLLR m n v) (μ.prod (productLaw (0 : C → ℝ) v)) := by
  apply integrable_finsetSum
  intro c _
  have hlinear := ((hδ c).integrable (by norm_num)).div_const (v:ℝ)
  have hcross := hlinear.mul_prod (coordinate_integrable (0 : C → ℝ) v c)
  have hconstant := (((hδ c).integrable_sq).div_const (2*(v:ℝ))).comp_fst (productLaw (0 : C → ℝ) v)
  exact hcross.add hconstant

theorem centeredLLR_integral (μ : Measure A) [IsProbabilityMeasure μ]
    (m n : A → C → ℝ) (v : ℝ≥0)
    (hδ : ∀ c, MemLp (fun a ↦ m a c-n a c) 2 μ) :
    (∫ p, centeredLLR m n v p ∂μ.prod (productLaw (0 : C → ℝ) v))=
      ∫ a, (∑ c, (m a c-n a c)^2)/(2*(v:ℝ)) ∂μ := by
  rw [integral_prod _ (centeredLLR_integrable μ m n v hδ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a ↦ by
    have hi (c : C) : Integrable (fun z : C → ℝ ↦
        (m a c-n a c)/(v:ℝ)*z c+(m a c-n a c)^2/(2*(v:ℝ))) (productLaw (0 : C → ℝ) v) :=
      ((coordinate_integrable (0 : C → ℝ) v c).const_mul _).add (integrable_const _)
    change (∫ z, ∑ c, ((m a c-n a c)/(v:ℝ)*z c+(m a c-n a c)^2/(2*(v:ℝ)))
      ∂productLaw (0 : C → ℝ) v)=_
    rw [integral_finsetSum _ (fun c _ ↦ hi c)]
    dsimp only
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_add ((coordinate_integrable (0 : C → ℝ) v c).const_mul _) (integrable_const _),
      integral_const_mul,coordinate_mean,integral_const]
    simp)

theorem gaussian_compProd_llr_integrable (μ : Measure A) [IsProbabilityMeasure μ]
    (m n : A → C → ℝ) (hm : Measurable m) (hn : Measurable n) (v : ℝ≥0) (hv : v≠0)
    (hδ : ∀ c, MemLp (fun a ↦ m a c-n a c) 2 μ) :
    Integrable (llr (μ ⊗ₘ gaussianKernel m hm v hv) (μ ⊗ₘ gaussianKernel n hn v hv))
      (μ ⊗ₘ gaussianKernel m hm v hv) := by
  rw [integrable_congr (gaussian_compProd_llr_affine μ m n hm hn v hv)]
  have hmap : Measurable (fun p : A × (C → ℝ) ↦ (p.1,m p.1+p.2)) :=
    measurable_fst.prodMk ((hm.comp measurable_fst).add measurable_snd)
  have hpres : MeasurePreserving (fun p : A × (C → ℝ) ↦ (p.1,m p.1+p.2))
      (μ.prod (productLaw (0 : C → ℝ) v)) (μ ⊗ₘ gaussianKernel m hm v hv) :=
    ⟨hmap,shifted_product_eq_compProd μ m hm v hv⟩
  apply (hpres.integrable_comp (affineLLR_measurable m n hm hn v).aestronglyMeasurable).mp
  have heq : (affineLLR m n v ∘ (fun p : A × (C → ℝ) ↦ (p.1,m p.1+p.2)))=centeredLLR m n v := by
    funext p
    exact affineLLR_shift m n v p
  rw [heq]
  exact centeredLLR_integrable μ m n v hδ

theorem gaussian_compProd_integral_llr (μ : Measure A) [IsProbabilityMeasure μ]
    (m n : A → C → ℝ) (hm : Measurable m) (hn : Measurable n) (v : ℝ≥0) (hv : v≠0)
    (hδ : ∀ c, MemLp (fun a ↦ m a c-n a c) 2 μ) :
    (∫ p, llr (μ ⊗ₘ gaussianKernel m hm v hv) (μ ⊗ₘ gaussianKernel n hn v hv) p
      ∂μ ⊗ₘ gaussianKernel m hm v hv)=
      ∫ a, (∑ c, (m a c-n a c)^2)/(2*(v:ℝ)) ∂μ := by
  have hmap : Measurable (fun p : A × (C → ℝ) ↦ (p.1,m p.1+p.2)) :=
    measurable_fst.prodMk ((hm.comp measurable_fst).add measurable_snd)
  have hLaw : HasLaw (fun p : A × (C → ℝ) ↦ (p.1,m p.1+p.2))
      (μ ⊗ₘ gaussianKernel m hm v hv) (μ.prod (productLaw (0 : C → ℝ) v)) :=
    ⟨hmap.aemeasurable,shifted_product_eq_compProd μ m hm v hv⟩
  calc
    _ = ∫ p, affineLLR m n v p ∂μ ⊗ₘ gaussianKernel m hm v hv :=
      integral_congr_ae (gaussian_compProd_llr_affine μ m n hm hn v hv)
    _ = ∫ p, affineLLR m n v (p.1,m p.1+p.2) ∂μ.prod (productLaw (0 : C → ℝ) v) :=
      (hLaw.integral_comp (affineLLR_measurable m n hm hn v).aestronglyMeasurable).symm
    _ = ∫ p, centeredLLR m n v p ∂μ.prod (productLaw (0 : C → ℝ) v) :=
      integral_congr_ae (Filter.Eventually.of_forall (affineLLR_shift m n v))
    _ = _ := centeredLLR_integral μ m n v hδ

theorem gaussian_compProd_kl (μ : Measure A) [IsProbabilityMeasure μ]
    (m n : A → C → ℝ) (hm : Measurable m) (hn : Measurable n) (v : ℝ≥0) (hv : v≠0)
    (hδ : ∀ c, MemLp (fun a ↦ m a c-n a c) 2 μ) :
    klDiv (μ ⊗ₘ gaussianKernel m hm v hv) (μ ⊗ₘ gaussianKernel n hn v hv)=
      ENNReal.ofReal (∫ a, (∑ c, (m a c-n a c)^2)/(2*(v:ℝ)) ∂μ) := by
  rw [klDiv_of_ac_of_integrable (gaussian_compProd_absolutelyContinuous μ m n hm hn v hv)
    (gaussian_compProd_llr_integrable μ m n hm hn v hv hδ),
    gaussian_compProd_integral_llr μ m n hm hn v hv hδ]
  simp only [probReal_univ,add_sub_cancel_right]

end
end Tournament.Lower.GaussianKL

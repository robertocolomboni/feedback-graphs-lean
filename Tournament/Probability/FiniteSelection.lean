module

public import Tournament.Probability.VectorKernel
public import Mathlib.Probability.HasCondDistrib

@[expose] public section

namespace Tournament.Probability

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

noncomputable section

variable {Ω A ι : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
variable [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem integrable_finite_selection (μ : Measure Ω) (F : Ω → ι → ℝ)
    (hF : ∀ i, Integrable (fun ω ↦ F ω i) μ) (I : Ω → ι) (hI : Measurable I) :
    Integrable (fun ω ↦ F ω (I ω)) μ := by
  have heq : (fun ω ↦ F ω (I ω))=(fun ω ↦ ∑ i, if I ω=i then F ω i else 0) := by
    funext ω
    simp
  rw [heq]
  apply integrable_finsetSum
  intro i _
  exact (hF i).indicator ((measurableSet_singleton i).preimage hI)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem integrable_finite_mean (μ : Measure Ω) (p : Ω → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun ω ↦ p ω i)) (F : Ω → ι → ℝ)
    (hF : ∀ i, Integrable (fun ω ↦ F ω i) μ) :
    Integrable (fun ω ↦ (p ω).mean (F ω)) μ := by
  have hSum : Integrable (fun ω ↦ ∑ i, |F ω i|) μ := integrable_finsetSum _ (fun i _ ↦ (hF i).abs)
  have hm : AEStronglyMeasurable (fun ω ↦ (p ω).mean (F ω)) μ := by
    unfold ProbabilityVector.mean
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun i _ ↦ (hp i).aestronglyMeasurable.mul (hF i).aestronglyMeasurable)
  apply hSum.mono' hm
  exact Filter.Eventually.of_forall (fun ω ↦ by
    rw [Real.norm_eq_abs]
    apply ((p ω).abs_mean_le (F ω)).trans
    exact Finset.sum_le_sum (fun i _ ↦ mul_le_of_le_one_left (abs_nonneg _) ((p ω).weight_le_one i)))

theorem conditional_finite_mean (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (I : Ω → ι) (hI : Measurable I)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (hLaw : HasCondDistrib I X (ProbabilityVector.kernel p hp) μ)
    (F : A → ι → ℝ) (hF : ∀ i, Measurable (fun a ↦ F a i))
    (hInt : ∀ i, Integrable (fun ω ↦ F (X ω) i) μ) :
    (∫ ω, F (X ω) (I ω) ∂μ)=∫ ω, (p (X ω)).mean (F (X ω)) ∂μ := by
  let ψ : A × ι → ℝ := fun q ↦ F q.1 q.2
  have hψ : Measurable ψ := measurable_from_prod_countable_left hF
  have hpres := hLaw.measurePreserving (hX.prodMk hI)
  have hiSelected := integrable_finite_selection μ (fun ω ↦ F (X ω)) hInt I hI
  have hiPair : Integrable ψ ((μ.map X) ⊗ₘ ProbabilityVector.kernel p hp) :=
    (hpres.integrable_comp hψ.aestronglyMeasurable).mp hiSelected
  have hMean : Measurable (fun a ↦ (p a).mean (F a)) :=
    Finset.measurable_sum Finset.univ (fun i _ ↦ (hp i).mul (hF i))
  calc
    _ = ∫ q, ψ q ∂(μ.map X) ⊗ₘ ProbabilityVector.kernel p hp :=
      hLaw.integral_comp hψ.aestronglyMeasurable
    _ = ∫ a, ∫ i, F a i ∂ProbabilityVector.kernel p hp a ∂μ.map X := Measure.integral_compProd hiPair
    _ = ∫ a, (p a).mean (F a) ∂μ.map X := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a ↦ ProbabilityVector.integral_kernel p hp a (F a))
    _ = _ := integral_map hX.aemeasurable hMean.aestronglyMeasurable

end
end Tournament.Probability

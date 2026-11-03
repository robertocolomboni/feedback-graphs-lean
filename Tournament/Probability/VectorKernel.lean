module

public import Tournament.Probability.FiniteMeasure
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

namespace Tournament.ProbabilityVector

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {A ι : Type*} [MeasurableSpace A] [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem measurable_toMeasure (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) :
    Measurable (fun a ↦ (p a).toMeasure) := by
  apply Measure.measurable_of_measurable_coe
  intro s _
  have heq : (fun a ↦ (p a).toMeasure s)=(fun a ↦ ∑ i, if i∈s then ENNReal.ofReal (p a i) else 0) := by
    funext a
    change (p a).toPMF.toMeasure s=_
    rw [PMF.toMeasure_apply_fintype]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i∈s <;> simp [hi,toPMF,PMF.ofFintype_apply]
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  by_cases hi : i∈s
  · simp only [ite_eq_left hi]
    exact (hp i).ennreal_ofReal
  · simp only [ite_eq_right hi]
    exact measurable_const

def kernel (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) : Kernel A ι where
  toFun a := (p a).toMeasure
  measurable' := measurable_toMeasure p hp

instance kernel_markov (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) :
    IsMarkovKernel (kernel p hp) where
  isProbabilityMeasure a := (p a).toMeasure_isProbability

theorem kernel_apply (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (a : A) :
    kernel p hp a=(p a).toMeasure := rfl

theorem integral_kernel (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (a : A)
    (f : ι → ℝ) : (∫ i, f i ∂kernel p hp a)=(p a).mean f := integral_toMeasure (p a) f

end
end Tournament.ProbabilityVector

module

public import Tournament.Probability.ConditionalComposition

@[expose] public section

namespace Tournament.Probability

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
variable [MeasurableSpace B] [MeasurableSpace C]

theorem conditional_product_of_fresh {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → A} {I : Ω → B} {G : Ω → C} {κ : Kernel A B} [IsMarkovKernel κ]
    (ν : Measure C) [IsProbabilityMeasure ν]
    (hI : HasCondDistrib I X κ μ)
    (hFresh : HasCondDistrib G (fun ω ↦ (X ω,I ω)) (Kernel.const (A × B) ν) μ) :
    HasCondDistrib (fun ω ↦ (G ω,I ω)) X (Kernel.const A ν ×ₖ κ) μ := by
  have h := conditional_pair hI hFresh
  have hProd : κ ⊗ₖ Kernel.const (A × B) ν=κ ×ₖ Kernel.const A ν := by
    rw [kernel_prod_eq_compProd]
    rfl
  rw [hProd] at h
  have hSwap := h.comp_left measurable_swap
  simpa only [Kernel.map_prod_swap,Function.comp_def,Prod.swap] using hSwap

end
end Tournament.Probability

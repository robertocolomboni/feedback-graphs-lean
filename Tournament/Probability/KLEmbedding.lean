module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

namespace Tournament.Probability

open MeasureTheory InformationTheory
open scoped ENNReal

noncomputable section

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem llr_map_embedding (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : A → B} (hf : MeasurableEmbedding f) (hac : μ≪ν) :
    (fun a ↦ llr (μ.map f) (ν.map f) (f a))=ᵐ[μ] llr μ ν := by
  filter_upwards [hac.ae_le (hf.rnDeriv_map μ ν)] with a ha
  exact congrArg (fun x ↦ Real.log x.toReal) ha

theorem klDiv_map_embedding_of_ac (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : A → B} (hf : MeasurableEmbedding f) (hac : μ≪ν) :
    klDiv (μ.map f) (ν.map f)=klDiv μ ν := by
  let : IsProbabilityMeasure (μ.map f) := inferInstance
  let : IsProbabilityMeasure (ν.map f) := inferInstance
  have hllr := llr_map_embedding μ ν hf hac
  have hint : Integrable (llr (μ.map f) (ν.map f)) (μ.map f) ↔ Integrable (llr μ ν) μ := by
    rw [hf.integrable_map_iff]
    exact integrable_congr hllr
  by_cases hi : Integrable (llr μ ν) μ
  · rw [klDiv_of_ac_of_integrable (hf.absolutelyContinuous_map hac) (hint.mpr hi),
      klDiv_of_ac_of_integrable hac hi]
    simp only [probReal_univ,add_sub_cancel_right]
    congr 1
    rw [hf.integral_map]
    exact integral_congr_ae hllr
  · rw [klDiv_of_not_integrable hi,klDiv_of_not_integrable (hint.not.mpr hi)]

theorem klDiv_prod_common_right (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : Measure B) [IsProbabilityMeasure ρ] : klDiv (μ.prod ρ) (ν.prod ρ)=klDiv μ ν := by
  simpa only [Measure.compProd_const] using
    InformationTheory.klDiv_compProd_left μ ν (ProbabilityTheory.Kernel.const A ρ)

end
end Tournament.Probability

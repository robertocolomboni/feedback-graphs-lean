module

public import Tournament.Foundations.Centering
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

namespace Tournament.ProbabilityVector

open scoped BigOperators MeasureTheory ENNReal Classical
open MeasureTheory Filter

noncomputable section

variable {Ω : Type*} [Fintype Ω]

def toPMF (μ : ProbabilityVector Ω) : PMF Ω :=
  PMF.ofFintype (fun ω ↦ ENNReal.ofReal (μ ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ μ.nonneg ω),μ.sum_eq_one]
    norm_num)

variable [MeasurableSpace Ω]

def toMeasure (μ : ProbabilityVector Ω) : Measure Ω := μ.toPMF.toMeasure

instance toMeasure_isProbability (μ : ProbabilityVector Ω) : IsProbabilityMeasure μ.toMeasure := by
  change IsProbabilityMeasure μ.toPMF.toMeasure
  infer_instance

variable [MeasurableSingletonClass Ω]

theorem toMeasure_singleton (μ : ProbabilityVector Ω) (ω : Ω) : μ.toMeasure {ω}=ENNReal.ofReal (μ ω) :=
  PMF.toMeasure_apply_singleton μ.toPMF ω (MeasurableSet.singleton ω)

theorem integral_toMeasure (μ : ProbabilityVector Ω) (f : Ω → ℝ) : (∫ ω, f ω ∂μ.toMeasure)=μ.mean f := by
  change (∫ ω, f ω ∂μ.toPMF.toMeasure)=_
  rw [PMF.integral_eq_sum]
  unfold mean
  apply Finset.sum_congr rfl
  intro ω _
  change (ENNReal.ofReal (μ ω)).toReal • f ω=μ ω*f ω
  rw [ENNReal.toReal_ofReal (μ.nonneg ω),smul_eq_mul]

theorem setIntegral_toMeasure (μ : ProbabilityVector Ω) (f : Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, f ω ∂μ.toMeasure)=μ.mean (fun ω ↦ if ω∈A then f ω else 0) := by
  rw [← integral_indicator hA,integral_toMeasure]
  congr 1

theorem ae_toMeasure_iff (μ : ProbabilityVector Ω) (P : Ω → Prop) :
    (∀ᵐ ω ∂μ.toMeasure, P ω) ↔ ∀ ω, 0<μ ω → P ω := by
  rw [ae_iff_of_countable]
  simp only [toMeasure_singleton,ne_eq,ENNReal.ofReal_eq_zero,not_le]

end
end Tournament.ProbabilityVector

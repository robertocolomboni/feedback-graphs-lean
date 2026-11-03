module

public import Tournament.Probability.FiniteMeasure
public import Tournament.Probability.FiniteConditional
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

namespace Tournament.FiniteConditional

open scoped BigOperators MeasureTheory Classical
open MeasureTheory Filter

noncomputable section

variable {Ω S : Type*} [Fintype Ω] [Fintype S]
variable [mΩ : MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [mS : MeasurableSpace S] [MeasurableSingletonClass S]

theorem condExp_of_fiber_identity (μ : ProbabilityVector Ω) (info : Ω → S) (f : Ω → ℝ) (H : S → ℝ)
    (hfiber : ∀ s, fiberSum μ info f s=H s*fiberMass μ info s) :
    μ.toMeasure[f | MeasurableSpace.comap info mS] =ᵐ[μ.toMeasure] fun ω ↦ H (info ω) := by
  let mh := MeasurableSpace.comap info mS
  let : MeasurableSpace Ω := mΩ
  have hinfo : Measurable info := measurable_of_finite info
  have hm : mh≤mΩ := hinfo.comap_le
  have hH : Measurable H := measurable_of_finite H
  have hsmall : Measurable[mh] (fun ω ↦ H (info ω)) := hH.comp (comap_measurable info)
  have hset (A : Set Ω) (hA : MeasurableSet[mh] A) (_hfin : μ.toMeasure A<⊤) :
      (∫ ω in A, H (info ω) ∂μ.toMeasure)=∫ ω in A, f ω ∂μ.toMeasure := by
    obtain ⟨B,_hB,hBA⟩ := MeasurableSpace.measurableSet_comap.mp hA
    have hglobal : MeasurableSet A := hm A hA
    rw [μ.setIntegral_toMeasure _ A hglobal,μ.setIntegral_toMeasure _ A hglobal]
    subst A
    change μ.mean (fun ω ↦ if info ω∈B then H (info ω) else 0)=
      μ.mean (fun ω ↦ if info ω∈B then f ω else 0)
    calc
      _ = ∑ s, (if s∈B then H s else 0)*fiberMass μ info s :=
        mean_fiber_mass μ info (fun s ↦ if s∈B then H s else 0)
      _ = ∑ s, (if s∈B then 1 else 0)*fiberSum μ info f s := by
        apply Finset.sum_congr rfl
        intro s _
        rw [hfiber s]
        by_cases hs : s∈B <;> simp [hs]
      _ = μ.mean (fun ω ↦ (if info ω∈B then 1 else 0)*f ω) :=
        (mean_fiber_expansion μ info (fun s ↦ if s∈B then 1 else 0) f).symm
      _ = _ := by
        congr 1
        funext ω
        by_cases hs : info ω∈B <;> simp [hs]
  have hCE : (fun ω ↦ H (info ω)) =ᵐ[μ.toMeasure] μ.toMeasure[f | mh] :=
    ae_eq_condExp_of_forall_setIntegral_eq hm (Integrable.of_finite (f := f))
      (fun _ _ _ ↦ (Integrable.of_finite (f := fun ω ↦ H (info ω))).integrableOn)
      hset hsmall.stronglyMeasurable.aestronglyMeasurable
  exact hCE.symm

end
end Tournament.FiniteConditional

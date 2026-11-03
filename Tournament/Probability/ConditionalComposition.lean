module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.CompProdEqIff

@[expose] public section

namespace Tournament.Probability

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
variable [MeasurableSpace B] [MeasurableSpace C]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
variable {κ : Kernel A B} {η : Kernel (A × B) C} [IsMarkovKernel κ] [IsMarkovKernel η]

omit [IsProbabilityMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η] in
theorem conditional_pair (hY : HasCondDistrib Y X κ μ)
    (hZ : HasCondDistrib Z (fun ω ↦ (X ω,Y ω)) η μ) :
    HasCondDistrib (fun ω ↦ (Y ω,Z ω)) X (κ ⊗ₖ η) μ := by
  have hRaw : HasLaw (fun ω ↦ ((X ω,Y ω),Z ω)) (((μ.map X) ⊗ₘ κ) ⊗ₘ η) μ := by
    change HasLaw (fun ω ↦ ((X ω,Y ω),Z ω))
      ((μ.map (fun ω ↦ (X ω,Y ω))) ⊗ₘ η) μ at hZ
    rwa [hY.map_eq] at hZ
  have hAssoc : HasLaw (MeasurableEquiv.prodAssoc : (A × B) × C ≃ᵐ A × (B × C))
      ((((μ.map X) ⊗ₘ κ) ⊗ₘ η).map MeasurableEquiv.prodAssoc) (((μ.map X) ⊗ₘ κ) ⊗ₘ η) :=
    ⟨MeasurableEquiv.prodAssoc.measurable.aemeasurable,rfl⟩
  have h := hAssoc.comp hRaw
  rw [Measure.compProd_assoc'] at h
  exact h

omit [IsMarkovKernel κ] [IsMarkovKernel η] in
theorem conditional_next (hY : HasCondDistrib Y X κ μ)
    (hZ : HasCondDistrib Z (fun ω ↦ (X ω,Y ω)) η μ) :
    HasCondDistrib Z X (κ ⊗ₖ η).snd μ := (conditional_pair hY hZ).snd

theorem kernel_prod_eq_compProd (κ : Kernel A B) (ξ : Kernel A C) [IsMarkovKernel κ] [IsMarkovKernel ξ] :
    κ ×ₖ ξ=κ ⊗ₖ (ξ.comap Prod.fst measurable_fst) := by
  ext a s hs
  rw [Kernel.prod_apply',Kernel.compProd_apply]
  · rfl
  · exact hs
  · exact hs

theorem independent_enlargement {ξ : Kernel A C} [IsMarkovKernel ξ]
    (hJoint : HasCondDistrib (fun ω ↦ (Y ω,Z ω)) X (κ ×ₖ ξ) μ) :
    HasCondDistrib Z (fun ω ↦ (X ω,Y ω))
      (ξ.comap (fun q : A × B ↦ q.1) measurable_fst : Kernel (A × B) C) μ := by
  rw [kernel_prod_eq_compProd] at hJoint
  exact hJoint.of_compProd

theorem replace_independent_marginal {ξ ζ : Kernel A C} [IsMarkovKernel ξ] [IsMarkovKernel ζ]
    [MeasurableSpace.CountableOrCountablyGenerated A C]
    (hJoint : HasCondDistrib (fun ω ↦ (Y ω,Z ω)) X (κ ×ₖ ξ) μ)
    (hZ : HasCondDistrib Z X ζ μ) :
    HasCondDistrib (fun ω ↦ (Y ω,Z ω)) X (κ ×ₖ ζ) μ := by
  have hMarg : HasCondDistrib Z X ξ μ := by
    simpa only [Kernel.snd_prod] using hJoint.snd
  have hAE : ξ =ᵐ[μ.map X] ζ := Kernel.ae_eq_of_compProd_eq (hMarg.map_eq.symm.trans hZ.map_eq)
  have hProd : κ ×ₖ ξ =ᵐ[μ.map X] κ ×ₖ ζ := by
    filter_upwards [hAE] with a ha
    simp only [Kernel.prod_apply,ha]
  change HasLaw (fun ω ↦ (X ω,(Y ω,Z ω))) ((μ.map X) ⊗ₘ (κ ×ₖ ζ)) μ
  rw [← Measure.compProd_congr hProd]
  exact hJoint

theorem conditional_const_of_const_condition (X : Ω → A) (Y : Ω → B)
    (a : A) (hX : X=fun _ ↦ a) (hY : Measurable Y)
    (ν : Measure B) [IsProbabilityMeasure ν] (hLaw : HasLaw Y ν μ) :
    HasCondDistrib Y X (Kernel.const A ν) μ := by
  subst X
  refine ⟨(measurable_const.prodMk hY).aemeasurable,?_⟩
  rw [Measure.map_const,measure_univ,one_smul,Measure.compProd_const,Measure.dirac_prod]
  rw [← hLaw.map_eq,Measure.map_map measurable_prodMk_left hY]
  rfl

end
end Tournament.Probability

module

public import Tournament.Probability.ConditionalComposition
public import Mathlib.Probability.Independence.Conditional

@[expose] public section

namespace Tournament.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

noncomputable section

variable {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
variable [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
variable [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]

def CondIndepGiven (X : Ω → A) (Y : Ω → B) (Z : Ω → C) (μ : Measure Ω) : Prop :=
  ∀ (s : Set B) (t : Set C), MeasurableSet s → MeasurableSet t →
    (μ⟦Y ⁻¹' s ∩ Z ⁻¹' t | MeasurableSpace.comap X inferInstance⟧) =ᵐ[μ]
      fun ω ↦ (μ⟦Y ⁻¹' s | MeasurableSpace.comap X inferInstance⟧) ω *
        (μ⟦Z ⁻¹' t | MeasurableSpace.comap X inferInstance⟧) ω

omit [StandardBorelSpace B] [Nonempty B] [StandardBorelSpace C] [Nonempty C] in

theorem condIndepGiven_iff_native [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (Y : Ω → B) (hY : Measurable Y)
    (Z : Ω → C) (hZ : Measurable Z) :
    CondIndepGiven X Y Z μ ↔ Y ⟂ᵢ[X,hX;μ] Z := by
  exact (condIndepFun_iff_condExp_inter_preimage_eq_mul hY hZ).symm

theorem conditional_product_of_indep_given (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (Y : Ω → B) (hY : Measurable Y)
    (Z : Ω → C) (hZ : Measurable Z) (hIndep : CondIndepGiven X Y Z μ) :
    HasCondDistrib (fun ω ↦ (Y ω,Z ω)) X (condDistrib Y X μ ×ₖ condDistrib Z X μ) μ := by
  have hRect (s : Set B) (t : Set C) (hs : MeasurableSet s) (ht : MeasurableSet t) :
      (fun ω ↦ condDistrib (fun ω ↦ (Y ω,Z ω)) X μ (X ω) (s ×ˢ t)) =ᵐ[μ]
        fun ω ↦ condDistrib Y X μ (X ω) s * condDistrib Z X μ (X ω) t := by
    filter_upwards [condDistrib_ae_eq_condExp hX (hY.prodMk hZ) (hs.prod ht),
      condDistrib_ae_eq_condExp hX hY hs, condDistrib_ae_eq_condExp hX hZ ht,
      hIndep s t hs ht] with ω hPair hLeft hRight hFactor
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
    simp only [ENNReal.toReal_mul]
    simpa only [measureReal_def, Set.mk_preimage_prod] using
      hPair.trans (hFactor.trans (congrArg₂ (· * ·) hLeft.symm hRight.symm))
  refine ⟨(hX.prodMk (hY.prodMk hZ)).aemeasurable,?_⟩
  rw [← compProd_map_condDistrib hX.aemeasurable (hY.prodMk hZ).aemeasurable]
  apply Measure.ext_prod₃
  intro u s t hu hs ht
  rw [Measure.compProd_apply_prod hu (hs.prod ht),
    Measure.compProd_apply_prod hu (hs.prod ht)]
  simp only [Kernel.prod_apply_prod]
  apply setLIntegral_congr_fun_ae hu
  have hMap : (fun a ↦ condDistrib (fun ω ↦ (Y ω,Z ω)) X μ a (s ×ˢ t)) =ᵐ[μ.map X]
      fun a ↦ condDistrib Y X μ a s * condDistrib Z X μ a t := by
    have hm : MeasurableSet {a | condDistrib (fun ω ↦ (Y ω,Z ω)) X μ a (s ×ˢ t) =
        condDistrib Y X μ a s * condDistrib Z X μ a t} :=
      measurableSet_eq_fun (Kernel.measurable_coe _ (hs.prod ht))
        ((Kernel.measurable_coe _ hs).mul (Kernel.measurable_coe _ ht))
    exact (ae_map_iff (μ := μ) hX.aemeasurable hm).mpr (hRect s t hs ht)
  filter_upwards [hMap] with a ha using fun _ ↦ ha

theorem conditional_product_of_indep_given_marginals
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (Y : Ω → B) (hY : Measurable Y)
    (Z : Ω → C) (hZ : Measurable Z) (hIndep : CondIndepGiven X Y Z μ)
    (κ : Kernel A B) (ξ : Kernel A C) [IsMarkovKernel κ] [IsMarkovKernel ξ]
    (hYκ : HasCondDistrib Y X κ μ) (hZξ : HasCondDistrib Z X ξ μ) :
    HasCondDistrib (fun ω ↦ (Y ω,Z ω)) X (κ ×ₖ ξ) μ := by
  have hJoint := conditional_product_of_indep_given μ X hX Y hY Z hZ hIndep
  have hLeft : HasCondDistrib Y X (condDistrib Y X μ) μ := by
    simpa only [Kernel.fst_prod] using hJoint.fst
  have hRight : HasCondDistrib Z X (condDistrib Z X μ) μ := by
    simpa only [Kernel.snd_prod] using hJoint.snd
  have hLeftAE : condDistrib Y X μ =ᵐ[μ.map X] κ :=
    Kernel.ae_eq_of_compProd_eq (hLeft.map_eq.symm.trans hYκ.map_eq)
  have hRightAE : condDistrib Z X μ =ᵐ[μ.map X] ξ :=
    Kernel.ae_eq_of_compProd_eq (hRight.map_eq.symm.trans hZξ.map_eq)
  have hProd : condDistrib Y X μ ×ₖ condDistrib Z X μ =ᵐ[μ.map X] κ ×ₖ ξ := by
    filter_upwards [hLeftAE,hRightAE] with a ha hb
    simp only [Kernel.prod_apply,ha,hb]
  change HasLaw (fun ω ↦ (X ω,(Y ω,Z ω))) ((μ.map X) ⊗ₘ (κ ×ₖ ξ)) μ
  rw [← Measure.compProd_congr hProd]
  exact hJoint

theorem conditional_law_of_singleton_condExp [Countable B] [MeasurableSingletonClass B]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (Y : Ω → B) (hY : Measurable Y)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (hProb : ∀ j : B,
      (μ⟦Y ⁻¹' {j} | MeasurableSpace.comap X inferInstance⟧) =ᵐ[μ]
        fun ω ↦ (κ (X ω)).real {j}) :
    HasCondDistrib Y X κ μ := by
  have hCanonical : HasCondDistrib Y X (condDistrib Y X μ) μ :=
    ⟨(hX.prodMk hY).aemeasurable,
      (compProd_map_condDistrib hX.aemeasurable hY.aemeasurable).symm⟩
  have hSingleton (j : B) : (fun a ↦ (condDistrib Y X μ a).real {j}) =ᵐ[μ.map X]
      fun a ↦ (κ a).real {j} := by
    have hSource := (condDistrib_ae_eq_condExp hX hY (measurableSet_singleton j)).trans (hProb j)
    have hm : MeasurableSet {a | (condDistrib Y X μ a).real {j} = (κ a).real {j}} :=
      measurableSet_eq_fun
        ((Kernel.measurable_coe _ (measurableSet_singleton j)).ennreal_toReal)
        ((Kernel.measurable_coe _ (measurableSet_singleton j)).ennreal_toReal)
    exact (ae_map_iff (μ := μ) hX.aemeasurable hm).mpr hSource
  have hKernels : condDistrib Y X μ =ᵐ[μ.map X] κ := by
    have hAll : ∀ᵐ a ∂μ.map X, ∀ j : B,
        (condDistrib Y X μ a).real {j} = (κ a).real {j} :=
      (ae_all_iff).mpr hSingleton
    filter_upwards [hAll] with a ha
    exact Measure.ext_of_measureReal_singleton ha
  change HasLaw (fun ω ↦ (X ω,Y ω)) ((μ.map X) ⊗ₘ κ) μ
  rw [← Measure.compProd_congr hKernels]
  exact hCanonical

theorem conditional_product_of_indep [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (Y : Ω → B) (hY : Measurable Y)
    (Z : Ω → C) (hZ : Measurable Z) (hIndep : Y ⟂ᵢ[X,hX;μ] Z) :
    HasCondDistrib (fun ω ↦ (Y ω,Z ω)) X (condDistrib Y X μ ×ₖ condDistrib Z X μ) μ := by
  refine ⟨(hX.prodMk (hY.prodMk hZ)).aemeasurable,?_⟩
  rw [Measure.compProd_eq_comp_prod]
  exact (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hY hZ hX).mp hIndep

end
end Tournament.Probability

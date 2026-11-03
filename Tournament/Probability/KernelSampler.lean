module

public import Tournament.Probability.VectorKernel
public import Tournament.Probability.FiniteConditionalLaw
public import Mathlib.Probability.Kernel.Representation
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

namespace Tournament.Probability.KernelSampler

open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval ENNReal
noncomputable section

abbrev ProbRow (Y : Type*) [MeasurableSpace Y] :=
  {μ : Measure Y // IsProbabilityMeasure μ}

def universalKernel (Y : Type*) [MeasurableSpace Y] : Kernel (ProbRow Y) Y where
  toFun := Subtype.val
  measurable' := measurable_subtype_coe

instance universalKernel_markov (Y : Type*) [MeasurableSpace Y] :
    IsMarkovKernel (universalKernel Y) where
  isProbabilityMeasure μ := μ.property

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable [Nonempty Y] [StandardBorelSpace Y]

def universalDraw : ProbRow Y → unitInterval → Y :=
  Classical.choose (Kernel.exists_measurable_map_eq_unitInterval (universalKernel Y))

theorem universalDraw_measurable :
    Measurable (Function.uncurry (universalDraw (Y := Y))) :=
  (Classical.choose_spec
    (Kernel.exists_measurable_map_eq_unitInterval (universalKernel Y))).1

theorem universalDraw_map (μ : ProbRow Y) :
    (volume : Measure unitInterval).map (universalDraw μ) = μ.val :=
  (Classical.choose_spec
    (Kernel.exists_measurable_map_eq_unitInterval (universalKernel Y))).2 μ

def draw (κ : Kernel X Y) [IsMarkovKernel κ] : X → unitInterval → Y :=
  fun x u ↦ universalDraw ⟨κ x, inferInstance⟩ u

theorem draw_measurable (κ : Kernel X Y) [IsMarkovKernel κ] : Measurable (Function.uncurry (draw κ)) := by
  have hrow : Measurable (fun x : X ↦ (⟨κ x, inferInstance⟩ : ProbRow Y)) :=
    κ.measurable.subtype_mk
  exact universalDraw_measurable.comp ((hrow.comp measurable_fst).prodMk measurable_snd)

theorem draw_map (κ : Kernel X Y) [IsMarkovKernel κ] (x : X) :
    (volume : Measure unitInterval).map (draw κ x)=κ x :=
  universalDraw_map ⟨κ x, inferInstance⟩

theorem draw_eq_of_row_eq_cross {X' : Type*} [MeasurableSpace X']
    (κ : Kernel X Y) [IsMarkovKernel κ] (κ' : Kernel X' Y) [IsMarkovKernel κ']
    (x : X) (x' : X') (h : κ x = κ' x') (u : unitInterval) :
    draw κ x u = draw κ' x' u := by
  exact congrArg (fun μ : ProbRow Y ↦ universalDraw μ u) (Subtype.ext h)

theorem draw_eq_of_row_eq (κ : Kernel X Y) [IsMarkovKernel κ]
    (x x' : X) (h : κ x = κ x') (u : unitInterval) :
    draw κ x u = draw κ x' u :=
  draw_eq_of_row_eq_cross κ κ x x' h u

theorem draw_hasLaw (κ : Kernel X Y) [IsMarkovKernel κ] (x : X) :
    HasLaw (draw κ x) (κ x) (volume : Measure unitInterval) :=
  ⟨(draw_measurable κ).of_uncurry_left.aemeasurable,draw_map κ x⟩

theorem draw_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (κ : Kernel X Y) [IsMarkovKernel κ] (x : Ω → X) (u : Ω → unitInterval)
    (hx : Measurable x) (hu : Measurable u) : Measurable (fun ω ↦ draw κ (x ω) (u ω)) :=
  (draw_measurable κ).comp (hx.prodMk hu)

variable [Fintype Y]
variable {H : Type*} [Fintype H] [MeasurableSpace H] [DiscreteMeasurableSpace H]

theorem attach_finite_hasLaw (κ : Kernel X Y) [IsMarkovKernel κ] (c : H → X)
    (μ : ProbabilityVector H) (row : H → ProbabilityVector Y)
    (hRow : ∀ h, κ (c h)=(row h).toMeasure) :
    HasLaw (fun q : H × unitInterval ↦ (q.1,draw κ (c q.1) q.2))
      (μ.joint row).toMeasure (μ.toMeasure.prod (volume : Measure unitInterval)) := by
  have hMeas : Measurable (fun q : H × unitInterval ↦ (q.1,draw κ (c q.1) q.2)) :=
    measurable_fst.prodMk (draw_measurable_comp κ (fun q ↦ c q.1) Prod.snd
      ((Measurable.of_discrete (f := c)).comp (f := (Prod.fst : H × unitInterval → H)) measurable_fst)
      measurable_snd)
  refine ⟨hMeas.aemeasurable,?_⟩
  change (μ.toMeasure.prod (volume : Measure unitInterval)).map
    (fun q : H × unitInterval ↦ (q.1,draw κ (c q.1) q.2))=(μ.joint row).toMeasure
  apply Measure.ext_of_singleton
  rintro ⟨h,y⟩
  rw [Measure.map_apply hMeas (measurableSet_singleton (h,y))]
  have hPre : (fun q : H × unitInterval ↦ (q.1,draw κ (c q.1) q.2)) ⁻¹' {(h,y)}=
      ({h} : Set H) ×ˢ {u | draw κ (c h) u=y} := by
    ext q
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Prod.mk.injEq,Set.mem_prod,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hh,hy⟩
      exact ⟨hh,by simpa only [hh] using hy⟩
    · rintro ⟨hh,hy⟩
      exact ⟨hh,by simpa only [hh] using hy⟩
  have hSample : (volume : Measure unitInterval) {u | draw κ (c h) u=y}=(row h).toMeasure {y} := by
    calc
      _ = κ (c h) {y} := (draw_hasLaw κ (c h)).measure_eq (p := fun a ↦ a=y) (measurableSet_singleton y)
      _ = _ := by rw [hRow h]
  calc
    _ = μ.toMeasure {h}*(volume : Measure unitInterval) {u | draw κ (c h) u=y} := by
      rw [hPre,Measure.prod_prod]
    _ = μ.toMeasure {h}*(row h).toMeasure {y} := by rw [hSample]
    _ = ENNReal.ofReal (μ h)*ENNReal.ofReal (row h y) := by
      rw [ProbabilityVector.toMeasure_singleton μ h,ProbabilityVector.toMeasure_singleton (row h) y]
    _ = ENNReal.ofReal (μ h*row h y) := (ENNReal.ofReal_mul (μ.nonneg h)).symm
    _ = _ := (ProbabilityVector.toMeasure_singleton (μ.joint row) (h,y)).symm

theorem extend_finite_hasLaw {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → H) (hf : Measurable f) (μ : ProbabilityVector H) (hLaw : HasLaw f μ.toMeasure ν)
    (κ : Kernel X Y) [IsMarkovKernel κ] (c : H → X) (row : H → ProbabilityVector Y)
    (hRow : ∀ h, κ (c h)=(row h).toMeasure) :
    HasLaw (fun q : Ω × unitInterval ↦ (f q.1,draw κ (c (f q.1)) q.2))
      (μ.joint row).toMeasure (ν.prod (volume : Measure unitInterval)) := by
  have hFirst : HasLaw (fun q : Ω × unitInterval ↦ f q.1) μ.toMeasure
      (ν.prod (volume : Measure unitInterval)) :=
    hLaw.comp (measurePreserving_fst (μ := ν) (ν := (volume : Measure unitInterval))).hasLaw
  have hSecond : HasLaw (fun q : Ω × unitInterval ↦ q.2) (volume : Measure unitInterval)
      (ν.prod (volume : Measure unitInterval)) :=
    (measurePreserving_snd (μ := ν) (ν := (volume : Measure unitInterval))).hasLaw
  have hPair := (indepFun_prod hf measurable_id).hasLaw_prod hFirst hSecond
  exact (attach_finite_hasLaw κ c μ row hRow).comp hPair

end
end Tournament.Probability.KernelSampler

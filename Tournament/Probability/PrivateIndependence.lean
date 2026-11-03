module

public import Mathlib.Probability.HasLaw

@[expose] public section

namespace Tournament.Probability

open MeasureTheory ProbabilityTheory

noncomputable section

theorem independent_pullback {Ω A B D : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace D] {P : Measure Ω} {μ : Measure A}
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (r : Ω → A) (hR : HasLaw r μ P) (f : A → B) (g : A → D)
    (hf : Measurable f) (hg : Measurable g) (hi : IndepFun f g μ) :
    IndepFun (fun ω ↦ f (r ω)) (fun ω ↦ g (r ω)) P := by
  have hF : HasLaw f (μ.map f) μ := ⟨hf.aemeasurable,rfl⟩
  have hG : HasLaw g (μ.map g) μ := ⟨hg.aemeasurable,rfl⟩
  exact (indepFun_iff_hasLaw_prodMk_prod (hF.comp hR) (hG.comp hR)).mpr
    ((hi.hasLaw_prod hF hG).comp hR)

theorem independent_private_extension {Ω Seed A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Seed] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (f : Ω → A) (g : Ω → B) (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g μ) :
    IndepFun (fun p : Seed × Ω ↦ (p.1,f p.2)) (fun p ↦ g p.2) (ν.prod μ) := by
  let : IsProbabilityMeasure (μ.map f) := inferInstance
  let : IsProbabilityMeasure (μ.map g) := inferInstance
  have hFirst : HasLaw (fun p : Seed × Ω ↦ (p.1,f p.2)) (ν.prod (μ.map f)) (ν.prod μ) := by
    refine ⟨measurable_fst.aemeasurable.prodMk (hf.comp measurable_snd).aemeasurable,?_⟩
    calc
      _ = (ν.map id).prod (μ.map f) := (Measure.map_prod_map ν μ measurable_id hf).symm
      _ = _ := by rw [Measure.map_id]
  have hG : HasLaw g (μ.map g) μ := ⟨hg.aemeasurable,rfl⟩
  have hSecond : HasLaw (fun p : Seed × Ω ↦ g p.2) (μ.map g) (ν.prod μ) :=
    hG.comp (measurePreserving_snd (μ := ν) (ν := μ)).hasLaw
  have hRaw : HasLaw (fun p : Seed × Ω ↦ (p.1,(f p.2,g p.2)))
      (ν.prod ((μ.map f).prod (μ.map g))) (ν.prod μ) := by
    refine ⟨measurable_fst.aemeasurable.prodMk ((hf.prodMk hg).comp measurable_snd).aemeasurable,?_⟩
    calc
      _ = (ν.map id).prod (μ.map (fun ω ↦ (f ω,g ω))) :=
        (Measure.map_prod_map ν μ measurable_id (hf.prodMk hg)).symm
      _ = _ := by rw [Measure.map_id,hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable]
  have hAssoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : Seed × (A × B) ≃ᵐ (Seed × A) × B)
      (ν.prod ((μ.map f).prod (μ.map g))) ((ν.prod (μ.map f)).prod (μ.map g)) :=
    (measurePreserving_prodAssoc ν (μ.map f) (μ.map g)).symm
  have hJoint : HasLaw (fun p : Seed × Ω ↦ ((p.1,f p.2),g p.2))
      ((ν.prod (μ.map f)).prod (μ.map g)) (ν.prod μ) := hAssoc.hasLaw.comp hRaw
  exact (indepFun_iff_hasLaw_prodMk_prod hFirst hSecond).mpr hJoint

end
end Tournament.Probability

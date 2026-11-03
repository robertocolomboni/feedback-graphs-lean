module

public import Tournament.Upper.DartboardFreshDraws
public import Tournament.Upper.DartboardFiniteHorizon
public import Tournament.Probability.KernelSampler

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal BigOperators unitInterval

noncomputable section

theorem conditional_sample_of_independent_seed
    {Ω A S B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace S] [MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (X : Ω → A) (U : Ω → S) (hX : Measurable X)
    (hU : HasLaw U ν μ) (hIndep : X ⟂ᵢ[μ] U)
    (κ : Kernel A B) [IsMarkovKernel κ] (f : A → S → B)
    (hf : Measurable (Function.uncurry f)) (hRow : ∀ a, ν.map (f a) = κ a) :
    HasCondDistrib (fun ω ↦ f (X ω) (U ω)) X κ μ := by
  have hMap : ((μ.map X).prod ν).map (fun q : A × S ↦ (q.1,f q.1 q.2)) =
      (μ.map X) ⊗ₘ κ := by
    have hm : Measurable (fun q : A × S ↦ (q.1,f q.1 q.2)) := measurable_fst.prodMk hf
    ext s hs
    rw [Measure.map_apply hm hs,
      Measure.prod_apply (hs.preimage hm),
      Measure.compProd_apply hs]
    apply lintegral_congr
    intro a
    rw [← hRow a, Measure.map_apply hf.of_uncurry_left (hs.preimage measurable_prodMk_left)]
    rfl
  have hPair := hIndep.hasLaw_prod (show HasLaw X (μ.map X) μ from ⟨hX.aemeasurable,rfl⟩) hU
  have hSample : HasLaw (fun q : A × S ↦ (q.1,f q.1 q.2)) ((μ.map X) ⊗ₘ κ)
      ((μ.map X).prod ν) := ⟨(measurable_fst.prodMk hf).aemeasurable,hMap⟩
  exact hSample.comp hPair

theorem conditional_map_with_context
    {Ω A S B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace S] [MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A) (Y : Ω → S)
    (κ : Kernel A S) [IsMarkovKernel κ] (κ' : Kernel A B) [IsMarkovKernel κ']
    (hY : HasCondDistrib Y X κ μ) (f : A → S → B)
    (hf : Measurable (Function.uncurry f)) (hRow : ∀ a, (κ a).map (f a) = κ' a) :
    HasCondDistrib (fun ω ↦ f (X ω) (Y ω)) X κ' μ := by
  have hm : Measurable (fun q : A × S ↦ (q.1,f q.1 q.2)) := measurable_fst.prodMk hf
  have hMap : ((μ.map X) ⊗ₘ κ).map (fun q : A × S ↦ (q.1,f q.1 q.2)) =
      (μ.map X) ⊗ₘ κ' := by
    ext s hs
    rw [Measure.map_apply hm hs, Measure.compProd_apply (hs.preimage hm),
      Measure.compProd_apply hs]
    apply lintegral_congr
    intro a
    rw [← hRow a, Measure.map_apply hf.of_uncurry_left (hs.preimage measurable_prodMk_left)]
    rfl
  exact (show HasLaw (fun q : A × S ↦ (q.1,f q.1 q.2)) ((μ.map X) ⊗ₘ κ')
      ((μ.map X) ⊗ₘ κ) from ⟨hm.aemeasurable,hMap⟩).comp hY

variable {A ι : Type*} [MeasurableSpace A] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

def keepingCoinKernel (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ)
    (hg : ∀ a i, 0≤g a i) (hgm : ∀ i, Measurable (fun a ↦ g a i)) : Kernel (A × ι) Bool :=
  ProbabilityVector.kernel
    (fun q ↦ Restarts.coin (keep η (g q.1) q.2) (keep_pos η (g q.1) q.2).le
      (keep_le_one η hη (g q.1) (hg q.1) q.2)) (by
        intro b
        apply measurable_from_prod_countable_left
        intro i
        cases b
        · exact measurable_const.sub (((hgm i).const_mul (-η)).exp)
        · exact ((hgm i).const_mul (-η)).exp)

instance keepingCoinKernel_markov (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ)
    (hg : ∀ a i, 0≤g a i) (hgm : ∀ i, Measurable (fun a ↦ g a i)) :
    IsMarkovKernel (keepingCoinKernel η hη g hg hgm) := by
  unfold keepingCoinKernel
  infer_instance

def resamplingKernel (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (g : A → ι → ℝ) (hgm : ∀ i, Measurable (fun a ↦ g a i)) : Kernel (A × ι) ι :=
  ProbabilityVector.kernel (fun q ↦ Model.exponentialUpdate (p q.1) η (g q.1))
    (fun i ↦ (update_weight_measurable p hp g hgm η i).comp measurable_fst)

instance resamplingKernel_markov (p : A → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (η : ℝ) (g : A → ι → ℝ)
    (hgm : ∀ i, Measurable (fun a ↦ g a i)) : IsMarkovKernel (resamplingKernel p hp η g hgm) := by
  unfold resamplingKernel
  infer_instance

def freshUniformOutput (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i)
    (hgm : ∀ i, Measurable (fun a ↦ g a i)) (q : A × ι) (u : unitInterval × unitInterval) : ι :=
  if Tournament.Probability.KernelSampler.draw (keepingCoinKernel η hη g hg hgm) q u.1 then q.2
  else Tournament.Probability.KernelSampler.draw (resamplingKernel p hp η g hgm) q u.2

theorem freshUniformOutput_measurable (p : A → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (η : ℝ) (hη : 0≤η)
    (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i) (hgm : ∀ i, Measurable (fun a ↦ g a i)) :
    Measurable (Function.uncurry (freshUniformOutput p hp η hη g hg hgm)) := by
  have hc := Tournament.Probability.KernelSampler.draw_measurable_comp
    (keepingCoinKernel η hη g hg hgm) (fun q : (A × ι) × (unitInterval × unitInterval) ↦ q.1)
    (fun q ↦ q.2.1) measurable_fst (measurable_fst.comp measurable_snd)
  have hd := Tournament.Probability.KernelSampler.draw_measurable_comp
    (resamplingKernel p hp η g hgm) (fun q : (A × ι) × (unitInterval × unitInterval) ↦ q.1)
    (fun q ↦ q.2.2) measurable_fst (measurable_snd.comp measurable_snd)
  exact Measurable.ite (hc (measurableSet_singleton true)) (measurable_snd.comp measurable_fst) hd

theorem freshUniformOutput_map (p : A → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (η : ℝ) (hη : 0≤η)
    (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i) (hgm : ∀ i, Measurable (fun a ↦ g a i)) (q : A × ι) :
    ((volume : Measure unitInterval).prod volume).map (freshUniformOutput p hp η hη g hg hgm q) =
      transitionRowKernel p hp η hη g hg hgm q := by
  let c := Tournament.Probability.KernelSampler.draw (keepingCoinKernel η hη g hg hgm) q
  let d := Tournament.Probability.KernelSampler.draw (resamplingKernel p hp η g hgm) q
  have hc : Measurable c := (Tournament.Probability.KernelSampler.draw_measurable _).of_uncurry_left
  have hd : Measurable d := (Tournament.Probability.KernelSampler.draw_measurable _).of_uncurry_left
  have hPair : ((volume : Measure unitInterval).prod volume).map (Prod.map c d) =
      (freshDrawLaw (p q.1) η hη (g q.1) (hg q.1) q.2).toMeasure := by
    rw [← Measure.map_prod_map _ _ hc hd]
    rw [Tournament.Probability.KernelSampler.draw_map, Tournament.Probability.KernelSampler.draw_map]
    rw [freshDrawLaw, ProbabilityVector.toMeasure_joint _ _ (fun _ ↦ measurable_const)]
    exact Measure.compProd_const.symm
  calc
    _ = (((volume : Measure unitInterval).prod volume).map (Prod.map c d)).map
        (fun r : Bool × ι ↦ if r.1 then q.2 else r.2) := by
      rw [Measure.map_map (Measurable.of_discrete) (hc.prodMap hd)]
      rfl
    _ = _ := by rw [hPair]; exact freshDrawLaw_map (p q.1) η hη (g q.1) (hg q.1) q.2

omit [Nonempty ι] in

theorem keep_resample_row_map (p : A → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (η : ℝ) (hη : 0≤η)
    (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i) (hgm : ∀ i, Measurable (fun a ↦ g a i)) (q : A × ι) :
    ((keepingCoinKernel η hη g hg hgm ×ₖ resamplingKernel p hp η g hgm) q).map
      (fun r : Bool × ι ↦ if r.1 then q.2 else r.2) = transitionRowKernel p hp η hη g hg hgm q := by
  have hLaw : (freshDrawLaw (p q.1) η hη (g q.1) (hg q.1) q.2).toMeasure =
      (keepingCoinKernel η hη g hg hgm ×ₖ resamplingKernel p hp η g hgm) q := by
    rw [Kernel.prod_apply, freshDrawLaw, ProbabilityVector.toMeasure_joint _ _ (fun _ ↦ measurable_const)]
    exact Measure.compProd_const
  rw [← hLaw]
  exact freshDrawLaw_map (p q.1) η hη (g q.1) (hg q.1) q.2

omit [Nonempty ι] in
theorem conditional_keep_resample_of_joint
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A × ι) (C : Ω → Bool) (R J : Ω → ι)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i)
    (hgm : ∀ i, Measurable (fun a ↦ g a i))
    (hJoint : HasCondDistrib (fun ω ↦ (C ω,R ω)) X
      (keepingCoinKernel η hη g hg hgm ×ₖ resamplingKernel p hp η g hgm) μ)
    (hUpdate : J =ᵐ[μ] fun ω ↦ if C ω then (X ω).2 else R ω) :
    HasCondDistrib J X (transitionRowKernel p hp η hη g hg hgm) μ := by
  have hf : Measurable (fun q : (A × ι) × (Bool × ι) ↦ if q.2.1 then q.1.2 else q.2.2) :=
    Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
      (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)
  have h := conditional_map_with_context μ X (fun ω ↦ (C ω,R ω))
    (keepingCoinKernel η hη g hg hgm ×ₖ resamplingKernel p hp η g hgm)
    (transitionRowKernel p hp η hη g hg hgm) hJoint
    (fun q r ↦ if r.1 then q.2 else r.2) hf (keep_resample_row_map p hp η hη g hg hgm)
  exact h.congr (hUpdate.mono (fun _ hω ↦ congrArg (Prod.mk _) hω))

theorem conditional_keep_resample_of_uniforms
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A × ι) (hX : Measurable X) (U V : Ω → unitInterval) (J : Ω → ι)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i)
    (hgm : ∀ i, Measurable (fun a ↦ g a i))
    (hLaw : HasLaw (fun ω ↦ (U ω,V ω)) ((volume : Measure unitInterval).prod volume) μ)
    (hIndep : X ⟂ᵢ[μ] (fun ω ↦ (U ω,V ω)))
    (hUpdate : J =ᵐ[μ] fun ω ↦ freshUniformOutput p hp η hη g hg hgm (X ω) (U ω,V ω)) :
    HasCondDistrib J X (transitionRowKernel p hp η hη g hg hgm) μ := by
  have h := conditional_sample_of_independent_seed μ ((volume : Measure unitInterval).prod volume)
    X (fun ω ↦ (U ω,V ω)) hX hLaw hIndep (transitionRowKernel p hp η hη g hg hgm)
    (freshUniformOutput p hp η hη g hg hgm) (freshUniformOutput_measurable p hp η hη g hg hgm)
    (freshUniformOutput_map p hp η hη g hg hgm)
  exact h.congr (hUpdate.mono (fun _ hω ↦ congrArg (Prod.mk _) hω))

def freshCoinKernel (η : ℝ) (hη : 0≤η) (n : ℕ) : Kernel (LossHistory ι (n+1) × ι) Bool :=
  keepingCoinKernel η hη (fun h i ↦ (h (Fin.last n) i : ℝ))
    (fun h i ↦ (h (Fin.last n) i).coe_nonneg) (lastLoss_measurable n)

def freshResampleKernel (η : ℝ) (n : ℕ) : Kernel (LossHistory ι (n+1) × ι) ι :=
  resamplingKernel (fun h ↦ historyWeights η n (Fin.init h)) (previousWeights_measurable η n)
    η (fun h i ↦ (h (Fin.last n) i : ℝ)) (lastLoss_measurable n)

instance freshCoinKernel_markov (η : ℝ) (hη : 0≤η) (n : ℕ) :
    IsMarkovKernel (freshCoinKernel (ι := ι) η hη n) := by
  unfold freshCoinKernel
  infer_instance

instance freshResampleKernel_markov (η : ℝ) (n : ℕ) :
    IsMarkovKernel (freshResampleKernel (ι := ι) η n) := by
  unfold freshResampleKernel
  infer_instance

end
end Tournament.Upper.ShrinkingDartboard

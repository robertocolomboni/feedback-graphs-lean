module

public import Tournament.Upper.DartboardMeasurable
public import Tournament.Probability.ConditionalComposition

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {A ι : Type*} [MeasurableSpace A] [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem kernel_mean_transport (p : ProbabilityVector ι) (η : ℝ) (hη : 0≤η) (g : ι → ℝ)
    (hg : ∀ i, 0≤g i) (f : ι → ℝ) :
    p.mean (fun i ↦ ((kernel p η hη g hg).row i).mean f)=(Model.exponentialUpdate p η g).mean f := by
  unfold ProbabilityVector.mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (∑ i, p i*kernel p η hη g hg i j)*f j := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ ↦ by
        change p i*(kernel p η hη g hg i j*f j)=p i*kernel p η hη g hg i j*f j
        ring)
    _ = _ := by rw [kernel_marginal]

theorem transitionRowWeights_measurable (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i)
    (hgm : ∀ i, Measurable (fun a ↦ g a i)) (j : ι) :
    Measurable (fun q : A × ι ↦ (kernel (p q.1) η hη (g q.1) (hg q.1)).row q.2 j) := by
    apply measurable_from_prod_countable_left
    intro i
    have hk : Measurable (fun a ↦ keep η (g a) i) := ((hgm i).const_mul (-η)).exp
    have hu := update_weight_measurable p hp g hgm η j
    change Measurable (fun a ↦ (if i=j then keep η (g a) i else 0)+
      (1-keep η (g a) i)*Model.exponentialUpdate (p a) η (g a) j)
    by_cases hij : i=j
    · simp only [ite_eq_left hij]
      exact hk.add ((measurable_const.sub hk).mul hu)
    · simp only [ite_eq_right hij,zero_add]
      exact (measurable_const.sub hk).mul hu

def transitionRowKernel (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i)
    (hgm : ∀ i, Measurable (fun a ↦ g a i)) : Kernel (A × ι) ι :=
  ProbabilityVector.kernel (fun q ↦ (kernel (p q.1) η hη (g q.1) (hg q.1)).row q.2)
    (transitionRowWeights_measurable p hp η hη g hg hgm)

instance transitionRowKernel_markov (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i)
    (hgm : ∀ i, Measurable (fun a ↦ g a i)) : IsMarkovKernel (transitionRowKernel p hp η hη g hg hgm) := by
  unfold transitionRowKernel
  infer_instance

theorem transitionRowKernel_apply (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i)
    (hgm : ∀ i, Measurable (fun a ↦ g a i)) (a : A) (i : ι) :
    transitionRowKernel p hp η hη g hg hgm (a,i)=((kernel (p a) η hη (g a) (hg a)).row i).toMeasure := rfl

theorem transition_kernel_transport (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i)
    (hgm : ∀ i, Measurable (fun a ↦ g a i)) :
    ((ProbabilityVector.kernel p hp) ⊗ₖ transitionRowKernel p hp η hη g hg hgm).snd=
      ProbabilityVector.kernel (fun a ↦ Model.exponentialUpdate (p a) η (g a))
        (update_weight_measurable p hp g hgm η) := by
  apply Kernel.ext
  intro a
  have hi (f : ι → ℝ) :
      (∫ j, f j ∂((ProbabilityVector.kernel p hp) ⊗ₖ transitionRowKernel p hp η hη g hg hgm).snd a)=
        (Model.exponentialUpdate (p a) η (g a)).mean f := by
    rw [Kernel.snd_apply,integral_map measurable_snd.aemeasurable (Measurable.of_discrete (f := f)).aestronglyMeasurable,
      ProbabilityTheory.integral_compProd (Integrable.of_finite)]
    change (∫ i, (∫ j, f j ∂((kernel (p a) η hη (g a) (hg a)).row i).toMeasure) ∂(p a).toMeasure)=_
    simp_rw [ProbabilityVector.integral_toMeasure]
    exact kernel_mean_transport (p a) η hη (g a) (hg a) f
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro j
  have h := hi (({j} : Set ι).indicator (1 : ι → ℝ))
  rw [integral_indicator_one (measurableSet_singleton j)] at h
  calc
    _ = (Model.exponentialUpdate (p a) η (g a)).mean (({j} : Set ι).indicator (1 : ι → ℝ)) := h
    _ = ∫ i, ({j} : Set ι).indicator (1 : ι → ℝ) i ∂(Model.exponentialUpdate (p a) η (g a)).toMeasure :=
      (ProbabilityVector.integral_toMeasure _ _).symm
    _ = _ := integral_indicator_one (measurableSet_singleton j)

theorem conditional_update {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (I J : Ω → ι) (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (η : ℝ) (hη : 0≤η) (g : A → ι → ℝ) (hg : ∀ a i, 0≤g a i)
    (hgm : ∀ i, Measurable (fun a ↦ g a i))
    (hI : HasCondDistrib I X (ProbabilityVector.kernel p hp) μ)
    (hJ : HasCondDistrib J (fun ω ↦ (X ω,I ω)) (transitionRowKernel p hp η hη g hg hgm) μ) :
    HasCondDistrib J X (ProbabilityVector.kernel (fun a ↦ Model.exponentialUpdate (p a) η (g a))
      (update_weight_measurable p hp g hgm η)) μ := by
  have h := Tournament.Probability.conditional_next hI hJ
  rwa [transition_kernel_transport] at h

end
end Tournament.Upper.ShrinkingDartboard

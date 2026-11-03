module

public import Tournament.Lower.TranscriptLaws
public import Tournament.Lower.TransitionShift
public import Tournament.Lower.GaussianJointKL

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory InformationTheory Model.MeasurableGame
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

def conditionalEnergy (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (h : Information Seed S t.val) : ℝ :=
  shiftEnergy (currentShift E θ j h-parentShift E θ j t h)/(2*(Parameters.sigma T)^2)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [MeasurableSpace Seed] in
theorem conditionalEnergy_eq_mean_difference (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (h : Information Seed S t.val) :
    conditionalEnergy E θ j t h=
      (∑ c, (transitionMean E θ none t h c-transitionMean E θ j t h c)^2)/(2*(incrementVariance T:ℝ)) := by
  unfold conditionalEnergy shiftEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [transitionMean_difference]
  simp only [neg_sq,Pi.sub_apply]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [MeasurableSpace Seed] in
theorem conditionalEnergy_nonneg (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (h : Information Seed S t.val) : 0≤conditionalEnergy E θ j t h := by
  unfold conditionalEnergy shiftEnergy
  positivity

theorem conditionalEnergy_measurable (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    Measurable (conditionalEnergy (Seed := Seed) E θ j t) := by
  unfold conditionalEnergy shiftEnergy
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro c _
  exact (((measurable_pi_apply c).comp
    ((currentShift_measurable E θ j t.val).sub (parentShift_measurable E θ j t))).pow_const 2)

theorem conditionalEnergy_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j k : Coordinate S) (t : Fin T) :
    Integrable (conditionalEnergy E θ j t) (informationLaw ν π E θ k t) := by
  have heq : conditionalEnergy (Seed := Seed) E θ j t=
      (fun h ↦ (∑ c, (transitionMean E θ none t h c-transitionMean E θ j t h c)^2)/(2*(incrementVariance T:ℝ))) := by
    funext h
    exact conditionalEnergy_eq_mean_difference E θ j t h
  rw [heq]
  apply Integrable.div_const
  apply integrable_finsetSum
  intro c _
  exact (transitionMean_difference_memLp ν π E θ j k t c).integrable_sq

def expectedStepEnergy (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) (s : ℕ) : ℝ :=
  if hs : s<T then ∫ h, conditionalEnergy E θ j ⟨s,hs⟩ h ∂informationLaw ν π E θ none ⟨s,hs⟩ else 0

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem expectedStepEnergy_nonneg (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) (s : ℕ) : 0≤expectedStepEnergy (T := T) ν π E θ j s := by
  unfold expectedStepEnergy
  split_ifs
  · exact integral_nonneg (conditionalEnergy_nonneg E θ j _)
  · exact le_rfl

theorem transcript_kl_step (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    klDiv (transcriptLaw (T := T) ν π E θ none (t.val+1)) (transcriptLaw (T := T) ν π E θ j (t.val+1))=
      klDiv (transcriptLaw (T := T) ν π E θ none t.val) (transcriptLaw (T := T) ν π E θ j t.val)+
        ENNReal.ofReal (expectedStepEnergy (T := T) ν π E θ j t.val) := by
  have ht := t.isLt
  have hac := transcriptLaw_absolutelyContinuous (T := T) ν π E θ j t.val (by omega)
  have ha := informationLaw_ac ν π E θ j t hac
  have hjoint : (informationLaw ν π E θ none t) ⊗ₘ transitionKernel E θ none t ≪
      (informationLaw ν π E θ j t) ⊗ₘ transitionKernel E θ j t := by
    let : IsProbabilityMeasure (informationLaw ν π E θ j t) := informationLaw_probability ν π E θ j t
    let : IsMarkovKernel (transitionKernel (Seed := Seed) E θ j t) := transitionKernel_markov E θ j t
    apply ha.compProd
    exact Filter.Eventually.of_forall (fun h ↦ GaussianKL.productLaw_absolutelyContinuous _ _ _
      (incrementVariance_ne_zero T (by have ht := t.isLt; omega)))
  rw [transcriptLaw_succ ν π E θ none t,transcriptLaw_succ ν π E θ j t,
    Tournament.Probability.klDiv_map_embedding_of_ac _ _ (historyExtensionEquiv t.val).measurableEmbedding hjoint,
    klDiv_compProd_eq_add,informationLaw_kl ν π E θ j t hac]
  congr 1
  change klDiv ((informationLaw ν π E θ none t) ⊗ₘ
      GaussianKL.gaussianKernel (transitionMean E θ none t) (transitionMean_measurable E θ none t) _ _)
    ((informationLaw ν π E θ none t) ⊗ₘ
      GaussianKL.gaussianKernel (transitionMean E θ j t) (transitionMean_measurable E θ j t) _ _)=_
  rw [GaussianKL.gaussian_compProd_kl (informationLaw ν π E θ none t) _ _ _ _ _ _
    (fun c ↦ transitionMean_difference_memLp ν π E θ j none t c)]
  congr 1
  simp only [expectedStepEnergy,dite_eq_left t.isLt]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h ↦ (conditionalEnergy_eq_mean_difference E θ j t h).symm)

theorem transcript_kl_sum (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (n : ℕ) (hn : n≤T) :
    klDiv (transcriptLaw (T := T) ν π E θ none n) (transcriptLaw (T := T) ν π E θ j n)=
      ENNReal.ofReal (∑ s∈Finset.range n, expectedStepEnergy (T := T) ν π E θ j s) := by
  induction n with
  | zero =>
    have heq : transcriptLaw (T := T) ν π E θ j 0=transcriptLaw (T := T) ν π E θ none 0 := rfl
    rw [heq,klDiv_self]
    simp
  | succ n ih =>
    let t : Fin T := ⟨n,by omega⟩
    have hstep := transcript_kl_step ν π E θ j t
    change klDiv (transcriptLaw (T := T) ν π E θ none (n+1))
      (transcriptLaw (T := T) ν π E θ j (n+1))=_ at hstep
    rw [hstep,ih (by omega),Finset.sum_range_succ,
      ENNReal.ofReal_add (Finset.sum_nonneg (fun s _ ↦ expectedStepEnergy_nonneg ν π E θ j s))
        (expectedStepEnergy_nonneg ν π E θ j n)]

end
end Tournament.Lower

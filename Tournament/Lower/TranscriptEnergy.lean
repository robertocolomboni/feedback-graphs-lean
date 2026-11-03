module

public import Tournament.Lower.TranscriptKL

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory InformationTheory Model.MeasurableGame
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

def sampleConditionalEnergy (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ :=
  conditionalEnergy E θ j t (information π E θ none t p)

theorem sampleConditionalEnergy_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    Integrable (sampleConditionalEnergy π E θ j t) (privateLaw ν S T) :=
  (conditionalEnergy_integrable ν π E θ j none t).comp_aemeasurable
    (information_measurable π E θ none t).aemeasurable

theorem expectedStepEnergy_eq_integral (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    expectedStepEnergy (T := T) ν π E θ j t.val=
      ∫ p, sampleConditionalEnergy π E θ j t p ∂privateLaw ν S T := by
  have hi : HasLaw (information π E θ none t) (informationLaw ν π E θ none t) (privateLaw ν S T) :=
    ⟨(information_measurable π E θ none t).aemeasurable,rfl⟩
  simp only [expectedStepEnergy,dite_eq_left t.isLt]
  exact (hi.integral_comp (conditionalEnergy_measurable E θ j t).aestronglyMeasurable).symm

theorem sum_expectedStepEnergy_eq_integral (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    (∑ s∈Finset.range T, expectedStepEnergy (T := T) ν π E θ j s)=
      ∫ p, ∑ t : Fin T, sampleConditionalEnergy π E θ j t p ∂privateLaw ν S T := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [expectedStepEnergy_eq_integral ν π E θ j]
  exact (integral_finsetSum _ (fun t _ ↦ sampleConditionalEnergy_integrable ν π E θ j t)).symm

theorem augmented_kl_eq_energy (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    klDiv (augmentedTranscriptLaw (T := T) ν π E θ none) (augmentedTranscriptLaw (T := T) ν π E θ j)=
      ENNReal.ofReal (∫ p, ∑ t : Fin T, sampleConditionalEnergy π E θ j t p ∂privateLaw ν S T) := by
  have h := transcript_kl_sum (T := T) ν π E θ j T le_rfl
  rw [sum_expectedStepEnergy_eq_integral] at h
  exact h

theorem augmented_kl_ne_top (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    klDiv (augmentedTranscriptLaw (T := T) ν π E θ none) (augmentedTranscriptLaw (T := T) ν π E θ j)≠⊤ := by
  rw [augmented_kl_eq_energy]
  exact ENNReal.ofReal_ne_top

theorem augmented_kl_toReal (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    (klDiv (augmentedTranscriptLaw (T := T) ν π E θ none) (augmentedTranscriptLaw (T := T) ν π E θ j)).toReal=
      ∫ p, ∑ t : Fin T, sampleConditionalEnergy π E θ j t p ∂privateLaw ν S T := by
  rw [augmented_kl_eq_energy,ENNReal.toReal_ofReal]
  exact integral_nonneg (fun p ↦ Finset.sum_nonneg (fun t _ ↦ conditionalEnergy_nonneg E θ j t _))

theorem augmented_kl_sum_toReal (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) :
    (∑ j : S, (klDiv (augmentedTranscriptLaw (T := T) ν π E θ none)
      (augmentedTranscriptLaw (T := T) ν π E θ (some j))).toReal)=
      ∫ p, ∑ t : Fin T, ∑ j : S, sampleConditionalEnergy π E θ (some j) t p ∂privateLaw ν S T := by
  simp_rw [augmented_kl_toReal]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p ↦ Finset.sum_comm)
  · intro j _
    exact integrable_finsetSum _ (fun t _ ↦ sampleConditionalEnergy_integrable ν π E θ (some j) t)

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem sampleConditionalEnergy_eq_shift (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    sampleConditionalEnergy π E θ j t p=
      shiftEnergy (timeShift E θ j (observedActionPath π E θ none p) (observedSignPath p) (t.val+1)-
        timeShift E θ j (observedActionPath π E θ none p) (observedSignPath p) (Dyadic.parent (t.val+1)))/
          (2*(Parameters.sigma T)^2) := by
  unfold sampleConditionalEnergy conditionalEnergy
  rw [currentShift_on_actual_history,parentShift_on_actual_history]

end
end Tournament.Lower

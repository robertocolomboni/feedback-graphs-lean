module

public import Tournament.Lower.AugmentedGaussianTransition
public import Tournament.Lower.CurrentSigns
public import Tournament.Model.SensorTranscript
public import Tournament.Probability.KLEmbedding

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory InformationTheory Model.MeasurableGame
open scoped Classical NNReal ENNReal

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

def signLaw : Measure ℝ := FairSigns.coinLaw.map FairSigns.value

instance signLaw_probability : IsProbabilityMeasure signLaw := by
  unfold signLaw
  infer_instance

def transcriptLaw (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) (n : ℕ) : Measure (Seed × SensorHistory ι (AugmentedSignal S) n) :=
  (privateLaw ν S T).map (pastState π E θ j n)

instance transcriptLaw_probability (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (n : ℕ) :
    IsProbabilityMeasure (transcriptLaw (T := T) ν π E θ j n) := by
  unfold transcriptLaw
  infer_instance

def informationLaw (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) (t : Fin T) : Measure (Information Seed S t.val) :=
  (privateLaw ν S T).map (information π E θ j t)

instance informationLaw_probability (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    IsProbabilityMeasure (informationLaw ν π E θ j t) := by
  unfold informationLaw
  infer_instance

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem private_current_sign_law (ν : Measure Seed) [IsProbabilityMeasure ν] (t : Fin T) :
    HasLaw (fun p : Seed × WalkSign.Space T (Coordinate S) ↦ WalkSign.sign t p.2) signLaw (privateLaw ν S T) := by
  have hW : HasLaw (WalkSign.sign (C := Coordinate S) t) signLaw (environmentLaw S T) :=
    (FairSigns.sign_law T t).comp
      (measurePreserving_fst (μ := FairSigns.law T) (ν := GaussianProduct.law (C := Coordinate S) T (incrementVariance T))).hasLaw
  exact hW.comp (measurePreserving_snd (μ := ν) (ν := environmentLaw S T)).hasLaw

theorem informationLaw_eq (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    informationLaw ν π E θ j t=
      ((transcriptLaw (T := T) ν π E θ j t.val).prod signLaw).map
        (adjoinChosenAction π (augmentedDecoder E S) t.val) := by
  have hState : HasLaw (pastState (T := T) π E θ j t.val) (transcriptLaw (T := T) ν π E θ j t.val)
      (privateLaw ν S T) := ⟨(pastState_measurable π E θ j t.val).aemeasurable,rfl⟩
  have hpair := (pastState_current_sign_independent ν π E θ j t).hasLaw_prod hState (private_current_sign_law ν t)
  have hAction : HasLaw (adjoinChosenAction π (augmentedDecoder E S) t.val)
      (((transcriptLaw (T := T) ν π E θ j t.val).prod signLaw).map
        (adjoinChosenAction π (augmentedDecoder E S) t.val))
      ((transcriptLaw (T := T) ν π E θ j t.val).prod signLaw) :=
    ⟨(adjoinChosenAction_measurable π _ (augmentedDecoder_measurable E S) t.val).aemeasurable,rfl⟩
  exact (hAction.comp hpair).map_eq

theorem transcriptLaw_succ (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    transcriptLaw (T := T) ν π E θ j (t.val+1)=
      ((informationLaw ν π E θ j t) ⊗ₘ transitionKernel E θ j t).map (historyExtensionEquiv t.val) := by
  have hCond := transitionObservation_conditional ν π E θ j t
  have heq : (fun p : Seed × WalkSign.Space T (Coordinate S) ↦
      historyExtensionEquiv t.val (information π E θ j t p,transitionObservation π E θ j t p))=
      pastState π E θ j (t.val+1) := by
    funext p
    simp only [historyExtensionEquiv,information,transitionObservation,pastState,augmentedHistory,
      runSensor,sensorAction,augmentedSignal,dite_eq_left t.isLt]
    rfl
  have hExt : HasLaw (historyExtensionEquiv (ι := ι) (Seed := Seed) (B := ℝ) (Z := Coordinate S → ℝ) t.val)
      (((informationLaw ν π E θ j t) ⊗ₘ transitionKernel E θ j t).map (historyExtensionEquiv t.val))
      ((informationLaw ν π E θ j t) ⊗ₘ transitionKernel E θ j t) :=
    ⟨(historyExtensionEquiv t.val).measurable.aemeasurable,rfl⟩
  have h := (hExt.comp hCond).map_eq
  change (privateLaw ν S T).map (fun p ↦
    historyExtensionEquiv t.val (information π E θ j t p,transitionObservation π E θ j t p))=_ at h
  rw [heq] at h
  exact h

theorem informationLaw_ac (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (hac : transcriptLaw (T := T) ν π E θ none t.val ≪ transcriptLaw (T := T) ν π E θ j t.val) :
    informationLaw ν π E θ none t ≪ informationLaw ν π E θ j t := by
  rw [informationLaw_eq,informationLaw_eq]
  exact (hac.prod Measure.AbsolutelyContinuous.rfl).map
    (adjoinChosenAction_measurable π _ (augmentedDecoder_measurable E S) t.val)

theorem informationLaw_kl (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (hac : transcriptLaw (T := T) ν π E θ none t.val ≪ transcriptLaw (T := T) ν π E θ j t.val) :
    klDiv (informationLaw ν π E θ none t) (informationLaw ν π E θ j t)=
      klDiv (transcriptLaw (T := T) ν π E θ none t.val) (transcriptLaw (T := T) ν π E θ j t.val) := by
  rw [informationLaw_eq,informationLaw_eq,
    Tournament.Probability.klDiv_map_embedding_of_ac _ _
      (adjoinChosenAction_embedding π _ (augmentedDecoder_measurable E S) t.val)
      (hac.prod Measure.AbsolutelyContinuous.rfl),
    Tournament.Probability.klDiv_prod_common_right]

theorem transcriptLaw_absolutelyContinuous (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (n : ℕ) (hn : n≤T) :
    transcriptLaw (T := T) ν π E θ none n ≪ transcriptLaw (T := T) ν π E θ j n := by
  induction n with
  | zero => exact Measure.AbsolutelyContinuous.rfl
  | succ n ih =>
    let t : Fin T := ⟨n,by omega⟩
    have ha := informationLaw_ac ν π E θ j t (ih (by omega))
    rw [transcriptLaw_succ ν π E θ none t,transcriptLaw_succ ν π E θ j t]
    have hjoint : (informationLaw ν π E θ none t) ⊗ₘ transitionKernel E θ none t ≪
        (informationLaw ν π E θ j t) ⊗ₘ transitionKernel E θ j t := by
      let : IsProbabilityMeasure (informationLaw ν π E θ j t) := informationLaw_probability ν π E θ j t
      let : IsMarkovKernel (transitionKernel (Seed := Seed) E θ j t) := transitionKernel_markov E θ j t
      apply ha.compProd
      exact Filter.Eventually.of_forall (fun h ↦ GaussianKL.productLaw_absolutelyContinuous _ _ _
        (incrementVariance_ne_zero T (by omega)))
    exact hjoint.map (historyExtensionEquiv n).measurable

end
end Tournament.Lower

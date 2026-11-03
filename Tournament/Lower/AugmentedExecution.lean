module

public import Tournament.Model.MeasurableSensor
public import Tournament.Lower.LowerRegret
public import Tournament.Lower.VisitCounts

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

abbrev AugmentedSignal (S : Finset ι) := ℝ × (Coordinate S → ℝ)

def augmentedDecoder (E : ι → ι → Prop) (S : Finset ι) (_t : ℕ) (p : ι × AugmentedSignal S) : ι → ℝ :=
  feedbackDecoder E S p.1 p.2.1 p.2.2

theorem augmentedDecoder_measurable (E : ι → ι → Prop) (S : Finset ι) (t : ℕ) :
    Measurable (augmentedDecoder E S t) :=
  measurable_from_prod_countable_right (fun a ↦ (feedbackDecoder_continuous E S a).measurable)

theorem shift_joint_measurable (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    Measurable (fun p : ι × ℝ ↦ shift E θ j p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro a
  apply Measurable.of_eval
  intro c
  unfold shift
  dsimp only
  split_ifs <;> fun_prop

def augmentedSignal (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (s : ℕ)
    (p : WalkSign.Space T (Coordinate S) × ι) : AugmentedSignal S :=
  if hs : s<T then
    let sign := WalkSign.sign ⟨s,hs⟩ p.1
    (sign,augmented E θ j p.2 sign (fun c ↦ WalkSign.walk c (s+1) p.1))
  else (1,0)

theorem augmentedSignal_measurable (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (s : ℕ) :
    Measurable (augmentedSignal (T := T) E θ j s) := by
  unfold augmentedSignal
  by_cases hs : s<T
  · simp only [dite_eq_left hs]
    have hsign : Measurable (fun p : WalkSign.Space T (Coordinate S) × ι ↦ WalkSign.sign ⟨s,hs⟩ p.1) :=
      (WalkSign.sign_measurable T ⟨s,hs⟩).comp measurable_fst
    have hx : Measurable (fun p : WalkSign.Space T (Coordinate S) × ι ↦ fun c ↦ WalkSign.walk c (s+1) p.1) := by
      apply Measurable.of_eval
      intro c
      exact (WalkSign.walk_measurable T c (s+1)).comp measurable_fst
    have hshift := (shift_joint_measurable E θ j).comp (measurable_snd.prodMk hsign)
    exact hsign.prodMk (hx.add hshift)
  · simp only [dite_eq_right hs]
    exact measurable_const

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem augmentedSignal_decodes (E : ι → ι → Prop) (hS : SparseMembers E S)
    (θ : ℝ) (j : Coordinate S) (s : ℕ) (hs : s<T) (ω : WalkSign.Space T (Coordinate S)) (a : ι) :
    augmentedDecoder E S s (a,augmentedSignal E θ j s (ω,a))=graphRecord E a (sampledLoss θ j s ω) := by
  funext v
  simp only [augmentedDecoder,augmentedSignal,dite_eq_left hs,sampledLoss,graphRecord]
  exact feedback_reconstruction hS θ j a _ (WalkSign.sign_square ⟨s,hs⟩ ω) _ v

def augmentedHistory (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : ℕ) : Seed × WalkSign.Space T (Coordinate S) → SensorHistory ι (AugmentedSignal S) t :=
  runSensor π (augmentedDecoder E S) (augmentedSignal E θ j) t

theorem augmentedHistory_measurable (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) (t : ℕ) : Measurable (augmentedHistory (T := T) π E θ j t) :=
  runSensor_measurable π _ (augmentedDecoder_measurable E S) _ (augmentedSignal_measurable E θ j) t

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem augmented_history_decodes (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S)
    (θ : ℝ) (j : Coordinate S) (t : ℕ) (ht : t≤T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    decodeHistory (augmentedDecoder E S) t (augmentedHistory π E θ j t p)=
      runHistory π E (sampledLoss θ j) t p :=
  decoded_runSensor π E _ _ _ t
    (fun s hs ω a ↦ augmentedSignal_decodes E hS θ j s (by omega) ω a) p

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem augmented_action_eq_original (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S)
    (θ : ℝ) (j : Coordinate S) (t : ℕ) (ht : t≤T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    sensorAction π (augmentedDecoder E S) (augmentedSignal E θ j) t p=learnerAction π E θ j t p :=
  sensorAction_eq_action π E _ _ _ t
    (fun s hs ω a ↦ augmentedSignal_decodes E hS θ j s (by omega) ω a) p

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem augmentedHistory_actions (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S)
    (θ : ℝ) (j : Coordinate S) (q : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    (augmentedHistory π E θ j T p q).1=learnerAction π E θ j q.val p := by
  have h := runSensor_entry π (augmentedDecoder E S) (augmentedSignal E θ j) T q p
  exact (congrArg Prod.fst h).trans (augmented_action_eq_original π E hS θ j q.val q.isLt.le p)

def augmentedTranscript (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (p : Seed × WalkSign.Space T (Coordinate S)) : Seed × SensorHistory ι (AugmentedSignal S) T :=
  (p.1,augmentedHistory π E θ j T p)

theorem augmentedTranscript_measurable (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) : Measurable (augmentedTranscript (T := T) π E θ j) :=
  measurable_fst.prodMk (augmentedHistory_measurable π E θ j T)

def augmentedTranscriptLaw (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) : Measure (Seed × SensorHistory ι (AugmentedSignal S) T) :=
  (privateLaw ν S T).map (augmentedTranscript π E θ j)

instance augmentedTranscriptLaw_probability (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    IsProbabilityMeasure (augmentedTranscriptLaw (T := T) ν π E θ j) := by
  unfold augmentedTranscriptLaw
  infer_instance

theorem augmented_action_law (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (hS : SparseMembers E S) (θ : ℝ) (j : Coordinate S) :
    (augmentedTranscriptLaw (T := T) ν π E θ j).map (fun p ↦ fun q : Fin T ↦ (p.2 q).1)=
      (privateLaw ν S T).map (fun p ↦ fun q : Fin T ↦ learnerAction π E θ j q.val p) := by
  unfold augmentedTranscriptLaw
  rw [Measure.map_map (by fun_prop) (augmentedTranscript_measurable π E θ j)]
  apply Measure.map_congr
  apply Filter.Eventually.of_forall
  intro p
  funext q
  exact augmentedHistory_actions π E hS θ j q p

end
end Tournament.Lower

module

public import Tournament.Lower.InnovationPast

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

abbrev Information (Seed : Type*) (S : Finset ι) (n : ℕ) :=
  Seed × (SensorHistory ι (AugmentedSignal S) n × (ι × ℝ))

def information (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) : Information Seed S t.val :=
  (p.1,(augmentedHistory π E θ j t.val p,
    (sensorAction π (augmentedDecoder E S) (augmentedSignal E θ j) t.val p,WalkSign.sign t p.2)))

theorem information_measurable (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) : Measurable (information π E θ j t) := by
  have hh := augmentedHistory_measurable (T := T) π E θ j t.val
  have ha := sensorAction_measurable π (augmentedDecoder E S) (augmentedDecoder_measurable E S)
    (augmentedSignal (T := T) E θ j) (augmentedSignal_measurable (T := T) E θ j) t.val
  have hs : Measurable (fun p : Seed × WalkSign.Space T (Coordinate S) ↦ WalkSign.sign t p.2) :=
    (WalkSign.sign_measurable T t).comp measurable_snd
  exact measurable_fst.prodMk (hh.prodMk (ha.prodMk hs))

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem information_erase (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (seed : Seed) (ω : WalkSign.Space T (Coordinate S)) :
    information π E θ j t (seed,eraseInnovation t ω)=information π E θ j t (seed,ω) := by
  unfold information
  rw [augmentedHistory_erase π E θ j t t.val le_rfl seed ω,augmentedAction_erase π E θ j t seed ω]
  rfl

def informationFactor (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (r : Seed × (FairSigns.Space T × (GaussianProduct.otherIndices (C := Coordinate S) t → ℝ))) :
    Information Seed S t.val :=
  information π E θ j t (r.1,(r.2.1,GaussianProduct.restoreOther t r.2.2))

theorem informationFactor_measurable (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) : Measurable (informationFactor π E θ j t) := by
  have hrestore : Measurable (fun r : Seed × (FairSigns.Space T ×
      (GaussianProduct.otherIndices (C := Coordinate S) t → ℝ)) ↦
      (r.1,(r.2.1,GaussianProduct.restoreOther t r.2.2))) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((GaussianProduct.restoreOther_measurable t).comp (measurable_snd.comp measurable_snd)))
  exact (information_measurable π E θ j t).comp hrestore

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem informationFactor_snapshot (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    informationFactor π E θ j t (p.1,(p.2.1,GaussianProduct.otherSnapshot t p.2.2))=information π E θ j t p := by
  unfold informationFactor
  rw [GaussianProduct.restoreOther_snapshot]
  exact information_erase π E θ j t p.1 p.2

theorem information_innovation_independent (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    IndepFun (information π E θ j t) (fun p : Seed × WalkSign.Space T (Coordinate S) ↦
      GaussianProduct.currentSnapshot t p.2.2) (privateLaw ν S T) := by
  have hi := GaussianProduct.current_independent_private (C := Coordinate S) ν T (incrementVariance T) t
  have h := hi.comp (φ := informationFactor π E θ j t) (ψ := id)
    (informationFactor_measurable π E θ j t) measurable_id
  have heq : (fun p : Seed × WalkSign.Space T (Coordinate S) ↦
      informationFactor π E θ j t (p.1,(p.2.1,GaussianProduct.otherSnapshot t p.2.2)))=
      information π E θ j t := by
    funext p
    exact informationFactor_snapshot π E θ j t p
  change IndepFun (fun p : Seed × WalkSign.Space T (Coordinate S) ↦
    informationFactor π E θ j t (p.1,(p.2.1,GaussianProduct.otherSnapshot t p.2.2)))
      (fun p ↦ GaussianProduct.currentSnapshot t p.2.2) (privateLaw ν S T) at h
  rw [heq] at h
  exact h

end
end Tournament.Lower

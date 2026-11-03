module

public import Tournament.Lower.AugmentedInformation
public import Tournament.Lower.GaussianShiftKL

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal

noncomputable section

variable {ι Seed : Type*} {S : Finset ι} {T : ℕ}

def parentHistoryIndex (t : Fin T) (hpa : Dyadic.parent (t.val+1)≠0) : Fin t.val :=
  ⟨Dyadic.parent (t.val+1)-1,by
    have h := Dyadic.parent_lt (t.val+1) (by omega)
    omega⟩

def parentObservation (t : Fin T) (h : Information Seed S t.val) : Coordinate S → ℝ :=
  if hpa : Dyadic.parent (t.val+1)=0 then 0 else (h.2.1 (parentHistoryIndex t hpa)).2.2

def parentShift (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (h : Information Seed S t.val) : Coordinate S → ℝ :=
  if hpa : Dyadic.parent (t.val+1)=0 then 0 else
    let prev := h.2.1 (parentHistoryIndex t hpa)
    shift E θ j prev.1 prev.2.1

def currentShift (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    {n : ℕ} (h : Information Seed S n) : Coordinate S → ℝ := shift E θ j h.2.2.1 h.2.2.2

def transitionMean (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (h : Information Seed S t.val) : Coordinate S → ℝ :=
  parentObservation t h+currentShift E θ j h-parentShift E θ j t h

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [MeasurableSpace Seed]

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem parentObservation_measurable (t : Fin T) : Measurable (parentObservation (Seed := Seed) (S := S) t) := by
  unfold parentObservation
  by_cases hpa : Dyadic.parent (t.val+1)=0
  · simp only [dite_eq_left hpa]
    exact measurable_const
  · simp only [dite_eq_right hpa]
    have heval : Measurable (fun h : Information Seed S t.val ↦ h.2.1 (parentHistoryIndex t hpa)) :=
      (measurable_pi_apply (parentHistoryIndex t hpa)).comp (measurable_fst.comp measurable_snd)
    exact heval.snd.snd

theorem parentShift_measurable (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    Measurable (parentShift (Seed := Seed) E θ j t) := by
  unfold parentShift
  by_cases hpa : Dyadic.parent (t.val+1)=0
  · simp only [dite_eq_left hpa]
    exact measurable_const
  · simp only [dite_eq_right hpa]
    have heval : Measurable (fun h : Information Seed S t.val ↦ h.2.1 (parentHistoryIndex t hpa)) :=
      (measurable_pi_apply (parentHistoryIndex t hpa)).comp (measurable_fst.comp measurable_snd)
    exact (shift_joint_measurable E θ j).comp (heval.fst.prodMk heval.snd.fst)

theorem currentShift_measurable (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (n : ℕ) :
    Measurable (currentShift (Seed := Seed) (n := n) E θ j) :=
  (shift_joint_measurable E θ j).comp (measurable_snd.comp measurable_snd)

theorem transitionMean_measurable (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    Measurable (transitionMean (Seed := Seed) E θ j t) :=
  ((parentObservation_measurable t).add (currentShift_measurable E θ j t.val)).sub (parentShift_measurable E θ j t)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [MeasurableSpace Seed] in
theorem reference_transitionMean (E : ι → ι → Prop) (θ : ℝ) (t : Fin T)
    (h : Information Seed S t.val) : transitionMean E θ none t h=parentObservation t h := by
  have hp : parentShift E θ (none : Coordinate S) t h=0 := by
    unfold parentShift
    split_ifs
    · rfl
    · exact shift_reference E θ _ _
  rw [transitionMean,hp,currentShift,shift_reference,add_zero,sub_zero]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [MeasurableSpace Seed] in
theorem sample_walk_parent (t : Fin T) (c : Coordinate S) (ω : WalkSign.Space T (Coordinate S)) :
    WalkSign.walk c (t.val+1) ω=WalkSign.walk c (Dyadic.parent (t.val+1)) ω+
      GaussianProduct.currentSnapshot t ω.2 c := by
  have h := congrFun (GaussianProduct.walk_parent (T := T) c (t.val+1) (by omega) (by omega)) ω.2
  simpa only [WalkSign.walk,Pi.add_apply,GaussianProduct.increment,GaussianProduct.currentSnapshot,
    Nat.add_sub_cancel] using h

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem parentObservation_identity (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    parentObservation t (information π E θ j t p)=
      (fun c ↦ WalkSign.walk c (Dyadic.parent (t.val+1)) p.2)+parentShift E θ j t (information π E θ j t p) := by
  by_cases hpa : Dyadic.parent (t.val+1)=0
  · simp only [parentObservation,parentShift,dite_eq_left hpa,add_zero]
    funext c
    rw [hpa]
    exact (congrFun (GaussianProduct.walk_zero (T := T) c) p.2.2).symm
  · let q := parentHistoryIndex t hpa
    have hq : q.val+1=Dyadic.parent (t.val+1) := by
      dsimp only [q,parentHistoryIndex]
      omega
    have hqT : q.val<T := q.isLt.trans t.isLt
    have he : augmentedHistory π E θ j t.val p q=
        (sensorAction π (augmentedDecoder E S) (augmentedSignal E θ j) q.val p,
          augmentedSignal E θ j q.val (p.2,sensorAction π (augmentedDecoder E S) (augmentedSignal E θ j) q.val p)) :=
      runSensor_entry π _ _ t.val q p
    simp only [parentObservation,parentShift,dite_eq_right hpa,information]
    rw [he]
    simp only [augmentedSignal,dite_eq_left hqT,augmented]
    rw [hq]

def transitionObservation (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) : Coordinate S → ℝ :=
  (augmentedSignal E θ j t.val (p.2,sensorAction π (augmentedDecoder E S) (augmentedSignal E θ j) t.val p)).2

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem transitionObservation_identity (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    transitionObservation π E θ j t p=transitionMean E θ j t (information π E θ j t p)+
      GaussianProduct.currentSnapshot t p.2.2 := by
  have hobs : transitionObservation π E θ j t p=
      (fun c ↦ WalkSign.walk c (t.val+1) p.2)+currentShift E θ j (information π E θ j t p) := by
    simp only [transitionObservation,augmentedSignal,dite_eq_left t.isLt,augmented,currentShift,information]
  rw [hobs,transitionMean,parentObservation_identity]
  funext c
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [sample_walk_parent]
  ring

end
end Tournament.Lower

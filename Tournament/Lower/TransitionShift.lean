module

public import Tournament.Lower.AugmentedGaussianMean
public import Tournament.Lower.ShiftCongestion

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {ι Seed : Type*} {S : Finset ι} {T : ℕ}

theorem shift_coordinate_abs_le (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (a : ι)
    (sign : ℝ) (hsign : |sign|=1) (c : Coordinate S) : |shift E θ j a sign c|≤|θ| := by
  unfold shift
  split_ifs <;> simp [abs_mul,hsign,abs_nonneg]

def observedSignPath (p : Seed × WalkSign.Space T (Coordinate S)) (s : ℕ) : ℝ :=
  if hs : s<T then WalkSign.sign ⟨s,hs⟩ p.2 else 1

theorem observedSignPath_abs (p : Seed × WalkSign.Space T (Coordinate S)) (s : ℕ) :
    |observedSignPath p s|=1 := by
  unfold observedSignPath
  split_ifs
  · exact FairSigns.value_abs _
  · norm_num

theorem observedSignPath_square (p : Seed × WalkSign.Space T (Coordinate S)) (s : ℕ) :
    (observedSignPath p s)^2=1 := by
  unfold observedSignPath
  split_ifs
  · exact WalkSign.sign_square _ _
  · norm_num

variable [MeasurableSpace ι] [MeasurableSpace Seed]

def observedActionPath (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (k : Coordinate S)
    (p : Seed × WalkSign.Space T (Coordinate S)) (s : ℕ) : ι :=
  sensorAction π (augmentedDecoder E S) (augmentedSignal E θ k) s p

theorem currentShift_on_actual_history (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j k : Coordinate S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    currentShift E θ j (information π E θ k t p)=
      timeShift E θ j (observedActionPath π E θ k p) (observedSignPath p) (t.val+1) := by
  simp only [currentShift,information,timeShift,ite_eq_right (by omega : t.val+1≠0),
    Nat.add_sub_cancel,observedSignPath,dite_eq_left t.isLt,observedActionPath]

theorem parentShift_on_actual_history (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j k : Coordinate S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    parentShift E θ j t (information π E θ k t p)=
      timeShift E θ j (observedActionPath π E θ k p) (observedSignPath p) (Dyadic.parent (t.val+1)) := by
  by_cases hpa : Dyadic.parent (t.val+1)=0
  · simp only [parentShift,dite_eq_left hpa,timeShift,ite_eq_left hpa]
  · let q := parentHistoryIndex t hpa
    have hqT : q.val<T := q.isLt.trans t.isLt
    have he : augmentedHistory π E θ k t.val p q=
        (sensorAction π (augmentedDecoder E S) (augmentedSignal E θ k) q.val p,
          augmentedSignal E θ k q.val (p.2,sensorAction π (augmentedDecoder E S) (augmentedSignal E θ k) q.val p)) :=
      runSensor_entry π _ _ t.val q p
    simp only [parentShift,dite_eq_right hpa,information]
    rw [he]
    simp only [augmentedSignal,dite_eq_left hqT,timeShift,ite_eq_right hpa,observedActionPath,observedSignPath]
    change shift E θ j _ (WalkSign.sign ⟨q.val,hqT⟩ p.2)=
      shift E θ j _ (if hs : Dyadic.parent (t.val+1)-1<T then WalkSign.sign ⟨Dyadic.parent (t.val+1)-1,hs⟩ p.2 else 1)
    have hpT : Dyadic.parent (t.val+1)-1<T := hqT
    simp only [dite_eq_left hpT]
    rfl

theorem shift_on_actual_history_abs (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j k : Coordinate S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) (c : Coordinate S) :
    |currentShift E θ j (information π E θ k t p) c|≤|θ| ∧
      |parentShift E θ j t (information π E θ k t p) c|≤|θ| := by
  constructor
  · exact shift_coordinate_abs_le E θ j _ _ (FairSigns.value_abs _) c
  · rw [parentShift_on_actual_history]
    unfold timeShift
    split_ifs
    · simpa only [Pi.zero_apply,abs_zero] using abs_nonneg θ
    · exact shift_coordinate_abs_le E θ j _ _ (observedSignPath_abs p _) c

omit [MeasurableSpace ι] [MeasurableSpace Seed] in
theorem transitionMean_difference (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (h : Information Seed S t.val) (c : Coordinate S) :
    transitionMean E θ none t h c-transitionMean E θ j t h c=
      -(currentShift E θ j h c-parentShift E θ j t h c) := by
  rw [reference_transitionMean,transitionMean]
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem transitionMean_difference_abs (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j k : Coordinate S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) (c : Coordinate S) :
    |transitionMean E θ none t (information π E θ k t p) c-
      transitionMean E θ j t (information π E θ k t p) c|≤2*|θ| := by
  rw [transitionMean_difference,abs_neg]
  have h := shift_on_actual_history_abs π E θ j k t p c
  exact (abs_sub _ _).trans (by linarith)

variable [DiscreteMeasurableSpace ι] [Fintype ι]

theorem transitionMean_difference_memLp (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j k : Coordinate S) (t : Fin T) (c : Coordinate S) :
    MemLp (fun h ↦ transitionMean E θ none t h c-transitionMean E θ j t h c) 2
      ((privateLaw ν S T).map (information π E θ k t)) := by
  have hm : Measurable (fun h : Information Seed S t.val ↦
      transitionMean E θ none t h c-transitionMean E θ j t h c) :=
    ((measurable_pi_apply c).comp (transitionMean_measurable E θ none t)).sub
      ((measurable_pi_apply c).comp (transitionMean_measurable E θ j t))
  apply (memLp_map_measure_iff hm.aestronglyMeasurable (information_measurable π E θ k t).aemeasurable).mpr
  apply MemLp.of_bound ((hm.comp (information_measurable π E θ k t)).aestronglyMeasurable) (2*|θ|)
  exact Filter.Eventually.of_forall (fun p ↦ by
    simpa only [Function.comp_apply,Real.norm_eq_abs] using transitionMean_difference_abs π E θ j k t p c)

end
end Tournament.Lower

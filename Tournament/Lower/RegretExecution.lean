module

public import Tournament.Lower.SignCancellation
public import Tournament.Lower.RegretPointwise
public import Tournament.Model.MeasurableRegret

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal BigOperators

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace Seed]
variable {S : Finset ι} {T : ℕ}

def memberIndicator (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (v : S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ :=
  if learnerAction π E θ j t.val p=v.val then 1 else 0

def outsideIndicator (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ :=
  if learnerAction π E θ j t.val p∈S then 0 else 1

def roundNoise (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (v : S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ :=
  memberNoise (learnerAction π E θ j t.val p) (WalkSign.sign t p.2)
    (fun c ↦ WalkSign.walk c (t.val+1) p.2) v

def roundError (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ := ∑ v : S, clippingError θ j t v p.2

def visits (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (v : S) (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ := ∑ t : Fin T, memberIndicator π E θ j v t p

def outsideVisits (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ := ∑ t : Fin T, outsideIndicator π E θ j t p

def noiseTotal (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (v : S) (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ := ∑ t : Fin T, roundNoise π E θ j v t p

def errorTotal (θ : ℝ) (j : Coordinate S) (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ :=
  ∑ t : Fin T, roundError θ j t p

def switchTotal (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ := (Model.switchCount T (fun t ↦ learnerAction π E θ j t p):ℝ)

theorem memberIndicator_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (v : S) (t : Fin T) :
    Integrable (memberIndicator π E θ j v t) (privateLaw ν S T) := by
  have hmeas : Measurable (memberIndicator π E θ j v t) :=
    Measurable.ite ((measurableSet_singleton v.val).preimage (learnerAction_measurable π E θ j t.val))
      measurable_const measurable_const
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro p
  unfold memberIndicator
  split_ifs <;> norm_num

theorem outsideIndicator_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    Integrable (outsideIndicator π E θ j t) (privateLaw ν S T) := by
  have hmeas : Measurable (outsideIndicator π E θ j t) :=
    Measurable.ite ((MeasurableSet.of_discrete (s := (S : Set ι))).preimage
      (learnerAction_measurable π E θ j t.val)) measurable_const measurable_const
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro p
  unfold outsideIndicator
  split_ifs <;> norm_num

omit [DiscreteMeasurableSpace ι] in
theorem roundNoise_eq_sum (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (v : S) (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    roundNoise π E θ j v t p=∑ u : S, selectedWalkDifference π E θ j t u v p := rfl

theorem roundNoise_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (v : S) (t : Fin T) :
    Integrable (roundNoise π E θ j v t) (privateLaw ν S T) := by
  change Integrable (fun p ↦ ∑ u : S, selectedWalkDifference π E θ j t u v p) _
  exact integrable_finsetSum _ (fun u _ ↦ selectedWalkDifference_integrable ν π E θ j t u v)

theorem roundNoise_mean_zero (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (v : S) (t : Fin T) :
    ∫ p, roundNoise π E θ j v t p ∂privateLaw ν S T=0 := by
  simp only [roundNoise_eq_sum]
  rw [integral_finsetSum _ (fun u _ ↦ selectedWalkDifference_integrable ν π E θ j t u v)]
  simp only [selectedWalkDifference_mean_zero ν π E θ j t,Finset.sum_const_zero]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem roundError_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (θ : ℝ) (j : Coordinate S) (t : Fin T) : Integrable (roundError θ j t) (privateLaw ν S T) := by
  apply integrable_finsetSum
  intro v _
  exact (measurePreserving_snd (μ := ν) (ν := environmentLaw S T)).integrable_comp_of_integrable
    (clippingError_integrable θ j t v)

theorem visits_integrable (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (v : S) :
    Integrable (visits (T := T) π E θ j v) (privateLaw ν S T) :=
  integrable_finsetSum _ (fun t _ ↦ memberIndicator_integrable ν π E θ j v t)

theorem outsideVisits_integrable (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    Integrable (outsideVisits (T := T) π E θ j) (privateLaw ν S T) :=
  integrable_finsetSum _ (fun t _ ↦ outsideIndicator_integrable ν π E θ j t)

theorem noiseTotal_integrable (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (v : S) :
    Integrable (noiseTotal (T := T) π E θ j v) (privateLaw ν S T) :=
  integrable_finsetSum _ (fun t _ ↦ roundNoise_integrable ν π E θ j v t)

theorem noiseTotal_mean_zero (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (v : S) :
    ∫ p, noiseTotal (T := T) π E θ j v p ∂privateLaw ν S T=0 := by
  rw [show noiseTotal (T := T) π E θ j v=(fun p ↦ ∑ t : Fin T, roundNoise π E θ j v t p) by rfl,
    integral_finsetSum _ (fun t _ ↦ roundNoise_integrable ν π E θ j v t)]
  simp only [roundNoise_mean_zero ν π E θ j v,Finset.sum_const_zero]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem errorTotal_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (θ : ℝ) (j : Coordinate S) : Integrable (errorTotal (T := T) θ j) (privateLaw ν S T) :=
  integrable_finsetSum _ (fun t _ ↦ roundError_integrable ν θ j t)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem errorTotal_expectation_le (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 2≤T)
    (hST : S.card≤T) (θ : ℝ) (hθ : 0≤θ ∧ θ≤1/64) (j : Coordinate S) :
    (∫ p, errorTotal θ j p ∂privateLaw ν S T)≤1/1024 := by
  have hi : Integrable (fun ω ↦ ∑ t : Fin T, ∑ v : S, clippingError θ j t v ω) (environmentLaw S T) :=
    integrable_finsetSum _ (fun t _ ↦ integrable_finsetSum _ (fun v _ ↦ clippingError_integrable θ j t v))
  calc
    _ = ∫ ω, ∑ t : Fin T, ∑ v : S, clippingError θ j t v ω ∂environmentLaw S T :=
      (measurePreserving_snd (μ := ν) (ν := environmentLaw S T)).hasLaw.integral_comp hi.aestronglyMeasurable
    _ ≤ _ := clipping_error_sum hT hST θ hθ j

omit [DiscreteMeasurableSpace ι] in
theorem outsideVisits_nonneg (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (p : Seed × WalkSign.Space T (Coordinate S)) : 0≤outsideVisits π E θ j p := by
  apply Finset.sum_nonneg
  intro t _
  unfold outsideIndicator
  split_ifs <;> norm_num

omit [DiscreteMeasurableSpace ι] in
theorem switchTotal_nonneg (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (p : Seed × WalkSign.Space T (Coordinate S)) : 0≤switchTotal π E θ j p := by
  unfold switchTotal
  positivity

theorem switchTotal_integrable [Fintype ι] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    Integrable (switchTotal (T := T) π E θ j) (privateLaw ν S T) := by
  have hmeas : Measurable (switchTotal (T := T) π E θ j) :=
    (Measurable.of_discrete (f := fun n : ℕ ↦ (n:ℝ))).comp
      (switchCount_measurable T (learnerAction π E θ j) (learnerAction_measurable π E θ j))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (T:ℝ)
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (switchTotal_nonneg π E θ j p)]
  unfold switchTotal
  exact_mod_cast (Model.switchCount_le T (fun t ↦ learnerAction π E θ j t p)).trans (Nat.sub_le T 1)

variable [Fintype ι] [Nonempty ι]

def learnerRegretPath (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ :=
  Model.pathRegret T (fun t ↦ sampledLoss θ j t p.2) (fun t ↦ learnerAction π E θ j t p)

def expectedRegret (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) : ℝ := ∫ p, learnerRegretPath (T := T) π E θ j p ∂privateLaw ν S T

theorem learnerRegretPath_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    Integrable (learnerRegretPath (T := T) π E θ j) (privateLaw ν S T) := by
  apply pathRegret_integrable (privateLaw ν S T) T (fun t p ↦ sampledLoss θ j t p.2)
    (fun t a ↦ ((sampledLoss_measurable θ j t).eval (a := a)).comp measurable_snd)
    (fun t p a ↦ sampledLoss_bounds θ j t p.2 a)
    (learnerAction π E θ j) (learnerAction_measurable π E θ j)

end
end Tournament.Lower

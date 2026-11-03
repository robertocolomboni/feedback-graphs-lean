module

public import Tournament.Lower.CausalEnvironment

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace Seed]
variable {S : Finset ι} {T : ℕ}

def privateLaw (ν : Measure Seed) (S : Finset ι) (T : ℕ) :
    Measure (Seed × WalkSign.Space T (Coordinate S)) := ν.prod (environmentLaw S T)

instance privateLaw_probability (ν : Measure Seed) [IsProbabilityMeasure ν] (S : Finset ι) (T : ℕ) :
    IsProbabilityMeasure (privateLaw ν S T) := by
  unfold privateLaw
  infer_instance

def flipPrivate (t : Fin T) (p : Seed × WalkSign.Space T (Coordinate S)) :
    Seed × WalkSign.Space T (Coordinate S) := (p.1,flipSample t p.2)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem flipPrivate_preserving (ν : Measure Seed) [IsProbabilityMeasure ν] (t : Fin T) :
    MeasurePreserving (flipPrivate (S := S) t) (privateLaw ν S T) (privateLaw ν S T) :=
  (MeasurePreserving.id ν).prod (flipSample_preserving t)

def selectedWalkDifference (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (u v : S) (p : Seed × WalkSign.Space T (Coordinate S)) : ℝ :=
  if learnerAction π E θ j t.val p=u.val then
    WalkSign.sign t p.2*(WalkSign.walk (some u) (t.val+1) p.2-WalkSign.walk (some v) (t.val+1) p.2)
  else 0

theorem selectedWalkDifference_measurable (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (u v : S) : Measurable (selectedWalkDifference π E θ j t u v) := by
  have ha := learnerAction_measurable (T := T) π E θ j t.val
  have hs : Measurable (fun p : Seed × WalkSign.Space T (Coordinate S) ↦ WalkSign.sign t p.2) :=
    (WalkSign.sign_measurable (C := Coordinate S) T t).comp measurable_snd
  have hu : Measurable (fun p : Seed × WalkSign.Space T (Coordinate S) ↦ WalkSign.walk (some u) (t.val+1) p.2) :=
    (WalkSign.walk_measurable T (some u) (t.val+1)).comp measurable_snd
  have hv : Measurable (fun p : Seed × WalkSign.Space T (Coordinate S) ↦ WalkSign.walk (some v) (t.val+1) p.2) :=
    (WalkSign.walk_measurable T (some v) (t.val+1)).comp measurable_snd
  exact Measurable.ite ((measurableSet_singleton u.val).preimage ha) (hs.mul (hu.sub hv)) measurable_const

omit [DiscreteMeasurableSpace ι] in
theorem selectedWalkDifference_flip (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (t : Fin T) (u v : S) (p : Seed × WalkSign.Space T (Coordinate S)) :
    selectedWalkDifference π E θ j t u v (flipPrivate t p)= -selectedWalkDifference π E θ j t u v p := by
  have ha := learnerAction_flip π E θ j t p.1 p.2
  have hs := flipSample_sign t p.2
  simp only [selectedWalkDifference,flipPrivate,ha,hs]
  split_ifs <;> simp only [WalkSign.walk,flipSample,neg_mul,neg_zero]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem private_walk_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (c : Coordinate S) (t : ℕ) :
    Integrable (fun p : Seed × WalkSign.Space T (Coordinate S) ↦ WalkSign.walk c t p.2) (privateLaw ν S T) := by
  have h := (WalkSign.walk_law T (incrementVariance T) c t).comp
    (measurePreserving_snd (μ := ν) (ν := environmentLaw S T)).hasLaw
  exact (Dyadic.gaussian_increment_memLp h).integrable (by norm_num)

theorem selectedWalkDifference_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (u v : S) : Integrable (selectedWalkDifference π E θ j t u v) (privateLaw ν S T) := by
  have hi := (private_walk_integrable (S := S) (T := T) ν (some u) (t.val+1)).sub
    (private_walk_integrable (S := S) (T := T) ν (some v) (t.val+1))
  apply hi.mono (selectedWalkDifference_measurable π E θ j t u v).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  have hs : |WalkSign.sign t p.2|=1 := FairSigns.value_abs _
  by_cases ha : learnerAction π E θ j t.val p=u.val
  · simp only [selectedWalkDifference,ite_eq_left ha,Real.norm_eq_abs,abs_mul,hs,one_mul,Pi.sub_apply,le_refl]
  · simp only [selectedWalkDifference,ite_eq_right ha,norm_zero]
    exact norm_nonneg _

theorem selectedWalkDifference_mean_zero (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S)
    (t : Fin T) (u v : S) : ∫ p, selectedWalkDifference π E θ j t u v p ∂privateLaw ν S T=0 := by
  have hf := selectedWalkDifference_measurable π E θ j t u v
  have hsame :
      (∫ p, selectedWalkDifference π E θ j t u v (flipPrivate t p) ∂privateLaw ν S T)=
        ∫ p, selectedWalkDifference π E θ j t u v p ∂privateLaw ν S T :=
    (flipPrivate_preserving ν t).hasLaw.integral_comp hf.aestronglyMeasurable
  have hneg :
      (∫ p, selectedWalkDifference π E θ j t u v (flipPrivate t p) ∂privateLaw ν S T)=
        -(∫ p, selectedWalkDifference π E θ j t u v p ∂privateLaw ν S T) := by
    calc
      _ = ∫ p, -selectedWalkDifference π E θ j t u v p ∂privateLaw ν S T := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (selectedWalkDifference_flip π E θ j t u v)
      _ = _ := integral_neg _
  linarith

end
end Tournament.Lower

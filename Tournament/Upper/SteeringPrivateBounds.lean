module

public import Tournament.Upper.SteeringPrivateSeed
public import Tournament.Upper.TunedExecution

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open MeasureTheory Model MeasurableGame BlockParameters Tuning
open scoped Classical

noncomputable section

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

omit [Nonempty ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem schedule_total (S : SteeringParameters ι) :
    prefixHorizon (fun b ↦ S.schedule b+1) S.blockCount = S.T :=
  UniformSchedule.total S.T (horizon S.m) (by unfold horizon; positivity)

omit [Nonempty ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem schedule_horizon_pos (S : SteeringParameters ι) :
    0 < prefixHorizon (fun b ↦ S.schedule b+1) S.blockCount := by
  rw [schedule_total]
  have := S.time_ge_two
  omega

def seedStrategy (S : SteeringParameters ι) (default : ι) : Strategy.{u,0} ι :=
  if hr : S.rounded = true then
    S.roundedPrivateStrategy hr S.schedule S.blockCount S.schedule_horizon_pos default
  else
    S.idealPrivateStrategy (by cases h : S.rounded <;> simp_all)
      S.schedule S.blockCount S.schedule_horizon_pos default

theorem seedStrategy_regret_eq_mean [LinearOrder ι]
    (S : SteeringParameters ι) (E : ι → ι → Prop) (hTournament : S.tournament = selectedEdge E)
    (default : ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (S.seedStrategy default).regret S.T E loss =
      ((S.algorithm S.schedule loss hLoss).execution S.blockCount).mean
        (fun x ↦ pathRegret S.T loss (S.actions S.schedule default S.blockCount x)) := by
  by_cases hr : S.rounded = true
  · simp only [seedStrategy, dite_eq_left hr]
    have h := S.roundedPrivateStrategy_regret_eq_mean hr E hTournament
      S.schedule S.blockCount S.schedule_horizon_pos default loss hLoss
    rw [schedule_total] at h
    exact h
  · simp only [seedStrategy, dite_eq_right hr]
    have hi : S.rounded = false := by cases h : S.rounded <;> simp_all
    have h := S.idealPrivateStrategy_regret_eq_mean hi E hTournament
      S.schedule S.blockCount S.schedule_horizon_pos default loss hLoss
    rw [schedule_total] at h
    exact h

theorem seedStrategy_expectedSwitches_eq_mean [LinearOrder ι]
    (S : SteeringParameters ι) (E : ι → ι → Prop) (hTournament : S.tournament = selectedEdge E)
    (default : ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (S.seedStrategy default).expectedSwitches S.T E loss =
      ((S.algorithm S.schedule loss hLoss).execution S.blockCount).mean
        (fun x ↦ (switchCount S.T (S.actions S.schedule default S.blockCount x) : ℝ)) := by
  by_cases hr : S.rounded = true
  · simp only [seedStrategy, dite_eq_left hr]
    have h := S.roundedPrivateStrategy_expectedSwitches_eq_mean hr E hTournament
      S.schedule S.blockCount S.schedule_horizon_pos default loss hLoss
    rw [schedule_total] at h
    exact h
  · simp only [seedStrategy, dite_eq_right hr]
    have hi : S.rounded = false := by cases h : S.rounded <;> simp_all
    have h := S.idealPrivateStrategy_expectedSwitches_eq_mean hi E hTournament
      S.schedule S.blockCount S.schedule_horizon_pos default loss hLoss
    rw [schedule_total] at h
    exact h

theorem seedStrategy_fixed_rate [LinearOrder ι]
    (S : SteeringParameters ι) (E : ι → ι → Prop) (hTournament : S.tournament = selectedEdge E)
    (default : ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t))
    (hκ : 1/(S.T:ℝ) ≤ DyadicRate.base S.m) :
    (S.seedStrategy default).regret S.T E loss ≤
      (2:ℝ)^25*threshold (Fintype.card ι) S.T*(S.m:ℝ)*logScale (Fintype.card ι) S.T*
        Real.log (Fintype.card ι:ℝ)/DyadicRate.base S.m+14*meanRate S.m*(S.T:ℝ)+3 ∧
    (S.seedStrategy default).expectedSwitches S.T E loss ≤ 10*meanRate S.m*(S.T:ℝ)+1 := by
  rw [seedStrategy_regret_eq_mean S E hTournament default loss hLoss,
    seedStrategy_expectedSwitches_eq_mean S E hTournament default loss hLoss]
  have h := S.fixed_rate_execution loss hLoss default hκ
  simpa only [ProbabilityVector.integral_toMeasure,
    pathRegret_decidableEq (Classical.decEq ι) (inferInstance : DecidableEq ι),
    switchCount_decidableEq (Classical.decEq ι) (inferInstance : DecidableEq ι)] using h

theorem seedStrategy_tuned [LinearOrder ι]
    (S : SteeringParameters ι) (E : ι → ι → Prop) (hTournament : S.tournament = selectedEdge E)
    (hm : S.m = exponent (target (Fintype.card ι) S.T))
    (hr : target (Fintype.card ι) S.T ≤ 1/32)
    (default : ι) (loss : ℕ → ι → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (S.seedStrategy default).regret S.T E loss ≤
        (2:ℝ)^40*min (S.T:ℝ) (performanceScale (Fintype.card ι) S.T) ∧
      (S.seedStrategy default).expectedSwitches S.T E loss ≤
        (2:ℝ)^40*min (S.T:ℝ) (performanceScale (Fintype.card ι) S.T) := by
  rw [seedStrategy_regret_eq_mean S E hTournament default loss hLoss,
    seedStrategy_expectedSwitches_eq_mean S E hTournament default loss hLoss]
  have h := S.tuned_small_target hm hr loss hLoss default
  dsimp only at h
  rw [S.feedback_algorithm_eq S.schedule loss hLoss] at h
  simpa only [ProbabilityVector.integral_toMeasure,
    pathRegret_decidableEq (Classical.decEq ι) (inferInstance : DecidableEq ι),
    switchCount_decidableEq (Classical.decEq ι) (inferInstance : DecidableEq ι)] using h

end
end Tournament.Upper.SteeringParameters

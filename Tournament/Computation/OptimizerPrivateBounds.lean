module

public import Tournament.Computation.OptimizerFeedback
public import Tournament.Upper.SteeringArbitraryOrientation

@[expose] public section

namespace Tournament.Computation.OptimizerPrivateBounds

open MeasureTheory Upper Model MeasurableGame BlockParameters Tuning
open OptimizerCodeMeasurable OptimizerFeedback
open scoped Classical
noncomputable section

variable {K : ℕ} [Nonempty (Fin K)]
local instance finClassicalDecidableEq : DecidableEq (Fin K) :=
  fun a b ↦ Classical.propDecidable (a=b)

def privateStrategy (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) (default : Fin K) : Strategy.{0,0} (Fin K) :=
  (feedbackPolicy S solve hc).privateStrategy S.tournament S.schedule S.blockCount
    (liftedCompressedLaw_atom_measurable S solve hc S.schedule S.blockCount)
    S.schedule_horizon_pos default

theorem regret_eq_mean (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) (E : Fin K → Fin K → Prop)
    (hObs : OrientationObserved E S.tournament) (default : Fin K)
    (loss : ℕ → Fin K → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (privateStrategy S solve hc default).regret S.T E loss =
      (((parameters S solve hc).algorithm S.schedule loss hLoss).execution S.blockCount).mean
        (fun x ↦ pathRegret S.T loss ((parameters S solve hc).actions S.schedule default S.blockCount x)) := by
  have h := (feedbackPolicy S solve hc).privateStrategy_regret_eq_mean_of_observed
    (metadataIndependent S solve hc) S.tournament E hObs S.schedule S.blockCount
    (liftedCompressedLaw_atom_measurable S solve hc S.schedule S.blockCount)
    S.schedule_horizon_pos default loss
  rw [algorithm_eq S solve hc S.schedule loss hLoss, S.schedule_total] at h
  exact h

theorem expectedSwitches_eq_mean (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) (E : Fin K → Fin K → Prop)
    (hObs : OrientationObserved E S.tournament) (default : Fin K)
    (loss : ℕ → Fin K → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (privateStrategy S solve hc default).expectedSwitches S.T E loss =
      (((parameters S solve hc).algorithm S.schedule loss hLoss).execution S.blockCount).mean
        (fun x ↦ (switchCount S.T ((parameters S solve hc).actions S.schedule default S.blockCount x):ℝ)) := by
  have h := (feedbackPolicy S solve hc).privateStrategy_expectedSwitches_eq_mean_of_observed
    (metadataIndependent S solve hc) S.tournament E hObs S.schedule S.blockCount
    (liftedCompressedLaw_atom_measurable S solve hc S.schedule S.blockCount)
    S.schedule_horizon_pos default loss
  rw [algorithm_eq S solve hc S.schedule loss hLoss, S.schedule_total] at h
  exact h

theorem fixed_rate (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) (E : Fin K → Fin K → Prop)
    (hObs : OrientationObserved E S.tournament) (default : Fin K)
    (loss : ℕ → Fin K → ℝ) (hLoss : ∀ t, BoundedLoss (loss t))
    (hκ : 1/(S.T:ℝ)≤DyadicRate.base S.m) :
    (privateStrategy S solve hc default).regret S.T E loss ≤
      (2:ℝ)^25*threshold (Fintype.card (Fin K)) S.T*(S.m:ℝ)*logScale (Fintype.card (Fin K)) S.T*
        Real.log (Fintype.card (Fin K):ℝ)/DyadicRate.base S.m+14*meanRate S.m*(S.T:ℝ)+3 ∧
    (privateStrategy S solve hc default).expectedSwitches S.T E loss ≤
      10*meanRate S.m*(S.T:ℝ)+1 := by
  rw [regret_eq_mean S solve hc E hObs default loss hLoss,
    expectedSwitches_eq_mean S solve hc E hObs default loss hLoss]
  have h := (parameters S solve hc).fixed_rate_execution loss hLoss default hκ
  dsimp only at h
  rw [ProbabilityVector.integral_toMeasure, ProbabilityVector.integral_toMeasure] at h
  convert h using 1 <;> congr!

theorem tuned (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (hc : CorrectOnRounded S solve) (E : Fin K → Fin K → Prop)
    (hObs : OrientationObserved E S.tournament)
    (hm : S.m=exponent (target (Fintype.card (Fin K)) S.T))
    (hr : target (Fintype.card (Fin K)) S.T≤1/32) (default : Fin K)
    (loss : ℕ → Fin K → ℝ) (hLoss : ∀ t, BoundedLoss (loss t)) :
    (privateStrategy S solve hc default).regret S.T E loss ≤
        (2:ℝ)^40*min (S.T:ℝ) (performanceScale (Fintype.card (Fin K)) S.T) ∧
    (privateStrategy S solve hc default).expectedSwitches S.T E loss ≤
        (2:ℝ)^40*min (S.T:ℝ) (performanceScale (Fintype.card (Fin K)) S.T) := by
  rw [regret_eq_mean S solve hc E hObs default loss hLoss,
    expectedSwitches_eq_mean S solve hc E hObs default loss hLoss]
  have h := (parameters S solve hc).tuned_small_target hm hr loss hLoss default
  dsimp only at h
  rw [ProbabilityVector.integral_toMeasure, ProbabilityVector.integral_toMeasure] at h
  convert h using 1 <;> congr!

end
end Tournament.Computation.OptimizerPrivateBounds

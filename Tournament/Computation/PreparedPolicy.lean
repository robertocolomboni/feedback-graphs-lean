module

public import Tournament.Computation.FinitePreparation
public import Tournament.Computation.OptimizerFeedback

@[expose] public section

namespace Tournament.Computation.PreparedPolicy

open Upper Model BlockParameters
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000

variable {K : ℕ} [Nonempty (Fin K)]

local instance finClassicalDecidableEq : DecidableEq (Fin K) :=
  fun a b => Classical.propDecidable (a=b)

def output (S : SteeringParameters (Fin K)) (π : ProbabilityVector (Fin K)) :=
  FinitePreparation.prepare S.tournament S.T (S.anchor π) (DyadicRate.base S.m)

def holding (S : SteeringParameters (Fin K)) (π : ProbabilityVector (Fin K)) : HoldingFamily (Fin K) := by
  let P := OptimizerCodeMeasurable.parameters S (AssignmentExactSolver.candidate K)
    (AssignmentExactSolver.correctOnRounded S)
  let out := output S π
  have hs : out.sampling=(P.holding π).sampling :=
    (FinitePreparation.prepare_parameters S π).2.1
  have hx : out.refresh=(P.holding π).refresh :=
    (FinitePreparation.prepare_parameters S π).2.2.1
  exact {
    sampling := {
      weight := out.sampling
      nonneg := by rw [hs]; exact (P.holding π).sampling.nonneg
      sum_eq_one := by rw [hs]; exact (P.holding π).sampling.sum_eq_one }
    refresh := {
      weight := out.refresh
      nonneg := by rw [hx]; exact (P.holding π).refresh.nonneg
      sum_eq_one := by rw [hx]; exact (P.holding π).refresh.sum_eq_one }
    sampling_pos := by
      change ∀ i, 0<out.sampling i
      rw [hs]
      exact (P.holding π).sampling_pos
    refresh_pos := by
      change ∀ i, 0<out.refresh i
      rw [hx]
      exact (P.holding π).refresh_pos
    refresh_ge_half := by
      change ∀ i, out.sampling i/2≤out.refresh i
      rw [hs,hx]
      exact (P.holding π).refresh_ge_half }

omit [Nonempty (Fin K)] in
theorem holding_ext {H J : HoldingFamily (Fin K)}
    (hs : H.sampling=J.sampling) (hx : H.refresh=J.refresh) : H=J := by
  cases H
  cases J
  cases hs
  cases hx
  rfl

theorem holding_eq (S : SteeringParameters (Fin K)) (π : ProbabilityVector (Fin K)) :
    holding S π=(OptimizerCodeMeasurable.parameters S (AssignmentExactSolver.candidate K)
      (AssignmentExactSolver.correctOnRounded S)).holding π := by
  apply holding_ext
  · apply ProbabilityVector.ext_weights
    intro i
    exact congrFun (FinitePreparation.prepare_parameters S π).2.1 i
  · apply ProbabilityVector.ext_weights
    intro i
    exact congrFun (FinitePreparation.prepare_parameters S π).2.2.1 i

def familyRules (S : SteeringParameters (Fin K)) (H : HoldingFamily (Fin K)) :
    DyadicScoreRules H S.tournament S.m := fun j =>
  tournamentScoreRule S.tournament S.isTournament _ _ H.sampling_pos
    (H.kernel_reversible (DyadicRate.rate_pos S.m j))
    (H.kernel_holding_ge_half (DyadicRate.rate_pos S.m j))

def rules (S : SteeringParameters (Fin K)) (π : ProbabilityVector (Fin K)) :
    DyadicScoreRules (holding S π) S.tournament S.m := familyRules S (holding S π)

def decoder (S : SteeringParameters (Fin K)) (π : ProbabilityVector (Fin K))
    (s : Fin K) (obs : Fin K → ℝ) (i : Fin K) : ℝ :=
  let out := output S π
  let z : Fin K → ℝ := fun k =>
    ∑ r, (if k=r then 0 else -out.assignment.1 s k r)*(obs r-obs k)
  (z i-∑ k, S.anchor π k*z k)/out.sampling s

theorem decoder_eq (S : SteeringParameters (Fin K)) (π : ProbabilityVector (Fin K)) :
    decoder S π=OptimizerCodeMeasurable.decoder S (AssignmentExactSolver.candidate K)
      (AssignmentExactSolver.correctOnRounded S) π := by
  funext s obs i
  dsimp only [decoder,output]
  rw [(FinitePreparation.prepare_parameters S π).1,
    (FinitePreparation.prepare_parameters S π).2.1]
  rfl

def feedbackPolicy (S : SteeringParameters (Fin K)) : FeedbackEW (Fin K) S.m where
  rate := learningRate (Fintype.card (Fin K)) S.T S.m
  policy π := dyadicComparisonPolicy (holding S π) S.m (rules S π)
    (threshold (Fintype.card (Fin K)) S.T)
  output π j offset ns log :=
    truncateEstimate (learningRate (Fintype.card (Fin K)) S.T S.m)
      (blockObservedEstimate (rules S π j) (decoder S π)
        (threshold (Fintype.card (Fin K)) S.T) offset ns log)

theorem feedbackPolicy_eq (S : SteeringParameters (Fin K)) :
    feedbackPolicy S=OptimizerFeedback.feedbackPolicy S (AssignmentExactSolver.candidate K)
      (AssignmentExactSolver.correctOnRounded S) := by
  unfold feedbackPolicy OptimizerFeedback.feedbackPolicy
  congr 1
  · funext π
    unfold rules
    rw [holding_eq]
    rfl
  · funext π j offset ns log i
    unfold OptimizerFeedback.output rules
    rw [holding_eq,decoder_eq]
    rfl

end
end Tournament.Computation.PreparedPolicy

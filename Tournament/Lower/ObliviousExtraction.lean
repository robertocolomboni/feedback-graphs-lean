module

public import Tournament.Lower.BayesRegret
public import Tournament.Model.DeterministicExecution
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal BigOperators

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

omit [DiscreteMeasurableSpace ι] in
theorem sampledLoss_deterministic_regret (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (j : Coordinate S) (seed : Seed) (ω : WalkSign.Space T (Coordinate S)) :
    deterministicPathRegret T π E (fun t ↦ sampledLoss θ j t ω) seed=learnerRegretPath π E θ j (seed,ω) := by
  unfold deterministicPathRegret learnerRegretPath
  congr 1
  funext n
  exact action_section π E (sampledLoss θ j) n seed ω

theorem expectedRegret_eq_oblivious_average (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    expectedRegret (T := T) ν π E θ j=
      ∫ ω, deterministicExpectedRegret T ν π E (fun t ↦ sampledLoss θ j t ω) ∂environmentLaw S T := by
  have hi := learnerRegretPath_integrable (T := T) ν π E θ j
  rw [expectedRegret,privateLaw,integral_prod_symm _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω ↦ by
    unfold deterministicExpectedRegret
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun seed ↦ (sampledLoss_deterministic_regret π E θ j seed ω).symm))

theorem exists_oblivious_loss_ge_environment (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    ∃ loss : ℕ → ι → ℝ, (∀ t a, 0≤loss t a ∧ loss t a≤1) ∧
      expectedRegret (T := T) ν π E θ j≤deterministicExpectedRegret T ν π E loss := by
  have hi := learnerRegretPath_integrable (T := T) ν π E θ j
  have hsections : Integrable (fun ω ↦ deterministicExpectedRegret T ν π E (fun t ↦ sampledLoss θ j t ω))
      (environmentLaw S T) := by
    have h := hi.integral_prod_right
    have heq : (fun ω : WalkSign.Space T (Coordinate S) ↦ ∫ seed, learnerRegretPath π E θ j (seed,ω) ∂ν)=
        (fun ω : WalkSign.Space T (Coordinate S) ↦ deterministicExpectedRegret T ν π E (fun t ↦ sampledLoss θ j t ω)) := by
      funext ω
      unfold deterministicExpectedRegret
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun seed ↦ (sampledLoss_deterministic_regret π E θ j seed ω).symm)
    rw [heq] at h
    exact h
  obtain ⟨ω,hω⟩ := exists_integral_le hsections
  refine ⟨(fun t ↦ sampledLoss θ j t ω),(fun t a ↦ sampledLoss_bounds θ j t ω a),?_⟩
  rw [expectedRegret_eq_oblivious_average]
  exact hω

end
end Tournament.Lower

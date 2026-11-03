module

public import Tournament.Computation.OptimizerMainTransfer
public import Tournament.Computation.AssignmentSerialization
public import Tournament.Upper.RoundedFeedbackDecoder

@[expose] public section

namespace Tournament.Computation.OptimizerCodeMeasurable

open MeasureTheory Upper Model BlockParameters
open scoped BigOperators Classical
noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace A]

theorem code_functional_measurable (p : A → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (T : ℕ)
    (f : (ι → ℕ) → ℕ → ℝ) :
    Measurable (fun a ↦ f (Rounding.numerator (p a) T) (Rounding.denominator (p a) T)) := by
  apply Probability.measurable_of_discrete_factor
    (fun a ↦ Rounding.code (p a) T) (Rounding.code_measurable p hp T)
  intro a b h
  change Rounding.numerator (p a) T = Rounding.numerator (p b) T at h
  simp only [Rounding.denominator, h]

section FiniteWire

variable {K : ℕ}

local instance finClassicalDecidableEq : DecidableEq (Fin K) :=
  fun a b ↦ Classical.propDecidable (a=b)

def wireInput (F : Fin K → Fin K → Prop) [DecidableRel F]
    (w : ProbabilityVector (Fin K)) (T : ℕ) : List Bool :=
  AssignmentSerialization.serialize K
    (AssignmentEncoding.encode F (Rounding.numerator w T) (Rounding.denominator w T))

theorem wireInput_functional_measurable (F : Fin K → Fin K → Prop) [DecidableRel F]
    (p : A → ProbabilityVector (Fin K)) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (T : ℕ) (f : List Bool → ℝ) :
    Measurable (fun a ↦ f (wireInput F (p a) T)) :=
  code_functional_measurable p hp T
    (fun n D ↦ f (AssignmentSerialization.serialize K (AssignmentEncoding.encode F n D)))

abbrev Candidate (K : ℕ) := List Bool → AssignmentEncoding.Variable (Fin K) → ℚ

variable [Nonempty (Fin K)]

def program (S : SteeringParameters (Fin K)) (π : ProbabilityVector (Fin K)) :
    AssignmentEncoding.Program (Fin K) :=
  AssignmentEncoding.encode S.tournament
    (Rounding.numerator (S.anchor π) S.T) (Rounding.denominator (S.anchor π) S.T)

def solution (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (π : ProbabilityVector (Fin K)) : AssignmentEncoding.Variable (Fin K) → ℝ :=
  fun k ↦ (solve (wireInput S.tournament (S.anchor π) S.T) k : ℝ)

def data (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (π : ProbabilityVector (Fin K)) : AssignmentData (Fin K) :=
  AssignmentEncoding.unpack (solution S solve π)

structure CorrectOnRounded (S : SteeringParameters (Fin K)) (solve : Candidate K) : Prop where
  feasible : ∀ π, (program S π).Feasible (solution S solve π)
  optimal : ∀ π x, (program S π).Feasible x →
    AssignmentEncoding.evaluate (program S π).objective (solution S solve π) ≤
      AssignmentEncoding.evaluate (program S π).objective x

theorem data_feasible (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (π : ProbabilityVector (Fin K)) :
    data S solve π ∈ feasibleData S.tournament
      (Rounding.anchor (S.anchor π) S.T (by have := S.time_ge_two; omega)) := by
  apply (AssignmentEncoding.rounded_feasible_iff S.tournament (S.anchor π)
    S.card_ge_two S.time_ge_two (S.anchor_floor π) (data S solve π)).mp
  simpa only [data, program, AssignmentEncoding.pack_unpack] using h.feasible π

def assignment (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (π : ProbabilityVector (Fin K)) :
    ComparisonAssignment S.tournament
      (Rounding.anchor (S.anchor π) S.T (by have := S.time_ge_two; omega)) :=
  assignmentOfData S.tournament _
    (Rounding.anchor_pos (S.anchor π) S.card_ge_two S.time_ge_two (S.anchor_floor π))
    (data S solve π) (data_feasible S solve h π)

theorem assignment_optimal (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (π : ProbabilityVector (Fin K))
    (B : ComparisonAssignment S.tournament
      (Rounding.anchor (S.anchor π) S.T (by have := S.time_ge_two; omega))) :
    (assignment S solve h π).totalWeight ≤ B.totalWeight := by
  have hB := (AssignmentEncoding.rounded_feasible_iff S.tournament (S.anchor π)
    S.card_ge_two S.time_ge_two (S.anchor_floor π) (assignmentData B)).mpr (assignmentData_mem B)
  have ho := h.optimal π (AssignmentEncoding.pack (assignmentData B)) hB
  unfold program at ho
  rw [← AssignmentEncoding.pack_unpack (solution S solve π),
    AssignmentEncoding.objective_eq, AssignmentEncoding.objective_eq] at ho
  exact ho

def optimalFamily (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) : OptimizerMainTransfer.OptimalFamily S where
  assignment := assignment S solve h
  optimal := assignment_optimal S solve h

def parameters (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) : OptimizerMainTransfer.Parameters (Fin K) :=
  OptimizerMainTransfer.ofOptimalFamily S (optimalFamily S solve h)

theorem solution_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (p : A → ProbabilityVector (Fin K)) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (k : AssignmentEncoding.Variable (Fin K)) :
    Measurable (fun a ↦ solution S solve (p a) k) :=
  wireInput_functional_measurable S.tournament (fun a ↦ S.anchor (p a))
    (SteeringParameters.anchor_weight_measurable S p hp) S.T (fun bs ↦ (solve bs k : ℝ))

theorem matrix_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (p : A → ProbabilityVector (Fin K))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (s i r : Fin K) :
    Measurable (fun a ↦ (assignment S solve h (p a)).matrix s i r) :=
  solution_measurable S solve p hp (.inl (s,i,r))

theorem sourceWeight_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (p : A → ProbabilityVector (Fin K))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (s : Fin K) :
    Measurable (fun a ↦ (assignment S solve h (p a)).sourceWeight s) :=
  solution_measurable S solve p hp (.inr s)

theorem sourceLaw_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (p : A → ProbabilityVector (Fin K))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (s : Fin K) :
    Measurable (fun a ↦ (assignment S solve h (p a)).sourceLaw s) :=
  (sourceWeight_measurable S solve h p hp s).div
    (Finset.measurable_sum _ (fun i _ ↦ sourceWeight_measurable S solve h p hp i))

theorem holding_sampling_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (p : A → ProbabilityVector (Fin K))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (i : Fin K) :
    Measurable (fun a ↦ ((parameters S solve h).holding (p a)).sampling i) :=
  ComparisonAssignment.preparedSampling_measurable (fun a ↦ assignment S solve h (p a))
    (sourceLaw_measurable S solve h p hp) (fun a ↦ S.anchor (p a))
    (SteeringParameters.anchor_weight_measurable S p hp)
    (DyadicRate.base S.m) (DyadicRate.base_pos S.m) (base_le_one_thirtytwo S.bands_ge_five) i

theorem holding_refresh_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (p : A → ProbabilityVector (Fin K))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (i : Fin K) :
    Measurable (fun a ↦ ((parameters S solve h).holding (p a)).refresh i) :=
  ComparisonAssignment.preparedFamily_refresh_measurable (fun a ↦ assignment S solve h (p a))
    (sourceLaw_measurable S solve h p hp) (fun a ↦ S.anchor (p a))
    (SteeringParameters.anchor_weight_measurable S p hp) (fun a ↦ S.anchor_pos (p a))
    (DyadicRate.base S.m) (DyadicRate.base_pos S.m) (base_le_one_thirtytwo S.bands_ge_five) i

theorem holding_kernel_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (p : A → ProbabilityVector (Fin K))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (τ : ℝ) (hτ : 0<τ) (i j : Fin K) :
    Measurable (fun a ↦ ((parameters S solve h).holding (p a)).kernel τ hτ i j) :=
  HoldingFamily.kernel_entry_measurable _ (holding_sampling_measurable S solve h p hp)
    (holding_refresh_measurable S solve h p hp) τ hτ i j

theorem rules_decoder_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (p : A → ProbabilityVector (Fin K))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) (j : Fin (S.m+1)) :
    ScoreRule.DecoderMeasurable (fun a ↦ (parameters S solve h).rules (p a) j) := by
  exact ScoreRule.tournament_decoder_measurable S.isTournament
    (holding_kernel_measurable S solve h p hp (DyadicRate.rate S.m j) (DyadicRate.rate_pos S.m j))
    (fun a ↦ ((parameters S solve h).holding (p a)).sampling_pos)
    (fun a ↦ ((parameters S solve h).holding (p a)).kernel_reversible (DyadicRate.rate_pos S.m j))
    (fun a ↦ ((parameters S solve h).holding (p a)).kernel_holding_ge_half (DyadicRate.rate_pos S.m j))

def decoder (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (π : ProbabilityVector (Fin K)) :
    Fin K → (Fin K → ℝ) → Fin K → ℝ :=
  (assignment S solve h π).estimatorDecoder (S.anchor π) ((parameters S solve h).holding π).sampling

theorem decoder_correct (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (π : ProbabilityVector (Fin K))
    (loss : Fin K → ℝ) (s i : Fin K) :
    decoder S solve h π s (comparisonObservation S.tournament s loss) i =
      applyEstimator ((parameters S solve h).estimator π) s loss i :=
  ComparisonAssignment.estimatorDecoder_observation _ _ _ _ _ _

theorem decoder_measurable (S : SteeringParameters (Fin K)) (solve : Candidate K)
    (h : CorrectOnRounded S solve) (p : A → ProbabilityVector (Fin K))
    (hp : ∀ i, Measurable (fun a ↦ p a i)) :
    EstimatorDecoderMeasurable (fun a ↦ decoder S solve h (p a)) := by
  intro s hs obs hObs k
  apply Probability.measurable_countable_parameter
    (fun i a ↦ decoder S solve h (p a) i (obs a) k) _ s hs
  intro i
  exact ComparisonAssignment.estimatorDecoder_measurable _ (matrix_measurable S solve h p hp)
    _ _ (SteeringParameters.anchor_weight_measurable S p hp)
    (holding_sampling_measurable S solve h p hp) obs hObs i k

end FiniteWire

end
end Tournament.Computation.OptimizerCodeMeasurable

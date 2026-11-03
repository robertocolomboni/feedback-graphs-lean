module

public import Tournament.Computation.FiniteBlockRunner
public import Tournament.Computation.FinitePreparation
public import Tournament.Computation.OptimizerFeedback
public import Tournament.Computation.PreparedPolicy
public import Tournament.Model.RegretDecidable

@[expose] public section

namespace Tournament.Computation.FiniteAdaptiveRunner

open Model Upper FiniteRequests FiniteChunkRunner

noncomputable section

variable {K m : ℕ} [Nonempty (Fin K)]

abbrev History (K m : ℕ) (n : ℕ → ℕ) (B : ℕ) :=
  FiniteProcess.History (fun b => DyadicBlockOutcome (Fin K) m (n b)) B

def execute (policy : GraphFeedbackEW (Fin K) m) (n : ℕ → ℕ) :
    (B : ℕ) → Program K (History K m n B × ProbabilityVector (Fin K))
  | 0 => .pure (ULift.up (), ExponentialWeights.uniform)
  | B+1 => (execute policy n B).bind fun past =>
      (FiniteBlockRunner.execute (policy.policy past.2)
        (prefixHorizon (fun b => n b+1) B) (n B)).map fun block =>
          ((past.1,block.1), exponentialUpdate past.2 policy.rate
            (policy.output past.2 block.1.1 (prefixHorizon (fun b => n b+1) B)
              (Restarts.parts (n B) block.1.2.1) block.2))

theorem execute_expect (policy : GraphFeedbackEW (Fin K) m) (n : ℕ → ℕ)
    (E : Fin K → Fin K → Prop) (loss : ℕ → Fin K → ℝ) (B : ℕ)
    (f : History K m n B × ProbabilityVector (Fin K) → ℝ) :
    Program.expect (observations E loss) (execute policy n B) f =
      ((policy.algorithm E n loss).execution B).mean
        (fun h => f (h,(policy.algorithm E n loss).distribution B h)) := by
  induction B with
  | zero =>
      simp [execute, Program.expect_pure, AdaptiveEW.execution, FiniteProcess.law,
        FiniteProcess.initial, ProbabilityVector.mean, AdaptiveEW.distribution]
  | succ B ih =>
      simp only [execute, Program.expect_bind, Program.expect_map]
      rw [ih]
      change _ = ((_ : ProbabilityVector (History K m n B)).joint
        ((policy.algorithm E n loss).kernel B)).mean _
      rw [ProbabilityVector.joint_mean]
      congr 1
      funext hist
      rw [FiniteBlockRunner.execute_expect]
      rfl

def optimizerProgram (S : SteeringParameters (Fin K)) (E : Fin K → Fin K → Prop)
    (n : ℕ → ℕ) (B : ℕ) :
    Program K (History K S.m n B × ProbabilityVector (Fin K)) :=
  execute ((PreparedPolicy.feedbackPolicy S).toGraph E) n B

theorem optimizerProgram_expect (S : SteeringParameters (Fin K))
    (E : Fin K → Fin K → Prop) (hE : S.tournament=selectedEdge E)
    (n : ℕ → ℕ) (B : ℕ) (loss : ℕ → Fin K → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t))
    (f : History K S.m n B × ProbabilityVector (Fin K) → ℝ) :
    Program.expect (observations E loss) (optimizerProgram S E n B) f =
      (((OptimizerCodeMeasurable.parameters S (AssignmentExactSolver.candidate K)
        (AssignmentExactSolver.correctOnRounded S)).algorithm n loss hloss).execution B).mean
          (fun h => f (h,((OptimizerCodeMeasurable.parameters S (AssignmentExactSolver.candidate K)
            (AssignmentExactSolver.correctOnRounded S)).algorithm n loss hloss).distribution B h)) := by
  unfold optimizerProgram
  rw [PreparedPolicy.feedbackPolicy_eq, execute_expect, FeedbackEW.toGraph_algorithm, ← hE,
    OptimizerFeedback.algorithm_eq S (AssignmentExactSolver.candidate K)
      (AssignmentExactSolver.correctOnRounded S) n loss hloss]
  rfl

theorem optimizerProgram_bound (S : SteeringParameters (Fin K))
    (E : Fin K → Fin K → Prop) (hE : S.tournament=selectedEdge E)
    (hm : S.m=Tuning.exponent (Tuning.target (Fintype.card (Fin K)) S.T))
    (hr : Tuning.target (Fintype.card (Fin K)) S.T≤1/32)
    (default : Fin K) (loss : ℕ → Fin K → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) :
    let A := OptimizerCodeMeasurable.parameters S (AssignmentExactSolver.candidate K)
      (AssignmentExactSolver.correctOnRounded S)
    let program := optimizerProgram S E S.schedule S.blockCount
    Program.expect (observations E loss) program
        (fun out => pathRegret S.T loss (A.actions S.schedule default S.blockCount out.1)) ≤
      (2:ℝ)^40*min (S.T:ℝ) (Tuning.performanceScale (Fintype.card (Fin K)) S.T) ∧
    Program.expect (observations E loss) program
        (fun out => (switchCount S.T (A.actions S.schedule default S.blockCount out.1):ℝ)) ≤
      (2:ℝ)^40*min (S.T:ℝ) (Tuning.performanceScale (Fintype.card (Fin K)) S.T) := by
  dsimp only
  rw [optimizerProgram_expect S E hE S.schedule S.blockCount loss hloss,
    optimizerProgram_expect S E hE S.schedule S.blockCount loss hloss]
  have h := (OptimizerCodeMeasurable.parameters S (AssignmentExactSolver.candidate K)
    (AssignmentExactSolver.correctOnRounded S)).tuned_small_target hm hr loss hloss default
  dsimp only at h
  rw [ProbabilityVector.integral_toMeasure, ProbabilityVector.integral_toMeasure] at h
  simp only [pathRegret_decidableEq (Classical.decEq (Fin K))
    (inferInstance : DecidableEq (Fin K)), switchCount_decidableEq (Classical.decEq (Fin K))
    (inferInstance : DecidableEq (Fin K))] at h
  convert h using 1 <;> congr!

end
end Tournament.Computation.FiniteAdaptiveRunner

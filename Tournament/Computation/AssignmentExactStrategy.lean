module

public import Tournament.Computation.AssignmentExactSolver
public import Tournament.Computation.OptimizerMinimax

@[expose] public section

namespace Tournament.Computation.AssignmentExactStrategy

open MeasureTheory Upper Model MeasurableGame Tuning

noncomputable section

variable {K : ℕ} [Nonempty (Fin K)]

theorem correctForGraph (E : Fin K→Fin K→Prop) (hE : StronglyRevealing E) (T : ℕ) :
    OptimizerMinimax.CorrectForGraph (AssignmentExactSolver.candidate K) E hE T := by
  intro hK hT hr
  exact AssignmentExactSolver.correctOnRounded (graphTunedParameters E hE T hK hT hr true)

def strategy (E : Fin K→Fin K→Prop) (hE : StronglyRevealing E) (T : ℕ)
    (default : Fin K) : Strategy.{0,0} (Fin K) :=
  OptimizerMinimax.strategy E hE T default (AssignmentExactSolver.candidate K) (correctForGraph E hE T)

theorem strategy_bound (E : Fin K→Fin K→Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1≤T) (default : Fin K) (loss : ℕ→Fin K→ℝ)
    (hLoss : ∀t,BoundedLoss (loss t)) :
    (strategy E hE T default).regret T E loss≤
        (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card (Fin K)) T) ∧
    (strategy E hE T default).expectedSwitches T E loss≤
        (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card (Fin K)) T) :=
  OptimizerMinimax.strategy_bound E hE T hT default (AssignmentExactSolver.candidate K)
    (correctForGraph E hE T) loss hLoss

theorem minimax_upper (E : Fin K→Fin K→Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1≤T) :
    minimax.{0,0} T E≤(2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card (Fin K)) T) :=
  OptimizerMinimax.minimax_upper E hE T hT (AssignmentExactSolver.candidate K) (correctForGraph E hE T)

end
end Tournament.Computation.AssignmentExactStrategy

module

public import Tournament.Computation.FiniteAdaptiveRunner
public import Tournament.Upper.GraphTunedExecution
public import Tournament.Upper.TrivialRegimes
public import Tournament.Correspondence.FiniteLoss

@[expose] public section

namespace Tournament.Computation.FiniteTournamentProgram

open Model Upper Tuning FiniteRequests FiniteChunkRunner FiniteAdaptiveRunner
open scoped Classical

noncomputable section

variable {K : ℕ} [Nonempty (Fin K)]

def constantProgram (default : Fin K) : (T : ℕ) → Program K (ℕ → Fin K)
  | 0 => .pure (fun _ => default)
  | T+1 => (constantProgram default T).bind fun _ =>
      (Program.observation T default).map fun _ => fun _ => default

omit [Nonempty (Fin K)] in
theorem constantProgram_expect (default : Fin K) (T : ℕ)
    (obs : ℕ → Fin K → Fin K → ℝ) (f : (ℕ → Fin K) → ℝ) :
    Program.expect obs (constantProgram default T) f = f (fun _ => default) := by
  induction T generalizing f with
  | zero => rfl
  | succ T ih =>
      simp only [constantProgram, Program.expect_bind, Program.expect_map, Program.expect_observation]
      exact ih _

def tournamentProgram (E : Fin K → Fin K → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (default : Fin K) : Program K (ℕ → Fin K) :=
  if hK : Fintype.card (Fin K)=1 then constantProgram default T
  else if hT : 2≤T then
    if hr : target (Fintype.card (Fin K)) T≤1/32 then
      let hK2 : 2≤Fintype.card (Fin K) := by have := Fintype.card_pos (α := Fin K); omega
      let S := graphTunedParameters E hE T hK2 hT hr true
      let A := OptimizerCodeMeasurable.parameters S (AssignmentExactSolver.candidate K)
        (AssignmentExactSolver.correctOnRounded S)
      (optimizerProgram S E S.schedule S.blockCount).map
        (fun out => A.actions S.schedule default S.blockCount out.1)
    else constantProgram default T
  else constantProgram default T

theorem tournamentProgram_bound (E : Fin K → Fin K → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1≤T) (default : Fin K) (loss : ℕ → Fin K → ℝ)
    (hLoss : ∀ t, BoundedLoss (loss t)) :
    Program.expect (observations E loss) (tournamentProgram E hE T default)
        (pathRegret T loss) ≤
      (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card (Fin K)) T) ∧
    Program.expect (observations E loss) (tournamentProgram E hE T default)
        (fun actions => (switchCount T actions:ℝ)) ≤
      (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card (Fin K)) T) := by
  unfold tournamentProgram
  split
  · rename_i hK
    rw [constantProgram_expect, constantProgram_expect]
    have h := fixed_action_card_one E T hK default loss
    simpa only [GraphStrategy.regret_constant, GraphStrategy.switches_constant,
      switchCount_constant, Nat.cast_zero,
      pathRegret_decidableEq (Classical.decEq (Fin K)) (inferInstance : DecidableEq (Fin K))] using h
  · rename_i hK
    have hK2 : 2≤Fintype.card (Fin K) := by have := Fintype.card_pos (α := Fin K); omega
    split
    · rename_i hT2
      split
      · rename_i hr
        simp only [Program.expect_map]
        exact optimizerProgram_bound (graphTunedParameters E hE T hK2 hT2 hr true)
          E rfl rfl hr default loss hLoss
      · rename_i hr
        rw [constantProgram_expect, constantProgram_expect]
        have h := fixed_action_large_target E T hK2 hT2 (lt_of_not_ge hr) default loss hLoss
        simpa only [GraphStrategy.regret_constant, GraphStrategy.switches_constant,
          switchCount_constant, Nat.cast_zero,
          pathRegret_decidableEq (Classical.decEq (Fin K)) (inferInstance : DecidableEq (Fin K))] using h
    · rename_i hT2
      have hTeq : T=1 := by omega
      subst T
      rw [constantProgram_expect, constantProgram_expect]
      have h := fixed_action_time_one E hK2 default loss hLoss
      simpa only [Nat.cast_one, GraphStrategy.regret_constant, GraphStrategy.switches_constant,
        switchCount_constant, Nat.cast_zero,
        pathRegret_decidableEq (Classical.decEq (Fin K)) (inferInstance : DecidableEq (Fin K))] using h

theorem tournamentProgram_bound_finite (E : Fin K → Fin K → Prop) (hE : StronglyRevealing E)
    (T : ℕ) (hT : 1≤T) (default : Fin K) (loss : Fin T → Fin K → ℝ)
    (hLoss : ∀ t, BoundedLoss (loss t)) :
    Program.expect (observations E (Correspondence.finiteLossExtension loss))
        (tournamentProgram E hE T default) (pathRegret T (Correspondence.finiteLossExtension loss)) ≤
      (2:ℝ)^40*min (T:ℝ) (performanceScale K T) ∧
    Program.expect (observations E (Correspondence.finiteLossExtension loss))
        (tournamentProgram E hE T default) (fun actions => (switchCount T actions:ℝ)) ≤
      (2:ℝ)^40*min (T:ℝ) (performanceScale K T) := by
  simpa only [Fintype.card_fin] using tournamentProgram_bound E hE T hT default
    (Correspondence.finiteLossExtension loss) (Correspondence.finiteLossExtension_bounded loss hLoss)

end
end Tournament.Computation.FiniteTournamentProgram

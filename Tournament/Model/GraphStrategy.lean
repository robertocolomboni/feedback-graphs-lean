module

public import Tournament.Model.GraphFeedbackEW
public import Tournament.Model.ScheduledExecution

@[expose] public section

namespace Tournament.Model

open scoped BigOperators Classical MeasureTheory
open MeasureTheory FiniteProcess Upper

noncomputable section

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

inductive GraphStrategy (ι : Type u) [Fintype ι] where
  | constant (i : ι)
  | blocks (default : ι) (m : ℕ) (n : ℕ → ℕ) (B : ℕ) (policy : GraphFeedbackEW ι m)

namespace GraphStrategy

def Outcome : GraphStrategy ι → Type u
  | .constant _ => ULift.{u} Unit
  | .blocks _ m n B _ => History (fun b ↦ DyadicBlockOutcome ι m (n b)) B

instance outcomeFintype (S : GraphStrategy ι) : Fintype S.Outcome := by
  cases S with
  | constant _ => exact inferInstanceAs (Fintype (ULift.{u} Unit))
  | blocks _ m n B _ => exact inferInstanceAs (Fintype (History (fun b ↦ DyadicBlockOutcome ι m (n b)) B))

def law : (S : GraphStrategy ι) → (ι → ι → Prop) → (ℕ → ι → ℝ) → ProbabilityVector S.Outcome
  | .constant _, _, _ => ProbabilityVector.pure (ULift.up ())
  | .blocks _ _ n B P, E, loss => (P.algorithm E n loss).execution B

def actions : (S : GraphStrategy ι) → S.Outcome → ℕ → ι
  | .constant i, _ => fun _ ↦ i
  | .blocks default _ n B _, x => ScheduledExecution.trajectory default (fun b ↦ n b+1)
      (fun _ y ↦ blockActions default (Restarts.parts _ y.2.1) y.2.2) B x

def regret (S : GraphStrategy ι) (E : ι → ι → Prop) (T : ℕ) (loss : ℕ → ι → ℝ) : ℝ :=
  (S.law E loss).mean (fun x ↦ pathRegret T loss (S.actions x))

def switches (S : GraphStrategy ι) (E : ι → ι → Prop) (T : ℕ) (loss : ℕ → ι → ℝ) : ℝ :=
  (S.law E loss).mean (fun x ↦ (switchCount T (S.actions x):ℝ))

theorem regret_eq_expected_cost_sub_best (S : GraphStrategy ι) (E : ι → ι → Prop)
    (T : ℕ) (loss : ℕ → ι → ℝ) :
    S.regret E T loss=(S.law E loss).mean (fun x ↦ accumulatedLoss T loss (S.actions x)+
      (switchCount T (S.actions x):ℝ))-bestFixedLoss T loss := by
  unfold regret pathRegret
  rw [ProbabilityVector.mean_sub,ProbabilityVector.mean_const]

theorem regret_constant (i : ι) (E : ι → ι → Prop) (T : ℕ) (loss : ℕ → ι → ℝ) :
    (constant i).regret E T loss=pathRegret T loss (fun _ ↦ i) := by
  unfold regret actions
  exact ProbabilityVector.mean_const ((constant i).law E loss) (pathRegret T loss (fun _ ↦ i))

theorem switches_constant (i : ι) (E : ι → ι → Prop) (T : ℕ) (loss : ℕ → ι → ℝ) :
    (constant i).switches E T loss=0 := by
  unfold switches actions
  simp only [switchCount_constant,Nat.cast_zero,ProbabilityVector.mean_const]

theorem regret_blocks (default : ι) (m : ℕ) (n : ℕ → ℕ) (B : ℕ) (P : GraphFeedbackEW ι m)
    (E : ι → ι → Prop) (T : ℕ) (loss : ℕ → ι → ℝ) :
    (blocks default m n B P).regret E T loss=
      ∫ x, pathRegret T loss (ScheduledExecution.trajectory default (fun b ↦ n b+1)
        (fun _ y ↦ blockActions default (Restarts.parts _ y.2.1) y.2.2) B x)
          ∂((P.algorithm E n loss).execution B).toMeasure := by
  rw [ProbabilityVector.integral_toMeasure]
  rfl

theorem switches_blocks (default : ι) (m : ℕ) (n : ℕ → ℕ) (B : ℕ) (P : GraphFeedbackEW ι m)
    (E : ι → ι → Prop) (T : ℕ) (loss : ℕ → ι → ℝ) :
    (blocks default m n B P).switches E T loss=
      ∫ x, (switchCount T (ScheduledExecution.trajectory default (fun b ↦ n b+1)
        (fun _ y ↦ blockActions default (Restarts.parts _ y.2.1) y.2.2) B x):ℝ)
          ∂((P.algorithm E n loss).execution B).toMeasure := by
  rw [ProbabilityVector.integral_toMeasure]
  rfl

end GraphStrategy
end
end Tournament.Model

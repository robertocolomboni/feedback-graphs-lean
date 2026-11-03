module

public import Tournament.Model.GraphFeedbackEW

@[expose] public section

namespace Tournament.Computation.FiniteRequests

inductive Program (K : ℕ) (α : Type) : Type 1 where
  | pure (value : α)
  | draw {β : Type} [Fintype β] (law : ProbabilityVector β) (next : β → Program K α)
  | observe (time : ℕ) (action : Fin K) (next : (Fin K → ℝ) → Program K α)

namespace Program

variable {K : ℕ} {α β : Type}

def bind : Program K α → (α → Program K β) → Program K β
  | .pure x, f => f x
  | @Program.draw _ _ γ inst p next, f => @Program.draw K β γ inst p (fun x => bind (next x) f)
  | .observe t i next, f => .observe t i (fun obs => bind (next obs) f)

def map (f : α → β) (p : Program K α) : Program K β := bind p (fun x => .pure (f x))

def sample {α : Type} [Fintype α] (p : ProbabilityVector α) : Program K α :=
  .draw p .pure

def observation (time : ℕ) (action : Fin K) : Program K (Fin K → ℝ) :=
  .observe time action .pure

noncomputable def expect (observations : ℕ → Fin K → Fin K → ℝ) :
    Program K α → (α → ℝ) → ℝ
  | .pure x, f => f x
  | @Program.draw _ _ γ inst p next, f => @ProbabilityVector.mean γ inst p
      (fun x => expect observations (next x) f)
  | .observe t i next, f => expect observations (next (observations t i)) f

@[simp] theorem expect_pure (observations : ℕ → Fin K → Fin K → ℝ) (a : α) (f : α → ℝ) :
    expect observations (.pure a) f = f a := rfl

theorem expect_bind (observations : ℕ → Fin K → Fin K → ℝ) (p : Program K α)
    (next : α → Program K β) (f : β → ℝ) :
    expect observations (p.bind next) f =
      expect observations p (fun x => expect observations (next x) f) := by
  induction p with
  | pure a => rfl
  | draw law next ih =>
      dsimp only [bind, expect]
      exact congrArg law.mean (funext ih)
  | observe t i next ih => exact ih (observations t i)

@[simp] theorem expect_map (observations : ℕ → Fin K → Fin K → ℝ) (p : Program K α)
    (g : α → β) (f : β → ℝ) :
    expect observations (p.map g) f = expect observations p (fun x => f (g x)) := by
  exact expect_bind observations p (fun x => .pure (g x)) f

@[simp] theorem expect_sample {α : Type} [Fintype α]
    (observations : ℕ → Fin K → Fin K → ℝ) (p : ProbabilityVector α) (f : α → ℝ) :
    expect observations (sample p) f = p.mean f := rfl

@[simp] theorem expect_observation (observations : ℕ → Fin K → Fin K → ℝ)
    (t : ℕ) (i : Fin K) (f : (Fin K → ℝ) → ℝ) :
    expect observations (observation t i) f = f (observations t i) := rfl

end Program
end Tournament.Computation.FiniteRequests

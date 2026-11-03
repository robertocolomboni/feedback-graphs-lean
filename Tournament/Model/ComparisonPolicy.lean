module

public import Tournament.Probability.FinitePath

@[expose] public section

namespace Tournament.Model

open scoped Classical

variable {ι : Type*} [Fintype ι]

noncomputable section

def comparisonObservation (F : ι → ι → Prop) (s : ι) (loss : ι → ℝ) (k : ι) : ℝ :=
  if F s k then loss s - loss k else 0

abbrev ComparisonHistory (ι : Type*) : ℕ → Type _
  | 0 => ι
  | n+1 => (ComparisonHistory ι n × (ι → ℝ)) × ι

def currentAction : (n : ℕ) → ComparisonHistory ι n → ι
  | 0, i => i
  | _+1, (_,i) => i

def recordComparisons (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    (n : ℕ) → FinitePath.History ι n → ComparisonHistory ι n
  | 0, i => i
  | n+1, (hist,i) => ((recordComparisons F loss n hist,
      comparisonObservation F (FinitePath.lastState n hist) (loss n)), i)

omit [Fintype ι] in
theorem currentAction_record (F : ι → ι → Prop) (loss : ℕ → ι → ℝ)
    (n : ℕ) (hist : FinitePath.History ι n) :
    currentAction n (recordComparisons F loss n hist) = FinitePath.lastState n hist := by
  cases n <;> rfl

structure ComparisonPolicy (ι : Type*) [Fintype ι] where
  initial : ProbabilityVector ι
  next : (n : ℕ) → ComparisonHistory ι n → (ι → ℝ) → ProbabilityVector ι

namespace ComparisonPolicy

def law (π : ComparisonPolicy ι) (F : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    (n : ℕ) → ProbabilityVector (FinitePath.History ι n)
  | 0 => π.initial
  | n+1 => (law π F loss n).joint (fun hist ↦
      π.next n (recordComparisons F loss n hist)
        (comparisonObservation F (FinitePath.lastState n hist) (loss n)))

end ComparisonPolicy
end
end Tournament.Model

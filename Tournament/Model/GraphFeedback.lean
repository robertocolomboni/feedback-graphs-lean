module

public import Tournament.Model.ComparisonPolicy
public import Tournament.Graphs.Feedback
public import Tournament.Probability.Extensionality

@[expose] public section

namespace Tournament.Model

open scoped Classical

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def graphObservation (E : ι → ι → Prop) (s : ι) (loss : ι → ℝ) (k : ι) : ℝ :=
  if E s k then loss k else 0

def selectedComparison (E : ι → ι → Prop) (s : ι) (obs : ι → ℝ) (k : ι) : ℝ :=
  if selectedEdge E s k then obs s-obs k else 0

omit [Fintype ι] in
theorem selectedComparison_record (E : ι → ι → Prop) (s : ι) (loss : ι → ℝ) :
    selectedComparison E s (graphObservation E s loss)=comparisonObservation (selectedEdge E) s loss := by
  funext k
  by_cases hk : selectedEdge E s k
  · have hcomparison := selectedEdge_determinesComparison hk
      (graphObservation E s loss) loss (by
        intro j hj
        simp only [graphObservation, ite_eq_left hj])
    simpa only [selectedComparison, comparisonObservation, ite_eq_left hk] using hcomparison
  · simp only [selectedComparison,comparisonObservation,ite_eq_right hk]

def translateHistory (E : ι → ι → Prop) : (n : ℕ) → ComparisonHistory ι n → ComparisonHistory ι n
  | 0, i => i
  | n+1, ((hist,obs),i) =>
      ((translateHistory E n hist,selectedComparison E (currentAction n hist) obs),i)

omit [Fintype ι] in
theorem translateHistory_current (E : ι → ι → Prop) (n : ℕ) (hist : ComparisonHistory ι n) :
    currentAction n (translateHistory E n hist)=currentAction n hist := by
  cases n <;> rfl

def recordGraph (E : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    (n : ℕ) → FinitePath.History ι n → ComparisonHistory ι n
  | 0, i => i
  | n+1, (hist,i) => ((recordGraph E loss n hist,
      graphObservation E (FinitePath.lastState n hist) (loss n)),i)

omit [Fintype ι] [LinearOrder ι] in
theorem recordGraph_current (E : ι → ι → Prop) (loss : ℕ → ι → ℝ)
    (n : ℕ) (hist : FinitePath.History ι n) :
    currentAction n (recordGraph E loss n hist)=FinitePath.lastState n hist := by
  cases n <;> rfl

omit [Fintype ι] in
theorem translateHistory_record (E : ι → ι → Prop) (loss : ℕ → ι → ℝ)
    (n : ℕ) (hist : FinitePath.History ι n) :
    translateHistory E n (recordGraph E loss n hist)=recordComparisons (selectedEdge E) loss n hist := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases hist with ⟨hist,i⟩
    simp only [recordGraph,translateHistory,recordComparisons,ih hist,recordGraph_current,
      selectedComparison_record]

structure GraphPolicy (ι : Type*) [Fintype ι] where
  initial : ProbabilityVector ι
  next : (n : ℕ) → ComparisonHistory ι n → (ι → ℝ) → ProbabilityVector ι

def GraphPolicy.law (π : GraphPolicy ι) (E : ι → ι → Prop) (loss : ℕ → ι → ℝ) :
    (n : ℕ) → ProbabilityVector (FinitePath.History ι n)
  | 0 => π.initial
  | n+1 => (π.law E loss n).joint (fun hist ↦ π.next n (recordGraph E loss n hist)
      (graphObservation E (FinitePath.lastState n hist) (loss n)))

def ComparisonPolicy.toGraph (π : ComparisonPolicy ι) (E : ι → ι → Prop) : GraphPolicy ι where
  initial := π.initial
  next n hist obs := π.next n (translateHistory E n hist)
    (selectedComparison E (currentAction n hist) obs)

theorem ComparisonPolicy.toGraph_law (π : ComparisonPolicy ι) (E : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (n : ℕ) :
    (π.toGraph E).law E loss n=π.law (selectedEdge E) loss n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply ProbabilityVector.ext_weights
    intro hist
    change (π.toGraph E).law E loss n hist.1*
      π.next n (translateHistory E n (recordGraph E loss n hist.1))
        (selectedComparison E (currentAction n (recordGraph E loss n hist.1))
          (graphObservation E (FinitePath.lastState n hist.1) (loss n))) hist.2=
      π.law (selectedEdge E) loss n hist.1*
        π.next n (recordComparisons (selectedEdge E) loss n hist.1)
          (comparisonObservation (selectedEdge E) (FinitePath.lastState n hist.1) (loss n)) hist.2
    rw [ih,translateHistory_record,recordGraph_current,selectedComparison_record]

end
end Tournament.Model

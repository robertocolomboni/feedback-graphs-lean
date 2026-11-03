module

public import Tournament.Graphs.Feedback
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace Tournament.Computation.GraphPreparation

variable {K : ℕ}

def select (A : Fin K → Fin K → Bool) (i j : Fin K) : Bool :=
  if i=j then A i i else
    (A i i && A i j) && (!(A j j && A j i) || decide (i<j))

def materialize (A : Fin K → Fin K → Bool) : List (List Bool) :=
  (List.finRange K).map (fun i => (List.finRange K).map (select A i))

theorem select_correct (A : Fin K → Fin K → Bool) (i j : Fin K) :
    select A i j=true ↔ selectedEdge (fun a b => A a b=true) i j := by
  cases hj : A j j <;> simp [select, selectedEdge, hj]

theorem output_eq (A : Fin K → Fin K → Bool) :
    (fun i j => select A i j=true)=selectedEdge (fun i j => A i j=true) := by
  funext i j
  exact propext (select_correct A i j)

theorem materialize_entry (A : Fin K → Fin K → Bool) (i j : Fin K) :
    ((materialize A)[i.val]?.bind (fun row => row[j.val]?))=some (select A i j) := by
  simp [materialize, i.isLt, j.isLt]

theorem specification (A : Fin K → Fin K → Bool)
    (hA : StronglyRevealing (fun i j => A i j=true)) :
    (∀ i j, select A i j=true → A i j=true) ∧
    IsTournament (fun i j => select A i j=true) ∧
    StronglyObservable (fun i j => select A i j=true) ∧
    (∀ i j, select A i j=true → DeterminesComparison (fun a b => A a b=true) i i j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact selectedEdge_subgraph (fun a b => A a b=true) ((select_correct A i j).mp hij)
  · rw [output_eq]
    exact selectedEdge_isTournament hA
  · rw [output_eq]
    exact selectedEdge_stronglyObservable hA
  · intro i j hij
    exact selectedEdge_determinesComparison ((select_correct A i j).mp hij)

end Tournament.Computation.GraphPreparation

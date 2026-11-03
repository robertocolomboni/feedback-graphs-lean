module

public import Tournament.Graphs.Structure
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament

variable {ι : Type*}

def SameFeedback (E : ι → ι → Prop) (s : ι) (f g : ι → ℝ) : Prop :=
  ∀ i, E s i → f i = g i

def DeterminesComparison (E : ι → ι → Prop) (s i j : ι) : Prop :=
  ∀ f g : ι → ℝ, SameFeedback E s f g → f i - f j = g i - g j

theorem determinesComparison_self (E : ι → ι → Prop) (s i : ι) :
    DeterminesComparison E s i i := by
  intro f g _
  simp

theorem determinesComparison_of_observed {E : ι → ι → Prop} {s i j : ι}
    (hi : E s i) (hj : E s j) : DeterminesComparison E s i j := by
  intro f g h
  rw [h i hi, h j hj]

theorem selectedEdge_determinesComparison [LinearOrder ι]
    {E : ι → ι → Prop} {s j : ι} (h : selectedEdge E s j) :
    DeterminesComparison E s s j := by
  apply determinesComparison_of_observed
  · exact (selectedEdge_self E s).mp (selectedEdge_source_loop E h)
  · exact selectedEdge_subgraph E h

def InClosedNeighborhood (F : ι → ι → Prop) (s i : ι) : Prop :=
  i = s ∨ F s i

theorem closedNeighborhood_determinesComparison [LinearOrder ι]
    {E : ι → ι → Prop} {s i j : ι}
    (hi : InClosedNeighborhood (selectedEdge E) s i)
    (hj : InClosedNeighborhood (selectedEdge E) s j) :
    DeterminesComparison E s i j := by
  classical
  by_cases hss : E s s
  · apply determinesComparison_of_observed
    · rcases hi with rfl | hi
      · exact hss
      · exact selectedEdge_subgraph E hi
    · rcases hj with rfl | hj
      · exact hss
      · exact selectedEdge_subgraph E hj
  · have hi' : i = s := by
      rcases hi with hi | hi
      · exact hi
      · exact False.elim (hss ((selectedEdge_self E s).mp (selectedEdge_source_loop E hi)))
    have hj' : j = s := by
      rcases hj with hj | hj
      · exact hj
      · exact False.elim (hss ((selectedEdge_self E s).mp (selectedEdge_source_loop E hj)))
    subst i
    subst j
    exact determinesComparison_self E s s

theorem comparison_from_source (f : ι → ℝ) (s i j : ι) :
    f i - f j = (f s - f j) - (f s - f i) := by
  ring

end Tournament

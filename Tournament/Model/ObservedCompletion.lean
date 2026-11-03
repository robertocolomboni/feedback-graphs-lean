module

public import Tournament.Model.GraphFeedback
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

namespace Tournament.Model

open MeasureTheory
open scoped Classical

noncomputable section

variable {ι A : Type*} {t : ℕ}

def observedCompletion (obs : Fin t → ι → ℝ) (s : ℕ) (i : ι) : ℝ :=
  if hs : s < t then obs ⟨s,hs⟩ i else 0

theorem observedCompletion_past (obs : Fin t → ι → ℝ) (s : Fin t) :
    observedCompletion obs s.val = obs s := by
  funext i
  simp only [observedCompletion, dite_eq_left s.isLt]

theorem observedCompletion_future (obs : Fin t → ι → ℝ) (s : ℕ) (hs : t ≤ s) :
    observedCompletion obs s = 0 := by
  funext i
  simp only [observedCompletion, dite_eq_right (by omega : ¬ s < t), Pi.zero_apply]

theorem observedCompletion_measurable [MeasurableSpace A]
    (obs : A → Fin t → ι → ℝ) (hobs : Measurable obs) (s : ℕ) (i : ι) :
    Measurable (fun a ↦ observedCompletion (obs a) s i) := by
  by_cases hs : s < t
  · simp only [observedCompletion, dite_eq_left hs]
    have htime : Measurable (fun a ↦ obs a (⟨s,hs⟩ : Fin t)) :=
      (measurable_pi_apply (⟨s,hs⟩ : Fin t)).comp hobs
    exact (measurable_pi_apply i).comp htime
  · simp only [observedCompletion, dite_eq_right hs]
    exact measurable_const

theorem graphObservation_idempotent (E : ι → ι → Prop) (a : ι) (loss : ι → ℝ) :
    graphObservation E a (graphObservation E a loss) = graphObservation E a loss := by
  funext i
  by_cases hi : E a i <;> simp only [graphObservation, hi, ite_true, ite_false]

theorem observedCompletion_preserves_graph (E : ι → ι → Prop)
    (actions : Fin t → ι) (loss : ℕ → ι → ℝ) (s : Fin t) :
    graphObservation E (actions s)
      (observedCompletion (fun r ↦ graphObservation E (actions r) (loss r.val)) s.val) =
      graphObservation E (actions s) (loss s.val) := by
  rw [observedCompletion_past, graphObservation_idempotent]

theorem observedCompletion_preserves_comparison [LinearOrder ι]
    (E : ι → ι → Prop) (actions : Fin t → ι) (loss : ℕ → ι → ℝ) (s : Fin t) :
    comparisonObservation (selectedEdge E) (actions s)
      (observedCompletion (fun r ↦ graphObservation E (actions r) (loss r.val)) s.val) =
      comparisonObservation (selectedEdge E) (actions s) (loss s.val) := by
  rw [← selectedComparison_record, ← selectedComparison_record,
    observedCompletion_preserves_graph]

end
end Tournament.Model

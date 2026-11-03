module

public import Tournament.Upper.AssignmentOptimum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

namespace Tournament.Upper

open MeasureTheory
open scoped Classical BigOperators

noncomputable section

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

theorem positiveAssignmentAnchor_measurable (p : X → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun x ↦ p x i)) (hPos : ∀ x i, 0 < p x i) :
    Measurable (fun x ↦ positiveAssignmentAnchor (p x) (hPos x)) := by
  exact (Measurable.of_eval hp).subtype_mk

theorem optimizedAssignment_data_measurable (F : ι → ι → Prop) (hF : IsTournament F)
    (p : X → ProbabilityVector ι) (hp : ∀ i, Measurable (fun x ↦ p x i))
    (hPos : ∀ x i, 0 < p x i) :
    Measurable (fun x ↦ assignmentData (optimizedAssignment F hF (p x) (hPos x))) := by
  change Measurable (fun x ↦ optimalAssignmentData F hF
    (positiveAssignmentAnchor (p x) (hPos x)))
  exact (optimalAssignmentData_measurable F hF).comp
    (positiveAssignmentAnchor_measurable p hp hPos)

theorem optimizedAssignment_matrix_measurable (F : ι → ι → Prop) (hF : IsTournament F)
    (p : X → ProbabilityVector ι) (hp : ∀ i, Measurable (fun x ↦ p x i))
    (hPos : ∀ x i, 0 < p x i) (s i r : ι) :
    Measurable (fun x ↦ (optimizedAssignment F hF (p x) (hPos x)).matrix s i r) := by
  have h := optimizedAssignment_data_measurable F hF p hp hPos
  exact ((h.fst.eval (a := s)).eval (a := i)).eval (a := r)

theorem optimizedAssignment_sourceWeight_measurable (F : ι → ι → Prop)
    (hF : IsTournament F) (p : X → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun x ↦ p x i)) (hPos : ∀ x i, 0 < p x i) (s : ι) :
    Measurable (fun x ↦ (optimizedAssignment F hF (p x) (hPos x)).sourceWeight s) := by
  exact (optimizedAssignment_data_measurable F hF p hp hPos).snd.eval

theorem optimizedAssignment_totalWeight_measurable (F : ι → ι → Prop)
    (hF : IsTournament F) (p : X → ProbabilityVector ι)
    (hp : ∀ i, Measurable (fun x ↦ p x i)) (hPos : ∀ x i, 0 < p x i) :
    Measurable (fun x ↦ (optimizedAssignment F hF (p x) (hPos x)).totalWeight) := by
  exact Finset.measurable_sum _ (fun s _ ↦
    optimizedAssignment_sourceWeight_measurable F hF p hp hPos s)

theorem optimizedAssignment_sourceLaw_measurable (F : ι → ι → Prop) (hF : IsTournament F)
    (p : X → ProbabilityVector ι) (hp : ∀ i, Measurable (fun x ↦ p x i))
    (hPos : ∀ x i, 0 < p x i) (s : ι) :
    Measurable (fun x ↦ (optimizedAssignment F hF (p x) (hPos x)).sourceLaw s) := by
  exact (optimizedAssignment_sourceWeight_measurable F hF p hp hPos s).div
    (optimizedAssignment_totalWeight_measurable F hF p hp hPos)

end

end Tournament.Upper

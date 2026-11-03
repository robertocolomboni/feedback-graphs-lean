module

public import Tournament.Upper.PreparedMeasurable

@[expose] public section

namespace Tournament.Model

open MeasureTheory
open scoped Classical
noncomputable section

variable {ι : Type*} [MeasurableSpace ι]

instance comparisonHistoryMeasurableSpace : (n : ℕ) → MeasurableSpace (ComparisonHistory ι n)
  | 0 => inferInstanceAs (MeasurableSpace ι)
  | n+1 => @Prod.instMeasurableSpace (ComparisonHistory ι n × (ι → ℝ)) ι
      (@Prod.instMeasurableSpace (ComparisonHistory ι n) (ι → ℝ)
        (comparisonHistoryMeasurableSpace n) inferInstance) inferInstance

theorem currentAction_measurable (n : ℕ) : Measurable (currentAction (ι := ι) n) := by
  cases n with
  | zero => exact measurable_id
  | succ n => exact measurable_snd

end
end Tournament.Model

namespace Tournament.Upper

open MeasureTheory Model
open scoped Classical BigOperators
noncomputable section

variable {ι A : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [MeasurableSpace A]

theorem finiteKernel_value_measurable (P : A → FiniteKernel ι)
    (hP : ∀ i j, Measurable (fun a ↦ P a i j)) (i j : A → ι) (hi : Measurable i) (hj : Measurable j) :
    Measurable (fun a ↦ P a (i a) (j a)) := by
  apply Probability.measurable_countable_parameter (fun k a ↦ P a k (j a)) _ i hi
  intro k
  exact Probability.measurable_countable_parameter (fun l a ↦ P a k l) (hP k) j hj

theorem scoreFromComparisons_measurable (F : ι → ι → Prop) (P : A → FiniteKernel ι)
    (hP : ∀ i j, Measurable (fun a ↦ P a i j)) (i j : A → ι) (hi : Measurable i) (hj : Measurable j)
    (obs : A → ι → ℝ) (hObs : ∀ k, Measurable (fun a ↦ obs a k)) :
    Measurable (fun a ↦ scoreFromComparisons F (P a) (i a) (obs a) (j a)) := by
  apply Probability.measurable_countable_parameter
    (fun ij a ↦ scoreFromComparisons F (P a) ij.1 (obs a) ij.2) _ (fun a ↦ (i a,j a)) (hi.prodMk hj)
  intro ij
  by_cases hji : ij.2=ij.1
  · simp only [scoreFromComparisons,ite_eq_left hji]
    apply Measurable.div _ (hP ij.1 ij.1)
    apply Measurable.neg
    apply Finset.measurable_sum
    intro k _
    by_cases hF : F ij.1 k
    · simp only [ite_eq_left hF]
      exact (hP ij.1 k).mul (hObs k)
    · simp only [ite_eq_right hF,mul_zero]
      exact measurable_const
  · simp only [scoreFromComparisons,ite_eq_right hji]
    by_cases hF : F ij.1 ij.2
    · simpa only [ite_eq_left hF] using hObs ij.2
    · simp only [ite_eq_right hF]
      exact measurable_const

end
end Tournament.Upper

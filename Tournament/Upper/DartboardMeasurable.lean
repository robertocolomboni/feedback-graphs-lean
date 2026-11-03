module

public import Tournament.Upper.DartboardPath
public import Tournament.Probability.VectorKernel

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {A ι : Type*} [MeasurableSpace A] [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem update_weight_measurable (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (g : A → ι → ℝ) (hg : ∀ i, Measurable (fun a ↦ g a i)) (η : ℝ) (i : ι) :
    Measurable (fun a ↦ Model.exponentialUpdate (p a) η (g a) i) := by
  have hnum (j : ι) : Measurable (fun a ↦ p a j*Real.exp (-η*g a j)) :=
    (hp j).mul ((hg j).const_mul (-η)).exp
  exact (hnum i).div (Finset.measurable_sum Finset.univ (fun j _ ↦ hnum j))

theorem weights_measurable (η : ℝ) (g : A → ℕ → ι → ℝ) (hg : ∀ n i, Measurable (fun a ↦ g a n i))
    (n : ℕ) (i : ι) : Measurable (fun a ↦ weights η (g a) n i) := by
  induction n generalizing i with
  | zero => exact measurable_const
  | succ n ih =>
    exact update_weight_measurable (fun a ↦ weights η (g a) n) ih
      (fun a ↦ g a n) (hg n) η i

instance historyMeasurableSpace (n : ℕ) : MeasurableSpace (FinitePath.History ι n) := ⊤

instance historyDiscreteMeasurableSpace (n : ℕ) : DiscreteMeasurableSpace (FinitePath.History ι n) := ⟨fun _ ↦ trivial⟩

end
end Tournament.Upper.ShrinkingDartboard

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace Tournament.Probability

open MeasureTheory
open scoped Classical BigOperators
noncomputable section

theorem integral_nat_count {Ω α : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Finset α) (P : Ω → α → Prop)
    [∀ ω i, Decidable (P ω i)] :
    (∫ ω, ((∑ i∈s, if P ω i then 1 else 0 : ℕ):ℝ) ∂μ)=∑ i∈s, μ.real {ω | P ω i} := by
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [integral_finsetSum s (fun _ _ ↦ Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  have h : (fun ω ↦ if P ω i then (1:ℝ) else 0)=({ω | P ω i}).indicator (1 : Ω → ℝ) := by
    funext ω
    by_cases hp : P ω i <;> simp [hp]
  rw [h,integral_indicator_one MeasurableSet.of_discrete]

end
end Tournament.Probability

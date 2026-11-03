module

public import Tournament.Upper.ExplorationMoments

@[expose] public section

namespace Tournament.Upper.Exploration

open MeasureTheory ProbabilityTheory ShrinkingDartboard
open scoped Classical

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem actual_dartboard_guarantee (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0<η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T : ℕ) (hT : 1≤T) (default : ι) :
    RandomGuarantee (execution E D κ hκ hκ1 η hη.le loss hloss T).toMeasure
      (estimatesOnExecution E D κ hκ loss hloss T) (fun n x ↦ latentAt D default T x n) η T := by
  let μ := (execution E D κ hκ hκ1 η hη.le loss hloss T).toMeasure
  let g := estimatesOnExecution E D κ hκ loss hloss T
  let I := fun n x ↦ latentAt D default T x n
  let β := fun n ↦ Kernel.const (LossHistory ι n) (estimateLaw E D κ hκ hκ1 (loss n) (hloss n))
  let δ := fun n ↦ condDistrib (I n) (lossHistory g n) μ
  have : ∀ n, IsMarkovKernel (β n) := fun _ ↦ inferInstance
  have : ∀ n, IsMarkovKernel (δ n) := fun _ ↦ inferInstance
  exact shrinking_dartboard_before μ g (fun _ ↦ measurable_of_finite _) I
    (fun _ ↦ measurable_of_finite _) η hη T β δ
    (initial_latent_law E D κ hκ hκ1 η hη.le loss hloss T hT default)
    (fun n hn ↦ independent_estimate_latent E D κ hκ hκ1 η hη.le loss hloss T n hn default)
    (fun n hn ↦ fresh_latent_transition E D κ hκ hκ1 η hη.le loss hloss T n hn default)
    (fun _ _ _ ↦ Integrable.of_finite)

end
end Tournament.Upper.Exploration

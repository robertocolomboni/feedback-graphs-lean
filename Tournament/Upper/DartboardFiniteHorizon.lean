module

public import Tournament.Upper.DartboardGuarantee

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem conditional_past_before (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (I : ℕ → Ω → ι) (η : ℝ) (hη : 0≤η) (T : ℕ)
    (β : (n : ℕ) → Kernel (LossHistory ι n) (LossVector ι))
    (δ : (n : ℕ) → Kernel (LossHistory ι n) ι)
    [∀ n, IsMarkovKernel (β n)] [∀ n, IsMarkovKernel (δ n)]
    (hInitial : HasCondDistrib (I 0) (lossHistory g 0)
      (ProbabilityVector.kernel (historyWeights η 0) (historyWeights_measurable η 0)) μ)
    (hIndep : ∀ n<T, HasCondDistrib (fun ω ↦ (g n ω,I n ω)) (lossHistory g n) (β n ×ₖ δ n) μ)
    (hFresh : ∀ n, n+1<T → HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshTransition η hη n) μ) (n : ℕ) (hn : n<T) :
    HasCondDistrib (I n) (lossHistory g n)
      (ProbabilityVector.kernel (historyWeights η n) (historyWeights_measurable η n)) μ := by
  induction n with
  | zero => exact hInitial
  | succ n ih =>
    have hCurrent := conditional_current_of_past μ g I η n (β n) (δ n) (hIndep n (by omega)) (ih (by omega))
    exact conditional_update μ (lossHistory g (n+1)) (I n) (I (n+1))
      (fun h ↦ historyWeights η n (Fin.init h)) (previousWeights_measurable η n)
      η hη (fun h i ↦ (h (Fin.last n) i : ℝ)) (fun h i ↦ (h (Fin.last n) i).coe_nonneg)
      (lastLoss_measurable n) hCurrent (hFresh n hn)

theorem shrinking_dartboard_before (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0<η) (T : ℕ)
    (β : (n : ℕ) → Kernel (LossHistory ι n) (LossVector ι))
    (δ : (n : ℕ) → Kernel (LossHistory ι n) ι)
    [∀ n, IsMarkovKernel (β n)] [∀ n, IsMarkovKernel (δ n)]
    (hInitial : HasLaw (I 0) (ExponentialWeights.uniform (ι := ι)).toMeasure μ)
    (hIndep : ∀ n<T, HasCondDistrib (fun ω ↦ (g n ω,I n ω)) (lossHistory g n) (β n ×ₖ δ n) μ)
    (hFresh : ∀ n, n+1<T → HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshTransition η hη.le n) μ)
    (hInt : ∀ n ∈ Finset.range T, ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ) :
    RandomGuarantee μ g I η T := by
  have hInit := initial_condition μ g I (hI 0) η hInitial
  have hCurrent (n : ℕ) (hn : n<T) : HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ :=
    conditional_current_of_past μ g I η n (β n) (δ n) (hIndep n hn)
      (conditional_past_before μ g I η hη.le T β δ hInit hIndep hFresh n hn)
  refine ⟨hCurrent,?_,?_⟩
  · exact fun i ↦ expected_second_order μ g hg I hI η hη T
      (fun n hn ↦ hCurrent n (Finset.mem_range.mp hn)) hInt i
  · exact expected_switches μ g hg I hI η hη.le T
      (fun n hn ↦ hCurrent n (Finset.mem_range.mp hn))
      (fun n hn ↦ hFresh n (by simp only [Finset.mem_range] at hn; omega)) hInt

end
end Tournament.Upper.ShrinkingDartboard

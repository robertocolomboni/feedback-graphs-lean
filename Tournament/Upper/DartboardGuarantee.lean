module

public import Tournament.Upper.DartboardSwitches

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

def RandomGuarantee (μ : Measure Ω) (g : ℕ → Ω → LossVector ι) (I : ℕ → Ω → ι)
    (η : ℝ) (T : ℕ) : Prop :=
  (∀ n<T, HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ) ∧
  (∀ i, ENNReal.ofReal ((∫ ω, ∑ t ∈ Finset.range T, (g t ω (I t ω) : ℝ) ∂μ)-
      (∫ ω, ∑ t ∈ Finset.range T, (g t ω i : ℝ) ∂μ))≤
    ENNReal.ofReal (Real.log (Fintype.card ι:ℝ)/η)+ENNReal.ofReal (η/2)*
      (∫⁻ ω, ENNReal.ofReal (quadraticTotal η g T ω) ∂μ)) ∧
  ((∫ ω, (Model.switchCount T (fun t ↦ I t ω) : ℝ) ∂μ)≤
    η*(∫ ω, ∑ t ∈ Finset.range T, (randomWeights η g t ω).mean (fun i ↦ (g t ω i : ℝ)) ∂μ))

theorem shrinking_dartboard (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0<η) (T : ℕ)
    (β : (n : ℕ) → Kernel (LossHistory ι n) (LossVector ι))
    (δ : (n : ℕ) → Kernel (LossHistory ι n) ι)
    [∀ n, IsMarkovKernel (β n)] [∀ n, IsMarkovKernel (δ n)]
    (hInitial : HasLaw (I 0) (ExponentialWeights.uniform (ι := ι)).toMeasure μ)
    (hIndep : ∀ n<T, HasCondDistrib (fun ω ↦ (g n ω,I n ω)) (lossHistory g n) (β n ×ₖ δ n) μ)
    (hFresh : ∀ n<T, HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshTransition η hη.le n) μ)
    (hInt : ∀ n ∈ Finset.range T, ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ) :
    RandomGuarantee μ g I η T := by
  have hInit := initial_condition μ g I (hI 0) η hInitial
  have hCurrent (n : ℕ) (hn : n<T) :
      HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ :=
    conditional_current_upto μ g I η hη.le T β δ hInit hIndep hFresh n hn
  refine ⟨hCurrent,?_,?_⟩
  · exact fun i ↦ expected_second_order μ g hg I hI η hη T
      (fun n hn ↦ hCurrent n (Finset.mem_range.mp hn)) hInt i
  · exact expected_switches μ g hg I hI η hη.le T
      (fun n hn ↦ hCurrent n (Finset.mem_range.mp hn))
      (fun n hn ↦ hFresh n (by simp only [Finset.mem_range] at hn; omega)) hInt

theorem shrinking_dartboard_of_native_independence [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0<η) (T : ℕ)
    (hInitial : HasLaw (I 0) (ExponentialWeights.uniform (ι := ι)).toMeasure μ)
    (hIndep : ∀ n<T, g n ⟂ᵢ[lossHistory g n,lossHistory_measurable g hg n;μ] I n)
    (hFresh : ∀ n<T, HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshTransition η hη.le n) μ)
    (hInt : ∀ n ∈ Finset.range T, ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ) :
    RandomGuarantee μ g I η T := by
  exact shrinking_dartboard μ g hg I hI η hη T
    (fun t ↦ condDistrib (g t) (lossHistory g t) μ)
    (fun t ↦ condDistrib (I t) (lossHistory g t) μ) hInitial
    (fun t ht ↦ Tournament.Probability.conditional_product_of_indep μ (lossHistory g t)
      (lossHistory_measurable g hg t) (g t) (hg t) (I t) (hI t) (hIndep t ht)) hFresh hInt

end
end Tournament.Upper.ShrinkingDartboard

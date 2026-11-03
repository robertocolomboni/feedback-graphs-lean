module

public import Tournament.Upper.DartboardHistory
public import Tournament.Probability.ConditionalIndependence

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

def previousWeightKernel (η : ℝ) (n : ℕ) : Kernel (LossHistory ι (n+1)) ι :=
  ProbabilityVector.kernel (fun h ↦ historyWeights η n (Fin.init h)) (previousWeights_measurable η n)

def freshTransition (η : ℝ) (hη : 0≤η) (n : ℕ) : Kernel (LossHistory ι (n+1) × ι) ι :=
  transitionRowKernel (fun h ↦ historyWeights η n (Fin.init h)) (previousWeights_measurable η n)
    η hη (fun h i ↦ (h (Fin.last n) i : ℝ)) (fun h i ↦ (h (Fin.last n) i).coe_nonneg)
    (lastLoss_measurable n)

instance freshTransition_markov (η : ℝ) (hη : 0≤η) (n : ℕ) : IsMarkovKernel (freshTransition (ι := ι) η hη n) := by
  unfold freshTransition
  infer_instance

theorem initial_condition (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (I : ℕ → Ω → ι) (hI : Measurable (I 0)) (η : ℝ)
    (hLaw : HasLaw (I 0) (ExponentialWeights.uniform (ι := ι)).toMeasure μ) :
    HasCondDistrib (I 0) (lossHistory g 0)
      (ProbabilityVector.kernel (historyWeights η 0) (historyWeights_measurable η 0)) μ := by
  apply Tournament.Probability.conditional_const_of_const_condition (lossHistory g 0) (I 0)
    (fun t ↦ Fin.elim0 t) _ hI _ hLaw
  funext ω t
  exact Fin.elim0 t

theorem conditional_current_of_past (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (I : ℕ → Ω → ι) (η : ℝ) (n : ℕ)
    (β : Kernel (LossHistory ι n) (LossVector ι)) [IsMarkovKernel β]
    (δ : Kernel (LossHistory ι n) ι) [IsMarkovKernel δ]
    (hJoint : HasCondDistrib (fun ω ↦ (g n ω,I n ω)) (lossHistory g n) (β ×ₖ δ) μ)
    (hPast : HasCondDistrib (I n) (lossHistory g n)
      (ProbabilityVector.kernel (historyWeights η n) (historyWeights_measurable η n)) μ) :
    HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ := by
  have hJoint' := Tournament.Probability.replace_independent_marginal hJoint hPast
  have hCurrent := Tournament.Probability.independent_enlargement hJoint'
  have h := hCurrent.measurableEquiv_comp_right (appendLoss n)
  rw [append_lossHistory] at h
  exact h

theorem conditional_past (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (I : ℕ → Ω → ι) (η : ℝ) (hη : 0≤η)
    (β : (n : ℕ) → Kernel (LossHistory ι n) (LossVector ι))
    (δ : (n : ℕ) → Kernel (LossHistory ι n) ι)
    [∀ n, IsMarkovKernel (β n)] [∀ n, IsMarkovKernel (δ n)]
    (hInitial : HasCondDistrib (I 0) (lossHistory g 0)
      (ProbabilityVector.kernel (historyWeights η 0) (historyWeights_measurable η 0)) μ)
    (hIndep : ∀ n, HasCondDistrib (fun ω ↦ (g n ω,I n ω)) (lossHistory g n) (β n ×ₖ δ n) μ)
    (hFresh : ∀ n, HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshTransition η hη n) μ) (n : ℕ) :
    HasCondDistrib (I n) (lossHistory g n)
      (ProbabilityVector.kernel (historyWeights η n) (historyWeights_measurable η n)) μ := by
  induction n with
  | zero => exact hInitial
  | succ n ih =>
    have hCurrent := conditional_current_of_past μ g I η n (β n) (δ n) (hIndep n) ih
    exact conditional_update μ (lossHistory g (n+1)) (I n) (I (n+1))
      (fun h ↦ historyWeights η n (Fin.init h)) (previousWeights_measurable η n)
      η hη (fun h i ↦ (h (Fin.last n) i : ℝ)) (fun h i ↦ (h (Fin.last n) i).coe_nonneg)
      (lastLoss_measurable n) hCurrent (hFresh n)

theorem conditional_current (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (I : ℕ → Ω → ι) (η : ℝ) (hη : 0≤η)
    (β : (n : ℕ) → Kernel (LossHistory ι n) (LossVector ι))
    (δ : (n : ℕ) → Kernel (LossHistory ι n) ι)
    [∀ n, IsMarkovKernel (β n)] [∀ n, IsMarkovKernel (δ n)]
    (hInitial : HasCondDistrib (I 0) (lossHistory g 0)
      (ProbabilityVector.kernel (historyWeights η 0) (historyWeights_measurable η 0)) μ)
    (hIndep : ∀ n, HasCondDistrib (fun ω ↦ (g n ω,I n ω)) (lossHistory g n) (β n ×ₖ δ n) μ)
    (hFresh : ∀ n, HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshTransition η hη n) μ) (n : ℕ) :
    HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ :=
  conditional_current_of_past μ g I η n (β n) (δ n) (hIndep n)
    (conditional_past μ g I η hη β δ hInitial hIndep hFresh n)

theorem conditional_current_of_native_independence [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0≤η)
    (hInitial : HasCondDistrib (I 0) (lossHistory g 0)
      (ProbabilityVector.kernel (historyWeights η 0) (historyWeights_measurable η 0)) μ)
    (hIndep : ∀ n, g n ⟂ᵢ[lossHistory g n,lossHistory_measurable g hg n;μ] I n)
    (hFresh : ∀ n, HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshTransition η hη n) μ) (n : ℕ) :
    HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ := by
  exact conditional_current μ g I η hη
    (fun t ↦ condDistrib (g t) (lossHistory g t) μ)
    (fun t ↦ condDistrib (I t) (lossHistory g t) μ) hInitial
    (fun t ↦ Tournament.Probability.conditional_product_of_indep μ (lossHistory g t)
      (lossHistory_measurable g hg t) (g t) (hg t) (I t) (hI t) (hIndep t)) hFresh n

theorem conditional_past_upto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (I : ℕ → Ω → ι) (η : ℝ) (hη : 0≤η) (T : ℕ)
    (β : (n : ℕ) → Kernel (LossHistory ι n) (LossVector ι))
    (δ : (n : ℕ) → Kernel (LossHistory ι n) ι)
    [∀ n, IsMarkovKernel (β n)] [∀ n, IsMarkovKernel (δ n)]
    (hInitial : HasCondDistrib (I 0) (lossHistory g 0)
      (ProbabilityVector.kernel (historyWeights η 0) (historyWeights_measurable η 0)) μ)
    (hIndep : ∀ n<T, HasCondDistrib (fun ω ↦ (g n ω,I n ω)) (lossHistory g n) (β n ×ₖ δ n) μ)
    (hFresh : ∀ n<T, HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshTransition η hη n) μ) (n : ℕ) (hn : n≤T) :
    HasCondDistrib (I n) (lossHistory g n)
      (ProbabilityVector.kernel (historyWeights η n) (historyWeights_measurable η n)) μ := by
  induction n with
  | zero => exact hInitial
  | succ n ih =>
    have hnT : n<T := by omega
    have hCurrent := conditional_current_of_past μ g I η n (β n) (δ n) (hIndep n hnT) (ih (by omega))
    exact conditional_update μ (lossHistory g (n+1)) (I n) (I (n+1))
      (fun h ↦ historyWeights η n (Fin.init h)) (previousWeights_measurable η n)
      η hη (fun h i ↦ (h (Fin.last n) i : ℝ)) (fun h i ↦ (h (Fin.last n) i).coe_nonneg)
      (lastLoss_measurable n) hCurrent (hFresh n hnT)

theorem conditional_current_upto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (I : ℕ → Ω → ι) (η : ℝ) (hη : 0≤η) (T : ℕ)
    (β : (n : ℕ) → Kernel (LossHistory ι n) (LossVector ι))
    (δ : (n : ℕ) → Kernel (LossHistory ι n) ι)
    [∀ n, IsMarkovKernel (β n)] [∀ n, IsMarkovKernel (δ n)]
    (hInitial : HasCondDistrib (I 0) (lossHistory g 0)
      (ProbabilityVector.kernel (historyWeights η 0) (historyWeights_measurable η 0)) μ)
    (hIndep : ∀ n<T, HasCondDistrib (fun ω ↦ (g n ω,I n ω)) (lossHistory g n) (β n ×ₖ δ n) μ)
    (hFresh : ∀ n<T, HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshTransition η hη n) μ) (n : ℕ) (hn : n<T) :
    HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ :=
  conditional_current_of_past μ g I η n (β n) (δ n) (hIndep n hn)
    (conditional_past_upto μ g I η hη T β δ hInitial hIndep hFresh n hn.le)

end
end Tournament.Upper.ShrinkingDartboard

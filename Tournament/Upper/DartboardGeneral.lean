module

public import Tournament.Upper.DartboardFreshRandomness
public import Tournament.Probability.ConditionalIndependence

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem freshTransition_of_fresh_coin_draw
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0≤η) (n : ℕ)
    (C : Ω → Bool) (R : Ω → ι) (hC : Measurable C) (hR : Measurable R)
    (hCoin : HasCondDistrib C (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) (freshCoinKernel η hη n) μ)
    (hDraw : HasCondDistrib R (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) (freshResampleKernel η n) μ)
    (hIndependent : Tournament.Probability.CondIndepGiven
      (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) C R μ)
    (hUpdate : I (n+1) =ᵐ[μ] fun ω ↦ if C ω then I n ω else R ω) :
    HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) (freshTransition η hη n) μ := by
  have hJoint := Tournament.Probability.conditional_product_of_indep_given_marginals μ
    (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) ((lossHistory_measurable g hg (n+1)).prodMk (hI n))
    C hC R hR hIndependent (freshCoinKernel η hη n) (freshResampleKernel η n) hCoin hDraw
  exact conditional_keep_resample_of_joint μ (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) C R (I (n+1))
    (fun h ↦ historyWeights η n (Fin.init h)) (previousWeights_measurable η n) η hη
    (fun h i ↦ (h (Fin.last n) i : ℝ)) (fun h i ↦ (h (Fin.last n) i).coe_nonneg)
    (lastLoss_measurable n) hJoint hUpdate

theorem shrinking_dartboard_of_primitive_laws
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0<η) (T : ℕ)
    (C : ℕ → Ω → Bool) (R : ℕ → Ω → ι)
    (hC : ∀ n, n+1<T → Measurable (C n)) (hR : ∀ n, n+1<T → Measurable (R n))
    (hInitial : HasLaw (I 0) (ExponentialWeights.uniform (ι := ι)).toMeasure μ)
    (hIndep : ∀ n<T, Tournament.Probability.CondIndepGiven (lossHistory g n) (g n) (I n) μ)
    (hCoin : ∀ n, n+1<T → HasCondDistrib (C n) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshCoinKernel η hη.le n) μ)
    (hDraw : ∀ n, n+1<T → HasCondDistrib (R n) (fun ω ↦ (lossHistory g (n+1) ω,I n ω))
      (freshResampleKernel η n) μ)
    (hFresh : ∀ n, n+1<T → Tournament.Probability.CondIndepGiven
      (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) (C n) (R n) μ)
    (hUpdate : ∀ n, n+1<T → I (n+1) =ᵐ[μ] fun ω ↦ if C n ω then I n ω else R n ω)
    (hInt : ∀ n ∈ Finset.range T, ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ) :
    RandomGuarantee μ g I η T := by
  have hTransition (n : ℕ) (hn : n+1<T) :
      HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) (freshTransition η hη.le n) μ :=
    freshTransition_of_fresh_coin_draw μ g hg I hI η hη.le n (C n) (R n) (hC n hn) (hR n hn)
      (hCoin n hn) (hDraw n hn) (hFresh n hn) (hUpdate n hn)
  exact shrinking_dartboard_before μ g hg I hI η hη T
    (fun n ↦ condDistrib (g n) (lossHistory g n) μ)
    (fun n ↦ condDistrib (I n) (lossHistory g n) μ) hInitial
    (fun n hn ↦ Tournament.Probability.conditional_product_of_indep_given μ (lossHistory g n)
      (lossHistory_measurable g hg n) (g n) (hg n) (I n) (hI n) (hIndep n hn)) hTransition hInt

theorem shrinking_dartboard_general
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0<η) (T : ℕ)
    (C : ℕ → Ω → Bool) (R : ℕ → Ω → ι)
    (hC : ∀ n, n+1<T → Measurable (C n)) (hR : ∀ n, n+1<T → Measurable (R n))
    (hInitial : HasLaw (I 0) (ExponentialWeights.uniform (ι := ι)).toMeasure μ)
    (hIndep : ∀ n<T, Tournament.Probability.CondIndepGiven (lossHistory g n) (g n) (I n) μ)
    (hCoin : ∀ n, n+1<T → ∀ b : Bool,
      (μ⟦{ω | C n ω=b} | MeasurableSpace.comap (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) inferInstance⟧) =ᵐ[μ]
        fun ω ↦ if b then keep η (fun i ↦ (g n ω i : ℝ)) (I n ω)
          else 1-keep η (fun i ↦ (g n ω i : ℝ)) (I n ω))
    (hDraw : ∀ n, n+1<T → ∀ j : ι,
      (μ⟦{ω | R n ω=j} | MeasurableSpace.comap (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) inferInstance⟧) =ᵐ[μ]
        fun ω ↦ Model.exponentialUpdate (randomWeights η g n ω) η (fun i ↦ (g n ω i : ℝ)) j)
    (hFresh : ∀ n, n+1<T → Tournament.Probability.CondIndepGiven
      (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) (C n) (R n) μ)
    (hUpdate : ∀ n, n+1<T → I (n+1) =ᵐ[μ] fun ω ↦ if C n ω then I n ω else R n ω)
    (hInt : ∀ n ∈ Finset.range T, ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ) :
    RandomGuarantee μ g I η T := by
  apply shrinking_dartboard_of_primitive_laws μ g hg I hI η hη T C R hC hR hInitial hIndep
  · intro n hn
    apply Tournament.Probability.conditional_law_of_singleton_condExp μ
      (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) ((lossHistory_measurable g hg (n+1)).prodMk (hI n))
      (C n) (hC n hn) (freshCoinKernel η hη.le n)
    intro b
    rw [Set.preimage_singleton]
    convert hCoin n hn b using 1
    funext ω
    change ((Restarts.coin _ _ _).toMeasure).real {b} = _
    rw [measureReal_def, ProbabilityVector.toMeasure_singleton, ENNReal.toReal_ofReal (ProbabilityVector.nonneg _ b)]
    rfl
  · intro n hn
    apply Tournament.Probability.conditional_law_of_singleton_condExp μ
      (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) ((lossHistory_measurable g hg (n+1)).prodMk (hI n))
      (R n) (hR n hn) (freshResampleKernel η n)
    intro j
    rw [Set.preimage_singleton]
    convert hDraw n hn j using 1
    funext ω
    change ((Model.exponentialUpdate _ η _).toMeasure).real {j} = _
    rw [measureReal_def, ProbabilityVector.toMeasure_singleton, ENNReal.toReal_ofReal (ProbabilityVector.nonneg _ j)]
    change Model.exponentialUpdate (historyWeights η n (lossHistory g n ω)) η
      (fun i ↦ (g n ω i : ℝ)) j = _
    rw [historyWeights_eq_weights]
    rfl
  · exact hFresh
  · exact hUpdate
  · exact hInt

end
end Tournament.Upper.ShrinkingDartboard

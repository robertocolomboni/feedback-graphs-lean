module

public import Tournament.Upper.DartboardExpectation

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory Filter
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

omit [Nonempty ι] in
theorem switch_indicator_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I J : Ω → ι) (hI : Measurable I) (hJ : Measurable J) :
    Integrable (fun ω ↦ if J ω=I ω then (0:ℝ) else 1) μ := by
  apply (integrable_const (1:ℝ)).mono'
    ((Measurable.ite (measurableSet_eq_fun hJ hI) measurable_const measurable_const).aestronglyMeasurable)
  exact Eventually.of_forall (fun ω ↦ by split_ifs <;> norm_num)

theorem switch_step_expectation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0≤η) (n : ℕ)
    (hFresh : HasCondDistrib (I (n+1)) (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) (freshTransition η hη n) μ)
    (hInt : ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ) :
    (∫ ω, if I (n+1) ω=I n ω then (0:ℝ) else 1 ∂μ)≤η*(∫ ω, (g n ω (I n ω) : ℝ) ∂μ) := by
  let X : Ω → LossHistory ι (n+1) × ι := fun ω ↦ (lossHistory g (n+1) ω,I n ω)
  have hX : Measurable X := (lossHistory_measurable g hg (n+1)).prodMk (hI n)
  let p : (LossHistory ι (n+1) × ι) → ProbabilityVector ι := fun q ↦
    (kernel (historyWeights η n (Fin.init q.1)) η hη (fun i ↦ (q.1 (Fin.last n) i : ℝ))
      (fun i ↦ (q.1 (Fin.last n) i).coe_nonneg)).row q.2
  have hp : ∀ j, Measurable (fun q ↦ p q j) := transitionRowWeights_measurable _
    (previousWeights_measurable η n) η hη _ (fun h i ↦ (h (Fin.last n) i).coe_nonneg) (lastLoss_measurable n)
  let F : (LossHistory ι (n+1) × ι) → ι → ℝ := fun q j ↦ if j=q.2 then 0 else 1
  have hF (j : ι) : Measurable (fun q ↦ F q j) :=
    Measurable.ite (measurableSet_eq_fun measurable_const measurable_snd) measurable_const measurable_const
  have hFI (j : ι) : Integrable (fun ω ↦ F (X ω) j) μ := by
    apply (integrable_const (1:ℝ)).mono' ((hF j).comp hX).aestronglyMeasurable
    exact Eventually.of_forall (fun ω ↦ by
      change ‖(if j=(X ω).2 then (0:ℝ) else 1)‖≤1
      split_ifs <;> norm_num)
  have hLaw : HasCondDistrib (I (n+1)) X (ProbabilityVector.kernel p hp) μ := hFresh
  have hEq := Tournament.Probability.conditional_finite_mean μ X hX (I (n+1)) (hI (n+1)) p hp hLaw F hF hFI
  have hMean := Tournament.Probability.integrable_finite_mean μ (fun ω ↦ p (X ω))
    (fun j ↦ (hp j).comp hX) (fun ω j ↦ F (X ω) j) hFI
  have hSelected := Tournament.Probability.integrable_finite_selection μ (fun ω j ↦ (g n ω j : ℝ)) hInt (I n) (hI n)
  change (∫ ω, F (X ω) (I (n+1) ω) ∂μ)≤_
  rw [hEq]
  calc
    _ ≤ ∫ ω, η*(g n ω (I n ω) : ℝ) ∂μ := integral_mono hMean (hSelected.const_mul η) (fun ω ↦ by
      exact kernel_switch_le _ η hη (fun i ↦ (g n ω i : ℝ)) (fun i ↦ (g n ω i).coe_nonneg) (I n ω))
    _ = _ := integral_const_mul _ _

theorem expected_switches (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0≤η) (T : ℕ)
    (hCurrent : ∀ n ∈ Finset.range T, HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ)
    (hFresh : ∀ n ∈ Finset.range (T-1), HasCondDistrib (I (n+1))
      (fun ω ↦ (lossHistory g (n+1) ω,I n ω)) (freshTransition η hη n) μ)
    (hInt : ∀ n ∈ Finset.range T, ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ) :
    (∫ ω, (Model.switchCount T (fun t ↦ I t ω) : ℝ) ∂μ)≤
      η*(∫ ω, ∑ t ∈ Finset.range T, (randomWeights η g t ω).mean (fun i ↦ (g t ω i : ℝ)) ∂μ) := by
  have hSub : Finset.range (T-1) ⊆ Finset.range T := Finset.range_mono (Nat.sub_le T 1)
  have hCast (ω : Ω) : (Model.switchCount T (fun t ↦ I t ω) : ℝ)=
      ∑ t ∈ Finset.range (T-1), if I (t+1) ω=I t ω then (0:ℝ) else 1 := by
    simp only [Model.switchCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
  simp_rw [hCast]
  rw [integral_finsetSum _ (fun t _ ↦ switch_indicator_integrable μ (I t) (I (t+1)) (hI t) (hI (t+1)))]
  have hMean (t : ℕ) (ht : t ∈ Finset.range T) :
      Integrable (fun ω ↦ (randomWeights η g t ω).mean (fun i ↦ (g t ω i : ℝ))) μ :=
    Tournament.Probability.integrable_finite_mean μ (randomWeights η g t)
      (randomWeights_measurable η g hg t) (fun ω i ↦ (g t ω i : ℝ)) (hInt t ht)
  rw [integral_finsetSum _ hMean,Finset.mul_sum]
  calc
    _ ≤ ∑ t ∈ Finset.range (T-1), η*(∫ ω, (randomWeights η g t ω).mean (fun i ↦ (g t ω i : ℝ)) ∂μ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact (switch_step_expectation μ g hg I hI η hη t (hFresh t ht) (hInt t (hSub ht))).trans_eq
        (congrArg (fun x : ℝ ↦ η*x) (loss_expectation μ g hg I hI η t (hCurrent t (hSub ht)) (hInt t (hSub ht))))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSub (fun t _ _ ↦ mul_nonneg hη
      (integral_nonneg (fun ω ↦ (randomWeights η g t ω).mean_nonneg (fun i ↦ (g t ω i).coe_nonneg))))

end
end Tournament.Upper.ShrinkingDartboard

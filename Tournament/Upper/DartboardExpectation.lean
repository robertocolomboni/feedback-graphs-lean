module

public import Tournament.Upper.DartboardConditionalMarginals
public import Tournament.Probability.FiniteSelection

@[expose] public section

namespace Tournament.Upper.ShrinkingDartboard

open MeasureTheory ProbabilityTheory Filter
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

def randomWeights (η : ℝ) (g : ℕ → Ω → LossVector ι) (n : ℕ) (ω : Ω) : ProbabilityVector ι :=
  weights η (fun t i ↦ (g t ω i : ℝ)) n

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem randomWeights_measurable (η : ℝ) (g : ℕ → Ω → LossVector ι)
    (hg : ∀ n, Measurable (g n)) (n : ℕ) (i : ι) :
    Measurable (fun ω ↦ randomWeights η g n ω i) :=
  weights_measurable η (fun ω t i ↦ (g t ω i : ℝ))
    (fun t j ↦ measurable_coe_nnreal_real.comp ((measurable_pi_apply j).comp (hg t))) n i

theorem loss_expectation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (n : ℕ)
    (hCurrent : HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ)
    (hInt : ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ) :
    (∫ ω, (g n ω (I n ω) : ℝ) ∂μ)=
      ∫ ω, (randomWeights η g n ω).mean (fun i ↦ (g n ω i : ℝ)) ∂μ := by
  have h := Tournament.Probability.conditional_finite_mean μ (lossHistory g (n+1))
    (lossHistory_measurable g hg (n+1)) (I n) (hI n)
    (fun h ↦ historyWeights η n (Fin.init h)) (previousWeights_measurable η n) hCurrent
    (fun h i ↦ (h (Fin.last n) i : ℝ)) (lastLoss_measurable n) hInt
  simpa only [init_lossHistory,last_lossHistory,historyWeights_eq_weights,randomWeights] using h

def quadraticTotal (η : ℝ) (g : ℕ → Ω → LossVector ι) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T, (randomWeights η g t ω).squareNorm (fun i ↦ (g t ω i : ℝ))

omit [MeasurableSpace Ω] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem quadraticTotal_nonneg (η : ℝ) (g : ℕ → Ω → LossVector ι) (T : ℕ) (ω : Ω) :
    0≤quadraticTotal η g T ω := Finset.sum_nonneg (fun _ _ ↦ ProbabilityVector.squareNorm_nonneg _ _)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem quadraticTotal_measurable (η : ℝ) (g : ℕ → Ω → LossVector ι)
    (hg : ∀ n, Measurable (g n)) (T : ℕ) : Measurable (quadraticTotal η g T) := by
  apply Finset.measurable_sum
  intro t _
  apply Finset.measurable_sum
  intro i _
  exact (randomWeights_measurable η g hg t i).mul
    ((measurable_coe_nnreal_real.comp ((measurable_pi_apply i).comp (hg t))).pow_const 2)

theorem expected_second_order_finite (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0<η) (T : ℕ)
    (hCurrent : ∀ n ∈ Finset.range T, HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ)
    (hInt : ∀ n ∈ Finset.range T, ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ)
    (hQuad : Integrable (quadraticTotal η g T) μ) (i : ι) :
    (∫ ω, ∑ t ∈ Finset.range T, (g t ω (I t ω) : ℝ) ∂μ)-
        (∫ ω, ∑ t ∈ Finset.range T, (g t ω i : ℝ) ∂μ)≤
      Real.log (Fintype.card ι:ℝ)/η+(η/2)*(∫ ω, quadraticTotal η g T ω ∂μ) := by
  have hMean (t : ℕ) (ht : t ∈ Finset.range T) :
      Integrable (fun ω ↦ (randomWeights η g t ω).mean (fun j ↦ (g t ω j : ℝ))) μ :=
    Tournament.Probability.integrable_finite_mean μ (randomWeights η g t)
      (randomWeights_measurable η g hg t) (fun ω j ↦ (g t ω j : ℝ)) (hInt t ht)
  have hSelected (t : ℕ) (ht : t ∈ Finset.range T) :
      Integrable (fun ω ↦ (g t ω (I t ω) : ℝ)) μ :=
    Tournament.Probability.integrable_finite_selection μ (fun ω j ↦ (g t ω j : ℝ)) (hInt t ht) (I t) (hI t)
  have hPair (t : ℕ) (ht : t ∈ Finset.range T) :
      Integrable (fun ω ↦ (randomWeights η g t ω).mean (fun j ↦ (g t ω j : ℝ))-(g t ω i : ℝ)) μ :=
    (hMean t ht).sub (hInt t ht i)
  have hPot : ∀ᵐ ω ∂μ, (∑ t ∈ Finset.range T,
      ((randomWeights η g t ω).mean (fun j ↦ (g t ω j : ℝ))-(g t ω i : ℝ)))≤
      Real.log (Fintype.card ι:ℝ)/η+(η/2)*quadraticTotal η g T ω :=
    Eventually.of_forall (fun ω ↦ nonnegative_second_order η hη (fun t j ↦ (g t ω j : ℝ)) T
      (fun t _ j ↦ (g t ω j).coe_nonneg) i)
  have hBound := integral_mono_ae (integrable_finsetSum _ hPair)
    ((integrable_const _).add (hQuad.const_mul (η/2))) hPot
  simp only [Pi.add_apply] at hBound
  rw [integral_finsetSum _ hPair,integral_add (integrable_const _) (hQuad.const_mul (η/2)),
    integral_const_mul] at hBound
  simp only [integral_const,probReal_univ,one_smul] at hBound
  rw [integral_finsetSum _ hSelected,integral_finsetSum _ (fun t ht ↦ hInt t ht i),← Finset.sum_sub_distrib]
  calc
    _ = ∑ t ∈ Finset.range T, ∫ ω,
        ((randomWeights η g t ω).mean (fun j ↦ (g t ω j : ℝ))-(g t ω i : ℝ)) ∂μ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [integral_sub (hMean t ht) (hInt t ht i),loss_expectation μ g hg I hI η t (hCurrent t ht) (hInt t ht)]
    _ ≤ _ := hBound

theorem expected_second_order (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ℕ → Ω → LossVector ι) (hg : ∀ n, Measurable (g n))
    (I : ℕ → Ω → ι) (hI : ∀ n, Measurable (I n)) (η : ℝ) (hη : 0<η) (T : ℕ)
    (hCurrent : ∀ n ∈ Finset.range T, HasCondDistrib (I n) (lossHistory g (n+1)) (previousWeightKernel η n) μ)
    (hInt : ∀ n ∈ Finset.range T, ∀ i, Integrable (fun ω ↦ (g n ω i : ℝ)) μ) (i : ι) :
    ENNReal.ofReal ((∫ ω, ∑ t ∈ Finset.range T, (g t ω (I t ω) : ℝ) ∂μ)-
      (∫ ω, ∑ t ∈ Finset.range T, (g t ω i : ℝ) ∂μ))≤
      ENNReal.ofReal (Real.log (Fintype.card ι:ℝ)/η)+ENNReal.ofReal (η/2)*
        (∫⁻ ω, ENNReal.ofReal (quadraticTotal η g T ω) ∂μ) := by
  by_cases hInfinite : (∫⁻ ω, ENNReal.ofReal (quadraticTotal η g T ω) ∂μ)=∞
  · simp [hInfinite,ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0<η/2))]
  · have hQuad : Integrable (quadraticTotal η g T) μ :=
      ⟨(quadraticTotal_measurable η g hg T).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (quadraticTotal_nonneg η g T))).mpr
          (lt_top_iff_ne_top.mpr hInfinite)⟩
    have h := ENNReal.ofReal_le_ofReal (expected_second_order_finite μ g hg I hI η hη T hCurrent hInt hQuad i)
    have hc : 0≤Real.log (Fintype.card ι:ℝ)/η :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))) hη.le
    have hq : 0≤∫ ω, quadraticTotal η g T ω ∂μ := integral_nonneg (quadraticTotal_nonneg η g T)
    rw [ENNReal.ofReal_add hc (mul_nonneg (by linarith) hq),ENNReal.ofReal_mul (by linarith : 0≤η/2),
      ofReal_integral_eq_lintegral_ofReal hQuad (Eventually.of_forall (quadraticTotal_nonneg η g T))] at h
    exact h

end
end Tournament.Upper.ShrinkingDartboard

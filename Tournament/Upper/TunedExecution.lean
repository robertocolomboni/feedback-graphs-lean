module

public import Tournament.Upper.SteeringFeedbackPolicy
public import Tournament.Upper.Tuning

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess Model ExponentialWeights BlockParameters Tuning

noncomputable section
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem tuned_small_target (A : SteeringParameters ι)
    (hm : A.m=exponent (target (Fintype.card ι) A.T))
    (hr : target (Fintype.card ι) A.T≤1/32)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) :
    let P := A.feedbackPolicy.algorithm A.tournament A.schedule loss
    (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x)
      ∂(P.execution A.blockCount).toMeasure)≤
        (2:ℝ)^40*min (A.T:ℝ) (performanceScale (Fintype.card ι) A.T) ∧
      (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ)
        ∂(P.execution A.blockCount).toMeasure)≤
          (2:ℝ)^40*min (A.T:ℝ) (performanceScale (Fintype.card ι) A.T) := by
  let P := A.feedbackPolicy.algorithm A.tournament A.schedule loss
  let μ := (P.execution A.blockCount).toMeasure
  let q := performanceScale (Fintype.card ι) A.T
  have hq : 4<q := performanceScale_gt_four A.card_ge_two A.time_ge_two
  have hκ : 1/(A.T:ℝ)≤DyadicRate.base A.m := by
    rw [hm]
    exact (tuned_parameters A.card_ge_two A.time_ge_two hr).2.2.2.1
  have hf := A.feedback_fixed_rate loss hloss default hκ
  have hc : (2:ℝ)^25*threshold (Fintype.card ι) A.T*(A.m:ℝ)*logScale (Fintype.card ι) A.T*
      Real.log (Fintype.card ι:ℝ)/DyadicRate.base A.m≤(2:ℝ)^26*2000*q := by
    rw [hm]
    exact tuned_comparison_term A.card_ge_two A.time_ge_two hr
  have hμ : meanRate A.m*(A.T:ℝ)≤4*q := by
    rw [hm]
    exact tuned_meanRate A.card_ge_two A.time_ge_two hr
  have hRscale : (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x) ∂μ)≤(2:ℝ)^40*q := by
    norm_num at hc ⊢
    linarith [hf.1]
  have hSscale : (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ) ∂μ)≤(2:ℝ)^40*q := by
    norm_num
    linarith [hf.2]
  have hRtime : (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x) ∂μ)≤2*(A.T:ℝ) := by
    have hp (x : History (fun b ↦ DyadicBlockOutcome ι A.m (A.schedule b)) A.blockCount) :
        pathRegret A.T loss (A.actions A.schedule default A.blockCount x)≤2*(A.T:ℝ) :=
      le_trans (le_abs_self _) (pathRegret_norm_le A.T loss hloss _)
    have h := integral_mono_ae (Integrable.of_finite (μ := μ)
      (f := fun x ↦ pathRegret A.T loss (A.actions A.schedule default A.blockCount x)))
      (integrable_const (μ := μ) (2*(A.T:ℝ))) (Eventually.of_forall hp)
    simpa only [integral_const,probReal_univ,one_smul] using h
  have hStime : (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ) ∂μ)≤(A.T:ℝ) := by
    have hp (x : History (fun b ↦ DyadicBlockOutcome ι A.m (A.schedule b)) A.blockCount) :
        (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ)≤(A.T:ℝ) := by
      exact_mod_cast le_trans (switchCount_le _ _) (Nat.sub_le A.T 1)
    have h := integral_mono_ae (Integrable.of_finite (μ := μ)
      (f := fun x ↦ (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ)))
      (integrable_const (μ := μ) (A.T:ℝ)) (Eventually.of_forall hp)
    simpa only [integral_const,probReal_univ,one_smul] using h
  have hT : (0:ℝ)≤(A.T:ℝ) := by positivity
  change (∫ x, pathRegret A.T loss (A.actions A.schedule default A.blockCount x) ∂μ)≤
      (2:ℝ)^40*min (A.T:ℝ) q ∧
    (∫ x, (switchCount A.T (A.actions A.schedule default A.blockCount x):ℝ) ∂μ)≤
      (2:ℝ)^40*min (A.T:ℝ) q
  rw [mul_min_of_nonneg (A.T:ℝ) q (by norm_num : (0:ℝ)≤2^40)]
  constructor
  · exact le_min (by norm_num; linarith) hRscale
  · exact le_min (by norm_num; linarith) hSscale

end
end Tournament.Upper.SteeringParameters

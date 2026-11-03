module

public import Tournament.Upper.OneRoundEndpoint
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace Tournament.ProbabilityVector

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def minimumWeight (v : ProbabilityVector ι) : ℝ := by
  haveI : Nonempty ι := v.nonempty
  exact Finset.univ.inf' Finset.univ_nonempty (fun i ↦ v i)

theorem minimumWeight_le (v : ProbabilityVector ι) (i : ι) : v.minimumWeight≤v i := by
  have : Nonempty ι := v.nonempty
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem minimumWeight_pos (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) : 0<v.minimumWeight := by
  have : Nonempty ι := v.nonempty
  exact (Finset.lt_inf'_iff _).mpr (fun i _ ↦ hv i)

def anchorLog (v : ProbabilityVector ι) : ℝ := Real.log (Real.exp 1/v.minimumWeight)

theorem anchorLog_ge_one (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) : 1≤v.anchorLog := by
  have : Nonempty ι := v.nonempty
  let i : ι := Classical.arbitrary ι
  have hmin := v.minimumWeight_pos hv
  have hmin1 : v.minimumWeight≤1 := le_trans (v.minimumWeight_le i) (v.weight_le_one i)
  unfold anchorLog
  rw [Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hmin),Real.log_exp]
  have hlog := Real.log_nonpos (le_of_lt hmin) hmin1
  linarith

end
end Tournament.ProbabilityVector

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

structure BalancedEstimator (F : ι → ι → Prop) (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (Ψ : ι → ι → ι → ℝ) (L₀ : ℝ) : Prop where
  observable : ScoreRule.EstimatorObservable F Ψ
  kills_constants : EstimatorKillsConstants Ψ
  calibration : EstimatorCalibration Ψ H.sampling w
  endpoints : EstimatorEndpointBounds H w Ψ L₀
  size : ∀ s f, BoundedLoss f → ∀ i, |applyEstimator Ψ s f i|≤L₀*H.ratio s

namespace ComparisonAssignment

variable {F : ι → ι → Prop} {v : ProbabilityVector ι}

theorem prepared_estimator_balanced (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (hhalf : ∀ i, w i/2≤v i) (htwo : ∀ i, v i≤2*w i)
    (hweight : A.totalWeight≤3*v.anchorLog) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) :
    let H := A.preparedFamily w hw κ hκ hκ32
    BalancedEstimator F H w (A.estimator w H.sampling) (128*v.anchorLog) := by
  dsimp only
  let H := A.preparedFamily w hw κ hκ hκ32
  have hΛ := v.anchorLog_ge_one A.anchor_pos
  have hΛ0 : 0≤v.anchorLog := by linarith
  have hwv : ∀ i, w i≤2*v i := fun i ↦ by linarith [hhalf i]
  refine ⟨A.estimator_observable w H.sampling,A.estimator_kills_constants w H.sampling,
    A.estimator_calibration w H.sampling H.sampling_pos,?_,?_⟩
  · intro f
    have hp := A.persistence_bound w hw hwv htwo κ hκ hκ32 f
    have ho := A.one_round_bound w hw hwv htwo κ hκ hκ32 f
    have hcp : (288/7)*A.totalWeight≤128*v.anchorLog := by nlinarith
    have hco : (2048/49)*A.totalWeight≤128*v.anchorLog := by nlinarith
    constructor
    · exact le_trans hp (mul_le_mul_of_nonneg_right hcp (H.sampling.variance_nonneg f))
    · exact le_trans ho (mul_le_mul_of_nonneg_right hco (H.refresh.variance_nonneg f))
  · intro s f hf i
    have hs := A.prepared_estimator_size w hw κ hκ hκ32 s f hf i
    have hc : 4*A.totalWeight≤128*v.anchorLog := by nlinarith
    exact le_trans hs (mul_le_mul_of_nonneg_right hc (le_of_lt (H.ratio_pos s)))

theorem balanced_estimator_from_assignment (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (hhalf : ∀ i, w i/2≤v i) (htwo : ∀ i, v i≤2*w i)
    (hweight : A.totalWeight≤3*v.anchorLog) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) :
    let H := A.preparedFamily w hw κ hκ hκ32
    κ*H.maxRatio<1/4 ∧ (∀ i, w i≤(8/7)*H.sampling i) ∧
      (∑ i, |H.sampling i-w i|)≤8*κ ∧ 1≤128*v.anchorLog ∧
        BalancedEstimator F H w (A.estimator w H.sampling) (128*v.anchorLog) := by
  refine ⟨A.preparedFamily_maxRatio w hw κ hκ hκ32,A.preparedFamily_weight_domination w hw κ hκ hκ32,
    A.preparedFamily_distance w hw κ hκ hκ32,?_,A.prepared_estimator_balanced w hw hhalf htwo hweight κ hκ hκ32⟩
  have hΛ := v.anchorLog_ge_one A.anchor_pos
  linarith

end ComparisonAssignment
end
end Tournament.Upper

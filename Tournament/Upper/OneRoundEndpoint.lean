module

public import Tournament.Upper.PreparedMoments

@[expose] public section

namespace Tournament.Upper.ComparisonAssignment

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι] {F : ι → ι → Prop} {v : ProbabilityVector ι}

theorem one_round_bound (A : ComparisonAssignment F v) (w : ProbabilityVector ι) (hw : ∀ i, 0<w i)
    (hwv : ∀ i, w i≤2*v i) (hvw : ∀ i, v i≤2*w i)
    (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (f : ι → ℝ) :
    let H := A.preparedFamily w hw κ hκ hκ32
    (∑ s, H.sampling s*w.squareNorm (estimationError (A.estimator w H.sampling) w s f))≤
      (2048/49)*A.totalWeight*H.refresh.variance f := by
  dsimp only
  let H := A.preparedFamily w hw κ hκ hκ32
  let Ψ := A.estimator w H.sampling
  have hcal := A.estimator_calibration w H.sampling H.sampling_pos
  have hmean : ∀ i, H.sampling.mean (fun s ↦ applyEstimator Ψ s f i)=w.center f i :=
    fun i ↦ calibrated_mean Ψ H.sampling w hcal f i
  have hidentity := H.sampling.mean_squareNorm_centered w (fun s ↦ applyEstimator Ψ s f) (w.center f) hmean
  have hvariance : (∑ s, H.sampling s*w.squareNorm (estimationError Ψ w s f))≤
      ∑ s, H.sampling s*w.squareNorm (applyEstimator Ψ s f) := by
    change H.sampling.mean (fun s ↦ w.squareNorm (fun i ↦ applyEstimator Ψ s f i-w.center f i))≤_
    rw [hidentity]
    have hn := w.squareNorm_nonneg (w.center f)
    change H.sampling.mean (fun s ↦ w.squareNorm (applyEstimator Ψ s f))-w.squareNorm (w.center f)≤
      H.sampling.mean (fun s ↦ w.squareNorm (applyEstimator Ψ s f))
    linarith
  have hraw : (∑ s, H.sampling s*w.squareNorm (applyEstimator Ψ s f))=
      ∑ s, w.squareNorm (w.center (A.act s f))/H.sampling s := by
    apply Finset.sum_congr rfl
    intro s _
    rw [A.estimator_norm]
    field_simp [ne_of_gt (H.sampling_pos s)]
  have hterm : ∀ s, w.squareNorm (w.center (A.act s f))/H.sampling s≤
      (32/7)*(v.squareNorm (A.act s f)/v s) := by
    intro s
    have hp := H.sampling_pos s
    have hv := A.anchor_pos s
    have hF := A.centered_act_norm_le w hwv s f
    have hN := v.squareNorm_nonneg (A.act s f)
    have hpv : (7/16)*v s≤H.sampling s := by
      have hbase := A.preparedSampling_ge_weight w κ hκ hκ32 s
      change (7/8)*w s≤H.sampling s at hbase
      linarith [hvw s]
    rw [show (32/7)*(v.squareNorm (A.act s f)/v s)=((32/7)*v.squareNorm (A.act s f))/v s by ring]
    apply (div_le_div_iff₀ hp hv).mpr
    have hmul := mul_le_mul_of_nonneg_right hF (le_of_lt hv)
    have hmul' := mul_le_mul_of_nonneg_left hpv hN
    nlinarith
  have hmid : ∀ i, (v.midpoint A.sourceLaw) i≤(16/7)*H.refresh i := by
    intro i
    have hwp := A.preparedFamily_weight_domination w hw κ hκ hκ32 i
    change w i≤(8/7)*H.sampling i at hwp
    have hvp : v i≤(16/7)*H.sampling i := by linarith [hvw i]
    have hq := A.sourceLaw.nonneg i
    change (v i+A.sourceLaw i)/2≤(16/7)*((H.sampling i+A.sourceLaw i)/2)
    linarith
  have hvar := (v.midpoint A.sourceLaw).variance_le_mul_variance H.refresh f (16/7) (by norm_num) hmid
  have hsecond := A.second_assignment_moment f
  calc
    _ ≤ _ := hvariance
    _ = _ := hraw
    _ ≤ (32/7)*(∑ s, v.squareNorm (A.act s f)/v s) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun s _ ↦ hterm s)
    _ ≤ (128/7)*A.totalWeight*(v.midpoint A.sourceLaw).variance f := by nlinarith
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hvar (show 0≤(128/7)*A.totalWeight by have := A.totalWeight_pos; positivity)
      calc
        _ ≤ (128/7)*A.totalWeight*((16/7)*H.refresh.variance f) := hm
        _ = _ := by ring

end
end Tournament.Upper.ComparisonAssignment

module

public import Tournament.Upper.AssignmentEstimator

@[expose] public section

namespace Tournament.ProbabilityVector

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι]

theorem squareNorm_center_le (w : ProbabilityVector ι) (f : ι → ℝ) :
    w.squareNorm (w.center f)≤w.squareNorm f := by
  change w.variance f≤_
  simpa only [sub_zero,squareNorm] using w.variance_le_sum_sq_sub f 0

theorem squareNorm_domination (w v : ProbabilityVector ι) (c : ℝ)
    (hwv : ∀ i, w i≤c*v i) (f : ι → ℝ) : w.squareNorm f≤c*v.squareNorm f := by
  unfold squareNorm
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ by
    have hm := mul_le_mul_of_nonneg_right (hwv i) (sq_nonneg (f i))
    convert hm using 1
    ring)

theorem squareNorm_sub_le_two (w : ProbabilityVector ι) (f g : ι → ℝ) :
    w.squareNorm (fun i ↦ f i-g i)≤2*w.squareNorm f+2*w.squareNorm g := by
  unfold squareNorm
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ ↦ by
    have hm := mul_nonneg (w.nonneg i) (sq_nonneg (f i+g i))
    nlinarith)

end Tournament.ProbabilityVector

namespace Tournament.Upper.ComparisonAssignment

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι] {F : ι → ι → Prop} {v : ProbabilityVector ι}

theorem centered_act_norm_le (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hwv : ∀ i, w i≤2*v i) (s : ι) (f : ι → ℝ) :
    w.squareNorm (w.center (A.act s f))≤2*v.squareNorm (A.act s f) :=
  le_trans (w.squareNorm_center_le _) (w.squareNorm_domination v 2 hwv _)

theorem estimator_norm (A : ComparisonAssignment F v) (w p : ProbabilityVector ι) (s : ι) (f : ι → ℝ) :
    w.squareNorm (applyEstimator (A.estimator w p) s f)=w.squareNorm (w.center (A.act s f))/(p s)^2 := by
  have hfun : applyEstimator (A.estimator w p) s f=(fun i ↦ w.center (A.act s f) i/p s) :=
    funext (A.estimator_apply w p s f)
  rw [hfun,w.squareNorm_div]

theorem error_norm_le_two (A : ComparisonAssignment F v) (w p : ProbabilityVector ι) (s : ι) (f : ι → ℝ) :
    w.squareNorm (estimationError (A.estimator w p) w s f)≤
      2*(w.squareNorm (w.center (A.act s f))/(p s)^2)+2*w.variance f := by
  have hb := w.squareNorm_sub_le_two (applyEstimator (A.estimator w p) s f) (w.center f)
  rw [A.estimator_norm] at hb
  exact hb

theorem persistence_term (A : ComparisonAssignment F v) (w : ProbabilityVector ι) (hw : ∀ i, 0<w i)
    (hwv : ∀ i, w i≤2*v i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (s : ι) (f : ι → ℝ) :
    let H := A.preparedFamily w hw κ hκ hκ32
    (H.sampling s/H.ratio s)*w.squareNorm (estimationError (A.estimator w H.sampling) w s f)≤
      8*(v.squareNorm (A.act s f)/A.sourceLaw s)+4*H.sampling s*w.variance f := by
  dsimp only
  let H := A.preparedFamily w hw κ hκ hκ32
  have hp := H.sampling_pos s
  have hx := H.refresh_pos s
  have hq := A.sourceLaw_pos s
  have hF := A.centered_act_norm_le w hwv s f
  have hV := v.squareNorm_nonneg (A.act s f)
  have hvar := w.variance_nonneg f
  have hxp := H.refresh_ge_half s
  have hxq := A.preparedFamily_refresh_ge_source w hw κ hκ hκ32 s
  change A.sourceLaw s/2≤H.refresh s at hxq
  have hratio : H.sampling s/H.ratio s=(H.sampling s)^2/H.refresh s := by
    unfold HoldingFamily.ratio
    field_simp [ne_of_gt hp,ne_of_gt hx]
  have hsplit := mul_le_mul_of_nonneg_left (A.error_norm_le_two w H.sampling s f)
    (div_nonneg (le_of_lt hp) (le_of_lt (H.ratio_pos s)))
  rw [hratio] at hsplit
  have hdiag : (H.sampling s)^2/H.refresh s≤2*H.sampling s := by
    apply (div_le_iff₀ hx).mpr
    have hm := mul_le_mul_of_nonneg_left hxp (le_of_lt hp)
    nlinarith
  have hmain : 2*w.squareNorm (w.center (A.act s f))/H.refresh s≤
      8*(v.squareNorm (A.act s f)/A.sourceLaw s) := by
    rw [show 8*(v.squareNorm (A.act s f)/A.sourceLaw s)=(8*v.squareNorm (A.act s f))/A.sourceLaw s by ring]
    apply (div_le_div_iff₀ hx hq).mpr
    have hmul := mul_le_mul_of_nonneg_right hF (le_of_lt hq)
    have hmul' := mul_le_mul_of_nonneg_left hxq hV
    nlinarith
  calc
    _ = ((H.sampling s)^2/H.refresh s)*w.squareNorm (estimationError (A.estimator w H.sampling) w s f) := by rw [hratio]
    _ ≤ ((H.sampling s)^2/H.refresh s)*(2*(w.squareNorm (w.center (A.act s f))/(H.sampling s)^2)+2*w.variance f) := hsplit
    _ = 2*w.squareNorm (w.center (A.act s f))/H.refresh s+
        2*((H.sampling s)^2/H.refresh s)*w.variance f := by field_simp [ne_of_gt hp]
    _ ≤ 8*(v.squareNorm (A.act s f)/A.sourceLaw s)+4*H.sampling s*w.variance f :=
      add_le_add hmain (by nlinarith [mul_le_mul_of_nonneg_right hdiag hvar])

theorem persistence_bound (A : ComparisonAssignment F v) (w : ProbabilityVector ι) (hw : ∀ i, 0<w i)
    (hwv : ∀ i, w i≤2*v i) (hvw : ∀ i, v i≤2*w i)
    (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (f : ι → ℝ) :
    let H := A.preparedFamily w hw κ hκ hκ32
    (∑ s, (H.sampling s/H.ratio s)*w.squareNorm (estimationError (A.estimator w H.sampling) w s f))≤
      (288/7)*A.totalWeight*H.sampling.variance f := by
  dsimp only
  let H := A.preparedFamily w hw κ hκ hκ32
  have hfirst := A.first_assignment_moment f
  have hvar := w.variance_nonneg f
  have hvw := v.variance_le_mul_variance w f 2 (by norm_num) hvw
  have hwp := w.variance_le_mul_variance H.sampling f (8/7) (by norm_num)
    (A.preparedFamily_weight_domination w hw κ hκ hκ32)
  have hR := A.totalWeight_ge_one
  calc
    _ ≤ ∑ s, (8*(v.squareNorm (A.act s f)/A.sourceLaw s)+4*H.sampling s*w.variance f) :=
      Finset.sum_le_sum (fun s _ ↦ A.persistence_term w hw hwv κ hκ hκ32 s f)
    _ = 8*(∑ s, v.squareNorm (A.act s f)/A.sourceLaw s)+4*w.variance f := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,← Finset.mul_sum,H.sampling.sum_eq_one]
      ring
    _ ≤ 16*A.totalWeight*v.variance f+4*w.variance f := by nlinarith
    _ ≤ 36*A.totalWeight*w.variance f := by
      have hm := mul_le_mul_of_nonneg_left hvw (show 0≤16*A.totalWeight by have := A.totalWeight_pos; positivity)
      have hm' := mul_le_mul_of_nonneg_right hR hvar
      nlinarith
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hwp (show 0≤36*A.totalWeight by have := A.totalWeight_pos; positivity)
      calc
        _ ≤ 36*A.totalWeight*((8/7)*H.sampling.variance f) := hm
        _ = _ := by ring

end
end Tournament.Upper.ComparisonAssignment

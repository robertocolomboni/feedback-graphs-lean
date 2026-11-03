module

public import Tournament.Upper.PreparedFamily
public import Tournament.Upper.ChunkPolicy

@[expose] public section

namespace Tournament.Upper.ComparisonAssignment

open scoped BigOperators Classical
open Model

noncomputable section

variable {ι : Type*} [Fintype ι] {F : ι → ι → Prop} {v : ProbabilityVector ι}

def estimator (A : ComparisonAssignment F v) (w p : ProbabilityVector ι) (s i r : ι) : ℝ :=
  (A.matrix s i r-w.mean (fun k ↦ A.matrix s k r))/p s

theorem estimator_apply (A : ComparisonAssignment F v) (w p : ProbabilityVector ι) (s : ι) (f : ι → ℝ) (i : ι) :
    applyEstimator (A.estimator w p) s f i=w.center (A.act s f) i/p s := by
  have hmean : (∑ r, w.mean (fun k ↦ A.matrix s k r)*f r)=w.mean (A.act s f) := by
    unfold ProbabilityVector.mean act applyEstimator
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact Finset.sum_congr rfl (fun r _ ↦ by ring)
  unfold applyEstimator estimator
  simp only [div_mul_eq_mul_div,← Finset.sum_div,sub_mul,Finset.sum_sub_distrib]
  rw [hmean]
  rfl

theorem estimator_calibration (A : ComparisonAssignment F v) (w p : ProbabilityVector ι)
    (hp : ∀ s, 0<p s) : EstimatorCalibration (A.estimator w p) p w := by
  intro i r
  have hcancel : ∀ s, p s*A.estimator w p s i r=A.matrix s i r-w.mean (fun k ↦ A.matrix s k r) := by
    intro s
    unfold estimator
    field_simp [ne_of_gt (hp s)]
  have hcol : (∑ s, w.mean (fun k ↦ A.matrix s k r))=w r-v r := by
    unfold ProbabilityVector.mean
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,A.total_matrix]
    simp [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,w.sum_eq_one]
  simp_rw [hcancel]
  rw [Finset.sum_sub_distrib,A.total_matrix,hcol]
  ring

theorem estimator_kills_constants (A : ComparisonAssignment F v) (w p : ProbabilityVector ι) :
    EstimatorKillsConstants (A.estimator w p) := by
  intro s i
  have hmean : (∑ r, w.mean (fun k ↦ A.matrix s k r))=0 := by
    unfold ProbabilityVector.mean
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,A.row_sum,mul_zero]
    exact Finset.sum_const_zero
  unfold estimator
  rw [← Finset.sum_div,Finset.sum_sub_distrib,A.row_sum,hmean,sub_self,zero_div]

omit [Fintype ι] in
theorem observation_of_closed (s : ι) (f : ι → ℝ) (i : ι) (hi : InClosedNeighborhood F s i) :
    comparisonObservation F s f i=f s-f i := by
  rcases hi with rfl | hi
  · simp [comparisonObservation]
  · simp only [comparisonObservation,ite_eq_left hi]

def comparisonDecoder (A : ComparisonAssignment F v) (s : ι) (obs : ι → ℝ) (i : ι) : ℝ :=
  ∑ r, A.edgeWeight s i r*(obs r-obs i)

theorem comparisonDecoder_eq (A : ComparisonAssignment F v) (s : ι) (f : ι → ℝ) (i : ι) :
    A.comparisonDecoder s (comparisonObservation F s f) i=A.act s f i := by
  rw [A.comparison_form]
  unfold comparisonDecoder
  apply Finset.sum_congr rfl
  intro r _
  by_cases hs : InClosedNeighborhood F s i ∧ InClosedNeighborhood F s r
  · rw [observation_of_closed s f i hs.1,observation_of_closed s f r hs.2]
    ring
  · have hz : A.edgeWeight s i r=0 := by simp only [edgeWeight,A.support s i r hs,neg_zero,ite_self]
    rw [hz,zero_mul,zero_mul]

theorem estimator_observable (A : ComparisonAssignment F v) (w p : ProbabilityVector ι) :
    ScoreRule.EstimatorObservable F (A.estimator w p) := by
  refine ⟨fun s obs i ↦ w.center (A.comparisonDecoder s obs) i/p s,?_⟩
  intro f _ s i
  rw [A.estimator_apply]
  have hdecode : A.comparisonDecoder s (comparisonObservation F s f)=A.act s f :=
    funext (fun k ↦ A.comparisonDecoder_eq s f k)
  change w.center (A.act s f) i/p s=w.center (A.comparisonDecoder s (comparisonObservation F s f)) i/p s
  rw [hdecode]

theorem centered_act_abs_le (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (s : ι) (f : ι → ℝ) (hf : BoundedLoss f) (i : ι) :
    |w.center (A.act s f) i|≤2*A.sourceWeight s := by
  have hbound : ∀ k, |A.act s f k|≤A.sourceWeight s :=
    fun k ↦ le_trans (A.act_abs_le_diagonal s f hf k) (A.load_le_source s k)
  have hmean : |w.mean (A.act s f)|≤A.sourceWeight s := by
    calc
      _ ≤ w.mean (fun k ↦ |A.act s f k|) := w.abs_mean_le _
      _ ≤ w.mean (fun _ ↦ A.sourceWeight s) := w.mean_mono hbound
      _ = _ := w.mean_const _
  change |A.act s f i-w.mean (A.act s f)|≤_
  have habs := abs_sub_le (A.act s f i) 0 (w.mean (A.act s f))
  simp only [sub_zero,zero_sub,abs_neg] at habs
  linarith [hbound i]

theorem prepared_estimator_size (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32)
    (s : ι) (f : ι → ℝ) (hf : BoundedLoss f) (i : ι) :
    |applyEstimator (A.estimator w (A.preparedFamily w hw κ hκ hκ32).sampling) s f i|≤
      4*A.totalWeight*(A.preparedFamily w hw κ hκ hκ32).ratio s := by
  let H := A.preparedFamily w hw κ hκ hκ32
  have hp := H.sampling_pos s
  rw [A.estimator_apply,abs_div,abs_of_pos hp]
  calc
    _ ≤ (2*A.sourceWeight s)/H.sampling s :=
      div_le_div_of_nonneg_right (A.centered_act_abs_le w s f hf i) (le_of_lt hp)
    _ ≤ 4*A.totalWeight*H.ratio s := by
      apply (div_le_iff₀ hp).mpr
      have he := congrArg (fun z : ℝ ↦ 4*A.totalWeight*z) (H.weighted_ratio s)
      have hq : A.sourceLaw s≤2*H.refresh s := by
        have hx := A.preparedFamily_refresh_ge_source w hw κ hκ hκ32 s
        change A.sourceLaw s/2≤H.refresh s at hx
        linarith
      have hm := mul_le_mul_of_nonneg_left hq (le_of_lt A.totalWeight_pos)
      rw [A.totalWeight_mul_sourceLaw] at hm
      nlinarith

end
end Tournament.Upper.ComparisonAssignment

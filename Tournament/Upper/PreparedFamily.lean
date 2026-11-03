module

public import Tournament.Upper.AssignmentMoments

@[expose] public section

namespace Tournament.Upper.ComparisonAssignment

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι] {F : ι → ι → Prop} {v : ProbabilityVector ι}

def preparedSampling (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) : ProbabilityVector ι where
  weight i := (1-4*κ)*w i+4*κ*A.sourceLaw i
  nonneg i := by
    have hw := w.nonneg i
    have hq := A.sourceLaw.nonneg i
    have hc : 0≤1-4*κ := by linarith
    positivity
  sum_eq_one := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,w.sum_eq_one,A.sourceLaw.sum_eq_one]
    ring

theorem preparedSampling_ge_weight (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (i : ι) :
    (7/8)*w i≤A.preparedSampling w κ hκ hκ32 i := by
  have hw := w.nonneg i
  have hq := A.sourceLaw.nonneg i
  have hm := mul_le_mul_of_nonneg_right (show (7/8:ℝ)≤1-4*κ by linarith) hw
  change (7/8)*w i≤(1-4*κ)*w i+4*κ*A.sourceLaw i
  nlinarith

theorem preparedSampling_ge_source (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (i : ι) :
    4*κ*A.sourceLaw i≤A.preparedSampling w κ hκ hκ32 i := by
  change _≤(1-4*κ)*w i+4*κ*A.sourceLaw i
  have hw := w.nonneg i
  have hc : 0≤1-4*κ := by linarith
  nlinarith

theorem preparedSampling_pos (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (i : ι) :
    0<A.preparedSampling w κ hκ hκ32 i :=
  lt_of_lt_of_le (mul_pos (by norm_num) (hw i)) (A.preparedSampling_ge_weight w κ hκ hκ32 i)

def preparedFamily (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) : HoldingFamily ι where
  sampling := A.preparedSampling w κ hκ hκ32
  refresh := (A.preparedSampling w κ hκ hκ32).midpoint A.sourceLaw
  sampling_pos := A.preparedSampling_pos w hw κ hκ hκ32
  refresh_pos i := by
    change 0<(A.preparedSampling w κ hκ hκ32 i+A.sourceLaw i)/2
    have hp := A.preparedSampling_pos w hw κ hκ hκ32 i
    have hq := A.sourceLaw_pos i
    positivity
  refresh_ge_half i := by
    change A.preparedSampling w κ hκ hκ32 i/2≤(A.preparedSampling w κ hκ hκ32 i+A.sourceLaw i)/2
    have hq := A.sourceLaw.nonneg i
    linarith

theorem preparedFamily_weight_domination (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (i : ι) :
    w i≤(8/7)*(A.preparedFamily w hw κ hκ hκ32).sampling i := by
  have hp := A.preparedSampling_ge_weight w κ hκ hκ32 i
  change w i≤(8/7)*A.preparedSampling w κ hκ hκ32 i
  linarith

theorem preparedFamily_refresh_ge_source (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (i : ι) :
    A.sourceLaw i/2≤(A.preparedFamily w hw κ hκ hκ32).refresh i := by
  change A.sourceLaw i/2≤(A.preparedSampling w κ hκ hκ32 i+A.sourceLaw i)/2
  have hp := (A.preparedSampling w κ hκ hκ32).nonneg i
  linarith

theorem preparedFamily_ratio_bound (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) (i : ι) :
    κ*(A.preparedFamily w hw κ hκ hκ32).ratio i≤κ/2+1/8 := by
  let H := A.preparedFamily w hw κ hκ hκ32
  have hpp := H.sampling_pos i
  have hp : 4*κ*A.sourceLaw i≤H.sampling i := A.preparedSampling_ge_source w κ hκ hκ32 i
  have hx : H.refresh i=(H.sampling i+A.sourceLaw i)/2 := rfl
  have he := congrArg (fun z : ℝ ↦ κ*z) (H.weighted_ratio i)
  rw [hx] at he
  have hmul : H.sampling i*(κ*H.ratio i)≤H.sampling i*(κ/2+1/8) := by nlinarith
  exact (mul_le_mul_iff_right₀ hpp).mp hmul

theorem preparedFamily_maxRatio (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) :
    κ*(A.preparedFamily w hw κ hκ hκ32).maxRatio<1/4 := by
  let H := A.preparedFamily w hw κ hκ hκ32
  have : Nonempty ι := v.nonempty
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty H.ratio
  have hmax : H.maxRatio=H.ratio i := hi
  change κ*H.maxRatio<1/4
  rw [hmax]
  have hb := A.preparedFamily_ratio_bound w hw κ hκ hκ32 i
  change κ*H.ratio i≤κ/2+1/8 at hb
  linarith

theorem preparedFamily_distance (A : ComparisonAssignment F v) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) :
    (∑ i, |(A.preparedFamily w hw κ hκ hκ32).sampling i-w i|)≤8*κ := by
  have hcoord : ∀ i, |(A.preparedFamily w hw κ hκ hκ32).sampling i-w i|=4*κ*|A.sourceLaw i-w i| := by
    intro i
    change |(1-4*κ)*w i+4*κ*A.sourceLaw i-w i|=4*κ*|A.sourceLaw i-w i|
    rw [show (1-4*κ)*w i+4*κ*A.sourceLaw i-w i=(4*κ)*(A.sourceLaw i-w i) by ring,
      abs_mul,abs_of_nonneg (by positivity : 0≤4*κ)]
  simp_rw [hcoord]
  calc
    _ ≤ ∑ i, 4*κ*(A.sourceLaw i+w i) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg (A.sourceLaw.nonneg i),abs_of_nonneg (w.nonneg i)] using
        abs_sub_le (A.sourceLaw i) 0 (w i)
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,A.sourceLaw.sum_eq_one,w.sum_eq_one]
      ring

end
end Tournament.Upper.ComparisonAssignment

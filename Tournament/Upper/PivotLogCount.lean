module

public import Tournament.Upper.PivotCount
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

namespace Tournament.Upper.RootedPivots

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem minimumWeight_le_one (v : ProbabilityVector ι) : v.minimumWeight≤1 := by
  have : Nonempty ι := v.nonempty
  let i : ι := Classical.arbitrary ι
  exact le_trans (v.minimumWeight_le i) (v.weight_le_one i)

theorem half_le_log_two : (1/2:ℝ)≤Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h
  exact h

def countThreshold (v : ProbabilityVector ι) : ℕ :=
  ⌈Real.log (1/v.minimumWeight)/Real.log 2⌉₊

theorem countThreshold_geometric (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    (1/2:ℝ)^(countThreshold v)≤v.minimumWeight := by
  have hmin := v.minimumWeight_pos hv
  have hlog : 0<Real.log 2 := lt_of_lt_of_le (by norm_num) half_le_log_two
  have hceil := Nat.le_ceil (Real.log (1/v.minimumWeight)/Real.log 2)
  have hlogs : Real.log (1/v.minimumWeight)≤Real.log ((2:ℝ)^countThreshold v) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ hlog).mp hceil
  have hpow : 1/v.minimumWeight≤(2:ℝ)^countThreshold v :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlogs
  have hmul := (div_le_iff₀ hmin).mp hpow
  rw [div_pow,one_pow]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2^countThreshold v)).mpr
  nlinarith

theorem countThreshold_add_two_le_log (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) :
    (countThreshold v:ℝ)+2≤3*v.anchorLog := by
  have hmin := v.minimumWeight_pos hv
  have hmin1 := minimumWeight_le_one v
  have hratio : (1:ℝ)≤1/v.minimumWeight := (le_div_iff₀ hmin).mpr (by linarith)
  have hl : 0≤Real.log (1/v.minimumWeight) := Real.log_nonneg hratio
  have hlog : 0<Real.log 2 := lt_of_lt_of_le (by norm_num) half_le_log_two
  have hceil := (Nat.ceil_lt_add_one (div_nonneg hl hlog.le)).le
  have hquot : Real.log (1/v.minimumWeight)/Real.log 2≤3*Real.log (1/v.minimumWeight) := by
    apply (div_le_iff₀ hlog).mpr
    have hm := mul_le_mul_of_nonneg_left half_le_log_two hl
    nlinarith
  have hanchor : v.anchorLog=1+Real.log (1/v.minimumWeight) := by
    unfold ProbabilityVector.anchorLog
    rw [Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hmin),Real.log_exp]
    rw [Real.log_div (by norm_num) (ne_of_gt hmin),Real.log_one]
    ring
  rw [hanchor]
  change (⌈Real.log (1/v.minimumWeight)/Real.log 2⌉₊:ℝ)+2≤_
  linarith

theorem expectedCount_le_log (F : ι → ι → Prop) (hF : IsTournament F)
    (v : ProbabilityVector ι) (hv : ∀ i, 0<v i) (n : ℕ) (U : Finset ι) :
    expectedCount F v hv n U≤3*v.anchorLog :=
  le_trans (expectedCount_le_threshold F hF v hv n (countThreshold v)
    (countThreshold_geometric v hv) U) (countThreshold_add_two_le_log v hv)

end
end Tournament.Upper.RootedPivots

module

public import Tournament.Probability.MarkovExponential
public import Tournament.Upper.OccupationPotentials
public import Tournament.Upper.ChunkTheorem

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open FinitePath Upper

variable {ι : Type*} [Fintype ι]

noncomputable section

theorem stationary_ratio_total_mean (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (n : ℕ) :
    (law (H.kernel τ hτ) H.sampling n).mean (stateTotal H.ratio n) = (n:ℝ)+1 := by
  unfold stateTotal
  rw [ProbabilityVector.mean_sum]
  calc
    _ = ∑ t ∈ Finset.range (n+1), (1:ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [stationary_stateAt_mean (H.kernel τ hτ) H.sampling (H.kernel_stationary hτ) n t
        (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) H.ratio, H.mean_ratio]
    _ = (n:ℝ)+1 := by simp

theorem reference_ratio_exponential_mean_le (H : HoldingFamily ι)
    {κ τ : ℝ} (hκ : 0 < κ) (hκmax : κ*H.maxRatio ≤ 1/4) (hκτ : κ ≤ τ)
    (h : ℕ) (hhκ : (h:ℝ)*κ ≤ 1/8) (n : ℕ) (hn : n+1 ≤ h) :
    (law (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling n).mean
      (fun hist ↦ Real.exp ((κ/12)*stateTotal H.ratio n hist)) ≤ 1+2*(κ/12)*((n:ℝ)+1) := by
  have hτ : 0 < τ := lt_of_lt_of_le hκ hκτ
  have hmax : H.maxRatio ≤ 1/(4*κ) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*κ)).mpr
    nlinarith
  have hbound : ∀ i, H.ratio i ≤ 1/(4*κ) :=
    fun i ↦ le_trans (H.ratio_le_maxRatio i) hmax
  have hfuture : ∀ k, k ≤ n → ∀ i, futureValue (H.kernel τ hτ) H.ratio k i ≤ 5/κ := by
    intro k hk i
    rw [futureValue_eq_occupation]
    exact H.expected_ratio_occupation_le ((H.kernel τ hτ).row i) hκ hκmax hκτ h hhκ k (by omega)
  have hprod : (κ/12)*(1/(4*κ)+5/κ) = 7/16 := by
    field_simp
    ring
  have hmgf := state_sum_exponential_mean_le (H.kernel τ hτ) H.sampling H.ratio
    (fun i ↦ le_of_lt (H.ratio_pos i)) n (1/(4*κ)) (5/κ) (by positivity) hbound hfuture
    (κ/12) (by positivity) (by rw [hprod]; norm_num)
  rw [H.stationary_ratio_total_mean hτ n, hprod] at hmgf
  calc
    _ ≤ 1+(κ/12)*((n:ℝ)+1)/(1-7/16) := hmgf
    _ ≤ 1+2*(κ/12)*((n:ℝ)+1) := by
      norm_num
      have hnonneg : 0 ≤ (κ/12)*((n:ℝ)+1) := by positivity
      nlinarith

theorem tilted_ratio_exponential_mean_le (H : HoldingFamily ι)
    {κ τ : ℝ} (hκ : 0 < κ) (hκmax : κ*H.maxRatio ≤ 1/4) (hκτ : κ ≤ τ)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (h : ℕ) (hhκ : (h:ℝ)*κ ≤ 1/8) (n : ℕ) (hn : n+1 ≤ h) :
    (R.tiltedLaw loss hloss M hM n).mean
      (fun hist ↦ Real.exp ((κ/12)*stateTotal H.ratio n hist)) ≤
        Real.exp ((5/2)*(κ/12)*((n:ℝ)+1)) := by
  have href := H.reference_ratio_exponential_mean_le hκ hκmax hκτ h hhκ n hn
  have hdom := R.tilted_nonneg_mean_le loss hloss M hM n
    (fun hist ↦ Real.exp ((κ/12)*stateTotal H.ratio n hist)-1) (by
      intro hist
      apply sub_nonneg.mpr
      apply Real.one_le_exp_iff.mpr
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun t _ ↦ le_of_lt (H.ratio_pos (stateAt n hist t))))
  simp only [ProbabilityVector.mean_sub, ProbabilityVector.mean_const] at hdom
  calc
    _ ≤ 1+(5/2)*(κ/12)*((n:ℝ)+1) := by linarith
    _ ≤ Real.exp ((5/2)*(κ/12)*((n:ℝ)+1)) := by
      simpa only [add_comm] using Real.add_one_le_exp ((5/2)*(κ/12)*((n:ℝ)+1))

end
end Tournament.HoldingFamily

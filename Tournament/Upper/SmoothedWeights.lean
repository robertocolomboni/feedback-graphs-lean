module

public import Tournament.Upper.ExponentialWeights

@[expose] public section

namespace Tournament.Upper.ExponentialWeights

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def smooth (π : ProbabilityVector ι) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) : ProbabilityVector ι where
  weight i := (1-ε)*π i+ε*uniform i
  nonneg i := add_nonneg (mul_nonneg (by linarith) (π.nonneg i)) (mul_nonneg hε (uniform.nonneg i))
  sum_eq_one := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,π.sum_eq_one,uniform.sum_eq_one]
    ring

theorem smooth_mean (π : ProbabilityVector ι) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1) (f : ι → ℝ) :
    (smooth π ε hε hε1).mean f=(1-ε)*π.mean f+ε*uniform.mean f := by
  unfold ProbabilityVector.mean smooth
  simp only [add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]

theorem le_twice_smooth (π : ProbabilityVector ι) (ε : ℝ) (hε : 0≤ε) (hεhalf : ε≤1/2) (i : ι) :
    π i≤2*smooth π ε hε (by linarith) i := by
  have hp := π.nonneg i
  have hu := uniform (ι := ι) |>.nonneg i
  have h₁ := mul_nonneg (show 0≤1/2-ε by linarith) hp
  have h₂ := mul_nonneg hε hu
  change π i≤2*((1-ε)*π i+ε*uniform i)
  nlinarith

theorem squareNorm_le_twice_smooth (π : ProbabilityVector ι) (ε : ℝ) (hε : 0≤ε) (hεhalf : ε≤1/2) (f : ι → ℝ) :
    π.squareNorm f≤2*(smooth π ε hε (by linarith)).squareNorm f := by
  unfold ProbabilityVector.squareNorm
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ by
    have h := mul_le_mul_of_nonneg_right (le_twice_smooth π ε hε hεhalf i) (sq_nonneg (f i))
    nlinarith)

theorem smooth_loss_charge (π : ProbabilityVector ι) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (f : ι → ℝ) (h : ℝ) (hf : ∀ i, 0≤f i ∧ f i≤h) :
    (smooth π ε hε hε1).mean f-π.mean f≤ε*h := by
  have hp : 0≤π.mean f := π.mean_nonneg (fun i ↦ (hf i).1)
  have hu : uniform.mean f≤h := by
    calc
      _ ≤ uniform.mean (fun _ : ι ↦ h) := uniform.mean_mono (fun i ↦ (hf i).2)
      _ = _ := ProbabilityVector.mean_const _ _
  rw [smooth_mean]
  have hmul := mul_le_mul_of_nonneg_left (show uniform.mean f-π.mean f≤h by linarith) hε
  nlinarith

omit [Nonempty ι] in
theorem centered_comparison (π w : ProbabilityVector ι) (f : ι → ℝ) (i : ι) :
    π.mean (w.center f)-w.center f i=π.mean f-f i := by
  unfold ProbabilityVector.center
  rw [ProbabilityVector.mean_sub,ProbabilityVector.mean_const]
  ring

omit [Nonempty ι] in
theorem comparison_bias_abs (π : ProbabilityVector ι) (ξ : ι → ℝ) (i : ι) :
    |π.mean ξ-ξ i|≤2*‖ξ‖ := by
  have hmean : |π.mean ξ|≤‖ξ‖ := by
    calc
      _ ≤ π.mean (fun j ↦ |ξ j|) := π.abs_mean_le _
      _ ≤ π.mean (fun _ ↦ ‖ξ‖) := π.mean_mono (fun j ↦ by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ j)
      _ = _ := ProbabilityVector.mean_const _ _
  have hi : |ξ i|≤‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ i
  have htri := abs_sub_le (π.mean ξ) 0 (ξ i)
  simp only [sub_zero,zero_sub,abs_neg] at htri
  linarith

theorem conditional_comparison_lower (π : ProbabilityVector ι) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (L ξ : ι → ℝ) (h : ℝ) (hL : ∀ i, 0≤L i ∧ L i≤h) (i : ι) :
    (smooth π ε hε hε1).mean L-L i-ε*h-2*‖ξ‖≤
      π.mean (fun j ↦ (smooth π ε hε hε1).center L j-ξ j)-
        ((smooth π ε hε hε1).center L i-ξ i) := by
  have hs := smooth_loss_charge π ε hε hε1 L h hL
  have hb := (abs_le.mp (comparison_bias_abs π ξ i)).2
  rw [ProbabilityVector.mean_sub]
  have hc := centered_comparison π (smooth π ε hε hε1) L i
  linarith

end
end Tournament.Upper.ExponentialWeights

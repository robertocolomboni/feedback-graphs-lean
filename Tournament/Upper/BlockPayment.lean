module

public import Tournament.Upper.BlockParameters

@[expose] public section

namespace Tournament.Upper.BlockParameters

open scoped Classical

noncomputable section

theorem moment_coefficient_le {K T m : ℕ} (hK : 2≤K) (hT : 2≤T) (hm : 5≤m)
    (L₀ : ℝ) (hL₀ : L₀≤(2:ℝ)^8*logScale K T) :
    paymentCoefficient K T m*((2:ℝ)^14*(m:ℝ)*L₀/DyadicRate.base m)≤ScoreRule.steeringStrength (threshold K T) := by
  have hM : 0<threshold K T := lt_of_lt_of_le (by norm_num) (threshold_ge_one hK hT)
  have hΛ : 0<logScale K T := lt_of_lt_of_le (by norm_num) (logScale_ge_one hK hT)
  have hm0 : (0:ℝ)<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hκ := DyadicRate.base_pos m
  calc
    _ = L₀/(1024*threshold K T*logScale K T) := by
      unfold paymentCoefficient
      field_simp
      ring
    _ ≤ ScoreRule.steeringStrength (threshold K T) := by
      unfold ScoreRule.steeringStrength
      apply (div_le_div_iff₀ (by positivity : (0:ℝ)<1024*threshold K T*logScale K T) (by positivity)).mpr
      norm_num at hL₀
      have hx := mul_le_mul_of_nonneg_left hL₀ (show 0≤4*threshold K T by positivity)
      nlinarith

theorem payment_from_moment {K T m : ℕ} (hK : 2≤K) (hT : 2≤T) (hm : 5≤m)
    (L₀ : ℝ) (hL₀ : L₀≤(2:ℝ)^8*logScale K T) (Γ h V : ℝ)
    (hΓ : 0≤Γ+meanRate m*h/16)
    (hV : V≤((2:ℝ)^14*(m:ℝ)*L₀/DyadicRate.base m)*(Γ+meanRate m*h/16)) :
    paymentCoefficient K T m*V-ScoreRule.steeringStrength (threshold K T)*meanRate m*h/16≤
      ScoreRule.steeringStrength (threshold K T)*Γ := by
  have hc : 0≤paymentCoefficient K T m := by
    rw [← twice_learningRate]
    exact mul_nonneg (by norm_num) (learningRate_pos hK hT hm).le
  have h₁ := mul_le_mul_of_nonneg_left hV hc
  have h₂ := mul_le_mul_of_nonneg_right (moment_coefficient_le hK hT hm L₀ hL₀) hΓ
  nlinarith

end
end Tournament.Upper.BlockParameters

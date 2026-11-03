module

public import Tournament.Characterization.Observable

@[expose] public section

namespace Tournament.Characterization

open Lower.Domination
noncomputable section

theorem root_log_comparison (a L x : ℝ) (ha : 0≤a) (hL : 0≤L) (hx : 1≤x) (hLx : L≤x) :
    (a*L)^((1:ℝ)/3)≤x*(max 1 (a/x^2))^((1:ℝ)/3) := by
  have hx0 : 0<x := by linarith
  have hM : 0≤max 1 (a/x^2) := le_trans (by norm_num : (0:ℝ)≤1) (le_max_left _ _)
  apply (pow_le_pow_iff_left₀ (by positivity : 0≤(a*L)^((1:ℝ)/3))
    (by positivity : 0≤x*(max 1 (a/x^2))^((1:ℝ)/3)) (by decide : (3:ℕ)≠0)).mp
  rw [root_cube _ (mul_nonneg ha hL),mul_pow,root_cube _ hM]
  have hRatio : a≤max 1 (a/x^2)*x^2 := (div_le_iff₀ (sq_pos_of_pos hx0)).mp (le_max_right _ _)
  calc
    a*L≤a*x := mul_le_mul_of_nonneg_left hLx ha
    _ ≤(max 1 (a/x^2)*x^2)*x := mul_le_mul_of_nonneg_right hRatio hx0.le
    _ =x^3*max 1 (a/x^2) := by ring

theorem upper_shape_comparison (γ T L x : ℝ) (hγ : 0≤γ) (hT : 0<T)
    (hL : 0≤L) (hx : 1≤x) (hLx : L≤x) :
    min (5*(γ*L)^((1:ℝ)/3)*T^((2:ℝ)/3)) T≤
      5*x*T^((2:ℝ)/3)*(max 1 (min γ T/x^2))^((1:ℝ)/3) := by
  have hTime : 0≤T^((2:ℝ)/3) := Real.rpow_nonneg hT.le _
  by_cases hγT : γ≤T
  · rw [min_eq_left hγT]
    apply (min_le_left _ _).trans
    have hRoot := root_log_comparison γ L x hγ hL hx hLx
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRoot (by norm_num : (0:ℝ)≤5)) hTime
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  · have hTγ : T≤γ := le_of_not_ge hγT
    rw [min_eq_right hTγ]
    apply (min_le_right _ _).trans
    have hRoot : T^((1:ℝ)/3)≤x*(max 1 (T/x^2))^((1:ℝ)/3) := by
      simpa only [mul_one] using root_log_comparison T 1 x hT.le (by norm_num) hx hx
    have hProd : T^((1:ℝ)/3)*T^((2:ℝ)/3)=T := by rw [← Real.rpow_add hT]; norm_num
    have h := mul_le_mul_of_nonneg_right hRoot hTime
    rw [hProd] at h
    have hNonneg : 0≤x*T^((2:ℝ)/3)*(max 1 (T/x^2))^((1:ℝ)/3) := by
      apply mul_nonneg (mul_nonneg (by linarith) hTime)
      exact Real.rpow_nonneg (le_trans (by norm_num : (0:ℝ)≤1) (le_max_left _ _)) _
    nlinarith [h]

theorem upper_lower_ratio (K γ T : ℕ) (hK : 2≤K) (hT : 2≤T) :
    min (5*((γ:ℝ)*Real.log (K:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3)) (T:ℝ)≤
      (5120*Lower.Dyadic.upsilon T*logCard K)*bound K γ T := by
  have hLog : 0≤Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤K))
  have hx : 1≤logCard K := logCard_ge_one K hK
  have hU : 0<Lower.Dyadic.upsilon T := lt_of_lt_of_le (by norm_num)
    (Lower.Parameters.upsilon_ge_one T (by omega))
  have h := upper_shape_comparison (γ:ℝ) (T:ℝ) (Real.log (K:ℝ)) (logCard K)
    (Nat.cast_nonneg _) (by exact_mod_cast (by omega : 0<T)) hLog hx (by dsimp [logCard]; linarith)
  calc
    _ ≤5*logCard K*(T:ℝ)^((2:ℝ)/3)*
        (max 1 (min (γ:ℝ) (T:ℝ)/(logCard K)^2))^((1:ℝ)/3) := h
    _ = _ := by unfold bound; field_simp [ne_of_gt hU]; ring

theorem upper_lower_ratio_explicit (K γ T : ℕ) (hK : 2≤K) (hT : 2≤T) :
    min (5*((γ:ℝ)*Real.log (K:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3)) (T:ℝ)≤
      (5120*(Real.log (2*(T:ℝ))/Real.log 2)*Real.log (Real.exp 1*(K:ℝ)))*
        ((T:ℝ)^((2:ℝ)/3)*
          (max 1 (min (γ:ℝ) (T:ℝ)/(Real.log (Real.exp 1*(K:ℝ)))^2))^((1:ℝ)/3)/
            (1024*(Real.log (2*(T:ℝ))/Real.log 2))) := by
  simpa only [bound,logCard_eq K hK,Lower.Dyadic.upsilon] using upper_lower_ratio K γ T hK hT

end
end Tournament.Characterization

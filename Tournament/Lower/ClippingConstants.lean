module

public import Tournament.Lower.ClippingPointwise
public import Tournament.Lower.Parameters
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

namespace Tournament.Lower

open Real
open scoped NNReal

noncomputable section

theorem clipping_coefficient_at_max (U : ℝ) (hU : 0<U) :
    sqrt (2*(1/(128*U))/π)=1/(8*sqrt (π*U)) := by
  have hs : (sqrt (π*U))^2=π*U := sq_sqrt (by positivity)
  have hspos : 0<sqrt (π*U) := sqrt_pos.mpr (by positivity)
  have heq : (sqrt (2*(1/(128*U))/π))^2=(1/(8*sqrt (π*U)))^2 := by
    rw [sq_sqrt (by positivity),div_pow,mul_pow,hs]
    field_simp
    norm_num
  exact (sq_eq_sq₀ (by positivity) (by positivity)).mp heq

theorem clipping_gaussian_tail_le_exp (U : ℝ) (hU : 0<U) (v : ℝ≥0)
    (hv : (v:ℝ)≤1/(128*U)) :
    sqrt (2*(v:ℝ)/π)*exp (-(7/32)^2/(2*(v:ℝ)))≤exp (-3*U)/(8*sqrt (π*U)) := by
  by_cases hv0 : v=0
  · subst v
    simp only [NNReal.coe_zero,mul_zero,zero_div,sqrt_zero,zero_mul]
    positivity
  · have hvr : (0:ℝ)<(v:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv0)
    have hcoef : sqrt (2*(v:ℝ)/π)≤1/(8*sqrt (π*U)) := by
      rw [← clipping_coefficient_at_max U hU]
      apply sqrt_le_sqrt
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by norm_num)) pi_pos.le
    have hscaled : (v:ℝ)*(128*U)≤1 := (le_div_iff₀ (by positivity)).mp hv
    have he : -(7/32:ℝ)^2/(2*(v:ℝ))≤ -3*U := by
      apply (div_le_iff₀ (by positivity : 0<2*(v:ℝ))).mpr
      nlinarith
    calc
      _ ≤ (1/(8*sqrt (π*U)))*exp (-3*U) :=
        mul_le_mul hcoef (exp_le_exp.mpr he) (exp_pos _).le (by positivity)
      _ = _ := by ring

theorem clipping_exponential_decay (T : ℕ) (hT : 2≤T) :
    exp (-3*Dyadic.upsilon T)≤1/(2*(T:ℝ))^4 := by
  have ht : (0:ℝ)<2*(T:ℝ) := by
    have : (0:ℝ)<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
    positivity
  have hU := Parameters.upsilon_ge_two T hT
  have hl : log 2≤3/4 := by linarith [log_two_lt_d9]
  have hid : Dyadic.upsilon T*log 2=log (2*(T:ℝ)) := by
    unfold Dyadic.upsilon
    exact div_mul_cancel₀ _ (ne_of_gt (log_pos (by norm_num : (1:ℝ)<2)))
  have hmul := mul_le_mul_of_nonneg_left hl (by linarith : 0≤Dyadic.upsilon T)
  have he : -3*Dyadic.upsilon T≤ -4*log (2*(T:ℝ)) := by nlinarith [hid]
  calc
    _ ≤ exp (-4*log (2*(T:ℝ))) := exp_le_exp.mpr he
    _ = 1/(2*(T:ℝ))^4 := by
      have hexp : -4*log (2*(T:ℝ))= -log ((2*(T:ℝ))^4) := by rw [log_pow]; norm_num
      rw [hexp,exp_neg,exp_log (by positivity),one_div]

theorem clipping_prefactor_le (U : ℝ) (hU : 2≤U) : 1/(8*sqrt (π*U))≤1/20 := by
  have hs : (sqrt (π*U))^2=π*U := sq_sqrt (by positivity)
  have hs0 := sqrt_nonneg (π*U)
  have hp := pi_gt_d2
  have hu : 2*π≤π*U := by simpa only [mul_comm π 2] using mul_le_mul_of_nonneg_left hU pi_pos.le
  have hroot : 5/2≤sqrt (π*U) := by nlinarith
  apply (div_le_iff₀ (by positivity : 0<8*sqrt (π*U))).mpr
  nlinarith

theorem clipping_gaussian_tail_le (T : ℕ) (hT : 2≤T) (v : ℝ≥0)
    (hv : (v:ℝ)≤1/(128*Dyadic.upsilon T)) :
    sqrt (2*(v:ℝ)/π)*exp (-(7/32)^2/(2*(v:ℝ)))≤(1/(2*(T:ℝ))^4)/20 := by
  have hU := Parameters.upsilon_ge_two T hT
  calc
    _ ≤ exp (-3*Dyadic.upsilon T)/(8*sqrt (π*Dyadic.upsilon T)) :=
      clipping_gaussian_tail_le_exp _ (by linarith) v hv
    _ = (1/(8*sqrt (π*Dyadic.upsilon T)))*exp (-3*Dyadic.upsilon T) := by ring
    _ ≤ (1/20)*(1/(2*(T:ℝ))^4) :=
      mul_le_mul (clipping_prefactor_le _ hU) (clipping_exponential_decay T hT)
        (exp_pos _).le (by norm_num)
    _ = _ := by ring

theorem clipping_sum_numerical_bound (T n : ℕ) (hT : 2≤T) (hn : n≤T) :
    (T:ℝ)*(n:ℝ)*((1/(2*(T:ℝ))^4)/20)≤1/1024 := by
  have ht : (2:ℝ)≤(T:ℝ) := by exact_mod_cast hT
  have hnr : (n:ℝ)≤(T:ℝ) := by exact_mod_cast hn
  have ht0 : (T:ℝ)≠0 := by linarith
  calc
    _ ≤ (T:ℝ)^2*((1/(2*(T:ℝ))^4)/20) := by
      apply mul_le_mul_of_nonneg_right
      · nlinarith
      · positivity
    _ = 1/(320*(T:ℝ)^2) := by field_simp; ring
    _ ≤ _ := by
      apply (div_le_iff₀ (by positivity : 0<320*(T:ℝ)^2)).mpr
      nlinarith [sq_nonneg ((T:ℝ)-2)]

end
end Tournament.Lower

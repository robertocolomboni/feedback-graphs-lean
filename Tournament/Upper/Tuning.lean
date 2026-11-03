module

public import Tournament.Upper.FixedRateArithmetic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace Tournament.Upper.Tuning

open scoped BigOperators Classical
open BlockParameters

noncomputable section

def target (K T : ℕ) : ℝ := logScale K T*Real.sqrt (Real.log (K:ℝ)/(T:ℝ))

def exponent (r : ℝ) : ℕ := ⌊Real.log (1/r)/Real.log 2⌋₊

def performanceScale (K T : ℕ) : ℝ := Real.sqrt ((T:ℝ)*Real.log (K:ℝ))*(logScale K T)^2

theorem log_two_strict_lower : (1/2:ℝ)<Real.log 2 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≠1)
  rw [one_div,Real.log_inv] at h
  norm_num at h
  linarith

theorem log_two_lower : (1/2:ℝ)≤Real.log 2 := by
  exact log_two_strict_lower.le

theorem log_card_lower {K : ℕ} (hK : 2≤K) : (1/2:ℝ)≤Real.log (K:ℝ) := by
  have hm := Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤(K:ℝ) by exact_mod_cast hK)
  exact le_trans log_two_lower hm

theorem log_base (m : ℕ) : Real.log (DyadicRate.base m)=-(m:ℝ)*Real.log 2 := by
  rw [DyadicRate.base_eq_inv_pow,Real.log_inv,Real.log_pow]
  ring

theorem exponent_ge_five {r : ℝ} (hr : 0<r) (hr32 : r≤1/32) : 5≤exponent r := by
  have hlog2 : 0<Real.log 2 := by linarith [log_two_lower]
  have hinv : (32:ℝ)≤1/r := (le_div_iff₀ hr).mpr (by nlinarith)
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<32) hinv
  have h32 : Real.log (32:ℝ)=5*Real.log 2 := by
    rw [show (32:ℝ)=2^5 by norm_num,Real.log_pow]
    norm_num
  rw [h32] at hlog
  have hx : (5:ℝ)≤Real.log (1/r)/Real.log 2 := (le_div_iff₀ hlog2).mpr hlog
  unfold exponent
  exact (Nat.le_floor_iff (show 0≤Real.log (1/r)/Real.log 2 by linarith)).mpr (by simpa using hx)

theorem dyadic_bracket {r : ℝ} (hr : 0<r) (hr32 : r≤1/32) :
    r≤DyadicRate.base (exponent r) ∧ DyadicRate.base (exponent r)<2*r := by
  have hlog2 : 0<Real.log 2 := by linarith [log_two_lower]
  have hinv : (1:ℝ)≤1/r := (le_div_iff₀ hr).mpr (by nlinarith)
  have hx0 : 0≤Real.log (1/r)/Real.log 2 := div_nonneg (Real.log_nonneg hinv) hlog2.le
  have hf := Nat.floor_le hx0
  have hg := Nat.lt_floor_add_one (Real.log (1/r)/Real.log 2)
  change (exponent r:ℝ)≤Real.log (1/r)/Real.log 2 at hf
  change Real.log (1/r)/Real.log 2<(exponent r:ℝ)+1 at hg
  have hf' := (le_div_iff₀ hlog2).mp hf
  have hg' := (div_lt_iff₀ hlog2).mp hg
  rw [one_div,Real.log_inv] at hf' hg'
  constructor
  · apply (Real.log_le_log_iff hr (DyadicRate.base_pos _)).mp
    rw [log_base]
    linarith
  · apply (Real.log_lt_log_iff (DyadicRate.base_pos _) (mul_pos (by norm_num) hr)).mp
    rw [log_base,Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt hr)]
    linarith

theorem exponent_le_log_time {r : ℝ} {T : ℕ} (hT : 2≤T) (hr : 0<r)
    (hr32 : r≤1/32) (hrT : 1/(T:ℝ)≤r) :
    (exponent r:ℝ)≤Real.log (T:ℝ)/Real.log 2 := by
  have hT0 : (0:ℝ)<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hlog2 : 0<Real.log 2 := by linarith [log_two_lower]
  have hinv : 1/r≤(T:ℝ) := by
    apply (div_le_iff₀ hr).mpr
    have hh := (div_le_iff₀ hT0).mp hrT
    nlinarith
  have hx0 : 0≤Real.log (1/r)/Real.log 2 := by
    apply div_nonneg _ hlog2.le
    apply Real.log_nonneg
    exact (le_div_iff₀ hr).mpr (by nlinarith)
  have hf := Nat.floor_le hx0
  change (exponent r:ℝ)≤Real.log (1/r)/Real.log 2 at hf
  exact le_trans hf (div_le_div_of_nonneg_right
    (Real.log_le_log (one_div_pos.mpr hr) hinv) hlog2.le)

theorem log_time_le_twice_scale {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    Real.log (T:ℝ)/Real.log 2≤2*logScale K T := by
  have hk0 : (0:ℝ)<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have ht0 : (0:ℝ)<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hk : 0≤Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤K by omega))
  have ht : 0≤Real.log (T:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤T by omega))
  have hΛ : logScale K T=1+Real.log (K:ℝ)+Real.log (T:ℝ) := by
    unfold logScale
    rw [Real.log_mul (ne_of_gt (mul_pos (Real.exp_pos 1) hk0)) (ne_of_gt ht0),
      Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hk0),Real.log_exp]
  apply (div_le_iff₀ (show 0<Real.log 2 by linarith [log_two_lower])).mpr
  have hm := mul_le_mul_of_nonneg_left log_two_lower (show 0≤2*logScale K T by linarith [logScale_ge_one hK hT])
  rw [hΛ] at hm ⊢
  nlinarith

theorem logScale_expand {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    logScale K T=1+Real.log (K:ℝ)+Real.log (T:ℝ) := by
  have hk0 : (0:ℝ)<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have ht0 : (0:ℝ)<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  unfold logScale
  rw [Real.log_mul (ne_of_gt (mul_pos (Real.exp_pos 1) hk0)) (ne_of_gt ht0),
    Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hk0),Real.log_exp]

theorem ratio_sqrt_mul_time {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    Real.sqrt (Real.log (K:ℝ)/(T:ℝ))*(T:ℝ)=Real.sqrt ((T:ℝ)*Real.log (K:ℝ)) := by
  have hlog : 0≤Real.log (K:ℝ) := le_trans (by norm_num) (log_card_lower hK)
  have ht : (0:ℝ)≤(T:ℝ) := by positivity
  rw [Real.sqrt_div hlog,Real.sqrt_mul ht]
  calc
    _ = Real.sqrt (Real.log (K:ℝ))*((T:ℝ)/Real.sqrt (T:ℝ)) := by ring
    _ = _ := by rw [Real.div_sqrt]; ring

theorem sqrt_total_gt_one {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    1<Real.sqrt ((T:ℝ)*Real.log (K:ℝ)) := by
  have hlog : (1/2:ℝ)<Real.log (K:ℝ) := lt_of_lt_of_le log_two_strict_lower
    (Real.log_le_log (by norm_num) (by exact_mod_cast hK))
  have ht : (2:ℝ)≤(T:ℝ) := by exact_mod_cast hT
  apply (Real.lt_sqrt (by norm_num : (0:ℝ)≤1)).mpr
  nlinarith

theorem target_pos {K T : ℕ} (hK : 2≤K) (hT : 2≤T) : 0<target K T := by
  have hlog : 0<Real.log (K:ℝ) := lt_of_lt_of_le (by norm_num) (log_card_lower hK)
  have ht : (0:ℝ)<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  exact mul_pos (lt_of_lt_of_le (by norm_num) (logScale_ge_one hK hT)) (Real.sqrt_pos.mpr (div_pos hlog ht))

theorem target_ge_inverse_time {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    1/(T:ℝ)≤target K T := by
  have ht : (0:ℝ)<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  apply (div_le_iff₀ ht).mpr
  unfold target
  rw [mul_assoc,ratio_sqrt_mul_time hK hT]
  have hroot := sqrt_total_gt_one hK hT
  have hΛ := logScale_ge_one hK hT
  nlinarith

theorem performanceScale_gt_four {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    4<performanceScale K T := by
  have hk : (1/2:ℝ)<Real.log (K:ℝ) := lt_of_lt_of_le log_two_strict_lower
    (Real.log_le_log (by norm_num) (by exact_mod_cast hK))
  have ht : (1/2:ℝ)<Real.log (T:ℝ) := lt_of_lt_of_le log_two_strict_lower
    (Real.log_le_log (by norm_num) (by exact_mod_cast hT))
  have hΛ : 2<logScale K T := by rw [logScale_expand hK hT]; linarith
  have hr := sqrt_total_gt_one hK hT
  unfold performanceScale
  calc
    (4:ℝ)<(logScale K T)^2 := by nlinarith
    _ ≤ Real.sqrt ((T:ℝ)*Real.log (K:ℝ))*(logScale K T)^2 := by nlinarith [sq_nonneg (logScale K T)]

theorem threshold_le_two_thousand_scale {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    threshold K T≤2000*logScale K T := by
  have hp : (0:ℝ)<(K:ℝ)*(T:ℝ) := lt_of_lt_of_le (by norm_num) (product_ge_four hK hT)
  have hlog2 : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hM : threshold K T=100*(Real.log 2+20*Real.log ((K:ℝ)*(T:ℝ))) := by
    unfold threshold BlockParameters.failure
    rw [div_div_eq_mul_div,div_one,Real.log_mul (by norm_num : (2:ℝ)≠0) (pow_ne_zero _ (ne_of_gt hp)),
      Real.log_pow]
    norm_num
  have hΛ : logScale K T=1+Real.log ((K:ℝ)*(T:ℝ)) := by
    unfold logScale
    rw [mul_assoc,Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hp),Real.log_exp]
  rw [hM,hΛ]
  linarith

theorem log_div_ratio_sqrt {K T : ℕ} (hK : 2≤K) (hT : 2≤T) :
    Real.log (K:ℝ)/Real.sqrt (Real.log (K:ℝ)/(T:ℝ))=Real.sqrt ((T:ℝ)*Real.log (K:ℝ)) := by
  have hlog : 0≤Real.log (K:ℝ) := le_trans (by norm_num) (log_card_lower hK)
  have ht : (0:ℝ)≤(T:ℝ) := by positivity
  rw [Real.sqrt_div hlog,div_div_eq_mul_div,Real.sqrt_mul ht]
  calc
    _ = (Real.log (K:ℝ)/Real.sqrt (Real.log (K:ℝ)))*Real.sqrt (T:ℝ) := by ring
    _ = _ := by rw [Real.div_sqrt]; ring

theorem tuned_parameters {K T : ℕ} (hK : 2≤K) (hT : 2≤T)
    (hr : target K T≤1/32) :
    5≤exponent (target K T) ∧
      target K T≤DyadicRate.base (exponent (target K T)) ∧
      DyadicRate.base (exponent (target K T))<2*target K T ∧
      1/(T:ℝ)≤DyadicRate.base (exponent (target K T)) ∧
      (exponent (target K T):ℝ)≤2*logScale K T := by
  have hp := target_pos hK hT
  have hb := dyadic_bracket hp hr
  exact ⟨exponent_ge_five hp hr,hb.1,hb.2,(target_ge_inverse_time hK hT).trans hb.1,
    (exponent_le_log_time hT hp hr (target_ge_inverse_time hK hT)).trans (log_time_le_twice_scale hK hT)⟩

theorem tuned_meanRate {K T : ℕ} (hK : 2≤K) (hT : 2≤T)
    (hr : target K T≤1/32) :
    meanRate (exponent (target K T))*(T:ℝ)≤4*performanceScale K T := by
  let m := exponent (target K T)
  have hp := tuned_parameters hK hT hr
  have hm : (2:ℝ)≤(m:ℝ) := by exact_mod_cast (show 2≤m by dsimp only [m]; omega)
  have hΛ : 0≤logScale K T := le_trans (by norm_num) (logScale_ge_one hK hT)
  have ht : (0:ℝ)≤(T:ℝ) := by positivity
  have hr0 := target_pos hK hT
  have hμ : meanRate m≤DyadicRate.base m*(m:ℝ) := by
    unfold meanRate
    have hκ := (DyadicRate.base_pos m).le
    nlinarith
  calc
    _ ≤ DyadicRate.base m*(m:ℝ)*(T:ℝ) := mul_le_mul_of_nonneg_right hμ ht
    _ ≤ (2*target K T)*(2*logScale K T)*(T:ℝ) := by
      gcongr
      · exact hp.2.2.1.le
      · exact hp.2.2.2.2
    _ = 4*performanceScale K T := by
      unfold target performanceScale
      calc
        _ = 4*(logScale K T)^2*(Real.sqrt (Real.log (K:ℝ)/(T:ℝ))*(T:ℝ)) := by ring
        _ = _ := by rw [ratio_sqrt_mul_time hK hT]; ring

theorem tuned_comparison_term {K T : ℕ} (hK : 2≤K) (hT : 2≤T)
    (hr : target K T≤1/32) :
    (2:ℝ)^25*threshold K T*(exponent (target K T):ℝ)*logScale K T*Real.log (K:ℝ)/
      DyadicRate.base (exponent (target K T))≤(2:ℝ)^26*2000*performanceScale K T := by
  have hp := tuned_parameters hK hT hr
  have hM := threshold_le_two_thousand_scale hK hT
  have hΛ : 0<logScale K T := lt_of_lt_of_le (by norm_num) (logScale_ge_one hK hT)
  have hlog : 0<Real.log (K:ℝ) := lt_of_lt_of_le (by norm_num) (log_card_lower hK)
  have ht : (0:ℝ)<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hroot : 0<Real.sqrt (Real.log (K:ℝ)/(T:ℝ)) := Real.sqrt_pos.mpr (div_pos hlog ht)
  have hr0 := target_pos hK hT
  calc
    _ ≤ (2:ℝ)^25*(2000*logScale K T)*(2*logScale K T)*logScale K T*Real.log (K:ℝ)/target K T := by
      gcongr
      · exact hp.2.2.2.2
      · exact hp.2.1
    _ = (2:ℝ)^26*2000*(logScale K T)^2*
        (Real.log (K:ℝ)/Real.sqrt (Real.log (K:ℝ)/(T:ℝ))) := by
      unfold target
      field_simp
    _ = _ := by rw [log_div_ratio_sqrt hK hT]; unfold performanceScale; ring

theorem large_target_fixed_action {K T : ℕ} (hK : 2≤K) (hT : 2≤T)
    (hr : 1/32<target K T) : (T:ℝ)<32*performanceScale K T := by
  have ht : (0:ℝ)<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hm := mul_lt_mul_of_pos_right hr ht
  have heq : target K T*(T:ℝ)=logScale K T*Real.sqrt ((T:ℝ)*Real.log (K:ℝ)) := by
    unfold target
    rw [mul_assoc,ratio_sqrt_mul_time hK hT]
  rw [heq] at hm
  have hΛ := logScale_ge_one hK hT
  have hroot := (sqrt_total_gt_one hK hT).le
  unfold performanceScale
  nlinarith [mul_nonneg (show 0≤logScale K T-1 by linarith)
    (show 0≤logScale K T*Real.sqrt ((T:ℝ)*Real.log (K:ℝ)) by positivity)]

theorem performanceScale_time_one {K : ℕ} (hK : 2≤K) : 1≤performanceScale K 1 := by
  have hlog := log_card_lower hK
  have hs : (1/2:ℝ)≤Real.sqrt (Real.log (K:ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hk0 : (K:ℝ)≠0 := by exact_mod_cast (show K≠0 by omega)
  have hΛ : logScale K 1=1+Real.log (K:ℝ) := by
    unfold logScale
    norm_num
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) hk0,Real.log_exp]
  unfold performanceScale
  norm_num
  rw [hΛ]
  have hsq : (9/4:ℝ)≤(1+Real.log (K:ℝ))^2 := by nlinarith
  have hm := mul_le_mul hs hsq (by norm_num : (0:ℝ)≤9/4) (Real.sqrt_nonneg _)
  nlinarith

end
end Tournament.Upper.Tuning

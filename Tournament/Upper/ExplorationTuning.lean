module

public import Tournament.Upper.ExplorationCost
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace Tournament.Upper.Exploration

noncomputable section

def rate (D L T : ℝ) : ℝ := (D*L/(9*T))^((1:ℝ)/3)

def learningRate (D L T : ℝ) : ℝ := Real.sqrt (rate D L T*L/(T*D))

theorem rate_pos (D L T : ℝ) (hD : 0<D) (hL : 0<L) (hT : 0<T) : 0<rate D L T := by
  unfold rate
  positivity

theorem rate_cube (D L T : ℝ) (hD : 0≤D) (hL : 0≤L) (hT : 0<T) :
    9*T*(rate D L T)^3=D*L := by
  have h : ((D*L/(9*T))^((1:ℝ)/3))^3=D*L/(9*T) := by
    simpa [one_div] using Real.rpow_inv_natCast_pow
      (show 0≤D*L/(9*T) by positivity) (by decide : (3:ℕ)≠0)
  unfold rate
  rw [h]
  field_simp

theorem learningRate_pos (D L T : ℝ) (hD : 0<D) (hL : 0<L) (hT : 0<T) :
    0<learningRate D L T := by
  have hκ := rate_pos D L T hD hL hT
  unfold learningRate
  positivity

theorem learningRate_sq (D L T : ℝ) (hD : 0<D) (hL : 0<L) (hT : 0<T) :
    (learningRate D L T)^2=rate D L T*L/(T*D) := by
  have hκ := rate_pos D L T hD hL hT
  exact Real.sq_sqrt (by positivity)

theorem tuned_first_terms (D L T : ℝ) (hD : 0<D) (hL : 0<L) (hT : 0<T) :
    L/learningRate D L T=3*rate D L T*T ∧
      learningRate D L T*T*D/rate D L T=3*rate D L T*T := by
  let κ := rate D L T
  let η := learningRate D L T
  have hκ : 0<κ := rate_pos D L T hD hL hT
  have hη : 0<η := learningRate_pos D L T hD hL hT
  have hc : 9*T*κ^3=D*L := rate_cube D L T hD.le hL.le hT
  have hs : η^2=κ*L/(T*D) := learningRate_sq D L T hD hL hT
  have he : η*D=3*κ^2 := by
    apply (sq_eq_sq₀ (mul_nonneg hη.le hD.le) (by positivity)).mp
    calc
      _ = (κ*L/(T*D))*D^2 := by rw [mul_pow,hs]
      _ = κ*(D*L)/T := by field_simp
      _ = κ*(9*T*κ^3)/T := by rw [hc]
      _ = _ := by field_simp; ring
  change L/η=3*κ*T ∧ η*T*D/κ=3*κ*T
  constructor
  · apply (div_eq_iff (ne_of_gt hη)).mpr
    apply mul_right_cancel₀ (ne_of_gt hD)
    calc
      _ = 9*T*κ^3 := by nlinarith [hc]
      _ = (3*κ*T)*(η*D) := by rw [he]; ring
      _ = _ := by ring
  · apply (div_eq_iff (ne_of_gt hκ)).mpr
    calc
      _ = (η*D)*T := by ring
      _ = _ := by rw [he]; ring

theorem unsimplified_budget_le (D L T κ η : ℝ) (hD : 1≤D) (hT : 0≤T)
    (hκ : 0<κ) (hκhalf : κ≤1/2) (hη : 0≤η) :
    L/η+η*T*(1+D/(2*κ))+3*κ*T≤L/η+η*T*D/κ+3*κ*T := by
  have haux : 1+D/(2*κ)≤D/κ := by
    apply (le_div_iff₀ hκ).mpr
    field_simp at *
    nlinarith
  have hm := mul_le_mul_of_nonneg_left haux (mul_nonneg hη hT)
  simpa only [mul_div_assoc,add_comm,add_left_comm,add_assoc] using
    add_le_add_right (add_le_add_left hm (L/η)) (3*κ*T)

theorem tuned_budget (D L T : ℝ) (hD : 0<D) (hL : 0<L) (hT : 0<T) :
    L/learningRate D L T+learningRate D L T*T*D/rate D L T+3*rate D L T*T=
      9*rate D L T*T := by
  rcases tuned_first_terms D L T hD hL hT with ⟨hfirst,hsecond⟩
  rw [hfirst,hsecond]
  ring

theorem final_constant (D L T : ℝ) (hD : 0<D) (hL : 0<L) (hT : 0<T) :
    9*rate D L T*T=(3:ℝ)^((4:ℝ)/3)*(D*L)^((1:ℝ)/3)*T^((2:ℝ)/3) := by
  have hTpow : T/T^((1:ℝ)/3)=T^((2:ℝ)/3) := by
    have h := Real.rpow_sub hT (1:ℝ) ((1:ℝ)/3)
    norm_num at h
    exact h.symm
  have hThree : (9:ℝ)/(9:ℝ)^((1:ℝ)/3)=(3:ℝ)^((4:ℝ)/3) := by
    have h := Real.rpow_sub (by norm_num : (0:ℝ)<9) (1:ℝ) ((1:ℝ)/3)
    norm_num at h
    rw [← h,show (9:ℝ)=(3:ℝ)^2 by norm_num,← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)]
    norm_num
  unfold rate
  rw [Real.div_rpow (by positivity) (by positivity),Real.mul_rpow (by norm_num) hT.le]
  calc
    _ = ((9:ℝ)/(9:ℝ)^((1:ℝ)/3))*(D*L)^((1:ℝ)/3)*(T/T^((1:ℝ)/3)) := by ring
    _ = _ := by rw [hThree,hTpow]

theorem large_rate_horizon (D L T : ℝ) (hD : 0<D) (hL : 0<L) (hT : 0<T)
    (hLarge : 1/2<rate D L T) : T<(8/9)*D*L := by
  have hκ := rate_pos D L T hD hL hT
  have hc := rate_cube D L T hD.le hL.le hT
  have hp : (1/2:ℝ)^3<(rate D L T)^3 := pow_lt_pow_left₀ hLarge (by norm_num) (by decide : (3:ℕ)≠0)
  nlinarith

theorem large_rate_fixed_action (D L T : ℝ) (hD : 0<D) (hL : 0<L) (hT : 0<T)
    (hLarge : 1/2<rate D L T) : T≤(D*L)^((1:ℝ)/3)*T^((2:ℝ)/3) := by
  have ht := large_rate_horizon D L T hD hL hT hLarge
  have hlt : T≤D*L := by nlinarith [mul_pos hD hL]
  have hp := Real.rpow_le_rpow hT.le hlt (by norm_num : (0:ℝ)≤1/3)
  have hm := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hT.le ((2:ℝ)/3))
  have hid : T^((1:ℝ)/3)*T^((2:ℝ)/3)=T := by
    rw [← Real.rpow_add hT]
    norm_num
  rwa [hid] at hm

end
end Tournament.Upper.Exploration

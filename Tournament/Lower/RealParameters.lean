module

public import Tournament.Lower.Parameters

@[expose] public section

namespace Tournament.Lower.RealParameters

noncomputable section

def theta (T n : ℕ) (m : ℝ) : ℝ :=
  1/(32*Dyadic.upsilon T)*((n:ℝ)/(m*(T:ℝ)))^((1:ℝ)/3)

theorem theta_nonneg (T n : ℕ) (m : ℝ) (hT : 1≤T) (hm : 1≤m) : 0≤theta T n m := by
  have hu := Parameters.upsilon_ge_one T hT
  unfold theta
  positivity

theorem theta_pos (T n : ℕ) (m : ℝ) (hT : 1≤T) (hn : 1≤n) (hm : 1≤m) : 0<theta T n m := by
  have hu := Parameters.upsilon_ge_one T hT
  have ht : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hm0 : 0<m := by linarith
  unfold theta
  positivity

theorem theta_le_one_sixty_four (T n : ℕ) (m : ℝ) (hT : 2≤T) (hn : n≤T) (hm : 1≤m) :
    theta T n m≤1/64 := by
  have hU := Parameters.upsilon_ge_two T hT
  have ht : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hnr : (n:ℝ)≤(T:ℝ) := by exact_mod_cast hn
  have hratio : (n:ℝ)/(m*(T:ℝ))≤1 := by
    apply (div_le_one (by positivity : 0<m*(T:ℝ))).mpr
    nlinarith
  have hp : ((n:ℝ)/(m*(T:ℝ)))^((1:ℝ)/3)≤1 :=
    Real.rpow_le_one (by positivity) hratio (by norm_num)
  unfold theta
  have hinv : 1/(32*Dyadic.upsilon T)≤1/64 := by
    apply (div_le_iff₀ (by nlinarith : 0<32*Dyadic.upsilon T)).mpr
    nlinarith
  calc
    _ ≤ (1/(32*Dyadic.upsilon T))*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := by simpa only [mul_one] using hinv

theorem theta_cube_identity (T n : ℕ) (m : ℝ) (hT : 1≤T) (hm : 1≤m) :
    1024*m*Dyadic.upsilon T^3*(theta T n m)^3*(T:ℝ)=(n:ℝ)/32 := by
  have hU : Dyadic.upsilon T≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Parameters.upsilon_ge_one T hT))
  have ht : (T:ℝ)≠0 := by exact_mod_cast (by omega : T≠0)
  have hm0 : m≠0 := by linarith
  have hc : (((n:ℝ)/(m*(T:ℝ)))^((1:ℝ)/3))^3=(n:ℝ)/(m*(T:ℝ)) := by
    simpa [one_div] using Real.rpow_inv_natCast_pow
      (show 0≤(n:ℝ)/(m*(T:ℝ)) by positivity) (by decide : (3:ℕ)≠0)
  unfold theta
  rw [mul_pow,hc]
  field_simp
  ring

theorem theta_time_identity (T n : ℕ) (m : ℝ) (hT : 1≤T) (hm : 1≤m) :
    theta T n m*(T:ℝ)/8=
      (T:ℝ)^((2:ℝ)/3)*((n:ℝ)/m)^((1:ℝ)/3)/(256*Dyadic.upsilon T) := by
  have ht : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hm0 : m≠0 := by linarith
  have hU : Dyadic.upsilon T≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Parameters.upsilon_ge_one T hT))
  have hratio : (n:ℝ)/(m*(T:ℝ))=((n:ℝ)/m)/(T:ℝ) := by ring
  have hpow : (T:ℝ)/(T:ℝ)^((1:ℝ)/3)=(T:ℝ)^((2:ℝ)/3) := by
    have h := Real.rpow_sub ht (1:ℝ) ((1:ℝ)/3)
    norm_num at h
    exact h.symm
  unfold theta
  rw [hratio,Real.div_rpow (by positivity) ht.le]
  calc
    _ = ((n:ℝ)/m)^((1:ℝ)/3)*((T:ℝ)/(T:ℝ)^((1:ℝ)/3))/(256*Dyadic.upsilon T) := by ring
    _ = _ := by rw [hpow]; ring

end
end Tournament.Lower.RealParameters

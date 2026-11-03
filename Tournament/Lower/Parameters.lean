module

public import Tournament.Lower.DyadicParent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace Tournament.Lower.Parameters

open scoped NNReal

noncomputable section

def sigma (T : ℕ) : ℝ := 1/(16*Dyadic.upsilon T)

def theta (T n m : ℕ) : ℝ :=
  1/(32*Dyadic.upsilon T)*((n:ℝ)/((m:ℝ)*(T:ℝ)))^((1:ℝ)/3)

theorem upsilon_ge_one (T : ℕ) (hT : 1≤T) : 1≤Dyadic.upsilon T := by
  have h := Dyadic.bandCount_le_upsilon T (by omega)
  have hb : (1:ℝ)≤(Dyadic.bandCount T:ℝ) := by
    have : 1≤Dyadic.bandCount T := by unfold Dyadic.bandCount; omega
    exact_mod_cast this
  exact hb.trans h

theorem upsilon_ge_two (T : ℕ) (hT : 2≤T) : 2≤Dyadic.upsilon T := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold Dyadic.upsilon
  apply (le_div_iff₀ hl).mpr
  have hfour : (4:ℝ)≤2*(T:ℝ) := by exact_mod_cast (by omega : 4≤2*T)
  have h := Real.log_le_log (by norm_num : (0:ℝ)<4) hfour
  have heq : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  linarith

theorem sigma_pos (T : ℕ) (hT : 1≤T) : 0<sigma T := by
  have h := upsilon_ge_one T hT
  unfold sigma
  positivity

theorem sigma_inverse_square (T : ℕ) (hT : 1≤T) : (sigma T)^2*(256*Dyadic.upsilon T^2)=1 := by
  have hu : Dyadic.upsilon T≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (upsilon_ge_one T hT))
  unfold sigma
  field_simp
  ring

theorem ratio_bounds (T n m : ℕ) (hT : 1≤T) (hn : n≤T) (hm : 1≤m) :
    0≤(n:ℝ)/((m:ℝ)*(T:ℝ)) ∧ (n:ℝ)/((m:ℝ)*(T:ℝ))≤1 := by
  have ht : (0:ℝ)<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hmr : (1:ℝ)≤(m:ℝ) := by exact_mod_cast hm
  have hnr : (n:ℝ)≤(T:ℝ) := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_le_one (by positivity : 0<(m:ℝ)*(T:ℝ))).mpr
    nlinarith

theorem theta_nonneg (T n m : ℕ) (hT : 1≤T) : 0≤theta T n m := by
  have hu := upsilon_ge_one T hT
  unfold theta
  positivity

theorem theta_pos (T n m : ℕ) (hT : 1≤T) (hn : 1≤n) (hm : 1≤m) : 0<theta T n m := by
  have hu := upsilon_ge_one T hT
  have htr : (0:ℝ)<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hnr : (0:ℝ)<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hmr : (0:ℝ)<(m:ℝ) := by exact_mod_cast (by omega : 0<m)
  unfold theta
  positivity

theorem theta_le_one_sixty_four (T n m : ℕ) (hT : 2≤T) (hn : n≤T) (hm : 1≤m) :
    theta T n m≤1/64 := by
  have hu := upsilon_ge_two T hT
  have hb := ratio_bounds T n m (by omega) hn hm
  have hp : ((n:ℝ)/((m:ℝ)*(T:ℝ)))^((1:ℝ)/3)≤1 := by
    exact Real.rpow_le_one hb.1 hb.2 (by norm_num)
  unfold theta
  have hinv : 1/(32*Dyadic.upsilon T)≤1/64 := by
    apply (div_le_iff₀ (by nlinarith : 0<32*Dyadic.upsilon T)).mpr
    nlinarith
  calc
    _ ≤ (1/(32*Dyadic.upsilon T))*1 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := by simpa only [mul_one] using hinv

theorem theta_cube_identity (T n m : ℕ) (hT : 1≤T) (hm : 1≤m) :
    1024*(m:ℝ)*Dyadic.upsilon T^3*(theta T n m)^3*(T:ℝ)=(n:ℝ)/32 := by
  have hu : Dyadic.upsilon T≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (upsilon_ge_one T hT))
  have htr : (T:ℝ)≠0 := by exact_mod_cast (by omega : T≠0)
  have hmr : (m:ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
  have hc : (((n:ℝ)/((m:ℝ)*(T:ℝ)))^((1:ℝ)/3))^3=(n:ℝ)/((m:ℝ)*(T:ℝ)) := by
    simpa [one_div] using Real.rpow_inv_natCast_pow
      (show 0≤(n:ℝ)/((m:ℝ)*(T:ℝ)) by positivity) (by decide : (3:ℕ)≠0)
  unfold theta
  rw [mul_pow,hc]
  field_simp
  ring

theorem theta_time_identity (T n m : ℕ) (hT : 1≤T) (hm : 1≤m) :
    theta T n m*(T:ℝ)/8=
      (T:ℝ)^((2:ℝ)/3)*((n:ℝ)/(m:ℝ))^((1:ℝ)/3)/(256*Dyadic.upsilon T) := by
  have ht : (0:ℝ)<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
  have hu : Dyadic.upsilon T≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (upsilon_ge_one T hT))
  have hratio : (n:ℝ)/((m:ℝ)*(T:ℝ))=((n:ℝ)/(m:ℝ))/(T:ℝ) := by ring
  have hpow : (T:ℝ)/(T:ℝ)^((1:ℝ)/3)=(T:ℝ)^((2:ℝ)/3) := by
    have h := Real.rpow_sub ht (1:ℝ) ((1:ℝ)/3)
    norm_num at h
    exact h.symm
  unfold theta
  rw [hratio,Real.div_rpow (by positivity) ht.le]
  calc
    _ = ((n:ℝ)/(m:ℝ))^((1:ℝ)/3)*((T:ℝ)/(T:ℝ)^((1:ℝ)/3))/(256*Dyadic.upsilon T) := by ring
    _ = _ := by rw [hpow]; ring

end
end Tournament.Lower.Parameters

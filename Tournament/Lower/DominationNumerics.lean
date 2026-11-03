module

public import Tournament.Graphs.FewObservers
public import Tournament.Lower.Parameters

@[expose] public section

namespace Tournament.Lower.Domination

noncomputable section

def logCard (K : ℕ) : ℝ := 1+Real.log (K:ℝ)

theorem logCard_eq (K : ℕ) (hK : 2≤K) :
    logCard K=Real.log (Real.exp 1*(K:ℝ)) := by
  have hK0 : (K:ℝ)≠0 := by exact_mod_cast (by omega : K≠0)
  rw [Real.log_mul (Real.exp_ne_zero _) hK0,Real.log_exp]
  rfl

theorem logCard_ge_one (K : ℕ) (hK : 2≤K) : 1≤logCard K := by
  dsimp [logCard]
  linarith [Upper.Tuning.log_card_lower hK]

theorem small_ratio_le_eight (x γ T : ℝ) (hx : 0<x) (hγ : γ≤32*(x-1)) :
    min γ T/x^2≤8 := by
  apply (div_le_iff₀ (sq_pos_of_pos hx)).mpr
  have hmin := min_le_left γ T
  nlinarith [sq_nonneg (x-2)]

theorem truncated_size (γ s T c : ℝ) (hc : 1≤c) (hT : 0≤T) (hs : γ/c≤s) :
    min γ T/c≤min s T := by
  have hc0 : 0<c := by linarith
  apply le_min
  · exact (div_le_div_of_nonneg_right (min_le_left γ T) hc0.le).trans hs
  · exact (div_le_div_of_nonneg_right (min_le_right γ T) hc0.le).trans
      ((div_le_iff₀ hc0).mpr (by nlinarith))

theorem root_cube (x : ℝ) (hx : 0≤x) : (x^((1:ℝ)/3))^3=x := by
  simpa [one_div] using Real.rpow_inv_natCast_pow hx (by decide : (3:ℕ)≠0)

theorem quarter_root_le (A B : ℝ) (hA : 0≤A) (hB : 0≤B) (hAB : A≤16*B) :
    A^((1:ℝ)/3)/4≤B^((1:ℝ)/3) := by
  apply (pow_le_pow_iff_left₀ (by positivity : 0≤A^((1:ℝ)/3)/4)
    (by positivity : 0≤B^((1:ℝ)/3)) (by decide : (3:ℕ)≠0)).mp
  rw [div_pow,root_cube A hA,root_cube B hB]
  norm_num
  linarith

theorem small_max_root_le_two (A : ℝ) (hA : A≤8) :
    (max 1 A)^((1:ℝ)/3)≤2 := by
  apply (pow_le_pow_iff_left₀ (by positivity : 0≤(max 1 A)^((1:ℝ)/3))
    (by norm_num : (0:ℝ)≤2) (by decide : (3:ℕ)≠0)).mp
  rw [root_cube _ (le_trans (by norm_num : (0:ℝ)≤1) (le_max_left _ _))]
  calc
    _ ≤ 8 := max_le (by norm_num) hA
    _ = _ := by norm_num

theorem truncated_ratio (γ s T x : ℝ) (hx : 0<x)
    (hMin : min γ T/(16*x)≤min s T) : min γ T/x^2≤16*(min s T/x) := by
  apply (div_le_iff₀ (sq_pos_of_pos hx)).mpr
  calc
    _ ≤ min s T*(16*x) := (div_le_iff₀ (by positivity : 0<16*x)).mp hMin
    _ = _ := by field_simp

end
end Tournament.Lower.Domination

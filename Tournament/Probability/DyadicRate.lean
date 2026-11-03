module

public import Tournament.Foundations.Centering
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Tournament.DyadicRate

open scoped BigOperators

noncomputable section

def base (m : ℕ) : ℝ := (1/2)^m

def rate (m : ℕ) (j : Fin (m+1)) : ℝ := base m * 2^j.val

def weight (m : ℕ) (j : Fin (m+1)) : ℝ :=
  if j.val < m then (1/2)^(j.val+1) else base m

theorem geometric_partition (m : ℕ) :
    (∑ j : Fin m, (1/2:ℝ)^(j.val+1)) + (1/2:ℝ)^m = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [pow_succ (1/2:ℝ) m]
    linarith

def law (m : ℕ) : ProbabilityVector (Fin (m+1)) where
  weight := weight m
  nonneg j := by unfold weight base; split <;> positivity
  sum_eq_one := by
    rw [Fin.sum_univ_castSucc]
    have hfirst : (∑ j : Fin m, weight m j.castSucc) = ∑ j : Fin m, (1/2:ℝ)^(j.val+1) := by
      apply Finset.sum_congr rfl
      intro j _
      exact ite_eq_left j.isLt
    rw [hfirst]
    simp only [weight, Fin.val_last, Nat.lt_irrefl, ite_false, base]
    exact geometric_partition m

theorem base_pos (m : ℕ) : 0 < base m := by unfold base; positivity

theorem base_eq_inv_pow (m : ℕ) : base m = ((2:ℝ)^m)⁻¹ := by
  simp [base, one_div, inv_pow]

theorem base_mul_pow (m : ℕ) : base m*(2:ℝ)^m = 1 := by
  unfold base
  rw [← mul_pow]
  norm_num

theorem rate_pos (m : ℕ) (j : Fin (m+1)) : 0 < rate m j := by
  unfold rate
  exact mul_pos (base_pos m) (by positivity)

theorem base_le_rate (m : ℕ) (j : Fin (m+1)) : base m ≤ rate m j := by
  have hp : (1:ℝ) ≤ 2^j.val := one_le_pow₀ (by norm_num)
  have h := mul_le_mul_of_nonneg_left hp (le_of_lt (base_pos m))
  unfold rate
  simpa only [mul_one] using h

theorem rate_le_one (m : ℕ) (j : Fin (m+1)) : rate m j ≤ 1 := by
  have hp : (2:ℝ)^j.val ≤ 2^m := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ j.isLt)
  calc
    rate m j ≤ base m*2^m := mul_le_mul_of_nonneg_left hp (le_of_lt (base_pos m))
    _ = 1 := base_mul_pow m

theorem rate_last (m : ℕ) : rate m (Fin.last m) = 1 := base_mul_pow m

theorem weight_last (m : ℕ) : weight m (Fin.last m) = base m := by
  simp [weight]

theorem weight_mul_rate (m : ℕ) (j : Fin (m+1)) (hj : j.val < m) :
    weight m j*rate m j = base m/2 := by
  have hp : (1/2:ℝ)^(j.val+1)*(2:ℝ)^j.val = 1/2 := by
    rw [pow_succ]
    calc
      _ = ((1/2:ℝ)^j.val * 2^j.val)*(1/2) := by ring
      _ = 1/2 := by rw [← mul_pow]; norm_num
  unfold weight rate
  rw [ite_eq_left hj]
  calc
    _ = base m*((1/2:ℝ)^(j.val+1)*2^j.val) := by ring
    _ = base m/2 := by rw [hp]; ring

theorem weight_eq_base_div (m : ℕ) (j : Fin (m+1)) (hj : j.val < m) :
    law m j = base m/(2*rate m j) := by
  apply (eq_div_iff (ne_of_gt (mul_pos (by norm_num) (rate_pos m j)))).mpr
  have h := weight_mul_rate m j hj
  change weight m j*(2*rate m j) = base m
  linarith

theorem mean_rate (m : ℕ) : (law m).mean (rate m) = base m*(1+(m:ℝ)/2) := by
  change (∑ j, weight m j*rate m j) = _
  rw [Fin.sum_univ_castSucc]
  have hfirst : (∑ j : Fin m, weight m j.castSucc*rate m j.castSucc) = ∑ _j : Fin m, base m/2 := by
    exact Finset.sum_congr rfl (fun j _ ↦ weight_mul_rate m j.castSucc j.isLt)
  rw [hfirst, weight_last, rate_last, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end
end Tournament.DyadicRate

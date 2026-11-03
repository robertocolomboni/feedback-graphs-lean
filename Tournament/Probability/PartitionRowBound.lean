module

public import Tournament.Probability.GeometricPartition
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

namespace Tournament.GeometricPartition

open scoped BigOperators Classical

noncomputable section

theorem geometric_sum_le {χ : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ < 1) (h : ℕ) :
    (∑ t ∈ Finset.range h, χ^t) ≤ 1/(1-χ) := by
  apply (le_div_iff₀ (sub_pos.mpr hχ1)).mpr
  rw [geom_sum_mul_of_le_one (le_of_lt hχ1)]
  linarith [pow_nonneg hχ h]

theorem row_sum_le {χ : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ < 1) (h t : ℕ) (ht : t<h) :
    (∑ u ∈ Finset.range h, χ^(Nat.dist t u)) ≤ 2/(1-χ) := by
  have heq : h=(t+1)+(h-(t+1)) := by omega
  conv_lhs => rw [heq,Finset.sum_range_add]
  have hhead : (∑ u ∈ Finset.range (t+1), χ^(Nat.dist t u)) = ∑ u ∈ Finset.range (t+1), χ^u := by
    have hd : (∑ u ∈ Finset.range (t+1), χ^(Nat.dist t u)) =
        ∑ u ∈ Finset.range (t+1), χ^(t-u) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Nat.dist_eq_sub_of_le_right (by have := Finset.mem_range.mp hu; omega)]
    rw [hd]
    simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun u ↦ χ^u) (t+1)
  have htail : (∑ u ∈ Finset.range (h-(t+1)), χ^(Nat.dist t ((t+1)+u))) ≤ 1/(1-χ) := by
    calc
      _ ≤ ∑ u ∈ Finset.range (h-(t+1)), χ^u := by
        apply Finset.sum_le_sum
        intro u _
        have hd : Nat.dist t ((t+1)+u)=u+1 := by
          rw [Nat.dist_eq_sub_of_le (by omega)]
          omega
        rw [hd,pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hχ u) (le_of_lt hχ1)
      _ ≤ _ := geometric_sum_le hχ hχ1 (h-(t+1))
  rw [hhead]
  have hfirst := geometric_sum_le hχ hχ1 (t+1)
  have htwo : 2/(1-χ)=1/(1-χ)+1/(1-χ) := by ring
  rw [htwo]
  exact add_le_add hfirst htail

theorem quadratic_le_diagonal {χ : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ < 1)
    (y : ℕ → ℝ) (offset h : ℕ) :
    quadratic χ y offset h ≤ (2/(1-χ))*(∑ t ∈ Finset.range h, y (offset+t)^2) := by
  let B : ℝ := ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h, χ^(Nat.dist t u)*y (offset+t)^2
  let C : ℝ := ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h, χ^(Nat.dist t u)*y (offset+u)^2
  have hdom : quadratic χ y offset h ≤ (B+C)/2 := by
    have hterm : quadratic χ y offset h ≤
        ∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
          (χ^(Nat.dist t u)*y (offset+t)^2+χ^(Nat.dist t u)*y (offset+u)^2)/2 := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro u _
      have hs := mul_nonneg (pow_nonneg hχ (Nat.dist t u))
        (sq_nonneg (y (offset+t)-y (offset+u)))
      nlinarith
    calc
      _ ≤ _ := hterm
      _ = (B+C)/2 := by
        simp_rw [← Finset.sum_div]
        simp only [Finset.sum_add_distrib]
        rfl
  have hsym : C=B := by
    dsimp only [C,B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    rw [Nat.dist_comm]
  have hrow : B ≤ (2/(1-χ))*(∑ t ∈ Finset.range h, y (offset+t)^2) := by
    calc
      B = ∑ t ∈ Finset.range h, (∑ u ∈ Finset.range h, χ^(Nat.dist t u))*y (offset+t)^2 := by
        apply Finset.sum_congr rfl
        intro t _
        exact (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ t ∈ Finset.range h, (2/(1-χ))*y (offset+t)^2 := by
        apply Finset.sum_le_sum
        intro t ht
        exact mul_le_mul_of_nonneg_right (row_sum_le hχ hχ1 h t (Finset.mem_range.mp ht)) (sq_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hsym] at hdom
  linarith

theorem quadratic_zero (y : ℕ → ℝ) (offset h : ℕ) :
    quadratic 0 y offset h = ∑ t ∈ Finset.range h, y (offset+t)^2 := by
  rw [quadratic_eq_diagonal_pairs]
  have hz : (∑ t ∈ Finset.range h, ∑ u ∈ Finset.range h,
      if t<u then (0:ℝ)^(u-t)*y (offset+t)*y (offset+u) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro u _
    by_cases htu : t<u
    · rw [ite_eq_left htu,zero_pow (by omega : u-t ≠ 0),zero_mul,zero_mul]
    · rw [ite_eq_right htu]
  rw [hz,mul_zero,add_zero]

theorem quadratic_le_zero_correlation {χ : ℝ} (hχ : 0 ≤ χ) (hχ1 : χ < 1)
    (y : ℕ → ℝ) (offset h : ℕ) :
    quadratic χ y offset h ≤ (2/(1-χ))*quadratic 0 y offset h := by
  rw [quadratic_zero]
  exact quadratic_le_diagonal hχ hχ1 y offset h

end
end Tournament.GeometricPartition

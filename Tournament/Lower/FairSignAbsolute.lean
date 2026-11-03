module

public import Tournament.Lower.FairSignMoments
public import Tournament.Probability.FiniteMoments
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace Tournament.Lower.FairSigns

open MeasureTheory
open scoped Classical BigOperators
noncomputable section

theorem absolute_sum_lower (T : ℕ) (hT : 1≤T) :
    Real.sqrt ((T:ℝ)/3)≤∫ ω, |∑ t : Fin T, sign t ω| ∂law T := by
  let M := ∫ ω, |∑ t : Fin T, sign t ω| ∂law T
  have hM : 0≤M := integral_nonneg (fun _ ↦ abs_nonneg _)
  have hHolder := Tournament.Probability.second_absolute_fourth (law T) (fun ω ↦ ∑ t : Fin T, sign t ω)
  rw [sum_second,sum_fourth] at hHolder
  have hFourth : 3*(T:ℝ)^2-2*(T:ℝ)≤3*(T:ℝ)^2 := by nlinarith [Nat.cast_nonneg T (α := ℝ)]
  have hFourth0 : 0≤3*(T:ℝ)^2-2*(T:ℝ) := by
    rw [← sum_fourth]
    exact integral_nonneg (fun _ ↦ by positivity)
  have hPower := Real.rpow_le_rpow hFourth0 hFourth (by norm_num : (0:ℝ)≤1/3)
  have hLarge : (T:ℝ)≤M^((2:ℝ)/3)*(3*(T:ℝ)^2)^((1:ℝ)/3) :=
    hHolder.trans (mul_le_mul_of_nonneg_left hPower (by positivity))
  have hCube := pow_le_pow_left₀ (Nat.cast_nonneg T) hLarge 3
  rw [mul_pow,← Real.rpow_mul_natCast hM,← Real.rpow_mul_natCast (by positivity : (0:ℝ)≤3*(T:ℝ)^2)] at hCube
  norm_num at hCube
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (by omega : 0<T)
  have hSquare : (T:ℝ)/3≤M^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hT0)).mp
    nlinarith [hCube]
  exact Real.sqrt_le_iff.mpr ⟨hM,hSquare⟩

theorem half_absolute_sum_lower (T : ℕ) (hT : 1≤T) :
    Real.sqrt (T:ℝ)/4≤(∫ ω, |∑ t : Fin T, sign t ω| ∂law T)/2 := by
  have h := absolute_sum_lower T hT
  have hT0 : (0:ℝ)≤(T:ℝ) := Nat.cast_nonneg T
  have hS1 := Real.sq_sqrt hT0
  have hS2 := Real.sq_sqrt (show (0:ℝ)≤(T:ℝ)/3 by positivity)
  have hCompare : Real.sqrt (T:ℝ)≤2*Real.sqrt ((T:ℝ)/3) := by
    apply (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity : (0:ℝ)≤2*Real.sqrt ((T:ℝ)/3))
      (by decide : (2:ℕ)≠0)).mp
    nlinarith
  linarith

end
end Tournament.Lower.FairSigns

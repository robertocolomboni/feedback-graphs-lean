module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Tournament.Probability

open MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem finite_memLp (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (p : ℝ≥0∞) : MemLp f p μ := by
  apply MemLp.of_bound (Measurable.of_discrete (f := f)).aestronglyMeasurable (∑ ω, ‖f ω‖)
  exact Filter.Eventually.of_forall (fun ω ↦
    Finset.single_le_sum (fun x _ ↦ norm_nonneg (f x)) (Finset.mem_univ ω))

theorem second_absolute_fourth (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) :
    (∫ ω, (f ω)^2 ∂μ)≤(∫ ω, |f ω| ∂μ)^((2:ℝ)/3)*(∫ ω, (f ω)^4 ∂μ)^((1:ℝ)/3) := by
  let F : Ω → ℝ := fun ω ↦ |f ω|^((2:ℝ)/3)
  let G : Ω → ℝ := fun ω ↦ |f ω|^((4:ℝ)/3)
  have hpq : Real.HolderConjugate (3/2:ℝ) 3 := Real.holderConjugate_iff.mpr (by norm_num)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := F) (g := G) (Filter.Eventually.of_forall (fun _ ↦ by dsimp [F]; positivity))
    (Filter.Eventually.of_forall (fun _ ↦ by dsimp [G]; positivity))
    (finite_memLp μ F _) (finite_memLp μ G _)
  have hProduct (ω : Ω) : F ω*G ω=(f ω)^2 := by
    dsimp [F,G]
    rw [← Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num : (0:ℝ)≤2/3) (by norm_num : (0:ℝ)≤4/3)]
    norm_num
  have hFirst (ω : Ω) : (F ω)^((3:ℝ)/2)=|f ω| := by
    dsimp [F]
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hFourth (ω : Ω) : (G ω)^(3:ℝ)=(f ω)^4 := by
    dsimp [G]
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
    calc
      _ = (|f ω|^2)^2 := by ring
      _ = ((f ω)^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  have hProductInt : (∫ ω, F ω*G ω ∂μ)=∫ ω, (f ω)^2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hProduct)
  have hFirstInt : (∫ ω, (F ω)^((3:ℝ)/2) ∂μ)=∫ ω, |f ω| ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hFirst)
  have hFourthInt : (∫ ω, (G ω)^(3:ℝ) ∂μ)=∫ ω, (f ω)^4 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hFourth)
  rw [hProductInt,hFirstInt,hFourthInt] at hH
  norm_num at hH
  exact hH

end
end Tournament.Probability

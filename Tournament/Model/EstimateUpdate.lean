module

public import Tournament.Foundations.Centering
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

namespace Tournament.Model

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def truncateEstimate (η : ℝ) (z : ι → ℝ) : ι → ℝ :=
  if η*‖z‖ ≤ 1 then z else 0

theorem exponentialNormalizer_pos (π : ProbabilityVector ι) (η : ℝ) (z : ι → ℝ) :
    0 < π.mean (fun i ↦ Real.exp (-η*z i)) := by
  have hweight : ∃ i, 0 < π i := by
    by_contra h
    have hz : ∀ i, π i=0 := by
      intro i
      exact le_antisymm (not_lt.mp (fun hi ↦ h ⟨i,hi⟩)) (π.nonneg i)
    have hsum := π.sum_eq_one
    simp only [hz,Finset.sum_const_zero] at hsum
    norm_num at hsum
  unfold ProbabilityVector.mean
  apply Finset.sum_pos' (fun i _ ↦ mul_nonneg (π.nonneg i) (le_of_lt (Real.exp_pos _)))
  rcases hweight with ⟨i,hi⟩
  exact ⟨i,Finset.mem_univ i,mul_pos hi (Real.exp_pos _)⟩

def exponentialUpdate (π : ProbabilityVector ι) (η : ℝ) (z : ι → ℝ) : ProbabilityVector ι where
  weight i := π i*Real.exp (-η*z i)/π.mean (fun j ↦ Real.exp (-η*z j))
  nonneg i := div_nonneg (mul_nonneg (π.nonneg i) (le_of_lt (Real.exp_pos _)))
    (le_of_lt (exponentialNormalizer_pos π η z))
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (exponentialNormalizer_pos π η z))

end
end Tournament.Model

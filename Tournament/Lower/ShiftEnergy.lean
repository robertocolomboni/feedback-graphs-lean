module

public import Tournament.Lower.Environments
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace Tournament.Lower

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*}

def shiftEnergy {S : Finset ι} (x : Coordinate S → ℝ) : ℝ := ∑ c, (x c)^2

theorem shift_energy_candidate (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ)
    (j : S) (a : ι) (sign : ℝ) (hsign : sign^2=1) :
    shiftEnergy (shift E θ (some j) a sign)=θ^2*(if E a j then 1 else 0) := by
  by_cases he : E a j
  · by_cases ha : a∈S
    · simp [shiftEnergy,shift,ha,observesCandidate,he]
    · simp [shiftEnergy,shift,ha,observesCandidate,he,mul_pow,hsign]
  · simp [shiftEnergy,shift,observesCandidate,he]

theorem shift_energy_sum (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ)
    (a : ι) (sign : ℝ) (hsign : sign^2=1) :
    (∑ j : S, shiftEnergy (shift E θ (some j) a sign))=θ^2*((observed E S a).card:ℝ) := by
  simp only [shift_energy_candidate E θ _ a sign hsign,← Finset.mul_sum]
  congr 1
  rw [Finset.sum_coe_sort S (fun j ↦ if E a j then (1:ℝ) else 0)]
  simp [observed]

theorem shiftEnergy_sub_le {S : Finset ι} (x y : Coordinate S → ℝ) :
    shiftEnergy (x-y)≤2*shiftEnergy x+2*shiftEnergy y := by
  unfold shiftEnergy
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (x c+y c)]

theorem same_member_shift (E : ι → ι → Prop) {S : Finset ι} (θ : ℝ)
    (j : Coordinate S) {a : ι} (ha : a∈S) (sign sign' : ℝ) :
    shift E θ j a sign=shift E θ j a sign' := by
  funext c
  simp only [shift,ite_eq_left ha]

end
end Tournament.Lower

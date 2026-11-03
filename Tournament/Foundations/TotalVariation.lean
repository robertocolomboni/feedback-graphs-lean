module

public import Tournament.Foundations.Centering
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Tournament.ProbabilityVector

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem mean_sub_le_half_range (p w : ProbabilityVector ι) (f : ι → ℝ) (h : ℝ)
    (hf : ∀ i, 0≤f i ∧ f i≤h) :
    p.mean f-w.mean f≤(h/2)*(∑ i, |p i-w i|) := by
  have hsum : (∑ i, (p i-w i))=0 := by rw [Finset.sum_sub_distrib,p.sum_eq_one,w.sum_eq_one]; ring
  have hid : p.mean f-w.mean f=∑ i, (p i-w i)*(f i-h/2) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hsum,zero_mul,sub_zero]
    simp [mean,sub_mul,Finset.sum_sub_distrib]
  rw [hid,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hcenter : |f i-h/2|≤h/2 := abs_le.mpr ⟨by linarith [(hf i).1],by linarith [(hf i).2]⟩
  calc
    _ ≤ |p i-w i| * |f i-h/2| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ |p i-w i| * (h/2) := mul_le_mul_of_nonneg_left hcenter (abs_nonneg _)
    _ = _ := by ring

end
end Tournament.ProbabilityVector

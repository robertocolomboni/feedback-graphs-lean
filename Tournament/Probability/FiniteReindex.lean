module

public import Tournament.Foundations.Centering

@[expose] public section

namespace Tournament.ProbabilityVector

open scoped BigOperators

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

def reindex (μ : ProbabilityVector α) (e : α ≃ β) : ProbabilityVector β where
  weight b := μ (e.symm b)
  nonneg b := μ.nonneg (e.symm b)
  sum_eq_one := by
    calc
      (∑ b, μ (e.symm b)) = ∑ a, μ a := Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)
      _ = 1 := μ.sum_eq_one

theorem reindex_mean (μ : ProbabilityVector α) (e : α ≃ β) (f : β → ℝ) :
    (μ.reindex e).mean f=μ.mean (fun a ↦ f (e a)) := by
  unfold mean reindex
  apply Fintype.sum_equiv e.symm
  intro b
  change μ (e.symm b)*f b=μ (e.symm b)*f (e (e.symm b))
  rw [e.apply_symm_apply]

end
end Tournament.ProbabilityVector

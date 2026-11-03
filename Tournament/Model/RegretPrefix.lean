module

public import Tournament.Model.Regret

@[expose] public section

namespace Tournament.Model

variable {ι : Type*}

theorem switchCount_eq_of_prefix [DecidableEq ι] (T : ℕ) (X Y : ℕ → ι)
    (h : ∀ t<T, X t=Y t) : switchCount T X=switchCount T Y := by
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  rw [h (t+1) (by omega),h t (by omega)]

theorem accumulatedLoss_eq_of_prefix (T : ℕ) (loss : ℕ → ι → ℝ) (X Y : ℕ → ι)
    (h : ∀ t<T, X t=Y t) : accumulatedLoss T loss X=accumulatedLoss T loss Y := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [h t (Finset.mem_range.mp ht)]

theorem pathRegret_eq_of_action_prefix [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (T : ℕ) (loss : ℕ → ι → ℝ) (X Y : ℕ → ι) (h : ∀ t<T, X t=Y t) :
    pathRegret T loss X=pathRegret T loss Y := by
  unfold pathRegret
  rw [accumulatedLoss_eq_of_prefix T loss X Y h,switchCount_eq_of_prefix T X Y h]

end Tournament.Model

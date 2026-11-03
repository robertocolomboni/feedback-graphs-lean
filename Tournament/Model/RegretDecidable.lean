module

public import Tournament.Model.Regret

@[expose] public section

namespace Tournament.Model

variable {ι : Type*}

theorem switchCount_decidableEq (first second : DecidableEq ι) (T : ℕ) (X : ℕ → ι) :
    @switchCount ι first T X=@switchCount ι second T X := by
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : X (t+1)=X t
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

theorem pathRegret_decidableEq [Fintype ι] [Nonempty ι] (first second : DecidableEq ι)
    (T : ℕ) (loss : ℕ → ι → ℝ) (X : ℕ → ι) :
    (letI := first; pathRegret T loss X)=(letI := second; pathRegret T loss X) := by
  unfold pathRegret
  rw [switchCount_decidableEq first second]

end Tournament.Model

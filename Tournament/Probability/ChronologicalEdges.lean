module

public import Tournament.Probability.ChronologicalPath
public import Tournament.Probability.EdgeConditioning

@[expose] public section

namespace Tournament.FinitePath

open scoped BigOperators

variable {ι : Type*}

noncomputable section

theorem firstState_eq_stateAt (n : ℕ) (hist : History ι n) : firstState n hist = stateAt n hist 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateAt_prefix n hist 0 (Nat.zero_le n)]
    exact ih hist.1

theorem stateAt_constant (i : ι) (n t : ℕ) : stateAt n (constantHistory i n) t = i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (if t ≤ n then stateAt n (constantHistory i n) t else i) = i
    rw [ih]
    split <;> rfl

theorem firstState_constant (i : ι) (n : ℕ) : firstState n (constantHistory i n) = i := by
  rw [firstState_eq_stateAt, stateAt_constant]

theorem stateAt_prepend_zero (i : ι) (n : ℕ) (hist : History ι n) :
    stateAt (n+1) (prepend i n hist) 0 = i := by
  rw [← firstState_eq_stateAt, firstState_prepend]

theorem stateAt_prepend_succ (i : ι) (n : ℕ) (hist : History ι n) (t : ℕ) (ht : t ≤ n) :
    stateAt (n+1) (prepend i n hist) (t+1) = stateAt n hist t := by
  induction n generalizing t with
  | zero =>
    have ht0 : t=0 := Nat.eq_zero_of_le_zero ht
    subst t
    rfl
  | succ n ih =>
    by_cases htn : t ≤ n
    · rw [stateAt_prefix (n+1) (prepend i (n+1) hist) (t+1) (by omega), stateAt_prefix n hist t htn]
      exact ih hist.1 t htn
    · have ht' : t=n+1 := by omega
      subst t
      rw [stateAt_last, lastState_prepend, stateAt_last]

theorem transition_prepend_zero (d : ι → ι → ℝ) (i : ι) (n : ℕ) (hist : History ι n) :
    transitionValue d (n+1) (prepend i n hist) 0 = d i (firstState n hist) := by
  unfold transitionValue
  rw [stateAt_prepend_zero, stateAt_prepend_succ i n hist 0 (Nat.zero_le n), ← firstState_eq_stateAt]

theorem transition_prepend_succ (d : ι → ι → ℝ) (i : ι) (n : ℕ) (hist : History ι n)
    (t : ℕ) (ht : t < n) :
    transitionValue d (n+1) (prepend i n hist) (t+1) = transitionValue d n hist t := by
  unfold transitionValue
  rw [stateAt_prepend_succ i n hist t (by omega), stateAt_prepend_succ i n hist (t+1) (by omega)]

theorem edgeTotal_prepend (d : ℕ → ι → ι → ℝ) (i : ι) (n : ℕ) (hist : History ι n) :
    edgeTotal d (n+1) (prepend i n hist) = d 0 i (firstState n hist) + edgeTotal (fun t ↦ d (t+1)) n hist := by
  unfold edgeTotal
  rw [Finset.sum_range_succ', transition_prepend_zero]
  have htail : (∑ t ∈ Finset.range n, transitionValue (d (t+1)) (n+1) (prepend i n hist) (t+1)) =
      ∑ t ∈ Finset.range n, transitionValue (d (t+1)) n hist t := by
    exact Finset.sum_congr rfl (fun t ht ↦ transition_prepend_succ _ i n hist t (Finset.mem_range.mp ht))
  rw [htail, add_comm]

theorem edgeTotal_constant (d : ℕ → ι → ι → ℝ) (i : ι) (hdiag : ∀ t, d t i i=0) (n : ℕ) :
    edgeTotal d n (constantHistory i n) = 0 := by
  simp only [edgeTotal, transitionValue, stateAt_constant, hdiag, Finset.sum_const_zero]

end
end Tournament.FinitePath

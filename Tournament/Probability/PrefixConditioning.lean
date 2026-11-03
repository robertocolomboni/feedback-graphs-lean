module

public import Tournament.Probability.Correlations
public import Tournament.Probability.FiniteConditional

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι]

noncomputable section

namespace ProbabilityVector

def pure (s : ι) : ProbabilityVector ι where
  weight i := if i=s then 1 else 0
  nonneg i := by split <;> norm_num
  sum_eq_one := by simp

theorem pure_mean (s : ι) (f : ι → ℝ) : (pure s).mean f = f s := by
  simp [pure, mean]

end ProbabilityVector

namespace FinitePath

def initialSegment : (n : ℕ) → History ι n → (t : ℕ) → t ≤ n → History ι t
  | 0, i, t, ht => by
      have h : t=0 := Nat.eq_zero_of_le_zero ht
      subst t
      exact i
  | n+1, hist, t, ht => by
      by_cases h : t=n+1
      · exact h.symm ▸ hist
      · exact initialSegment n hist.1 t (by omega)

omit [Fintype ι] in
theorem prefix_self (n : ℕ) (hist : History ι n) : initialSegment n hist n le_rfl = hist := by
  cases n <;> simp [initialSegment]

omit [Fintype ι] in
theorem prefix_succ_of_le (n : ℕ) (hist : History ι n × ι) (t : ℕ) (ht : t ≤ n) :
    initialSegment (n+1) hist t (by omega) = initialSegment n hist.1 t ht := by
  simp only [initialSegment, dite_eq_right (by omega : ¬ t=n+1)]

omit [Fintype ι] in
theorem prefix_prefix (n : ℕ) (hist : History ι n) (t s : ℕ) (ht : t ≤ n) (hs : s ≤ t) :
    initialSegment t (initialSegment n hist t ht) s hs = initialSegment n hist s (le_trans hs ht) := by
  induction n generalizing t s with
  | zero =>
    have ht0 : t=0 := Nat.eq_zero_of_le_zero ht
    have hs0 : s=0 := by omega
    subst t
    subst s
    rfl
  | succ n ih =>
    by_cases ht' : t=n+1
    · subst t
      rw [prefix_self]
    · have htn : t ≤ n := by omega
      have hsn : s ≤ n := by omega
      rw [prefix_succ_of_le n hist t htn, prefix_succ_of_le n hist s hsn]
      exact ih hist.1 t s htn hs

omit [Fintype ι] in
theorem prefix_lastState (n : ℕ) (hist : History ι n) (t : ℕ) (ht : t ≤ n) :
    lastState t (initialSegment n hist t ht) = stateAt n hist t := by
  induction n generalizing t with
  | zero =>
    have ht0 : t=0 := Nat.eq_zero_of_le_zero ht
    subst t
    rfl
  | succ n ih =>
    by_cases ht' : t=n+1
    · subst t
      rw [prefix_self, stateAt_last]
    · have htn : t ≤ n := by omega
      rw [prefix_succ_of_le n hist t htn, stateAt_prefix n hist t htn]
      exact ih hist.1 t htn

omit [Fintype ι] in
theorem stateAt_initialSegment (n : ℕ) (hist : History ι n) (t u : ℕ) (ht : t ≤ n) (hu : u ≤ t) :
    stateAt t (initialSegment n hist t ht) u = stateAt n hist u := by
  calc
    _ = lastState u (initialSegment t (initialSegment n hist t ht) u hu) :=
      (prefix_lastState t (initialSegment n hist t ht) u hu).symm
    _ = lastState u (initialSegment n hist u (le_trans hu ht)) := by rw [prefix_prefix]
    _ = _ := prefix_lastState n hist u (le_trans hu ht)

theorem prefix_future_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (n t u : ℕ) (htu : t ≤ u) (hun : u ≤ n) (a : History ι t → ℝ) (f : ι → ℝ) :
    (law P μ n).mean (fun hist ↦ a (initialSegment n hist t (le_trans htu hun)) * f (stateAt n hist u)) =
      (law P μ t).mean (fun hist ↦ a hist * ((P.act)^[u-t]) f (lastState t hist)) := by
  induction n generalizing t u f with
  | zero =>
    have hu0 : u=0 := Nat.eq_zero_of_le_zero hun
    have ht0 : t=0 := by omega
    subst u
    subst t
    simp only [prefix_self, stateAt_last, Nat.sub_self, Function.iterate_zero, id_eq]
  | succ n ih =>
    by_cases hun' : u ≤ n
    · have htn : t ≤ n := by omega
      change ((law P μ n).joint (fun hist ↦ P.row (lastState n hist))).mean
        (fun hist : History ι n × ι ↦ a (initialSegment (n+1) hist t (by omega)) *
          f (stateAt (n+1) hist u)) = _
      have heq : (fun hist : History ι n × ι ↦ a (initialSegment (n+1) hist t (by omega)) *
          f (stateAt (n+1) hist u)) =
          (fun hist ↦ a (initialSegment n hist.1 t htn) * f (stateAt n hist.1 u)) := by
        funext hist
        rw [prefix_succ_of_le n hist t htn, stateAt_prefix n hist u hun']
      rw [heq, ProbabilityVector.joint_first_mean (law P μ n)
        (fun hist ↦ P.row (lastState n hist))
        (fun hist ↦ a (initialSegment n hist t htn) * f (stateAt n hist u))]
      exact ih t u htu hun' a f
    · have hu' : u=n+1 := by omega
      subst u
      by_cases htn : t ≤ n
      · change ((law P μ n).joint (fun hist ↦ P.row (lastState n hist))).mean
          (fun hist : History ι n × ι ↦ a (initialSegment (n+1) hist t (by omega)) *
            f (stateAt (n+1) hist (n+1))) = _
        rw [ProbabilityVector.joint_mean]
        have heq : (fun hist : History ι n ↦ (P.row (lastState n hist)).mean
            (fun j ↦ a (initialSegment (n+1) (hist,j) t (by omega)) * f (stateAt (n+1) (hist,j) (n+1)))) =
            (fun hist ↦ a (initialSegment n hist t htn) * P.act f (stateAt n hist n)) := by
          funext hist
          simp only [prefix_succ_of_le n (hist, _) t htn, stateAt_last, lastState,
            ProbabilityVector.mean_const_mul]
          rfl
        rw [heq, ih t n htn le_rfl a (P.act f)]
        have hexp : n+1-t = (n-t)+1 := by omega
        rw [hexp, Function.iterate_succ_apply]
      · have ht' : t=n+1 := by omega
        subst t
        simp only [prefix_self, stateAt_last, Nat.sub_self, Function.iterate_zero, id_eq]

end FinitePath
end
end Tournament

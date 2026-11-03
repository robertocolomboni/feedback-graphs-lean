module

public import Tournament.Probability.MarkovConditional
public import Tournament.Probability.ExponentialMoment

@[expose] public section

namespace Tournament.FinitePath

open scoped BigOperators Classical
open AccumulatedMoments FiniteConditional

variable {ι : Type*} [Fintype ι]

noncomputable section

def pastInformation (n s : ℕ) (hist : History ι n) : Fin (n+1) → ι :=
  fun u ↦ stateAt n hist (min u.val (s-1))

omit [Fintype ι] in
theorem pastInformation_increasing (n : ℕ) : IncreasingInformation (pastInformation (ι := ι) n) := by
  intro s t hst hist hist' heq
  funext u
  have hv : min u.val (s-1) < n+1 := lt_of_le_of_lt (Nat.min_le_left _ _) u.isLt
  have h := congrFun heq (⟨min u.val (s-1),hv⟩ : Fin (n+1))
  change stateAt n hist (min (min u.val (s-1)) (t-1)) =
    stateAt n hist' (min (min u.val (s-1)) (t-1)) at h
  have hle : min u.val (s-1) ≤ t-1 := by omega
  rw [Nat.min_eq_left hle] at h
  exact h

def stateObservable (f : ι → ℝ) (n t : ℕ) (hist : History ι n) : ℝ :=
  if t ≤ n then f (stateAt n hist t) else 0

def stateTotal (f : ι → ℝ) (n : ℕ) (hist : History ι n) : ℝ :=
  ∑ t ∈ Finset.range (n+1), f (stateAt n hist t)

omit [Fintype ι] in
theorem stateObservable_adapted (f : ι → ℝ) (n t : ℕ) (ht : t < n+1) :
    DependsOn (pastInformation (ι := ι) n (t+1)) (stateObservable f n t) := by
  intro hist hist' heq
  have htn : t ≤ n := by omega
  have hs := congrFun heq (⟨t,by omega⟩ : Fin (n+1))
  change stateAt n hist (min t (t+1-1)) = stateAt n hist' (min t (t+1-1)) at hs
  have hmin : min t (t+1-1) = t := by omega
  rw [hmin] at hs
  dsimp only [stateObservable]
  rw [ite_eq_left htn, ite_eq_left htn, hs]

omit [Fintype ι] in
theorem sum_stateObservable (f : ι → ℝ) (n : ℕ) (hist : History ι n) :
    (∑ t ∈ Finset.range (n+1), stateObservable f n t hist) = stateTotal f n hist := by
  apply Finset.sum_congr rfl
  intro t ht
  exact ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp ht))

theorem state_sum_exponential_mean_le (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (n : ℕ) (b v : ℝ) (hB : 0 ≤ b+v)
    (hf : ∀ i, f i ≤ b)
    (hfuture : ∀ k, k ≤ n → ∀ i, futureValue P f k i ≤ v)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθB : θ*(b+v) < 1) :
    (law P μ n).mean (fun hist ↦ Real.exp (θ*stateTotal f n hist)) ≤
      1+θ*(law P μ n).mean (stateTotal f n)/(1-θ*(b+v)) := by
  have hnonneg : ∀ t hist, 0 ≤ stateObservable f n t hist := by
    intro t hist
    unfold stateObservable
    split
    · exact hf0 _
    · exact le_rfl
  have hbounded : ∀ t, t<n+1 → ∀ hist, stateObservable f n t hist ≤ b := by
    intro t ht hist
    rw [stateObservable, ite_eq_left (by omega : t ≤ n)]
    exact hf _
  have hcond : ∀ t, t<n+1 → MeanLE (law P μ n) (pastInformation n (t+1))
      (fun hist ↦ ∑ u ∈ Finset.range (n+1), if t<u then stateObservable f n u hist else 0) v := by
    intro t ht
    have htn : t ≤ n := by omega
    have hbase := conditional_future_occupation_le P μ f n t htn v
      (hfuture (n-t) (Nat.sub_le n t))
    have heq : (fun hist : History ι n ↦ ∑ u ∈ Finset.range (n+1),
        if t<u then stateObservable f n u hist else 0) = futurePathSum f n t := by
      funext hist
      rw [futurePathSum_eq_strict_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [stateObservable, ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hu))]
    rw [heq]
    apply meanLE_coarsen (law P μ n) (fun hist ↦ initialSegment n hist t htn)
      (pastInformation n (t+1)) (futurePathSum f n t) v _ hbase
    intro hist hist' hprefix
    funext u
    have hu : min u.val (t+1-1) ≤ t := by omega
    have h := congrArg (fun past ↦ stateAt t past (min u.val (t+1-1))) hprefix
    rw [stateAt_initialSegment n hist t _ htn hu, stateAt_initialSegment n hist' t _ htn hu] at h
    exact h
  have h := accumulated_exponential_mean_le (law P μ n) (pastInformation n)
    (pastInformation_increasing n) (stateObservable f n) (n+1) (stateObservable_adapted f n)
    hnonneg b v hB hbounded hcond θ hθ hθB
  simpa only [sum_stateObservable] using h

end
end Tournament.FinitePath

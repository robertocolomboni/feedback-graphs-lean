module

public import Tournament.Probability.EdgeConditioning
public import Tournament.Probability.MarkovExponential

@[expose] public section

namespace Tournament.FinitePath

open scoped BigOperators Classical
open AccumulatedMoments FiniteConditional

variable {ι : Type*} [Fintype ι]

noncomputable section

def edgeInformation (n s : ℕ) (hist : History ι n) : Fin (n+1) → ι := pastInformation n (s+1) hist

omit [Fintype ι] in
theorem edgeInformation_increasing (n : ℕ) : IncreasingInformation (edgeInformation (ι := ι) n) := by
  intro s t hst hist hist' heq
  exact pastInformation_increasing n (s+1) (t+1) (by omega) hist hist' heq

def edgeObservable (d : ℕ → ι → ι → ℝ) (n t : ℕ) (hist : History ι n) : ℝ :=
  if t<n then transitionValue (d t) n hist t else 0

omit [Fintype ι] in
theorem edgeObservable_adapted (d : ℕ → ι → ι → ℝ) (n t : ℕ) (ht : t<n) :
    DependsOn (edgeInformation (ι := ι) n (t+1)) (edgeObservable d n t) := by
  intro hist hist' heq
  have ha := congrFun heq (⟨t,by omega⟩ : Fin (n+1))
  have hb := congrFun heq (⟨t+1,by omega⟩ : Fin (n+1))
  change stateAt n hist (min t (t+1+1-1)) = stateAt n hist' (min t (t+1+1-1)) at ha
  change stateAt n hist (min (t+1) (t+1+1-1)) = stateAt n hist' (min (t+1) (t+1+1-1)) at hb
  have hmina : min t (t+1+1-1)=t := by omega
  have hminb : min (t+1) (t+1+1-1)=t+1 := by omega
  rw [hmina] at ha
  rw [hminb] at hb
  dsimp only [edgeObservable]
  rw [ite_eq_left ht, ite_eq_left ht]
  unfold transitionValue
  rw [ha,hb]

omit [Fintype ι] in
theorem sum_edgeObservable (d : ℕ → ι → ι → ℝ) (n : ℕ) (hist : History ι n) :
    (∑ t ∈ Finset.range n, edgeObservable d n t hist) = edgeTotal d n hist := by
  exact Finset.sum_congr rfl (fun t ht ↦ ite_eq_left (Finset.mem_range.mp ht))

theorem edge_sum_exponential_mean_le (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (d : ℕ → ι → ι → ℝ) (hd0 : ∀ t i j, 0 ≤ d t i j) (n : ℕ) (b v : ℝ) (hB : 0 ≤ b+v)
    (hbound : ∀ t i j, d t i j ≤ b)
    (hfuture : ∀ s, s ≤ n → ∀ i, futureEdgeValue P d s (n-s) i ≤ v)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθB : θ*(b+v)<1) :
    (law P μ n).mean (fun hist ↦ Real.exp (θ*edgeTotal d n hist)) ≤
      1+θ*(law P μ n).mean (edgeTotal d n)/(1-θ*(b+v)) := by
  have hnonneg : ∀ t hist, 0 ≤ edgeObservable d n t hist := by
    intro t hist
    unfold edgeObservable
    split
    · exact hd0 t _ _
    · exact le_rfl
  have hbounded : ∀ t, t<n → ∀ hist, edgeObservable d n t hist ≤ b := by
    intro t ht hist
    rw [edgeObservable, ite_eq_left ht]
    exact hbound t _ _
  have hcond : ∀ t, t<n → MeanLE (law P μ n) (edgeInformation n (t+1))
      (fun hist ↦ ∑ u ∈ Finset.range n, if t<u then edgeObservable d n u hist else 0) v := by
    intro t ht
    have hs : t+1 ≤ n := by omega
    have hbase := conditional_future_edge_le P μ d n (t+1) hs v (hfuture (t+1) hs)
    have heq : (fun hist : History ι n ↦ ∑ u ∈ Finset.range n,
        if t<u then edgeObservable d n u hist else 0) = futureEdgePathSum d n (t+1) := by
      funext hist
      rw [futureEdgePathSum_eq_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [edgeObservable, ite_eq_left (Finset.mem_range.mp hu)]
      by_cases h : t<u
      · rw [ite_eq_left h, ite_eq_left (by omega : t+1 ≤ u)]
      · rw [ite_eq_right h, ite_eq_right (by omega : ¬ t+1 ≤ u)]
    rw [heq]
    apply meanLE_coarsen (law P μ n) (fun hist ↦ initialSegment n hist (t+1) hs)
      (edgeInformation n (t+1)) (futureEdgePathSum d n (t+1)) v _ hbase
    intro hist hist' hprefix
    funext u
    have hu : min u.val (t+1+1-1) ≤ t+1 := by omega
    have h := congrArg (fun past ↦ stateAt (t+1) past (min u.val (t+1+1-1))) hprefix
    rw [stateAt_initialSegment n hist (t+1) _ hs hu, stateAt_initialSegment n hist' (t+1) _ hs hu] at h
    exact h
  have h := accumulated_exponential_mean_le (law P μ n) (edgeInformation n)
    (edgeInformation_increasing n) (edgeObservable d n) n (edgeObservable_adapted d n)
    hnonneg b v hB hbounded hcond θ hθ hθB
  simpa only [sum_edgeObservable] using h

end
end Tournament.FinitePath

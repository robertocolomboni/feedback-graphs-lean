module

public import Tournament.Probability.MarkovConditional

@[expose] public section

namespace Tournament.FinitePath

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι]

noncomputable section

def edgeTotal (d : ℕ → ι → ι → ℝ) (n : ℕ) (hist : History ι n) : ℝ :=
  ∑ u ∈ Finset.range n, transitionValue (d u) n hist u

theorem prefix_edge_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (n t u : ℕ) (htu : t ≤ u) (hun : u < n) (a : History ι t → ℝ) (d : ι → ι → ℝ) :
    (law P μ n).mean (fun hist ↦ a (initialSegment n hist t (by omega))*transitionValue d n hist u) =
      (law P μ t).mean (fun hist ↦ a hist * ((P.act)^[u-t])
        (fun i ↦ (P.row i).mean (d i)) (lastState t hist)) := by
  induction n generalizing t u with
  | zero => omega
  | succ n ih =>
    by_cases hun' : u < n
    · have htn : t ≤ n := by omega
      change ((law P μ n).joint (fun hist ↦ P.row (lastState n hist))).mean
        (fun hist : History ι n × ι ↦ a (initialSegment (n+1) hist t (by omega))*transitionValue d (n+1) hist u) = _
      have heq : (fun hist : History ι n × ι ↦
          a (initialSegment (n+1) hist t (by omega))*transitionValue d (n+1) hist u) =
          (fun hist ↦ a (initialSegment n hist.1 t htn)*transitionValue d n hist.1 u) := by
        funext hist
        rw [prefix_succ_of_le n hist t htn, transitionValue_prefix d n hist u hun']
      rw [heq, ProbabilityVector.joint_first_mean (law P μ n) (fun hist ↦ P.row (lastState n hist))
        (fun hist ↦ a (initialSegment n hist t htn)*transitionValue d n hist u)]
      exact ih t u htu hun' a
    · have hu' : u=n := by omega
      subst u
      change ((law P μ n).joint (fun hist ↦ P.row (lastState n hist))).mean
        (fun hist : History ι n × ι ↦ a (initialSegment (n+1) hist t (by omega))*transitionValue d (n+1) hist n) = _
      rw [ProbabilityVector.joint_mean]
      have heq : (fun hist : History ι n ↦ (P.row (lastState n hist)).mean (fun j ↦
          a (initialSegment (n+1) (hist,j) t (by omega))*transitionValue d (n+1) (hist,j) n)) =
          (fun hist ↦ a (initialSegment n hist t htu)*(P.row (lastState n hist)).mean (d (lastState n hist))) := by
        funext hist
        simp only [prefix_succ_of_le n (hist, _) t htu, transitionValue_last, ProbabilityVector.mean_const_mul]
      rw [heq]
      have h := prefix_future_mean P μ n t n htu le_rfl a (fun i ↦ (P.row i).mean (d i))
      simpa only [stateAt_last] using h

def futureEdgeValue (P : FiniteKernel ι) (d : ℕ → ι → ι → ℝ) (s k : ℕ) (i : ι) : ℝ :=
  ∑ r ∈ Finset.range k, ((P.act)^[r]) (fun j ↦ (P.row j).mean (d (s+r) j)) i

def futureEdgePathSum (d : ℕ → ι → ι → ℝ) (n s : ℕ) (hist : History ι n) : ℝ :=
  ∑ r ∈ Finset.range (n-s), transitionValue (d (s+r)) n hist (s+r)

theorem prefix_future_edge_sum_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (d : ℕ → ι → ι → ℝ) (n s : ℕ) (hs : s ≤ n) (a : History ι s → ℝ) :
    (law P μ n).mean (fun hist ↦ a (initialSegment n hist s hs)*futureEdgePathSum d n s hist) =
      (law P μ s).mean (fun hist ↦ a hist*futureEdgeValue P d s (n-s) (lastState s hist)) := by
  have heq : (fun hist : History ι n ↦ a (initialSegment n hist s hs)*futureEdgePathSum d n s hist) =
      (fun hist ↦ ∑ r ∈ Finset.range (n-s),
        a (initialSegment n hist s hs)*transitionValue (d (s+r)) n hist (s+r)) := by
    funext hist
    exact Finset.mul_sum _ _ _
  rw [heq, ProbabilityVector.mean_sum]
  calc
    _ = ∑ r ∈ Finset.range (n-s), (law P μ s).mean (fun hist ↦ a hist * ((P.act)^[r])
        (fun i ↦ (P.row i).mean (d (s+r) i)) (lastState s hist)) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : r < n-s := Finset.mem_range.mp hr
      have h := prefix_edge_mean P μ n s (s+r) (by omega) (by omega) a (d (s+r))
      simpa only [Nat.add_sub_cancel_left] using h
    _ = _ := by
      rw [← ProbabilityVector.mean_sum]
      congr 1
      funext hist
      exact (Finset.mul_sum _ _ _).symm

theorem futureEdgeValue_eq_mean (P : FiniteKernel ι) (d : ℕ → ι → ι → ℝ) (s k : ℕ) (i : ι) :
    futureEdgeValue P d s k i =
      (law P (ProbabilityVector.pure i) k).mean (edgeTotal (fun r ↦ d (s+r)) k) := by
  unfold futureEdgeValue edgeTotal
  rw [ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have h := prefix_edge_mean P (ProbabilityVector.pure i) k 0 r (Nat.zero_le r) (Finset.mem_range.mp hr)
    (fun _ ↦ 1) (d (s+r))
  simp only [one_mul, Nat.sub_zero] at h
  have h' : (law P (ProbabilityVector.pure i) k).mean (fun hist ↦ transitionValue (d (s+r)) k hist r) =
      ((P.act)^[r]) (fun j ↦ (P.row j).mean (d (s+r) j)) i := by
    exact h.trans (ProbabilityVector.pure_mean i _)
  exact h'.symm

theorem conditional_future_edge_le (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (d : ℕ → ι → ι → ℝ) (n s : ℕ) (hs : s ≤ n) (v : ℝ)
    (hv : ∀ i, futureEdgeValue P d s (n-s) i ≤ v) :
    FiniteConditional.MeanLE (law P μ n) (fun hist ↦ initialSegment n hist s hs)
      (futureEdgePathSum d n s) v := by
  intro past
  rw [FiniteConditional.fiberSum_eq_mean, FiniteConditional.fiberMass_eq_mean,
    prefix_future_edge_sum_mean P μ d n s hs (fun hist ↦ if hist=past then 1 else 0),
    prefix_mean P μ n s hs (fun hist ↦ if hist=past then 1 else 0), ← ProbabilityVector.mean_const_mul]
  apply ProbabilityVector.mean_mono
  intro hist
  split
  · simpa only [one_mul, mul_one] using hv (lastState s hist)
  · simp

omit [Fintype ι] in
theorem futureEdgePathSum_eq_sum (d : ℕ → ι → ι → ℝ) (n s : ℕ) (hist : History ι n) :
    futureEdgePathSum d n s hist = ∑ u ∈ Finset.range n, if s ≤ u then transitionValue (d u) n hist u else 0 := by
  have hfilter : (Finset.range n).filter (fun u ↦ s ≤ u) = Finset.Ico s n := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter, hfilter, Finset.sum_Ico_eq_sum_range]
  rfl

end
end Tournament.FinitePath

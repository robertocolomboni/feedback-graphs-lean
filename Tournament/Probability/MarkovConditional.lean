module

public import Tournament.Probability.PrefixConditioning
public import Tournament.Probability.Occupation
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace FiniteConditional

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

omit [Fintype S] in
theorem fiberSum_eq_mean (μ : ProbabilityVector Ω) (info : Ω → S) (f : Ω → ℝ) (s : S) :
    fiberSum μ info f s = μ.mean (fun ω ↦ (if info ω=s then 1 else 0)*f ω) := by
  unfold fiberSum ProbabilityVector.mean
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : info ω=s <;> simp [h]

omit [Fintype S] in
theorem fiberMass_eq_mean (μ : ProbabilityVector Ω) (info : Ω → S) (s : S) :
    fiberMass μ info s = μ.mean (fun ω ↦ if info ω=s then 1 else 0) := by
  unfold fiberMass ProbabilityVector.mean
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : info ω=s <;> simp [h]

theorem meanLE_coarsen {T : Type*} [Fintype T] (μ : ProbabilityVector Ω)
    (info : Ω → S) (coarse : Ω → T) (f : Ω → ℝ) (c : ℝ)
    (hrefine : ∀ ω ω', info ω=info ω' → coarse ω=coarse ω') (hf : MeanLE μ info f c) :
    MeanLE μ coarse f c := by
  intro s
  rw [fiberSum_eq_mean, fiberMass_eq_mean]
  apply mean_mul_le μ info (fun ω ↦ if coarse ω=s then 1 else 0) f _ _ c hf
  · intro ω ω' heq
    dsimp only
    rw [hrefine ω ω' heq]
  · intro ω
    split <;> norm_num

end FiniteConditional

namespace FinitePath

variable {ι : Type*} [Fintype ι]

theorem prefix_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (n t : ℕ) (ht : t ≤ n) (a : History ι t → ℝ) :
    (law P μ n).mean (fun hist ↦ a (initialSegment n hist t ht)) = (law P μ t).mean a := by
  have h := prefix_future_mean P μ n t t le_rfl ht a (fun _ ↦ 1)
  simpa only [mul_one, Nat.sub_self, Function.iterate_zero, id_eq] using h

theorem stateAt_mean_predict (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (n t : ℕ) (ht : t ≤ n) (f : ι → ℝ) :
    (law P μ n).mean (fun hist ↦ f (stateAt n hist t)) = μ.mean (((P.act)^[t]) f) := by
  have h := prefix_future_mean P μ n 0 t (Nat.zero_le t) ht (fun _ ↦ 1) f
  simp only [one_mul, Nat.sub_zero] at h
  exact h

theorem occupation_mean_predict (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (f : ι → ℝ) (n : ℕ) :
    (law P μ n).mean (occupation f n) = μ.mean (fun i ↦ ∑ t ∈ Finset.range n, ((P.act)^[t]) f i) := by
  unfold occupation
  rw [ProbabilityVector.mean_sum, ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact stateAt_mean_predict P μ n t (Nat.le_of_lt (Finset.mem_range.mp ht)) f

def futureValue (P : FiniteKernel ι) (f : ι → ℝ) (k : ℕ) (i : ι) : ℝ :=
  ∑ r ∈ Finset.range k, ((P.act)^[r+1]) f i

def futurePathSum (f : ι → ℝ) (n t : ℕ) (hist : History ι n) : ℝ :=
  ∑ r ∈ Finset.range (n-t), f (stateAt n hist (t+1+r))

theorem futureValue_eq_occupation (P : FiniteKernel ι) (f : ι → ℝ) (k : ℕ) (i : ι) :
    futureValue P f k i = (law P (P.row i) k).mean (occupation f k) := by
  unfold futureValue
  rw [occupation_mean_predict, ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Function.iterate_succ_apply']
  rfl

theorem prefix_future_sum_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (n t : ℕ) (ht : t ≤ n) (a : History ι t → ℝ) (f : ι → ℝ) :
    (law P μ n).mean (fun hist ↦ a (initialSegment n hist t ht)*futurePathSum f n t hist) =
      (law P μ t).mean (fun hist ↦ a hist * futureValue P f (n-t) (lastState t hist)) := by
  have heq : (fun hist : History ι n ↦ a (initialSegment n hist t ht)*futurePathSum f n t hist) =
      (fun hist ↦ ∑ r ∈ Finset.range (n-t), a (initialSegment n hist t ht)*f (stateAt n hist (t+1+r))) := by
    funext hist
    exact Finset.mul_sum _ _ _
  rw [heq, ProbabilityVector.mean_sum]
  calc
    _ = ∑ r ∈ Finset.range (n-t), (law P μ t).mean (fun hist ↦
        a hist * ((P.act)^[r+1]) f (lastState t hist)) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : r < n-t := Finset.mem_range.mp hr
      have hpred := prefix_future_mean P μ n t (t+1+r) (by omega) (by omega) a f
      have hexp : t+1+r-t=r+1 := by omega
      simpa only [hexp] using hpred
    _ = _ := by
      rw [← ProbabilityVector.mean_sum]
      congr 1
      funext hist
      exact (Finset.mul_sum _ _ _).symm

theorem conditional_future_occupation_le (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (f : ι → ℝ) (n t : ℕ) (ht : t ≤ n) (v : ℝ)
    (hv : ∀ i, futureValue P f (n-t) i ≤ v) :
    FiniteConditional.MeanLE (law P μ n) (fun hist ↦ initialSegment n hist t ht)
      (futurePathSum f n t) v := by
  intro s
  rw [FiniteConditional.fiberSum_eq_mean, FiniteConditional.fiberMass_eq_mean,
    prefix_future_sum_mean P μ n t ht (fun hist ↦ if hist=s then 1 else 0) f,
    prefix_mean P μ n t ht (fun hist ↦ if hist=s then 1 else 0),
    ← ProbabilityVector.mean_const_mul]
  apply ProbabilityVector.mean_mono
  intro hist
  split
  · simpa only [one_mul, mul_one] using hv (lastState t hist)
  · simp

omit [Fintype ι] in
theorem futurePathSum_eq_strict_sum (f : ι → ℝ) (n t : ℕ) (hist : History ι n) :
    futurePathSum f n t hist =
      ∑ u ∈ Finset.range (n+1), if t<u then f (stateAt n hist u) else 0 := by
  have hfilter : (Finset.range (n+1)).filter (fun u ↦ t<u) = Finset.Ico (t+1) (n+1) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter, hfilter, Finset.sum_Ico_eq_sum_range]
  have hlen : n+1-(t+1)=n-t := by omega
  rw [hlen]
  rfl

end FinitePath
end
end Tournament

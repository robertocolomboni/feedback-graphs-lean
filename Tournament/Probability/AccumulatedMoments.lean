module

public import Tournament.Probability.OrderedMoments
public import Tournament.Probability.FiniteConditional

@[expose] public section

namespace Tournament.AccumulatedMoments

open scoped BigOperators Classical
open OrderedMoments FiniteConditional

variable {Ω : Type*} [Fintype Ω]
variable {S : ℕ → Type*} [∀ t, Fintype (S t)]

noncomputable section

def IncreasingInformation (info : (t : ℕ) → Ω → S t) : Prop :=
  ∀ s t, s ≤ t → ∀ ω ω', info t ω = info t ω' → info s ω = info s ω'

theorem ordered_step_mean_le (μ : ProbabilityVector Ω) (info : (t : ℕ) → Ω → S t)
    (hinfo : IncreasingInformation info) (Y : ℕ → Ω → ℝ) (n : ℕ)
    (hY : ∀ t, t<n → DependsOn (info (t+1)) (Y t))
    (hY0 : ∀ t ω, 0 ≤ Y t ω) (b v : ℝ)
    (hbound : ∀ t, t<n → ∀ ω, Y t ω ≤ b)
    (hfuture : ∀ t, t<n → MeanLE μ (info (t+1))
      (fun ω ↦ ∑ u ∈ Finset.range n, if t<u then Y u ω else 0) v) (k : ℕ) :
    μ.mean (fun ω ↦ orderedProducts (fun t ↦ Y t ω) (k+2) n) ≤
      (b+v)*μ.mean (fun ω ↦ orderedProducts (fun t ↦ Y t ω) (k+1) n) := by
  have heq : (fun ω ↦ orderedProducts (fun t ↦ Y t ω) (k+2) n) =
      (fun ω ↦ ∑ t ∈ Finset.range n, (Y t ω*orderedProducts (fun u ↦ Y u ω) k (t+1)) *
        inclusiveTail (fun u ↦ Y u ω) n t) := by
    funext ω
    exact orderedProducts_last_index (fun t ↦ Y t ω) k n
  rw [heq, ProbabilityVector.mean_sum]
  calc
    (∑ t ∈ Finset.range n, μ.mean (fun ω ↦
        (Y t ω*orderedProducts (fun u ↦ Y u ω) k (t+1))*inclusiveTail (fun u ↦ Y u ω) n t)) ≤
        ∑ t ∈ Finset.range n, (b+v)*μ.mean (fun ω ↦
          Y t ω*orderedProducts (fun u ↦ Y u ω) k (t+1)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htn : t < n := Finset.mem_range.mp ht
      have hZ : DependsOn (info (t+1))
          (fun ω ↦ Y t ω*orderedProducts (fun u ↦ Y u ω) k (t+1)) := by
        intro ω ω' hobs
        have hvalues : ∀ u, u<t+1 → Y u ω=Y u ω' := by
          intro u hu
          apply hY u (by omega)
          exact hinfo (u+1) (t+1) (by omega) ω ω' hobs
        have hprod := orderedProducts_congr_prefix (fun u ↦ Y u ω) (fun u ↦ Y u ω')
          (t+1) hvalues k (t+1) le_rfl
        dsimp only
        rw [hvalues t (by omega), hprod]
      have hZ0 : ∀ ω, 0 ≤ Y t ω*orderedProducts (fun u ↦ Y u ω) k (t+1) := by
        intro ω
        exact mul_nonneg (hY0 t ω) (orderedProducts_nonneg _ (fun u ↦ hY0 u ω) k (t+1))
      have hinc : MeanLE μ (info (t+1)) (fun ω ↦ inclusiveTail (fun u ↦ Y u ω) n t) (b+v) := by
        have hsplit : (fun ω ↦ inclusiveTail (fun u ↦ Y u ω) n t) =
            (fun ω ↦ Y t ω + ∑ u ∈ Finset.range n, if t<u then Y u ω else 0) := by
          funext ω
          exact inclusiveTail_split _ n t htn
        rw [hsplit]
        exact meanLE_add μ (info (t+1)) (Y t)
          (fun ω ↦ ∑ u ∈ Finset.range n, if t<u then Y u ω else 0) b v
          (meanLE_of_pointwise μ (info (t+1)) (Y t) b (hbound t htn)) (hfuture t htn)
      exact mean_mul_le μ (info (t+1))
        (fun ω ↦ Y t ω*orderedProducts (fun u ↦ Y u ω) k (t+1))
        (fun ω ↦ inclusiveTail (fun u ↦ Y u ω) n t) hZ hZ0 (b+v) hinc
    _ = (b+v)*(∑ t ∈ Finset.range n, μ.mean
        (fun ω ↦ Y t ω*orderedProducts (fun u ↦ Y u ω) k (t+1))) :=
      (Finset.mul_sum _ _ _).symm
    _ = (b+v)*μ.mean (fun ω ↦ orderedProducts (fun t ↦ Y t ω) (k+1) n) := by
      rw [← ProbabilityVector.mean_sum]
      rfl

theorem ordered_moment_le (μ : ProbabilityVector Ω) (info : (t : ℕ) → Ω → S t)
    (hinfo : IncreasingInformation info) (Y : ℕ → Ω → ℝ) (n : ℕ)
    (hY : ∀ t, t<n → DependsOn (info (t+1)) (Y t))
    (hY0 : ∀ t ω, 0 ≤ Y t ω) (b v : ℝ) (hB : 0 ≤ b+v)
    (hbound : ∀ t, t<n → ∀ ω, Y t ω ≤ b)
    (hfuture : ∀ t, t<n → MeanLE μ (info (t+1))
      (fun ω ↦ ∑ u ∈ Finset.range n, if t<u then Y u ω else 0) v) (k : ℕ) :
    μ.mean (fun ω ↦ orderedProducts (fun t ↦ Y t ω) (k+1) n) ≤
      (b+v)^k * μ.mean (fun ω ↦ ∑ t ∈ Finset.range n, Y t ω) := by
  induction k with
  | zero =>
    have heq : (fun ω ↦ orderedProducts (fun t ↦ Y t ω) 1 n) =
        (fun ω ↦ ∑ t ∈ Finset.range n, Y t ω) := by
      funext ω
      exact orderedProducts_one _ n
    rw [heq, pow_zero, one_mul]
  | succ k ih =>
    calc
      _ ≤ (b+v)*μ.mean (fun ω ↦ orderedProducts (fun t ↦ Y t ω) (k+1) n) :=
        ordered_step_mean_le μ info hinfo Y n hY hY0 b v hbound hfuture k
      _ ≤ (b+v)*((b+v)^k * μ.mean (fun ω ↦ ∑ t ∈ Finset.range n, Y t ω)) :=
        mul_le_mul_of_nonneg_left ih hB
      _ = _ := by rw [pow_succ]; ring

theorem accumulated_moment_le (μ : ProbabilityVector Ω) (info : (t : ℕ) → Ω → S t)
    (hinfo : IncreasingInformation info) (Y : ℕ → Ω → ℝ) (n : ℕ)
    (hY : ∀ t, t<n → DependsOn (info (t+1)) (Y t))
    (hY0 : ∀ t ω, 0 ≤ Y t ω) (b v : ℝ) (hB : 0 ≤ b+v)
    (hbound : ∀ t, t<n → ∀ ω, Y t ω ≤ b)
    (hfuture : ∀ t, t<n → MeanLE μ (info (t+1))
      (fun ω ↦ ∑ u ∈ Finset.range n, if t<u then Y u ω else 0) v) (k : ℕ) :
    μ.mean (fun ω ↦ (∑ t ∈ Finset.range n, Y t ω)^(k+1)) ≤
      (Nat.factorial (k+1):ℝ)*(b+v)^k * μ.mean (fun ω ↦ ∑ t ∈ Finset.range n, Y t ω) := by
  calc
    _ ≤ μ.mean (fun ω ↦ (Nat.factorial (k+1):ℝ)*orderedProducts (fun t ↦ Y t ω) (k+1) n) :=
      μ.mean_mono (fun ω ↦ sum_pow_le_factorial_ordered _ (fun t ↦ hY0 t ω) (k+1) n)
    _ = (Nat.factorial (k+1):ℝ)*μ.mean
        (fun ω ↦ orderedProducts (fun t ↦ Y t ω) (k+1) n) := μ.mean_const_mul _ _
    _ ≤ (Nat.factorial (k+1):ℝ)*((b+v)^k * μ.mean (fun ω ↦ ∑ t ∈ Finset.range n, Y t ω)) :=
      mul_le_mul_of_nonneg_left (ordered_moment_le μ info hinfo Y n hY hY0 b v hB hbound hfuture k)
        (Nat.cast_nonneg _)
    _ = _ := by ring

end
end Tournament.AccumulatedMoments

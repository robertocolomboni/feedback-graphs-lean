module

public import Tournament.Probability.GeometricPartition
public import Tournament.Upper.ChunkMeanEnergy

@[expose] public section

namespace Tournament.GeometricPartition

open scoped BigOperators Classical

noncomputable section

variable {ι β : Type*} [Fintype ι] [Fintype β]

omit [Fintype ι] in
theorem linearMap_interval_sum (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (f : ℕ → ι → ℝ) (start n : ℕ) :
    (fun i ↦ ∑ t ∈ Finset.range (n+1), A (f (start+t)) i)=
      A (fun i ↦ ∑ t ∈ Finset.range (n+1), f (start+t) i) := by
  have hfun : (fun i ↦ ∑ t ∈ Finset.range (n+1), f (start+t) i)=
      ∑ t ∈ Finset.range (n+1), f (start+t) := by funext i; simp only [Finset.sum_apply]
  rw [hfun,map_sum]
  funext i
  simp only [Finset.sum_apply]

theorem weighted_chunkVectorSquareSum (p : ProbabilityVector ι) (a : β → ℝ)
    (A : β → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (f : ℕ → ι → ℝ) (offset : ℕ) (ns : List ℕ) :
    (∑ b, a b*chunkVectorSquareSum p (fun t ↦ A b (f t)) offset ns)=
      Restarts.chunkSum (fun start n ↦ ∑ b, a b*p.squareNorm
        (A b (fun i ↦ ∑ t ∈ Finset.range (n+1), f (start+t) i))) offset ns := by
  unfold chunkVectorSquareSum
  simp_rw [linearMap_interval_sum]
  rw [Restarts.chunkSum_finset_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Restarts.chunkSum_const_mul]

theorem interval_bound_temporal_domination (p : ProbabilityVector ι) (a : β → ℝ)
    (A : β → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (f : ℕ → ι → ℝ) (C : ℝ)
    (hinterval : ∀ start n, (∑ b, a b*p.squareNorm (A b (fun i ↦ ∑ t ∈ Finset.range (n+1), f (start+t) i)))≤
      C*p.squareNorm (fun i ↦ ∑ t ∈ Finset.range (n+1), f (start+t) i))
    {χ : ℝ} (hχ : 0≤χ) (hχ1 : χ≤1) (offset n : ℕ) :
    (∑ b, a b*vectorQuadratic p χ (fun t ↦ A b (f t)) offset (n+1))≤
      C*vectorQuadratic p χ f offset (n+1) := by
  let μ := Restarts.law (1-χ) (sub_nonneg.mpr hχ1) (by linarith) n
  have hrepr (g : ℕ → ι → ℝ) : vectorQuadratic p χ g offset (n+1)=
      μ.mean (fun coins ↦ chunkVectorSquareSum p g offset (Restarts.parts n coins)) :=
    vectorQuadratic_eq_mean_chunkSquares p hχ hχ1 g offset n
  simp_rw [hrepr]
  have hleft : (∑ b, a b*μ.mean
      (fun coins ↦ chunkVectorSquareSum p (fun t ↦ A b (f t)) offset (Restarts.parts n coins)))=
      μ.mean (fun coins ↦
        ∑ b, a b*chunkVectorSquareSum p (fun t ↦ A b (f t)) offset (Restarts.parts n coins)) := by
    rw [ProbabilityVector.mean_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [ProbabilityVector.mean_const_mul]
  rw [hleft,← ProbabilityVector.mean_const_mul]
  apply ProbabilityVector.mean_mono
  intro coins
  rw [weighted_chunkVectorSquareSum]
  unfold chunkVectorSquareSum
  rw [← Restarts.chunkSum_const_mul]
  exact Restarts.chunkSum_mono _ _ hinterval (Restarts.parts n coins) offset

end
end Tournament.GeometricPartition

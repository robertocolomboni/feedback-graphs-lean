module

public import Tournament.Probability.AccumulatedMoments
public import Tournament.Probability.FiniteAccumulatedBridge
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

namespace Tournament.AccumulatedMoments

open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

noncomputable section

theorem exponential_mean_le_of_moments (μ : ProbabilityVector Ω) (V : Ω → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hmoment : ∀ k, μ.mean (fun ω ↦ V ω^(k+1)) ≤
      (Nat.factorial (k+1):ℝ)*B^k*μ.mean V)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθB : θ*B < 1) :
    μ.mean (fun ω ↦ Real.exp (θ*V ω)) ≤ 1+θ*μ.mean V/(1-θ*B) := by
  let a : ℕ → ℝ := fun k ↦ μ.mean (fun ω ↦ (θ*V ω)^k/(Nat.factorial k:ℝ))
  let g : ℕ → ℝ := fun k ↦ if k=0 then 1 else θ*μ.mean V*(θ*B)^(k-1)
  have hexpω (ω : Ω) : HasSum (fun k ↦ μ ω*((θ*V ω)^k/(Nat.factorial k:ℝ)))
      (μ ω*Real.exp (θ*V ω)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (θ*V ω)).mul_left (μ ω)
  have hexp : HasSum a (μ.mean (fun ω ↦ Real.exp (θ*V ω))) :=
    hasSum_sum (fun ω _ ↦ hexpω ω)
  have hnorm : ‖θ*B‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hθ hB)]
  have hgeom := (hasSum_geometric_of_norm_lt_one hnorm).mul_left (θ*μ.mean V)
  have htail : HasSum (fun k ↦ g (k+1)) (θ*μ.mean V/(1-θ*B)) := by
    simpa only [g, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel,
      div_eq_mul_inv] using hgeom
  have hmajorant : HasSum g (1+θ*μ.mean V/(1-θ*B)) := by
    have h := (hasSum_nat_add_iff 1).mp htail
    simpa only [Finset.sum_range_one, g, ite_eq_left rfl, ite_true, add_comm] using h
  have hle : ∀ k, a k ≤ g k := by
    intro k
    cases k with
    | zero =>
      simp only [a, g, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ite_eq_left rfl,
        ProbabilityVector.mean_const]
      exact le_rfl
    | succ k =>
      have hfactorial : (Nat.factorial (k+1):ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (k+1)
      have heq : a (k+1) = (θ^(k+1)/(Nat.factorial (k+1):ℝ))*μ.mean (fun ω ↦ V ω^(k+1)) := by
        have hfun : (fun ω ↦ (θ*V ω)^(k+1)/(Nat.factorial (k+1):ℝ)) =
            (fun ω ↦ (θ^(k+1)/(Nat.factorial (k+1):ℝ)) * V ω^(k+1)) := by
          funext ω
          rw [mul_pow]
          ring
        dsimp only [a]
        rw [hfun, ProbabilityVector.mean_const_mul]
      rw [heq]
      calc
        _ ≤ (θ^(k+1)/(Nat.factorial (k+1):ℝ))*
            ((Nat.factorial (k+1):ℝ)*B^k*μ.mean V) :=
          mul_le_mul_of_nonneg_left (hmoment k) (by positivity)
        _ = g (k+1) := by
          simp only [g, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, mul_pow, pow_succ]
          field_simp
  exact hasSum_le hle hexp hmajorant

theorem accumulated_exponential_mean_le {S : ℕ → Type*} [∀ t, Fintype (S t)]
    (μ : ProbabilityVector Ω) (info : (t : ℕ) → Ω → S t)
    (hinfo : IncreasingInformation info) (Y : ℕ → Ω → ℝ) (n : ℕ)
    (hY : ∀ t, t<n → FiniteConditional.DependsOn (info (t+1)) (Y t))
    (hY0 : ∀ t ω, 0 ≤ Y t ω) (b v : ℝ) (hB : 0 ≤ b+v)
    (hbound : ∀ t, t<n → ∀ ω, Y t ω ≤ b)
    (hfuture : ∀ t, t<n → FiniteConditional.MeanLE μ (info (t+1))
      (fun ω ↦ ∑ u ∈ Finset.range n, if t<u then Y u ω else 0) v)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθB : θ*(b+v) < 1) :
    μ.mean (fun ω ↦ Real.exp (θ*(∑ t ∈ Finset.range n, Y t ω))) ≤
      1+θ*μ.mean (fun ω ↦ ∑ t ∈ Finset.range n, Y t ω)/(1-θ*(b+v)) := by
  rcases hB.eq_or_lt with hzero | hpos
  · apply exponential_mean_le_of_moments μ (fun ω ↦ ∑ t ∈ Finset.range n, Y t ω) (b+v) hB
      (fun k ↦ accumulated_moment_le μ info hinfo Y n hY hY0 b v hB hbound hfuture k) θ hθ hθB
  · exact accumulated_exponential_mean_le_from_general μ info hinfo Y n hY hY0
      b v hpos hbound hfuture θ hθ hθB

end
end Tournament.AccumulatedMoments

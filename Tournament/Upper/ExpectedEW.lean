module

public import Tournament.Upper.RandomEW

@[expose] public section

namespace Tournament.Upper.ExponentialWeights

open scoped BigOperators MeasureTheory
open MeasureTheory Filter

noncomputable section

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

def smoothedWeights (η : ℝ) (g : ℕ → Ω → ι → ℝ) (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (b : ℕ) (ω : Ω) : ProbabilityVector ι := smooth (weights η g b ω) ε hε hε1

theorem expected_second_order (μ : Measure Ω) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : 0<η) (g : ℕ → Ω → ι → ℝ) (B : ℕ)
    (ε : ℝ) (hε : 0≤ε) (hεhalf : ε≤1/2)
    (hg : ∀ b ∈ Finset.range B, ∀ i, AEStronglyMeasurable (fun ω ↦ g b ω i) μ)
    (hbound : ∀ᵐ ω ∂μ, ∀ b ∈ Finset.range B, η*‖g b ω‖≤1) (i : ι) :
    (∑ b ∈ Finset.range B, ∫ ω, ((weights η g b ω).mean (g b ω)-g b ω i) ∂μ)≤
      Real.log (Fintype.card ι:ℝ)/η+2*η*(∑ b ∈ Finset.range B,
        ∫ ω, (smoothedWeights η g ε hε (by linarith) b ω).squareNorm (g b ω) ∂μ) := by
  have hπ (b : ℕ) (hb : b∈Finset.range B) (j : ι) :
      AEStronglyMeasurable (fun ω ↦ weights η g b ω j) μ :=
    trajectory_aestronglyMeasurable μ uniform η g b (fun t ht ↦ hg t (by simp only [Finset.mem_range] at hb ⊢; omega)) j
  have hw (b : ℕ) (hb : b∈Finset.range B) (j : ι) :
      AEStronglyMeasurable (fun ω ↦ smoothedWeights η g ε hε (by linarith) b ω j) μ :=
    smooth_aestronglyMeasurable μ (weights η g b) ε hε (by linarith) (hπ b hb) j
  have hbnd (b : ℕ) (hb : b∈Finset.range B) : ∀ᵐ ω ∂μ, η*‖g b ω‖≤1 :=
    hbound.mono (fun _ h ↦ h b hb)
  have hcmp (b : ℕ) (hb : b∈Finset.range B) :
      Integrable (fun ω ↦ (weights η g b ω).mean (g b ω)-g b ω i) μ :=
    MeasureRandomWeights.integrable_comparison μ (weights η g b) (hπ b hb) (g b)
      (estimate_integrable μ η hη (g b) (hg b hb) (hbnd b hb)) i
  have hsq (b : ℕ) (hb : b∈Finset.range B) :
      Integrable (fun ω ↦ (smoothedWeights η g ε hε (by linarith) b ω).squareNorm (g b ω)) μ :=
    estimate_secondMoment_integrable μ _ (hw b hb) η hη (g b) (hg b hb) (hbnd b hb)
  have hsumCmp := integrable_finsetSum (Finset.range B) hcmp
  have hsumSq := integrable_finsetSum (Finset.range B) hsq
  have hpointwise : ∀ᵐ ω ∂μ,
      (∑ b ∈ Finset.range B, ((weights η g b ω).mean (g b ω)-g b ω i))≤
        Real.log (Fintype.card ι:ℝ)/η+2*η*(∑ b ∈ Finset.range B,
          (smoothedWeights η g ε hε (by linarith) b ω).squareNorm (g b ω)) := by
    filter_upwards [hbound] with ω hω
    have hew := second_order η hη (fun b ↦ g b ω) B hω i
    have hdom : (∑ b ∈ Finset.range B, (weights η g b ω).squareNorm (g b ω))≤
        2*(∑ b ∈ Finset.range B, (smoothedWeights η g ε hε (by linarith) b ω).squareNorm (g b ω)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun b _ ↦ squareNorm_le_twice_smooth (weights η g b ω) ε hε hεhalf (g b ω))
    have hmul := mul_le_mul_of_nonneg_left hdom hη.le
    change (∑ b ∈ Finset.range B, ((weights η g b ω).mean (g b ω)-g b ω i))≤
      Real.log (Fintype.card ι:ℝ)/η+η*(∑ b ∈ Finset.range B, (weights η g b ω).squareNorm (g b ω)) at hew
    linarith
  calc
    _ = ∫ ω, ∑ b ∈ Finset.range B, ((weights η g b ω).mean (g b ω)-g b ω i) ∂μ :=
      (integral_finsetSum (Finset.range B) hcmp).symm
    _ ≤ ∫ ω, (Real.log (Fintype.card ι:ℝ)/η+2*η*(∑ b ∈ Finset.range B,
        (smoothedWeights η g ε hε (by linarith) b ω).squareNorm (g b ω))) ∂μ :=
      integral_mono_ae hsumCmp ((integrable_const _).add (hsumSq.const_mul (2*η))) hpointwise
    _ = _ := by
      rw [integral_add (integrable_const _) (hsumSq.const_mul (2*η)),integral_const_mul,
        integral_finsetSum (Finset.range B) hsq]
      simp

end
end Tournament.Upper.ExponentialWeights

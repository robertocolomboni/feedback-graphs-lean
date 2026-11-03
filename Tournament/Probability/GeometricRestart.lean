module

public import Tournament.Probability.Restarts
public import Tournament.Probability.FiniteMeasure
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

namespace Tournament.Restarts

open scoped BigOperators ENNReal Classical
open MeasureTheory

noncomputable section

def geometricWeight (τ : ℝ) (n : ℕ) : ℝ := (1 - τ) ^ n * τ

theorem geometricWeight_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    0 ≤ geometricWeight τ n :=
  mul_nonneg (pow_nonneg (sub_nonneg.mpr hτ1) _) hτ

theorem geometricWeight_one (n : ℕ) :
    geometricWeight 1 n = if n = 0 then 1 else 0 := by
  cases n <;> simp [geometricWeight]

def geometricLengthLaw (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) : PMF ℕ :=
  (ProbabilityTheory.geometricMeasure ⟨τ, hτ.le, hτ1⟩).toPMF

theorem geometricLengthLaw_apply (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    geometricLengthLaw τ hτ hτ1 n = ENNReal.ofReal (geometricWeight τ n) := by
  unfold geometricLengthLaw
  rw [Measure.toPMF_apply, ProbabilityTheory.geometricMeasure_singleton]
  · rfl
  · intro h
    have hzero : τ = 0 := congrArg Subtype.val h
    exact hτ.ne' hzero

variable {ι : Type*} [Fintype ι]

/-- A stopped reference path, with no deterministic bound on its number of transitions. -/
abbrev UntruncatedChunkOutcome (ι : Type*) := (n : ℕ) × FinitePath.History ι n

instance untruncatedChunkMeasurableSpace : MeasurableSpace (UntruncatedChunkOutcome ι) := ⊤

instance untruncatedChunkDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (UntruncatedChunkOutcome ι) := ⟨fun _ ↦ trivial⟩

/-- The restart length is geometric; conditional on that length, the path has the
original Markov-chain law. The chunk has `outcome.1 + 1` rounds. -/
def untruncatedChunkLaw (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) : PMF (UntruncatedChunkOutcome ι) :=
  ⟨fun outcome ↦ geometricLengthLaw τ hτ hτ1 outcome.1 *
      (FinitePath.law P μ outcome.1).toPMF outcome.2, by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [ENNReal.tsum_sigma']
    simp only [ENNReal.tsum_mul_left]
    have hsum (n : ℕ) : (∑' hist, (FinitePath.law P μ n).toPMF hist) = 1 :=
      (FinitePath.law P μ n).toPMF.tsum_coe
    simp only [hsum, mul_one]
    exact (geometricLengthLaw τ hτ hτ1).tsum_coe⟩

theorem untruncatedChunkLaw_apply (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (n : ℕ) (hist : FinitePath.History ι n) :
    untruncatedChunkLaw P μ τ hτ hτ1 ⟨n, hist⟩ =
      ENNReal.ofReal (geometricWeight τ n * FinitePath.law P μ n hist) := by
  change geometricLengthLaw τ hτ hτ1 n * ENNReal.ofReal (FinitePath.law P μ n hist) = _
  rw [geometricLengthLaw_apply, ENNReal.ofReal_mul (geometricWeight_nonneg hτ.le hτ1 n)]

theorem untruncatedChunkLaw_length_mass (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    (∑ hist : FinitePath.History ι n, untruncatedChunkLaw P μ τ hτ hτ1 ⟨n, hist⟩) =
      ENNReal.ofReal (geometricWeight τ n) := by
  change (∑ hist : FinitePath.History ι n,
    geometricLengthLaw τ hτ hτ1 n * (FinitePath.law P μ n).toPMF hist) = _
  have hsum : (∑ hist : FinitePath.History ι n, (FinitePath.law P μ n).toPMF hist) = 1 := by
    simpa only [tsum_fintype] using (FinitePath.law P μ n).toPMF.tsum_coe
  rw [← Finset.mul_sum, hsum, mul_one, geometricLengthLaw_apply]

theorem untruncatedChunkLaw_one (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (n : ℕ) (hist : FinitePath.History ι n) :
    untruncatedChunkLaw P μ 1 zero_lt_one le_rfl ⟨n, hist⟩ =
      if n = 0 then ENNReal.ofReal (FinitePath.law P μ n hist) else 0 := by
  rw [untruncatedChunkLaw_apply, geometricWeight_one]
  split_ifs <;> simp

theorem untruncatedChunkLaw_singleton (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (outcome : UntruncatedChunkOutcome ι) :
    (untruncatedChunkLaw P μ τ hτ hτ1).toMeasure {outcome} =
      ENNReal.ofReal (geometricWeight τ outcome.1 *
        FinitePath.law P μ outcome.1 outcome.2) := by
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact untruncatedChunkLaw_apply P μ τ hτ hτ1 outcome.1 outcome.2

theorem untruncatedChunk_lintegral (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (f : UntruncatedChunkOutcome ι → ℝ) (hf : ∀ outcome, 0 ≤ f outcome) :
    (∫⁻ outcome, ENNReal.ofReal (f outcome) ∂(untruncatedChunkLaw P μ τ hτ hτ1).toMeasure) =
      ∑' n, ENNReal.ofReal (geometricWeight τ n *
        (FinitePath.law P μ n).mean (fun hist ↦ f ⟨n, hist⟩)) := by
  rw [lintegral_countable', ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  simp only [untruncatedChunkLaw_singleton, tsum_fintype]
  rw [ProbabilityVector.mean, Finset.mul_sum]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro hist _
    rw [← ENNReal.ofReal_mul (hf ⟨n, hist⟩)]
    congr 1
    ring
  · intro hist _
    exact mul_nonneg (geometricWeight_nonneg hτ.le hτ1 n)
      (mul_nonneg ((FinitePath.law P μ n).nonneg hist) (hf ⟨n, hist⟩))

end
end Tournament.Restarts

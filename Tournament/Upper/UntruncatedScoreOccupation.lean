module

public import Tournament.Upper.ScoreOccupation
public import Tournament.Probability.GeometricRestart
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

namespace Tournament.Restarts

open scoped BigOperators Classical

theorem geometricWeight_hasSum {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    HasSum (geometricWeight τ) 1 := by
  have hs := (hasSum_geometric_of_lt_one (sub_nonneg.mpr hτ1)
    (show 1 - τ < 1 by linarith)).mul_right τ
  change HasSum (fun n : ℕ ↦ (1 - τ) ^ n * τ) 1
  simpa only [sub_sub_cancel, inv_mul_cancel₀ hτ.ne'] using hs

theorem geometricWeight_hasSum_length {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    HasSum (fun n : ℕ ↦ geometricWeight τ n * (n : ℝ)) ((1 - τ) / τ) := by
  have hq : ‖1 - τ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hτ1)]
    linarith
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hq).mul_right τ
  convert hs using 1
  · ext n
    unfold geometricWeight
    ring
  · simp only [sub_sub_cancel]
    field_simp

end Tournament.Restarts

namespace Tournament.Upper.ScoreRule

open scoped BigOperators ENNReal Classical
open MeasureTheory FinitePath

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

noncomputable section

theorem absoluteScores_nonneg (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (n : ℕ) (hist : History ι n) : 0 ≤ R.absoluteScores loss n hist := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases hist with ⟨hist, j⟩
    exact add_nonneg (ih hist) (abs_nonneg _)

/-- Averaging the fixed-length potential bound against the geometric restart law.
Here `n` counts transitions, so the corresponding chunk has `n + 1` rounds. -/
theorem untruncated_absoluteScores_summable_le (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (μ : ProbabilityVector ι) :
    Summable (fun n ↦ Restarts.geometricWeight τ n *
      (law (H.kernel τ hτ) μ n).mean (R.absoluteScores loss n)) ∧
    (∑' n, Restarts.geometricWeight τ n *
      (law (H.kernel τ hτ) μ n).mean (R.absoluteScores loss n)) ≤ 7 := by
  let a : ℕ → ℝ := fun n ↦ (law (H.kernel τ hτ) μ n).mean (R.absoluteScores loss n)
  have ha0 : ∀ n, 0 ≤ a n := fun n ↦
    ProbabilityVector.mean_nonneg _ (R.absoluteScores_nonneg loss n)
  have hrow : ∀ t i, ((H.kernel τ hτ).row i).mean
      (fun j ↦ |R.score t (loss t) i j|) ≤ 2 * H.refreshRate τ i := by
    intro t i
    have hscore := R.row_abs_score_le_two_switches t (loss t) (hloss t) i
    have hhold := H.kernel_holding_lower hτ i
    linarith
  have ha : ∀ n, a n ≤ 2 * ((n : ℝ) * H.meanRefreshRate τ + 3) := by
    intro n
    have habs := R.absoluteScores_mean_le loss μ (H.refreshRate τ) hrow n
    have hocc := H.expected_refresh_occupation_le μ hτ hτ1 n
    dsimp only [a]
    linarith
  have hsum : HasSum (fun n : ℕ ↦ Restarts.geometricWeight τ n *
      (2 * ((n : ℝ) * H.meanRefreshRate τ + 3)))
      (2 * (H.meanRefreshRate τ * ((1 - τ) / τ) + 3)) := by
    convert ((Restarts.geometricWeight_hasSum_length hτ hτ1).mul_right
      (2 * H.meanRefreshRate τ)).add
      ((Restarts.geometricWeight_hasSum hτ hτ1).mul_right 6) using 1
    · ext n
      ring
    · ring
  have hnonneg : ∀ n, 0 ≤ Restarts.geometricWeight τ n * a n := fun n ↦
    mul_nonneg (Restarts.geometricWeight_nonneg hτ.le hτ1 n) (ha0 n)
  have hle : ∀ n, Restarts.geometricWeight τ n * a n ≤
      Restarts.geometricWeight τ n * (2 * ((n : ℝ) * H.meanRefreshRate τ + 3)) := fun n ↦
    mul_le_mul_of_nonneg_left (ha n) (Restarts.geometricWeight_nonneg hτ.le hτ1 n)
  have hsummable := Summable.of_nonneg_of_le hnonneg hle hsum.summable
  have hmean : H.meanRefreshRate τ * ((1 - τ) / τ) ≤ 1 / 2 := by
    calc
      _ ≤ (τ / 2) * ((1 - τ) / τ) :=
        mul_le_mul_of_nonneg_right (H.meanRefreshRate_le hτ.le)
          (div_nonneg (sub_nonneg.mpr hτ1) hτ.le)
      _ = (1 - τ) / 2 := by field_simp
      _ ≤ 1 / 2 := by linarith
  refine ⟨hsummable, ?_⟩
  calc
    (∑' n, Restarts.geometricWeight τ n * a n) ≤
        ∑' n, Restarts.geometricWeight τ n *
          (2 * ((n : ℝ) * H.meanRefreshRate τ + 3)) :=
      hsummable.tsum_le_tsum hle hsum.summable
    _ = 2 * (H.meanRefreshRate τ * ((1 - τ) / τ) + 3) := hsum.tsum_eq
    _ ≤ 7 := by linarith

theorem untruncated_chunk_absoluteScores_lintegral_le (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (μ : ProbabilityVector ι) :
    (∫⁻ outcome, ENNReal.ofReal (R.absoluteScores loss outcome.1 outcome.2)
      ∂(Restarts.untruncatedChunkLaw (H.kernel τ hτ) μ τ hτ hτ1).toMeasure) ≤ 7 := by
  rw [Restarts.untruncatedChunk_lintegral _ _ _ _ _ _
    (fun outcome ↦ R.absoluteScores_nonneg loss outcome.1 outcome.2)]
  have h := R.untruncated_absoluteScores_summable_le H hτ hτ1 loss hloss μ
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦
    mul_nonneg (Restarts.geometricWeight_nonneg hτ.le hτ1 n)
      (ProbabilityVector.mean_nonneg _ (R.absoluteScores_nonneg loss n))) h.1]
  exact_mod_cast ENNReal.ofReal_le_ofReal h.2

theorem untruncated_chunk_absoluteScores_integrable (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (μ : ProbabilityVector ι) :
    Integrable (fun outcome ↦ R.absoluteScores loss outcome.1 outcome.2)
      (Restarts.untruncatedChunkLaw (H.kernel τ hτ) μ τ hτ hτ1).toMeasure := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (f := fun outcome : Restarts.UntruncatedChunkOutcome ι ↦
      R.absoluteScores loss outcome.1 outcome.2)
    (μ := (Restarts.untruncatedChunkLaw (H.kernel τ hτ) μ τ hτ hτ1).toMeasure)
    Measurable.of_discrete.aestronglyMeasurable
    (Filter.Eventually.of_forall fun outcome ↦
      R.absoluteScores_nonneg loss outcome.1 outcome.2)).mp
  exact ne_top_of_le_ne_top (by norm_num)
    (R.untruncated_chunk_absoluteScores_lintegral_le H hτ hτ1 loss hloss μ)

theorem untruncated_chunk_absoluteScores_le (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (μ : ProbabilityVector ι) :
    (∫ outcome, R.absoluteScores loss outcome.1 outcome.2
      ∂(Restarts.untruncatedChunkLaw (H.kernel τ hτ) μ τ hτ hτ1).toMeasure) ≤ 7 := by
  have h := R.untruncated_chunk_absoluteScores_lintegral_le H hτ hτ1 loss hloss μ
  rw [← ofReal_integral_eq_lintegral_ofReal
    (R.untruncated_chunk_absoluteScores_integrable H hτ hτ1 loss hloss μ)
    (Filter.Eventually.of_forall fun outcome ↦
      R.absoluteScores_nonneg loss outcome.1 outcome.2)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 7)).mp (by simpa using h)

end
end Tournament.Upper.ScoreRule

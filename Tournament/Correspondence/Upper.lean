module

public import Tournament.Probability.FinitePath
public import Tournament.Upper.ScoreTail
public import Tournament.Upper.UntruncatedScoreOccupation
public import Tournament.Upper.EstimatorDyadicTail
public import Tournament.Upper.Rounding
public import Tournament.Upper.CenteredBasis
public import Tournament.Probability.PartitionThinning

@[expose] public section

namespace Tournament.Correspondence

open scoped Classical BigOperators MeasureTheory
open Tournament Upper

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem holding_chains (H : HoldingFamily ι) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (H.kernel τ hτ).Reversible H.sampling ∧
    H.meanRefreshRate τ ≤ τ / 2 ∧
    (∀ s, H.refreshRate τ s ≤ 1 / 2 ∧
      H.meanRefreshRate τ / 3 ≤ H.refreshRate τ s ∧
      1 - H.refreshRate τ s ≤ H.kernel τ hτ s s ∧
      1 / 2 ≤ 1 - H.refreshRate τ s) ∧
    (∀ n t, t ≤ n → ∀ f : ι → ℝ,
      (FinitePath.law (H.kernel τ hτ) H.sampling n).mean
        (fun hist ↦ f (FinitePath.stateAt n hist t)) = H.sampling.mean f) ∧
    (∀ h : ℕ, 1 ≤ h →
      (FinitePath.law (H.kernel τ hτ) H.sampling (h-1)).mean
        (fun hist ↦ (Model.switchCount h (FinitePath.stateAt (h-1) hist) : ℝ)) ≤
          (h-1 : ℕ) * τ / 2) := by
  refine ⟨H.kernel_reversible hτ, H.meanRefreshRate_le hτ.le, ?_, ?_, ?_⟩
  · intro s
    have ha := H.refreshRate_le_half hτ.le s
    exact ⟨ha, H.refreshRate_ge_third_mean hτ hτ1 s,
      H.kernel_holding_lower hτ s, by linarith⟩
  · intro n t ht f
    exact FinitePath.stationary_stateAt_mean _ _ (H.kernel_stationary hτ) n t ht f
  · intro h hh
    exact FinitePath.holding_expected_switchCount_horizon H hτ h hh

theorem score_and_estimate_tails (H : HoldingFamily ι) (F : ι → ι → Prop)
    (m : ℕ) (_hm : 5 ≤ m) (hmax : DyadicRate.base m * H.maxRatio ≤ 1/4)
    (M δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hMlog : 100 * Real.log (2/δ) ≤ M) (n offset : ℕ)
    (hnκ : ((n : ℝ)+1) * DyadicRate.base m ≤ 1/8) :
    (∀ (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1), DyadicRate.base m ≤ τ →
      ∀ (R : ScoreRule F (H.kernel τ hτ) H.sampling)
        (loss : ℕ → ι → ℝ), (∀ t, BoundedLoss (loss t)) →
      ∀ (μ : ProbabilityVector ι) (remaining : ℕ),
        (Restarts.referenceChunkLaw (H.kernel τ hτ) μ τ hτ.le hτ1 remaining).probability
          (fun outcome ↦ R.stopEvent loss M (Restarts.length remaining outcome.1) outcome.2) ≤ δ) ∧
    (∀ (R : DyadicScoreRules H F m) (Ψ : ι → ι → ι → ℝ)
      (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (L₀ : ℝ),
      1 ≤ L₀ →
      (∀ s f, BoundedLoss f → ‖applyEstimator Ψ s f‖ ≤ L₀ * H.ratio s) →
      (∀ outcome : DyadicBlockOutcome ι m n,
        ‖dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome‖ ≤
          ((n : ℝ)+1) * L₀ / (3 * DyadicRate.base m)) ∧
      (dyadicBlockLaw H m R loss hloss M
        (TailConstants.threshold_ge_one hδ hδ1.le hMlog) offset n).probability
        (fun outcome ↦ 2 * M * L₀ / DyadicRate.base m <
          ‖dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome‖) ≤ δ/2) := by
  constructor
  · intro τ hτ hτ1 _hκτ R loss hloss μ remaining
    exact H.score_stopping_tail hτ hτ1 R loss hloss μ M δ hδ hδ1.le hMlog remaining
  · intro R Ψ loss hloss L₀ hL₀ hΨ
    exact H.estimator_tail m hmax R Ψ loss hloss M L₀ hL₀ hΨ δ hδ hδ1.le hMlog n offset hnκ

theorem spectral_structure (H : HoldingFamily ι) :
    (∀ i j, H.sampling i * H.generatorMatrix i j =
      (if i=j then H.refresh i else 0) - H.refresh i * H.refresh j) ∧
    (∀ i j, H.sampling i * H.generatorMatrix i j =
      H.sampling j * H.generatorMatrix j i) ∧
    H.generator (fun _ ↦ (1 : ℝ)) = 0 ∧
    (∀ f, FiniteKernel.weightedInner H.sampling f (H.generator f) = H.refresh.variance f) ∧
    (Fintype.card H.CenteredIndex = Fintype.card ι - 1 ∧
      H.constantCenteredBasis none = (fun _ ↦ (1 : ℝ)) ∧
      (∀ n, H.constantCenteredBasis (some n) = H.eigenvector n) ∧
      (∀ n, H.sampling.mean (H.eigenvector n) = 0 ∧
        H.generator (H.eigenvector n) = (fun i ↦ H.eigenvalue n * H.eigenvector n i) ∧
        1/2 ≤ H.eigenvalue n ∧ H.eigenvalue n ≤ H.maxRatio) ∧
      (∀ m n, FiniteKernel.weightedInner H.sampling (H.eigenvector m) (H.eigenvector n) =
        if m=n then 1 else 0) ∧
      (∀ τ (hτ : 0 < τ), (H.kernel τ hτ).act (fun _ ↦ (1 : ℝ)) = (fun _ ↦ (1 : ℝ)) ∧
        (∀ n, (H.kernel τ hτ).act (H.eigenvector n) =
          (fun i ↦ eigenMultiplier τ (H.eigenvalue n) * H.eigenvector n i)) ∧
        (∀ f, H.onePlusGeneratorMap τ (H.generatorResolvent τ hτ f) = f))) := by
  exact ⟨H.weighted_generatorMatrix, H.weighted_generatorMatrix_symmetric,
    H.generator_const 1, H.generator_quadratic, H.spectral_structure⟩

theorem occupation_potentials (H : HoldingFamily ι) (F : ι → ι → Prop)
    (κ τ : ℝ) (hκ : 0 < κ) (_hκ32 : κ ≤ 1/32)
    (hmax : κ * H.maxRatio ≤ 1/4) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1)
    (h : ℕ) (_hh : 1 ≤ h) (hhκ : (h : ℝ) * κ ≤ 1/8) :
    (∀ (μ : ProbabilityVector ι) (n : ℕ), n ≤ h →
      (FinitePath.law (H.kernel τ (lt_of_lt_of_le hκ hκτ)) μ n).mean
        (FinitePath.occupation H.ratio n) ≤ 5/κ) ∧
    (∀ (R : ScoreRule F (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling)
      (loss : ℕ → ι → ℝ), (∀ t, BoundedLoss (loss t)) →
      ∀ (μ : ProbabilityVector ι) (n : ℕ),
        (Restarts.referenceChunkLaw (H.kernel τ (lt_of_lt_of_le hκ hκτ)) μ τ
          (lt_of_lt_of_le hκ hκτ).le hτ1 n).mean
          (fun outcome ↦ R.absoluteScores loss (Restarts.length n outcome.1) outcome.2) ≤ 7) ∧
    (∀ (R : ScoreRule F (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling)
      (loss : ℕ → ι → ℝ), (∀ t, BoundedLoss (loss t)) →
      ∀ (μ : ProbabilityVector ι),
        MeasureTheory.Integrable
          (fun outcome : Restarts.UntruncatedChunkOutcome ι ↦
            R.absoluteScores loss outcome.1 outcome.2)
          (Restarts.untruncatedChunkLaw (H.kernel τ (lt_of_lt_of_le hκ hκτ)) μ τ
            (lt_of_lt_of_le hκ hκτ) hτ1).toMeasure ∧
        (∫ outcome, R.absoluteScores loss outcome.1 outcome.2
          ∂(Restarts.untruncatedChunkLaw (H.kernel τ (lt_of_lt_of_le hκ hκτ)) μ τ
            (lt_of_lt_of_le hκ hκτ) hτ1).toMeasure) ≤ 7) := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ n hn
    exact H.expected_ratio_occupation_le μ hκ hmax hκτ h hhκ n hn
  · intro R loss hloss μ n
    exact ScoreRule.reference_chunk_absoluteScores_le H (lt_of_lt_of_le hκ hκτ) hτ1 R loss hloss μ n
  · intro R loss hloss μ
    exact ⟨ScoreRule.untruncated_chunk_absoluteScores_integrable H
        (lt_of_lt_of_le hκ hκτ) hτ1 R loss hloss μ,
      ScoreRule.untruncated_chunk_absoluteScores_le H
        (lt_of_lt_of_le hκ hκτ) hτ1 R loss hloss μ⟩

theorem geometric_partition (χ : ℝ) (hχ : 0 ≤ χ) (hχ1 : χ < 1) (offset n : ℕ) :
    (∀ y : ℕ → ℝ,
      (GeometricPartition.quadratic χ y offset (n+1) =
        (Restarts.law (1-χ) (sub_nonneg.mpr hχ1.le) (by linarith) n).mean
          (fun cuts ↦ Restarts.chunkSquareSum y offset (Restarts.parts n cuts))) ∧
      0 ≤ GeometricPartition.quadratic χ y offset (n+1) ∧
      (∀ χ', 0 ≤ χ' → χ' ≤ χ →
        GeometricPartition.quadratic χ y offset (n+1) ≤
          (2*(1-χ')/(1-χ)) * GeometricPartition.quadratic χ' y offset (n+1)) ∧
      ((∑ t ∈ Finset.range (n+1), y (offset+t))^2 / (1+(1-χ)*(n : ℝ)) ≤
        GeometricPartition.quadratic χ y offset (n+1))) ∧
    (∀ y : ℕ → ℝ, GeometricPartition.quadratic χ y offset (n+1) ≤
      (2/(1-χ)) * ∑ t ∈ Finset.range (n+1), y (offset+t)^2) ∧
    (∀ (p : ProbabilityVector ι) (g : ℕ → ι → ℝ),
      GeometricPartition.vectorQuadratic p χ g offset (n+1) =
        (Restarts.law (1-χ) (sub_nonneg.mpr hχ1.le) (by linarith) n).mean
          (fun cuts ↦ GeometricPartition.chunkVectorSquareSum p g offset (Restarts.parts n cuts))) := by
  exact ⟨fun y ↦ GeometricPartition.geometric_partition hχ hχ1 y offset n,
    fun y ↦ GeometricPartition.quadratic_le_diagonal hχ hχ1 y offset (n+1),
    fun p g ↦ GeometricPartition.vectorQuadratic_eq_mean_chunkSquares p hχ hχ1.le g offset n⟩

theorem rounding (w : ProbabilityVector ι) (T : ℕ)
    (hK : 2 ≤ Fintype.card ι) (hT : 2 ≤ T)
    (hwfloor : ∀ i, 1 / ((Fintype.card ι : ℝ) * (T : ℝ)) ≤ w i) :
    (∀ i, (8/9) * w i ≤ Rounding.anchor w T (by omega) i ∧
      Rounding.anchor w T (by omega) i ≤ (5/4) * w i) ∧
    8 / (9 * (Fintype.card ι : ℝ) * (T : ℝ)) ≤
      (Rounding.anchor w T (by omega)).minimumWeight ∧
    (Rounding.anchor w T (by omega)).anchorLog ≤
      (4/3) * BlockParameters.logScale (Fintype.card ι) T ∧
    (∀ i, 1 ≤ Rounding.numerator w T i ∧
      Rounding.numerator w T i ≤ 4 * Fintype.card ι * T ∧
      Rounding.denominator w T ≤ 5 * Fintype.card ι * T) := by
  exact ⟨Rounding.anchor_bounds w hK hT hwfloor,
    Rounding.anchor_minimum_floor w hK hT hwfloor,
    Rounding.anchorLog_le_four_thirds w hK hT hwfloor,
    Rounding.numerator_denominator_bounds w hK hT hwfloor⟩

end
end Tournament.Correspondence

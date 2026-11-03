module

public import Tournament.Probability.EdgeExponential
public import Tournament.Upper.StoppedScoreBridge
public import Tournament.Probability.ExponentialTail

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open Upper FinitePath

variable {ι : Type*} [Fintype ι]

noncomputable section

theorem reference_absoluteScores_exponential_mean_le (H : HoldingFamily ι)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {F : ι → ι → Prop}
    (R : ScoreRule F (H.kernel τ hτ) H.sampling) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (μ : ProbabilityVector ι) (n : ℕ) :
    (Restarts.referenceChunkLaw (H.kernel τ hτ) μ τ (le_of_lt hτ) hτ1 n).mean
      (fun outcome ↦ Real.exp ((1/16)*R.absoluteScores loss (Restarts.length n outcome.1) outcome.2)) ≤ 2 := by
  let Q := StoppedChain.kernel (H.kernel τ hτ) τ (le_of_lt hτ) hτ1
  let d := StoppedChain.liftEdge (fun t i j ↦ |R.score t (loss t) i j|)
  have hd0 : ∀ t i j, 0 ≤ d t i j := by
    intro t i j
    cases i <;> cases j <;> simp [d, StoppedChain.liftEdge]
  have hbound : ∀ t i j, d t i j ≤ 1 := by
    intro t i j
    cases i with
    | none => cases j <;> norm_num [d, StoppedChain.liftEdge]
    | some i =>
      cases j with
      | none => norm_num [d, StoppedChain.liftEdge]
      | some j => exact R.score_abs_le_one t (hloss t) i j
  have hfuture : ∀ s, s ≤ n → ∀ i, futureEdgeValue Q d s (n-s) i ≤ 7 := by
    intro s _ i
    exact StoppedChain.absoluteScore_futureValue_le H hτ hτ1 R loss hloss s (n-s) i
  have hmean : (law Q (StoppedChain.initial μ) n).mean (edgeTotal d n) ≤ 7 := by
    calc
      _ = (Restarts.referenceChunkLaw (H.kernel τ hτ) μ τ (le_of_lt hτ) hτ1 n).mean
          (fun outcome ↦ R.absoluteScores loss (Restarts.length n outcome.1) outcome.2) :=
        StoppedChain.lifted_absoluteScores_mean H hτ hτ1 R loss μ n
      _ ≤ 7 := Upper.ScoreRule.reference_chunk_absoluteScores_le H hτ hτ1 R loss hloss μ n
  have hmgf := edge_sum_exponential_mean_le Q (StoppedChain.initial μ) d hd0 n 1 7 (by norm_num)
    hbound hfuture (1/16) (by norm_num) (by norm_num)
  have hQ : (law Q (StoppedChain.initial μ) n).mean (fun hist ↦ Real.exp ((1/16)*edgeTotal d n hist)) < 2 := by
    calc
      _ ≤ 1+(1/16)*(law Q (StoppedChain.initial μ) n).mean (edgeTotal d n)/(1-(1/16)*(1+7)) := hmgf
      _ < 2 := by norm_num; linarith
  calc
    _ = (law Q (StoppedChain.initial μ) n).mean (fun hist ↦ Real.exp ((1/16)*edgeTotal d n hist)) :=
      (StoppedChain.lifted_absoluteScores_functional_mean H hτ hτ1 R loss μ n (fun x ↦ Real.exp ((1/16)*x))).symm
    _ ≤ 2 := le_of_lt hQ

theorem score_stopping_tail (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (μ : ProbabilityVector ι)
    (M δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlog : 100*Real.log (2/δ) ≤ M) (n : ℕ) :
    (Restarts.referenceChunkLaw (H.kernel τ hτ) μ τ (le_of_lt hτ) hτ1 n).probability
      (fun outcome ↦ R.stopEvent loss M (Restarts.length n outcome.1) outcome.2) ≤ δ := by
  let ν := Restarts.referenceChunkLaw (H.kernel τ hτ) μ τ (le_of_lt hτ) hτ1 n
  let V := fun outcome : Restarts.ChunkOutcome ι n ↦ R.absoluteScores loss (Restarts.length n outcome.1) outcome.2
  have hM : 1 ≤ M := TailConstants.threshold_ge_one hδ hδ1 hMlog
  have hevent : ∀ outcome, R.stopEvent loss M (Restarts.length n outcome.1) outcome.2 → M-1 < V outcome := by
    intro outcome hstop
    exact R.stop_implies_absoluteScores_gt loss M hM (Restarts.length n outcome.1) outcome.2 hstop
  have hmgf := H.reference_absoluteScores_exponential_mean_le hτ hτ1 R loss hloss μ n
  have hmarkov := ν.exponential_markov_le V (1/16) (M-1) (by norm_num)
  calc
    ν.probability (fun outcome ↦ R.stopEvent loss M (Restarts.length n outcome.1) outcome.2) ≤
        ν.probability (fun outcome ↦ M-1 < V outcome) := ν.probability_mono hevent
    _ ≤ Real.exp (-(1/16)*(M-1))*ν.mean (fun outcome ↦ Real.exp ((1/16)*V outcome)) := hmarkov
    _ ≤ Real.exp (-(1/16)*(M-1))*2 := mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = 2*Real.exp (-(M-1)/16) := by
      have heq : -(1/16:ℝ)*(M-1) = -(M-1)/16 := by ring
      rw [heq, mul_comm]
    _ ≤ δ := TailConstants.score_tail_le hδ hδ1 hMlog

end
end Tournament.HoldingFamily

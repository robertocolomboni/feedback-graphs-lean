module

public import Tournament.Upper.BlockPolicy

@[expose] public section

namespace Tournament.Upper

open scoped Classical

noncomputable section

variable {ι : Type*} [Fintype ι] {F : ι → ι → Prop}

theorem probing_block (H : HoldingFamily ι) (m : ℕ) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (hobs : ScoreRule.EstimatorObservable F Ψ)
    (M δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlog : 100*Real.log (2/δ) ≤ M) :
    ∃ π : Model.RestartComparisonPolicy ι m,
      π.rates = DyadicRate.law m ∧ π.restart = DyadicRate.rate m ∧
      (∀ j offset n, ((π.chunks j).chunk offset n).initial = H.sampling) ∧
      (∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) offset n outcome,
        π.law F loss offset n outcome =
          dyadicBlockLaw H m R loss _hloss M (TailConstants.threshold_ge_one hδ hδ1 hMlog) offset n outcome) ∧
      (∃ output : (j : Fin (m+1)) → (offset : ℕ) → (ns : List ℕ) → BlockTranscript ι ns → ι → ℝ,
        ∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) offset n
          (outcome : DyadicBlockOutcome ι m n) k,
          output outcome.1 offset (Restarts.parts n outcome.2.1)
            (recordBlockComparisons F loss offset (Restarts.parts n outcome.2.1) outcome.2.2) k =
              dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome k) ∧
      ∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) (default : ι) offset n,
        (π.law F loss offset n).mean
          (fun outcome ↦ Model.accumulatedLoss (n+1) (fun t ↦ loss (offset+t))
            (blockActions default (Restarts.parts n outcome.2.1) outcome.2.2)) ≤
          H.sampling.mean (blockLoss (fun t ↦ loss (offset+t)) (n+1)) -
            ScoreRule.steeringStrength M*blockProbingGain H m loss offset (n+1)+
            ScoreRule.steeringStrength M*δ*((n:ℝ)+1)^3 ∧
        (π.law F loss offset n).mean (fun outcome ↦
          (Model.switchCount (n+1) (blockActions default (Restarts.parts n outcome.2.1) outcome.2.2) : ℝ)) ≤
            (13/8)*(DyadicRate.base m*(1+(m:ℝ)/2))*((n:ℝ)+1) := by
  let hM := TailConstants.threshold_ge_one hδ hδ1 hMlog
  refine ⟨dyadicComparisonPolicy H m R M,rfl,rfl,?_,?_,?_,?_⟩
  · intro j offset n
    rfl
  · intro loss hloss offset n outcome
    exact dyadicComparisonPolicy_law H m R M hM loss hloss offset n outcome
  · exact dyadicBlockEstimate_observable H m R Ψ hobs M
  · intro loss hloss default offset n
    constructor
    · rw [dyadicComparisonPolicy_mean H m R M hM loss hloss]
      exact dyadic_block_loss_bound H m R loss hloss M hM δ hδ hδ1 hMlog default offset n
    · rw [dyadicComparisonPolicy_mean H m R M hM loss hloss]
      exact dyadic_block_switchCount_mean_le H m R loss hloss M hM default n offset

end
end Tournament.Upper

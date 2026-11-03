module

public import Tournament.Upper.BlockGuarantee
public import Tournament.Probability.Extensionality

@[expose] public section

namespace Tournament.Upper

open scoped Classical
open BlockParameters

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem dyadicTruncatedEstimate_observable {F : ι → ι → Prop} (H : HoldingFamily ι)
    (m : ℕ) (R : DyadicScoreRules H F m) (Ψ : ι → ι → ι → ℝ)
    (hobs : ScoreRule.EstimatorObservable F Ψ) (M η : ℝ) :
    ∃ output : (j : Fin (m+1)) → (offset : ℕ) → (ns : List ℕ) → BlockTranscript ι ns → ι → ℝ,
      ∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) offset n
        (outcome : DyadicBlockOutcome ι m n),
        output outcome.1 offset (Restarts.parts n outcome.2.1)
          (recordBlockComparisons F loss offset (Restarts.parts n outcome.2.1) outcome.2.2)=
            Model.truncateEstimate η (dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome) := by
  obtain ⟨raw,hraw⟩ := dyadicBlockEstimate_observable H m R Ψ hobs M
  refine ⟨fun j offset ns log ↦ Model.truncateEstimate η (raw j offset ns log),?_⟩
  intro loss hloss offset n outcome
  have hid : raw outcome.1 offset (Restarts.parts n outcome.2.1)
      (recordBlockComparisons F loss offset (Restarts.parts n outcome.2.1) outcome.2.2)=
        dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome :=
    funext (fun i ↦ hraw loss hloss offset n outcome i)
  dsimp only
  rw [hid]

theorem prepared_block_policy (F : ι → ι → Prop) (hF : IsTournament F)
    (w : ProbabilityVector ι) (hw : ∀ i, 0<w i) (T m : ℕ)
    (hK : 2≤Fintype.card ι) (hT : 2≤T) (hm : 5≤m)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) :
    let H := preparedHolding F hF w hw m hm
    let R := preparedRules F hF w hw m hm
    let Ψ := preparedEstimator F hF w hw m hm
    let M := threshold (Fintype.card ι) T
    let η := learningRate (Fintype.card ι) T m
    ∃ π : Model.RestartComparisonPolicy ι m,
      (∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) offset n outcome,
        π.law F loss offset n outcome=dyadicBlockLaw H m R loss _hloss M (threshold_ge_one hK hT) offset n outcome) ∧
      (∃ output : (j : Fin (m+1)) → (offset : ℕ) → (ns : List ℕ) → BlockTranscript ι ns → ι → ℝ,
        ∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) offset n
          (outcome : DyadicBlockOutcome ι m n),
          output outcome.1 offset (Restarts.parts n outcome.2.1)
            (recordBlockComparisons F loss offset (Restarts.parts n outcome.2.1) outcome.2.2)=
              Model.truncateEstimate η (dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome)) ∧
      ∀ (loss : ℕ → ι → ℝ) (_hloss : ∀ t, BoundedLoss (loss t)) (default : ι) offset n (_hn : n+1≤horizon m),
        OneBlockGuarantee (π.law F loss offset n) w (blockLoss (fun t ↦ loss (offset+t)) (n+1))
          (dyadicBlockCorrectedEstimate H m R Ψ loss M offset n)
          (blockCost default loss offset) (blockInternalSwitches default) T m n := by
  let H := preparedHolding F hF w hw m hm
  let R := preparedRules F hF w hw m hm
  let Ψ := preparedEstimator F hF w hw m hm
  let M := threshold (Fintype.card ι) T
  let η := learningRate (Fintype.card ι) T m
  refine ⟨dyadicComparisonPolicy H m R M,?_,?_,?_⟩
  · intro loss hloss offset n outcome
    exact dyadicComparisonPolicy_law H m R M (threshold_ge_one hK hT) loss hloss offset n outcome
  · have hbal := (prepared_inputs F hF w hw m hm).2.2.2.2
    exact dyadicTruncatedEstimate_observable H m R Ψ hbal.observable M η
  · intro loss hloss default offset n hn
    have hlaw : (dyadicComparisonPolicy H m R M).law F loss offset n=
        dyadicBlockLaw H m R loss hloss M (threshold_ge_one hK hT) offset n := by
      apply ProbabilityVector.ext_weights
      intro outcome
      exact dyadicComparisonPolicy_law H m R M (threshold_ge_one hK hT) loss hloss offset n outcome
    rw [hlaw]
    exact prepared_block_guarantee F hF w hw T m hK hT hm hwfloor loss hloss default offset n hn

end
end Tournament.Upper

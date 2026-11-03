module

public import Tournament.Probability.DyadicRate
public import Tournament.Upper.EstimatorBlockTail

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace ProbabilityVector

variable {Ω : Type*} [Fintype Ω] {β : Ω → Type*} [∀ x, Fintype (β x)]

theorem sigmaJoint_probability (μ : ProbabilityVector Ω) (κ : (x : Ω) → ProbabilityVector (β x))
    (A : Sigma β → Prop) :
    (μ.sigmaJoint κ).probability A = μ.mean (fun x ↦ (κ x).probability (fun y ↦ A ⟨x,y⟩)) :=
  sigmaJoint_mean μ κ (fun outcome ↦ if A outcome then 1 else 0)

end ProbabilityVector

namespace Upper

variable {ι : Type*} [Fintype ι]

abbrev DyadicScoreRules (H : HoldingFamily ι) (F : ι → ι → Prop) (m : ℕ) :=
  (j : Fin (m+1)) → ScoreRule F (H.kernel (DyadicRate.rate m j) (DyadicRate.rate_pos m j)) H.sampling

abbrev DyadicBlockOutcome (ι : Type*) (m n : ℕ) :=
  (_j : Fin (m+1)) × (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins)

instance dyadicBlockOutcomeFintype (m n : ℕ) : Fintype (DyadicBlockOutcome ι m n) :=
  inferInstanceAs (Fintype ((_j : Fin (m+1)) × (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins)))

def dyadicBlockLaw (H : HoldingFamily ι) {F : ι → ι → Prop} (m : ℕ) (R : DyadicScoreRules H F m)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M) (offset n : ℕ) :
    ProbabilityVector (DyadicBlockOutcome ι m n) :=
  (DyadicRate.law m).sigmaJoint (fun j ↦ partitionedBlockLaw (R j) loss hloss M hM
    (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) offset n)

def dyadicBlockCorrectedEstimate (H : HoldingFamily ι) {F : ι → ι → Prop} (m : ℕ)
    (R : DyadicScoreRules H F m) (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ)
    (M : ℝ) (offset n : ℕ) (outcome : DyadicBlockOutcome ι m n) : ι → ℝ :=
  blockCorrectedEstimate (R outcome.1) Ψ loss M offset (Restarts.parts n outcome.2.1) outcome.2.2

end Upper

namespace HoldingFamily

open Upper

variable {ι : Type*} [Fintype ι]

theorem estimator_tail_dyadic (H : HoldingFamily ι) {F : ι → ι → Prop}
    (m : ℕ) (hκmax : DyadicRate.base m*H.maxRatio ≤ 1/4) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M : ℝ) (hM : 1 ≤ M) (L0 : ℝ) (hL0 : 1 ≤ L0)
    (hΨ : ∀ s loss, BoundedLoss loss → ∀ k, |applyEstimator Ψ s loss k| ≤ L0*H.ratio s)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlog : 100*Real.log (2/δ) ≤ M)
    (n offset : ℕ) (hnκ : ((n:ℝ)+1)*DyadicRate.base m ≤ 1/8) :
    (∀ outcome : DyadicBlockOutcome ι m n,
      ‖dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome‖ ≤
        ((n:ℝ)+1)*L0/(3*DyadicRate.base m)) ∧
    (dyadicBlockLaw H m R loss hloss M hM offset n).probability
      (fun outcome ↦ 2*M*L0/DyadicRate.base m <
        ‖dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome‖) ≤ δ/2 := by
  constructor
  · intro outcome
    have h := H.blockCorrectedEstimate_deterministic_bound (DyadicRate.base_pos m) hκmax
      (DyadicRate.base_le_rate m outcome.1) (R outcome.1) Ψ loss hloss M hM L0 (by linarith) hΨ
      (Restarts.parts n outcome.2.1) offset outcome.2.2
    simpa only [dyadicBlockCorrectedEstimate, Restarts.parts_totalRounds, Nat.cast_add, Nat.cast_one] using h
  · change ((DyadicRate.law m).sigmaJoint (fun j ↦ partitionedBlockLaw (R j) loss hloss M hM
      (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) offset n)).probability
      (fun outcome : (_j : Fin (m+1)) × (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins) ↦
        2*M*L0/DyadicRate.base m <
          ‖blockCorrectedEstimate (R outcome.1) Ψ loss M offset (Restarts.parts n outcome.2.1) outcome.2.2‖) ≤ δ/2
    rw [ProbabilityVector.sigmaJoint_probability]
    calc
      _ ≤ (DyadicRate.law m).mean (fun _ ↦ δ/2) := by
        apply ProbabilityVector.mean_mono
        intro j
        exact H.played_block_estimator_tail (DyadicRate.base_pos m) hκmax (DyadicRate.base_le_rate m j)
          (DyadicRate.rate_le_one m j) (R j) Ψ loss hloss M hM L0 hL0 hΨ δ hδ hδ1 hMlog n offset hnκ
      _ = δ/2 := ProbabilityVector.mean_const _ _

theorem estimator_tail (H : HoldingFamily ι) {F : ι → ι → Prop}
    (m : ℕ) (hκmax : DyadicRate.base m*H.maxRatio ≤ 1/4) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M L0 : ℝ) (hL0 : 1 ≤ L0)
    (hΨ : ∀ s loss, BoundedLoss loss → ‖applyEstimator Ψ s loss‖ ≤ L0*H.ratio s)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlog : 100*Real.log (2/δ) ≤ M)
    (n offset : ℕ) (hnκ : ((n:ℝ)+1)*DyadicRate.base m ≤ 1/8) :
    (∀ outcome : DyadicBlockOutcome ι m n,
      ‖dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome‖ ≤
        ((n:ℝ)+1)*L0/(3*DyadicRate.base m)) ∧
    (dyadicBlockLaw H m R loss hloss M (TailConstants.threshold_ge_one hδ hδ1 hMlog) offset n).probability
      (fun outcome ↦ 2*M*L0/DyadicRate.base m <
        ‖dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome‖) ≤ δ/2 := by
  apply H.estimator_tail_dyadic m hκmax R Ψ loss hloss M
    (TailConstants.threshold_ge_one hδ hδ1 hMlog) L0 hL0 _ δ hδ hδ1 hMlog n offset hnκ
  intro s f hf k
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (applyEstimator Ψ s f) k).trans (hΨ s f hf)

end HoldingFamily
end
end Tournament

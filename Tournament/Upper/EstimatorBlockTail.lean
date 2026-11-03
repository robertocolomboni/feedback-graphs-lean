module

public import Tournament.Upper.EstimatorBlockBounds
public import Tournament.Probability.ExponentialTail

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open Upper FinitePath

variable {ι : Type*} [Fintype ι]

noncomputable section

theorem blockCorrectedEstimate_deterministic_bound (H : HoldingFamily ι)
    {κ τ : ℝ} (hκ : 0 < κ) (hκmax : κ*H.maxRatio ≤ 1/4) (hκτ : κ ≤ τ)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M : ℝ) (hM : 1 ≤ M) (L0 : ℝ) (hL0 : 0 ≤ L0)
    (hΨ : ∀ s loss, BoundedLoss loss → ∀ k, |applyEstimator Ψ s loss k| ≤ L0*H.ratio s)
    (ns : List ℕ) (offset : ℕ) (outcome : BlockOutcome ι ns) :
    ‖blockCorrectedEstimate R Ψ loss M offset ns outcome‖ ≤ (Restarts.totalRounds ns:ℝ)*L0/(3*κ) := by
  have hmax : H.maxRatio ≤ 1/(4*κ) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*κ)).mpr
    nlinarith
  have hratio : ∀ i, H.ratio i ≤ 1/(4*κ) := fun i ↦ le_trans (H.ratio_le_maxRatio i) hmax
  have hV := blockRatioTotal_le H.ratio (1/(4*κ)) hratio ns outcome
  calc
    _ ≤ (4/3)*L0*blockRatioTotal H.ratio ns outcome :=
      blockCorrectedEstimate_norm_le R Ψ loss hloss M hM H.ratio (fun i ↦ le_of_lt (H.ratio_pos i))
        L0 hL0 (fun t s k ↦ hΨ s (loss t) (hloss t) k) ns offset outcome
    _ ≤ (4/3)*L0*((Restarts.totalRounds ns:ℝ)*(1/(4*κ))) :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    _ = _ := by field_simp

theorem played_block_estimator_tail (H : HoldingFamily ι)
    {κ τ : ℝ} (hκ : 0 < κ) (hκmax : κ*H.maxRatio ≤ 1/4) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M : ℝ) (hM : 1 ≤ M) (L0 : ℝ) (hL0 : 1 ≤ L0)
    (hΨ : ∀ s loss, BoundedLoss loss → ∀ k, |applyEstimator Ψ s loss k| ≤ L0*H.ratio s)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlog : 100*Real.log (2/δ) ≤ M)
    (n offset : ℕ) (hnκ : ((n:ℝ)+1)*κ ≤ 1/8) :
    (partitionedBlockLaw R loss hloss M hM τ
      (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 offset n).probability
      (fun outcome ↦ 2*M*L0/κ <
        ‖blockCorrectedEstimate R Ψ loss M offset (Restarts.parts n outcome.1) outcome.2‖) ≤ δ/2 := by
  let μ := partitionedBlockLaw R loss hloss M hM τ (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 offset n
  let V := fun outcome : (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins) ↦
    blockRatioTotal H.ratio (Restarts.parts n outcome.1) outcome.2
  let Z := fun outcome : (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins) ↦
    blockCorrectedEstimate R Ψ loss M offset (Restarts.parts n outcome.1) outcome.2
  have hL0' : 0 ≤ L0 := by linarith
  have hnorm (outcome) : ‖Z outcome‖ ≤ (4/3)*L0*V outcome :=
    blockCorrectedEstimate_norm_le R Ψ loss hloss M hM H.ratio (fun i ↦ le_of_lt (H.ratio_pos i))
      L0 hL0' (fun t s k ↦ hΨ s (loss t) (hloss t) k) _ offset _
  have hevent : ∀ outcome, 2*M*L0/κ < ‖Z outcome‖ → 3*M/(2*κ) < V outcome := by
    intro outcome hZ
    by_contra hV
    have hV' : V outcome ≤ 3*M/(2*κ) := le_of_not_gt hV
    have hmul := mul_le_mul_of_nonneg_left hV' (by positivity : 0 ≤ (4/3)*L0)
    have heq : (4/3)*L0*(3*M/(2*κ)) = 2*M*L0/κ := by field_simp; ring
    rw [heq] at hmul
    linarith [hnorm outcome]
  have hmgf := H.played_block_ratio_exponential_mean_le hκ hκmax hκτ hτ1 R loss hloss M hM n offset hnκ
  have htail := μ.exponential_tail_le V (κ/12) (3*M/(2*κ)) (1/32) (by positivity) hmgf
  have hprod : (κ/12)*(3*M/(2*κ)) = M/8 := by field_simp; ring
  rw [hprod] at htail
  calc
    μ.probability (fun outcome ↦ 2*M*L0/κ < ‖Z outcome‖) ≤ μ.probability (fun outcome ↦ 3*M/(2*κ) < V outcome) :=
      μ.probability_mono hevent
    _ ≤ Real.exp (1/32-M/8) := htail
    _ ≤ δ/2 := TailConstants.estimator_tail_le_half hδ hδ1 hMlog

theorem estimator_tail_fixed_rate (H : HoldingFamily ι)
    {κ τ : ℝ} (hκ : 0 < κ) (hκmax : κ*H.maxRatio ≤ 1/4) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M : ℝ) (hM : 1 ≤ M) (L0 : ℝ) (hL0 : 1 ≤ L0)
    (hΨ : ∀ s loss, BoundedLoss loss → ∀ k, |applyEstimator Ψ s loss k| ≤ L0*H.ratio s)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlog : 100*Real.log (2/δ) ≤ M)
    (n offset : ℕ) (hnκ : ((n:ℝ)+1)*κ ≤ 1/8) :
    (∀ outcome : (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins),
      ‖blockCorrectedEstimate R Ψ loss M offset (Restarts.parts n outcome.1) outcome.2‖ ≤
        ((n:ℝ)+1)*L0/(3*κ)) ∧
    (partitionedBlockLaw R loss hloss M hM τ
      (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 offset n).probability
      (fun outcome ↦ 2*M*L0/κ <
        ‖blockCorrectedEstimate R Ψ loss M offset (Restarts.parts n outcome.1) outcome.2‖) ≤ δ/2 := by
  constructor
  · intro outcome
    have h := H.blockCorrectedEstimate_deterministic_bound hκ hκmax hκτ R Ψ loss hloss M hM L0
      (by linarith) hΨ (Restarts.parts n outcome.1) offset outcome.2
    simpa only [Restarts.parts_totalRounds, Nat.cast_add, Nat.cast_one] using h
  · exact H.played_block_estimator_tail hκ hκmax hκτ hτ1 R Ψ loss hloss M hM L0 hL0 hΨ δ hδ hδ1 hMlog n offset hnκ

end
end Tournament.HoldingFamily

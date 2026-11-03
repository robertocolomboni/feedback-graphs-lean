module

public import Tournament.Upper.RoundedPreparation

@[expose] public section

namespace Tournament.Computation.OptimizerTransfer

open Upper BlockParameters
open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem optimal_weight_bound (F : ι → ι → Prop) (hF : IsTournament F)
    {v : ProbabilityVector ι} (A : ComparisonAssignment F v)
    (hopt : ∀ B : ComparisonAssignment F v, A.totalWeight≤B.totalWeight) :
    A.totalWeight≤3*v.anchorLog :=
  (hopt (RootedPivots.randomizedAssignment F hF v A.anchor_pos)).trans
    (RootedPivots.randomizedAssignment_bound F hF v A.anchor_pos)

theorem rounded_inputs_for_optimizer (F : ι → ι → Prop) (hF : IsTournament F)
    (w : ProbabilityVector ι) (hw : ∀ i, 0<w i) (T : ℕ)
    (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (m : ℕ) (hm : 5≤m)
    (A : ComparisonAssignment F (Rounding.anchor w T (by omega)))
    (hopt : ∀ B : ComparisonAssignment F (Rounding.anchor w T (by omega)),
      A.totalWeight≤B.totalWeight) :
    let v := Rounding.anchor w T (by omega)
    let H := A.preparedFamily w hw (DyadicRate.base m) (DyadicRate.base_pos m)
      (base_le_one_thirtytwo hm)
    DyadicRate.base m*H.maxRatio≤1/4 ∧ (∀ i, w i≤2*H.sampling i) ∧
      (∑ i, |H.sampling i-w i|)≤8*DyadicRate.base m ∧ 1≤128*v.anchorLog ∧
        128*v.anchorLog≤(2:ℝ)^8*logScale (Fintype.card ι) T ∧
          BalancedEstimator F H w (A.estimator w H.sampling) (128*v.anchorLog) := by
  let v := Rounding.anchor w T (show 0<T by omega)
  have hhalf (i : ι) : w i/2≤v i := by
    have h := (Rounding.anchor_bounds w hK hT hwfloor i).1
    nlinarith [w.nonneg i]
  have htwo (i : ι) : v i≤2*w i := by
    have h := (Rounding.anchor_bounds w hK hT hwfloor i).2
    nlinarith [w.nonneg i]
  rcases A.balanced_estimator_from_assignment w hw hhalf htwo
    (optimal_weight_bound F hF A hopt) (DyadicRate.base m)
    (DyadicRate.base_pos m) (base_le_one_thirtytwo hm) with ⟨hmax,hdom,hdist,hL,hbal⟩
  refine ⟨hmax.le,?_,hdist,hL,?_,hbal⟩
  · intro i
    have hp := (A.preparedFamily w hw (DyadicRate.base m) (DyadicRate.base_pos m)
      (base_le_one_thirtytwo hm)).sampling.nonneg i
    have hi := hdom i
    nlinarith
  · have hl : v.anchorLog≤(4/3)*logScale (Fintype.card ι) T :=
      Rounding.anchorLog_le_four_thirds w hK hT hwfloor
    have hΛ := logScale_ge_one hK hT
    norm_num
    linarith

theorem rounded_block_guarantee_for_optimizer (F : ι → ι → Prop) (hF : IsTournament F)
    (w : ProbabilityVector ι) (hw : ∀ i, 0<w i) (T : ℕ)
    (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (m : ℕ) (hm : 5≤m)
    (A : ComparisonAssignment F (Rounding.anchor w T (by omega)))
    (hopt : ∀ B : ComparisonAssignment F (Rounding.anchor w T (by omega)),
      A.totalWeight≤B.totalWeight)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (offset n : ℕ)
    (hn : n+1≤horizon m) :
    let H := A.preparedFamily w hw (DyadicRate.base m) (DyadicRate.base_pos m)
      (base_le_one_thirtytwo hm)
    let R : DyadicScoreRules H F m := fun j =>
      tournamentScoreRule F hF _ _ H.sampling_pos
        (H.kernel_reversible (DyadicRate.rate_pos m j))
        (H.kernel_holding_ge_half (DyadicRate.rate_pos m j))
    OneBlockGuarantee (dyadicBlockLaw H m R loss hloss (threshold (Fintype.card ι) T)
      (threshold_ge_one hK hT) offset n)
      w (blockLoss (fun t => loss (offset+t)) (n+1))
      (dyadicBlockCorrectedEstimate H m R (A.estimator w H.sampling)
        loss (threshold (Fintype.card ι) T) offset n)
      (blockCost default loss offset) (blockInternalSwitches default) T m n := by
  rcases rounded_inputs_for_optimizer F hF w hw T hK hT hwfloor m hm A hopt with
    ⟨hmax,hwp,hdist,hL,hLΛ,hbal⟩
  exact block_guarantee_from_inputs _ w T m hK hT hm _ _
    (128*(Rounding.anchor w T (by omega)).anchorLog) hL hLΛ hmax hwp hdist hbal
    loss hloss default offset n hn

end
end Tournament.Computation.OptimizerTransfer

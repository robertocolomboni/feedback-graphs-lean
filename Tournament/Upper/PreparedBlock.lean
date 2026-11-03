module

public import Tournament.Upper.BlockParameters
public import Tournament.Upper.BlockTheorem

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

def preparedHolding (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (m : ℕ) (hm : 5≤m) : HoldingFamily ι :=
  (optimizedAssignment F hF w hw).preparedFamily w hw (DyadicRate.base m)
    (DyadicRate.base_pos m) (BlockParameters.base_le_one_thirtytwo hm)

def preparedEstimator (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (m : ℕ) (hm : 5≤m) : ι → ι → ι → ℝ :=
  (optimizedAssignment F hF w hw).estimator w (preparedHolding F hF w hw m hm).sampling

def preparedRules (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (m : ℕ) (hm : 5≤m) : DyadicScoreRules (preparedHolding F hF w hw m hm) F m :=
  fun j ↦ tournamentScoreRule F hF _ _ (preparedHolding F hF w hw m hm).sampling_pos
    ((preparedHolding F hF w hw m hm).kernel_reversible (DyadicRate.rate_pos m j))
    ((preparedHolding F hF w hw m hm).kernel_holding_ge_half (DyadicRate.rate_pos m j))

theorem prepared_inputs (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (m : ℕ) (hm : 5≤m) :
    let H := preparedHolding F hF w hw m hm
    DyadicRate.base m*H.maxRatio≤1/4 ∧ (∀ i, w i≤2*H.sampling i) ∧
      (∑ i, |H.sampling i-w i|)≤8*DyadicRate.base m ∧ 1≤128*w.anchorLog ∧
        BalancedEstimator F H w (preparedEstimator F hF w hw m hm) (128*w.anchorLog) := by
  rcases prepare_balanced F hF w hw (DyadicRate.base m) (DyadicRate.base_pos m)
    (BlockParameters.base_le_one_thirtytwo hm) with ⟨_,hmax,hdom,hdist,hL,hbal⟩
  refine ⟨hmax.le,?_,hdist,hL,hbal⟩
  intro i
  have hp := (preparedHolding F hF w hw m hm).sampling.nonneg i
  have hi : w i≤(8/7)*(preparedHolding F hF w hw m hm).sampling i := hdom i
  nlinarith

end
end Tournament.Upper

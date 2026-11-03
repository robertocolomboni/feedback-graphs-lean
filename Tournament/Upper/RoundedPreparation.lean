module

public import Tournament.Upper.Rounding
public import Tournament.Upper.PreparedBlockPolicy

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open BlockParameters

noncomputable section

variable {ι : Type*} [Fintype ι]

def roundedHolding (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (T : ℕ) (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (m : ℕ) (hm : 5≤m) : HoldingFamily ι :=
  (optimizedAssignment F hF (Rounding.anchor w T (by omega)) (Rounding.anchor_pos w hK hT hwfloor)).preparedFamily
    w hw (DyadicRate.base m) (DyadicRate.base_pos m) (base_le_one_thirtytwo hm)

def roundedEstimator (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (T : ℕ) (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (m : ℕ) (hm : 5≤m) : ι → ι → ι → ℝ :=
  (optimizedAssignment F hF (Rounding.anchor w T (by omega)) (Rounding.anchor_pos w hK hT hwfloor)).estimator
    w (roundedHolding F hF w hw T hK hT hwfloor m hm).sampling

def roundedRules (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (T : ℕ) (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (m : ℕ) (hm : 5≤m) :
    DyadicScoreRules (roundedHolding F hF w hw T hK hT hwfloor m hm) F m :=
  fun j ↦ tournamentScoreRule F hF _ _ (roundedHolding F hF w hw T hK hT hwfloor m hm).sampling_pos
    ((roundedHolding F hF w hw T hK hT hwfloor m hm).kernel_reversible (DyadicRate.rate_pos m j))
    ((roundedHolding F hF w hw T hK hT hwfloor m hm).kernel_holding_ge_half (DyadicRate.rate_pos m j))

theorem rounded_inputs (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (T : ℕ) (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (m : ℕ) (hm : 5≤m) :
    let v := Rounding.anchor w T (by omega)
    let H := roundedHolding F hF w hw T hK hT hwfloor m hm
    DyadicRate.base m*H.maxRatio≤1/4 ∧ (∀ i, w i≤2*H.sampling i) ∧
      (∑ i, |H.sampling i-w i|)≤8*DyadicRate.base m ∧ 1≤128*v.anchorLog ∧
        128*v.anchorLog≤(2:ℝ)^8*logScale (Fintype.card ι) T ∧
          BalancedEstimator F H w (roundedEstimator F hF w hw T hK hT hwfloor m hm) (128*v.anchorLog) := by
  let v := Rounding.anchor w T (show 0<T by omega)
  have hv : ∀ i, 0<v i := Rounding.anchor_pos w hK hT hwfloor
  have hhalf (i : ι) : w i/2≤v i := by
    have hl : (8/9)*w i≤v i := (Rounding.anchor_bounds w hK hT hwfloor i).1
    nlinarith [w.nonneg i]
  have htwo (i : ι) : v i≤2*w i := by
    have hu : v i≤(5/4)*w i := (Rounding.anchor_bounds w hK hT hwfloor i).2
    nlinarith [w.nonneg i]
  rcases optimal_preparation_balanced F hF v w hv hw hhalf htwo (DyadicRate.base m)
    (DyadicRate.base_pos m) (base_le_one_thirtytwo hm) with ⟨_,hmax,hdom,hdist,hL,hbal⟩
  refine ⟨hmax.le,?_,hdist,hL,?_,hbal⟩
  · intro i
    have hp := (roundedHolding F hF w hw T hK hT hwfloor m hm).sampling.nonneg i
    have hi : w i≤(8/7)*(roundedHolding F hF w hw T hK hT hwfloor m hm).sampling i := hdom i
    nlinarith
  · have hl : v.anchorLog≤(4/3)*logScale (Fintype.card ι) T := Rounding.anchorLog_le_four_thirds w hK hT hwfloor
    have hΛ := logScale_ge_one hK hT
    norm_num
    linarith

theorem rounded_block_guarantee (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (T : ℕ) (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (m : ℕ) (hm : 5≤m)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (offset n : ℕ)
    (hn : n+1≤horizon m) :
    let H := roundedHolding F hF w hw T hK hT hwfloor m hm
    let R := roundedRules F hF w hw T hK hT hwfloor m hm
    OneBlockGuarantee (dyadicBlockLaw H m R loss hloss (threshold (Fintype.card ι) T) (threshold_ge_one hK hT) offset n)
      w (blockLoss (fun t ↦ loss (offset+t)) (n+1))
      (dyadicBlockCorrectedEstimate H m R (roundedEstimator F hF w hw T hK hT hwfloor m hm)
        loss (threshold (Fintype.card ι) T) offset n)
      (blockCost default loss offset) (blockInternalSwitches default) T m n := by
  rcases rounded_inputs F hF w hw T hK hT hwfloor m hm with ⟨hmax,hwp,hdist,hL,hLΛ,hbal⟩
  exact block_guarantee_from_inputs (roundedHolding F hF w hw T hK hT hwfloor m hm) w T m hK hT hm
    (roundedRules F hF w hw T hK hT hwfloor m hm) (roundedEstimator F hF w hw T hK hT hwfloor m hm)
    (128*(Rounding.anchor w T (by omega)).anchorLog) hL hLΛ hmax hwp hdist hbal loss hloss default offset n hn

theorem rounded_block_policy (F : ι → ι → Prop) (hF : IsTournament F) (w : ProbabilityVector ι)
    (hw : ∀ i, 0<w i) (T : ℕ) (hK : 2≤Fintype.card ι) (hT : 2≤T)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i) (m : ℕ) (hm : 5≤m) :
    let H := roundedHolding F hF w hw T hK hT hwfloor m hm
    let R := roundedRules F hF w hw T hK hT hwfloor m hm
    let Ψ := roundedEstimator F hF w hw T hK hT hwfloor m hm
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
  let H := roundedHolding F hF w hw T hK hT hwfloor m hm
  let R := roundedRules F hF w hw T hK hT hwfloor m hm
  let Ψ := roundedEstimator F hF w hw T hK hT hwfloor m hm
  let M := threshold (Fintype.card ι) T
  let η := learningRate (Fintype.card ι) T m
  refine ⟨dyadicComparisonPolicy H m R M,?_,?_,?_⟩
  · intro loss hloss offset n outcome
    exact dyadicComparisonPolicy_law H m R M (threshold_ge_one hK hT) loss hloss offset n outcome
  · have hbal := (rounded_inputs F hF w hw T hK hT hwfloor m hm).2.2.2.2.2
    exact dyadicTruncatedEstimate_observable H m R Ψ hbal.observable M η
  · intro loss hloss default offset n hn
    have hlaw : (dyadicComparisonPolicy H m R M).law F loss offset n=
        dyadicBlockLaw H m R loss hloss M (threshold_ge_one hK hT) offset n := by
      apply ProbabilityVector.ext_weights
      intro outcome
      exact dyadicComparisonPolicy_law H m R M (threshold_ge_one hK hT) loss hloss offset n outcome
    rw [hlaw]
    exact rounded_block_guarantee F hF w hw T hK hT hwfloor m hm loss hloss default offset n hn

end
end Tournament.Upper

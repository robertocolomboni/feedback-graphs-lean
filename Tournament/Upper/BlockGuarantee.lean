module

public import Tournament.Upper.PreparedBlock
public import Tournament.Upper.BlockPayment
public import Tournament.Upper.EnergyTheorem
public import Tournament.Probability.Truncation
public import Tournament.Foundations.TotalVariation

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open BlockParameters

noncomputable section

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

def blockInternalSwitches {m n : ℕ} (default : ι) (outcome : DyadicBlockOutcome ι m n) : ℝ :=
  (Model.switchCount (n+1) (blockActions default (Restarts.parts n outcome.2.1) outcome.2.2):ℝ)

def blockCost {m n : ℕ} (default : ι) (loss : ℕ → ι → ℝ) (offset : ℕ)
    (outcome : DyadicBlockOutcome ι m n) : ℝ :=
  Model.accumulatedLoss (n+1) (fun t ↦ loss (offset+t))
    (blockActions default (Restarts.parts n outcome.2.1) outcome.2.2)+blockInternalSwitches default outcome+1

omit [Fintype ι] in
theorem blockLoss_bounds (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (h : ℕ) (i : ι) :
    0≤blockLoss loss h i ∧ blockLoss loss h i≤(h:ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun t _ ↦ (hloss t i).1)
  · calc
      _ ≤ ∑ _t ∈ Finset.range h, (1:ℝ) := Finset.sum_le_sum (fun t _ ↦ (hloss t i).2)
      _ = _ := by simp

structure OneBlockGuarantee (μ : ProbabilityVector Ω) (w : ProbabilityVector ι) (L : ι → ℝ)
    (Z : Ω → ι → ℝ) (C S : Ω → ℝ) (T m n : ℕ) : Prop where
  mean : ∀ i, μ.mean (fun ω ↦ Model.truncateEstimate (learningRate (Fintype.card ι) T m) (Z ω) i)=
    w.center L i-μ.truncationBias (learningRate (Fintype.card ι) T m) Z i
  range : ∀ ω, learningRate (Fintype.card ι) T m*
    ‖Model.truncateEstimate (learningRate (Fintype.card ι) T m) (Z ω)‖≤1
  bias : ‖μ.truncationBias (learningRate (Fintype.card ι) T m) Z‖≤
    (2:ℝ)^6*failure (Fintype.card ι) T*((n:ℝ)+1)*logScale (Fintype.card ι) T/DyadicRate.base m
  cost : μ.mean C≤w.mean L+1+6*meanRate m*((n:ℝ)+1)+failure (Fintype.card ι) T*((n:ℝ)+1)^3-
    paymentCoefficient (Fintype.card ι) T m*μ.mean
      (fun ω ↦ w.squareNorm (Model.truncateEstimate (learningRate (Fintype.card ι) T m) (Z ω)))
  switches : μ.mean (fun ω ↦ S ω+1)≤1+2*meanRate m*((n:ℝ)+1)

theorem block_guarantee_from_inputs {F : ι → ι → Prop} (H : HoldingFamily ι) (w : ProbabilityVector ι)
    (T m : ℕ) (hK : 2≤Fintype.card ι) (hT : 2≤T) (hm : 5≤m)
    (R : DyadicScoreRules H F m) (Ψ : ι → ι → ι → ℝ) (L₀ : ℝ) (hL₀ : 1≤L₀)
    (hLΛ : L₀≤(2:ℝ)^8*logScale (Fintype.card ι) T)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (hwp : ∀ i, w i≤2*H.sampling i)
    (hdist : (∑ i, |H.sampling i-w i|)≤8*DyadicRate.base m) (hbal : BalancedEstimator F H w Ψ L₀)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (offset n : ℕ)
    (hn : n+1≤horizon m) :
    OneBlockGuarantee (dyadicBlockLaw H m R loss hloss (threshold (Fintype.card ι) T) (threshold_ge_one hK hT) offset n)
      w (blockLoss (fun t ↦ loss (offset+t)) (n+1))
      (dyadicBlockCorrectedEstimate H m R Ψ loss (threshold (Fintype.card ι) T) offset n)
      (blockCost default loss offset) (blockInternalSwitches default) T m n := by
  let K := Fintype.card ι
  let δ := failure K T
  let M := threshold K T
  let η := learningRate K T m
  let Λ := logScale K T
  let κ := DyadicRate.base m
  let h : ℝ := (n:ℝ)+1
  let μ := dyadicBlockLaw H m R loss hloss M (threshold_ge_one hK hT) offset n
  let Z := dyadicBlockCorrectedEstimate H m R Ψ loss M offset n
  let G := fun ω ↦ Model.truncateEstimate η (Z ω)
  let L := blockLoss (fun t ↦ loss (offset+t)) (n+1)
  let Γ := blockProbingGain H m loss offset (n+1)
  have hκ : 0<κ := DyadicRate.base_pos m
  have hh : 0≤h := by dsimp [h]; positivity
  have hΛ : 1≤Λ := logScale_ge_one hK hT
  have hδ : 0<δ := failure_pos hK hT
  have hδ1 : δ≤1 := failure_le_one hK hT
  have hM : 1≤M := threshold_ge_one hK hT
  have hη : 0<η := learningRate_pos hK hT hm
  have hshort : ((n:ℝ)+1)*DyadicRate.base m≤1/8 := by
    simpa only [Nat.cast_add,Nat.cast_one] using short_block (show 3≤m by omega) hn
  have hraw := estimation_paid_by_steering H m hm hmax R Ψ w hbal.calibration hbal.kills_constants
    hwp L₀ hL₀ hbal.endpoints loss hloss M hM offset n hshort
  have htail := H.estimator_tail_dyadic m hmax R Ψ loss hloss M hM L₀ hL₀ hbal.size
    δ hδ hδ1 (le_refl _) n offset hshort
  have hbias : ‖μ.truncationBias η Z‖≤(h*L₀/(3*κ))*(δ/2) :=
    μ.truncationBias_norm_le η hη.le Z (h*L₀/(3*κ)) (2*M*L₀/κ) (δ/2)
      (by positivity) (by positivity) htail.1 (truncation_threshold_fits hK hT hm L₀ hLΛ) htail.2
  have hbias' : ‖μ.truncationBias η Z‖≤(2:ℝ)^6*δ*h*Λ/κ := by
    calc
      _ ≤ (h*L₀/(3*κ))*(δ/2) := hbias
      _ = (δ*h/κ)*(L₀/6) := by ring
      _ ≤ (δ*h/κ)*(64*Λ) := by
        have hscalar : L₀/6≤64*Λ := by norm_num at hLΛ; dsimp only [Λ,K]; linarith
        exact mul_le_mul_of_nonneg_left hscalar (by positivity)
      _ = _ := by norm_num; ring
  have hV : μ.mean (fun ω ↦ w.squareNorm (G ω))≤
      ((2:ℝ)^14*(m:ℝ)*L₀/κ)*(Γ+meanRate m*h/16) :=
    le_trans (μ.truncation_secondMoment_le w η Z) hraw.2
  have hΓ : 0≤Γ+meanRate m*h/16 := by
    have hg := (gain_energy_bounds H m loss hloss offset (n+1)).2
    simp only [Nat.cast_add,Nat.cast_one] at hg
    change -meanRate m*h/16≤Γ at hg
    linarith
  have hpay := payment_from_moment hK hT hm L₀ hLΛ Γ h
    (μ.mean (fun ω ↦ w.squareNorm (G ω))) hΓ hV
  have hlossBound := dyadic_block_loss_bound H m R loss hloss M hM δ hδ hδ1 (le_refl _) default offset n
  have hswitch := dyadic_block_switchCount_mean_le H m R loss hloss M hM default n offset
  have hswitch' : μ.mean (blockInternalSwitches default)≤(13/8)*meanRate m*h := hswitch
  have hbaseline : H.sampling.mean L≤w.mean L+4*κ*h := by
    have hdiff := H.sampling.mean_sub_le_half_range w L h (by
      intro i
      simpa only [L,h,Nat.cast_add,Nat.cast_one] using
        blockLoss_bounds (fun t ↦ loss (offset+t)) (fun t ↦ hloss (offset+t)) (n+1) i)
    have hd := mul_le_mul_of_nonneg_left hdist (show 0≤h/2 by positivity)
    change H.sampling.mean L-w.mean L≤h/2*(∑ i, |H.sampling i-w i|) at hdiff
    change h/2*(∑ i, |H.sampling i-w i|)≤h/2*(8*κ) at hd
    nlinarith
  have hcost : μ.mean (blockCost default loss offset)≤w.mean L+1+4*κ*h+(13/8)*meanRate m*h-
      ScoreRule.steeringStrength M*Γ+ScoreRule.steeringStrength M*δ*h^3 := by
    unfold blockCost
    rw [ProbabilityVector.mean_add,ProbabilityVector.mean_add,ProbabilityVector.mean_const]
    change μ.mean (fun outcome ↦ Model.accumulatedLoss (n+1) (fun t ↦ loss (offset+t))
      (blockActions default (Restarts.parts n outcome.2.1) outcome.2.2))≤
        H.sampling.mean L-ScoreRule.steeringStrength M*Γ+ScoreRule.steeringStrength M*δ*h^3 at hlossBound
    linarith
  have hβ : ScoreRule.steeringStrength M≤1 := by
    unfold ScoreRule.steeringStrength
    exact (div_le_one (by linarith : (0:ℝ)<4*M)).mpr (by linarith)
  have hμh : 0≤meanRate m*h := mul_nonneg (meanRate_nonneg m) hh
  have hkμ := mul_le_mul_of_nonneg_right (base_le_meanRate m) hh
  have hentry := mul_le_mul_of_nonneg_right hβ (show 0≤meanRate m*h/16 by positivity)
  have hrare := mul_le_mul_of_nonneg_right hβ (show 0≤δ*h^3 by positivity)
  refine ⟨?_,?_,hbias',?_,?_⟩
  · intro i
    rw [ProbabilityVector.truncated_mean,hraw.1 i]
  · intro outcome
    exact Model.truncateEstimate_range η (Z outcome)
  · change μ.mean (blockCost default loss offset)≤w.mean L+1+6*meanRate m*h+δ*h^3-
      paymentCoefficient K T m*μ.mean (fun ω ↦ w.squareNorm (G ω))
    nlinarith
  · rw [ProbabilityVector.mean_add,ProbabilityVector.mean_const]
    change μ.mean (blockInternalSwitches default)+1≤1+2*meanRate m*h
    nlinarith

theorem prepared_block_guarantee (F : ι → ι → Prop) (hF : IsTournament F)
    (w : ProbabilityVector ι) (hw : ∀ i, 0<w i) (T m : ℕ)
    (hK : 2≤Fintype.card ι) (hT : 2≤T) (hm : 5≤m)
    (hwfloor : ∀ i, 1/((Fintype.card ι:ℝ)*(T:ℝ))≤w i)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (offset n : ℕ)
    (hn : n+1≤horizon m) :
    OneBlockGuarantee
      (dyadicBlockLaw (preparedHolding F hF w hw m hm) m (preparedRules F hF w hw m hm) loss hloss
        (threshold (Fintype.card ι) T) (threshold_ge_one hK hT) offset n)
      w (blockLoss (fun t ↦ loss (offset+t)) (n+1))
      (dyadicBlockCorrectedEstimate (preparedHolding F hF w hw m hm) m (preparedRules F hF w hw m hm)
        (preparedEstimator F hF w hw m hm) loss (threshold (Fintype.card ι) T) offset n)
      (blockCost default loss offset) (blockInternalSwitches default) T m n := by
  rcases prepared_inputs F hF w hw m hm with ⟨hmax,hwp,hdist,hL₀,hbal⟩
  exact block_guarantee_from_inputs (preparedHolding F hF w hw m hm) w T m hK hT hm
    (preparedRules F hF w hw m hm) (preparedEstimator F hF w hw m hm) (128*w.anchorLog) hL₀
    (estimatorConstant_le w hw hK hT hwfloor) hmax hwp hdist hbal loss hloss default offset n hn

end
end Tournament.Upper

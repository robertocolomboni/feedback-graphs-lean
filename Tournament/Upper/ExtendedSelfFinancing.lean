module

public import Tournament.Upper.SelfFinancingRegret
public import Tournament.Probability.ExtendedExpectation

@[expose] public section

namespace Tournament.Upper.ExponentialWeights

open scoped BigOperators MeasureTheory Classical
open MeasureTheory Filter

noncomputable section

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

theorem self_financing_regret_extended (μ : Measure Ω) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : 0<η) (ε : ℝ) (hε : 0≤ε) (hεhalf : ε≤1/2)
    (B : ℕ) (length : ℕ → ℕ) (hlen : ∀ b ∈ Finset.range B, 0<length b)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t i, 0≤loss t i ∧ loss t i≤1)
    (X : Ω → ℕ → ι) (g ξ : ℕ → Ω → ι → ℝ) (σ : ℕ → Ω → ℝ)
    (history : ℕ → MeasurableSpace Ω) (hhistory : ∀ b ∈ Finset.range B, history b≤mΩ)
    (hpast : ∀ b ∈ Finset.range B, ∀ t, t<b → ∀ i,
      AEStronglyMeasurable[history b] (fun ω ↦ g t ω i) μ)
    (hg : ∀ b ∈ Finset.range B, ∀ i, AEStronglyMeasurable (fun ω ↦ g b ω i) μ)
    (hbound : ∀ᵐ ω ∂μ, ∀ b ∈ Finset.range B, η*‖g b ω‖≤1)
    (hCmeas : ∀ b ∈ Finset.range B,
      AEStronglyMeasurable (fun ω ↦ Model.scheduledBlockCost length loss (X ω) b) μ)
    (hRmeas : AEStronglyMeasurable (fun ω ↦ Model.pathRegret (Model.prefixHorizon length B) loss (X ω)) μ)
    (hσmeas : ∀ b ∈ Finset.range B, AEStronglyMeasurable (σ b) μ)
    (hcal : ∀ b ∈ Finset.range B, ∀ i, μ[fun ω ↦ g b ω i | history b] =ᵐ[μ]
      fun ω ↦ (smoothedWeights η g ε hε (by linarith) b ω).center (Model.scheduledBlockLoss length loss b) i-ξ b ω i)
    (hcost : ∀ b ∈ Finset.range B,
      μ[fun ω ↦ Model.scheduledBlockCost length loss (X ω) b | history b] ≤ᵐ[μ] fun ω ↦
        (smoothedWeights η g ε hε (by linarith) b ω).mean (Model.scheduledBlockLoss length loss b)+σ b ω-
          2*η*(μ[fun x ↦ (smoothedWeights η g ε hε (by linarith) b x).squareNorm (g b x) | history b]) ω) :
    (((∫ ω, Model.pathRegret (Model.prefixHorizon length B) loss (X ω) ∂μ):ℝ):EReal)≤
      ((Real.log (Fintype.card ι:ℝ)/η:ℝ):EReal)+
      (∑ b ∈ Finset.range B, ExtendedExpectation.mean μ (length b:ℝ) (fun ω ↦ σ b ω+2*‖ξ b ω‖))+
        ((ε*(Model.prefixHorizon length B:ℝ):ℝ):EReal) := by
  let p := weights η g
  let w := smoothedWeights η g ε hε (by linarith)
  have hξInt (b : ℕ) (hb : b∈Finset.range B) : Integrable (ξ b) μ := by
    have hp (j : ι) : AEStronglyMeasurable[history b] (fun ω ↦ p b ω j) μ :=
      trajectory_aestronglyMeasurable μ uniform η g b (hpast b hb) j
    have hp' (j : ι) : AEStronglyMeasurable[mΩ] (fun ω ↦ p b ω j) μ :=
      AEStronglyMeasurable.mono (hhistory b hb) (hp j)
    have hw (j : ι) : AEStronglyMeasurable[mΩ] (fun ω ↦ w b ω j) μ :=
      smooth_aestronglyMeasurable μ (p b) ε hε (by linarith) hp' j
    exact bias_integrable μ (history b) (w b) hw (g b)
      (fun _ ↦ Model.scheduledBlockLoss length loss b) (ξ b) (fun _ ↦ integrable_const _) (hcal b hb)
  have hσlower (b : ℕ) (hb : b∈Finset.range B) : ∀ᵐ ω ∂μ, -(length b:ℝ)≤σ b ω := by
    let C := fun ω ↦ Model.scheduledBlockCost length loss (X ω) b
    let Q := fun ω ↦ (w b ω).squareNorm (g b ω)
    have hC0 : 0≤ᵐ[μ] C := Eventually.of_forall (fun ω ↦
      (Model.scheduledBlockCost_bounds length loss hloss (X ω) b (hlen b hb)).1)
    have hQ0 : 0≤ᵐ[μ] Q := Eventually.of_forall (fun ω ↦ (w b ω).squareNorm_nonneg (g b ω))
    have hCc := condExp_nonneg (m := history b) hC0
    have hQc := condExp_nonneg (m := history b) hQ0
    filter_upwards [hCc,hQc,hcost b hb] with ω hc0 hq0 hc
    change (0:ℝ)≤(μ[C | history b]) ω at hc0
    change (0:ℝ)≤(μ[Q | history b]) ω at hq0
    have hmean : (w b ω).mean (Model.scheduledBlockLoss length loss b)≤(length b:ℝ) := by
      calc
        _ ≤ (w b ω).mean (fun _ ↦ (length b:ℝ)) := (w b ω).mean_mono (fun i ↦
          (Model.scheduledBlockLoss_bounds length loss hloss b i).2)
        _ = _ := ProbabilityVector.mean_const _ _
    have hc' : (μ[C | history b]) ω≤(w b ω).mean (Model.scheduledBlockLoss length loss b)+σ b ω-
        2*η*(μ[Q | history b]) ω := hc
    have hηQ : 0≤2*η*(μ[Q | history b]) ω := mul_nonneg (by positivity) hq0
    linarith
  have hlower (b : ℕ) (hb : b∈Finset.range B) : ∀ᵐ ω ∂μ, 0≤(σ b ω+2*‖ξ b ω‖)+(length b:ℝ) := by
    filter_upwards [hσlower b hb] with ω hω
    linarith [norm_nonneg (ξ b ω)]
  by_cases hall : ∀ b ∈ Finset.range B, Integrable (σ b) μ
  · have hreal := self_financing_regret μ η hη ε hε hεhalf B length hlen loss hloss X g ξ σ
      history hhistory hpast hg hbound hCmeas hRmeas hall hcal hcost
    have hsum : (∑ b ∈ Finset.range B, ExtendedExpectation.mean μ (length b:ℝ) (fun ω ↦ σ b ω+2*‖ξ b ω‖))=
        (((∑ b ∈ Finset.range B, ∫ ω, (σ b ω+2*‖ξ b ω‖) ∂μ):ℝ):EReal) := by
      calc
        _ = ∑ b ∈ Finset.range B, (((∫ ω, (σ b ω+2*‖ξ b ω‖) ∂μ):ℝ):EReal) := Finset.sum_congr rfl (fun b hb ↦
          ExtendedExpectation.mean_of_integrable μ (length b:ℝ) _
            ((hall b hb).add ((hξInt b hb).norm.const_mul 2)) (hlower b hb))
        _ = _ := (ExtendedExpectation.coe_finsetSum _ _).symm
    rw [hsum,← EReal.coe_add,← EReal.coe_add,EReal.coe_le_coe_iff]
    exact hreal
  · push Not at hall
    obtain ⟨b,hb,hnot⟩ := hall
    have hfmeas : AEStronglyMeasurable (fun ω ↦ σ b ω+2*‖ξ b ω‖) μ :=
      (hσmeas b hb).fun_add ((hξInt b hb).norm.aestronglyMeasurable.const_mul 2)
    have hfnot : ¬Integrable (fun ω ↦ σ b ω+2*‖ξ b ω‖) μ := by
      intro hf
      have hsub : Integrable (fun ω ↦ (σ b ω+2*‖ξ b ω‖)-2*‖ξ b ω‖) μ :=
        hf.sub ((hξInt b hb).norm.const_mul 2)
      exact hnot (hsub.congr (Eventually.of_forall (fun _ ↦ by ring)))
    have htop := ExtendedExpectation.mean_eq_top_of_not_integrable μ (length b:ℝ) _ hfmeas (hlower b hb) hfnot
    have hsum : (∑ b ∈ Finset.range B, ExtendedExpectation.mean μ (length b:ℝ) (fun ω ↦ σ b ω+2*‖ξ b ω‖))=⊤ :=
      ExtendedExpectation.finsetSum_eq_top_of_mem _ _
        (fun _ _ ↦ ExtendedExpectation.mean_ne_bot _ _ _) ⟨b,hb,htop⟩
    rw [hsum,EReal.coe_add_top,EReal.top_add_coe]
    exact le_top

end
end Tournament.Upper.ExponentialWeights

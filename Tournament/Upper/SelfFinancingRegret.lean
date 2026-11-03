module

public import Tournament.Upper.SelfFinancing
public import Tournament.Model.BlockAccounting

@[expose] public section

namespace Tournament.Upper.ExponentialWeights

open scoped BigOperators MeasureTheory Classical
open MeasureTheory Filter

noncomputable section

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

theorem self_financing_regret (μ : Measure Ω) [IsProbabilityMeasure μ]
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
    (hσ : ∀ b ∈ Finset.range B, Integrable (σ b) μ)
    (hcal : ∀ b ∈ Finset.range B, ∀ i, μ[fun ω ↦ g b ω i | history b] =ᵐ[μ]
      fun ω ↦ (smoothedWeights η g ε hε (by linarith) b ω).center (Model.scheduledBlockLoss length loss b) i-ξ b ω i)
    (hcost : ∀ b ∈ Finset.range B,
      μ[fun ω ↦ Model.scheduledBlockCost length loss (X ω) b | history b] ≤ᵐ[μ] fun ω ↦
        (smoothedWeights η g ε hε (by linarith) b ω).mean (Model.scheduledBlockLoss length loss b)+σ b ω-
          2*η*(μ[fun x ↦ (smoothedWeights η g ε hε (by linarith) b x).squareNorm (g b x) | history b]) ω) :
    (∫ ω, Model.pathRegret (Model.prefixHorizon length B) loss (X ω) ∂μ)≤
      Real.log (Fintype.card ι:ℝ)/η+(∑ b ∈ Finset.range B, ∫ ω, (σ b ω+2*‖ξ b ω‖) ∂μ)+
        ε*(Model.prefixHorizon length B:ℝ) := by
  let C := fun b ω ↦ Model.scheduledBlockCost length loss (X ω) b
  have hC (b : ℕ) (hb : b∈Finset.range B) : Integrable (C b) μ := by
    apply (integrable_const (2*(length b:ℝ))).mono' (hCmeas b hb)
    filter_upwards with ω
    have hc := Model.scheduledBlockCost_bounds length loss hloss (X ω) b (hlen b hb)
    rw [Real.norm_eq_abs,abs_of_nonneg hc.1]
    exact hc.2
  have hR : Integrable (fun ω ↦ Model.pathRegret (Model.prefixHorizon length B) loss (X ω)) μ := by
    apply (integrable_const (2*(Model.prefixHorizon length B:ℝ))).mono' hRmeas
    exact Eventually.of_forall (fun ω ↦ Model.pathRegret_norm_le _ loss hloss (X ω))
  obtain ⟨i,hi⟩ := Model.exists_bestFixedLoss (Model.prefixHorizon length B) loss
  have hb := self_financing_expected_cost μ η hη ε hε hεhalf B g
    (fun b _ ↦ Model.scheduledBlockLoss length loss b) ξ C σ (fun b ↦ (length b:ℝ))
    history hhistory hpast hg hbound
    (fun _ _ _ ↦ aestronglyMeasurable_const)
    (fun b _ ↦ Eventually.of_forall (fun _ j ↦ Model.scheduledBlockLoss_bounds length loss hloss b j))
    hC hσ hcal hcost i
  have hdet : (∑ b ∈ Finset.range B, ∫ _ω : Ω, Model.scheduledBlockLoss length loss b i ∂μ)=
      Model.fixedLoss (Model.prefixHorizon length B) loss i := by
    have hconst (b : ℕ) : (∫ _ω : Ω, Model.scheduledBlockLoss length loss b i ∂μ)=
        Model.scheduledBlockLoss length loss b i := by simp
    simp_rw [hconst]
    exact Model.scheduledBlockLoss_sum length loss B i
  have hlength : (∑ b ∈ Finset.range B, (length b:ℝ))=(Model.prefixHorizon length B:ℝ) := by
    simp [Model.prefixHorizon]
  rw [hdet,hlength] at hb
  have hsum : Integrable (fun ω ↦ ∑ b ∈ Finset.range B, C b ω) μ := integrable_finsetSum (Finset.range B) hC
  have hright : Integrable (fun ω ↦ (∑ b ∈ Finset.range B, C b ω)-Model.fixedLoss (Model.prefixHorizon length B) loss i) μ :=
    hsum.sub (integrable_const _)
  have hpoint : ∀ᵐ ω ∂μ, Model.pathRegret (Model.prefixHorizon length B) loss (X ω)≤
      (∑ b ∈ Finset.range B, C b ω)-Model.fixedLoss (Model.prefixHorizon length B) loss i := by
    filter_upwards with ω
    have hc := Model.scheduledCost_covers length loss B (X ω)
    unfold Model.pathRegret
    rw [hi]
    exact sub_le_sub_right hc _
  have hcompare := integral_mono_ae hR hright hpoint
  rw [integral_sub hsum (integrable_const _)] at hcompare
  have hconst : (∫ _ω : Ω, Model.fixedLoss (Model.prefixHorizon length B) loss i ∂μ)=
      Model.fixedLoss (Model.prefixHorizon length B) loss i := by simp
  rw [hconst] at hcompare
  exact le_trans hcompare hb

end
end Tournament.Upper.ExponentialWeights

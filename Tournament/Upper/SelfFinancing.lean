module

public import Tournament.Upper.ConditionalSelfFinancing

@[expose] public section

namespace Tournament.Upper.ExponentialWeights

open scoped BigOperators MeasureTheory
open MeasureTheory Filter

noncomputable section

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

theorem self_financing_expected_cost (μ : Measure Ω) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : 0<η) (ε : ℝ) (hε : 0≤ε) (hεhalf : ε≤1/2)
    (B : ℕ) (g L ξ : ℕ → Ω → ι → ℝ) (C σ : ℕ → Ω → ℝ) (h : ℕ → ℝ)
    (history : ℕ → MeasurableSpace Ω) (hhistory : ∀ b ∈ Finset.range B, history b≤mΩ)
    (hpast : ∀ b ∈ Finset.range B, ∀ t, t<b → ∀ i,
      AEStronglyMeasurable[history b] (fun ω ↦ g t ω i) μ)
    (hg : ∀ b ∈ Finset.range B, ∀ i, AEStronglyMeasurable (fun ω ↦ g b ω i) μ)
    (hbound : ∀ᵐ ω ∂μ, ∀ b ∈ Finset.range B, η*‖g b ω‖≤1)
    (hLmeas : ∀ b ∈ Finset.range B, ∀ i, AEStronglyMeasurable (fun ω ↦ L b ω i) μ)
    (hLbound : ∀ b ∈ Finset.range B, ∀ᵐ ω ∂μ, ∀ i, 0≤L b ω i ∧ L b ω i≤h b)
    (hC : ∀ b ∈ Finset.range B, Integrable (C b) μ)
    (hσ : ∀ b ∈ Finset.range B, Integrable (σ b) μ)
    (hcal : ∀ b ∈ Finset.range B, ∀ i, μ[fun ω ↦ g b ω i | history b] =ᵐ[μ]
      fun ω ↦ (smoothedWeights η g ε hε (by linarith) b ω).center (L b ω) i-ξ b ω i)
    (hcost : ∀ b ∈ Finset.range B, μ[C b | history b] ≤ᵐ[μ] fun ω ↦
      (smoothedWeights η g ε hε (by linarith) b ω).mean (L b ω)+σ b ω-
        2*η*(μ[fun x ↦ (smoothedWeights η g ε hε (by linarith) b x).squareNorm (g b x) | history b]) ω)
    (i : ι) :
    (∫ ω, ∑ b ∈ Finset.range B, C b ω ∂μ)-(∑ b ∈ Finset.range B, ∫ ω, L b ω i ∂μ)≤
      Real.log (Fintype.card ι:ℝ)/η+(∑ b ∈ Finset.range B, ∫ ω, (σ b ω+2*‖ξ b ω‖) ∂μ)+
        ε*(∑ b ∈ Finset.range B, h b) := by
  let p := weights η g
  let w := smoothedWeights η g ε hε (by linarith)
  have hp (b : ℕ) (hb : b∈Finset.range B) (j : ι) :
      AEStronglyMeasurable[history b] (fun ω ↦ p b ω j) μ :=
    trajectory_aestronglyMeasurable μ uniform η g b (hpast b hb) j
  have hp' (b : ℕ) (hb : b∈Finset.range B) (j : ι) :
      AEStronglyMeasurable[mΩ] (fun ω ↦ p b ω j) μ := AEStronglyMeasurable.mono (hhistory b hb) (hp b hb j)
  have hw (b : ℕ) (hb : b∈Finset.range B) (j : ι) :
      AEStronglyMeasurable[mΩ] (fun ω ↦ w b ω j) μ :=
    smooth_aestronglyMeasurable μ (p b) ε hε (by linarith) (hp' b hb) j
  have hbnd (b : ℕ) (hb : b∈Finset.range B) : ∀ᵐ ω ∂μ, η*‖g b ω‖≤1 :=
    hbound.mono (fun _ hω ↦ hω b hb)
  have hgInt (b : ℕ) (hb : b∈Finset.range B) (j : ι) : Integrable (fun ω ↦ g b ω j) μ :=
    estimate_integrable μ η hη (g b) (hg b hb) (hbnd b hb) j
  have hLInt (b : ℕ) (hb : b∈Finset.range B) (j : ι) : Integrable (fun ω ↦ L b ω j) μ := by
    apply (integrable_const (h b)).mono' (hLmeas b hb j)
    filter_upwards [hLbound b hb] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (hω j).1]
    exact (hω j).2
  have hmeanInt (b : ℕ) (hb : b∈Finset.range B) : Integrable (fun ω ↦ (w b ω).mean (L b ω)) μ :=
    MeasureRandomWeights.integrable_mean μ (w b) (hw b hb) (L b) (hLInt b hb)
  have hQInt (b : ℕ) (hb : b∈Finset.range B) : Integrable (fun ω ↦ (w b ω).squareNorm (g b ω)) μ :=
    estimate_secondMoment_integrable μ (w b) (hw b hb) η hη (g b) (hg b hb) (hbnd b hb)
  have hξInt (b : ℕ) (hb : b∈Finset.range B) : Integrable (ξ b) μ :=
    bias_integrable μ (history b) (w b) (hw b hb) (g b) (L b) (ξ b) (hLInt b hb) (hcal b hb)
  have hbudget (b : ℕ) (hb : b∈Finset.range B) :
      (∫ ω, C b ω ∂μ)-(∫ ω, L b ω i ∂μ)≤
        (∫ ω, ((p b ω).mean (g b ω)-g b ω i) ∂μ)+
        ((∫ ω, σ b ω ∂μ)+2*(∫ ω, ‖ξ b ω‖ ∂μ))+ε*h b-
          2*η*(∫ ω, (w b ω).squareNorm (g b ω) ∂μ) := by
    have hcomp : (∫ ω, (w b ω).mean (L b ω) ∂μ)-(∫ ω, L b ω i ∂μ)≤
        (∫ ω, ((p b ω).mean (g b ω)-g b ω i) ∂μ)+ε*h b+2*(∫ ω, ‖ξ b ω‖ ∂μ) :=
      comparison_integral_lower μ (hhistory b hb) (p b) (hp b hb) ε hε (by linarith)
        (g b) (L b) (ξ b) (h b) (hgInt b hb) (hLInt b hb) (hLbound b hb) (hcal b hb) i
    have hc := integrated_block_condition μ (hhistory b hb)
      (fun ω ↦ (w b ω).mean (L b ω)) (σ b) (fun ω ↦ (w b ω).squareNorm (g b ω)) (C b) η
        (hmeanInt b hb) (hσ b hb) (hQInt b hb) (hC b hb) (hcost b hb)
    linarith
  have hsum : (∑ b ∈ Finset.range B, ((∫ ω, C b ω ∂μ)-(∫ ω, L b ω i ∂μ)))≤
      (∑ b ∈ Finset.range B, ∫ ω, ((p b ω).mean (g b ω)-g b ω i) ∂μ)+
      (∑ b ∈ Finset.range B, ((∫ ω, σ b ω ∂μ)+2*(∫ ω, ‖ξ b ω‖ ∂μ)))+
        ε*(∑ b ∈ Finset.range B, h b)-2*η*(∑ b ∈ Finset.range B, ∫ ω, (w b ω).squareNorm (g b ω) ∂μ) := by
    calc
      _ ≤ ∑ b ∈ Finset.range B, ((∫ ω, ((p b ω).mean (g b ω)-g b ω i) ∂μ)+
          ((∫ ω, σ b ω ∂μ)+2*(∫ ω, ‖ξ b ω‖ ∂μ))+ε*h b-
            2*η*(∫ ω, (w b ω).squareNorm (g b ω) ∂μ)) := Finset.sum_le_sum hbudget
      _ = _ := by simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  have hew := expected_second_order μ η hη g B ε hε hεhalf hg hbound i
  change (∑ b ∈ Finset.range B, ∫ ω, ((p b ω).mean (g b ω)-g b ω i) ∂μ)≤
    Real.log (Fintype.card ι:ℝ)/η+2*η*(∑ b ∈ Finset.range B, ∫ ω, (w b ω).squareNorm (g b ω) ∂μ) at hew
  have hcharge : (∑ b ∈ Finset.range B, ∫ ω, (σ b ω+2*‖ξ b ω‖) ∂μ)=
      ∑ b ∈ Finset.range B, ((∫ ω, σ b ω ∂μ)+2*(∫ ω, ‖ξ b ω‖ ∂μ)) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [integral_add (hσ b hb) ((hξInt b hb).norm.const_mul 2),integral_const_mul]
  rw [integral_finsetSum (Finset.range B) hC,hcharge]
  rw [Finset.sum_sub_distrib] at hsum
  linarith

end
end Tournament.Upper.ExponentialWeights

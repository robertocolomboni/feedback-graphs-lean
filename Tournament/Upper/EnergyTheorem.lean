module

public import Tournament.Upper.ReferenceBound

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι] {F : ι → ι → Prop}

theorem dyadicBlock_secondMoment_energy_bound (H : HoldingFamily ι) (m : ℕ) (hm : 5≤m)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι)
    (hcal : EstimatorCalibration Ψ H.sampling w) (hkill : EstimatorKillsConstants Ψ)
    (hwp : ∀ i, w i≤2*H.sampling i) (L₀ : ℝ) (hL₀ : 1≤L₀)
    (hend : EstimatorEndpointBounds H w Ψ L₀) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1≤M) (offset n : ℕ)
    (hnκ : ((n:ℝ)+1)*DyadicRate.base m≤1/8) :
    (dyadicBlockLaw H m R loss hloss M hM offset n).mean (fun outcome ↦
      w.squareNorm (dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome))≤
        ((2:ℝ)^13*(m:ℝ)*L₀/DyadicRate.base m)*probingEnergy H m loss offset (n+1) := by
  have hred := dyadicBlock_secondMoment_reference_reduction H m R Ψ loss hloss M hM w hcal hwp offset n hnκ
  have href := reference_errors_paid_by_energy H w m hmax Ψ hcal hkill L₀ (by linarith) hend loss offset n
  have hκ := DyadicRate.base_pos m
  have hQ := probingEnergy_nonneg H m loss offset (n+1)
  have hm1 : (1:ℝ)≤(m:ℝ) := by exact_mod_cast (show 1≤m by omega)
  have hprod : (1:ℝ)≤(m:ℝ)*L₀ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (sub_nonneg.mpr hL₀)]
  have hcoeff : (86/3:ℝ)+4096*(m:ℝ)*L₀≤8192*(m:ℝ)*L₀ := by nlinarith
  calc
    _ ≤ (86/3)*probingEnergy H m loss offset (n+1)/DyadicRate.base m+
        (4/3)*referenceErrorEnergy H w m Ψ loss offset n := hred
    _ ≤ (86/3)*probingEnergy H m loss offset (n+1)/DyadicRate.base m+
        (4/3)*((3072*(m:ℝ)*L₀/DyadicRate.base m)*probingEnergy H m loss offset (n+1)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left href (by norm_num))
    _ = ((86/3:ℝ)+4096*(m:ℝ)*L₀)*(probingEnergy H m loss offset (n+1)/DyadicRate.base m) := by ring
    _ ≤ (8192*(m:ℝ)*L₀)*(probingEnergy H m loss offset (n+1)/DyadicRate.base m) :=
      mul_le_mul_of_nonneg_right hcoeff (div_nonneg hQ (le_of_lt hκ))
    _ = _ := by norm_num; ring

theorem dyadicBlock_secondMoment_steering_bound (H : HoldingFamily ι) (m : ℕ) (hm : 5≤m)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι)
    (hcal : EstimatorCalibration Ψ H.sampling w) (hkill : EstimatorKillsConstants Ψ)
    (hwp : ∀ i, w i≤2*H.sampling i) (L₀ : ℝ) (hL₀ : 1≤L₀)
    (hend : EstimatorEndpointBounds H w Ψ L₀) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1≤M) (offset n : ℕ)
    (hnκ : ((n:ℝ)+1)*DyadicRate.base m≤1/8) :
    (dyadicBlockLaw H m R loss hloss M hM offset n).mean (fun outcome ↦
      w.squareNorm (dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome))≤
        ((2:ℝ)^14*(m:ℝ)*L₀/DyadicRate.base m)*(blockProbingGain H m loss offset (n+1)+
          (DyadicRate.base m*(1+(m:ℝ)/2))*((n:ℝ)+1)/16) := by
  have he := dyadicBlock_secondMoment_energy_bound H m hm hmax R Ψ w hcal hkill hwp L₀ hL₀ hend loss hloss M hM offset n hnκ
  have hg := (gain_energy_bounds H m loss hloss offset (n+1)).1
  simp only [Nat.cast_add,Nat.cast_one] at hg
  have hκ := DyadicRate.base_pos m
  have hL₀0 : 0≤L₀ := by linarith
  calc
    _ ≤ _ := he
    _ ≤ ((2:ℝ)^13*(m:ℝ)*L₀/DyadicRate.base m)*(2*(blockProbingGain H m loss offset (n+1)+
        (DyadicRate.base m*(1+(m:ℝ)/2))*((n:ℝ)+1)/16)) := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by norm_num; ring

theorem estimation_paid_by_steering (H : HoldingFamily ι) (m : ℕ) (hm : 5≤m)
    (hmax : DyadicRate.base m*H.maxRatio≤1/4) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι)
    (hcal : EstimatorCalibration Ψ H.sampling w) (hkill : EstimatorKillsConstants Ψ)
    (hwp : ∀ i, w i≤2*H.sampling i) (L₀ : ℝ) (hL₀ : 1≤L₀)
    (hend : EstimatorEndpointBounds H w Ψ L₀) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1≤M) (offset n : ℕ)
    (hnκ : ((n:ℝ)+1)*DyadicRate.base m≤1/8) :
    (∀ i, (dyadicBlockLaw H m R loss hloss M hM offset n).mean
      (fun outcome ↦ dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome i)=
        w.center (blockLoss (fun t ↦ loss (offset+t)) (n+1)) i) ∧
    (dyadicBlockLaw H m R loss hloss M hM offset n).mean (fun outcome ↦
      w.squareNorm (dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome))≤
        ((2:ℝ)^14*(m:ℝ)*L₀/DyadicRate.base m)*(blockProbingGain H m loss offset (n+1)+
          (DyadicRate.base m*(1+(m:ℝ)/2))*((n:ℝ)+1)/16) := by
  exact ⟨fun i ↦ dyadicBlockEstimate_mean H m R Ψ loss hloss M hM w hcal offset n i,
    dyadicBlock_secondMoment_steering_bound H m hm hmax R Ψ w hcal hkill hwp L₀ hL₀ hend loss hloss M hM offset n hnκ⟩

end
end Tournament.Upper

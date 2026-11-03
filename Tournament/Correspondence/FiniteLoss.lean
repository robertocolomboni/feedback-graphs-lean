module

public import Tournament.Upper.EnergyTheorem

@[expose] public section

namespace Tournament.Correspondence

open scoped BigOperators Classical
open Upper

noncomputable section

variable {ι : Type*}

def finiteLossExtension {h : ℕ} (loss : Fin h → ι → ℝ) (t : ℕ) : ι → ℝ :=
  if ht : t < h then loss ⟨t, ht⟩ else fun _ ↦ 0

theorem finiteLossExtension_agrees {h : ℕ} (loss : Fin h → ι → ℝ) (t : Fin h) :
    finiteLossExtension loss t.val = loss t := by
  simp only [finiteLossExtension, dite_eq_left t.isLt]

theorem finiteLossExtension_bounded {h : ℕ} (loss : Fin h → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) :
    ∀ t, BoundedLoss (finiteLossExtension loss t) := by
  intro t i
  by_cases ht : t < h
  · simpa only [finiteLossExtension, dite_eq_left ht] using hloss ⟨t, ht⟩ i
  · simp only [finiteLossExtension, dite_eq_right ht]
    norm_num

theorem finiteLossExtension_total [Fintype ι] {h : ℕ} (loss : Fin h → ι → ℝ) :
    blockLoss (finiteLossExtension loss) h = fun i ↦ ∑ t : Fin h, loss t i := by
  funext i
  unfold blockLoss
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun t _ ↦ congrFun (finiteLossExtension_agrees loss t) i)

theorem finite_loss_specialization {h : ℕ} (P : (ℕ → ι → ℝ) → Prop)
    (hP : ∀ loss, (∀ t, BoundedLoss (loss t)) → P loss)
    (loss : Fin h → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) :
    P (finiteLossExtension loss) :=
  hP (finiteLossExtension loss) (finiteLossExtension_bounded loss hloss)

def dyadicScoreRulesOfInterval [Fintype ι] (H : HoldingFamily ι)
    (F : ι → ι → Prop) (m : ℕ)
    (rules : ∀ (τ : ℝ) (hτ : 0 < τ), DyadicRate.base m ≤ τ → τ ≤ 1 →
      ScoreRule F (H.kernel τ hτ) H.sampling) : DyadicScoreRules H F m :=
  fun j ↦ rules (DyadicRate.rate m j) (DyadicRate.rate_pos m j)
    (DyadicRate.base_le_rate m j) (DyadicRate.rate_le_one m j)

theorem estimation_paid_by_steering_finite [Fintype ι] {F : ι → ι → Prop}
    (H : HoldingFamily ι) (m : ℕ) (hm : 5 ≤ m)
    (hmax : DyadicRate.base m * H.maxRatio ≤ 1/4) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (w : ProbabilityVector ι)
    (hcal : EstimatorCalibration Ψ H.sampling w) (hkill : EstimatorKillsConstants Ψ)
    (hwp : ∀ i, w i ≤ 2 * H.sampling i) (L₀ : ℝ) (hL₀ : 1 ≤ L₀)
    (hend : EstimatorEndpointBounds H w Ψ L₀) (n : ℕ)
    (loss : Fin (n+1) → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M : ℝ) (hM : 1 ≤ M) (hnκ : ((n:ℝ)+1)*DyadicRate.base m ≤ 1/8) :
    (∀ i, (dyadicBlockLaw H m R (finiteLossExtension loss)
      (finiteLossExtension_bounded loss hloss) M hM 0 n).mean
      (fun outcome ↦ dyadicBlockCorrectedEstimate H m R Ψ (finiteLossExtension loss) M 0 n outcome i) =
        w.center (fun i ↦ ∑ t : Fin (n+1), loss t i) i) ∧
    (dyadicBlockLaw H m R (finiteLossExtension loss)
      (finiteLossExtension_bounded loss hloss) M hM 0 n).mean
      (fun outcome ↦ w.squareNorm
        (dyadicBlockCorrectedEstimate H m R Ψ (finiteLossExtension loss) M 0 n outcome)) ≤
      ((2:ℝ)^14*(m:ℝ)*L₀/DyadicRate.base m) *
        (blockProbingGain H m (finiteLossExtension loss) 0 (n+1) +
          (DyadicRate.base m*(1+(m:ℝ)/2))*((n:ℝ)+1)/16) := by
  have h := Upper.estimation_paid_by_steering H m hm hmax R Ψ w hcal hkill hwp L₀ hL₀
    hend (finiteLossExtension loss) (finiteLossExtension_bounded loss hloss) M hM 0 n hnκ
  simpa only [Nat.zero_add, finiteLossExtension_total] using h

end
end Tournament.Correspondence

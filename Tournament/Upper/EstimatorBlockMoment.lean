module

public import Tournament.Upper.BlockLaw

@[expose] public section

namespace Tournament.HoldingFamily

open scoped BigOperators Classical
open Upper FinitePath

variable {ι : Type*} [Fintype ι]

noncomputable section

theorem block_ratio_exponential_mean_le (H : HoldingFamily ι)
    {κ τ : ℝ} (hκ : 0 < κ) (hκmax : κ*H.maxRatio ≤ 1/4) (hκτ : κ ≤ τ)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (h : ℕ) (hhκ : (h:ℝ)*κ ≤ 1/8) :
    ∀ ns, Restarts.totalRounds ns ≤ h → ∀ offset,
    (blockLaw R loss hloss M hM offset ns).mean (fun outcome ↦
      Real.exp ((κ/12)*blockRatioTotal H.ratio ns outcome)) ≤
        Real.exp ((5/2)*(κ/12)*(Restarts.totalRounds ns:ℝ)) := by
  intro ns
  induction ns with
  | nil =>
    intro _ offset
    have heq : (fun outcome : BlockOutcome ι [] ↦ Real.exp ((κ/12)*blockRatioTotal H.ratio [] outcome)) =
        (fun _ ↦ (1:ℝ)) := by
      funext outcome
      simp [blockRatioTotal]
    rw [heq, ProbabilityVector.mean_const]
    simp [Restarts.totalRounds]
  | cons n ns ih =>
    intro hns offset
    let headLaw := (R.shift offset).tiltedLaw (fun t ↦ loss (offset+t))
      (fun t ↦ hloss (offset+t)) M hM n
    let tailLaw := blockLaw R loss hloss M hM (offset+(n+1)) ns
    change (headLaw.joint (fun _ ↦ tailLaw)).mean
      (fun outcome : History ι n × BlockOutcome ι ns ↦ Real.exp
        ((κ/12)*(stateTotal H.ratio n outcome.1+blockRatioTotal H.ratio ns outcome.2))) ≤ _
    rw [ProbabilityVector.independent_exp_add headLaw tailLaw (stateTotal H.ratio n)
      (blockRatioTotal H.ratio ns) (κ/12)]
    have hhead := H.tilted_ratio_exponential_mean_le hκ hκmax hκτ (R.shift offset)
      (fun t ↦ loss (offset+t)) (fun t ↦ hloss (offset+t)) M hM h hhκ n
      (Nat.le_trans (Restarts.head_rounds_le n ns) hns)
    have htail := ih (Nat.le_trans (Restarts.tail_rounds_le n ns) hns) (offset+(n+1))
    calc
      _ ≤ Real.exp ((5/2)*(κ/12)*((n:ℝ)+1)) *
          Real.exp ((5/2)*(κ/12)*(Restarts.totalRounds ns:ℝ)) :=
        mul_le_mul hhead htail (tailLaw.mean_nonneg (fun _ ↦ Real.exp_nonneg _)) (Real.exp_nonneg _)
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        simp only [Restarts.totalRounds, Nat.cast_add, Nat.cast_one]
        ring

theorem partitioned_block_ratio_exponential_mean_le (H : HoldingFamily ι)
    {κ τ : ℝ} (hκ : 0 < κ) (hκmax : κ*H.maxRatio ≤ 1/4) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (h : ℕ) (hhκ : (h:ℝ)*κ ≤ 1/8) (n : ℕ) (hn : n+1 ≤ h) (offset : ℕ) :
    (partitionedBlockLaw R loss hloss M hM τ
      (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 offset n).mean
      (fun outcome ↦ Real.exp ((κ/12)*blockRatioTotal H.ratio (Restarts.parts n outcome.1) outcome.2)) ≤
        Real.exp ((5/2)*(κ/12)*((n:ℝ)+1)) := by
  unfold partitionedBlockLaw
  rw [ProbabilityVector.sigmaJoint_mean]
  calc
    _ ≤ (Restarts.law τ (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 n).mean
        (fun _ ↦ Real.exp ((5/2)*(κ/12)*((n:ℝ)+1))) := by
      apply ProbabilityVector.mean_mono
      intro coins
      have hb := H.block_ratio_exponential_mean_le hκ hκmax hκτ R loss hloss M hM h hhκ
        (Restarts.parts n coins) (by rw [Restarts.parts_totalRounds]; exact hn) offset
      simpa only [Restarts.parts_totalRounds, Nat.cast_add, Nat.cast_one] using hb
    _ = _ := ProbabilityVector.mean_const _ _

theorem played_block_ratio_exponential_mean_le (H : HoldingFamily ι)
    {κ τ : ℝ} (hκ : 0 < κ) (hκmax : κ*H.maxRatio ≤ 1/4) (hκτ : κ ≤ τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ (lt_of_lt_of_le hκ hκτ)) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (n offset : ℕ) (hnκ : ((n:ℝ)+1)*κ ≤ 1/8) :
    (partitionedBlockLaw R loss hloss M hM τ
      (le_of_lt (lt_of_lt_of_le hκ hκτ)) hτ1 offset n).mean
      (fun outcome ↦ Real.exp ((κ/12)*blockRatioTotal H.ratio (Restarts.parts n outcome.1) outcome.2)) ≤
        Real.exp (1/32) := by
  have h := H.partitioned_block_ratio_exponential_mean_le hκ hκmax hκτ hτ1 R loss hloss M hM
    (n+1) (by simpa only [Nat.cast_add, Nat.cast_one] using hnκ) n le_rfl offset
  apply le_trans h
  apply Real.exp_le_exp.mpr
  nlinarith

end
end Tournament.HoldingFamily

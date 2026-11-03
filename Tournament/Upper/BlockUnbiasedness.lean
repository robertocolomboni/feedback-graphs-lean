module

public import Tournament.Upper.EstimatorDyadicTail

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace ProbabilityVector

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

theorem independent_second_mean (μ : ProbabilityVector Ω) (ν : ProbabilityVector S) (g : S → ℝ) :
    (μ.joint (fun _ ↦ ν)).mean (fun xy ↦ g xy.2) = ν.mean g := by
  rw [joint_mean]
  change μ.mean (fun _ ↦ ν.mean g) = ν.mean g
  exact μ.mean_const _

variable {ι : Type*} [Fintype ι]

theorem center_add (w : ProbabilityVector ι) (f g : ι → ℝ) (k : ι) :
    w.center (fun i ↦ f i+g i) k = w.center f k+w.center g k := by
  unfold center
  rw [mean_add]
  ring

end ProbabilityVector

namespace Upper

open FinitePath

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

omit [Fintype ι] in
theorem blockLoss_append (loss : ℕ → ι → ℝ) (offset a b : ℕ) (i : ι) :
    blockLoss (fun t ↦ loss (offset+t)) (a+b) i =
      blockLoss (fun t ↦ loss (offset+t)) a i + blockLoss (fun t ↦ loss ((offset+a)+t)) b i := by
  unfold blockLoss
  rw [Finset.sum_range_add]
  simp only [Nat.add_assoc]

theorem blockCorrectedEstimate_mean (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ p w) :
    ∀ ns offset k, (blockLaw R loss hloss M hM offset ns).mean
      (fun outcome ↦ blockCorrectedEstimate R Ψ loss M offset ns outcome k) =
        w.center (blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds ns)) k := by
  intro ns
  induction ns with
  | nil =>
    intro offset k
    have hzero : blockLoss (fun t ↦ loss (offset+t)) 0 = (fun _ ↦ (0:ℝ)) := by
      funext i
      simp [blockLoss]
    change (ProbabilityVector.pure (ULift.up ())).mean (fun _ ↦ (0:ℝ)) =
      w.center (blockLoss (fun t ↦ loss (offset+t)) 0) k
    rw [ProbabilityVector.mean_const, hzero]
    simp [ProbabilityVector.center]
  | cons n ns ih =>
    intro offset k
    let headLaw := (R.shift offset).tiltedLaw (fun t ↦ loss (offset+t))
      (fun t ↦ hloss (offset+t)) M hM n
    let tailLaw := blockLaw R loss hloss M hM (offset+(n+1)) ns
    change (headLaw.joint (fun _ ↦ tailLaw)).mean
      (fun outcome : History ι n × BlockOutcome ι ns ↦
        referenceEstimate Ψ (fun t ↦ loss (offset+t)) n outcome.1 k /
          (R.shift offset).likelihood (fun t ↦ loss (offset+t)) M n outcome.1 +
        blockCorrectedEstimate R Ψ loss M (offset+(n+1)) ns outcome.2 k) = _
    rw [ProbabilityVector.mean_add, ProbabilityVector.joint_first_mean headLaw (fun _ ↦ tailLaw)
      (fun hist ↦ referenceEstimate Ψ (fun t ↦ loss (offset+t)) n hist k /
        (R.shift offset).likelihood (fun t ↦ loss (offset+t)) M n hist),
      ProbabilityVector.independent_second_mean headLaw tailLaw
        (fun outcome ↦ blockCorrectedEstimate R Ψ loss M (offset+(n+1)) ns outcome k)]
    have hhead := ((R.shift offset).chunk_estimate_moments (fun t ↦ loss (offset+t))
      (fun t ↦ hloss (offset+t)) M hM w Ψ hcal n).1 k
    rw [hhead, ih (offset+(n+1)) k]
    have hsplit : blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds (n::ns)) =
        (fun i ↦ blockLoss (fun t ↦ loss (offset+t)) (n+1) i +
          blockLoss (fun t ↦ loss ((offset+(n+1))+t)) (Restarts.totalRounds ns) i) := by
      funext i
      exact blockLoss_append loss offset (n+1) (Restarts.totalRounds ns) i
    rw [hsplit, ProbabilityVector.center_add]

theorem partitionedBlockEstimate_mean (R : ScoreRule F P p) (Ψ : ι → ι → ι → ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ p w)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (offset n : ℕ) (k : ι) :
    (partitionedBlockLaw R loss hloss M hM τ hτ hτ1 offset n).mean
      (fun outcome ↦ blockCorrectedEstimate R Ψ loss M offset (Restarts.parts n outcome.1) outcome.2 k) =
        w.center (blockLoss (fun t ↦ loss (offset+t)) (n+1)) k := by
  unfold partitionedBlockLaw
  rw [ProbabilityVector.sigmaJoint_mean]
  have heq : (fun coins ↦ (blockLaw R loss hloss M hM offset (Restarts.parts n coins)).mean
      (fun outcome ↦ blockCorrectedEstimate R Ψ loss M offset (Restarts.parts n coins) outcome k)) =
      (fun _ ↦ w.center (blockLoss (fun t ↦ loss (offset+t)) (n+1)) k) := by
    funext coins
    rw [blockCorrectedEstimate_mean R Ψ loss hloss M hM w hcal, Restarts.parts_totalRounds]
  rw [heq, ProbabilityVector.mean_const]

theorem dyadicBlockEstimate_mean (H : HoldingFamily ι) (m : ℕ) (R : DyadicScoreRules H F m)
    (Ψ : ι → ι → ι → ℝ) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M : ℝ) (hM : 1 ≤ M) (w : ProbabilityVector ι) (hcal : EstimatorCalibration Ψ H.sampling w)
    (offset n : ℕ) (k : ι) :
    (dyadicBlockLaw H m R loss hloss M hM offset n).mean
      (fun outcome ↦ dyadicBlockCorrectedEstimate H m R Ψ loss M offset n outcome k) =
        w.center (blockLoss (fun t ↦ loss (offset+t)) (n+1)) k := by
  change ((DyadicRate.law m).sigmaJoint (fun j ↦ partitionedBlockLaw (R j) loss hloss M hM
    (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) offset n)).mean
    (fun outcome : (_j : Fin (m+1)) × (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins) ↦
      blockCorrectedEstimate (R outcome.1) Ψ loss M offset (Restarts.parts n outcome.2.1) outcome.2.2 k) = _
  rw [ProbabilityVector.sigmaJoint_mean]
  have heq : (fun j ↦ (partitionedBlockLaw (R j) loss hloss M hM (DyadicRate.rate m j)
      (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) offset n).mean
        (fun outcome ↦ blockCorrectedEstimate (R j) Ψ loss M offset (Restarts.parts n outcome.1) outcome.2 k)) =
      (fun _ ↦ w.center (blockLoss (fun t ↦ loss (offset+t)) (n+1)) k) := by
    funext j
    exact partitionedBlockEstimate_mean (R j) Ψ loss hloss M hM w hcal _ _ _ offset n k
  rw [heq, ProbabilityVector.mean_const]

end Upper
end
end Tournament

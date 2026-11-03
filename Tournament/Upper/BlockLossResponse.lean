module

public import Tournament.Upper.BlockStoppingError
public import Tournament.Upper.BlockSwitches

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace Model

variable {ι : Type*}

theorem accumulatedLoss_append (h k : ℕ) (loss : ℕ → ι → ℝ) (X Y : ℕ → ι) :
    accumulatedLoss (h+k) loss (appendActions h X Y) =
      accumulatedLoss h loss X + accumulatedLoss k (fun t ↦ loss (h+t)) Y := by
  unfold accumulatedLoss
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [appendActions,ite_eq_left (Finset.mem_range.mp ht)]
  · apply Finset.sum_congr rfl
    intro t _
    rw [appendActions,ite_eq_right (by omega : ¬ h+t<h),Nat.add_sub_cancel_left]

end Model

namespace Upper

open FinitePath

variable {ι : Type*}

def blockPlayedLoss (loss : ℕ → ι → ℝ) : (offset : ℕ) → (ns : List ℕ) → BlockOutcome ι ns → ℝ
  | _, [], _ => 0
  | offset, n::ns, outcome => pathLoss (fun t ↦ loss (offset+t)) n outcome.1 +
      blockPlayedLoss loss (offset+(n+1)) ns outcome.2

theorem blockPlayedLoss_eq_accumulatedLoss (loss : ℕ → ι → ℝ) (default : ι) :
    ∀ ns offset (outcome : BlockOutcome ι ns), blockPlayedLoss loss offset ns outcome =
      Model.accumulatedLoss (Restarts.totalRounds ns) (fun t ↦ loss (offset+t)) (blockActions default ns outcome) := by
  intro ns
  induction ns with
  | nil => intro offset outcome; simp [blockPlayedLoss,Restarts.totalRounds,Model.accumulatedLoss]
  | cons n ns ih =>
    intro offset outcome
    change pathLoss (fun t ↦ loss (offset+t)) n outcome.1 + blockPlayedLoss loss (offset+(n+1)) ns outcome.2 =
      Model.accumulatedLoss ((n+1)+Restarts.totalRounds ns) (fun t ↦ loss (offset+t))
        (Model.appendActions (n+1) (stateAt n outcome.1) (blockActions default ns outcome.2))
    rw [Model.accumulatedLoss_append]
    have htail := ih (offset+(n+1)) outcome.2
    exact congrArg (fun x ↦ pathLoss (fun t ↦ loss (offset+t)) n outcome.1+x)
      (by simpa only [Nat.add_assoc] using htail)

variable [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

def chunkGain (P : FiniteKernel ι) (p : ProbabilityVector ι) (loss : ℕ → ι → ℝ) (offset n : ℕ) : ℝ :=
  probingGain P p (fun t ↦ loss (offset+t)) n

def chunkRemainder (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ) (offset n : ℕ) : ℝ :=
  (R.shift offset).stopRemainder (fun t ↦ loss (offset+t)) M n

theorem blockPlayedLoss_mean (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M) :
    ∀ ns offset, (blockLaw R loss hloss M hM offset ns).mean (blockPlayedLoss loss offset ns) =
      p.mean (blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds ns)) -
        ScoreRule.steeringStrength M*Restarts.chunkSum (chunkGain P p loss) offset ns +
        ScoreRule.steeringStrength M*Restarts.chunkSum (chunkRemainder R loss M) offset ns := by
  intro ns
  induction ns with
  | nil =>
    intro offset
    have hzero : blockLoss (fun t ↦ loss (offset+t)) 0 = (fun _ ↦ (0:ℝ)) := by
      funext i
      simp [blockLoss]
    have hplayed : blockPlayedLoss loss offset [] = (fun _ ↦ (0:ℝ)) := rfl
    rw [hplayed,ProbabilityVector.mean_const]
    change 0 = p.mean (blockLoss (fun t ↦ loss (offset+t)) 0)-ScoreRule.steeringStrength M*0+ScoreRule.steeringStrength M*0
    rw [hzero,ProbabilityVector.mean_const]
    ring
  | cons n ns ih =>
    intro offset
    let headLaw := (R.shift offset).tiltedLaw (fun t ↦ loss (offset+t)) (fun t ↦ hloss (offset+t)) M hM n
    let tailLaw := blockLaw R loss hloss M hM (offset+(n+1)) ns
    change (headLaw.joint (fun _ ↦ tailLaw)).mean (fun outcome : History ι n × BlockOutcome ι ns ↦
      pathLoss (fun t ↦ loss (offset+t)) n outcome.1+blockPlayedLoss loss (offset+(n+1)) ns outcome.2) = _
    rw [ProbabilityVector.mean_add,ProbabilityVector.joint_first_mean headLaw (fun _ ↦ tailLaw)
      (pathLoss (fun t ↦ loss (offset+t)) n), ProbabilityVector.independent_second_mean headLaw tailLaw
        (blockPlayedLoss loss (offset+(n+1)) ns)]
    have hhead := ((R.shift offset).chunk_loss_response (fun t ↦ loss (offset+t))
      (fun t ↦ hloss (offset+t)) M hM n).1
    rw [hhead,ih (offset+(n+1))]
    have hsplit : blockLoss (fun t ↦ loss (offset+t)) (Restarts.totalRounds (n::ns)) =
        (fun i ↦ blockLoss (fun t ↦ loss (offset+t)) (n+1) i+
          blockLoss (fun t ↦ loss ((offset+(n+1))+t)) (Restarts.totalRounds ns) i) := by
      funext i
      exact blockLoss_append loss offset (n+1) (Restarts.totalRounds ns) i
    rw [hsplit,ProbabilityVector.mean_add]
    simp only [Restarts.chunkSum,chunkGain,chunkRemainder]
    ring

theorem partitionedBlockLoss_mean (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (offset n : ℕ) :
    (partitionedBlockLaw R loss hloss M hM τ hτ hτ1 offset n).mean
      (fun outcome ↦ blockPlayedLoss loss offset (Restarts.parts n outcome.1) outcome.2) =
      p.mean (blockLoss (fun t ↦ loss (offset+t)) (n+1)) -
        ScoreRule.steeringStrength M*Restarts.chunkSumMean τ hτ hτ1 (chunkGain P p loss) n offset +
        ScoreRule.steeringStrength M*Restarts.chunkSumMean τ hτ hτ1 (chunkRemainder R loss M) n offset := by
  unfold partitionedBlockLaw
  rw [ProbabilityVector.sigmaJoint_mean]
  have heq : (fun coins ↦ (blockLaw R loss hloss M hM offset (Restarts.parts n coins)).mean
      (blockPlayedLoss loss offset (Restarts.parts n coins))) =
      (fun coins ↦ p.mean (blockLoss (fun t ↦ loss (offset+t)) (n+1)) -
        ScoreRule.steeringStrength M*Restarts.chunkSum (chunkGain P p loss) offset (Restarts.parts n coins)+
        ScoreRule.steeringStrength M*Restarts.chunkSum (chunkRemainder R loss M) offset (Restarts.parts n coins)) := by
    funext coins
    rw [blockPlayedLoss_mean,Restarts.parts_totalRounds]
  rw [heq,ProbabilityVector.mean_add,ProbabilityVector.mean_sub,ProbabilityVector.mean_const,
    ProbabilityVector.mean_const_mul,ProbabilityVector.mean_const_mul]
  rfl

theorem block_remainder_mean_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hMlog : 100*Real.log (2/δ) ≤ M) (offset n : ℕ) :
    Restarts.chunkSumMean τ (le_of_lt hτ) hτ1 (chunkRemainder R loss M) n offset ≤ δ*((n:ℝ)+1)^3 := by
  calc
    _ ≤ (Restarts.law τ (le_of_lt hτ) hτ1 n).mean (fun coins ↦ Restarts.chunkSum
        (fun start k ↦ ((k:ℝ)+1)^2*chunkStopProbability R loss M start k) offset (Restarts.parts n coins)) := by
      apply ProbabilityVector.mean_mono
      intro coins
      apply Restarts.chunkSum_mono
      intro start k
      exact le_trans (le_abs_self _) ((R.shift start).stopRemainder_abs_le
        (fun t ↦ loss (start+t)) (fun t ↦ hloss (start+t)) M k)
    _ ≤ _ := block_stopping_error_le H hτ hτ1 R loss hloss M δ hδ hδ1 hMlog offset n

theorem partitioned_block_loss_bound (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hMlog : 100*Real.log (2/δ) ≤ M)
    (default : ι) (offset n : ℕ) :
    (partitionedBlockLaw R loss hloss M hM τ (le_of_lt hτ) hτ1 offset n).mean
      (fun outcome ↦ Model.accumulatedLoss (n+1) (fun t ↦ loss (offset+t))
        (blockActions default (Restarts.parts n outcome.1) outcome.2)) ≤
      H.sampling.mean (blockLoss (fun t ↦ loss (offset+t)) (n+1)) -
        ScoreRule.steeringStrength M*Restarts.chunkSumMean τ (le_of_lt hτ) hτ1
          (chunkGain (H.kernel τ hτ) H.sampling loss) n offset +
        ScoreRule.steeringStrength M*δ*((n:ℝ)+1)^3 := by
  have heq : (fun outcome : (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins) ↦
      Model.accumulatedLoss (n+1) (fun t ↦ loss (offset+t)) (blockActions default (Restarts.parts n outcome.1) outcome.2)) =
      (fun outcome ↦ blockPlayedLoss loss offset (Restarts.parts n outcome.1) outcome.2) := by
    funext outcome
    rw [blockPlayedLoss_eq_accumulatedLoss loss default,Restarts.parts_totalRounds]
  rw [heq,partitionedBlockLoss_mean]
  have hr := block_remainder_mean_le H hτ hτ1 R loss hloss M δ hδ hδ1 hMlog offset n
  have hβ := ScoreRule.steeringStrength_pos hM
  nlinarith

end Upper
end
end Tournament

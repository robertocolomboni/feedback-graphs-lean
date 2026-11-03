module

public import Tournament.Model.Concatenation
public import Tournament.Probability.RestartCount
public import Tournament.Upper.BlockUnbiasedness

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FinitePath

variable {ι : Type*}

noncomputable section

def blockActions (default : ι) : (ns : List ℕ) → BlockOutcome ι ns → ℕ → ι
  | [], _ => fun _ ↦ default
  | n::ns, outcome => Model.appendActions (n+1) (stateAt n outcome.1) (blockActions default ns outcome.2)

def chunkInternalSwitches [DecidableEq ι] : (ns : List ℕ) → BlockOutcome ι ns → ℕ
  | [], _ => 0
  | n::ns, outcome => switches n outcome.1 + chunkInternalSwitches ns outcome.2

theorem block_switchCount_le [DecidableEq ι] (default : ι) :
    ∀ ns (outcome : BlockOutcome ι ns),
    Model.switchCount (Restarts.totalRounds ns) (blockActions default ns outcome) ≤
      chunkInternalSwitches ns outcome + (ns.length-1) := by
  intro ns
  induction ns with
  | nil => intro outcome; simp [Restarts.totalRounds,Model.switchCount,chunkInternalSwitches]
  | cons n ns ih =>
    intro outcome
    cases ns with
    | nil =>
      change Model.switchCount (n+1) (Model.appendActions (n+1) (stateAt n outcome.1) (fun _ ↦ default)) ≤ switches n outcome.1
      rw [Model.switchCount_append_prefix,← switches_eq_switchCount]
    | cons m ms =>
      let k := Restarts.totalRounds (m::ms)-1
      have htail : Restarts.totalRounds (m::ms)=k+1 := by
        change (m+1)+Restarts.totalRounds ms = ((m+1)+Restarts.totalRounds ms)-1+1
        omega
      change Model.switchCount ((n+1)+Restarts.totalRounds (m::ms))
        (Model.appendActions (n+1) (stateAt n outcome.1) (blockActions default (m::ms) outcome.2)) ≤
        switches n outcome.1+chunkInternalSwitches (m::ms) outcome.2+((n::m::ms).length-1)
      rw [htail,Model.switchCount_append n k (stateAt n outcome.1) (blockActions default (m::ms) outcome.2),
        ← switches_eq_switchCount]
      have hIH : Model.switchCount (k+1) (blockActions default (m::ms) outcome.2) ≤
          chunkInternalSwitches (m::ms) outcome.2+((m::ms).length-1) := by
        simpa only [htail] using ih outcome.2
      have hboundary : (if blockActions default (m::ms) outcome.2 0=stateAt n outcome.1 n then 0 else 1) ≤ 1 := by
        split <;> norm_num
      simp only [List.length_cons] at hIH ⊢
      omega

variable [Fintype ι]

theorem tilted_chunk_switches_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M) (n : ℕ) :
    (R.tiltedLaw loss hloss M hM n).mean (fun hist ↦ (switches n hist : ℝ)) ≤ (5/8)*τ*(n:ℝ) := by
  have hdom := R.tilted_nonneg_mean_le loss hloss M hM n
    (fun hist ↦ (switches n hist : ℝ)) (fun _ ↦ Nat.cast_nonneg _)
  have href := holding_expected_switches H hτ n
  calc
    _ ≤ (5/4)*(law (H.kernel τ hτ) H.sampling n).mean (fun hist ↦ (switches n hist : ℝ)) := hdom
    _ ≤ (5/4)*((n:ℝ)*τ/2) := mul_le_mul_of_nonneg_left href (by norm_num)
    _ = _ := by ring

theorem block_internal_switches_mean_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M) :
    ∀ ns offset, (blockLaw R loss hloss M hM offset ns).mean
      (fun outcome ↦ (chunkInternalSwitches ns outcome : ℝ)) ≤ (5/8)*τ*(Restarts.totalRounds ns:ℝ) := by
  intro ns
  induction ns with
  | nil =>
    intro offset
    have heq : (fun outcome : BlockOutcome ι [] ↦ (chunkInternalSwitches [] outcome : ℝ)) = (fun _ ↦ 0) := by
      funext outcome
      simp [chunkInternalSwitches]
    rw [heq,ProbabilityVector.mean_const]
    simp [Restarts.totalRounds]
  | cons n ns ih =>
    intro offset
    let headLaw := (R.shift offset).tiltedLaw (fun t ↦ loss (offset+t))
      (fun t ↦ hloss (offset+t)) M hM n
    let tailLaw := blockLaw R loss hloss M hM (offset+(n+1)) ns
    have heq : (fun outcome : History ι n × BlockOutcome ι ns ↦
        (chunkInternalSwitches (n::ns) outcome : ℝ)) =
        (fun outcome ↦ (switches n outcome.1 : ℝ)+(chunkInternalSwitches ns outcome.2 : ℝ)) := by
      funext outcome
      exact Nat.cast_add _ _
    change (headLaw.joint (fun _ ↦ tailLaw)).mean
      (fun outcome : History ι n × BlockOutcome ι ns ↦ (chunkInternalSwitches (n::ns) outcome : ℝ)) ≤ _
    rw [heq,ProbabilityVector.mean_add,ProbabilityVector.joint_first_mean headLaw (fun _ ↦ tailLaw)
      (fun hist ↦ (switches n hist : ℝ)), ProbabilityVector.independent_second_mean headLaw tailLaw
        (fun outcome ↦ (chunkInternalSwitches ns outcome : ℝ))]
    have hhead := tilted_chunk_switches_le H hτ (R.shift offset)
      (fun t ↦ loss (offset+t)) (fun t ↦ hloss (offset+t)) M hM n
    have htail := ih (offset+(n+1))
    simp only [Restarts.totalRounds,Nat.cast_add,Nat.cast_one]
    nlinarith

theorem block_switchCount_mean_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (default : ι) (ns : List ℕ) (offset : ℕ) :
    (blockLaw R loss hloss M hM offset ns).mean (fun outcome ↦
      (Model.switchCount (Restarts.totalRounds ns) (blockActions default ns outcome) : ℝ)) ≤
        (5/8)*τ*(Restarts.totalRounds ns:ℝ)+(ns.length-1:ℕ) := by
  calc
    _ ≤ (blockLaw R loss hloss M hM offset ns).mean (fun outcome ↦
        (chunkInternalSwitches ns outcome : ℝ)+(ns.length-1:ℕ)) := by
      apply ProbabilityVector.mean_mono
      intro outcome
      exact_mod_cast block_switchCount_le default ns outcome
    _ = (blockLaw R loss hloss M hM offset ns).mean (fun outcome ↦ (chunkInternalSwitches ns outcome : ℝ)) +
        (ns.length-1:ℕ) := by rw [ProbabilityVector.mean_add,ProbabilityVector.mean_const]
    _ ≤ _ := add_le_add (block_internal_switches_mean_le H hτ R loss hloss M hM ns offset) le_rfl

theorem partitioned_block_switchCount_mean_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (default : ι) (n offset : ℕ) :
    (partitionedBlockLaw R loss hloss M hM τ (le_of_lt hτ) hτ1 offset n).mean
      (fun outcome ↦ (Model.switchCount (n+1)
        (blockActions default (Restarts.parts n outcome.1) outcome.2) : ℝ)) ≤ (13/8)*τ*((n:ℝ)+1) := by
  unfold partitionedBlockLaw
  rw [ProbabilityVector.sigmaJoint_mean]
  calc
    _ ≤ (Restarts.law τ (le_of_lt hτ) hτ1 n).mean (fun coins ↦
        (5/8)*τ*((n:ℝ)+1)+(Restarts.restartCount n coins:ℝ)) := by
      apply ProbabilityVector.mean_mono
      intro coins
      have h := block_switchCount_mean_le H hτ R loss hloss M hM default (Restarts.parts n coins) offset
      simpa only [Restarts.parts_totalRounds,Restarts.parts_boundary_count,Nat.cast_add,Nat.cast_one] using h
    _ = (5/8)*τ*((n:ℝ)+1)+(n:ℝ)*τ := by
      rw [ProbabilityVector.mean_add,ProbabilityVector.mean_const,Restarts.expected_restartCount]
    _ ≤ _ := by nlinarith

theorem dyadic_block_switchCount_mean_le (H : HoldingFamily ι) {F : ι → ι → Prop}
    (m : ℕ) (R : DyadicScoreRules H F m) (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (M : ℝ) (hM : 1 ≤ M) (default : ι) (n offset : ℕ) :
    (dyadicBlockLaw H m R loss hloss M hM offset n).mean (fun outcome ↦
      (Model.switchCount (n+1) (blockActions default (Restarts.parts n outcome.2.1) outcome.2.2) : ℝ)) ≤
        (13/8)*(DyadicRate.base m*(1+(m:ℝ)/2))*((n:ℝ)+1) := by
  change ((DyadicRate.law m).sigmaJoint (fun j ↦ partitionedBlockLaw (R j) loss hloss M hM
    (DyadicRate.rate m j) (le_of_lt (DyadicRate.rate_pos m j)) (DyadicRate.rate_le_one m j) offset n)).mean
    (fun outcome : (_j : Fin (m+1)) × (coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins) ↦
      (Model.switchCount (n+1) (blockActions default (Restarts.parts n outcome.2.1) outcome.2.2) : ℝ)) ≤ _
  rw [ProbabilityVector.sigmaJoint_mean]
  calc
    _ ≤ (DyadicRate.law m).mean (fun j ↦ (13/8)*(DyadicRate.rate m j)*((n:ℝ)+1)) := by
      apply ProbabilityVector.mean_mono
      intro j
      exact partitioned_block_switchCount_mean_le H (DyadicRate.rate_pos m j) (DyadicRate.rate_le_one m j)
        (R j) loss hloss M hM default n offset
    _ = _ := by
      rw [ProbabilityVector.mean_mul_const,ProbabilityVector.mean_const_mul,DyadicRate.mean_rate]

end
end Tournament.Upper

module

public import Tournament.Probability.ChunkPartitions
public import Tournament.Upper.EstimatorChunkTail

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace ProbabilityVector

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

theorem independent_product_mean (μ : ProbabilityVector Ω) (ν : ProbabilityVector S)
    (f : Ω → ℝ) (g : S → ℝ) :
    (μ.joint (fun _ ↦ ν)).mean (fun xy ↦ f xy.1*g xy.2) = μ.mean f*ν.mean g := by
  rw [joint_mean]
  simp only [mean_const_mul]
  exact mean_mul_const μ f (ν.mean g)

theorem independent_exp_add (μ : ProbabilityVector Ω) (ν : ProbabilityVector S)
    (f : Ω → ℝ) (g : S → ℝ) (θ : ℝ) :
    (μ.joint (fun _ ↦ ν)).mean (fun xy ↦ Real.exp (θ*(f xy.1+g xy.2))) =
      μ.mean (fun x ↦ Real.exp (θ*f x))*ν.mean (fun y ↦ Real.exp (θ*g y)) := by
  have heq : (fun xy : Ω × S ↦ Real.exp (θ*(f xy.1+g xy.2))) =
      (fun xy ↦ Real.exp (θ*f xy.1)*Real.exp (θ*g xy.2)) := by
    funext xy
    rw [mul_add, Real.exp_add]
  rw [heq]
  exact independent_product_mean μ ν (fun x ↦ Real.exp (θ*f x)) (fun y ↦ Real.exp (θ*g y))

end ProbabilityVector

namespace Upper

open FinitePath

universe u

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

namespace ScoreRule

def shift (R : ScoreRule F P p) (offset : ℕ) : ScoreRule F P p where
  sampling_pos := R.sampling_pos
  reversible := R.reversible
  holding := R.holding
  score t := R.score (offset+t)
  decoder t := R.decoder (offset+t)
  decoder_local t := R.decoder_local (offset+t)
  decoder_eq t := R.decoder_eq (offset+t)
  zero_mean t := R.zero_mean (offset+t)
  off_diagonal_abs t := R.off_diagonal_abs (offset+t)
  diagonal_abs t := R.diagonal_abs (offset+t)
  correlation t := R.correlation (offset+t)

end ScoreRule

abbrev BlockOutcome (ι : Type u) : List ℕ → Type u
  | [] => ULift Unit
  | n::ns => History ι n × BlockOutcome ι ns

instance blockOutcomeFintype (ns : List ℕ) : Fintype (BlockOutcome ι ns) := by
  induction ns with
  | nil => exact inferInstanceAs (Fintype (ULift Unit))
  | cons n ns ih =>
    letI : Fintype (BlockOutcome ι ns) := ih
    exact inferInstanceAs (Fintype (History ι n × BlockOutcome ι ns))

def blockLaw (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M) :
    (offset : ℕ) → (ns : List ℕ) → ProbabilityVector (BlockOutcome ι ns)
  | _, [] => ProbabilityVector.pure (ULift.up ())
  | offset, n::ns => ((R.shift offset).tiltedLaw (fun t ↦ loss (offset+t))
      (fun t ↦ hloss (offset+t)) M hM n).joint
        (fun _ ↦ blockLaw R loss hloss M hM (offset+(n+1)) ns)

def blockRatioTotal (f : ι → ℝ) : (ns : List ℕ) → BlockOutcome ι ns → ℝ
  | [], _ => 0
  | n::ns, outcome => stateTotal f n outcome.1 + blockRatioTotal f ns outcome.2

def partitionedBlockLaw (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (offset n : ℕ) :
    ProbabilityVector ((coins : Restarts.Coins n) × BlockOutcome ι (Restarts.parts n coins)) :=
  (Restarts.law τ hτ hτ1 n).sigmaJoint
    (fun coins ↦ blockLaw R loss hloss M hM offset (Restarts.parts n coins))

end Upper
end
end Tournament

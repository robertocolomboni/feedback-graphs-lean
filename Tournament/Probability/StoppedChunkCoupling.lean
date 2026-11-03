module

public import Tournament.Probability.StoppedChain

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace Restarts

theorem coin_mean {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (f : Bool → ℝ) :
    (coin τ hτ hτ1).mean f = τ*f true+(1-τ)*f false := by
  simp [ProbabilityVector.mean, coin]

end Restarts

namespace StoppedChain

open FinitePath

variable {ι : Type*} [Fintype ι]

def paddedMean (P : FiniteKernel ι) (μ : ProbabilityVector ι) (τ : ℝ)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) (f : History (Option ι) n → ℝ) : ℝ :=
  (Restarts.referenceChunkLaw P μ τ hτ hτ1 n).mean
    (fun outcome ↦ f (pad n (Restarts.length n outcome.1) (Restarts.length_le n outcome.1) outcome.2))

theorem padded_first_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) (f : History (Option ι) (n+1) → ℝ) :
    paddedMean P μ τ hτ hτ1 (n+1) f =
      μ.mean (fun i ↦ τ*f (prepend (some i) n (constantHistory none n)) +
        (1-τ)*paddedMean P (P.row i) τ hτ hτ1 n (fun hist ↦ f (prepend (some i) n hist))) := by
  rw [paddedMean, Restarts.referenceChunk_mean]
  change ((Restarts.coin τ hτ hτ1).joint (fun _ ↦ Restarts.law τ hτ hτ1 n)).mean
    (fun coins : Bool × Restarts.Coins n ↦ (law P μ (Restarts.length (n+1) coins)).mean
      (fun hist ↦ f (pad (n+1) (Restarts.length (n+1) coins) (Restarts.length_le (n+1) coins) hist))) = _
  rw [ProbabilityVector.joint_mean, Restarts.coin_mean]
  change τ*(Restarts.law τ hτ hτ1 n).mean (fun _ ↦
    μ.mean (fun i ↦ f (prepend (some i) n (constantHistory none n)))) +
    (1-τ)*(Restarts.law τ hτ hτ1 n).mean (fun coins ↦
      (law P μ (Restarts.length n coins+1)).mean
        (fun hist ↦ f (pad (n+1) (Restarts.length n coins+1) (by have h := Restarts.length_le n coins; omega) hist))) = _
  rw [ProbabilityVector.mean_const]
  have heq : (fun coins : Restarts.Coins n ↦ (law P μ (Restarts.length n coins+1)).mean
      (fun hist ↦ f (pad (n+1) (Restarts.length n coins+1) (by have h := Restarts.length_le n coins; omega) hist))) =
      (fun coins ↦ μ.mean (fun i ↦ (law P (P.row i) (Restarts.length n coins)).mean
        (fun hist ↦ f (prepend (some i) n (pad n (Restarts.length n coins) (Restarts.length_le n coins) hist))))) := by
    funext coins
    rw [law_first_mean]
    congr 1
    funext i
    congr 1
    funext hist
    rw [pad_prepend]
  rw [heq, ProbabilityVector.means_comm]
  have htail : (fun i ↦ (Restarts.law τ hτ hτ1 n).mean (fun coins ↦
      (law P (P.row i) (Restarts.length n coins)).mean
        (fun hist ↦ f (prepend (some i) n (pad n (Restarts.length n coins) (Restarts.length_le n coins) hist))))) =
      (fun i ↦ paddedMean P (P.row i) τ hτ hτ1 n (fun hist ↦ f (prepend (some i) n hist))) := by
    funext i
    exact (Restarts.referenceChunk_mean P (P.row i) τ hτ hτ1 n
      (fun outcome ↦ f (prepend (some i) n
        (pad n (Restarts.length n outcome.1) (Restarts.length_le n outcome.1) outcome.2)))).symm
  rw [htail, ← ProbabilityVector.mean_const_mul, ← ProbabilityVector.mean_const_mul,
    ← ProbabilityVector.mean_add]

theorem referenceChunk_padded_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) (f : History (Option ι) n → ℝ) :
    paddedMean P μ τ hτ hτ1 n f = (law (kernel P τ hτ hτ1) (initial μ) n).mean f := by
  induction n generalizing μ with
  | zero =>
    rw [paddedMean, Restarts.referenceChunk_mean]
    change (Restarts.law τ hτ hτ1 0).mean (fun _ ↦ μ.mean (fun i ↦ f (some i))) = (initial μ).mean f
    rw [ProbabilityVector.mean_const, initial_mean]
  | succ n ih =>
    rw [padded_first_mean, stopped_first_mean]
    congr 1
    funext i
    rw [ih (P.row i) (fun hist ↦ f (prepend (some i) n hist))]

end StoppedChain
end
end Tournament

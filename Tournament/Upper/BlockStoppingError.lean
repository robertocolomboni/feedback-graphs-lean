module

public import Tournament.Probability.ChunkSums
public import Tournament.Upper.ScoreTail

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FinitePath

variable {ι : Type*} [Fintype ι]
variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

noncomputable section

def chunkStopProbability (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ) (offset n : ℕ) : ℝ :=
  (R.shift offset).stopProbability (fun t ↦ loss (offset+t)) M n

theorem chunkStopProbability_nonneg (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (M : ℝ) (offset n : ℕ) : 0 ≤ chunkStopProbability R loss M offset n := by
  apply ProbabilityVector.mean_nonneg
  intro hist
  split <;> norm_num

theorem fresh_chunkStopProbability_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hMlog : 100*Real.log (2/δ) ≤ M) (offset n : ℕ) :
    Restarts.firstChunkMean τ (le_of_lt hτ) hτ1 (chunkStopProbability R loss M) n offset ≤ δ := by
  have h := H.score_stopping_tail hτ hτ1 (R.shift offset) (fun t ↦ loss (offset+t))
    (fun t ↦ hloss (offset+t)) H.sampling M δ hδ hδ1 hMlog n
  change ((Restarts.law τ (le_of_lt hτ) hτ1 n).sigmaJoint
    (fun coins ↦ law (H.kernel τ hτ) H.sampling (Restarts.length n coins))).probability
      (fun outcome : (coins : Restarts.Coins n) × History ι (Restarts.length n coins) ↦
        (R.shift offset).stopEvent (fun t ↦ loss (offset+t)) M (Restarts.length n outcome.1) outcome.2) ≤ δ at h
  unfold ProbabilityVector.probability at h
  rw [ProbabilityVector.sigmaJoint_mean] at h
  exact h

theorem block_stopping_error_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (R : ScoreRule F (H.kernel τ hτ) H.sampling) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hMlog : 100*Real.log (2/δ) ≤ M) (offset n : ℕ) :
    (Restarts.law τ (le_of_lt hτ) hτ1 n).mean (fun coins ↦ Restarts.chunkSum
      (fun start k ↦ ((k:ℝ)+1)^2*chunkStopProbability R loss M start k) offset (Restarts.parts n coins)) ≤
        δ*((n:ℝ)+1)^3 := by
  let q := chunkStopProbability R loss M
  have hq : ∀ start k, 0 ≤ q start k := chunkStopProbability_nonneg R loss M
  have hfresh : ∀ start k, Restarts.firstChunkMean τ (le_of_lt hτ) hτ1 q k start ≤ δ :=
    fun start k ↦ fresh_chunkStopProbability_le H hτ hτ1 R loss hloss M δ hδ hδ1 hMlog start k
  have hsum := Restarts.chunkSumMean_le_of_fresh (le_of_lt hτ) hτ1 q hq δ hfresh n offset
  calc
    _ ≤ (Restarts.law τ (le_of_lt hτ) hτ1 n).mean
        (fun coins ↦ ((n:ℝ)+1)^2*Restarts.chunkSum q offset (Restarts.parts n coins)) := by
      apply ProbabilityVector.mean_mono
      intro coins
      have h := Restarts.chunkSum_weighted_le q hq (n+1) (Restarts.parts n coins)
        (by rw [Restarts.parts_totalRounds]) offset
      simpa only [Nat.cast_add,Nat.cast_one] using h
    _ = ((n:ℝ)+1)^2*Restarts.chunkSumMean τ (le_of_lt hτ) hτ1 q n offset :=
      ProbabilityVector.mean_const_mul _ _ _
    _ ≤ ((n:ℝ)+1)^2*(((n:ℝ)+1)*δ) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = δ*((n:ℝ)+1)^3 := by ring

end
end Tournament.Upper

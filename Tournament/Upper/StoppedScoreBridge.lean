module

public import Tournament.Probability.StoppedChunkCoupling
public import Tournament.Probability.ChronologicalEdges
public import Tournament.Upper.ScoreOccupation
public import Tournament.Upper.BlockLaw

@[expose] public section

namespace Tournament.StoppedChain

open scoped BigOperators Classical
open FinitePath Upper

variable {ι : Type*}

noncomputable section

def liftEdge (d : ℕ → ι → ι → ℝ) (t : ℕ) : Option ι → Option ι → ℝ
  | some i, some j => d t i j
  | _, _ => 0

theorem firstState_pad (n m : ℕ) (hm : m ≤ n) (hist : History ι m) :
    firstState n (pad n m hm hist) = some (firstState m hist) := by
  cases n with
  | zero =>
    have hm0 : m=0 := Nat.eq_zero_of_le_zero hm
    subst m
    rfl
  | succ n =>
    cases m with
    | zero => exact firstState_prepend (some hist) n (constantHistory none n)
    | succ m =>
      exact firstState_prepend (some (firstState (m+1) hist)) n (pad n m (by omega) (dropFirst m hist))

theorem edgeTotal_pad (d : ℕ → ι → ι → ℝ) (n m : ℕ) (hm : m ≤ n) (hist : History ι m) :
    edgeTotal (liftEdge d) n (pad n m hm hist) = edgeTotal d m hist := by
  induction n generalizing m d with
  | zero =>
    have hm0 : m=0 := Nat.eq_zero_of_le_zero hm
    subst m
    simp [edgeTotal]
  | succ n ih =>
    cases m with
    | zero =>
      change edgeTotal (liftEdge d) (n+1) (prepend (some hist : Option ι) n (constantHistory none n)) = _
      rw [edgeTotal_prepend, firstState_constant, edgeTotal_constant _ none (fun _ ↦ rfl)]
      simp [liftEdge, edgeTotal]
    | succ m =>
      let i := firstState (m+1) hist
      let tail := dropFirst m hist
      have hhist : hist=prepend i m tail := (prepend_first_drop m hist).symm
      rw [hhist, pad_prepend n m (by omega) i tail, edgeTotal_prepend, edgeTotal_prepend, firstState_pad]
      change d 0 i (firstState m tail) +
        edgeTotal (fun t ↦ liftEdge d (t+1)) n (pad n m _ tail) =
        d 0 i (firstState m tail) + edgeTotal (fun t ↦ d (t+1)) m tail
      have hshift : (fun t ↦ liftEdge d (t+1)) = liftEdge (fun t ↦ d (t+1)) := rfl
      rw [hshift, ih (fun t ↦ d (t+1)) m (by omega) tail]

variable [Fintype ι]

theorem lifted_absoluteScores_functional_mean (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (μ : ProbabilityVector ι) (n : ℕ) (g : ℝ → ℝ) :
    (law (kernel (H.kernel τ hτ) τ (le_of_lt hτ) hτ1) (initial μ) n).mean
      (fun hist ↦ g (edgeTotal (liftEdge (fun t i j ↦ |R.score t (loss t) i j|)) n hist)) =
    (Restarts.referenceChunkLaw (H.kernel τ hτ) μ τ (le_of_lt hτ) hτ1 n).mean
      (fun outcome ↦ g (R.absoluteScores loss (Restarts.length n outcome.1) outcome.2)) := by
  rw [← referenceChunk_padded_mean]
  unfold paddedMean
  congr 1
  funext outcome
  rcases outcome with ⟨coins,hist⟩
  dsimp only
  rw [edgeTotal_pad]
  have heq := (R.absoluteScores_eq_sum loss (Restarts.length n coins) hist).symm
  exact congrArg g heq

theorem lifted_absoluteScores_mean (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (μ : ProbabilityVector ι) (n : ℕ) :
    (law (kernel (H.kernel τ hτ) τ (le_of_lt hτ) hτ1) (initial μ) n).mean
      (edgeTotal (liftEdge (fun t i j ↦ |R.score t (loss t) i j|)) n) =
    (Restarts.referenceChunkLaw (H.kernel τ hτ) μ τ (le_of_lt hτ) hτ1 n).mean
      (fun outcome ↦ R.absoluteScores loss (Restarts.length n outcome.1) outcome.2) := by
  rw [← referenceChunk_padded_mean]
  unfold paddedMean
  congr 1
  funext outcome
  rw [edgeTotal_pad]
  exact (R.absoluteScores_eq_sum loss _ _).symm

theorem lifted_absoluteScores_from_state_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (s : Option ι) (n : ℕ) :
    (law (kernel (H.kernel τ hτ) τ (le_of_lt hτ) hτ1) (ProbabilityVector.pure s) n).mean
      (edgeTotal (liftEdge (fun t i j ↦ |R.score t (loss t) i j|)) n) ≤ 7 := by
  cases s with
  | none =>
    rw [law_from_none, edgeTotal_constant _ none (fun _ ↦ rfl)]
    norm_num
  | some i =>
    have hstart : (law (kernel (H.kernel τ hτ) τ (le_of_lt hτ) hτ1) (initial (ProbabilityVector.pure i)) n).mean
        (edgeTotal (liftEdge (fun t i j ↦ |R.score t (loss t) i j|)) n) =
        (law (kernel (H.kernel τ hτ) τ (le_of_lt hτ) hτ1) (ProbabilityVector.pure (some i)) n).mean
          (edgeTotal (liftEdge (fun t i j ↦ |R.score t (loss t) i j|)) n) := by
      rw [law_mean_initial_state, initial_mean, ProbabilityVector.pure_mean]
    rw [← hstart, lifted_absoluteScores_mean]
    exact Upper.ScoreRule.reference_chunk_absoluteScores_le H hτ hτ1 R loss hloss (ProbabilityVector.pure i) n

theorem absoluteScore_futureValue_le (H : HoldingFamily ι) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {F : ι → ι → Prop} (R : ScoreRule F (H.kernel τ hτ) H.sampling)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (s k : ℕ) (i : Option ι) :
    futureEdgeValue (kernel (H.kernel τ hτ) τ (le_of_lt hτ) hτ1)
      (liftEdge (fun t i j ↦ |R.score t (loss t) i j|)) s k i ≤ 7 := by
  rw [futureEdgeValue_eq_mean]
  exact lifted_absoluteScores_from_state_le H hτ hτ1 (R.shift s)
    (fun t ↦ loss (s+t)) (fun t ↦ hloss (s+t)) i k

end
end Tournament.StoppedChain

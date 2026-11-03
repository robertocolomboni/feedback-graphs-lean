module

public import Tournament.Upper.ChunkMoments
public import Tournament.Probability.Correlations

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical
open FinitePath

variable {ι : Type*} [Fintype ι]

noncomputable section

def pathLoss (loss : ℕ → ι → ℝ) (n : ℕ) (hist : History ι n) : ℝ :=
  ∑ t ∈ Finset.range (n+1), loss t (stateAt n hist t)

omit [Fintype ι] in
theorem pathLoss_bounds (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t))
    (n : ℕ) (hist : History ι n) : 0 ≤ pathLoss loss n hist ∧ pathLoss loss n hist ≤ n+1 := by
  constructor
  · exact Finset.sum_nonneg (fun t _ ↦ (hloss t (stateAt n hist t)).1)
  · calc
      pathLoss loss n hist ≤ ∑ t ∈ Finset.range (n+1), (1:ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        exact (hloss t (stateAt n hist t)).2
      _ = n+1 := by simp

theorem pathLoss_mean (P : FiniteKernel ι) (p : ProbabilityVector ι) (hstat : P.Stationary p)
    (loss : ℕ → ι → ℝ) (n : ℕ) :
    (law P p n).mean (pathLoss loss n) = p.mean (blockLoss loss (n+1)) := by
  unfold pathLoss blockLoss
  rw [ProbabilityVector.mean_sum, ProbabilityVector.mean_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact stationary_stateAt_mean P p hstat n t
    (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) (loss t)

def probingGain (P : FiniteKernel ι) (p : ProbabilityVector ι) (loss : ℕ → ι → ℝ)
    (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, ∑ u ∈ Finset.range (n+1),
    if t<u then FiniteKernel.weightedInner p (loss t)
      (fun i ↦ ((P.act)^[u-t-1]) (loss u) i - P.act (((P.act)^[u-t-1]) (loss u)) i) else 0

namespace ScoreRule

variable {F : ι → ι → Prop} {P : FiniteKernel ι} {p : ProbabilityVector ι}

def rawSum (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) : (n : ℕ) → History ι n → ℝ
  | 0, _ => 0
  | n+1, (hist,j) => rawSum R loss n hist + R.score n (loss n) (lastState n hist) j

def stopEvent (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ) :
    (n : ℕ) → History ι n → Prop
  | 0, _ => False
  | n+1, (hist,j) => stopEvent R loss M n hist ∨
      (¬ |R.stoppedSum loss M n hist| ≤ M-1 ∨ ¬ |R.stoppedSum loss M (n+1) (hist,j)| ≤ M-1)

def stopProbability (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ) (n : ℕ) : ℝ :=
  (law P p n).mean (fun hist ↦ if R.stopEvent loss M n hist then 1 else 0)

def stopRemainder (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ) (n : ℕ) : ℝ :=
  (law P p n).mean (fun hist ↦
    (R.stoppedSum loss M n hist - R.rawSum loss n hist) * pathLoss loss n hist)

theorem stopEvent_iff_final_exceeded (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (M : ℝ) (hM : 1 ≤ M) (n : ℕ) (hist : History ι n) :
    R.stopEvent loss M n hist ↔ M-1 < |R.stoppedSum loss M n hist| := by
  induction n with
  | zero =>
    simp only [stopEvent, stoppedSum, abs_zero]
    constructor
    · exact False.elim
    · intro h
      linarith
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    rw [stopEvent, ih hist]
    simp only [not_le]
    have hfreeze : M-1 < |R.stoppedSum loss M n hist| →
        M-1 < |R.stoppedSum loss M (n+1) (hist,j)| := by
      intro h
      rw [stoppedSum_step, effectiveScore, ite_eq_right (not_le.mpr h), add_zero]
      exact h
    constructor
    · rintro (h | h | h)
      · exact hfreeze h
      · exact hfreeze h
      · exact h
    · intro h
      exact Or.inr (Or.inr h)

theorem rawSum_eq_sum (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (n : ℕ) (hist : History ι n) :
    R.rawSum loss n hist =
      ∑ t ∈ Finset.range n, transitionValue (R.score t (loss t)) n hist t := by
  induction n with
  | zero => simp [rawSum]
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    change R.rawSum loss n hist + R.score n (loss n) (lastState n hist) j = _
    rw [Finset.sum_range_succ]
    have hprefix : (∑ t ∈ Finset.range n, transitionValue (R.score t (loss t)) (n+1) (hist,j) t) =
        ∑ t ∈ Finset.range n, transitionValue (R.score t (loss t)) n hist t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact transitionValue_prefix _ n (hist,j) t (Finset.mem_range.mp ht)
    rw [hprefix, transitionValue_last, ih hist]

theorem stopped_eq_raw_of_not_stop (R : ScoreRule F P p) (loss : ℕ → ι → ℝ) (M : ℝ)
    (n : ℕ) (hist : History ι n) (hstop : ¬ R.stopEvent loss M n hist) :
    R.stoppedSum loss M n hist = R.rawSum loss n hist := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    have hprev : ¬ R.stopEvent loss M n hist := fun h ↦ hstop (Or.inl h)
    have hactive : |R.stoppedSum loss M n hist| ≤ M-1 := by
      by_contra h
      exact hstop (Or.inr (Or.inl h))
    rw [stoppedSum_step, effectiveScore, ite_eq_left hactive, rawSum, ih hist hprev]

theorem stopped_sub_raw_abs_le (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (n : ℕ) (hist : History ι n) :
    |R.stoppedSum loss M n hist - R.rawSum loss n hist| ≤ n := by
  induction n with
  | zero => simp [stoppedSum, rawSum]
  | succ n ih =>
    rcases hist with ⟨hist,j⟩
    have hprev := ih hist
    rw [stoppedSum_step, rawSum]
    by_cases hactive : |R.stoppedSum loss M n hist| ≤ M-1
    · rw [effectiveScore, ite_eq_left hactive]
      have heq : R.stoppedSum loss M n hist + R.score n (loss n) (lastState n hist) j -
          (R.rawSum loss n hist + R.score n (loss n) (lastState n hist) j) =
          R.stoppedSum loss M n hist - R.rawSum loss n hist := by ring
      rw [heq]
      push_cast
      linarith
    · rw [effectiveScore, ite_eq_right hactive, add_zero]
      have hscore := R.score_abs_le_one n (hloss n) (lastState n hist) j
      calc
        |R.stoppedSum loss M n hist - (R.rawSum loss n hist + R.score n (loss n) (lastState n hist) j)| =
            |(R.stoppedSum loss M n hist - R.rawSum loss n hist) - R.score n (loss n) (lastState n hist) j| := by
          congr 1
          ring
        _ ≤ |R.stoppedSum loss M n hist - R.rawSum loss n hist| + |R.score n (loss n) (lastState n hist) j| :=
          by simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (R.stoppedSum loss M n hist - R.rawSum loss n hist) 0
              (R.score n (loss n) (lastState n hist) j))
        _ ≤ (n:ℝ)+1 := add_le_add hprev hscore
        _ = (n+1:ℕ) := by push_cast; ring

theorem stopRemainder_abs_le (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (n : ℕ) :
    |R.stopRemainder loss M n| ≤ ((n:ℝ)+1)^2 * R.stopProbability loss M n := by
  calc
    |R.stopRemainder loss M n| ≤ (law P p n).mean (fun hist ↦
        |(R.stoppedSum loss M n hist - R.rawSum loss n hist) * pathLoss loss n hist|) :=
      (law P p n).abs_mean_le _
    _ ≤ (law P p n).mean (fun hist ↦
        ((n:ℝ)+1)^2 * (if R.stopEvent loss M n hist then 1 else 0)) := by
      apply ProbabilityVector.mean_mono
      intro hist
      by_cases hstop : R.stopEvent loss M n hist
      · rw [ite_eq_left hstop, mul_one, abs_mul]
        have hY := pathLoss_bounds loss hloss n hist
        rw [abs_of_nonneg hY.1]
        calc
          |R.stoppedSum loss M n hist - R.rawSum loss n hist| * pathLoss loss n hist ≤
              (n:ℝ)*((n:ℝ)+1) :=
            mul_le_mul (R.stopped_sub_raw_abs_le loss hloss M n hist) hY.2 hY.1 (Nat.cast_nonneg n)
          _ ≤ ((n:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      · rw [ite_eq_right hstop, mul_zero, R.stopped_eq_raw_of_not_stop loss M n hist hstop,
          sub_self, zero_mul, abs_zero]
    _ = ((n:ℝ)+1)^2 * R.stopProbability loss M n :=
      ProbabilityVector.mean_const_mul _ _ _

theorem score_loss_moment (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t))
    (n t u : ℕ) (ht : t < n) (hu : u ≤ n) :
    (law P p n).mean (fun hist ↦ transitionValue (R.score t (loss t)) n hist t *
      loss u (stateAt n hist u)) =
      -(if t<u then FiniteKernel.weightedInner p (loss t)
        (fun i ↦ ((P.act)^[u-t-1]) (loss u) i - P.act (((P.act)^[u-t-1]) (loss u)) i) else 0) := by
  by_cases htu : t < u
  · rw [ite_eq_left htu, transition_future_mean P p (P.reversible_stationary p R.reversible)
      (R.score t (loss t)) n t u htu hu (loss u)]
    exact R.correlation t (loss t) (hloss t) (((P.act)^[u-t-1]) (loss u))
  · rw [ite_eq_right htu, neg_zero]
    apply transition_past_mean_zero P p (R.score t (loss t)) _ n t u ht (by omega) (loss u)
    intro i
    exact R.zero_mean t (loss t) (hloss t) i

theorem rawSum_loss_mean (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (n : ℕ) :
    (law P p n).mean (fun hist ↦ R.rawSum loss n hist * pathLoss loss n hist) =
      -probingGain P p loss n := by
  have heq : (fun hist : History ι n ↦ R.rawSum loss n hist * pathLoss loss n hist) =
      (fun hist ↦ ∑ t ∈ Finset.range n, ∑ u ∈ Finset.range (n+1),
        transitionValue (R.score t (loss t)) n hist t * loss u (stateAt n hist u)) := by
    funext hist
    rw [R.rawSum_eq_sum]
    simp only [pathLoss, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [heq, ProbabilityVector.mean_sum]
  simp_rw [ProbabilityVector.mean_sum]
  calc
    (∑ t ∈ Finset.range n, ∑ u ∈ Finset.range (n+1), (law P p n).mean
        (fun hist ↦ transitionValue (R.score t (loss t)) n hist t * loss u (stateAt n hist u))) =
        ∑ t ∈ Finset.range n, ∑ u ∈ Finset.range (n+1),
          -(if t<u then FiniteKernel.weightedInner p (loss t)
            (fun i ↦ ((P.act)^[u-t-1]) (loss u) i - P.act (((P.act)^[u-t-1]) (loss u)) i) else 0) := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      exact R.score_loss_moment loss hloss n t u (Finset.mem_range.mp ht)
        (Nat.le_of_lt_succ (Finset.mem_range.mp hu))
    _ = -probingGain P p loss n := by
      simp only [probingGain, Finset.sum_neg_distrib]

theorem chunk_loss_response (R : ScoreRule F P p) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (M : ℝ) (hM : 1 ≤ M) (n : ℕ) :
    (R.tiltedLaw loss hloss M hM n).mean (pathLoss loss n) =
      p.mean (blockLoss loss (n+1)) - steeringStrength M * probingGain P p loss n +
        steeringStrength M * R.stopRemainder loss M n ∧
    |R.stopRemainder loss M n| ≤ ((n:ℝ)+1)^2 * R.stopProbability loss M n := by
  constructor
  · rw [R.tilted_mean_eq]
    have heq : (fun hist : History ι n ↦ R.likelihood loss M n hist * pathLoss loss n hist) =
        (fun hist ↦ pathLoss loss n hist + steeringStrength M *
          (R.stoppedSum loss M n hist * pathLoss loss n hist)) := by
      funext hist
      unfold likelihood
      ring
    rw [heq, ProbabilityVector.mean_add, ProbabilityVector.mean_const_mul,
      pathLoss_mean P p (P.reversible_stationary p R.reversible)]
    have hr : R.stopRemainder loss M n =
        (law P p n).mean (fun hist ↦ R.stoppedSum loss M n hist * pathLoss loss n hist) -
        (law P p n).mean (fun hist ↦ R.rawSum loss n hist * pathLoss loss n hist) := by
      unfold stopRemainder
      rw [← ProbabilityVector.mean_sub]
      congr 1
      funext hist
      ring
    rw [R.rawSum_loss_mean loss hloss n] at hr
    have hs : (law P p n).mean (fun hist ↦ R.stoppedSum loss M n hist * pathLoss loss n hist) =
        -probingGain P p loss n + R.stopRemainder loss M n := by linarith
    rw [hs]
    ring
  · exact R.stopRemainder_abs_le loss hloss M n

end ScoreRule
end
end Tournament.Upper

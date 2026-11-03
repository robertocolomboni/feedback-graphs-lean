module

public import Tournament.Probability.Correlations

@[expose] public section

namespace Tournament.FinitePath

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable section

def occupation (f : ι → ℝ) (n : ℕ) (hist : History ι n) : ℝ :=
  ∑ t ∈ Finset.range n, f (stateAt n hist t)

omit [Fintype ι] in
theorem occupation_step (f : ι → ℝ) (n : ℕ) (hist : History ι n × ι) :
    occupation f (n+1) hist = occupation f n hist.1 + f (lastState n hist.1) := by
  unfold occupation
  rw [Finset.sum_range_succ]
  have hprefix : (∑ t ∈ Finset.range n, f (stateAt (n+1) hist t)) =
      ∑ t ∈ Finset.range n, f (stateAt n hist.1 t) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [stateAt_prefix n hist t (Nat.le_of_lt (Finset.mem_range.mp ht))]
  rw [hprefix, stateAt_prefix n hist n le_rfl, stateAt_last]

theorem occupation_mean_step (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (f : ι → ℝ) (n : ℕ) :
    (law P μ (n+1)).mean (occupation f (n+1)) =
      (law P μ n).mean (occupation f n) + (law P μ n).mean (fun hist ↦ f (lastState n hist)) := by
  change ((law P μ n).joint (fun hist ↦ P.row (lastState n hist))).mean
    (fun hist : History ι n × ι ↦ occupation f (n+1) hist) = _
  have heq : (fun hist : History ι n × ι ↦ occupation f (n+1) hist) =
      (fun hist ↦ occupation f n hist.1 + f (lastState n hist.1)) := by
    funext hist
    exact occupation_step f n hist
  rw [heq, ProbabilityVector.mean_add,
    ProbabilityVector.joint_first_mean (law P μ n) (fun hist ↦ P.row (lastState n hist)) (occupation f n),
    ProbabilityVector.joint_first_mean (law P μ n) (fun hist ↦ P.row (lastState n hist))
      (fun hist ↦ f (lastState n hist))]

theorem latest_mean_step (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (f : ι → ℝ) (n : ℕ) :
    (law P μ (n+1)).mean (fun hist ↦ f (lastState (n+1) hist)) =
      (law P μ n).mean (fun hist ↦ P.act f (lastState n hist)) := by
  change ((law P μ n).joint (fun hist ↦ P.row (lastState n hist))).mean
    (fun hist : History ι n × ι ↦ f hist.2) = _
  rw [ProbabilityVector.joint_mean]
  rfl

theorem occupation_telescope (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (f g : ι → ℝ) (m : ℝ) (hpoisson : ∀ i, g i - P.act g i = f i - m) (n : ℕ) :
    (law P μ n).mean (occupation f n) =
      (n:ℝ)*m + μ.mean g - (law P μ n).mean (fun hist ↦ g (lastState n hist)) := by
  induction n with
  | zero =>
    have hzero : occupation f 0 = (fun _ : History ι 0 ↦ (0:ℝ)) := by
      funext hist
      simp [occupation]
    simp only [hzero, law, ProbabilityVector.mean_const, lastState, Nat.cast_zero, zero_mul]
    change (0:ℝ) = 0 + μ.mean g - μ.mean g
    ring
  | succ n ih =>
    rw [occupation_mean_step, ih, latest_mean_step]
    have heq : (fun hist : History ι n ↦ f (lastState n hist)) =
        (fun hist ↦ m + (g (lastState n hist) - P.act g (lastState n hist))) := by
      funext hist
      linarith [hpoisson (lastState n hist)]
    rw [heq, ProbabilityVector.mean_add, ProbabilityVector.mean_const, ProbabilityVector.mean_sub]
    push_cast
    ring

theorem occupation_mean_le (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (f g : ι → ℝ) (m lo hi : ℝ)
    (hpoisson : ∀ i, g i - P.act g i = f i - m)
    (hg : ∀ i, lo ≤ g i ∧ g i ≤ hi) (n : ℕ) :
    (law P μ n).mean (occupation f n) ≤ (n:ℝ)*m + hi-lo := by
  rw [occupation_telescope P μ f g m hpoisson]
  have hupper : μ.mean g ≤ hi := by
    calc
      μ.mean g ≤ μ.mean (fun _ ↦ hi) := μ.mean_mono (fun i ↦ (hg i).2)
      _ = hi := μ.mean_const hi
  have hlower : lo ≤ (law P μ n).mean (fun hist ↦ g (lastState n hist)) := by
    calc
      lo = (law P μ n).mean (fun _ ↦ lo) := ((law P μ n).mean_const lo).symm
      _ ≤ (law P μ n).mean (fun hist ↦ g (lastState n hist)) :=
        (law P μ n).mean_mono (fun hist ↦ (hg (lastState n hist)).1)
  linarith

end
end Tournament.FinitePath

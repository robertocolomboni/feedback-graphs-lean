module

public import Tournament.Probability.PrefixConditioning

@[expose] public section

namespace Tournament

open scoped BigOperators Classical

noncomputable section

namespace ProbabilityVector

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

theorem means_comm (μ : ProbabilityVector Ω) (ν : ProbabilityVector S) (f : Ω → S → ℝ) :
    μ.mean (fun x ↦ ν.mean (f x)) = ν.mean (fun y ↦ μ.mean (fun x ↦ f x y)) := by
  unfold mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end ProbabilityVector

namespace FinitePath

variable {ι : Type*} [Fintype ι]

def prepend (i : ι) : (n : ℕ) → History ι n → History ι (n+1)
  | 0, j => (i,j)
  | n+1, (hist,j) => (prepend i n hist,j)

def dropFirst : (n : ℕ) → History ι (n+1) → History ι n
  | 0, (_,j) => j
  | n+1, (hist,j) => (dropFirst n hist,j)

def firstState : (n : ℕ) → History ι n → ι
  | 0, i => i
  | n+1, (hist,_) => firstState n hist

def constantHistory (i : ι) : (n : ℕ) → History ι n
  | 0 => i
  | n+1 => (constantHistory i n,i)

omit [Fintype ι] in
theorem firstState_prepend (i : ι) (n : ℕ) (hist : History ι n) :
    firstState (n+1) (prepend i n hist) = i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih hist.1

omit [Fintype ι] in
theorem dropFirst_prepend (i : ι) (n : ℕ) (hist : History ι n) :
    dropFirst n (prepend i n hist) = hist := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (dropFirst n (prepend i n hist.1),hist.2) = hist
    rw [ih hist.1]

omit [Fintype ι] in
theorem prepend_first_drop (n : ℕ) (hist : History ι (n+1)) :
    prepend (firstState (n+1) hist) n (dropFirst n hist) = hist := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (prepend (firstState (n+1) hist.1) n (dropFirst n hist.1),hist.2) = hist
    rw [ih hist.1]

omit [Fintype ι] in
theorem lastState_prepend (i : ι) (n : ℕ) (hist : History ι n) :
    lastState (n+1) (prepend i n hist) = lastState n hist := by
  cases n <;> rfl

omit [Fintype ι] in
theorem prepend_constant (i : ι) (n : ℕ) :
    prepend i n (constantHistory i n) = constantHistory i (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (prepend i n (constantHistory i n),i) = (constantHistory i (n+1),i)
    rw [ih]

theorem law_first_mean (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (n : ℕ) (f : History ι (n+1) → ℝ) :
    (law P μ (n+1)).mean f = μ.mean (fun i ↦ (law P (P.row i) n).mean (fun hist ↦ f (prepend i n hist))) := by
  induction n with
  | zero =>
    exact ProbabilityVector.joint_mean μ (fun i ↦ P.row i) f
  | succ n ih =>
    change ((law P μ (n+1)).joint (fun hist ↦ P.row (lastState (n+1) hist))).mean f = _
    rw [ProbabilityVector.joint_mean, ih]
    congr 1
    funext i
    change (law P (P.row i) n).mean (fun hist ↦ (P.row (lastState (n+1) (prepend i n hist))).mean
      (fun j ↦ f (prepend i n hist,j))) =
      ((law P (P.row i) n).joint (fun hist ↦ P.row (lastState n hist))).mean
        (fun hist : History ι n × ι ↦ f (prepend i (n+1) hist))
    rw [ProbabilityVector.joint_mean]
    simp only [lastState_prepend, prepend]

theorem law_mean_initial_state (P : FiniteKernel ι) (μ : ProbabilityVector ι)
    (n : ℕ) (f : History ι n → ℝ) :
    (law P μ n).mean f = μ.mean (fun i ↦ (law P (ProbabilityVector.pure i) n).mean f) := by
  induction n with
  | zero =>
    change μ.mean f = μ.mean (fun i ↦ (ProbabilityVector.pure i).mean f)
    simp only [ProbabilityVector.pure_mean]
  | succ n ih =>
    change ((law P μ n).joint (fun hist ↦ P.row (lastState n hist))).mean f = _
    rw [ProbabilityVector.joint_mean, ih]
    congr 1
    funext i
    exact (ProbabilityVector.joint_mean (law P (ProbabilityVector.pure i) n)
      (fun hist ↦ P.row (lastState n hist)) f).symm

end FinitePath
end
end Tournament

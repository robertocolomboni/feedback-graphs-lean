module

public import Tournament.Probability.FinitePath
public import Mathlib.Logic.Function.Iterate
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Tournament.FinitePath

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable section

def transitionValue (d : ι → ι → ℝ) (n : ℕ) (hist : History ι n) (t : ℕ) : ℝ :=
  d (stateAt n hist t) (stateAt n hist (t+1))

omit [Fintype ι] in
theorem transitionValue_prefix (d : ι → ι → ℝ) (n : ℕ)
    (hist : History ι n × ι) (t : ℕ) (ht : t < n) :
    transitionValue d (n+1) hist t = transitionValue d n hist.1 t := by
  unfold transitionValue
  rw [stateAt_prefix n hist t (by omega), stateAt_prefix n hist (t+1) (by omega)]

omit [Fintype ι] in
theorem transitionValue_last (d : ι → ι → ℝ) (n : ℕ) (hist : History ι n × ι) :
    transitionValue d (n+1) hist n = d (lastState n hist.1) hist.2 := by
  unfold transitionValue
  rw [stateAt_prefix n hist n le_rfl, stateAt_last, stateAt_last]
  rfl

theorem transition_past_mean_zero (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (d : ι → ι → ℝ) (hd : ∀ i, (P.row i).mean (d i) = 0)
    (n t u : ℕ) (ht : t < n) (hu : u ≤ t) (f : ι → ℝ) :
    (law P p n).mean (fun hist ↦ transitionValue d n hist t * f (stateAt n hist u)) = 0 := by
  induction n generalizing t u with
  | zero => omega
  | succ n ih =>
    by_cases htn : t < n
    · have hun : u ≤ n := by omega
      change ((law P p n).joint (fun hist ↦ P.row (lastState n hist))).mean
        (fun hist : History ι n × ι ↦ transitionValue d (n+1) hist t * f (stateAt (n+1) hist u)) = 0
      have heq : (fun hist : History ι n × ι ↦
          transitionValue d (n+1) hist t * f (stateAt (n+1) hist u)) =
          (fun hist ↦ transitionValue d n hist.1 t * f (stateAt n hist.1 u)) := by
        funext hist
        rw [transitionValue_prefix d n hist t htn, stateAt_prefix n hist u hun]
      rw [heq, ProbabilityVector.joint_first_mean (law P p n)
        (fun hist ↦ P.row (lastState n hist))
        (fun hist ↦ transitionValue d n hist t * f (stateAt n hist u))]
      exact ih t u htn hu
    · have ht' : t = n := by omega
      subst t
      change ((law P p n).joint (fun hist ↦ P.row (lastState n hist))).mean _ = 0
      rw [ProbabilityVector.joint_mean]
      have heq : (fun hist : History ι n ↦ (P.row (lastState n hist)).mean
          (fun j ↦ transitionValue d (n+1) (hist,j) n * f (stateAt (n+1) (hist,j) u))) =
          (fun _ ↦ (0:ℝ)) := by
        funext hist
        simp only [transitionValue_last, stateAt_prefix n (hist, _) u hu]
        rw [ProbabilityVector.mean_mul_const, hd, zero_mul]
      rw [heq, ProbabilityVector.mean_const]

theorem transition_future_mean (P : FiniteKernel ι) (p : ProbabilityVector ι)
    (hstat : P.Stationary p) (d : ι → ι → ℝ)
    (n t u : ℕ) (htu : t < u) (hun : u ≤ n) (f : ι → ℝ) :
    (law P p n).mean (fun hist ↦ transitionValue d n hist t * f (stateAt n hist u)) =
      P.edgeSum p (fun i j ↦ d i j * ((P.act)^[u-t-1]) f j) := by
  induction n generalizing t u f with
  | zero => omega
  | succ n ih =>
    by_cases hun' : u ≤ n
    · have htn : t < n := by omega
      change ((law P p n).joint (fun hist ↦ P.row (lastState n hist))).mean
        (fun hist : History ι n × ι ↦ transitionValue d (n+1) hist t * f (stateAt (n+1) hist u)) = _
      have heq : (fun hist : History ι n × ι ↦
          transitionValue d (n+1) hist t * f (stateAt (n+1) hist u)) =
          (fun hist ↦ transitionValue d n hist.1 t * f (stateAt n hist.1 u)) := by
        funext hist
        rw [transitionValue_prefix d n hist t htn, stateAt_prefix n hist u hun']
      rw [heq, ProbabilityVector.joint_first_mean (law P p n)
        (fun hist ↦ P.row (lastState n hist))
        (fun hist ↦ transitionValue d n hist t * f (stateAt n hist u))]
      exact ih t u htu hun' f
    · have hu' : u = n+1 := by omega
      subst u
      by_cases htn : t < n
      · change ((law P p n).joint (fun hist ↦ P.row (lastState n hist))).mean _ = _
        rw [ProbabilityVector.joint_mean]
        have heq : (fun hist : History ι n ↦ (P.row (lastState n hist)).mean
            (fun j ↦ transitionValue d (n+1) (hist,j) t * f (stateAt (n+1) (hist,j) (n+1)))) =
            (fun hist ↦ transitionValue d n hist t * P.act f (stateAt n hist n)) := by
          funext hist
          simp only [transitionValue_prefix d n (hist, _) t htn, stateAt_last,
            lastState, ProbabilityVector.mean_const_mul]
          rfl
        rw [heq, ih t n htn le_rfl (P.act f)]
        have hexp : n+1-t-1 = (n-t-1)+1 := by omega
        rw [hexp, Function.iterate_succ_apply]
      · have ht' : t = n := by omega
        subst t
        change ((law P p n).joint (fun hist ↦ P.row (lastState n hist))).mean _ = _
        rw [ProbabilityVector.joint_mean]
        have heq : (fun hist : History ι n ↦ (P.row (lastState n hist)).mean
            (fun j ↦ transitionValue d (n+1) (hist,j) n * f (stateAt (n+1) (hist,j) (n+1)))) =
            (fun hist ↦ (P.row (lastState n hist)).mean (fun j ↦ d (lastState n hist) j * f j)) := by
          funext hist
          simp only [transitionValue_last, stateAt_last, lastState]
        rw [heq, stationary_latest_mean P p hstat n
          (fun i ↦ (P.row i).mean (fun j ↦ d i j * f j))]
        simp only [Nat.add_sub_cancel_left, Nat.sub_self, Function.iterate_zero, id_eq]
        unfold ProbabilityVector.mean FiniteKernel.edgeSum FiniteKernel.row
        simp only [Finset.mul_sum, mul_assoc]

end
end Tournament.FinitePath

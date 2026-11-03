module

public import Tournament.Upper.ExplorationEstimator

@[expose] public section

namespace Tournament.Upper.Exploration

open scoped Classical BigOperators

noncomputable section

variable {ι : Type*}

def played (D : Finset ι) (arm : ι) (q : Bool × D) : ι := if q.1 then q.2.val else arm

def explorationCount (D : Finset ι) (T : ℕ) (q : ℕ → Bool × D) : ℕ :=
  ∑ t ∈ Finset.range T, if (q t).1 then 1 else 0

theorem played_loss_le (D : Finset ι) (loss : ι → ℝ) (hloss : BoundedLoss loss)
    (arm : ι) (q : Bool × D) :
    loss (played D arm q)≤loss arm+(if q.1 then (1:ℝ) else 0) := by
  rcases q with ⟨b,s⟩
  cases b
  · simp only [played,Bool.false_eq_true,ite_false,add_zero,le_refl]
  · simp only [played,ite_true]
    linarith [(hloss s.val).2,(hloss arm).1]

theorem played_switches_le (D : Finset ι) (T : ℕ) (arms : ℕ → ι) (q : ℕ → Bool × D) :
    Model.switchCount T (fun t ↦ played D (arms t) (q t))≤
      Model.switchCount T arms+2*explorationCount D T q := by
  cases T with
  | zero => simp [Model.switchCount,explorationCount]
  | succ n =>
    let c : ℕ → ℕ := fun t ↦ if (q t).1 then 1 else 0
    have hStep (t : ℕ) :
        (if played D (arms (t+1)) (q (t+1))=played D (arms t) (q t) then (0:ℕ) else 1)≤
          (if arms (t+1)=arms t then 0 else 1)+c t+c (t+1) := by
      cases hb : (q t).1 <;> cases hb' : (q (t+1)).1 <;>
        simp [played,c,hb,hb'] <;> split_ifs <;> omega
    have hFirst : (∑ t ∈ Finset.range n, c t)≤∑ t ∈ Finset.range (n+1), c t :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ n))
    have hLast : (∑ t ∈ Finset.range n, c (t+1))≤∑ t ∈ Finset.range (n+1), c t := by
      rw [Finset.sum_range_succ' c n]
      omega
    have hSum := Finset.sum_le_sum (s := Finset.range n) (fun t _ ↦ hStep t)
    simp only [Finset.sum_add_distrib] at hSum
    change (∑ t ∈ Finset.range n,
      if played D (arms (t+1)) (q (t+1))=played D (arms t) (q t) then (0:ℕ) else 1)≤
      (∑ t ∈ Finset.range n, if arms (t+1)=arms t then 0 else 1)+
        2*(∑ t ∈ Finset.range (n+1), c t)
    omega

theorem played_accumulatedLoss_le (D : Finset ι) (T : ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (arms : ℕ → ι) (q : ℕ → Bool × D) :
    Model.accumulatedLoss T loss (fun t ↦ played D (arms t) (q t))≤
      Model.accumulatedLoss T loss arms+(explorationCount D T q : ℝ) := by
  calc
    _ ≤ ∑ t ∈ Finset.range T, (loss t (arms t)+(if (q t).1 then (1:ℝ) else 0)) :=
      Finset.sum_le_sum (fun t _ ↦ played_loss_le D (loss t) (hloss t) (arms t) (q t))
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [explorationCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]

variable [Fintype ι] [Nonempty ι]

theorem played_regret_le (D : Finset ι) (T : ℕ) (loss : ℕ → ι → ℝ)
    (hloss : ∀ t, BoundedLoss (loss t)) (arms : ℕ → ι) (q : ℕ → Bool × D) :
    Model.pathRegret T loss (fun t ↦ played D (arms t) (q t))≤
      Model.pathRegret T loss arms+3*(explorationCount D T q : ℝ) := by
  have hLoss := played_accumulatedLoss_le D T loss hloss arms q
  have hSwitch : (Model.switchCount T (fun t ↦ played D (arms t) (q t)) : ℝ)≤
      (Model.switchCount T arms : ℝ)+2*(explorationCount D T q : ℝ) := by
    exact_mod_cast played_switches_le D T arms q
  unfold Model.pathRegret
  linarith

end
end Tournament.Upper.Exploration

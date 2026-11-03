module

public import Tournament.Upper.ExplorationTuning
public import Tournament.Probability.ProcessConditional

@[expose] public section

namespace Tournament.Upper.Exploration

open scoped Classical BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

abbrev RoundOutcome (D : Finset ι) := ι × (Bool × D)
abbrev History (D : Finset ι) := FiniteProcess.History (fun _ ↦ RoundOutcome D)

def processWeights (E : ι → ι → Prop) (D : Finset ι) (κ η : ℝ) (loss : ℕ → ι → ℝ) :
    (n : ℕ) → History D n → ProbabilityVector ι
  | 0, _ => ExponentialWeights.uniform
  | n+1, h => Model.exponentialUpdate (processWeights E D κ η loss n h.1) η
      (estimate E D κ (loss n) h.2.2)

def latentRow (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) :
    (n : ℕ) → History D n → ProbabilityVector ι
  | 0, _ => ExponentialWeights.uniform
  | n+1, h => (ShrinkingDartboard.kernel (processWeights E D κ η loss n h.1) η hη
      (estimate E D κ (loss n) h.2.2) (estimate_nonneg E D κ hκ (loss n) (hloss n) h.2.2)).row h.2.1

def roundKernel (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (n : ℕ) (h : History D n) : ProbabilityVector (RoundOutcome D) :=
  (latentRow E D κ hκ η hη loss hloss n h).joint (fun _ ↦ law D κ hκ hκ1)

def execution (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T : ℕ) : ProbabilityVector (History D T) :=
  FiniteProcess.law (roundKernel E D κ hκ hκ1 η hη loss hloss) T

def actions (D : Finset ι) (default : ι) (T : ℕ) (h : History D T) (t : ℕ) : ι :=
  if ht : t<T then
    let r := (FiniteProcess.past (t+1) T (by omega) h).2
    played D r.1 r.2
  else default

theorem roundKernel_first_mean (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (n : ℕ) (h : History D n) (f : ι → ℝ) :
    (roundKernel E D κ hκ hκ1 η hη loss hloss n h).mean (fun r ↦ f r.1)=
      (latentRow E D κ hκ η hη loss hloss n h).mean f := ProbabilityVector.joint_first_mean _ _ f

theorem roundKernel_estimate_mean (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (n : ℕ) (h : History D n) (i : ι) :
    (roundKernel E D κ hκ.le hκ1 η hη loss hloss n h).mean
      (fun r ↦ estimate E D κ (loss n) r.2 i)=loss n i := by
  rw [roundKernel,ProbabilityVector.joint_mean]
  simp_rw [estimate_mean E D hD κ hκ hκ1 (loss n)]
  exact ProbabilityVector.mean_const _ _

theorem roundKernel_weighted_mean (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (n : ℕ) (h : History D n) :
    (roundKernel E D κ hκ.le hκ1 η hη loss hloss n h).mean
      (fun r ↦ (processWeights E D κ η loss n h).mean (estimate E D κ (loss n) r.2))=
      (processWeights E D κ η loss n h).mean (loss n) := by
  rw [roundKernel,ProbabilityVector.joint_mean]
  simp_rw [weighted_estimate_mean E D hD κ hκ hκ1 (loss n)]
  exact ProbabilityVector.mean_const _ _

theorem roundKernel_selected_estimate_mean (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (n : ℕ) (h : History D n) :
    (roundKernel E D κ hκ.le hκ1 η hη loss hloss n h).mean
      (fun r ↦ estimate E D κ (loss n) r.2 r.1)=
      (latentRow E D κ hκ.le η hη loss hloss n h).mean (loss n) := by
  rw [roundKernel,ProbabilityVector.joint_mean]
  simp_rw [estimate_mean E D hD κ hκ hκ1 (loss n)]

omit [Nonempty ι] in
theorem nextWeights_observable (E : ι → ι → Prop) (D : Finset ι) (κ η : ℝ)
    (p : ProbabilityVector ι) (loss : ι → ℝ) (r : RoundOutcome D) :
    Model.exponentialUpdate p η (estimate E D κ (Model.graphObservation E (played D r.1 r.2) loss) r.2)=
      Model.exponentialUpdate p η (estimate E D κ loss r.2) := by
  congr 1
  funext i
  exact estimate_observable E D κ loss r.2 r.1 i

def explorationAt (D : Finset ι) [Nonempty D] (T : ℕ) (h : History D T) (t : ℕ) : Bool × D :=
  if ht : t<T then (FiniteProcess.past (t+1) T (by omega) h).2.2
  else (false,Classical.choice (inferInstance : Nonempty D))

def latentAt (D : Finset ι) (default : ι) (T : ℕ) (h : History D T) (t : ℕ) : ι :=
  if ht : t<T then (FiniteProcess.past (t+1) T (by omega) h).2.1 else default

omit [Fintype ι] [Nonempty ι] in
theorem actions_eq_played (D : Finset ι) [Nonempty D] (default : ι) (T : ℕ) (h : History D T) :
    actions D default T h=fun t ↦ played D (latentAt D default T h t) (explorationAt D T h t) := by
  funext t
  by_cases ht : t<T <;> simp [actions,latentAt,explorationAt,ht,played]

omit [Fintype ι] [Nonempty ι] in
theorem exploration_indicator_mean (D : Finset ι) [Nonempty D] (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) :
    (law D κ hκ hκ1).mean (fun q ↦ if q.1 then (1:ℝ) else 0)=κ := by
  rw [law,ProbabilityVector.joint_mean,Restarts.coin_mean]
  simp only [ite_true,Bool.false_eq_true,ite_false,ProbabilityVector.mean_const,mul_one,mul_zero,add_zero]

theorem expected_exploration_count (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T : ℕ) :
    (execution E D κ hκ hκ1 η hη loss hloss T).mean
      (fun x ↦ (explorationCount D T (explorationAt D T x) : ℝ))=κ*(T:ℝ) := by
  let row := roundKernel E D κ hκ hκ1 η hη loss hloss
  have hStep (t : ℕ) (ht : t∈Finset.range T) :
      (execution E D κ hκ hκ1 η hη loss hloss T).mean
        (fun x ↦ if (explorationAt D T x t).1 then (1:ℝ) else 0)=κ := by
    have htT : t<T := Finset.mem_range.mp ht
    let f : History D (t+1) → ℝ := fun s ↦ if s.2.2.1 then 1 else 0
    have heq : (fun x : History D T ↦ if (explorationAt D T x t).1 then (1:ℝ) else 0)=
        fun x ↦ f (FiniteProcess.past (t+1) T (by omega) x) := by
      funext x
      simp only [explorationAt,dite_eq_left htT]
      rfl
    rw [heq]
    change (FiniteProcess.law row T).mean _=κ
    rw [FiniteProcess.mean_prefix row (t+1) T (by omega),FiniteProcess.law,ProbabilityVector.joint_mean]
    change (FiniteProcess.law row t).mean (fun s ↦
      ((latentRow E D κ hκ η hη loss hloss t s).joint (fun _ ↦ law D κ hκ hκ1)).mean
        (fun r ↦ if r.2.1 then (1:ℝ) else 0))=κ
    simp only [ProbabilityVector.joint_mean,exploration_indicator_mean,ProbabilityVector.mean_const]
  have hCast (x : History D T) : (explorationCount D T (explorationAt D T x) : ℝ)=
      ∑ t∈Finset.range T, if (explorationAt D T x t).1 then (1:ℝ) else 0 := by
    simp only [explorationCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp_rw [hCast]
  rw [ProbabilityVector.mean_sum]
  calc
    _ = ∑ _t∈Finset.range T, κ := Finset.sum_congr rfl hStep
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

theorem expected_exploration_regret_transfer (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, BoundedLoss (loss n)) (T : ℕ) (default : ι) :
    (execution E D κ hκ hκ1 η hη loss (fun n i ↦ (hloss n i).1) T).mean
      (fun x ↦ Model.pathRegret T loss (actions D default T x))≤
    (execution E D κ hκ hκ1 η hη loss (fun n i ↦ (hloss n i).1) T).mean
      (fun x ↦ Model.pathRegret T loss (latentAt D default T x))+3*κ*(T:ℝ) := by
  let μ := execution E D κ hκ hκ1 η hη loss (fun n i ↦ (hloss n i).1) T
  calc
    _ ≤ μ.mean (fun x ↦ Model.pathRegret T loss (latentAt D default T x)+
        3*(explorationCount D T (explorationAt D T x) : ℝ)) := by
      apply μ.mean_mono
      intro x
      rw [actions_eq_played]
      exact played_regret_le D T loss hloss (latentAt D default T x) (explorationAt D T x)
    _ = _ := by
      rw [ProbabilityVector.mean_add,ProbabilityVector.mean_const_mul,
        expected_exploration_count E D κ hκ hκ1 η hη loss (fun n i ↦ (hloss n i).1) T]
      ring

end
end Tournament.Upper.Exploration

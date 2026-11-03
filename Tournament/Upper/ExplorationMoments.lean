module

public import Tournament.Upper.ExplorationHypotheses

@[expose] public section

namespace Tournament.Upper.Exploration

open ShrinkingDartboard
open scoped Classical BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem mean_round (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (T t : ℕ) (ht : t<T) (f : History D (t+1) → ℝ) :
    (execution E D κ hκ hκ1 η hη loss hloss T).mean
      (fun x ↦ f (FiniteProcess.past (t+1) T (by omega) x))=
    (execution E D κ hκ hκ1 η hη loss hloss t).mean
      (fun s ↦ (roundKernel E D κ hκ hκ1 η hη loss hloss t s).mean (fun r ↦ f (s,r))) := by
  unfold execution
  rw [FiniteProcess.mean_prefix _ (t+1) T (by omega),FiniteProcess.law,ProbabilityVector.joint_mean]

theorem randomWeights_execution (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ) (η : ℝ)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (T t : ℕ) (ht : t≤T) (x : History D T) :
    randomWeights η (estimatesOnExecution E D κ hκ loss hloss T) t x=
      processWeights E D κ η loss t (FiniteProcess.past t T ht x) := by
  unfold randomWeights
  rw [← historyWeights_eq_weights,estimateHistory_execution E D κ hκ loss hloss T t ht,
    historyWeights_estimateHistory]

theorem mean_estimate_selected (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (T t : ℕ) (ht : t<T) (default : ι) :
    (execution E D κ hκ.le hκ1 η hη loss hloss T).mean (fun x ↦
      (estimatesOnExecution E D κ hκ.le loss hloss T t x (latentAt D default T x t) : ℝ))=
    (execution E D κ hκ.le hκ1 η hη loss hloss T).mean (fun x ↦ loss t (latentAt D default T x t)) := by
  let fEst : History D (t+1) → ℝ := fun h ↦ estimate E D κ (loss t) h.2.2 h.2.1
  let fTrue : History D (t+1) → ℝ := fun h ↦ loss t h.2.1
  have hEst : (fun x : History D T ↦
      (estimatesOnExecution E D κ hκ.le loss hloss T t x (latentAt D default T x t) : ℝ))=
      fun x ↦ fEst (FiniteProcess.past (t+1) T (by omega) x) := by
    funext x
    simp only [estimatesOnExecution,latentAt,dite_eq_left ht]
    rfl
  have hTrue : (fun x : History D T ↦ loss t (latentAt D default T x t))=
      fun x ↦ fTrue (FiniteProcess.past (t+1) T (by omega) x) := by
    funext x
    simp only [latentAt,dite_eq_left ht]
    rfl
  rw [hEst,hTrue,mean_round E D κ hκ.le hκ1 η hη loss hloss T t ht fEst,
    mean_round E D κ hκ.le hκ1 η hη loss hloss T t ht fTrue]
  apply congrArg (ProbabilityVector.mean (execution E D κ hκ.le hκ1 η hη loss hloss t))
  funext s
  exact (roundKernel_selected_estimate_mean E D hD κ hκ hκ1 η hη loss hloss t s).trans
    (roundKernel_first_mean E D κ hκ.le hκ1 η hη loss hloss t s (loss t)).symm

theorem mean_estimate_coordinate (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (T t : ℕ) (ht : t<T) (i : ι) :
    (execution E D κ hκ.le hκ1 η hη loss hloss T).mean
      (fun x ↦ (estimatesOnExecution E D κ hκ.le loss hloss T t x i : ℝ))=loss t i := by
  let f : History D (t+1) → ℝ := fun h ↦ estimate E D κ (loss t) h.2.2 i
  have heq : (fun x : History D T ↦ (estimatesOnExecution E D κ hκ.le loss hloss T t x i : ℝ))=
      fun x ↦ f (FiniteProcess.past (t+1) T (by omega) x) := by
    funext x
    simp only [estimatesOnExecution,dite_eq_left ht]
    rfl
  rw [heq,mean_round E D κ hκ.le hκ1 η hη loss hloss T t ht f]
  change (execution E D κ hκ.le hκ1 η hη loss hloss t).mean
    (fun s ↦ (roundKernel E D κ hκ.le hκ1 η hη loss hloss t s).mean
      (fun r ↦ estimate E D κ (loss t) r.2 i))=_
  simp only [roundKernel_estimate_mean E D hD κ hκ hκ1 η hη loss hloss,ProbabilityVector.mean_const]

omit [Fintype ι] [Nonempty ι] in
theorem prefix_first (D : Finset ι) (T t : ℕ) (ht : t<T) (x : History D T) :
    (FiniteProcess.past (t+1) T (by omega) x).1=FiniteProcess.past t T ht.le x := by
  have h := FiniteProcess.past_comp t (t+1) T (by omega) (by omega) x
  simpa only [FiniteProcess.past_succ t t le_rfl,FiniteProcess.past_self] using h

theorem mean_weighted_estimate_le_one (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, BoundedLoss (loss n))
    (T t : ℕ) (ht : t<T) :
    let g := estimatesOnExecution E D κ hκ.le loss (fun n i ↦ (hloss n i).1) T
    (execution E D κ hκ.le hκ1 η hη loss (fun n i ↦ (hloss n i).1) T).mean
      (fun x ↦ (randomWeights η g t x).mean (fun i ↦ (g t x i : ℝ)))≤1 := by
  let hn := fun n i ↦ (hloss n i).1
  let f : History D (t+1) → ℝ := fun h ↦ (processWeights E D κ η loss t h.1).mean
    (estimate E D κ (loss t) h.2.2)
  have heq : (fun x : History D T ↦
      (randomWeights η (estimatesOnExecution E D κ hκ.le loss hn T) t x).mean
        (fun i ↦ (estimatesOnExecution E D κ hκ.le loss hn T t x i : ℝ)))=
      fun x ↦ f (FiniteProcess.past (t+1) T (by omega) x) := by
    funext x
    rw [randomWeights_execution E D κ hκ.le η loss hn T t ht.le x,← prefix_first D T t ht x]
    simp only [estimatesOnExecution,dite_eq_left ht]
    rfl
  dsimp only
  rw [heq,mean_round E D κ hκ.le hκ1 η hη loss hn T t ht f]
  calc
    _ = (execution E D κ hκ.le hκ1 η hη loss hn t).mean
        (fun s ↦ (processWeights E D κ η loss t s).mean (loss t)) := by
      apply congrArg (ProbabilityVector.mean _)
      funext s
      exact roundKernel_weighted_mean E D hD κ hκ hκ1 η hη loss hn t s
    _ ≤ (execution E D κ hκ.le hκ1 η hη loss hn t).mean (fun _ ↦ 1) := by
      apply ProbabilityVector.mean_mono
      intro s
      exact ((processWeights E D κ η loss t s).mean_mono (fun i ↦ (hloss t i).2)).trans_eq
        ((processWeights E D κ η loss t s).mean_const 1)
    _ = _ := ProbabilityVector.mean_const _ _

theorem mean_weighted_secondMoment_le (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, BoundedLoss (loss n))
    (T t : ℕ) (ht : t<T) :
    let g := estimatesOnExecution E D κ hκ.le loss (fun n i ↦ (hloss n i).1) T
    (execution E D κ hκ.le hκ1 η hη loss (fun n i ↦ (hloss n i).1) T).mean
      (fun x ↦ (randomWeights η g t x).squareNorm (fun i ↦ (g t x i : ℝ)))≤(D.card:ℝ)/κ := by
  let hn := fun n i ↦ (hloss n i).1
  let f : History D (t+1) → ℝ := fun h ↦ (processWeights E D κ η loss t h.1).squareNorm
    (estimate E D κ (loss t) h.2.2)
  have heq : (fun x : History D T ↦
      (randomWeights η (estimatesOnExecution E D κ hκ.le loss hn T) t x).squareNorm
        (fun i ↦ (estimatesOnExecution E D κ hκ.le loss hn T t x i : ℝ)))=
      fun x ↦ f (FiniteProcess.past (t+1) T (by omega) x) := by
    funext x
    rw [randomWeights_execution E D κ hκ.le η loss hn T t ht.le x,← prefix_first D T t ht x]
    simp only [estimatesOnExecution,dite_eq_left ht]
    rfl
  dsimp only
  rw [heq,mean_round E D κ hκ.le hκ1 η hη loss hn T t ht f]
  calc
    _ ≤ (execution E D κ hκ.le hκ1 η hη loss hn t).mean (fun _ ↦ (D.card:ℝ)/κ) := by
      apply ProbabilityVector.mean_mono
      intro s
      change ((latentRow E D κ hκ.le η hη loss hn t s).joint (fun _ ↦ law D κ hκ.le hκ1)).mean
        (fun r ↦ (processWeights E D κ η loss t s).squareNorm (estimate E D κ (loss t) r.2))≤_
      rw [ProbabilityVector.joint_mean]
      change (latentRow E D κ hκ.le η hη loss hn t s).mean (fun _ ↦
        (law D κ hκ.le hκ1).mean (fun q ↦ (processWeights E D κ η loss t s).squareNorm (estimate E D κ (loss t) q)))≤_
      rw [ProbabilityVector.mean_const]
      exact weighted_estimate_secondMoment_le E D hD κ hκ hκ1 (loss t) (hloss t) _
    _ = _ := ProbabilityVector.mean_const _ _

end
end Tournament.Upper.Exploration

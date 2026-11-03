module

public import Tournament.Upper.ExplorationHistories
public import Tournament.Upper.DartboardFiniteHorizon

@[expose] public section

namespace Tournament.Upper.Exploration

open MeasureTheory ProbabilityTheory ShrinkingDartboard
open scoped Classical

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

def estimateVector (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (loss : ι → ℝ) (hloss : ∀ i, 0≤loss i) (q : Bool × D) : LossVector ι :=
  fun i ↦ ⟨estimate E D κ loss q i,estimate_nonneg E D κ hκ loss hloss q i⟩

def estimateLaw (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (loss : ι → ℝ) (hloss : ∀ i, 0≤loss i) : Measure (LossVector ι) :=
  (law D κ hκ hκ1).toMeasure.map (estimateVector E D κ hκ loss hloss)

instance estimateLaw_probability (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (loss : ι → ℝ) (hloss : ∀ i, 0≤loss i) :
    IsProbabilityMeasure (estimateLaw E D κ hκ hκ1 loss hloss) := by
  unfold estimateLaw
  infer_instance

theorem fresh_estimate_conditional (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T n : ℕ) (hn : n<T) (default : ι) :
    HasCondDistrib (estimatesOnExecution E D κ hκ loss hloss T n)
      (fun x ↦ (lossHistory (estimatesOnExecution E D κ hκ loss hloss T) n x,latentAt D default T x n))
      (Kernel.const (LossHistory ι n × ι) (estimateLaw E D κ hκ hκ1 (loss n) (hloss n)))
      (execution E D κ hκ hκ1 η hη loss hloss T).toMeasure := by
  let f : History D n × ι → LossHistory ι n × ι := fun q ↦
    (estimateHistory E D κ hκ loss hloss n q.1,q.2)
  have hFull := fresh_exploration_conditional E D κ hκ hκ1 η hη loss hloss n T (by omega)
  have hQ : HasCondDistrib (fun x ↦ (FiniteProcess.past (n+1) T (by omega) x).2.2)
      (f ∘ (fun x ↦ ((FiniteProcess.past (n+1) T (by omega) x).1,
        (FiniteProcess.past (n+1) T (by omega) x).2.1)))
      (Kernel.const (LossHistory ι n × ι) (law D κ hκ hκ1).toMeasure)
      (execution E D κ hκ hκ1 η hη loss hloss T).toMeasure :=
    HasCondDistrib.comp_right (hf := measurable_of_finite f) hFull
  have hInfo : f ∘ (fun x : History D T ↦ ((FiniteProcess.past (n+1) T (by omega) x).1,
      (FiniteProcess.past (n+1) T (by omega) x).2.1))=
      (fun x ↦ (lossHistory (estimatesOnExecution E D κ hκ loss hloss T) n x,latentAt D default T x n)) := by
    funext x
    have hPrefix : (FiniteProcess.past (n+1) T (by omega) x).1=FiniteProcess.past n T (by omega) x := by
      have hc := FiniteProcess.past_comp n (n+1) T (by omega) (by omega) x
      simpa only [FiniteProcess.past_succ n n le_rfl,FiniteProcess.past_self] using hc
    simp only [Function.comp_def,f,latentAt,dite_eq_left hn,estimateHistory_execution E D κ hκ loss hloss T n hn.le,hPrefix]
  rw [hInfo] at hQ
  have h := hQ.comp_left (measurable_of_finite (estimateVector E D κ hκ (loss n) (hloss n)))
  rw [Kernel.map_const _ (measurable_of_finite (estimateVector E D κ hκ (loss n) (hloss n)))] at h
  have hEst : estimatesOnExecution E D κ hκ loss hloss T n=
      fun x ↦ estimateVector E D κ hκ (loss n) (hloss n) (FiniteProcess.past (n+1) T (by omega) x).2.2 := by
    funext x
    simp only [estimatesOnExecution,dite_eq_left hn]
    rfl
  rw [hEst]
  exact h

theorem independent_estimate_latent (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T n : ℕ) (hn : n<T) (default : ι) :
    let μ := (execution E D κ hκ hκ1 η hη loss hloss T).toMeasure
    let g := estimatesOnExecution E D κ hκ loss hloss T
    let I := fun n x ↦ latentAt D default T x n
    HasCondDistrib (fun x ↦ (g n x,I n x)) (lossHistory g n)
      (Kernel.const (LossHistory ι n) (estimateLaw E D κ hκ hκ1 (loss n) (hloss n)) ×ₖ
        condDistrib (I n) (lossHistory g n) μ) μ := by
  dsimp only
  have hArm : HasCondDistrib (fun x ↦ latentAt D default T x n)
      (lossHistory (estimatesOnExecution E D κ hκ loss hloss T) n)
      (condDistrib (fun x ↦ latentAt D default T x n)
        (lossHistory (estimatesOnExecution E D κ hκ loss hloss T) n)
        (execution E D κ hκ hκ1 η hη loss hloss T).toMeasure)
      (execution E D κ hκ hκ1 η hη loss hloss T).toMeasure :=
    ⟨(measurable_of_finite _).aemeasurable,
      (compProd_map_condDistrib (measurable_of_finite _).aemeasurable
        (measurable_of_finite _).aemeasurable).symm⟩
  exact Tournament.Probability.conditional_product_of_fresh _ hArm
    (fresh_estimate_conditional E D κ hκ hκ1 η hη loss hloss T n hn default)

theorem initial_latent_law (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T : ℕ) (hT : 1≤T) (default : ι) :
    HasLaw (fun x ↦ latentAt D default T x 0) ExponentialWeights.uniform.toMeasure
      (execution E D κ hκ hκ1 η hη loss hloss T).toMeasure := by
  apply ProbabilityVector.hasLaw_of_mean
  intro f
  have h0 : 0<T := by omega
  let row := roundKernel E D κ hκ hκ1 η hη loss hloss
  calc
    _ = (FiniteProcess.law row 1).mean (fun h ↦ f h.2.1) := by
      simpa only [latentAt,dite_eq_left h0,execution,row] using
        FiniteProcess.mean_prefix row 1 T hT (fun h ↦ f h.2.1)
    _ = _ := by
      rw [FiniteProcess.law,ProbabilityVector.joint_mean]
      change (FiniteProcess.initial (Y := fun _ ↦ RoundOutcome D)).mean
        (fun _ ↦ (ExponentialWeights.uniform.joint (fun _ ↦ law D κ hκ hκ1)).mean (fun r ↦ f r.1))=_
      simp only [ProbabilityVector.joint_first_mean,ProbabilityVector.mean_const]

theorem freshTransition_history (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (η : ℝ) (hη : 0≤η) (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i)
    (n : ℕ) (h : History D (n+1)) :
    freshTransition η hη n (estimateHistory E D κ hκ loss hloss (n+1) h,h.2.1)=
      (latentRow E D κ hκ η hη loss hloss (n+1) h).toMeasure := by
  change ((ShrinkingDartboard.kernel
    (historyWeights η n (Fin.init (estimateHistory E D κ hκ loss hloss (n+1) h))) η hη
    (fun i ↦ (estimateHistory E D κ hκ loss hloss (n+1) h (Fin.last n) i : ℝ)) _).row h.2.1).toMeasure=_
  simp only [estimateHistory,Fin.init_snoc,Fin.snoc_last,historyWeights_estimateHistory]
  rfl

theorem fresh_latent_transition (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (loss : ℕ → ι → ℝ) (hloss : ∀ n, ∀ i, 0≤loss n i) (T n : ℕ) (hn : n+1<T) (default : ι) :
    HasCondDistrib (fun x ↦ latentAt D default T x (n+1))
      (fun x ↦ (lossHistory (estimatesOnExecution E D κ hκ loss hloss T) (n+1) x,latentAt D default T x n))
      (freshTransition η hη n) (execution E D κ hκ hκ1 η hη loss hloss T).toMeasure := by
  let : MeasurableSpace (History D (n+1)) := FiniteProcess.historyMeasurableSpace (n+1)
  let row := roundKernel E D κ hκ hκ1 η hη loss hloss
  let f : History D (n+1) → LossHistory ι (n+1) × ι := fun h ↦
    (estimateHistory E D κ hκ loss hloss (n+1) h,h.2.1)
  have hf : Measurable f := measurable_of_finite f
  have hNext := (FiniteProcess.next_hasCondDistrib row (n+1) T (by omega)).fst
  have hKernel : (ProbabilityVector.kernel (row (n+1)) (fun _ ↦ Measurable.of_discrete)).fst=
      (freshTransition η hη n).comap f hf := by
    apply Kernel.ext
    intro h
    rw [Kernel.fst_apply]
    calc
      _ = (latentRow E D κ hκ η hη loss hloss (n+1) h).toMeasure :=
        (ProbabilityVector.hasLaw_of_mean (row (n+1) h)
          (latentRow E D κ hκ η hη loss hloss (n+1) h) Prod.fst
          (fun g ↦ ProbabilityVector.joint_first_mean _ _ g)).map_eq
      _ = _ := (freshTransition_history E D κ hκ η hη loss hloss n h).symm
  rw [hKernel] at hNext
  have hComp := HasCondDistrib.comp_right (hf := hf) hNext
  have hAction : (fun x : History D T ↦ (FiniteProcess.past (n+2) T (by omega) x).2.1)=
      fun x ↦ latentAt D default T x (n+1) := by
    funext x
    simp only [latentAt,dite_eq_left hn]
  have hInfo : f ∘ FiniteProcess.past (n+1) T (by omega)=
      (fun x ↦ (lossHistory (estimatesOnExecution E D κ hκ loss hloss T) (n+1) x,latentAt D default T x n)) := by
    funext x
    simp only [Function.comp_def,f,estimateHistory_execution E D κ hκ loss hloss T (n+1) hn.le,
      latentAt,dite_eq_left (show n<T by omega)]
  rw [hInfo,hAction] at hComp
  exact hComp

end
end Tournament.Upper.Exploration

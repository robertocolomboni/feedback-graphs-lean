module

public import Tournament.Probability.ConditionalExecutionMeasurable
public import Tournament.Model.FiniteFeedback
public import Tournament.Model.ObservedCompletion

@[expose] public section

namespace Tournament.Model.ConditionalFeedback

open MeasureTheory ProbabilityTheory
open Tournament.Probability ConditionalRows ConditionalExecution
open MeasurableGame
open scoped Classical

noncomputable section

universe u
variable {Meta ι : Type u} [Fintype Meta] [Fintype ι] [Nonempty Meta] [Nonempty ι]
variable [MeasurableSpace Meta] [MeasurableSpace ι]
variable [DiscreteMeasurableSpace Meta] [DiscreteMeasurableSpace ι]
variable {T : ℕ}

def play : (t : ℕ) → Draw Meta ι t → ι
  | 0, x => x.2
  | _+1, i => i

def kernel (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (t : ℕ) :
    Kernel (FiniteProcess.History (Draw Meta ι) t × FiniteFeedback.Feedback ι t) (Draw Meta ι t) :=
  contextKernel t (fun z ↦ μ (observedCompletion z.2)) (fun x ↦ by
    apply (hμ x).comp
    apply Measurable.of_eval
    intro s
    apply Measurable.of_eval
    intro i
    exact observedCompletion_measurable Prod.snd measurable_snd s i)

instance kernel_markov
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (t : ℕ) : IsMarkovKernel (kernel μ hμ t) := by
  unfold kernel
  infer_instance

theorem kernel_apply
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (t : ℕ)
    (z : FiniteProcess.History (Draw Meta ι) t × FiniteFeedback.Feedback ι t) :
    kernel μ hμ t z = (row (μ (observedCompletion z.2)) t z.1).toMeasure := rfl

def CompletionLocal (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (E : ι → ι → Prop) : Prop :=
  ∀ (loss : ℕ → ι → ℝ) (t : ℕ) (ht : t < T) (q : Meta) (a : Fin t → ι) (i : ι),
    prefixMass (μ (observedCompletion (fun s ↦ graphObservation E (a s) (loss s.val))))
      (t+1) (by omega) q (Fin.snoc a i) =
    prefixMass (μ loss) (t+1) (by omega) q (Fin.snoc a i)

omit [Fintype Meta] [Fintype ι] [Nonempty Meta] [Nonempty ι]
  [MeasurableSpace Meta] [MeasurableSpace ι]
  [DiscreteMeasurableSpace Meta] [DiscreteMeasurableSpace ι] in
theorem record_eq_encode (E : ι → ι → Prop) (loss : ℕ → ι → ℝ)
    (t : ℕ) (h : FiniteProcess.History (Draw Meta ι) (t+1)) :
    FiniteFeedback.record E play loss (t+1) h =
      fun s ↦ graphObservation E ((encode t h).2 s) (loss s.val) := by
  induction t with
  | zero =>
    funext s
    have hs : s = 0 := Fin.eq_zero s
    subst s
    rfl
  | succ t ih =>
    change (Fin.snoc (FiniteFeedback.record E play loss (t+1) h.1)
      (graphRecord E (play (t+1) h.2) (loss (t+1))) : Fin (t+1+1) → ι → ℝ) = _
    rw [ih h.1]
    funext s
    refine Fin.lastCases ?_ (fun j ↦ ?_) s
    · simp only [Fin.snoc_last, encode, play, Fin.val_last]
      rw [@Fin.snoc_last (t+1) (fun _ ↦ ι) (h.2 : ι) (encode t h.1).2]
      rfl
    · simp only [Fin.snoc_castSucc, encode, Fin.val_castSucc]
      rw [@Fin.snoc_castSucc (t+1) (fun _ ↦ ι) (h.2 : ι) (encode t h.1).2 j]

theorem kernel_context_eq_row
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (E : ι → ι → Prop)
    (hLocal : CompletionLocal μ E) (loss : ℕ → ι → ℝ) (t : ℕ)
    (h : FiniteProcess.History (Draw Meta ι) t) :
    kernel μ hμ t (FiniteFeedback.context E play loss t h) = (row (μ loss) t h).toMeasure := by
  rw [kernel_apply]
  apply congrArg ProbabilityVector.toMeasure
  cases t with
  | zero =>
    by_cases hT : 0 < T
    · change (if hp : 0 < T then
          firstRow (μ (observedCompletion (FiniteFeedback.record E play loss 0 h))) hp
          else Upper.ExponentialWeights.uniform) =
        (if hp : 0 < T then firstRow (μ loss) hp else Upper.ExponentialWeights.uniform)
      rw [dite_eq_left hT, dite_eq_left hT]
      apply firstRow_eq_of_prefixMass
      intro q i
      let a : Fin 0 → ι := fun s ↦ Fin.elim0 s
      have hr : FiniteFeedback.record E play loss 0 h =
          fun s ↦ graphObservation E (a s) (loss s.val) := by
        funext s
        exact Fin.elim0 s
      rw [hr]
      simpa only [Fin.snoc_zero] using hLocal loss 0 hT q a i
    · change (if hp : 0 < T then
          firstRow (μ (observedCompletion (FiniteFeedback.record E play loss 0 h))) hp
          else Upper.ExponentialWeights.uniform) =
        (if hp : 0 < T then firstRow (μ loss) hp else Upper.ExponentialWeights.uniform)
      rw [dite_eq_right hT, dite_eq_right hT]
  | succ t =>
    by_cases ht : t+1 < T
    · change (if hp : t+1 < T then
          nextRow (μ (observedCompletion (FiniteFeedback.record E play loss (t+1) h)))
            (t+1) hp (encode t h).1 (encode t h).2 else Upper.ExponentialWeights.uniform) =
        (if hp : t+1 < T then nextRow (μ loss) (t+1) hp (encode t h).1 (encode t h).2
          else Upper.ExponentialWeights.uniform)
      rw [dite_eq_left ht, dite_eq_left ht]
      apply nextRow_eq_of_nextMass
      intro i
      rw [record_eq_encode]
      exact hLocal loss (t+1) ht (encode t h).1 (encode t h).2 i
    · change (if hp : t+1 < T then
          nextRow (μ (observedCompletion (FiniteFeedback.record E play loss (t+1) h)))
            (t+1) hp (encode t h).1 (encode t h).2 else Upper.ExponentialWeights.uniform) =
        (if hp : t+1 < T then nextRow (μ loss) (t+1) hp (encode t h).1 (encode t h).2
          else Upper.ExponentialWeights.uniform)
      rw [dite_eq_right ht, dite_eq_right ht]

def learner
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (default : ι) :
    Learner ι (UniformSeed.Space T) :=
  FiniteFeedback.learner (kernel μ hμ) play T default

theorem run_hasLaw
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (E : ι → ι → Prop)
    (hLocal : CompletionLocal μ E) (loss : ℕ → ι → ℝ) :
    HasLaw (UniformExecution.run (kernel μ hμ) (FiniteFeedback.context E play loss) T)
      (FiniteProcess.law (row (μ loss)) T).toMeasure (UniformSeed.law T) :=
  UniformExecution.run_hasLaw (kernel μ hμ) (FiniteFeedback.context E play loss)
    (row (μ loss)) (fun t h ↦ kernel_context_eq_row μ hμ E hLocal loss t h) T

end
end Tournament.Model.ConditionalFeedback

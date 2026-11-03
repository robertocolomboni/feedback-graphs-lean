module

public import Tournament.Probability.ConditionalExecution
public import Tournament.Probability.ProcessConditional

@[expose] public section

namespace Tournament.ConditionalExecution

open MeasureTheory ProbabilityTheory
open ConditionalRows
open scoped Classical

noncomputable section

universe u
variable {Meta ι : Type u}

instance drawMeasurableSpace [MeasurableSpace Meta] [MeasurableSpace ι] :
    (t : ℕ) → MeasurableSpace (Draw Meta ι t)
  | 0 => inferInstanceAs (MeasurableSpace (Meta × ι))
  | _+1 => inferInstanceAs (MeasurableSpace ι)

instance drawDiscreteMeasurableSpace [Fintype Meta] [Fintype ι]
    [MeasurableSpace Meta] [MeasurableSpace ι]
    [DiscreteMeasurableSpace Meta] [DiscreteMeasurableSpace ι] (t : ℕ) :
    DiscreteMeasurableSpace (Draw Meta ι t) := by
  cases t with
  | zero => exact inferInstanceAs (DiscreteMeasurableSpace (Meta × ι))
  | succ t => exact inferInstanceAs (DiscreteMeasurableSpace ι)

variable [Fintype Meta] [Fintype ι] [Nonempty Meta] [Nonempty ι]
variable [MeasurableSpace Meta] [MeasurableSpace ι]
variable [DiscreteMeasurableSpace Meta] [DiscreteMeasurableSpace ι]
variable {A : Type*} [MeasurableSpace A] {T : ℕ}

theorem row_weight_measurable_varying
    (μ : A → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x)) (t : ℕ)
    (h : A → FiniteProcess.History (Draw Meta ι) t) (hh : Measurable h)
    (i : Draw Meta ι t) : Measurable (fun z ↦ row (μ z) t (h z) i) := by
  cases t with
  | zero =>
    by_cases hT : 0 < T
    · have heq : (fun z ↦ row (μ z) 0 (h z) i) =
          (fun z ↦ firstRow (μ z) hT i) := by
        funext z
        change (if hp : 0 < T then firstRow (μ z) hp else Upper.ExponentialWeights.uniform) i = _
        rw [dite_eq_left hT]
      rw [heq]
      exact firstRow_weight_measurable μ hμ hT i
    · have heq : (fun z ↦ row (μ z) 0 (h z) i) =
          (fun _ : A ↦ (Upper.ExponentialWeights.uniform : ProbabilityVector (Meta × ι)) i) := by
        funext z
        change (if hp : 0 < T then firstRow (μ z) hp else Upper.ExponentialWeights.uniform) i = _
        rw [dite_eq_right hT]
      rw [heq]
      exact measurable_const
  | succ t =>
    by_cases ht : t+1 < T
    · have heq : (fun z ↦ row (μ z) (t+1) (h z) i) =
          (fun z ↦ nextRow (μ z) (t+1) ht (encode t (h z)).1 (encode t (h z)).2 i) := by
        funext z
        change (if hp : t+1 < T then
          nextRow (μ z) (t+1) hp (encode t (h z)).1 (encode t (h z)).2
          else Upper.ExponentialWeights.uniform) i = _
        rw [dite_eq_left ht]
      rw [heq]
      have he : @Measurable (FiniteProcess.History (Draw Meta ι) (t+1))
          (Meta × (Fin (t+1) → ι)) (FiniteProcess.historyMeasurableSpace (t+1))
          inferInstance (encode t) := by
        intro s _
        trivial
      have henc : Measurable (fun z ↦ encode t (h z)) := he.comp (f := h) hh
      exact nextRow_weight_measurable_varying μ hμ (t+1) ht
        (fun z ↦ (encode t (h z)).1) henc.fst (fun z ↦ (encode t (h z)).2) henc.snd i
    · have heq : (fun z ↦ row (μ z) (t+1) (h z) i) =
          (fun _ : A ↦ (Upper.ExponentialWeights.uniform : ProbabilityVector ι) i) := by
        funext z
        change (if hp : t+1 < T then
          nextRow (μ z) (t+1) hp (encode t (h z)).1 (encode t (h z)).2
          else Upper.ExponentialWeights.uniform) i = _
        rw [dite_eq_right ht]
      rw [heq]
      exact measurable_const

def contextKernel {O : Type*} [MeasurableSpace O] (t : ℕ)
    (μ : FiniteProcess.History (Draw Meta ι) t × O →
      ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x)) :
    Kernel (FiniteProcess.History (Draw Meta ι) t × O) (Draw Meta ι t) :=
  ProbabilityVector.kernel (fun z ↦ row (μ z) t z.1)
    (row_weight_measurable_varying μ hμ t Prod.fst measurable_fst)

instance contextKernel_markov {O : Type*} [MeasurableSpace O] (t : ℕ)
    (μ : FiniteProcess.History (Draw Meta ι) t × O →
      ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x)) :
    IsMarkovKernel (contextKernel t μ hμ) := by
  unfold contextKernel
  infer_instance

theorem contextKernel_apply {O : Type*} [MeasurableSpace O] (t : ℕ)
    (μ : FiniteProcess.History (Draw Meta ι) t × O →
      ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun z ↦ μ z x))
    (z : FiniteProcess.History (Draw Meta ι) t × O) :
    contextKernel t μ hμ z = (row (μ z) t z.1).toMeasure := rfl

end
end Tournament.ConditionalExecution

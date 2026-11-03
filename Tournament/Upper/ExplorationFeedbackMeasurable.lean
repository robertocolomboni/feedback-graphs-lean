module

public import Tournament.Upper.ExplorationFeedback

@[expose] public section

namespace Tournament.Upper.Exploration

open MeasureTheory ProbabilityTheory ShrinkingDartboard
open scoped Classical

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem clampedEstimate_measurable (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ)
    (q : Bool × D) (i : ι) : Measurable (fun obs : ι → ℝ ↦ clampedEstimate E D κ obs q i) := by
  unfold clampedEstimate estimate
  by_cases h : q.1 ∧ E q.2.val i
  · simp only [ite_eq_left h]
    exact measurable_const.mul ((measurable_pi_apply i).max measurable_const)
  · simp only [ite_eq_right h]
    exact measurable_const

theorem feedbackWeights_measurable (E : ι → ι → Prop) (D : Finset ι) (κ η : ℝ)
    (n : ℕ) (h : History D n) (i : ι) :
    Measurable (fun obs : Feedback ι n ↦ feedbackWeights E D κ η n h obs i) := by
  induction n generalizing i with
  | zero => exact measurable_const
  | succ n ih =>
    have hinit : Measurable (fun obs : Feedback ι (n+1) ↦ Fin.init obs) :=
      Measurable.of_eval (fun _ ↦ measurable_pi_apply _)
    exact update_weight_measurable
      (fun obs : Feedback ι (n+1) ↦ feedbackWeights E D κ η n h.1 (Fin.init obs))
      (fun j ↦ (ih h.1 j).comp hinit)
      (fun obs : Feedback ι (n+1) ↦ clampedEstimate E D κ (obs (Fin.last n)) h.2.2)
      (fun j ↦ (clampedEstimate_measurable E D κ h.2.2 j).comp (measurable_pi_apply _)) η i

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem feedbackLatentRow_measurable (E : ι → ι → Prop) (D : Finset ι) (κ : ℝ) (hκ : 0≤κ)
    (η : ℝ) (hη : 0≤η) (n : ℕ) (h : History D n) (j : ι) :
    Measurable (fun obs : Feedback ι n ↦ feedbackLatentRow E D κ hκ η hη n h obs j) := by
  cases n with
  | zero => exact measurable_const
  | succ n =>
    have hinit : Measurable (fun obs : Feedback ι (n+1) ↦ Fin.init obs) :=
      Measurable.of_eval (fun _ ↦ measurable_pi_apply _)
    have hm := transitionRowWeights_measurable
      (fun obs : Feedback ι (n+1) ↦ feedbackWeights E D κ η n h.1 (Fin.init obs))
      (fun i ↦ (feedbackWeights_measurable E D κ η n h.1 i).comp hinit) η hη
      (fun obs : Feedback ι (n+1) ↦ clampedEstimate E D κ (obs (Fin.last n)) h.2.2)
      (fun obs i ↦ clampedEstimate_nonneg E D κ hκ (obs (Fin.last n)) h.2.2 i)
      (fun i ↦ (clampedEstimate_measurable E D κ h.2.2 i).comp (measurable_pi_apply _)) j
    exact hm.comp (measurable_id.prodMk measurable_const)

theorem feedbackRound_weight_measurable (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η)
    (n : ℕ) (h : History D n) (r : RoundOutcome D) :
    Measurable (fun obs : Feedback ι n ↦ feedbackRound E D κ hκ hκ1 η hη n h obs r) :=
  (feedbackLatentRow_measurable E D κ hκ η hη n h r.1).mul_const _

def feedbackRoundKernel (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η) (n : ℕ) :
    Kernel (History D n × Feedback ι n) (RoundOutcome D) :=
  ProbabilityVector.kernel (fun q ↦ feedbackRound E D κ hκ hκ1 η hη n q.1 q.2) (fun r ↦ by
    apply measurable_from_prod_countable_right
    intro h
    exact feedbackRound_weight_measurable E D κ hκ hκ1 η hη n h r)

instance feedbackRoundKernel_markov (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η) (n : ℕ) :
    IsMarkovKernel (feedbackRoundKernel E D κ hκ hκ1 η hη n) := by
  unfold feedbackRoundKernel
  infer_instance

end
end Tournament.Upper.Exploration

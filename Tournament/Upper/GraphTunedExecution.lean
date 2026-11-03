module

public import Tournament.Model.GraphFeedbackEW
public import Tournament.Upper.TunedExecution

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter FiniteProcess Model ExponentialWeights BlockParameters Tuning

noncomputable section
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [LinearOrder ι]

local instance : DecidableEq ι := Classical.decEq ι

def graphTunedParameters (E : ι → ι → Prop) (hE : StronglyRevealing E) (T : ℕ)
    (hK : 2≤Fintype.card ι) (hT : 2≤T) (hr : target (Fintype.card ι) T≤1/32)
    (rounded : Bool := false) : SteeringParameters ι where
  tournament := selectedEdge E
  isTournament := selectedEdge_isTournament hE
  T := T
  m := exponent (target (Fintype.card ι) T)
  card_ge_two := hK
  time_ge_two := hT
  bands_ge_five := exponent_ge_five (target_pos hK hT) hr
  rounded := rounded

theorem graph_tuned_small_target (E : ι → ι → Prop) (hE : StronglyRevealing E) (T : ℕ)
    (hK : 2≤Fintype.card ι) (hT : 2≤T) (hr : target (Fintype.card ι) T≤1/32)
    (loss : ℕ → ι → ℝ) (hloss : ∀ t, BoundedLoss (loss t)) (default : ι) (rounded : Bool := false) :
    let A := graphTunedParameters E hE T hK hT hr rounded
    let P := (A.feedbackPolicy.toGraph E).algorithm E A.schedule loss
    (∫ x, pathRegret T loss (A.actions A.schedule default A.blockCount x)
      ∂(P.execution A.blockCount).toMeasure)≤
        (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) ∧
      (∫ x, (switchCount T (A.actions A.schedule default A.blockCount x):ℝ)
        ∂(P.execution A.blockCount).toMeasure)≤
          (2:ℝ)^40*min (T:ℝ) (performanceScale (Fintype.card ι) T) := by
  let A := graphTunedParameters E hE T hK hT hr rounded
  have heq := FeedbackEW.toGraph_algorithm A.feedbackPolicy E A.schedule loss
  change ((∫ x, pathRegret T loss (A.actions A.schedule default A.blockCount x)
    ∂(((A.feedbackPolicy.toGraph E).algorithm E A.schedule loss).execution A.blockCount).toMeasure)≤_ ∧ _)
  rw [heq]
  simpa only [A,graphTunedParameters] using A.tuned_small_target rfl hr loss hloss default

end
end Tournament.Upper

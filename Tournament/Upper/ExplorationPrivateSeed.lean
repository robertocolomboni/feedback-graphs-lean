module

public import Tournament.Upper.ExplorationMain
public import Tournament.Model.FiniteFeedback

@[expose] public section

namespace Tournament.Upper.Exploration

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open Tournament.Probability
open scoped Classical
noncomputable section

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι] in
theorem private_record_eq (E : ι → ι → Prop) (D : Finset ι) (loss : ℕ → ι → ℝ)
    (n : ℕ) (h : History D n) :
    FiniteFeedback.record E (fun _ (r : RoundOutcome D) ↦ played D r.1 r.2) loss n h=
      feedbackRecord E D loss n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FiniteFeedback.record,feedbackRecord,ih h.1]
    rfl

def privateLearner (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η) (T : ℕ) (default : ι) :
    Learner ι (UniformSeed.Space T) :=
  FiniteFeedback.learner (feedbackRoundKernel E D κ hκ hκ1 η hη)
    (fun _ r ↦ played D r.1 r.2) T default

def privateStrategy (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η) (T : ℕ) (default : ι) : Strategy.{u,0} ι :=
  FiniteFeedback.strategy (feedbackRoundKernel E D κ hκ hκ1 η hη)
    (fun _ r ↦ played D r.1 r.2) T default

theorem private_expected_regret_eq (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η) (T : ℕ) (default : ι)
    (loss : ℕ → ι → ℝ) :
    deterministicExpectedRegret T (UniformSeed.law T) (privateLearner E D κ hκ hκ1 η hη T default) E loss=
      (feedbackExecution E D κ hκ hκ1 η hη loss T).mean
        (fun x ↦ Model.pathRegret T loss (actions D default T x)) := by
  apply FiniteFeedback.expected_regret_eq_mean
  intro n h
  change (feedbackRound E D κ hκ hκ1 η hη n h
    (FiniteFeedback.record E (fun _ (r : RoundOutcome D) ↦ played D r.1 r.2) loss n h)).toMeasure=_
  rw [private_record_eq]

theorem private_expected_switches_eq (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (η : ℝ) (hη : 0≤η) (T : ℕ) (default : ι)
    (loss : ℕ → ι → ℝ) :
    (∫ ω, (Model.switchCount T (fun t ↦
      deterministicAction (privateLearner E D κ hκ hκ1 η hη T default) E loss t ω):ℝ) ∂UniformSeed.law T)=
      (feedbackExecution E D κ hκ hκ1 η hη loss T).mean
        (fun x ↦ (Model.switchCount T (actions D default T x):ℝ)) := by
  apply FiniteFeedback.expected_switches_eq_mean
  intro n h
  change (feedbackRound E D κ hκ hκ1 η hη n h
    (FiniteFeedback.record E (fun _ (r : RoundOutcome D) ↦ played D r.1 r.2) loss n h)).toMeasure=_
  rw [private_record_eq]

theorem observable_graph_private_seed (E : ι → ι → Prop) (D : Finset ι) [Nonempty D] (hD : ObservingSet E D)
    (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T)
    (hRate : rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)≤1/2) (default : ι) :
    ∃ σ : Strategy.{u,0} ι, ∀ loss : ℕ → ι → ℝ, (∀ t<T, BoundedLoss (loss t)) →
      σ.regret T E loss≤
        (3:ℝ)^((4:ℝ)/3)*((D.card:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3) := by
  obtain ⟨hκ,hη,hBound⟩ := observable_graph_lazy_exploration E D hD hK T hT hRate default
  let κ := rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
  let η := learningRate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)
  have hκ1 : κ≤1 := by dsimp [κ]; linarith
  refine ⟨privateStrategy E D κ hκ.le hκ1 η hη.le T default,?_⟩
  intro loss hLoss
  change deterministicExpectedRegret T (UniformSeed.law T)
    (privateLearner E D κ hκ.le hκ1 η hη.le T default) E loss≤_
  rw [private_expected_regret_eq]
  exact hBound loss hLoss

theorem observable_graph_small_rate_minimax (E : ι → ι → Prop) (D : Finset ι) [Nonempty D]
    (hD : ObservingSet E D) (hK : 2≤Fintype.card ι) (T : ℕ) (hT : 1≤T)
    (hRate : rate (D.card:ℝ) (Real.log (Fintype.card ι:ℝ)) (T:ℝ)≤1/2) (default : ι) :
    minimax.{u,0} T E≤
      (3:ℝ)^((4:ℝ)/3)*((D.card:ℝ)*Real.log (Fintype.card ι:ℝ))^((1:ℝ)/3)*(T:ℝ)^((2:ℝ)/3) := by
  obtain ⟨σ,hBound⟩ := observable_graph_private_seed E D hD hK T hT hRate default
  apply (minimax_le_worst σ T E).trans
  exact σ.worstRegret_le T E _ (fun loss hLoss ↦ hBound loss (fun t _ i ↦ hLoss t i))

end
end Tournament.Upper.Exploration

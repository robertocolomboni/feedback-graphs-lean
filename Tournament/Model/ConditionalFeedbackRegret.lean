module

public import Tournament.Model.ConditionalFeedback

@[expose] public section

namespace Tournament.Model.ConditionalFeedback

open MeasureTheory ProbabilityTheory
open Tournament.Probability ConditionalExecution
open MeasurableGame
open scoped Classical

noncomputable section

universe u
variable {Meta ι : Type u}

def traceActions (default : ι) {T : ℕ} (a : Fin T → ι) (t : ℕ) : ι :=
  if ht : t < T then a ⟨t,ht⟩ else default

theorem traceActions_of_lt (default : ι) {T : ℕ} (a : Fin T → ι) (t : ℕ) (ht : t < T) :
    traceActions default a t = a ⟨t,ht⟩ := by
  simp only [traceActions, dite_eq_left ht]

theorem traceActions_of_ge (default : ι) {T : ℕ} (a : Fin T → ι) (t : ℕ) (ht : T ≤ t) :
    traceActions default a t = default := by
  simp only [traceActions, dite_eq_right (by omega : ¬t < T)]

theorem play_past_eq_encode (T : ℕ) (h : FiniteProcess.History (Draw Meta ι) (T+1))
    (t : ℕ) (ht : t < T+1) :
    play t (FiniteProcess.past (t+1) (T+1) (by omega) h).2 =
      (encode T h).2 ⟨t,ht⟩ := by
  induction T generalizing t with
  | zero =>
    have ht0 : t = 0 := by omega
    subst t
    rw [FiniteProcess.past_self]
    rfl
  | succ T ih =>
    by_cases htLast : t = T+1
    · subst t
      rw [FiniteProcess.past_self]
      change (h.2 : ι) = (Fin.snoc (encode T h.1).2 (h.2 : ι) : Fin (T+1+1) → ι)
        (Fin.last (T+1))
      exact (@Fin.snoc_last (T+1) (fun _ ↦ ι) (h.2 : ι) (encode T h.1).2).symm
    · have ht' : t < T+1 := by omega
      rw [FiniteProcess.past_succ (t+1) (T+1) (by omega)]
      have hi : (⟨t,ht⟩ : Fin (T+1+1)) = (⟨t,ht'⟩ : Fin (T+1)).castSucc := Fin.ext rfl
      rw [hi]
      change play t (FiniteProcess.past (t+1) (T+1) (by omega) h.1).2 =
        (Fin.snoc (encode T h.1).2 (h.2 : ι) : Fin (T+1+1) → ι) (⟨t,ht'⟩ : Fin (T+1)).castSucc
      rw [@Fin.snoc_castSucc (T+1) (fun _ ↦ ι) (h.2 : ι) (encode T h.1).2 ⟨t,ht'⟩]
      exact ih h.1 t ht'

theorem sampledActions_eq_traceActions (default : ι) (T : ℕ)
    (h : FiniteProcess.History (Draw Meta ι) (T+1)) :
    FiniteFeedback.sampledActions play default (T+1) h = traceActions default (encode T h).2 := by
  funext t
  by_cases ht : t < T+1
  · simp only [FiniteFeedback.sampledActions, traceActions, dite_eq_left ht]
    exact play_past_eq_encode T h t ht
  · simp only [FiniteFeedback.sampledActions, traceActions, dite_eq_right ht]

variable [Fintype Meta] [Fintype ι] [Nonempty Meta] [Nonempty ι]
variable [MeasurableSpace Meta] [MeasurableSpace ι]
variable [DiscreteMeasurableSpace Meta] [DiscreteMeasurableSpace ι]
variable {T : ℕ}

theorem expected_regret_eq_mean
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin (T+1) → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (E : ι → ι → Prop)
    (hLocal : CompletionLocal μ E) (loss : ℕ → ι → ℝ) (default : ι) :
    deterministicExpectedRegret (T+1) (UniformSeed.law (T+1)) (learner μ hμ default) E loss =
      (μ loss).mean (fun x ↦ pathRegret (T+1) loss (traceActions default x.2)) := by
  rw [show learner μ hμ default = FiniteFeedback.learner (kernel μ hμ) play (T+1) default from rfl]
  rw [FiniteFeedback.expected_regret_eq_mean (kernel μ hμ) E play loss (T+1) default
    (row (μ loss)) (fun t h ↦ kernel_context_eq_row μ hμ E hLocal loss t h)]
  simp_rw [sampledActions_eq_traceActions]
  exact law_mean_encode (μ loss) (fun x ↦ pathRegret (T+1) loss (traceActions default x.2))

theorem expected_switches_eq_mean
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin (T+1) → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (E : ι → ι → Prop)
    (hLocal : CompletionLocal μ E) (loss : ℕ → ι → ℝ) (default : ι) :
    (∫ ω, (switchCount (T+1) (fun t ↦ deterministicAction (learner μ hμ default) E loss t ω) : ℝ)
      ∂UniformSeed.law (T+1)) =
      (μ loss).mean (fun x ↦ (switchCount (T+1) (traceActions default x.2) : ℝ)) := by
  rw [show learner μ hμ default = FiniteFeedback.learner (kernel μ hμ) play (T+1) default from rfl]
  rw [FiniteFeedback.expected_switches_eq_mean (kernel μ hμ) E play loss (T+1) default
    (row (μ loss)) (fun t h ↦ kernel_context_eq_row μ hμ E hLocal loss t h)]
  simp_rw [sampledActions_eq_traceActions]
  exact law_mean_encode (μ loss) (fun x ↦ (switchCount (T+1) (traceActions default x.2) : ℝ))

def strategy
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin (T+1) → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (default : ι) : Strategy.{u,0} ι :=
  FiniteFeedback.strategy (kernel μ hμ) play (T+1) default

theorem strategy_regret_eq_mean
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin (T+1) → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (E : ι → ι → Prop)
    (hLocal : CompletionLocal μ E) (loss : ℕ → ι → ℝ) (default : ι) :
    (strategy μ hμ default).regret (T+1) E loss =
      (μ loss).mean (fun x ↦ pathRegret (T+1) loss (traceActions default x.2)) :=
  expected_regret_eq_mean μ hμ E hLocal loss default

def strategyOfPositive
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (hT : 0 < T) (default : ι) :
    Strategy.{u,0} ι := by
  cases T with
  | zero => omega
  | succ T => exact strategy μ hμ default

theorem strategyOfPositive_regret_eq_mean
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (hT : 0 < T)
    (E : ι → ι → Prop) (hLocal : CompletionLocal μ E)
    (loss : ℕ → ι → ℝ) (default : ι) :
    (strategyOfPositive μ hμ hT default).regret T E loss =
      (μ loss).mean (fun x ↦ pathRegret T loss (traceActions default x.2)) := by
  cases T with
  | zero => omega
  | succ T => exact strategy_regret_eq_mean μ hμ E hLocal loss default

theorem expected_regret_eq_mean_of_positive
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (hT : 0 < T)
    (E : ι → ι → Prop) (hLocal : CompletionLocal μ E)
    (loss : ℕ → ι → ℝ) (default : ι) :
    deterministicExpectedRegret T (UniformSeed.law T) (learner μ hμ default) E loss =
      (μ loss).mean (fun x ↦ pathRegret T loss (traceActions default x.2)) := by
  cases T with
  | zero => omega
  | succ T => exact expected_regret_eq_mean μ hμ E hLocal loss default

theorem expected_switches_eq_mean_of_positive
    (μ : (ℕ → ι → ℝ) → ProbabilityVector (Meta × (Fin T → ι)))
    (hμ : ∀ x, Measurable (fun loss ↦ μ loss x)) (hT : 0 < T)
    (E : ι → ι → Prop) (hLocal : CompletionLocal μ E)
    (loss : ℕ → ι → ℝ) (default : ι) :
    (∫ ω, (switchCount T (fun t ↦ deterministicAction (learner μ hμ default) E loss t ω) : ℝ)
      ∂UniformSeed.law T) =
      (μ loss).mean (fun x ↦ (switchCount T (traceActions default x.2) : ℝ)) := by
  cases T with
  | zero => omega
  | succ T => exact expected_switches_eq_mean μ hμ E hLocal loss default

end
end Tournament.Model.ConditionalFeedback

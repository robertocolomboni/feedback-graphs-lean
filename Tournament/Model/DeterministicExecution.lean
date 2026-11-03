module

public import Tournament.Model.MeasurableRegret
public import Tournament.Model.MeasurableLearner

@[expose] public section

namespace Tournament.Model.MeasurableGame

open MeasureTheory
open scoped Classical

noncomputable section

variable {ι Seed Ω : Type*} [MeasurableSpace ι] [MeasurableSpace Seed] [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem runHistory_section (π : Learner ι Seed) (E : ι → ι → Prop) (loss : ℕ → Ω → ι → ℝ)
    (n : ℕ) (seed : Seed) (ω : Ω) :
    runHistory π E (fun t (_ : Unit) ↦ loss t ω) n (seed,())=runHistory π E loss n (seed,ω) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [runHistory,ih]

omit [MeasurableSpace Ω] in
theorem action_section (π : Learner ι Seed) (E : ι → ι → Prop) (loss : ℕ → Ω → ι → ℝ)
    (n : ℕ) (seed : Seed) (ω : Ω) :
    action π E (fun t (_ : Unit) ↦ loss t ω) n (seed,())=action π E loss n (seed,ω) := by
  simp only [action,runHistory_section]

def deterministicAction (π : Learner ι Seed) (E : ι → ι → Prop) (loss : ℕ → ι → ℝ)
    (n : ℕ) (seed : Seed) : ι := action π E (fun t (_ : Unit) ↦ loss t) n (seed,())

variable [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem deterministicAction_measurable (π : Learner ι Seed) (E : ι → ι → Prop) (loss : ℕ → ι → ℝ)
    (n : ℕ) : Measurable (deterministicAction π E loss n) :=
  (action_measurable π E (fun t (_ : Unit) ↦ loss t) (fun _ ↦ measurable_const) n).comp
    (measurable_id.prodMk measurable_const)

def deterministicPathRegret (T : ℕ) (π : Learner ι Seed) (E : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) (seed : Seed) : ℝ := pathRegret T loss (fun n ↦ deterministicAction π E loss n seed)

def deterministicExpectedRegret (T : ℕ) (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (loss : ℕ → ι → ℝ) : ℝ := ∫ seed, deterministicPathRegret T π E loss seed ∂ν

theorem deterministicPathRegret_integrable (T : ℕ) (ν : Measure Seed) [IsFiniteMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (loss : ℕ → ι → ℝ)
    (hbound : ∀ t a, 0≤loss t a ∧ loss t a≤1) :
    Integrable (deterministicPathRegret T π E loss) ν :=
  pathRegret_integrable ν T (fun t (_ : Seed) ↦ loss t) (fun _ _ ↦ measurable_const)
    (fun t _ a ↦ hbound t a) (deterministicAction π E loss) (deterministicAction_measurable π E loss)

end
end Tournament.Model.MeasurableGame

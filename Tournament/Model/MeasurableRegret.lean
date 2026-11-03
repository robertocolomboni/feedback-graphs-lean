module

public import Tournament.Model.MeasurableLearner
public import Tournament.Model.BlockAccounting
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

namespace Tournament.Model.MeasurableGame

open MeasureTheory
open scoped Classical BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem measurable_finite_min (s : Finset ι) (hne : s.Nonempty) (f : ι → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω ↦ s.inf' hne (fun i ↦ f i ω)) := by
  revert hne
  induction s using Finset.induction_on with
  | empty => intro h; simp at h
  | @insert i s hi ih =>
    intro hne
    by_cases hs : s.Nonempty
    · simp_rw [Finset.inf'_insert hs]
      exact (hf i).min (ih hs)
    · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simpa only [Finset.insert_empty,Finset.inf'_singleton] using hf i

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]

theorem measurable_variable_evaluation (f : Ω → ι → ℝ) (hf : ∀ i, Measurable (fun ω ↦ f ω i))
    (a : Ω → ι) (ha : Measurable a) : Measurable (fun ω ↦ f ω (a ω)) := by
  have heq : (fun ω ↦ f ω (a ω))=(fun ω ↦ ∑ i, if a ω=i then f ω i else 0) := by
    funext ω
    simp
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite ((measurableSet_singleton i).preimage ha) (hf i) measurable_const

theorem accumulatedLoss_measurable (T : ℕ) (loss : ℕ → Ω → ι → ℝ)
    (hloss : ∀ t i, Measurable (fun ω ↦ loss t ω i)) (path : ℕ → Ω → ι)
    (hpath : ∀ t, Measurable (path t)) :
    Measurable (fun ω ↦ accumulatedLoss T (fun t ↦ loss t ω) (fun t ↦ path t ω)) := by
  apply Finset.measurable_sum
  intro t _
  exact measurable_variable_evaluation (loss t) (hloss t) (path t) (hpath t)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem fixedLoss_measurable (T : ℕ) (loss : ℕ → Ω → ι → ℝ)
    (hloss : ∀ t i, Measurable (fun ω ↦ loss t ω i)) (i : ι) :
    Measurable (fun ω ↦ fixedLoss T (fun t ↦ loss t ω) i) :=
  Finset.measurable_sum _ (fun t _ ↦ hloss t i)

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] in
theorem bestFixedLoss_measurable [Nonempty ι] (T : ℕ) (loss : ℕ → Ω → ι → ℝ)
    (hloss : ∀ t i, Measurable (fun ω ↦ loss t ω i)) :
    Measurable (fun ω ↦ bestFixedLoss T (fun t ↦ loss t ω)) :=
  measurable_finite_min Finset.univ Finset.univ_nonempty _ (fixedLoss_measurable T loss hloss)

theorem switchCount_measurable (T : ℕ) (path : ℕ → Ω → ι) (hpath : ∀ t, Measurable (path t)) :
    Measurable (fun ω ↦ switchCount T (fun t ↦ path t ω)) := by
  apply Finset.measurable_sum
  intro t _
  exact (Measurable.of_discrete (f := fun p : ι × ι ↦ if p.1=p.2 then (0:ℕ) else 1)).comp
    ((hpath (t+1)).prodMk (hpath t))

theorem pathRegret_measurable [Nonempty ι] (T : ℕ) (loss : ℕ → Ω → ι → ℝ)
    (hloss : ∀ t i, Measurable (fun ω ↦ loss t ω i)) (path : ℕ → Ω → ι)
    (hpath : ∀ t, Measurable (path t)) :
    Measurable (fun ω ↦ pathRegret T (fun t ↦ loss t ω) (fun t ↦ path t ω)) := by
  have hs : Measurable (fun ω ↦ (switchCount T (fun t ↦ path t ω):ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ ↦ (n:ℝ))).comp (switchCount_measurable T path hpath)
  exact ((accumulatedLoss_measurable T loss hloss path hpath).add hs).sub
    (bestFixedLoss_measurable T loss hloss)

theorem pathRegret_integrable [Nonempty ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : ℕ) (loss : ℕ → Ω → ι → ℝ)
    (hloss : ∀ t i, Measurable (fun ω ↦ loss t ω i))
    (hbound : ∀ t ω i, 0≤loss t ω i ∧ loss t ω i≤1)
    (path : ℕ → Ω → ι) (hpath : ∀ t, Measurable (path t)) :
    Integrable (fun ω ↦ pathRegret T (fun t ↦ loss t ω) (fun t ↦ path t ω)) μ := by
  apply Integrable.of_bound (pathRegret_measurable T loss hloss path hpath).aestronglyMeasurable (2*(T:ℝ))
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs]
  exact pathRegret_norm_le T (fun t ↦ loss t ω) (fun t i ↦ hbound t ω i) (fun t ↦ path t ω)

end
end Tournament.Model.MeasurableGame

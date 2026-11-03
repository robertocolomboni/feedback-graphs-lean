module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

namespace Tournament.Probability

open MeasureTheory
open scoped Classical
noncomputable section

theorem measurable_of_discrete_factor {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    [DiscreteMeasurableSpace C] (code : A → C) (hCode : Measurable code) (f : A → ℝ)
    (hFiber : ∀ a b, code a=code b → f a=f b) : Measurable f := by
  let lookup : C → ℝ := fun c ↦ if h : ∃ a, code a=c then f h.choose else 0
  have hLookup (a : A) : lookup (code a)=f a := by
    dsimp only [lookup]
    rw [dite_eq_left (show ∃ b, code b=code a from ⟨a,rfl⟩)]
    exact hFiber _ a (Classical.choose_spec (show ∃ b, code b=code a from ⟨a,rfl⟩))
  have hEq : f=lookup ∘ code := by funext a; exact (hLookup a).symm
  rw [hEq]
  exact (Measurable.of_discrete (f := lookup)).comp hCode

theorem measurable_countable_parameter {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    [Countable C] [MeasurableSingletonClass C] (f : C → A → ℝ) (hf : ∀ c, Measurable (f c))
    (index : A → C) (hIndex : Measurable index) : Measurable (fun a ↦ f (index a) a) := by
  have h : Measurable (fun q : C × A ↦ f q.1 q.2) := measurable_from_prod_countable_right hf
  exact h.comp (hIndex.prodMk measurable_id)

end
end Tournament.Probability

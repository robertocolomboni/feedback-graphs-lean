module

public import Tournament.Probability.FiniteProcess

@[expose] public section

namespace Tournament.FiniteProcess

open scoped BigOperators Classical MeasureTheory
open MeasureTheory Filter

noncomputable section

universe u
variable {Y : ℕ → Type u} [∀ b, Fintype (Y b)]

instance historyMeasurableSpace (B : ℕ) : MeasurableSpace (History Y B) := ⊤

instance historyMeasurableSingleton (B : ℕ) : MeasurableSingletonClass (History Y B) :=
  ⟨fun _ ↦ trivial⟩

abbrev information (b B : ℕ) (h : b≤B) : MeasurableSpace (History Y B) :=
  MeasurableSpace.comap (past b B h) (historyMeasurableSpace b)

omit [∀ b, Fintype (Y b)] in
theorem information_le (b B : ℕ) (h : b≤B) :
    information (Y := Y) b B h≤historyMeasurableSpace B := le_top

theorem measurable_past_value (a b B : ℕ) (hab : a≤b) (hbB : b≤B)
    (f : History Y a → ℝ) :
    Measurable[information b B hbB] (fun x ↦ f (past a B (hab.trans hbB) x)) := by
  have hf : Measurable (fun s : History Y b ↦ f (past a b hab s)) := measurable_of_finite _
  have hc := hf.comp (comap_measurable (past b B hbB))
  simpa only [Function.comp_def,past_comp] using hc

theorem condExp_next (κ : (b : ℕ) → History Y b → ProbabilityVector (Y b))
    (b B : ℕ) (h : b+1≤B) (f : History Y (b+1) → ℝ) :
    (law κ B).toMeasure[fun x ↦ f (past (b+1) B h x) |
      information b B (by omega)] =ᵐ[(law κ B).toMeasure]
        fun x ↦ (κ b (past b B (by omega) x)).mean
          (fun y ↦ f (past b B (by omega) x,y)) := by
  apply FiniteConditional.condExp_of_fiber_identity (law κ B) (past b B (by omega))
    (fun x ↦ f (past (b+1) B h x)) (fun s ↦ (κ b s).mean (fun y ↦ f (s,y)))
  intro s
  rw [fiberSum_prefix κ b B h f s,fiberMass_prefix]
  ring

theorem integral_next (κ : (b : ℕ) → History Y b → ProbabilityVector (Y b))
    (b B : ℕ) (h : b+1≤B) (f : History Y (b+1) → ℝ) :
    (∫ x, f (past (b+1) B h x) ∂(law κ B).toMeasure)=
      (law κ b).mean (fun s ↦ (κ b s).mean (fun y ↦ f (s,y))) := by
  rw [ProbabilityVector.integral_toMeasure,mean_prefix]
  exact ProbabilityVector.joint_mean (law κ b) (κ b) f

end
end Tournament.FiniteProcess

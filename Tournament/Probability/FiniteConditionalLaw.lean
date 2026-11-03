module

public import Tournament.Probability.VectorKernel
public import Tournament.Probability.ProcessConditional
public import Mathlib.Probability.HasCondDistrib

@[expose] public section

namespace Tournament

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

noncomputable section

namespace ProbabilityVector

variable {Ω A : Type*} [Fintype Ω] [Fintype A]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

theorem hasLaw_of_mean (μ : ProbabilityVector Ω) (ν : ProbabilityVector A) (f : Ω → A)
    (hMean : ∀ g : A → ℝ, μ.mean (fun ω ↦ g (f ω))=ν.mean g) :
    HasLaw f ν.toMeasure μ.toMeasure := by
  refine ⟨(measurable_of_finite f).aemeasurable,?_⟩
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro a
  rw [← integral_indicator_one (measurableSet_singleton a),
    ← integral_indicator_one (measurableSet_singleton a),
    integral_map (measurable_of_finite f).aemeasurable (Measurable.of_discrete).aestronglyMeasurable,
    integral_toMeasure,integral_toMeasure]
  exact hMean _

theorem toMeasure_joint (μ : ProbabilityVector Ω) (κ : Ω → ProbabilityVector A)
    (hκ : ∀ i, Measurable (fun ω ↦ κ ω i)) :
    (μ.joint κ).toMeasure=μ.toMeasure ⊗ₘ ProbabilityVector.kernel κ hκ := by
  apply Measure.ext_of_singleton
  rintro ⟨ω,a⟩
  rw [toMeasure_singleton,← Set.singleton_prod_singleton,
    Measure.compProd_apply_prod (measurableSet_singleton ω) (measurableSet_singleton a),
    lintegral_singleton]
  simp only [ProbabilityVector.kernel_apply,toMeasure_singleton]
  change ENNReal.ofReal (μ ω*κ ω a)=_
  rw [ENNReal.ofReal_mul (μ.nonneg ω)]
  ring

end ProbabilityVector

namespace FiniteProcess

universe u
variable {Y : ℕ → Type u} [∀ n, Fintype (Y n)]

theorem prefix_hasLaw (κ : (b : ℕ) → History Y b → ProbabilityVector (Y b))
    (b B : ℕ) (h : b≤B) :
    HasLaw (past b B h) (law κ b).toMeasure (law κ B).toMeasure :=
  ProbabilityVector.hasLaw_of_mean (law κ B) (law κ b) (past b B h) (mean_prefix κ b B h)

variable [∀ n, MeasurableSpace (Y n)] [∀ n, DiscreteMeasurableSpace (Y n)]

theorem next_hasCondDistrib (κ : (b : ℕ) → History Y b → ProbabilityVector (Y b))
    (b B : ℕ) (h : b+1≤B) :
    HasCondDistrib (fun x ↦ (past (b+1) B h x).2) (past b B (by omega))
      (ProbabilityVector.kernel (κ b) (fun _ ↦ Measurable.of_discrete)) (law κ B).toMeasure := by
  have hPair : (fun x : History Y B ↦ (past b B (by omega) x,(past (b+1) B h x).2))=
      past (b+1) B h := by
    funext x
    apply Prod.ext
    · have hc := past_comp b (b+1) B (by omega) h x
      simpa only [past_succ b b le_rfl,past_self] using hc.symm
    · rfl
  change HasLaw _ (((law κ B).toMeasure.map (past b B (by omega))) ⊗ₘ _) (law κ B).toMeasure
  rw [(prefix_hasLaw κ b B (by omega)).map_eq,hPair,← ProbabilityVector.toMeasure_joint]
  exact ProbabilityVector.hasLaw_of_mean (law κ B) ((law κ b).joint (κ b))
    (past (b+1) B h) (mean_prefix κ (b+1) B h)

end FiniteProcess
end
end Tournament

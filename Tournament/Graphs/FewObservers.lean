module

public import Tournament.Graphs.FewObserverConstants
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section

namespace Tournament

open MeasureTheory
open scoped Classical unitInterval
noncomputable section

local instance : NormedSpace ℝ ℝ := @NormedField.toNormedSpace ℝ Real.normedField

variable {ι : Type*} [Fintype ι]

theorem few_observers (E : ι → ι → Prop) (hE : Observable E)
    (hK : 2≤Fintype.card ι)
    (hLarge : 32*Real.log (Fintype.card ι:ℝ)≤(dominationNumber E hE:ℝ)) :
    ∃ S : Finset ι,
      (dominationNumber E hE:ℝ)/(16*Real.log (Fintype.card ι:ℝ))≤(S.card:ℝ) ∧
      (∀ u∈S, ∀ v∈S, u≠v → ¬E u v) ∧
      (∀ a, ((observedMembers E S a).card:ℝ)≤1+Real.log (Fintype.card ι:ℝ)) := by
  obtain ⟨W,hW,hThin,hfn⟩ := ObserverThinning.exists_source_thin_set E hE hK hLarge
  let f := ObserverThinning.fraction (Fintype.card ι) (dominationNumber E hE)
  let q := ObserverSampling.samplingRate f (W.card:ℝ)
  have hRate := ObserverSampling.samplingRate_bounds f (W.card:ℝ) hfn
  let p : unitInterval := ⟨q,hRate.1.le,by linarith [hRate.2]⟩
  let k := ObserverSampling.threshold (Fintype.card ι)
  have hn : 0<(W.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hW
  have hf : 0<f := (ObserverThinning.fraction_bounds _ _ hK hLarge).2.1
  have hMean : (f*(W.card:ℝ))*q=1/4 := by
    dsimp [q,ObserverSampling.samplingRate]
    field_simp
  have hNq (a : ι) : ((observedMembers E W a).card:ℝ)*(p:ℝ)≤1/4 := by
    calc
      _ ≤ (f*(W.card:ℝ))*q := mul_le_mul_of_nonneg_right (hThin a) hRate.1.le
      _ = _ := hMean
  have hExpected := ObserverSampling.expected_survivors_ge E W p k f hThin hNq
  have hTail := ObserverSampling.threshold_tail_bound (Fintype.card ι) hK
  have hArithmetic := ObserverSampling.final_size_arithmetic
    (Fintype.card ι) (dominationNumber E hE) hK hLarge (W.card:ℝ) hn
  have hSize : (dominationNumber E hE:ℝ)/(16*Real.log (Fintype.card ι:ℝ))≤
      ∫ X, ((ObserverSampling.survivors E k (ObserverSampling.sample W X)).card:ℝ)
        ∂ObserverSampling.sampleLaw W p := by
    change q*(W.card:ℝ)-(Fintype.card ι:ℝ)*(4/3:ℝ)*(1/4:ℝ)^k-
      q^2*(W.card:ℝ)*f*(W.card:ℝ)≤_ at hExpected
    dsimp [k] at hExpected
    linarith
  obtain ⟨X,hX⟩ := exists_integral_le
    (Integrable.of_finite (μ := ObserverSampling.sampleLaw W p)
      (f := fun X ↦ ((ObserverSampling.survivors E k (ObserverSampling.sample W X)).card:ℝ)))
  refine ⟨ObserverSampling.survivors E k (ObserverSampling.sample W X),hSize.trans hX,?_,?_⟩
  · intro u hu v hv hne
    exact ObserverSampling.no_distinct_edges E k (ObserverSampling.sample W X) u v hu hv hne
  · intro a
    have hCount : ((observedMembers E
        (ObserverSampling.survivors E k (ObserverSampling.sample W X)) a).card:ℝ)≤((k-1:ℕ):ℝ) :=
      by exact_mod_cast ObserverSampling.surviving_observer_count E k (ObserverSampling.sample W X) a
    exact hCount.trans (ObserverSampling.threshold_observer_bound _ hK)

end
end Tournament

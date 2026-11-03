module

public import Tournament.Lower.AugmentedGaussianMean
public import Tournament.Lower.GaussianConditional

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory InformationTheory Model.MeasurableGame
open scoped Classical NNReal ENNReal

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

def transitionKernel (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    Kernel (Information Seed S t.val) (Coordinate S → ℝ) :=
  GaussianKL.gaussianKernel (transitionMean E θ j t) (transitionMean_measurable E θ j t)
    (incrementVariance T) (incrementVariance_ne_zero T (by have ht := t.isLt; omega))

instance transitionKernel_markov (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    IsMarkovKernel (transitionKernel (Seed := Seed) E θ j t) :=
  GaussianKL.gaussianKernel_markov _ _ _ _

theorem transitionObservation_conditional (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T) :
    HasCondDistrib (transitionObservation π E θ j t) (information π E θ j t)
      (transitionKernel E θ j t) (privateLaw ν S T) := by
  have hZ : HasLaw (fun p : Seed × WalkSign.Space T (Coordinate S) ↦
      GaussianProduct.currentSnapshot t p.2.2)
      (GaussianKL.productLaw (0 : Coordinate S → ℝ) (incrementVariance T)) (privateLaw ν S T) :=
    GaussianProduct.currentSnapshot_private_law ν T (incrementVariance T) t
  have h := GaussianKL.hasCondDistrib_shifted_innovation
    (information π E θ j t) (information_measurable π E θ j t)
    (fun p : Seed × WalkSign.Space T (Coordinate S) ↦ GaussianProduct.currentSnapshot t p.2.2)
    (transitionMean E θ j t) (transitionMean_measurable E θ j t)
    (incrementVariance T) (incrementVariance_ne_zero T (by have ht := t.isLt; omega)) hZ
    (information_innovation_independent ν π E θ j t)
  apply h.congr
  exact Filter.Eventually.of_forall (fun p ↦
    congrArg (fun x ↦ (information π E θ j t p,x)) (transitionObservation_identity π E θ j t p))

theorem transitionKernel_kl (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) (t : Fin T)
    (h : Information Seed S t.val) :
    klDiv (transitionKernel E θ (none : Coordinate S) t h) (transitionKernel E θ j t h)=
      ENNReal.ofReal (shiftEnergy (currentShift E θ j h-parentShift E θ j t h)/
        (2*(Parameters.sigma T)^2)) := by
  change klDiv (GaussianKL.productLaw (transitionMean E θ none t h) (incrementVariance T))
    (GaussianKL.productLaw (transitionMean E θ j t h) (incrementVariance T))=_
  rw [reference_transitionMean]
  have heq : transitionMean E θ j t h=
      parentObservation t h+(currentShift E θ j h-parentShift E θ j t h) := by
    unfold transitionMean
    abel
  rw [heq]
  exact gaussian_parent_shift_kl T (by have ht := t.isLt; omega) _ _ _

end
end Tournament.Lower

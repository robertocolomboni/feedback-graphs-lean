module

public import Tournament.Upper.AssignmentOptimum

@[expose] public section

namespace Tournament.Upper

open scoped BigOperators Classical

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem optimal_preparation_balanced (F : ι → ι → Prop) (hF : IsTournament F)
    (v w : ProbabilityVector ι) (hv : ∀ i, 0<v i) (hw : ∀ i, 0<w i)
    (hhalf : ∀ i, w i/2≤v i) (htwo : ∀ i, v i≤2*w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) :
    let A := optimizedAssignment F hF v hv
    let H := A.preparedFamily w hw κ hκ hκ32
    (∀ B : ComparisonAssignment F v, A.totalWeight≤B.totalWeight) ∧
      κ*H.maxRatio<1/4 ∧ (∀ i, w i≤(8/7)*H.sampling i) ∧
      (∑ i, |H.sampling i-w i|)≤8*κ ∧ 1≤128*v.anchorLog ∧
        BalancedEstimator F H w (A.estimator w H.sampling) (128*v.anchorLog) := by
  exact ⟨optimizedAssignment_isOptimal F hF v hv,
    (optimizedAssignment F hF v hv).balanced_estimator_from_assignment w hw hhalf htwo
      (optimizedAssignment_bounds F hF v hv).2 κ hκ hκ32⟩

theorem prepare_balanced (F : ι → ι → Prop) (hF : IsTournament F)
    (w : ProbabilityVector ι) (hw : ∀ i, 0<w i) (κ : ℝ) (hκ : 0<κ) (hκ32 : κ≤1/32) :
    let A := optimizedAssignment F hF w hw
    let H := A.preparedFamily w hw κ hκ hκ32
    (∀ B : ComparisonAssignment F w, A.totalWeight≤B.totalWeight) ∧
      κ*H.maxRatio<1/4 ∧ (∀ i, w i≤(8/7)*H.sampling i) ∧
      (∑ i, |H.sampling i-w i|)≤8*κ ∧ 1≤128*w.anchorLog ∧
        BalancedEstimator F H w (A.estimator w H.sampling) (128*w.anchorLog) :=
  optimal_preparation_balanced F hF w w hw hw (fun i ↦ by linarith [hw i])
    (fun i ↦ by linarith [hw i]) κ hκ hκ32

end
end Tournament.Upper

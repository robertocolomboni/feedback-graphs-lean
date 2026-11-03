module

public import Tournament.Model.ObservedCompletion

@[expose] public section

namespace Tournament.Model

open scoped Classical
noncomputable section

variable {ι : Type*}

def OrientationObserved (E F : ι → ι → Prop) : Prop :=
  ∀ s j, s≠j → F s j → E s s ∧ E s j

theorem selectedEdge_orientationObserved [LinearOrder ι] (E : ι → ι → Prop) :
    OrientationObserved E (selectedEdge E) := by
  intro s j hsj hF
  exact ((selectedEdge_ne E hsj).mp hF).1

theorem closedNeighborhood_comparison_of_observed (E F : ι → ι → Prop)
    (hObs : OrientationObserved E F) (s i j : ι)
    (hi : InClosedNeighborhood F s i) (hj : InClosedNeighborhood F s j) :
    DeterminesComparison E s i j := by
  by_cases hij : i=j
  · subst j; exact determinesComparison_self E s i
  · have hss : E s s := by
      by_cases his : i=s
      · have hjs : j≠s := fun hjs ↦ hij (his.trans hjs.symm)
        exact (hObs s j (Ne.symm hjs) (hj.resolve_left hjs)).1
      · exact (hObs s i (Ne.symm his) (hi.resolve_left his)).1
    apply determinesComparison_of_observed
    · rcases hi with rfl | hi
      · exact hss
      · by_cases his : i=s
        · simpa only [his] using hss
        · exact (hObs s i (Ne.symm his) hi).2
    · rcases hj with rfl | hj
      · exact hss
      · by_cases hjs : j=s
        · simpa only [hjs] using hss
        · exact (hObs s j (Ne.symm hjs) hj).2

theorem comparisonObservation_graphObservation_of_observed
    (E F : ι → ι → Prop) (hObs : OrientationObserved E F) (s : ι) (loss : ι → ℝ) :
    comparisonObservation F s (graphObservation E s loss)=comparisonObservation F s loss := by
  funext j
  by_cases hsj : s=j
  · subst j; simp [comparisonObservation]
  · by_cases hF : F s j
    · obtain ⟨hss,hsj⟩ := hObs s j hsj hF
      simp only [comparisonObservation,graphObservation,ite_eq_left hF,
        ite_eq_left hss,ite_eq_left hsj]
    · simp only [comparisonObservation,ite_eq_right hF]

theorem observedCompletion_preserves_comparison_of_observed {t : ℕ}
    (E F : ι → ι → Prop) (hObs : OrientationObserved E F)
    (actions : Fin t → ι) (loss : ℕ → ι → ℝ) (s : Fin t) :
    comparisonObservation F (actions s)
      (observedCompletion (fun r ↦ graphObservation E (actions r) (loss r.val)) s.val)=
      comparisonObservation F (actions s) (loss s.val) := by
  rw [observedCompletion_past]
  exact comparisonObservation_graphObservation_of_observed E F hObs _ _

end
end Tournament.Model

module

public import Tournament.Characterization.Intro
public import Tournament.Graphs.Feedback
public import Tournament.Graphs.FewObservers
public import Tournament.Lower.Main

@[expose] public section

namespace Tournament.Correspondence.MainLower

open MeasureTheory ProbabilityTheory
open Model.MeasurableGame Lower
open scoped Classical BigOperators NNReal

noncomputable section

universe u

theorem introductory_characterization {ι : Type u} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (E : ι → ι → Prop) (hK : 2 ≤ Fintype.card ι) (T : ℕ) (hT : 2 ≤ T) :
    (StronglyRevealing E →
      Real.sqrt (T : ℝ) / 4 ≤ minimax.{u,0} T E ∧
      minimax.{u,0} T E ≤
        ((2 : ℝ)^40 * Real.sqrt (Real.log (Fintype.card ι : ℝ)) *
          (Real.log (Real.exp 1 * (Fintype.card ι : ℝ) * (T : ℝ)))^2) *
            Real.sqrt (T : ℝ)) ∧
    (∀ hObs : Observable E, ¬StronglyRevealing E →
      Characterization.middleScale (dominationNumber E hObs) T /
        (5120 * (Real.log (2 * (T : ℝ)) / Real.log 2) *
          Real.log (Real.exp 1 * (Fintype.card ι : ℝ))) ≤ minimax.{u,0} T E ∧
      minimax.{u,0} T E ≤
        (5 * Real.log (Real.exp 1 * (Fintype.card ι : ℝ))) *
          Characterization.middleScale (dominationNumber E hObs) T) ∧
    (¬Observable E → (T : ℝ) / 4 ≤ minimax.{u,0} T E ∧
      minimax.{u,0} T E ≤ (T : ℝ)) :=
  ⟨fun hE ↦ Characterization.intro_strongly_revealing E hE hK T hT,
    fun hObs hNot ↦ Characterization.intro_observable_nonrevealing E hObs hNot hK T hT,
    fun hNot ↦ Characterization.intro_nonobservable E hNot hK T⟩

theorem graph_structure {ι : Type*} (E : ι → ι → Prop) :
    (StronglyRevealing E → StronglyObservable E) ∧
    (StronglyObservable E →
      (StronglyRevealing E ↔
        (∀ i j, ¬BanditPair E i j) ∧ (∀ i j, ¬LooplessPair E i j))) :=
  ⟨stronglyRevealing_implies_stronglyObservable,
    stronglyRevealing_iff_no_forbidden_pairs⟩

theorem reduction_to_observable_comparisons {ι : Type*} [Fintype ι]
    (E : ι → ι → Prop) :
    (StronglyRevealing E ↔ ∃ F : ι → ι → Prop,
      (∀ i j, F i j → E i j) ∧ IsTournament F ∧ StronglyObservable F) ∧
    (StronglyRevealing E → ∃ F : ι → ι → Prop,
      (∀ i j, F i j → E i j) ∧ IsTournament F ∧ StronglyObservable F ∧
        (∀ s j, F s j → DeterminesComparison E s s j)) := by
  let : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  refine ⟨stronglyRevealing_iff_spanning_tournament E, ?_⟩
  intro hE
  exact ⟨selectedEdge E, fun _ _ h ↦ selectedEdge_subgraph E h,
    selectedEdge_isTournament hE, selectedEdge_stronglyObservable hE,
    fun _ _ h ↦ selectedEdge_determinesComparison h⟩

theorem depth_and_congestion {C α : Type*} [Fintype C] [DecidableEq α]
    (T : ℕ) (hT : 2 ≤ T) (v : ℝ≥0) :
    (∀ t, t ≤ T → ((Dyadic.ancestors t).length : ℝ) ≤ Dyadic.upsilon T) ∧
    (∀ (c : C) t, t ≤ T →
      Var[GaussianProduct.walk c t; GaussianProduct.law T v] ≤
        Dyadic.upsilon T * (v : ℝ)) ∧
    (∀ u, ((Dyadic.children T u).card : ℝ) ≤ Dyadic.upsilon T) ∧
    (∀ I : ℕ → α,
      ((∑ t ∈ Finset.Icc 1 T,
        Dyadic.changed (Dyadic.padded I) (Dyadic.parent t) t) : ℝ) ≤
        Dyadic.upsilon T * ((Model.switchCount T I : ℝ) + 1)) := by
  exact ⟨fun t ht ↦ Dyadic.ancestor_depth T t (by omega) ht,
    fun c t ht ↦ GaussianProduct.walk_variance T v c t (by omega) ht,
    fun u ↦ Dyadic.children_card_le_upsilon T u (by omega),
    fun I ↦ Dyadic.parent_changes_le_switchCount I T (by omega)⟩

theorem clipping_error {ι : Type*} {S : Finset ι} {T : ℕ}
    (hT : 2 ≤ T) (hST : S.card ≤ T) (m : ℝ) (hm : 1 ≤ m)
    (j : Coordinate S) :
    (∫ ω, ∑ t : Fin T, ∑ v : S,
      clippingError (RealParameters.theta T S.card m) j t v ω
        ∂environmentLaw S T) ≤ 1 / 1024 :=
  clipping_error_sum hT hST _
    ⟨RealParameters.theta_nonneg T S.card m (by omega) hm,
      RealParameters.theta_le_one_sixty_four T S.card m hT hST hm⟩ j

theorem reconstruction {ι : Type*} (E : ι → ι → Prop) (S : Finset ι)
    (hS : SparseMembers E S) :
    ∃ decode : ι → ℝ → (Coordinate S → ℝ) → ι → ℝ,
      ∀ (j : Coordinate S) (θ : ℝ) (a : ι) (sign : ℝ), sign ^ 2 = 1 →
        ∀ (x : Coordinate S → ℝ) (v : ι), E a v →
          decode a sign (augmented E θ j a sign x) v =
            environmentLoss θ j sign x v := by
  refine ⟨feedbackDecoder E S, ?_⟩
  intro j θ a sign hsign x v hav
  simpa only [ite_eq_left hav] using feedback_reconstruction hS θ j a sign hsign x v

theorem regret {ι Seed : Type*} [MeasurableSpace ι]
    [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι] [MeasurableSpace Seed]
    {S : Finset ι} {T : ℕ} (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hT : 2 ≤ T) (hST : S.card ≤ T) (hS : 2 ≤ S.card)
    (m : ℝ) (hm : 1 ≤ m) (π : Learner ι Seed) (E : ι → ι → Prop) :
    let θ := RealParameters.theta T S.card m
    ((∫ p, switchTotal (T := T) π E θ (none : Coordinate S) p ∂privateLaw ν S T) +
      (1 / 4) * (∫ p, outsideVisits (T := T) π E θ (none : Coordinate S) p
        ∂privateLaw ν S T) - 1 / 512 ≤
      expectedRegret (T := T) ν π E θ (none : Coordinate S)) ∧
    (∀ j : S, θ * ((T : ℝ) - (∫ p, visits (T := T) π E θ (some j) j p
      ∂privateLaw ν S T)) - 1 / 512 ≤ expectedRegret (T := T) ν π E θ (some j)) := by
  have hθ : 0 ≤ RealParameters.theta T S.card m ∧
      RealParameters.theta T S.card m ≤ 1 / 64 :=
    ⟨RealParameters.theta_nonneg T S.card m (by omega) hm,
      RealParameters.theta_le_one_sixty_four T S.card m hT hST hm⟩
  have hSN : S.Nonempty := Finset.card_pos.mp (by omega)
  let v : S := ⟨hSN.choose, hSN.choose_spec⟩
  exact ⟨lower_regret_reference ν hT hST π E _ hθ v,
    fun j ↦ lower_regret_candidate ν hT hST π E _ hθ j⟩

end
end Tournament.Correspondence.MainLower

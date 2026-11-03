module

public import Tournament.Lower.BayesRegret
public import Tournament.Lower.RealParameters

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory InformationTheory Model.MeasurableGame
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

theorem kl_budget_identity_real (T : ℕ) (m : ℝ) (hT : 1≤T) (θ : ℝ) :
    (2*m*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*(2*θ*(T:ℝ))=
      1024*m*Dyadic.upsilon T^3*θ^3*(T:ℝ) := by
  have hU : Dyadic.upsilon T≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Parameters.upsilon_ge_one T hT))
  unfold Parameters.sigma
  field_simp
  ring

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

omit [Nonempty ι] in
theorem small_reference_cost_kl_real (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 2≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (hn : 1≤S.card)
    (m : ℝ) (hm : 1≤m) (hobs : ∀ a, ((observed E S a).card:ℝ)≤m)
    (hlarge : 1≤RealParameters.theta T S.card m*(T:ℝ))
    (hcost : referenceCost (S := S) (T := T) ν π E (RealParameters.theta T S.card m)<RealParameters.theta T S.card m*(T:ℝ)/4) :
    (∑ j : S, transcriptDivergence (T := T) ν π E (RealParameters.theta T S.card m) (some j))<(S.card:ℝ)/32 := by
  let θ := RealParameters.theta T S.card m
  have hθ : 0<θ := RealParameters.theta_pos T S.card m (by omega) hn hm
  have hU := Parameters.upsilon_ge_one T (by omega)
  have hσ := Parameters.sigma_pos T (by omega)
  have hC : 0<2*m*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2 := by positivity
  have hInfo := small_reference_information_cost ν π E θ hlarge hcost
  calc
    _ ≤ (2*m*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*
        referenceInformationCost (S := S) (T := T) ν π E θ := lower_kl_toReal_real ν (by omega) π E hS θ m hm hobs
    _ < (2*m*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*(2*θ*(T:ℝ)) :=
      mul_lt_mul_of_pos_left hInfo hC
    _ = _ := by rw [kl_budget_identity_real T m (by omega),RealParameters.theta_cube_identity T S.card m (by omega) hm]

theorem bayes_regret_real (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 2≤T) (hST : S.card≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (hn : 2≤S.card)
    (m : ℝ) (hm : 1≤m) (hobs : ∀ a, ((observed E S a).card:ℝ)≤m)
    (hlarge : 1≤RealParameters.theta T S.card m*(T:ℝ)) :
    let θ := RealParameters.theta T S.card m
    θ*(T:ℝ)/8≤max (expectedRegret (T := T) ν π E θ (none : Coordinate S))
      ((∑ j : S, expectedRegret (T := T) ν π E θ (some j))/(S.card:ℝ)) := by
  let θ := RealParameters.theta T S.card m
  change θ*(T:ℝ)/8≤max _ _
  change 1≤θ*(T:ℝ) at hlarge
  have hθ : 0≤θ ∧ θ≤1/64 :=
    ⟨RealParameters.theta_nonneg T S.card m (by omega) hm,RealParameters.theta_le_one_sixty_four T S.card m hT hST hm⟩
  have hSN : S.Nonempty := Finset.card_pos.mp (by omega)
  let v : S := ⟨hSN.choose,hSN.choose_spec⟩
  by_cases hcost : θ*(T:ℝ)/4≤referenceCost (S := S) (T := T) ν π E θ
  · have hR := lower_regret_reference ν hT hST π E θ hθ v
    change referenceCost (S := S) (T := T) ν π E θ-1/512≤_ at hR
    exact (show θ*(T:ℝ)/8≤expectedRegret (T := T) ν π E θ (none : Coordinate S) by linarith).trans (le_max_left _ _)
  · have hKL := small_reference_cost_kl_real ν hT π E hS (by omega) m hm hobs hlarge (lt_of_not_ge hcost)
    have hVisits := visits_average_lt_five_eighths ν (by omega) π E hS θ hn hKL
    have hn0 : 0<(Fintype.card S:ℝ) := by
      rw [Fintype.card_coe]
      exact_mod_cast (by omega : 0<S.card)
    have hAvg := average_candidate_regret
      (fun j : S ↦ ∫ p, visits (T := T) π E θ (some j) j p ∂privateLaw ν S T)
      (fun j : S ↦ expectedRegret (T := T) ν π E θ (some j)) θ (T:ℝ) hn0 hθ.1 hlarge
      (by simpa only [Fintype.card_coe] using hVisits.le)
      (fun j ↦ lower_regret_candidate ν hT hST π E θ hθ j)
    have hAvg' : θ*(T:ℝ)/8≤(∑ j : S, expectedRegret (T := T) ν π E θ (some j))/(S.card:ℝ) := by
      simpa only [Fintype.card_coe] using hAvg
    exact hAvg'.trans (le_max_right _ _)

end
end Tournament.Lower

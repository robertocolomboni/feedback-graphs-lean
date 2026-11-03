module

public import Tournament.Lower.BayesVisits

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory InformationTheory Model.MeasurableGame
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

theorem average_candidate_regret {J : Type*} [Fintype J] (V R : J → ℝ) (θ T : ℝ)
    (hn : 0<(Fintype.card J:ℝ)) (hθ : 0≤θ) (hlarge : 1≤θ*T)
    (hVisits : (∑ j, V j)/(Fintype.card J:ℝ)≤5*T/8)
    (hReg : ∀ j, θ*(T-V j)-1/512≤R j) :
    θ*T/8≤(∑ j, R j)/(Fintype.card J:ℝ) := by
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hReg j)
  have hformula : (∑ j, (θ*(T-V j)-1/512))=
      (Fintype.card J:ℝ)*(θ*T-1/512)-θ*(∑ j, V j) := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  rw [hformula] at hSum
  have havg : θ*(T-(∑ j, V j)/(Fintype.card J:ℝ))-1/512≤(∑ j, R j)/(Fintype.card J:ℝ) := by
    calc
      _ = ((Fintype.card J:ℝ)*(θ*T-1/512)-θ*(∑ j, V j))/(Fintype.card J:ℝ) := by
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hSum hn.le
  have hθV := mul_le_mul_of_nonneg_left hVisits hθ
  nlinarith

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

def referenceCost (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) : ℝ :=
  (∫ p, switchTotal (T := T) π E θ (none : Coordinate S) p ∂privateLaw ν S T)+
    (1/4)*(∫ p, outsideVisits (T := T) π E θ (none : Coordinate S) p ∂privateLaw ν S T)

def referenceInformationCost (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) : ℝ :=
  ∫ p, switchTotal (T := T) π E θ (none : Coordinate S) p+
    outsideVisits (T := T) π E θ (none : Coordinate S) p+1 ∂privateLaw ν S T

theorem small_reference_information_cost (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ) (hlarge : 1≤θ*(T:ℝ))
    (hcost : referenceCost (S := S) (T := T) ν π E θ<θ*(T:ℝ)/4) :
    referenceInformationCost (S := S) (T := T) ν π E θ<2*θ*(T:ℝ) := by
  have hN := switchTotal_integrable (T := T) ν π E θ (none : Coordinate S)
  have hO := outsideVisits_integrable (T := T) ν π E θ (none : Coordinate S)
  have hNN : 0≤∫ p, switchTotal (T := T) π E θ (none : Coordinate S) p ∂privateLaw ν S T :=
    integral_nonneg (switchTotal_nonneg π E θ (none : Coordinate S))
  unfold referenceInformationCost
  rw [integral_add (f := fun p ↦ switchTotal (T := T) π E θ (none : Coordinate S) p+
      outsideVisits (T := T) π E θ (none : Coordinate S) p) (g := fun _ ↦ (1:ℝ))
      (hN.add hO) (integrable_const (1:ℝ)),integral_add hN hO,integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  unfold referenceCost at hcost
  linarith

theorem kl_budget_identity (T m : ℕ) (hT : 1≤T) (θ : ℝ) :
    (2*(m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*(2*θ*(T:ℝ))=
      1024*(m:ℝ)*Dyadic.upsilon T^3*θ^3*(T:ℝ) := by
  have hU : Dyadic.upsilon T≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Parameters.upsilon_ge_one T hT))
  unfold Parameters.sigma
  field_simp
  ring

theorem small_reference_cost_kl (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 2≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (hn : 1≤S.card)
    (m : ℕ) (hm : 1≤m) (hobs : ∀ a, (observed E S a).card≤m)
    (hlarge : 1≤Parameters.theta T S.card m*(T:ℝ))
    (hcost : referenceCost (S := S) (T := T) ν π E (Parameters.theta T S.card m)<Parameters.theta T S.card m*(T:ℝ)/4) :
    (∑ j : S, transcriptDivergence (T := T) ν π E (Parameters.theta T S.card m) (some j))<(S.card:ℝ)/32 := by
  let θ := Parameters.theta T S.card m
  have hθ : 0<θ := Parameters.theta_pos T S.card m (by omega) hn hm
  have hU := Parameters.upsilon_ge_one T (by omega)
  have hm0 : 0<(m:ℝ) := by exact_mod_cast (by omega : 0<m)
  have hσ := Parameters.sigma_pos T (by omega)
  have hC : 0<2*(m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2 := by positivity
  have hInfo := small_reference_information_cost ν π E θ hlarge hcost
  calc
    _ ≤ (2*(m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*
        referenceInformationCost (S := S) (T := T) ν π E θ := lower_kl_toReal ν (by omega) π E hS θ m hobs
    _ < (2*(m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*(2*θ*(T:ℝ)) :=
      mul_lt_mul_of_pos_left hInfo hC
    _ = _ := by rw [kl_budget_identity T m (by omega),Parameters.theta_cube_identity T S.card m (by omega) hm]

theorem bayes_regret [Nonempty ι] (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 2≤T) (hST : S.card≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (hn : 2≤S.card)
    (m : ℕ) (hm : 1≤m) (hobs : ∀ a, (observed E S a).card≤m)
    (hlarge : 1≤Parameters.theta T S.card m*(T:ℝ)) :
    let θ := Parameters.theta T S.card m
    θ*(T:ℝ)/8≤max (expectedRegret (T := T) ν π E θ (none : Coordinate S))
      ((∑ j : S, expectedRegret (T := T) ν π E θ (some j))/(S.card:ℝ)) := by
  let θ := Parameters.theta T S.card m
  change θ*(T:ℝ)/8≤max _ _
  change 1≤θ*(T:ℝ) at hlarge
  have hθ : 0≤θ ∧ θ≤1/64 :=
    ⟨Parameters.theta_nonneg T S.card m (by omega),Parameters.theta_le_one_sixty_four T S.card m hT hST hm⟩
  have hSN : S.Nonempty := Finset.card_pos.mp (by omega)
  let v : S := ⟨hSN.choose,hSN.choose_spec⟩
  by_cases hcost : θ*(T:ℝ)/4≤referenceCost (S := S) (T := T) ν π E θ
  · have hR := lower_regret_reference ν hT hST π E θ hθ v
    change referenceCost (S := S) (T := T) ν π E θ-1/512≤_ at hR
    exact (show θ*(T:ℝ)/8≤expectedRegret (T := T) ν π E θ (none : Coordinate S) by linarith).trans (le_max_left _ _)
  · have hKL := small_reference_cost_kl ν hT π E hS (by omega) m hm hobs hlarge (lt_of_not_ge hcost)
    have hVisits := visits_average_le_five_eighths ν π E hS θ hn hKL
    have hn0 : 0<(Fintype.card S:ℝ) := by
      rw [Fintype.card_coe]
      exact_mod_cast (by omega : 0<S.card)
    have hAvg := average_candidate_regret
      (fun j : S ↦ ∫ p, visits (T := T) π E θ (some j) j p ∂privateLaw ν S T)
      (fun j : S ↦ expectedRegret (T := T) ν π E θ (some j)) θ (T:ℝ) hn0 hθ.1 hlarge
      (by simpa only [Fintype.card_coe] using hVisits)
      (fun j ↦ lower_regret_candidate ν hT hST π E θ hθ j)
    have hAvg' : θ*(T:ℝ)/8≤(∑ j : S, expectedRegret (T := T) ν π E θ (some j))/(S.card:ℝ) := by
      simpa only [Fintype.card_coe] using hAvg
    exact hAvg'.trans (le_max_right _ _)

end
end Tournament.Lower

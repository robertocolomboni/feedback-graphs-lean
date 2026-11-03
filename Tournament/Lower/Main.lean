module

public import Tournament.Lower.ObliviousExtraction
public import Tournament.Lower.FirstRound
public import Tournament.Lower.RealBayesRegret

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory Model.MeasurableGame
open scoped Classical NNReal BigOperators

noncomputable section

theorem exists_ge_finite_average {J : Type*} [Fintype J] [Nonempty J] (f : J → ℝ) :
    ∃ j, (∑ k, f k)/(Fintype.card J:ℝ)≤f j := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨j,?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k hk ↦ hj k hk)
  have hn : 0<(Fintype.card J:ℝ) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card J)
  apply (div_le_iff₀ hn).mpr
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hsum

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

theorem lower_bound_gap (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 2≤T) (hST : S.card≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (hn : 2≤S.card)
    (m : ℝ) (hm : 1≤m) (hobs : ∀ a, ((observed E S a).card:ℝ)≤m) :
    ∃ loss : ℕ → ι → ℝ, (∀ t a, 0≤loss t a ∧ loss t a≤1) ∧
      RealParameters.theta T S.card m*(T:ℝ)/8≤deterministicExpectedRegret T ν π E loss := by
  let θ := RealParameters.theta T S.card m
  by_cases hlarge : 1≤θ*(T:ℝ)
  · have h := bayes_regret_real ν hT hST π E hS hn m hm hobs hlarge
    rcases le_max_iff.mp h with h0 | hmix
    · obtain ⟨loss,hbound,hreg⟩ := exists_oblivious_loss_ge_environment (T := T) ν π E θ (none : Coordinate S)
      exact ⟨loss,hbound,h0.trans hreg⟩
    · have hSN : S.Nonempty := Finset.card_pos.mp (by omega)
      let : Nonempty S := ⟨⟨hSN.choose,hSN.choose_spec⟩⟩
      obtain ⟨j,hj⟩ := exists_ge_finite_average (fun j : S ↦ expectedRegret (T := T) ν π E θ (some j))
      have hj' : θ*(T:ℝ)/8≤expectedRegret (T := T) ν π E θ (some j) :=
        hmix.trans (by simpa only [Fintype.card_coe] using hj)
      obtain ⟨loss,hbound,hreg⟩ := exists_oblivious_loss_ge_environment (T := T) ν π E θ (some j)
      exact ⟨loss,hbound,hj'.trans hreg⟩
  · obtain ⟨a,_,b,_,hab⟩ := Finset.one_lt_card.mp (by omega : 1<S.card)
    obtain ⟨loss,hbound,hreg⟩ := exists_oblivious_loss_half T (by omega) ν π E a b hab
    refine ⟨loss,hbound,?_⟩
    have hsmall := lt_of_not_ge hlarge
    exact (show θ*(T:ℝ)/8≤(1:ℝ)/2 by linarith).trans hreg

theorem lower_bound_capped (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 2≤T) (hST : S.card≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (hn : 2≤S.card)
    (m : ℝ) (hm : 1≤m) (hobs : ∀ a, ((observed E S a).card:ℝ)≤m) :
    ∃ loss : ℕ → ι → ℝ, (∀ t a, 0≤loss t a ∧ loss t a≤1) ∧
      (T:ℝ)^((2:ℝ)/3)*((S.card:ℝ)/m)^((1:ℝ)/3)/(256*Dyadic.upsilon T)≤
        deterministicExpectedRegret T ν π E loss := by
  obtain ⟨loss,hbound,hreg⟩ := lower_bound_gap ν hT hST π E hS hn m hm hobs
  refine ⟨loss,hbound,?_⟩
  rwa [RealParameters.theta_time_identity T S.card m (by omega) hm] at hreg

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι] [MeasurableSpace Seed] in
theorem observed_mono (E : ι → ι → Prop) {S' S : Finset ι} (hsub : S'⊆S) (a : ι) :
    observed E S' a⊆observed E S a := fun _ h ↦
  Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2⟩

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [Nonempty ι] [MeasurableSpace Seed] in
theorem sparseMembers_mono (E : ι → ι → Prop) {S' S : Finset ι} (hsub : S'⊆S) (hS : SparseMembers E S) :
    SparseMembers E S' := by
  intro a ha
  exact (Finset.card_le_card (observed_mono E hsub a)).trans (hS a (hsub ha))

theorem lower_bound (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 2≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (hn : 2≤S.card)
    (m : ℝ) (hm : 1≤m) (hobs : ∀ a, ((observed E S a).card:ℝ)≤m) :
    ∃ loss : ℕ → ι → ℝ, (∀ t a, 0≤loss t a ∧ loss t a≤1) ∧
      (T:ℝ)^((2:ℝ)/3)*((min S.card T:ℝ)/m)^((1:ℝ)/3)/(256*Dyadic.upsilon T)≤
        deterministicExpectedRegret T ν π E loss := by
  obtain ⟨S',hsub,hcard⟩ := Finset.exists_subset_card_eq (min_le_left S.card T)
  have hn' : 2≤S'.card := by rw [hcard]; omega
  have hST : S'.card≤T := by rw [hcard]; exact min_le_right _ _
  have hobs' : ∀ a, ((observed E S' a).card:ℝ)≤m := by
    intro a
    have hcount : ((observed E S' a).card:ℝ)≤((observed E S a).card:ℝ) :=
      by exact_mod_cast Finset.card_le_card (observed_mono E hsub a)
    exact hcount.trans (hobs a)
  obtain ⟨loss,hbound,hreg⟩ := lower_bound_capped ν hT hST π E (sparseMembers_mono E hsub hS) hn' m hm hobs'
  refine ⟨loss,hbound,?_⟩
  simpa only [hcard,Nat.cast_min] using hreg

end
end Tournament.Lower

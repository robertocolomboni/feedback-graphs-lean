module

public import Tournament.Lower.TranscriptEnergy

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory InformationTheory Model.MeasurableGame
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

theorem sum_range_one_based (f : ℕ → ℝ) (n : ℕ) :
    (∑ s∈Finset.range n, f (s+1))=∑ s∈Finset.Icc 1 n, f s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega : 1≤n+1),ih]

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem sample_energy_congestion (hT : 1≤T) (π : Learner ι Seed) (E : ι → ι → Prop) (θ : ℝ)
    (m : ℕ) (hm : ∀ a, (observed E S a).card≤m) (p : Seed × WalkSign.Space T (Coordinate S)) :
    (∑ t : Fin T, ∑ j : S, sampleConditionalEnergy π E θ (some j) t p)≤
      (2*(m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*
        ((Model.switchCount T (observedActionPath π E θ none p):ℝ)+
          (outsideCount S T (observedActionPath π E θ none p):ℝ)+1) := by
  let I := observedActionPath π E θ (none : Coordinate S) p
  let sign := observedSignPath p
  let f : ℕ → ℝ := fun s ↦ ∑ j : S,
    shiftEnergy (timeShift E θ (some j) I sign s-timeShift E θ (some j) I sign (Dyadic.parent s))
  have heq : (∑ t : Fin T, ∑ j : S, sampleConditionalEnergy π E θ (some j) t p)=
      (∑ s∈Finset.Icc 1 T, f s)/(2*(Parameters.sigma T)^2) := by
    simp_rw [sampleConditionalEnergy_eq_shift,← Finset.sum_div]
    change (∑ t : Fin T, f (t.val+1))/(2*(Parameters.sigma T)^2)=_
    rw [Fin.sum_univ_eq_sum_range (fun s ↦ f (s+1)),sum_range_one_based]
  rw [heq]
  have h := shift_congestion_source E θ m hm I sign (observedSignPath_square p) T hT
  have hd : 0≤2*(Parameters.sigma T)^2 := by positivity
  calc
    _ ≤ (4*(m:ℝ)*θ^2*Dyadic.upsilon T*
        ((Model.switchCount T I:ℝ)+(outsideCount S T I:ℝ)+1))/(2*(Parameters.sigma T)^2) :=
      div_le_div_of_nonneg_right h hd
    _ = _ := by ring

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem observed_switches_equal (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S)
    (θ : ℝ) (j : Coordinate S) (p : Seed × WalkSign.Space T (Coordinate S)) :
    (Model.switchCount T (observedActionPath π E θ j p):ℝ)=switchTotal π E θ j p := by
  unfold Model.switchCount switchTotal
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hsT : s+1≤T := by have hh := Finset.mem_range.mp hs; omega
  rw [observedActionPath,augmented_action_eq_original π E hS θ j (s+1) hsT p,
    observedActionPath,augmented_action_eq_original π E hS θ j s (by omega) p]

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem observed_outside_equal (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S)
    (θ : ℝ) (j : Coordinate S) (p : Seed × WalkSign.Space T (Coordinate S)) :
    (outsideCount S T (observedActionPath π E θ j p):ℝ)=outsideVisits π E θ j p := by
  rw [outsideVisits_eq_outsideCount]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hsT : s≤T := (Finset.mem_range.mp hs).le
  rw [observedActionPath,augmented_action_eq_original π E hS θ j s hsT p]

theorem lower_kl_toReal (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 1≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (θ : ℝ)
    (m : ℕ) (hm : ∀ a, (observed E S a).card≤m) :
    (∑ j : S, (klDiv (augmentedTranscriptLaw (T := T) ν π E θ none)
      (augmentedTranscriptLaw (T := T) ν π E θ (some j))).toReal)≤
      (2*(m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*
        (∫ p, switchTotal (T := T) π E θ none p+outsideVisits (T := T) π E θ none p+1 ∂privateLaw ν S T) := by
  rw [augmented_kl_sum_toReal]
  have hN := switchTotal_integrable (T := T) ν π E θ (none : Coordinate S)
  have hO := outsideVisits_integrable (T := T) ν π E θ (none : Coordinate S)
  have hL : Integrable (fun p ↦ ∑ t : Fin T, ∑ j : S, sampleConditionalEnergy π E θ (some j) t p)
      (privateLaw ν S T) :=
    integrable_finsetSum _ (fun t _ ↦ integrable_finsetSum _
      (fun j _ ↦ sampleConditionalEnergy_integrable ν π E θ (some j) t))
  have hR := ((hN.add hO).add (integrable_const (1:ℝ))).const_mul
    (2*(m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)
  calc
    _ ≤ ∫ p, (2*(m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*
        (switchTotal π E θ none p+outsideVisits π E θ none p+1) ∂privateLaw ν S T := by
      apply integral_mono hL hR
      intro p
      have h := sample_energy_congestion hT π E θ m hm p
      rw [observed_switches_equal π E hS,observed_outside_equal π E hS] at h
      exact h
    _ = _ := integral_const_mul _ _

theorem lower_kl (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 1≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (θ : ℝ)
    (m : ℕ) (hm : ∀ a, (observed E S a).card≤m) :
    (∑ j : S, klDiv (augmentedTranscriptLaw (T := T) ν π E θ none)
      (augmentedTranscriptLaw (T := T) ν π E θ (some j)))≤
      ENNReal.ofReal ((2*(m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*
        (∫ p, switchTotal (T := T) π E θ none p+outsideVisits (T := T) π E θ none p+1 ∂privateLaw ν S T)) := by
  have heq : (∑ j : S, klDiv (augmentedTranscriptLaw (T := T) ν π E θ none)
      (augmentedTranscriptLaw (T := T) ν π E θ (some j)))=
      ENNReal.ofReal (∑ j : S, (klDiv (augmentedTranscriptLaw (T := T) ν π E θ none)
        (augmentedTranscriptLaw (T := T) ν π E θ (some j))).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ ENNReal.toReal_nonneg)]
    apply Finset.sum_congr rfl
    intro j _
    exact (ENNReal.ofReal_toReal (augmented_kl_ne_top ν π E θ (some j))).symm
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (lower_kl_toReal ν hT π E hS θ m hm)

theorem lower_kl_toReal_real (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 1≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (θ m : ℝ)
    (hm : 1≤m) (hobs : ∀ a, ((observed E S a).card:ℝ)≤m) :
    (∑ j : S, (klDiv (augmentedTranscriptLaw (T := T) ν π E θ none)
      (augmentedTranscriptLaw (T := T) ν π E θ (some j))).toReal)≤
      (2*m*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*
        (∫ p, switchTotal (T := T) π E θ none p+outsideVisits (T := T) π E θ none p+1 ∂privateLaw ν S T) := by
  have hNat : ∀ a, (observed E S a).card≤Nat.floor m := fun a ↦ Nat.le_floor (hobs a)
  have hU := Parameters.upsilon_ge_one T hT
  have hfloor : (Nat.floor m:ℝ)≤m := Nat.floor_le (by linarith)
  have hC : 2*(Nat.floor m:ℝ)*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2≤
      2*m*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2 := by gcongr
  have hN : 0≤∫ p, switchTotal (T := T) π E θ (none : Coordinate S) p+
      outsideVisits (T := T) π E θ none p+1 ∂privateLaw ν S T := by
    apply integral_nonneg
    intro p
    change 0≤switchTotal (T := T) π E θ (none : Coordinate S) p+outsideVisits (T := T) π E θ none p+1
    have hswitch := switchTotal_nonneg π E θ (none : Coordinate S) p
    have hout := outsideVisits_nonneg π E θ (none : Coordinate S) p
    linarith
  exact (lower_kl_toReal ν hT π E hS θ (Nat.floor m) hNat).trans (mul_le_mul_of_nonneg_right hC hN)

theorem lower_kl_real (ν : Measure Seed) [IsProbabilityMeasure ν] (hT : 1≤T)
    (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S) (θ m : ℝ)
    (hm : 1≤m) (hobs : ∀ a, ((observed E S a).card:ℝ)≤m) :
    (∑ j : S, klDiv (augmentedTranscriptLaw (T := T) ν π E θ none)
      (augmentedTranscriptLaw (T := T) ν π E θ (some j)))≤
      ENNReal.ofReal ((2*m*θ^2*Dyadic.upsilon T/(Parameters.sigma T)^2)*
        (∫ p, switchTotal (T := T) π E θ none p+outsideVisits (T := T) π E θ none p+1 ∂privateLaw ν S T)) := by
  have heq : (∑ j : S, klDiv (augmentedTranscriptLaw (T := T) ν π E θ none)
      (augmentedTranscriptLaw (T := T) ν π E θ (some j)))=
      ENNReal.ofReal (∑ j : S, (klDiv (augmentedTranscriptLaw (T := T) ν π E θ none)
        (augmentedTranscriptLaw (T := T) ν π E θ (some j))).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ ENNReal.toReal_nonneg)]
    apply Finset.sum_congr rfl
    intro j _
    exact (ENNReal.ofReal_toReal (augmented_kl_ne_top ν π E θ (some j))).symm
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (lower_kl_toReal_real ν hT π E hS θ m hm hobs)

end
end Tournament.Lower

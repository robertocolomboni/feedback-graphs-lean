module

public import Tournament.Lower.LowerKL
public import Tournament.Probability.Pinsker

@[expose] public section

namespace Tournament.Lower

open MeasureTheory ProbabilityTheory InformationTheory Model.MeasurableGame
open scoped Classical NNReal ENNReal BigOperators

noncomputable section

variable {ι Seed : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι]
variable [MeasurableSpace Seed] {S : Finset ι} {T : ℕ}

def transcriptVisits (v : S) (h : Seed × SensorHistory ι (AugmentedSignal S) T) : ℝ :=
  ∑ t : Fin T, if (h.2 t).1=v.val then 1 else 0

theorem transcriptVisits_measurable (v : S) : Measurable (transcriptVisits (Seed := Seed) (T := T) v) := by
  apply Finset.measurable_sum
  intro t _
  exact Measurable.ite ((measurableSet_singleton v.val).preimage
    (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd))) measurable_const measurable_const

omit [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Fintype ι] [MeasurableSpace Seed] in
theorem transcriptVisits_bounds (v : S) (h : Seed × SensorHistory ι (AugmentedSignal S) T) :
    0≤transcriptVisits v h ∧ transcriptVisits v h≤(T:ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ _ : Fin T, (1:ℝ) := Finset.sum_le_sum (fun _ _ ↦ by split_ifs <;> norm_num)
      _ = _ := by simp

omit [DiscreteMeasurableSpace ι] [Fintype ι] in
theorem transcriptVisits_actual (π : Learner ι Seed) (E : ι → ι → Prop) (hS : SparseMembers E S)
    (θ : ℝ) (j : Coordinate S) (v : S) (p : Seed × WalkSign.Space T (Coordinate S)) :
    transcriptVisits v (augmentedTranscript π E θ j p)=visits π E θ j v p := by
  apply Finset.sum_congr rfl
  intro t _
  simp only [augmentedTranscript,augmentedHistory_actions π E hS,memberIndicator]

theorem transcriptVisits_integral (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (hS : SparseMembers E S) (θ : ℝ) (j : Coordinate S) (v : S) :
    (∫ h, transcriptVisits (T := T) v h ∂augmentedTranscriptLaw (T := T) ν π E θ j)=
      ∫ p, visits (T := T) π E θ j v p ∂privateLaw ν S T := by
  have hLaw : HasLaw (augmentedTranscript (T := T) π E θ j) (augmentedTranscriptLaw (T := T) ν π E θ j)
      (privateLaw ν S T) := ⟨(augmentedTranscript_measurable π E θ j).aemeasurable,rfl⟩
  calc
    _ = ∫ p, transcriptVisits v (augmentedTranscript π E θ j p) ∂privateLaw ν S T :=
      (hLaw.integral_comp (transcriptVisits_measurable v).aestronglyMeasurable).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (transcriptVisits_actual π E hS θ j v))

def transcriptDistance (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) : ℝ :=
  Tournament.Probability.acTotalVariation (augmentedTranscriptLaw (T := T) ν π E θ none)
    (augmentedTranscriptLaw (T := T) ν π E θ j)

def transcriptDivergence (ν : Measure Seed) (π : Learner ι Seed) (E : ι → ι → Prop)
    (θ : ℝ) (j : Coordinate S) : ℝ :=
  (klDiv (augmentedTranscriptLaw (T := T) ν π E θ none) (augmentedTranscriptLaw (T := T) ν π E θ j)).toReal

theorem transcriptDistance_sq (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) (j : Coordinate S) :
    transcriptDistance (T := T) ν π E θ j^2≤transcriptDivergence (T := T) ν π E θ j/2 := by
  have hac : augmentedTranscriptLaw (T := T) ν π E θ none ≪ augmentedTranscriptLaw (T := T) ν π E θ j :=
    transcriptLaw_absolutelyContinuous (T := T) ν π E θ j T le_rfl
  have h := Tournament.Probability.pinsker hac (augmented_kl_ne_top ν π E θ j)
  have hs := (sq_le_sq₀ Tournament.Probability.acTotalVariation_nonneg (Real.sqrt_nonneg _)).mpr h
  change transcriptDistance (T := T) ν π E θ j^2≤Real.sqrt (transcriptDivergence (T := T) ν π E θ j/2)^2 at hs
  have hK : 0≤transcriptDivergence (T := T) ν π E θ j := ENNReal.toReal_nonneg
  rwa [Real.sq_sqrt (div_nonneg hK (by norm_num : (0:ℝ)≤2))] at hs

theorem visits_pinsker_transfer (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (hS : SparseMembers E S) (θ : ℝ) (v : S) :
    (∫ p, visits (T := T) π E θ (some v) v p ∂privateLaw ν S T)≤
      (∫ p, visits (T := T) π E θ none v p ∂privateLaw ν S T)+
        (T:ℝ)*transcriptDistance (T := T) ν π E θ (some v) := by
  have hac : augmentedTranscriptLaw (T := T) ν π E θ none ≪ augmentedTranscriptLaw (T := T) ν π E θ (some v) :=
    transcriptLaw_absolutelyContinuous (T := T) ν π E θ (some v) T le_rfl
  have h := Tournament.Probability.expectation_sub_le_totalVariation hac (transcriptVisits (T := T) v)
    (transcriptVisits_measurable v).aemeasurable (T:ℝ)
    (Filter.Eventually.of_forall (transcriptVisits_bounds v))
  rw [transcriptVisits_integral ν π E hS,transcriptVisits_integral ν π E hS] at h
  unfold transcriptDistance
  linarith

theorem finite_average_distance {J : Type*} [Fintype J] (q d : J → ℝ) (hn : 0<(Fintype.card J:ℝ))
    (hd : ∀ j, 0≤d j) (hpin : ∀ j, d j^2≤q j/2) (hKL : (∑ j, q j)<(Fintype.card J:ℝ)/32) :
    (∑ j, d j)<(Fintype.card J:ℝ)/8 := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : J ↦ (1:ℝ)) d
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hCS
  have hsq : (∑ j, d j^2)≤(∑ j, q j)/2 := by
    calc
      _ ≤ ∑ j, q j/2 := Finset.sum_le_sum (fun j _ ↦ hpin j)
      _ = _ := (Finset.sum_div _ _ _).symm
  have hscaled := mul_le_mul_of_nonneg_left hsq hn.le
  have hstrict := mul_lt_mul_of_pos_left hKL hn
  have hnonneg : 0≤∑ j, d j := Finset.sum_nonneg (fun j _ ↦ hd j)
  by_contra h
  have hge := le_of_not_gt h
  nlinarith [sq_nonneg ((∑ j, d j)-(Fintype.card J:ℝ)/8)]

omit [Fintype ι] in
theorem visits_sum_reference_le (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (θ : ℝ) :
    (∑ v : S, ∫ p, visits (T := T) π E θ none v p ∂privateLaw ν S T)≤(T:ℝ) := by
  rw [← integral_finsetSum _ (fun v _ ↦ visits_integrable ν π E θ none v)]
  calc
    _ ≤ ∫ _ : Seed × WalkSign.Space T (Coordinate S), (T:ℝ) ∂privateLaw ν S T := by
      apply integral_mono (integrable_finsetSum _ (fun v _ ↦ visits_integrable ν π E θ none v)) (integrable_const _)
      intro p
      have h := visits_plus_outside π E θ (none : Coordinate S) p
      have ho := outsideVisits_nonneg π E θ (none : Coordinate S) p
      linarith
    _ = _ := by simp

theorem visits_average_le_five_eighths (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Learner ι Seed)
    (E : ι → ι → Prop) (hS : SparseMembers E S) (θ : ℝ) (hn : 2≤S.card)
    (hKL : (∑ j : S, transcriptDivergence (T := T) ν π E θ (some j))<(S.card:ℝ)/32) :
    (∑ j : S, ∫ p, visits (T := T) π E θ (some j) j p ∂privateLaw ν S T)/(S.card:ℝ)≤5*(T:ℝ)/8 := by
  have hn0 : 0<(S.card:ℝ) := by exact_mod_cast (by omega : 0<S.card)
  have hn2 : (2:ℝ)≤(S.card:ℝ) := by exact_mod_cast hn
  have hD : (∑ j : S, transcriptDistance (T := T) ν π E θ (some j))<(S.card:ℝ)/8 := by
    simpa only [Fintype.card_coe] using finite_average_distance
      (fun j : S ↦ transcriptDivergence (T := T) ν π E θ (some j))
      (fun j : S ↦ transcriptDistance (T := T) ν π E θ (some j))
      (by simpa only [Fintype.card_coe] using hn0)
      (fun _ ↦ Tournament.Probability.acTotalVariation_nonneg)
      (fun j ↦ transcriptDistance_sq ν π E θ (some j))
      (by simpa only [Fintype.card_coe] using hKL)
  have hV := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ visits_pinsker_transfer (T := T) ν π E hS θ j)
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hV
  have hRef := visits_sum_reference_le (S := S) (T := T) ν π E θ
  apply (div_le_iff₀ hn0).mpr
  have hTD := mul_le_mul_of_nonneg_left hD.le (show 0≤(T:ℝ) by positivity)
  have hTN := mul_le_mul_of_nonneg_left hn2 (show 0≤(T:ℝ) by positivity)
  nlinarith

theorem visits_average_lt_five_eighths (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hT : 1 ≤ T) (π : Learner ι Seed) (E : ι → ι → Prop)
    (hS : SparseMembers E S) (θ : ℝ) (hn : 2 ≤ S.card)
    (hKL : (∑ j : S, transcriptDivergence (T := T) ν π E θ (some j)) < (S.card : ℝ) / 32) :
    (∑ j : S, ∫ p, visits (T := T) π E θ (some j) j p ∂privateLaw ν S T) /
      (S.card : ℝ) < 5 * (T : ℝ) / 8 := by
  have hn0 : 0 < (S.card : ℝ) := by exact_mod_cast (by omega : 0 < S.card)
  have hn2 : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hn
  have hT0 : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hD : (∑ j : S, transcriptDistance (T := T) ν π E θ (some j)) < (S.card : ℝ) / 8 := by
    simpa only [Fintype.card_coe] using finite_average_distance
      (fun j : S ↦ transcriptDivergence (T := T) ν π E θ (some j))
      (fun j : S ↦ transcriptDistance (T := T) ν π E θ (some j))
      (by simpa only [Fintype.card_coe] using hn0)
      (fun _ ↦ Tournament.Probability.acTotalVariation_nonneg)
      (fun j ↦ transcriptDistance_sq ν π E θ (some j))
      (by simpa only [Fintype.card_coe] using hKL)
  have hV := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ ↦ visits_pinsker_transfer (T := T) ν π E hS θ j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hV
  have hRef := visits_sum_reference_le (S := S) (T := T) ν π E θ
  apply (div_lt_iff₀ hn0).mpr
  have hTD := mul_lt_mul_of_pos_left hD hT0
  have hTN := mul_le_mul_of_nonneg_left hn2 hT0.le
  nlinarith

end
end Tournament.Lower

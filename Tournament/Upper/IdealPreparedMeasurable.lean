module

public import Tournament.Upper.AssignmentSelection
public import Tournament.Upper.PreparedMeasurable
public import Tournament.Upper.ChunkMeasurable

@[expose] public section

namespace Tournament.Upper.SteeringParameters

open MeasureTheory Model
open scoped Classical

noncomputable section

variable {ι A : Type*} [Fintype ι] [Nonempty ι]

def idealAssignment (S : SteeringParameters ι) (π : ProbabilityVector ι) :
    ComparisonAssignment S.tournament (S.anchor π) :=
  optimizedAssignment S.tournament S.isTournament (S.anchor π) (S.anchor_pos π)

variable [MeasurableSpace A]

theorem idealAssignment_matrix_measurable (S : SteeringParameters ι)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (s i r : ι) :
    Measurable (fun a ↦ (S.idealAssignment (p a)).matrix s i r) :=
  optimizedAssignment_matrix_measurable S.tournament S.isTournament (fun a ↦ S.anchor (p a))
    (anchor_weight_measurable S p hp) (fun a ↦ S.anchor_pos (p a)) s i r

theorem idealAssignment_sourceLaw_measurable (S : SteeringParameters ι)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (s : ι) :
    Measurable (fun a ↦ (S.idealAssignment (p a)).sourceLaw s) :=
  optimizedAssignment_sourceLaw_measurable S.tournament S.isTournament (fun a ↦ S.anchor (p a))
    (anchor_weight_measurable S p hp) (fun a ↦ S.anchor_pos (p a)) s

theorem ideal_holding_sampling_measurable (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (i : ι) :
    Measurable (fun a ↦ (S.holding (p a)).sampling i) := by
  simp only [holding, preparation, hIdeal, Bool.false_eq_true, ite_false]
  exact ComparisonAssignment.preparedSampling_measurable
    (fun a ↦ S.idealAssignment (p a)) (idealAssignment_sourceLaw_measurable S p hp)
    (fun a ↦ S.anchor (p a)) (anchor_weight_measurable S p hp)
    (DyadicRate.base S.m) (DyadicRate.base_pos S.m)
    (BlockParameters.base_le_one_thirtytwo S.bands_ge_five) i

theorem ideal_holding_refresh_measurable (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (i : ι) :
    Measurable (fun a ↦ (S.holding (p a)).refresh i) := by
  simp only [holding, preparation, hIdeal, Bool.false_eq_true, ite_false]
  exact ComparisonAssignment.preparedFamily_refresh_measurable
    (fun a ↦ S.idealAssignment (p a)) (idealAssignment_sourceLaw_measurable S p hp)
    (fun a ↦ S.anchor (p a)) (anchor_weight_measurable S p hp) (fun a ↦ S.anchor_pos (p a))
    (DyadicRate.base S.m) (DyadicRate.base_pos S.m)
    (BlockParameters.base_le_one_thirtytwo S.bands_ge_five) i

theorem ideal_holding_kernel_measurable (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i))
    (τ : ℝ) (hτ : 0 < τ) (i j : ι) :
    Measurable (fun a ↦ (S.holding (p a)).kernel τ hτ i j) :=
  HoldingFamily.kernel_entry_measurable (fun a ↦ S.holding (p a))
    (ideal_holding_sampling_measurable S hIdeal p hp)
    (ideal_holding_refresh_measurable S hIdeal p hp) τ hτ i j

theorem ideal_estimator_entry_measurable (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (s i r : ι) :
    Measurable (fun a ↦ S.estimator (p a) s i r) := by
  have hSampling := ideal_holding_sampling_measurable S hIdeal p hp
  simp only [holding, preparation, hIdeal, Bool.false_eq_true, ite_false] at hSampling
  simp only [estimator, preparation, hIdeal, Bool.false_eq_true, ite_false]
  exact ComparisonAssignment.estimator_measurable
    (fun a ↦ S.idealAssignment (p a)) (idealAssignment_matrix_measurable S p hp)
    (fun a ↦ S.anchor (p a)) _ (anchor_weight_measurable S p hp) hSampling s i r

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem ideal_rules_decoder_measurable (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (j : Fin (S.m + 1)) :
    ScoreRule.DecoderMeasurable (fun a ↦ S.rules (p a) j) := by
  intro n s k hs hk obs hObs
  simp only [rules_decoder_eq]
  exact scoreFromComparisons_measurable S.tournament _
    (ideal_holding_kernel_measurable S hIdeal p hp
      (DyadicRate.rate S.m j) (DyadicRate.rate_pos S.m j)) s k hs hk obs hObs

theorem ideal_observedRow_measurable (S : SteeringParameters ι) (hIdeal : S.rounded = false)
    (p : A → ProbabilityVector ι) (hp : ∀ i, Measurable (fun a ↦ p a i)) (j : Fin (S.m + 1))
    (M : ℝ) (n : ℕ) (hist : A → ComparisonHistory ι n) (hHist : Measurable hist)
    (obs : A → ι → ℝ) (hObs : ∀ k, Measurable (fun a ↦ obs a k)) (k : ι) :
    Measurable (fun a ↦ (S.rules (p a) j).observedRow M n (hist a) (obs a) k) :=
  ScoreRule.observedRow_weight_measurable (fun a ↦ S.rules (p a) j)
    (ideal_rules_decoder_measurable S hIdeal p hp j)
    (ideal_holding_kernel_measurable S hIdeal p hp
      (DyadicRate.rate S.m j) (DyadicRate.rate_pos S.m j))
    (ideal_holding_sampling_measurable S hIdeal p hp) M n hist hHist obs hObs k

end

end Tournament.Upper.SteeringParameters
